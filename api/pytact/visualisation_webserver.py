from dataclasses import asdict
from pathlib import Path
import argparse
import inflection
from functools import partial
from contextlib import ExitStack
try:
    # Python < 3.9
    import importlib_resources as ilr
except ImportError:
    import importlib.resources as ilr

from pytact.data_reader import data_reader, GlobalContextMessage, ProofState, CheckAlignmentMessage
from pytact.graph_visualize_browse import (
    GraphVisualizationData, GraphVisualizator, UrlMaker, Settings, GraphVisualizationOutput)

import capnp
import pytact.graph_api_capnp as graph_api_capnp

from sanic import Sanic
from sanic_ext import validate
from sanic.worker.loader import AppLoader

def post_process(output: GraphVisualizationOutput, settings: Settings):
    result = asdict(output)
    result['settings'] = settings
    result['edge_labels'] = [(v, inflection.camelize(name)) for (name, v) in
                             graph_api_capnp.EdgeClassification.schema.enumerants.items()]
    result['node_labels'] = [(v, inflection.camelize(name)) for (v, name) in
                             enumerate(list(graph_api_capnp.Graph.Node.Label.schema.union_fields))]
    return result

def create_app(dataset_path: Path) -> Sanic:
    app = Sanic("graph-visualizer")

    context_manager = ExitStack()
    template_path = ilr.files('pytact') / 'templates/'
    app.config.TEMPLATING_PATH_TO_TEMPLATES = context_manager.enter_context(ilr.as_file(template_path))
    if isinstance(dataset_path, Path):
        app.ctx.gvd = GraphVisualizationData(context_manager.enter_context(data_reader(dataset_path)))
    else:
        app.ctx.gvd = dataset_path

    @app.after_server_stop
    async def teardown(app):
        context_manager.close()

    class SanicUrlMaker(UrlMaker):

        def __init__(self, settings: Settings):
            self.query = {k: v for k, v in asdict(settings).items() if type(v) != bool or v}

        def definition(self, fname: Path, defid: int) -> str:
            return app.url_for('definition', path=fname.with_suffix(''), defid=defid, **self.query)

        def proof(self, fname: Path, defid: int) -> str:
            return app.url_for('proof', path=fname.with_suffix(''), defid=defid, **self.query)

        def outcome(self, fname: Path, defid: int, stepi: int, outcomei: int) -> str:
            return app.url_for('outcome', path=fname.with_suffix(''),
                            defid=defid, stepi=stepi, outcomei=outcomei, **self.query)

        def global_context(self, fname: Path) -> str:
            return app.url_for('global_context', path=fname.with_suffix(''), **self.query)

        def folder(self, path: Path) -> str:
            return app.url_for('folder', path=path, **self.query)

        def root_folder(self) -> str:
            return app.url_for('root_folder', **self.query)

    @app.get('/<path:path>/definition/<defid:int>/proof/step/<stepi:int>/outcome/<outcomei:int>')
    @validate(query=Settings)
    @app.ext.template("visualizer.html")
    async def outcome(request, path: str, defid: str, stepi: str, outcomei: str, query: Settings):
        gv = GraphVisualizator(app.ctx.gvd, SanicUrlMaker(query), query)
        return post_process(gv.outcome(Path(path).with_suffix(".bin"), int(defid), int(stepi), int(outcomei)), query)

    @app.get('/<path:path>/definition/<defid:int>/proof')
    @validate(query=Settings)
    @app.ext.template("visualizer.html")
    async def proof(request, path: str, defid: str, query: Settings):
        gv = GraphVisualizator(app.ctx.gvd, SanicUrlMaker(query), query)
        return post_process(gv.proof(Path(path).with_suffix(".bin"), int(defid)), query)

    @app.get('/<path:path>/definition/<defid:int>')
    @validate(query=Settings)
    @app.ext.template("visualizer.html")
    async def definition(request, path: str, defid: str, query: Settings):
        gv = GraphVisualizator(app.ctx.gvd, SanicUrlMaker(query), query)
        return post_process(gv.definition(Path(path).with_suffix(".bin"), int(defid)), query)

    @app.get('/<path:path>/context')
    @validate(query=Settings)
    @app.ext.template("visualizer.html")
    async def global_context(request, path: str, query: Settings):
        gv = GraphVisualizator(app.ctx.gvd, SanicUrlMaker(query), query)
        return post_process(gv.global_context(Path(path).with_suffix(".bin")), query)

    @app.get('/<path:path>')
    @validate(query=Settings)
    @app.ext.template("visualizer.html")
    async def folder(request, path: str, query: Settings):
        gv = GraphVisualizator(app.ctx.gvd, SanicUrlMaker(query), query)
        return post_process(gv.folder(Path(path)), query)

    @app.get('/')
    @validate(query=Settings)
    @app.ext.template("visualizer.html")
    async def root_folder(request, query: Settings):
        gv = GraphVisualizator(app.ctx.gvd, SanicUrlMaker(query), query)
        return post_process(gv.folder(Path()), query)

    return app


async def wrap_visualization(context : GlobalContextMessage) -> GlobalContextMessage:
    app = create_app(GraphVisualizationData(dict()))

    server = await app.create_server(
        port=8000, host="0.0.0.0", return_asyncio_server=True
    )

    await server.startup()
    await server.start_serving()

    async def wrapper(context, stack):
        data = { Path(f"Slice{i}.bin") : d for i, d in enumerate(stack)}
        app.ctx.gvd = GraphVisualizationData(data)
        prediction_requests = context.prediction_requests
        async for msg in prediction_requests:
            # Redirect any exceptions to Coq. Additionally, deal with CancellationError
            # thrown when a request from Coq is cancelled
            async with context.redirect_exceptions(Exception):
                if isinstance(msg, ProofState):
                    resp = yield msg
                    yield
                    await prediction_requests.asend(resp)
                elif isinstance(msg, CheckAlignmentMessage):
                    resp = yield msg
                    yield
                    await prediction_requests.asend(resp)
                elif isinstance(msg, GlobalContextMessage):
                    yield GlobalContextMessage(msg.definitions,
                                    msg.tactics,
                                    msg.log_annotation,
                                    wrapper(msg, stack + [msg.definitions]),
                                    msg.redirect_exceptions)
                else:
                    raise Exception(f"Capnp protocol error {msg}")

    return GlobalContextMessage(context.definitions,
                    context.tactics,
                    context.log_annotation,
                    wrapper(context, []),
                    context.redirect_exceptions)

def main():

    parser = argparse.ArgumentParser(
        description = 'Start an interactive server that visualizes a dataset',
        formatter_class=argparse.ArgumentDefaultsHelpFormatter)

    parser.add_argument('dataset',
                        type=str,
                        help=('The location of the dataset to visualize. ' +
                              'Either a dataset directory, or a SquashFS image, ' +
                              'which will be automatically mounted.'))
    parser.add_argument('--port',
                        type=int,
                        default=8080,
                        help='the port where the webserver should listen')
    parser.add_argument('--hostname',
                       type=str,
                       default='0.0.0.0',
                       help='the ip or domain of the hosting machine')
    parser.add_argument('--dev',
                        action='store_true',
                        help='run the server in development mode')
    group = parser.add_mutually_exclusive_group()
    group.add_argument('--fast', action='store_true', default=False,
                       help='Run the server with an optimal number of worker')
    group.add_argument('--workers', type=int, default=1,
                       help='The number of workers to use')

    args = parser.parse_args()

    dataset_path = Path(args.dataset).resolve()

    loader = AppLoader(factory=partial(create_app, dataset_path))
    app = loader.load()
    app.prepare(host=args.hostname, port=args.port, dev=args.dev, fast=args.fast, workers=args.workers)
    Sanic.serve(primary=app, app_loader=loader)

if __name__ == '__main__':
    main()
