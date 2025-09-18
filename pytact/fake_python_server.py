import asyncio
import contextlib
from functools import partial
import sys
import socket
import argparse
import pytact.graph_visualize as gv
import capnp
from pytact.data_reader import (capnp_message_generator, ProofState,
                                TacticPredictionGraph, TacticPredictionsGraph,
                                TacticPredictionText, TacticPredictionsText,
                                GlobalContextMessage, CheckAlignmentMessage, CheckAlignmentResponse)
from pytact.visualisation_webserver import wrap_visualization

async def text_prediction_loop(context : GlobalContextMessage):
    tactics = [ 'idtac "is it working?"', 'idtac "yes it is working!"', 'auto' ]
    prediction_requests = context.prediction_requests
    async for msg in prediction_requests:
        # Redirect any exceptions to Coq. Additionally, deal with CancellationError
        # thrown when a request from Coq is cancelled
        async with context.redirect_exceptions(Exception):
            if isinstance(msg, ProofState):
                proof_state = msg
                print(proof_state.text)
                preds = [TacticPredictionText(t, 0.5) for t in tactics]
                await prediction_requests.asend(TacticPredictionsText(preds))
            elif isinstance(msg, CheckAlignmentMessage):
                alignment = CheckAlignmentResponse([], [])
                await prediction_requests.asend(alignment)
            elif isinstance(msg, GlobalContextMessage):
                await text_prediction_loop(msg)
            else:
                raise Exception("Capnp protocol error")

async def graph_prediction_loop(context : GlobalContextMessage, prev_tactics, level):
    print(f"level {level}")
    for cluster in context.definitions.clustered_definitions(full = False):
        print('cluster:')
        for d in cluster:
            print(f'    {d.name}')

    tactics = prev_tactics.copy()
    for d in context.definitions.definitions(full = False):
        if p := d.proof:
            for ps in p:
                if t := ps.tactic:
                    tactics.add((t.ident, len(ps.outcomes[0].tactic_arguments)))

    print(context.log_annotation)
    prediction_requests = context.prediction_requests
    cool_definitions = [ d.node for d in context.definitions.definitions() if d.name == "Coq.Init.Logic.I" ]
    zeroArgs = [ident for (ident, parameters) in tactics if parameters == 0]
    oneArg = [ident for (ident, parameters) in tactics if parameters == 1]
    async for msg in prediction_requests:
        # Redirect any exceptions to Coq. Additionally, deal with CancellationError
        # thrown when a request from Coq is cancelled
        async with context.redirect_exceptions(Exception):
            if isinstance(msg, ProofState):
                proof_state = msg
                gv.visualize_proof_state(proof_state)
                preds = [TacticPredictionGraph(t, [], 0.5) for t in zeroArgs]
                if len(proof_state.context) > 0:
                    hyp_node = proof_state.context[0]
                    preds += [TacticPredictionGraph(t, [hyp_node], 0.5) for t in oneArg]
                for d in cool_definitions:
                    preds += [TacticPredictionGraph(t, [d], 0.5) for t in oneArg]
                await prediction_requests.asend(TacticPredictionsGraph(preds))
            elif isinstance(msg, CheckAlignmentMessage):
                unknown_definitions = list(context.definitions.definitions())
                unknown_tactics = [ident for (ident, _) in tactics]
                alignment = CheckAlignmentResponse(unknown_definitions, unknown_tactics)
                await prediction_requests.asend(alignment)
            elif isinstance(msg, GlobalContextMessage):
                await graph_prediction_loop(msg, tactics, level + 1)
            else:
                raise Exception(f"Capnp protocol error {msg}")



async def run_session(args, record_file, capnp_stream):
    messages_generator = capnp_message_generator(capnp_stream, args.rpc, record_file)
    if args.with_visualization:
        messages_generator = await wrap_visualization(messages_generator)
    if args.mode == 'text':
        print('Python server running in text mode')
        await text_prediction_loop(messages_generator)
    elif args.mode == 'graph':
        print('Python server running in graph mode')
        await graph_prediction_loop(messages_generator, set(), 0)
    else:
        raise Exception("The 'mode' argument needs to be either 'text' or 'graph'")

async def server():
    sys.setrecursionlimit(10000)
    parser = argparse.ArgumentParser(
        description = "Example python server capable of communicating with Coq through Tactician's 'synth' tactic",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter)

    parser.add_argument('mode',
                        type=str,
                        choices=['graph', 'text'],
                        help='"graph" to communicate in graph-mode, "text" to communicate in text-mode')
    parser.add_argument('--tcp',
                        type = int,
                        default = 0,
                        help='Run in tcp mode instead of stdin mode on the specified port.')
    parser.add_argument('--record',
                        dest="record_file",
                        type = str,
                        default = None,
                        help='Record all exchanged messages to the specified file, so that they can later be ' +
                        'replayed through "pytact-fake-coq"')
    parser.add_argument('--rpc', action='store_true', default = False,
                        help='Communicate through Cap\'n Proto RPC.')
    parser.add_argument('--with-visualization', action='store_true', default = False,
                        help='Launch a visualization webserver')
    args = parser.parse_args()

    if args.record_file is not None:
        record_context = open(args.record_file, 'wb')
    else:
        record_context = contextlib.nullcontext()
    with record_context as record_file:
        if args.tcp != 0:
            new_connection = partial(run_session, args, record_file)
            server = await capnp.AsyncIoStream.create_server(new_connection, host='localhost', port=args.tcp)
            async with server:
                await server.serve_forever()
        else:
            stdin_socket = socket.socket(fileno=sys.stdin.fileno())
            capnp_stream = await capnp.AsyncIoStream.create_connection(sock=stdin_socket)
            await run_session(args, record_file, capnp_stream)

def main():
    asyncio.run(capnp.run(server()), debug=True)

if __name__ == '__main__':
    main()
