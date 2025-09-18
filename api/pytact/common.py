"""
common  wrapping functions for python - capnp - tactician interface

provides class Proving with method run_prover that evaluates your python
proving session in coq environment over capnp communication

you need yourself to establish socket/pipe connection with capnp end of coq
and instantiate Proving object with
"""

import pkg_resources
import os
import logging
import asyncio
import functools
from typing import List
import capnp

test_filename_stdin = pkg_resources.resource_filename('pytact','tests/TestReinforceStdin.v')
test_filename_tcp  =  pkg_resources.resource_filename('pytact','tests/TestReinforceTcp.v')

def testfile(fname: str):
    return pkg_resources.resource_filename('pytact', os.path.join('tests', fname))


logger = logging.getLogger(__name__)





class Connection:
    """
    wrapper class for serving capnp  connection
    this wrapper is not specialized to a particular capnp schema
    """
    async def _reading_socket(self):
        """
        This loop reads from connected pipe and writes to local capnp client
        """
        client = self.client
        reader = self.reader
        while not reader.at_eof():
            data = await reader.read(4096)
            logger.debug("read from socket %d bytes", len(data))
            client.write(data)
            logger.debug("wrote to client %d bytes", len(data))

        logger.debug("_reading_socket ended")
        return '_reading_socket ended'


    async def _writing_socket(self):
        """
        This reads from local capnp client and writes to connected pipe
        """
        client = self.client
        writer = self.writer
        while True:
            data = await client.read(4096)
            logger.debug("read from client %d bytes", len(data))

            writer.write(data.tobytes())
            await writer.drain()
            logger.debug("wrote to socket %d bytes", len(data))

        logger.debug("_writing to socket ended")
        return '_writing_socket ended'

    def __init__(self, reader, writer):
        self.reader = reader
        self.writer = writer

        logger.debug("starting capnp client")

        import pytact.graph_api_capnp as api
        self.api = api

        self.client = capnp.TwoPartyClient()



    async def run(self, proc):
        """
        this method runs the function proc
        that defines the process of interacting with capnp connection
        on python side

        the function proc should be of async awaitable type that takes
        two arguments, proc(client, api), the types of client and api
        are like in these cals

        client = capnp.TwoPartyClient()
        api = capnp.load(api.capnp)

        and returns None when completed

        example:

        async def proc(client)
            # do your interaction with with capnp client using the api
            return

        """

        read_task = asyncio.create_task(self._reading_socket())
        write_task = asyncio.create_task(self._writing_socket())
        proc_task = asyncio.create_task(proc(self.client, self.api))

        _done, _pending = await asyncio.wait([read_task, write_task, proc_task],
                                           return_when=asyncio.FIRST_COMPLETED)

        if proc_task.done():
            logger.debug("process with capnp ended %s", repr(proc_task))
            if proc_task.exception():
                raise Exception("EXCEPTION in connection task; this is not expected, debug: %s",
                                repr(proc_task))

        else:
            if read_task.done():
                raise Exception("reading_socket ended before reinforce ended: "
                             "possibly terminated from other side")
            if write_task.done():
                raise Exception("_writing_socket ended ended before reinforce ended: "
                             "possibly connection broken")

        read_task.cancel()
        write_task.cancel()
        proc_task.cancel()
        self.writer.close()

        logger.info("serving connection finished")

class Proving(Connection):
    """
    this is a higher level wrapper over Connection class that
    provides higher level run_prover method that takes as an input
    and runs your function prover and provides
    to prover the pull object of graph_api.capnp schema

    Example:

    proving = Proving(reader, writer)
    await proving.run_prover(your_super_prover)

    where reader and writer are the read and write end of socket/pipe to
    the other end of capnp coq

    and where you need to implement your_super_prover function as you like

    See doc string of run_prover method
    """
    @staticmethod
    async def __proc(prover, client, api):
        logger.info("calling PullReinforce")
        pull = client.bootstrap().cast_as(api.PullReinforce)
        await prover(pull)

    async def run_prover(self, prover):
        """
        The method run_prover runs your function prover in coq
        evaluation session  using capnp protocol graph_api.capnp schema

        Your function prover should take one argument

        pull

        that is an object defined by graph_api.capnp schema

        You can start the  proving session in your functin prover
        by opening coq proving environment with a call to pull as follows:

        response = await pull.reinforce(lemma).a_wait

        You get available tactics with

        available = await response.available.tactics().a_wait

        You get the context and goal packed in response.result
        as specified in graph_api.capnp schema

        NOTICE: the implementation of this class depends on the particular naming
        and data structures we have chosen in graph_api.capnp schema

        This is subject to change
        """
        await self.run(functools.partial(self.__proc, prover))


def globalNode(nodeIndex):
    """
    returns capnp global node argument given local node index
    """
    return {'depIndex': 0, 'nodeIndex': nodeIndex}

def capnpLocalTactic(ident: int, local_arguments: List[int]):
    """
    returns capnpTactic argument given  ident and a list of local nodes
    """
    res = {'ident': ident}, [{'term': globalNode(nodeIndex)} for nodeIndex in local_arguments]
#           'arguments': [{'term': globalNode(nodeIndex)} for nodeIndex in local_arguments]}
    return res

def graph_api_capnp():
    return pkg_resources.resource_filename('pytact','graph_api.capnp')

async def runTactic(obj, tactic, vis=None):
    """
    wrapper on capnp runTactic with logging
    vis: pytact.graph_visualize.Visualizer
    """
    logger.info("awaiting tactic %s", repr(tactic))
    if isinstance(tactic, str):
        resp = await obj.runTextTactic(tactic).a_wait()
    else:
        resp = await obj.runTactic(*tactic).a_wait()
    result = resp.result
    logger.info('received result of type %s', result.which())
    if result.which() == 'newState':
        logger.info('new proof state: %s', result.newState.state.text)
        root = result.newState.state.root
        context = list(result.newState.state.context)
        logger.debug('with root: %d', root)
        logger.debug('with context: %s', repr(context))
    if vis is not None:
        vis.render(result)

    if result.which() == 'protocolError':
        logger.error('received protocolError %s', result.protocolError.which())
    #    raise ProtocolError  # our code is wrong

    return result
