"""
a test of connection to coq-tactician-api
"""

import sys
import asyncio
import socket
import argparse
import functools
import logging
import itertools

from typing import List, Optional, Iterable

import pytact.common

from pytact.common import Proving, capnpLocalTactic, runTactic
from pytact.graph_visualize import Visualizer

# Set up logging

logger = logging.getLogger(__name__)


# Open a new proof given a nameless theorem statement (str)
async def open_proof(pull, theorem: str, vis: Visualizer):
    logger.info("awaiting pull")
    resp = await pull.reinforce(theorem).a_wait()
    if not vis is None:
        vis.render(resp.result)

    available_cap = resp.available

    logger.info("awaiting awailable tactics")
    available = await available_cap.tactics().a_wait()

    for tac in available.tactics:
        logger.info("awaiting printTactic")
        tac_str = await available_cap.printTactic(tac.ident).a_wait()
        logger.info(
            "available tactic: ident %s, parameters %d, tac_str %s",
            tac.ident, tac.parameters, tac_str.tactic)

    return resp.result, available.tactics

class ProtocolError(Exception):
    """
    need more work on handling the errors
    """

async def search_dfs(result, tactics, limit) -> Optional[List[capnpLocalTactic]]:
    """
    launches recursive dfs proof search from the current proof search state of result
    if proof is found, returns the list of actions to execute to reach the proof"
    in Ocaml notations the return of search_dfs is None | Some of List


    TODO: currently is is simplistic dfs that assumes that the proof search graph is a Tree
    (i.e. that actions do not bring back the visited states)

    but as the proof search graph is not a tree, at the minimum we
    need to maintain the hashmap of the visited proof states and
    don't return and expand the visited proof states

    TODO: to perform this correctly we have to construct the correct
    invariant of the proof state, a proper faithful hash
    representation that completely identifies isomorphic
    proof states and distinguished non-isomorphic proof states
    """

    if limit == 0:
        return None # dfs limit exceeded

    logger.info('received result of type %s', result.which())

    if result.which() == 'protocolError':
        logger.error('received %s', result.protocolError.which())
        raise ProtocolError  # our code is wrong
    elif result.which() == 'failure':
        return None # dead branch, coq can't execute
    elif result.which() == 'complete':
        print('COMPLETE')
        return []   # proof found :)! hurrah
    elif result.which() == 'newState':
        logger.info('considering %s', result.which())
        root: int = result.newState.state.root
        context: List[int] = [n.nodeIndex for n in result.newState.state.context]
        logger.info('root is %d, context is %s', root, repr(context))

        actions = []
        for tac in tactics:
            for arg in itertools.product(context, repeat=tac.parameters):
                action = capnpLocalTactic(tac.ident, arg)
                actions.append(action)
        logger.info('expanding search node on %d actions available', len(actions))
        for action in actions:
            next_result = await runTactic(result.newState.obj, action)
            next_solution = await search_dfs(next_result, tactics, limit-1)
            if not next_solution is None:
                next_solution.append(action)
                return next_solution
        return None
    else:
        raise Exception # it supposed to be exhaustive


async def example_script_prover(args, pull):
    TAC_INTROS = 4249207563281686782
    TAC_APPLY = 3192827940261208899
    result, _ = await open_proof(pull, "forall A B C : Prop, (A -> B -> C) -> A -> B -> C", args.vis)
    result = await runTactic(result.newState.obj, capnpLocalTactic(TAC_INTROS, []), args.vis)
    result = await runTactic(result.newState.obj, "intro", args.vis)
    result = await runTactic(result.newState.obj, capnpLocalTactic(TAC_INTROS, []), args.vis)
    result = await runTactic(result.newState.obj, capnpLocalTactic(TAC_INTROS, []), args.vis)
    result = await runTactic(result.newState.obj, capnpLocalTactic(TAC_INTROS, []), args.vis)
    result = await runTactic(result.newState.obj, capnpLocalTactic(TAC_INTROS, []), args.vis)
    result = await runTactic(result.newState.obj, capnpLocalTactic(TAC_APPLY, [6]), args.vis)
    result = await runTactic(result.newState.obj, "apply H0", args.vis)
    result = await runTactic(result.newState.obj, capnpLocalTactic(TAC_APPLY, [8]), args.vis)
    assert result.which() == 'complete'  # if this is correct proof


async def dfs_prover(theorems: Iterable[str], args, pull):
    for theorem in theorems:
        print(f"DFS starts theorem {theorem}", end='')
        result, tactics = await open_proof(pull, theorem.strip(), vis=None)
        solution = await search_dfs(result, tactics, args.dfs_limit)
        if not solution is None:
            logging.info("Proof found:")
            for action in reversed(solution):
                print(action)
                result = await runTactic(result.newState.obj, action)
                if args.vis is not None:
                    args.vis.render(result)
        else:
            logging.info("Proof not found")


async def client_connected_cb(counter, args, reader, writer):
    logger.info("client connected to python server socket, remaining connections %d", counter.cnt)

    proving = Proving(reader, writer)

    if args.dfs:
        if not args.inputfile is None:
            theorems = open(args.inputfile, 'r')
        else:
            theorems = sys.stdin

        with theorems:
            await proving.run_prover(functools.partial(dfs_prover, theorems, args))
    else:
        await proving.run_prover(functools.partial(example_script_prover, args))

    counter.dec()
    logger.info("client connected cb finished %d", counter.cnt)


def my_parse_args():
    parser = argparse.ArgumentParser(
        description='example of python code interacting with coq-tactician-api')

    parser.add_argument('--interactive',
                        action='store_true',
                        help='drop to the python shell after proof execution')

    parser.add_argument('--loglevel',
                        default='INFO',
                        help='set logging.loglevel to be DEBUG, INFO, WARNING, ERROR, CRITICAL')


    parser.add_argument('--show-labels',
                        action='store_true',
                        help=('show labels on visualized graph')
                        )

    parser.add_argument('--pdfsequence',
                        action='store_true',
                        help=('write visualization output to a sequence of pdfs'
                             'graph0.pdf, graph1.pdf, ...'))

    parser.add_argument('--pdfname',
                        type=str,
                        default=None,
                        help=('name of pdf file(s) for graph visualization'))

    parser.add_argument('--dot',
                        action='store_true',
                        help='keep .dot files produced for graph visualization')


    parser.add_argument('--tcp', action='store_true',
                        help='drive coq-tactician-api with tcp/ip instead of stdin')

    parser.add_argument('--tcp-sessions',
                        type = int,
                        default= -1,
                        help='number of tcp-sessions to serve, with -1 standing for infinity')

    parser.add_argument('--ip', type=str,
                        default="127.0.0.1",
                        help='run python server on this ip')

    parser.add_argument('--port', type=int,
                        default=33333,
                        help='run python server on this port')

    parser.add_argument('--with-coq', action='store_true',
                       help='applies only to tcp mode: launch coq as a subprocess')


    parser.add_argument('--coqfile', type=str, default=None,
                        help=('path to coq source code file (.v extension) to execute'
                              'in coq-tactician-api'
                              f'the default is {pytact.common.test_filename_stdin}'
                              f'for --tcp --with-coq default is {pytact.common.test_filename_tcp}'))

    parser.add_argument('--inputfile', type=str, default=None,
                        help=('the filename of the inputfile file with a list of'
                             'independent context free propositions to prove'
                             'one proposition per line, for exampel "forall A:Prop, A->A" (without double quotes)'
                             'no keyword theorem and point in the end is required'))
    parser.add_argument('--testfile', type=str, default=None,
                        help=('the name of the test input file to run'
                              'that is included in this package'))

    parser.add_argument('--dfs', action='store_true',
                       help='run dfs search instead of a script')

    parser.add_argument('--dfs-limit', type=int,
                        default=50,
                        help=('number of dfs proof search tree total node visits'))


    args = parser.parse_args()
    if not args.testfile is None:
        args.inputfile = pytact.common.testfile(args.testfile)

    if args.coqfile is None:
        if (args.tcp and args.with_coq):
            args.coqfile = pytact.common.test_filename_tcp
        else:
            args.coqfile = pytact.common.test_filename_stdin

    numeric_level = getattr(logging, args.loglevel.upper(), None)
    if not isinstance(numeric_level, int):
        raise ValueError('Invalid log level: %s' % args.loglevel)

    args.loglevel = numeric_level

    if not args.pdfname is None:
        args.vis = Visualizer(args.pdfname, args.pdfsequence,
                         args.show_labels, cleanup=not args.dot)
    else:
        args.vis = None


    print(f"Python: running with tcp_enabled = {args.tcp} on"
          f"coqfile {args.coqfile} on inputfile {args.inputfile}"
          f"with visualization output to {args.pdfname}")

    return args


# this is a helper class to support finite number of
# evaluated connections in case of running
# tcp server on python side
# to signal finishing serving event
# normally serving will be finished
# with events like reaching the certain
# number of epochs, etc

class Counter:
    def __init__(self, n: int):
        self.cnt = n
        self.event = asyncio.Event()

    def dec(self):
        self.cnt -= 1
        if (self.cnt == 0):
            self.event.set()

    async def waiter(self):
        await self.event.wait()


async def a_main(args):
    counter = Counter(args.tcp_sessions)

    call_back = functools.partial(client_connected_cb, counter, args)
    if args.tcp:
        py_ip = args.ip
        py_port = args.port
        logger.info("starting a tcp/ip server on %s %d", py_ip, py_port)
        server = await asyncio.start_server(call_back, host=py_ip, port=py_port)
        if args.with_coq:
            print("Python: launching coqc in subprocess!!", file=sys.stderr)
            proc = await asyncio.create_subprocess_exec(
                'tactician', 'exec', 'coqc', args.coqfile,
                stdin=None,
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE)
            #coqout, coqerr = await proc.communicate()
            #print("proc finished!!", file=sys.stderr, flush=True)


            #with open('coq_out.txt','wb') as f:
            #    f.write(coqout)
            #with open('coq_err.txt','wb') as f:
            #    f.write(coqerr)

        async with server:
            server_task = asyncio.create_task(server.serve_forever())
            waiter_task = asyncio.create_task(counter.waiter())
            await asyncio.wait([server_task, waiter_task], return_when=asyncio.FIRST_COMPLETED)
            logger.info("server task %s", repr(server_task))
            logger.info("waiter task %s", repr(waiter_task))

            if server_task.done() and server.taks.exception():
                logger.error("server task exception %s", repr(server_task.exception()))
                raise server.taks.exception()

    else:
        print("Python: creating Unix socketpair and giving the other end as stdin to coqc",
              file=sys.stderr)

        py_sock, coq_sock = socket.socketpair()
        print(f"running tactician exec coqc {args.coqfile}")
        proc = await asyncio.create_subprocess_exec(
            'tactician', 'exec', 'coqc', args.coqfile,
            stdin=coq_sock,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE)
        coq_sock.close()

        reader, writer = await asyncio.open_connection(sock=py_sock)
        await call_back(reader, writer)
        print("Python: call_back is returned!")



def main():
    args = my_parse_args()

    logging.basicConfig(level=args.loglevel)
    asyncio.run(a_main(args), debug=args.loglevel)

if __name__ == '__main__':
    main()
