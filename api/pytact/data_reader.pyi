# NOTE: This file is derived from data_reader.pyx. Any changes here should be reflected there as well.

"""This module provides read access to dataset files of a Tactican API dataset.
Additionally, there is support for communicating with a Coq processes through
the same data-format. The next sections give an overview of how this can be
accomplished. For an overview of examples, see `pytact`.

# Reading a dataset

The dataset is mapped into memory using mmap, allowing random access to it's
structures while keeping memory low. This file contains three entry-points to a
dataset in order of preference:

1. Contextmanager `pytact.data_reader.data_reader(path)` provides high-level access to the data
   in directory `path`. This is the preferred entry-point unless you need
   something special.
2. Contextmanager `pytact.data_reader.lowlevel_data_reader(path)` provides low-level access to
   the data in directory `path`, giving direct access to the Cap'n Proto structures
   of the dataset. Use this when `data_reader` is too slow or you need access
   to data not provided by `data_reader`.
3. Contextmanager `file_dataset_reader` provides low-level access to
   the Cap'n Proto structures of a single file. Using this is usually not
   advisable.

Additionally, some indexing and traversal helpers are provided:
- `GlobalContextSets` calculates and caches the global context of a definition
  as a set, also caching intermediate results.
- `definition_dependencies` and `node_dependencies` traverse the graph starting
  from a node and return all direct, non-transitive definitions that node depends on.

# Communicating with a Coq process

Communication with a Coq process can be done either through a high-level or
low-level interface.

## Highlevel interface

The function `capnp_message_generator` converts a socket into a nested generator that
yields request messages for predictions and expects to be sent response messages
in return. A simple example of how to handle these messages is in `pytact.fake_python_server`.
Some docs can be found with `capnp_message_generator`.

The `capnp_message_generator` function can also dump the sequence of messages send
and received to a file. One can then use `capnp_message_generator_from_file` to replay
that sequence against a server, either in a unit-test where the call to `capnp_message_generator`
is mocked by `capnp_message_generator_from_file`, or using a fully fledged socket test
as can be found in `pytact.fake_coq_client`.

## Lowlevel interface

The function `capnp_message_generator_lowlevel` converts a socket into a generator that
yields lowlevel Cap'n Proto request messages for predictions and expects to be sent Cap'n proto
messages in return. There are four types of messages `msg` Coq sends.
1. Synchronize: If `msg.is_synchronize` is true, Coq is attempting to synchronize
   its state with the server. A `PredictionProtocol.Response.synchronized` message is expected
   in return.
2. Initialize: If `msg.is_initialize` is true, Coq is sending a list of available
   tactics and a global context fragment to be added to an existing stack of global context
   information. An empty stack can be created through `empty_online_definitions_initialize`.
   To add an initialize message to the stack, you can use
   ```
   with pytact.data_reader.online_definitions_initialize(existing_stack, msg) as definitions:
       print(type(definitions))
   ```
   Any subsequent messages will be made in the context of the
   tactics and predictions sent in this message, until an initialize message is received
   such that `msg.initialize.stack_size` is smaller than the current stack size.
   A `PredictionProtocol.Response.initialized` message is expected in response of this message.
4. Predict: If `msg.is_predict` is true, Coq is asking to predict a list of plausible
   tactics given a proof state. The proof state can be easily accessed using
   ```
   with pytact.data_reader.online_data_predict(definitions, msg.predict) as proof_state:
       print(dir(proof_state))
   ```
   A `PredictionProtocol.Response.prediction` or `PredictionProtocol.Response.textPrediction`
   message is expected in return.
5. Check Alignment: If `msg.is_check_alignment` is true, then Coq is asking the server
   to check which tactics and definitions are known to it. A
   `PredictionProtocol.Response.alignment` message is expected in return.

You can wrap the generator produced by `capnp_message_generator_lowlevel` into
`record_lowlevel_generator` in order to record the exchanged messages to disk.
This trace can later be replayed using
`capnp_message_generator_from_file_lowlevel` (or using the high-level interface).

"""

from __future__ import annotations
from contextlib import contextmanager, ExitStack
from dataclasses import dataclass
from typing import Any, Callable, TypeAlias, TypeVar, Union, cast, BinaryIO
from collections.abc import Iterable, Sequence, Generator
from pathlib import Path
from immutables import Map
import signal
import pytact.graph_api_capnp_cython as apic # type: ignore
import capnp# type: ignore
import pytact.graph_api_capnp as graph_api_capnp # type: ignore
import socket
import mmap
import itertools
import resource
import threading
import subprocess
import shutil
import time

@contextmanager
def file_dataset_reader(fname: Path) -> Generator[apic.Dataset_Reader, None, None]:
    """Load a single dataset file into memory, and expose its raw Cap'n Proto structures.

    This is a low-level function. Prefer to use `data_reader` or `lowlevel_data_reader`.
    """
    ...

class LowlevelDataReader:
    """A thin wrapper around the raw Cap'n Proto structures contained in a dataset directory.

    Every file in the directory is assigned an integer called a graph-id. This class is a
    `Sequence` that allows the retrieval of the structures in a file by its graph-id.
    Additionally, the function `local_to_global` translates a dependency-index relative to
    a graph-id to a new graph-id. This allows one to find out in which file a node in a
    graph is located.

    This is a lowlevel interface. For details on using the exposed structures the documentation
    in the Cap'n Proto API file.
    """

    graphid_by_filename : dict[Path, int]
    """Map from filenames in the data directory to their graph-id's."""

    graph_files : list[Path]
    """Map's a graph-id to a filename. Inverse of `graphid_by_filename`."""

    def local_to_global(self, graph: int, dep_index: int) -> int:
        """Convert a dependency-index relative to a graph-id to a new graph-id.

        This is used to find the graph-id where a particular node can be found. If `graph` is the
        graph-id that contains a reference to a node and `dep_index` is the relative location
        where that node can be found then `local_to_global(graph, dep_index)` finds the graph-id
        of the file where the node is physically located.
        """
        ...

    def __getitem__(self, graph: int):
        """Retrieve the raw Cap'n Proto structures associated with a graph-id."""
        ...

    def __len__(self) -> int: ...

@contextmanager
def lowlevel_data_reader(dataset_path: Path) -> Generator[LowlevelDataReader, None, None]:
    """Map a directory of dataset files into memory, and expose their raw Cap'n Proto structures.

    Arguments:
    `dataset_path`: Can either be a dataset directory, or a SquashFS image file. In case of an image
                    file `dataset.squ`, the image will be mounted using `squashfuse` on directory
                    `dataset/`, after which the contents of that directory will be read.

    This is a low-level function. Prefer to use `data_reader`. See `LowlevelDataReader` for
    further documentation.
    """
    ...

ProofStateId = int
TacticId = int
GraphId = int
NodeId = int
NodeHash = int

class Node:
    """A node in the calculus of inductive construction graph.

    A node has a `label`, a unique `identity` and `children`. Some nodes are also
    a `Definition`.
    """

    graph : GraphId
    """The id of the graph in which this node occurs. For lowlevel use only."""

    nodeid : NodeId
    """The local id of the node in the dataset. For lowlevel use only."""

    def __repr__(self):
        ...

    def __eq__(self, other: object) -> bool:
        """Physical equality of two nodes. Note that two nodes with a different physical equality
        may have the same `identity`. See `identity` for details.
        """
        ...

    def __hash__(self):
        """A hash that is corresponds to physical equality, not to be confused by `identity`."""
        ...

    @property
    def label(self) -> apic.Graph_Node_Label_Reader:
        """The label of the node, indicating it's function in the CIC graph."""
        ...

    @property
    def identity(self) -> NodeHash:
        """The identity of a node uniquely determines it. That is, one can consider any to nodes with the same
        identity to be equal. The notion of equal we use is as follows:
        1. Graph perspective: Two nodes have the same identity if and only if they are bisimilar.
           In this notion, bisimilarity does take into consideration the label of the nodes, modulo some
           equivalence class that is not fully specified here. One aspect of the equivalence class is that
           for definition nodes their associated global context (accessed through `Definition.previous`) is
           not taken into account.
        2. Lambda calculus perspective: Two nodes have the same identity if their corresponding lambda terms
           are alpha-equivalent. Note that two definitions with the same body are not considered
           alpha-equivalent.

        The identity of a node is used to perform partial graph-sharing. That is, two nodes with the same
        identity are merged when the graph is generated. There are two reasons why two nodes with the same
        semantic identity might have a different physical identity:
        1. Nodes are only merged when the first node exists in the same graph as the second node, or exists
           in a dependent graph. Hence, nodes originating from developments that do not depend on each other
           are never merged. Full graph-sharing would require global analysis on a dataset, which any consumer
           can optionally do as a post-processing step.
        2. Two definition nodes with the same name and body have the same identity. But if they occur in
           different global contexts, these nodes are physically different to ensure the integrity of their
           global contexts.

        Beware that the identity is currently a 64 bit field. For datasets that have graphs of size in the
        order of billions of nodes there is a non-trivial chance of a collision. (We consider this acceptable
        for machine learning purposes.)
        """
        ...

    @property
    def children(self) -> Sequence[tuple[int, Node]]:
        """The children of a node, together with the labels of the edges towards the children.
        Note that for efficiency purposes, the label is represented as an integer. The corresponding
        enum of this integer is `graph_api_capnp.EdgeClassification`."""
        ...

    @property
    def definition(self) -> Definition | None:
        """Some nodes in the CIC graph represent definitions. Such nodes contain extra information about the
        definition.
        """
        ...

class ProofState:
    """A proof state represents a particular point in the tactical proof of a constant."""

    @property
    def lowlevel(self):
        ...
    def __repr__(self):
        ...

    @property
    def root(self) -> Node:
        """The entry-point of the proof state, all nodes that are 'part of' the proof state are
        reachable from here."""
        ...

    @property
    def context(self) -> Sequence[Node]:
        """The local context of the proof state, given as a tuple of their original name as they appeared in the
        proof and the corresponding node.

        The nodes always have either label `contextAssum` or `contextDef`.
        Note that these nodes are also reachable from the root of the proof state.

        The names of the context elements should be used for debugging and viewing purposes only, because
        hypothesis-generating tactics have been modified to use auto-generated names. Hence, tactics should
        not be concerned about the names of the context.
        """
        ...

    @property
    def context_names(self) -> Sequence[str]:
        """The names of the local context nodes of the proof state, as they originally appeared in the proof.

        These names should be used for debugging and viewing purposes only, because hypothesis-generating tactics have
        been modified to use auto-generated names. Hence, tactics should not be concerned about the names of
        the context.
        """
        ...

    @property
    def context_text(self) -> Sequence[str]:
        """A textual representation of the type/definition of context nodes
        """
        ...

    @property
    def conclusion_text(self) -> str:
        """A textual representation of the conclusion of the proof state.
        """
        ...

    @property
    def text(self) -> str:
        """A textual representation of the proof state."""
        ...

    def __str__(self) -> str:
        ...

    @property
    def id(self) -> ProofStateId:
        """
        A unique identifier of the proof state. Any two proof states in a tactical proof that have an equal id
        can morally be regarded to be 'the same' proof state.
        IMPORTANT: Two proof states with the same id may still have different contents. This is because proof states
                   can contain existential variables (represented by the `evar` node) that can be filled as a
                   side-effect by a tactic running on another proof state.
        """
        ...

Unresolvable : TypeAlias = None
Unknown : TypeAlias = None
class Outcome:
    """An outcome is the result of running a tactic on a proof state. A tactic may run on multiple proof states."""

    tactic : apic.Tactic_Reader | Unknown
    """The tactic that generated the outcome. For it's arguments, see `tactic_arguments`

    Sometimes a tactic cannot or should not be recorded. In those cases, it is marked as 'unknown'.
    This currently happens with tactics that are run as a result of the `Proof with tac` construct and it
    happens for tactics that are known to be unsafe like `change_no_check`, `fix`, `cofix` and more.
    """

    @property
    def lowlevel(self):
        ...
    def __repr__(self):
        ...

    @property
    def before(self) -> ProofState:
        """The proof state before the tactic execution."""
        ...

    @property
    def after(self) -> Sequence[ProofState]:
        """The new proof states that were generated by the tactic."""
        ...

    @property
    def term(self) -> Node:
        """The proof term that witnesses the transition from the before state to the after states. It contains a
        hole (an `evar` node) for each of the after states. It may also refer to elements of the local context of
        the before state.
        """
        ...

    @property
    def term_text(self) -> str:
        """A textual representation of the proof term."""
        ...

    @property
    def tactic_arguments(self) -> Sequence[Node | Unresolvable]:
        """The arguments of the tactic that produced this outcome.

        The node is the root of a graph representing an argument that is a term in the calculus of constructions.
        Sometimes, an argument is not resolvable to a term, in which case it is marked as `Unresolvable`.
        """
        ...

class ProofStep:
    """A proof step is the execution of a single tactic on one or more proof states, producing a list of outcomes.
    """

    @property
    def lowlevel(self):
        ...
    def __repr__(self):
        ...

    @property
    def tactic(self) -> apic.Tactic_Reader | Unknown:
        """The tactic that generated the proof step. Note that the arguments of the tactic can be found in the
        individual outcomes, because they may be different for each outcome.

        Sometimes a tactic cannot or should not be recorded. In those cases, it is marked as 'unknown'.
        This currently happens with tactics that are run as a result of the `Proof with tac` construct and it
        happens for tactics that are known to be unsafe like `change_no_check`, `fix`, `cofix` and more.
        """
        ...

    @property
    def outcomes(self) -> Sequence[Outcome]:
        """A list of transformations of proof states to other proof states, as executed by the tactic of the proof
        step
        """
        ...

@dataclass
class Original:
    """Token that signals that a definition is original, as inputted by the
    user."""
    pass

@dataclass
class Discharged:
    """Token that signals that a definition is derived from an original after
    section closing."""

    original: Definition

@dataclass
class Substituted:
    """Token that signals that a definition is derived from an original after
    module functor instantiation."""

    original: Definition

@dataclass
class Inductive:
    """Token that signals that a definition is inductive."""

    representative: Definition
    """The representative of the mutually recursive cluster. For lowlevel use only"""

@dataclass
class Constructor:
    """Token that signals that a definition is a constructor."""

    representative: Definition
    """The representative of the mutually recursive cluster. For lowlevel use only"""

@dataclass
class Projection:
    """Token that signals that a definition is a projection."""

    representative: Definition
    """The representative of the mutually recursive cluster. For lowlevel use only"""

@dataclass
class ManualConstant:
    """Token that signals that a definition was inputted by the user by
    manually inputting a term."""
    pass

@dataclass
class TacticalConstant:
    """Token that signals that a lemma was proved by the user using
    a tactic proof."""

    proof: Sequence[ProofStep]
    """The proof of the lemma."""

@dataclass
class ManualSectionConstant:
    """Token that signals that a constant is a section variable or let-construct."""
    pass

@dataclass
class TacticalSectionConstant:
    """Token that signals that a constant is a section let-construct with a tactic proof."""

    proof: Sequence[ProofStep]
    """The proof of the lemma."""

class Definition:
    """A definition of the CIC, which is either a constant, inductive, constructor, projection or section
    variable. Constants and section variables can have tactical proofs associated to them.
    """

    node : Node
    """The node that is associated with this definition. It holds that
    `definition.node.definition == definition`.
    """

    @property
    def lowlevel(self):
        ...
    def __repr__(self):
        ...

    def __eq__(self, other: object) -> bool:
        """Physical equality of two nodes. Note that two nodes with a different physical equality
        may have the same `identity`. See `identity` for details.
        """
        ...

    def __hash__(self):
        """A hash that is corresponds to physical equality, not to be confused by `identity`."""
        ...

    @property
    def name(self) -> str:
        """The fully-qualified name of the definition. The name should be unique in a particular global context,
        but is not unique among different branches of the global in a dataset.
        """
        ...

    @property
    def previous(self) -> Definition | None:
        """The previous definition within the global context of the current file.

        Note that this is a lowlevel property. Prefer to use `global_context` or `clustered_global_context`.

        The contract on this field is that any definition nodes reachable from the forward closure of the definition
        must also be reachable through the chain of previous fields. An exception to this rule are mutually
        recursive definitions. Those nodes are placed into the global context in an arbitrary ordering.
        """
        ...

    @property
    def external_previous(self) -> Sequence[Definition]:
        """A list of definitions that are the representatives of files other than the current file that are
        part of the global context. This list becomes populated when a `Require` statement occurred right before
        the definition.

        Note that this is a lowlevel property. Prefer to use `global_context` or `clustered_global_context`.
        """
        ...

    def global_context(self, across_files : bool = True, inclusive = False) -> Iterable[Definition]:
        """All of the definitions in the global context when this definition was created.

        Note that this does not include this definition itself, except when the definition is a inductive,
        constructor or projection. Because those are mutually recursive objects, they reference themselves
        and are therefore part of their own global context.

        The resulting iterable is topologically sorted. That is, for any definition in the stream, any
        definition reachable from the forward closure of the definition also exists in the remainder of the
        stream. An exception to this rule are mutually recursive definitions, because no topological sort
        is possible there (see also `clustered_global_context`).

        Arguments:
        * `across_files`: if `False`, outputs only the definitions from the local file, default `True`.
        * `inclusive`: if `True`, outputs also itself, default `False`.
        Note: if it is a self-recursive definition, the `inclusive` argument is ignored, and considered as `True`
        """
        ...

    def clustered_global_context(self, across_files : bool = True, inclusive : bool = False) -> Iterable[list[Definition]]:
        """All of the definitions in the global context when this definition was created, clustered into
        mutually recursive cliques.

        The resulting iterable is topologically sorted. That is, for any definition in the stream, any
        definition reachable from the forward closure of the definition also exists in the remainder of the
        stream.

        Arguments:
        * `across_files`: if `False`, outputs only the definitions from the local file, default `True`.
        * `inclusive`: if `True`, outputs also the cluster of itself, default `False`.
        Note: if it is a self-recursive definition, the `inclusive` argument is ignored, and considered as `True`.
        """
        ...

    @property
    def status(self) -> Original | Discharged | Substituted:
        """
        A definition is either
        (1) an object as originally inputted by the user.
        (2) a definition that was originally defined in a section and has now had the section
            variables discharged into it.
        (3) a definition that was obtained by performing some sort of module functor substitution.
        When a definition is not original, we cross-reference to the definition that it was derived from.
        """
        ...

    @property
    def kind(self) -> Union[Inductive, Constructor, Projection,
                            ManualConstant, TacticalConstant,
                            ManualSectionConstant, TacticalSectionConstant]:
        """The kind of the definition.

        It can be an constant, section constant, inductive, constructor or projection. In case of a constant
        of a constant or section constant, an optional tactical proof can be associated. In case of an inductive,
        constructor or projection, another definition that acts as the representative of the mutually recursive
        cluster of definitions is associated.

        The associated information is low-level. Prefer to use the properties `proof` and `cluster` to access them.
        """
        ...

    @property
    def proof(self) -> Sequence[ProofStep] | None:
        """An optional tactical proof that was used to create this definition."""
        ...

    @property
    def cluster_representative(self) -> Definition:
        """A unique representative of the mutually recursive cluster of definitions this definition is part of.
        If the definition is not mutually recursive, the representative is itself.

        This is a low-level property. Prefer to use the `cluster` property.
        """
        ...

    @property
    def cluster(self) -> Iterable[Definition]:
        """The cluster of mutually recursive definitions that this definition is part of.
        If the definition is not mutually recursive, the cluster is a singleton."""
        ...

    @property
    def type_text(self) -> str:
        """A textual representation of the type of this definition."""
        ...

    @property
    def term_text(self) -> str | None:
        """A textual representation of the body of this definition.
        For inductives, constructors, projections, section variables and axioms this is `None`.
        """
        ...

    @property
    def is_file_representative(self) -> bool:
        """Returns true if this definition is the representative of the super-global context of it's file.
        Se also `Dataset.representative`."""
        ...

class Dataset:
    """The data corresponding to a single Coq source file. The data contains a representation of all definitions
    that have existed at any point throughout the compilation of the source file.
    """

    graph : GraphId
    filename : Path
    """The physical file in which the data contained in this class can be found."""

    @property
    def lowlevel(self):
        ...
    def __repr__(self):
        ...

    @property
    def dependencies(self) -> Sequence[Path]:
        """A list of physical paths of data files that are direct dependencies of this file.

        It is guaranteed that no cycles exist in the dependency relation between files induced by this field.
        """
        ...

    @property
    def representative(self) -> Definition | None:
        """The entry point of the global context of definitions that are available when this file is 'Required' by
        another file. The full global context can be obtained by following the `previous` node of definitions.
        If the compilation unit does not contain any 'super'-global definitions this may be `None`.

        This is a low-level property.
        Prefer to use `definitions(spine_only = True)` and `clustered_definitions(spine_only=True)`.
        """
        ...

    def definitions(self, across_files = False, spine_only = False) -> Iterable[Definition]:
        """All of the definitions present in the file.
        Note that some of these nodes may not be part of the 'super-global' context. Those are definitions inside
        of sections or module functors.

        Arguments:
        * `across_files`: if `True`, outputs also definitions from dependent files, default `False`.
        * `spine_only`: if True, outputs only the definitions on the main spine, default `False`.
        Note: `across_files = True` is incompatible with `spine_only = False`.

        When `spine_only = True`, the resulting iterable is topologically sorted. That is, for
        any definition in the stream, any definition reachable from the forward closure of the definition
        also exists in the remainder of the stream. An exception to this rule are mutually recursive definitions,
        because no topological sort is possible there (see also `clustered_definitions`).
        """
        ...

    def clustered_definitions(self, across_files = False, spine_only = False) -> Iterable[list[Definition]]:
        """All of the definitions present in the file, clustered by mutually recursive definitions.
        Note that some of these nodes may not be part of the 'super-global' context. Those are definitions inside
        of sections or module functors.

        Arguments:
        * `across_files`: if `True`, outputs also definitions from dependent files, default `False`.
        * `spine_only`: if `True`, outputs only the definitions on the main spine, default `False`.
        Note: `across_files = True` is incompatible with `spine_only = False`.

        When `spine_only = True`, the resulting iterable is topologically sorted. That is, for
        any definition in the stream, any definition reachable from the forward closure of the definition
        also exists in the remainder of the stream.
        """
        ...

    @property
    def module_name(self) -> str:
        ...

    def node_by_id(self, nodeid: NodeId) -> Node:
        """Lookup a node inside of this file by it's local node-id. This is a low-level function."""
        ...

def lowlevel_to_highlevel(lreader : LowlevelDataReader) -> dict[Path, Dataset]:
    """Convert a dataset initialized as a `LowLevelDataReader` into a high level interface."""
    ...

@contextmanager
def data_reader(dataset_path: Path) -> Generator[dict[Path, Dataset], None, None]:
    """Load a directory of dataset files into memory, and expose the data they contain.
    The result is a dictionary that maps physical paths to `Dataset` instances that allow access to the data.

    Arguments:
    `dataset_path`: Can either be a dataset directory, or a SquashFS image file. In case of an image
                    file `dataset.squ`, the image will be mounted using `squashfuse` on directory
                    `dataset/`, after which the contents of that directory will be read.

    """
    ...

class OnlineDefinitionsReader:
    """This class represents a global context to Python by Coq, containing all
    known definitions and available tactics."""

    def local_to_global(self, graph: int, dep_index: int) -> int:
        """Convert a dependency-index relative to a graph-id to a new graph-id.

        This is used to find the graph-id where a particular node can be found. If `graph` is the
        graph-id that contains a reference to a node and `dep_index` is the relative location
        where that node can be found then `local_to_global(graph, dep_index)` finds the index in
        the global context stack where the node is physically located.

        Lowlevel function.
        """
        ...

    @property
    def representative(self) -> Definition | None:
        """The last definition in the global context. All other definitions can be accessed by following
        the `Definition.previous` chain starting from this definitions.

        This is a low-level property.
        Prefer to use `definitions` and `clustered_definitions`.
        """
        ...

    def definitions(self, full : bool = True) -> Iterable[Definition]:
        """The list of definitions that are currently in the global context.

        The resulting iterable is topologically sorted. That is, for any definition in the stream, any
        definition reachable from the forward closure of the definition also exists in the remainder of
        the stream. An exception to this rule are mutually recursive definitions,
        because no topological sort is possible there (see also `clustered_definitions`).
        """
        ...

    def clustered_definitions(self, full : bool = True) -> Iterable[list[Definition]]:
        """All of the definitions present in the global context, clustered by mutually recursive definitions.

        The resulting iterable is topologically sorted. That is, for any definition in the stream, any
        definition reachable from the forward closure of the definition also exists in the remainder of
        the stream.
        """
        ...

@contextmanager
def online_definitions_initialize(stack: OnlineDefinitionsReader,
                                  init: apic.PredictionProtocol_Request_Initialize_Reader) -> Generator[OnlineDefinitionsReader, None, None]:
    """Given a new initialization message sent by Coq, construct a
    `OnlineDefinitiosnReader` object. This can be used to inspect the
    definitions currently available. Additionally, using `online_data_predict`
    it can be combined with a subsequent prediction request received from Coq
    to build a `ProofState`.
    """
    ...

def empty_online_definitions_initialize() -> OnlineDefinitionsReader:
    ...

@contextmanager
def online_data_predict(base: OnlineDefinitionsReader,
                        predict: apic.PredictionProtocol_Request_Predict_Reader) -> Generator[ProofState, None, None]:
    """Given a `OnlineDefinitionsReader` instance constructed through
    `online_data_initialize`, and a prediction message sent by Coq, construct a
    `ProofState` object that represents the current proof state in Coq.
    """
    ...

@dataclass
class TacticPredictionGraph:
    ident : int
    arguments : list[Node]
    confidence : float

@dataclass
class TacticPredictionsGraph:
    predictions : list[TacticPredictionsGraph]

@dataclass
class TacticPredictionText:
    tactic_text : str
    confidence : float

@dataclass
class TacticPredictionsText:
    predictions : list[TacticPredictionsText]

@dataclass
class CheckAlignmentMessage:
    pass

@dataclass
class CheckAlignmentResponse:
    unknown_definitions : list[Definition]
    unknown_tactics : list[int]

@dataclass
class GlobalContextMessage:
    """A message containing a new global context sent to Python from Coq,
    including all known definitions and available tactics."""

    definitions : OnlineDefinitionsReader
    tactics : Sequence[apic.AbstractTactic_Reader]

    log_annotation : str
    """An annotation representing the current position of Coq in a source
    document. For logging and debugging purposes."""

    prediction_requests : Generator[GlobalContextMessage | ProofState | CheckAlignmentMessage,
                                    None | TacticPredictionsGraph | TacticPredictionsText | CheckAlignmentResponse,
                                    None]
    """A sub-generator that produces new requests from Coq that are based on or
    extend the global context of the current message. Once the sub-generator
    runs out, the parent generator continues."""

def capnp_message_generator_lowlevel(socket: socket.socket) -> (
        Generator[apic.PredictionProtocol_Request_Reader,
                  capnp.lib.capnp._DynamicStructBuilder, None]):
    """A generator that facilitates communication between a prediction server and a Coq process.

    Given a `socket`, this function creates a generator that yields messages of type
    `pytact.graph_api_capnp_cython.PredictionProtocol_Request_Reader` after which a
    `capnp.lib.capnp._DynamicStructBuilder` message needs to be `send` back.
    """
    ...

def capnp_message_generator_from_file_lowlevel(
        message_file: BinaryIO,
        check : Callable[[Any, Any, Any], None] | None = None) -> (
        Generator[apic.PredictionProtocol_Request_Reader,
                  capnp.lib.capnp._DynamicStructBuilder, None]):
    """Replay and verify a pre-recorded communication sequence between Coq and a prediction server.

    Lowlevel variant of `capnp_message_generator_from_file`.

    Accepts a `message_file` containing a stream of Capt'n Proto messages as recorded using
    `capnp_message_generator(s, record=message_file)`. The resulting generator acts just like the generator
    created by `capnp_message_generator` except that it is not connected to the socket but just replays the
    pre-recorded messages.

    Arguments:
    - `check` is an optional callable that can be used to compare the response of the server to the recorded
      response. It accepts three arguments: The recorded message that was sent by Coq, the response of the server
      and the recorded response.
    """
    ...

def record_lowlevel_generator(
        record_file: BinaryIO,
        gen: Generator[apic.PredictionProtocol_Request_Reader,
                       capnp.lib.capnp._DynamicStructBuilder, None]) -> (
                           Generator[apic.PredictionProtocol_Request_Reader,
                                     capnp.lib.capnp._DynamicStructBuilder, None]):
    """Record a trace of the full interaction of a lowlevel generator to a file

    Wrap a lowlevel generator (such as from `capnp_message_generator_lowlevel`) and dump all exchanged messages
    to the given file. The file can later be replayed with `capnp_message_generator_from_file_lowlevel`.
    """
    ...

def prediction_generator(
        lgenerator: Generator[apic.PredictionProtocol_Request_Reader,
                              capnp.lib.capnp._DynamicStructBuilder, None],
        defs: OnlineDefinitionsReader):
    """Given the current global context stack `defs`, convert a low-level
    generator to a high-level `GlobalContextMessage`"""
    ...

def capnp_message_generator(socket: socket.socket, record: BinaryIO | None = None) -> GlobalContextMessage:
    """A generator that facilitates communication between a prediction server and a Coq process.

    Given a `socket`, this function creates a `GlobalContextMessage` `context`. This message contains an
    initially empty list of available tactics and definitions in the global context. Through
    `context.prediction_requests` one can access a generator that yields prediction requests and expects
    predictions to be sent in response. The possible messages are as follows:
    - `GlobalContextMessage`: An additional, nested, global context message that amends the current context
       with additional tactics and definitions. The prediction requests of this nested context need to be
       exhausted before continuing with messages from the current context.
    - `CheckAlignmentMessage`: A request to check which of Coq's current tactics and definitions the
      prediction server currently "knows about". The generator expects a `CheckAlignmentResponse` to be
      sent in response.
    - `ProofState`: A request to make tactic predictions for a given proof state. Either a
      `TacticPredictionsGraph` or a `TacticPredictionsText` message is expected in return.

    When `record` is passed a file descriptor, all received and sent messages will be dumped into that file
    descriptor. These messages can then be replayed later using `capnp_message_generator_from_file`.
    """
    ...

def capnp_message_generator_from_file(message_file: BinaryIO,
                                      check : Callable[[Any, Any, Any], None] | None = None,
                                      record: BinaryIO | None = None) -> GlobalContextMessage:
    """Replay and verify a pre-recorded communication sequence between Coq and a prediction server.

    Highlevel variant of `capnp_message_generator_from_file_lowlevel`.

    Accepts a `message_file` containing a stream of Capt'n Proto messages as recorded using
    `capnp_message_generator(s, record=message_file)`. The resulting generator acts just like the generator
    created by `capnp_message_generator` except that it is not connected to the socket but just replays the
    pre-recorded messages.

    Arguments:
    - `check` is an optional callable that can be used to compare the response of the server to the recorded
      response. It accepts three arguments: The recorded message that was sent by Coq, the response of the server
      and the recorded response.
    - `record` is an optional file that re-records the interaction with the current server
    """
    ...

class GlobalContextSets:
    """Lazily retrieve a the global context of a definition as a set, with memoization.

    Because this class can allocate (large) amounts of memory, use it as a context-manager. To create a new
    instance, and retrieve the context of a definition, use:
    ```
    with GlobalContextSets.new_context() as gcs:
        gcs.global_context_set(my_definition)
    ```
    This context will be cached, as well as intermediate results (global contexts of other definitions) as
    long as the context-set is in scope. Caching can be nested by using `sub_context`:
    ```
    with GlobalContextSets.new_context() as gcs:
        gcs.global_context_set(my_definition)
        with gcs.sub_context(lambda d:is_file_representative) as gcs_sub:
            # gcs_sub remembers anything in the case of gcs
            # caching is propagated to the parent cache only if the provided lambda evaluates to true
            gcs_sub.global_context_set(my_definition2)
    ```
    """
    def __init__(self, cache, parent: GlobalContextSets | None,
                 should_propagate: Callable[[Definition], bool]):
        """Do not call directly. Use `GlobalContextSets.new_context` and `GlobalContextSets.sub_context`."""
        ...

    def global_context_set(self, d: Definition) -> Map:
        """Retrieve the global context of a definition, caching the result, and intermediate results."""
        ...

    @contextmanager
    def sub_context(self, propagate: Callable[[Definition], bool]) -> Generator[GlobalContextSets, None, None]:
        """Create a sub-context with a separate cache from it's parent, but sharing any info that was
        already present in the parent's cache.

        For any intermediate results for a definition `d` for which `propagate(d)` evaluates to true,
        the result is propagated to the parent's cache."""
        ...

    @staticmethod
    def new_context() -> Generator[GlobalContextSets, None, None]:
        """Crate a new caching context where global-context-set's can be retrieved and cached."""
        ...

def node_dependencies(n: Node, deps: set[Definition] | None = None) -> set[Definition]:
    """Given a `Node` `n`, calculate the set of `Definition`'s that are directly reachable
    from `n`. Transitively reachable definitions are not included.
    """
    ...

def definition_dependencies(d: Definition) -> set[Definition]:
    """Given a `Definition` `d`, calculate the set of `Definition`'s that are directly reachable for `d`.
    Transitively reachable definitions are not included nor is `d` itself.
    """
    ...
