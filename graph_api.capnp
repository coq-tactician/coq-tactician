@0xfe647bf3a7fdcc2f;

######################################################################################################
#
#               Tactician Graph Encoding Schema File
#
# This file currently serves three different purposes, each with a different entry-point:
#
# 1. A schema for graph-based dataset exported from Coq. The entry-point for this is the `Dataset`
#    struct. That is, every file in the dataset contains a message conforming to this struct.
#
# 2. A communication protocol for proof synthesis with Tactician. There are two protocols for this:
#    - A simple, linear message exchange protocol, specified by the `PredictionProtocol` struct.
#    - An RPC based protocol, specified by the `PredictionServer` interface.
#
# 2. A communication protocol for proof exploration by a client. Proof exploration is started through
#    the `explore` function of the `PredictionServer` interface.
#
#
# All these three entry-points share a common base, which encodes the notion of graphs, terms,
# tactics and more.
#
######################################################################################################


######################################################################################################
#
#             Type aliases
#
######################################################################################################

using File = Text;
# The URI of a file in a dataset, relativized w.r.t. the root of the dataset

using NodeIndex = UInt32;
# A `NodeIndex` is the identity of a node in a graph
using DepIndex = UInt16;
# A `DepIndex` comes together with a `NodeIndex` and indicates to which graph a node belongs.
# How a dependency index should be resolved to a graph is not specified here. However, a
# dependency index of zero always refers to the 'current' graph.

using NodeIdentity = Int64;

using TacticId = Int64;
using ProofStateId = UInt32; # Note, proof state ids are only unique within their own proof
using ProofStateIdP = IntP; # Same as ProofStateId, except wrapped into a pointer
# Tactics, definitions and proof states are identified by hashes


######################################################################################################
#
#             Common datastructures
#
######################################################################################################

struct Graph {
  # A graph is the main data store (the 'heap') that contains the bulk of the data in the dataset and
  # during communication with Coq. A graph is a collection of labeled nodes with directed, labeled edges
  # between them. A graph may reference nodes from other graphs. For an edge 'A --> B' in the graph it
  # always holds that 'A' is part of the current graph, but 'B' may (or may not) be part of another graph.

  struct EdgeTarget { # Fits exactly in 64 bits. Let's keep it that way.
    # The 'pointy' end of an edge, together with the label of that edge.

    label @0 :EdgeClassification;
    target :group {
      depIndex @1 :DepIndex;
      # Indicates to which graph a node belongs. How this should be resolved is not specified here.
      # However, a value of zero always points to the 'current' graph.

      nodeIndex @2 :NodeIndex;
      # The index into `Graph.nodes` where this node can be found.
    }
  }

  struct Node { # Fits exactly in 128 bits.
    # A node has a label that optionally contains some additional information, together with a list of
    # outgoing edges (children).

    label :union { # Inlined for efficiency purposes
      # Proof state
      # Has a unique id (evar) for the proof state that distinquishes proof states with identical
      # contents but do not point to the same object nonetheless
      proofState @0 :ProofStateIdP;

      # Context
      contextDef @1 :Void;
      contextAssum @2 :Void;

      # Definitions
      definition @3 :Definition;
      constEmpty @4 :Void;

      # Sorts
      sortSProp @5 :Void;
      sortProp @6 :Void;
      sortSet @7 :Void;
      sortType @8 :Void; # Collapsed universe

      # Constr nodes
      rel @9 :Void;
      evar @10 :Void;
      evarSubst @11 :Void;
      cast @12 :Void;
      prod @13 :Void;
      lambda @14 :Void;
      letIn @15 :Void;
      app @16 :Void;
      case @17 :Void;
      caseBranch @18 :Void;
      fix @19 :Void;
      fixFun @20 :Void;
      coFix @21 :Void;
      coFixFun @22 :Void;

      # Primitives
      int @23 :IntP;
      float @24 :FloatP;
      primitive @25 :Text;
    }

    childrenIndex @26 :UInt32;
    childrenCount @27 :UInt16;
    # The children of a node are encoded as a range withing the `edges`-list of the graph.

    identity @28 :NodeIdentity;
    # The identity of a node uniquely determines it. That is, one can consider any to nodes with the same
    # identity to be equal. The notion of equal we use is as follows:
    # 1. Graph perspective: Two nodes have the same identity if and only if they are bisimilar.
    #    In this notion, bisimilarity does take into consideration the label of the nodes, modulo some
    #    equivalence class that is not fully specified here. One aspect of the equivalence class is that
    #    for definition nodes their associated global context (accessed through `Definition.previous`) is
    #    not taken into account.
    # 2. Lambda calculus perspective: Two nodes have the same identity if their corresponding lambda terms
    #    are alpha-equivalent. Note that two definitions with the same body are not considered
    #    alpha-equivalent.
    #
    # The identity of a node is used to perform partial graph-sharing. That is, two nodes with the same
    # identity are merged when the graph is generated. There are three reasons why two nodes with the same
    # semantic identity might have a different physical identity:
    # 1. Nodes are only merged when the first node exists in the same graph as the second node, or exists
    #    in a dependent graph. Hence, nodes originating from developments that do not depend on each other
    #    are never merged. Full graph-sharing would require global analysis on a dataset, which any consumer
    #    can optionally do as a post-processing step.
    # 2. Two definition nodes with the same name and body have the same identity. But if they occur in
    #    different global contexts, these nodes are physically different to ensure the integrity of their
    #    global contexts.
    # 3. For definitions with an opaque proof, the sub-graph that represents this opaque proof is ignored
    #    while calculating the identity. Morally we defend this decision with the concept that opaque proofs
    #    are invisible in Coq (proof irrelevance) and two constants with different proofs might as well be
    #    considered equal. Practically speaking, this is done so that one can compare the identity of a
    #    definition in a dataset quickly to a identity of a live definition during Coq interaction without
    #    having to produce the entire graph of opaque proofs (which tend to be large).
    #
    # Beware that the identity is currently a 64 bit field. For datasets that have graphs of size in the
    # order of billions of nodes there is a non-trivial chance of a collision. (We consider this acceptable
    # for machine learning purposes.)
  }

  nodes @0 :List(Node);
  edges @1 :List(EdgeTarget);
  # The main memory store of the graph. It acts as a heap similar to the main memory of a C/C++ program.
  # The heap is accessed by indexing the `nodes` list using a `NodeIndex` which returns a `Node`.
  # Every node has a label and a list of children, which is indicated as a range within the `edges` list using
  # `childrenIndex` and `childrenCount`. The targets of the edges can again be found in the `nodes` list of the
  # current file or of a dependency.
  # Note that just like in C/C++ doing pointer arithmetic on the heap is undefined behavior, and you may
  # encounter arbitrary garbage if you do this. In particular, iterating over the heap is discouraged.
  # Instead, you should access the heap through various entry-points that are provided.
}

struct AbstractTactic {
  ident @0 :TacticId;
  # An abstract tactic is referenced to using a identifier (hash).

  parameters @1 :UInt8;
  # Every tactic has a constant number of parameters that need to be filled in.
}

struct Tactic {
  # A concrete tactic with it's parameters determined. Somewhat strangely, this struct does not actually include
  # these parameters. They can instead be found in `Outcome.tacticArguments`. The reason for this is that one
  # tactic can run on multiple proof states at the same time and for all of those proof states, the arguments
  # may be resolved differently.

  ident @0 :TacticId;
  # A hash representing the identity of a tactic without it's arguments. Due to the complexity of the syntax
  # trees of Coq's tactics, we do not currently encode the syntax tree. Instead, this hash is a representative
  # of the syntax tree of the tactic with all of it's arguments removed.

  text @1 :Text;
  # The full text of the tactic including the full arguments. This does not currently correspond to
  # (ident, arguments) because in this dataset arguments do not include full terms, but only references to
  # definitions and local context elements. Tactics are postprocessed to remove explicit naming of new
  # hypotheses as much as possible, and instead asking Coq to invent a name.

  textNonAnonymous @5 :Text;
  # Same as `text` except that the tactic is not postprocessed to remove explicit naming of new hypotheses.

  baseText @2 :Text;
  # A textual representation of the base tactic without arguments. It tries to roughly correspond to `ident`.
  # Note, however, that this is both an under-approximation and an over-approximation. The reason is that tactic
  # printing is not 100% isomorphic to Coq's internal AST of tactics. Sometimes, different tactics get mapped to
  # the same text. Conversely, the same tactic may be mapped to different texts when identifiers are printed
  # using different partially-qualified names.

  intermText @3 :Text;
  # A textual representation that tries to come as close as possible to (ident, arguments).
  # It comes with the same caveats as `baseText`.

  exact @4 :Bool;
  # Indicates whether or not `ident` + `arguments` is faithfully reversible into the original "strictified" tactic.
  # Note that this does not necessarily mean that it represents exactly the tactic that was inputted by the user.
  # All tactics are modified to be 'strict' (meaning that tactics that have delayed variables in them break).
  # This flag measures the faithfulness of the representation w.r.t. the strict version of the tactic, not the
  # original tactic inputted by the user.
}

struct Argument {
  # A concrete argument of a tactic.
  union {
    unresolvable @0 :Void;
    # An argument that is currently unresolvable due to limitations of the extraction process.

    term :group {
      # The root of a graph representing an argument that is a term in the calculus of constructions.

      depIndex @1 :DepIndex;
      # Indicates to which graph a node belongs. How this should be resolved is not specified here.
      # However, a value of zero always points to the 'current' graph.

      nodeIndex @2 :NodeIndex;
      # The index into `Graph.nodes` where this node can be found.
    }
  }
}

struct Node {
  # A node in the CIC graph

  depIndex @0 :DepIndex;
  # Indicates to which graph a node belongs. How this should be resolved is not specified here.
  # However, a value of zero always points to the 'current' graph.

  nodeIndex @1 :NodeIndex;
  # The index into `Graph.nodes` where this node can be found.
}

struct ProofState {
  # A proof state represents a particular point in the tactical proof of a constant.

  root :group {
    # The entry-point of the proof state, all nodes that are 'part of' the proof state are reachable from here.

    depIndex @0 :DepIndex;
    # Indicates to which graph a node belongs. How this should be resolved is not specified here.
    # However, a value of zero always points to the 'current' graph.

    nodeIndex @1 :NodeIndex;
    # The index into `Graph.nodes` where this node can be found.
  }


  context @2 :List(Node);
  # The local context of the proof state. These nodes label's are either `contextAssum` or `contextDef`. Note that
  # these nodes are also reachable from the root of the proof state.

  contextNames @3 :List(Text);
  # The names of the local context nodes of the proof state, as they originally appeared in the proof.
  # These names should be used for debugging and viewing purposes only, because hypothesis-generating tactics have
  # been modified to use auto-generated names. Hence, tactics should not be concerned about the names of
  # the context.

  contextText @4 :List(Text);
  # A textual representation of the type/definition of context nodes

  conclusionText @5 :Text;
  # A textual representation of the conclusion of the proof state.

  text @6 :Text;
  # A textual representation of the proof state.

  id @7 :ProofStateId;
  # A unique identifier of the proof state. Any two proof states in a tactical proof that have an equal id
  # can morally be regarded to be 'the same' proof state.
  # IMPORTANT: Two proof states with the same id may still have different contents. This is because proof states
  #            can contain existential variables (represented by the `evar` node) that can be filled as a
  #            side-effect by a tactic running on another proof state.
  # TODO: This is currently duplicated with the id attached to the `ProofState` node that `root` points to.
  #       Eventually, this id should be resolved to a NodeIndex that represents the location of this proof state
  #       in the final proof term that was generated.
}

struct Outcome {
  # An outcome is the result of running a tactic on a proof state. A tactic may run on multiple proof states.

  before @0 :ProofState;
  # The proof state before the tactic execution.

  after @1 :List(ProofState);
  # The new proof states that were generated by the tactic.

  term :group {
    # The proof term that witnesses the transition from the before state to the after states. It contains a hole
    # (an `evar` node) for each of the after states. It may also refer to elements of the local context of the
    # before state.

    depIndex @2 :DepIndex;
    # Indicates to which graph a node belongs. How this should be resolved is not specified here.
    # However, a value of zero always points to the 'current' graph.

    nodeIndex @3 :NodeIndex;
    # The index into `Graph.nodes` where this node can be found.
  }

  termText @4 :Text;
  # A textual representation of the proof term.

  tacticArguments @5 :List(Argument);
  # The arguments of the tactic that produced this outcome. Note that these arguments belong to the tactic in
  # `ProofStep.tactic`.
}

struct ProofStep {
  # A proof step is the execution of a single tactic on one or more proof states, producing a list of outcomes.

  tactic :union {
    # The tactic that generated the proof step. Note that the arguments of the tactic can be found in the
    # individual outcomes, because they may be different for each outcome.

    unknown @0 :Void;
    # Sometimes a tactic cannot or should not be recorded. In those cases, it is marked as 'unknown'.
    # This currently happens with tactics that are run as a result of the `Proof with tac` construct and it
    # happens for tactics that are known to be unsafe like `change_no_check`, `fix`, `cofix` and more.

    known @1 :Tactic;
    # The tactic
  }

  outcomes @2 :List(Outcome);
  # A list of transformations of proof states to other proof states, as executed by the tactic of the proof step
}

struct Definition {
  # A definition of the CIC, which is either an constant, inductive, constructor, projection or section
  # variable. Constants and section variables can have tactical proofs associated to them.

  name @0 :Text;
  # The fully-qualified name of the definition. The name should be unique in a particular global context,
  # but is not unique among different branches of the global in a dataset.

  previous @1 :NodeIndex;
  # The previous definition within the global context of the current file.
  # For the first definition this field is set to `len(graph.nodes)`.
  # The contract on this field is that any definition nodes reachable from the forward closure of the definition
  # must also be reachable through the chain of previous fields. An exception to this rule are mutually
  # recursive definitions. Those nodes are placed into the global context in an arbitrary ordering.

  externalPrevious @2 :List(DepIndex);
  # This field provides information about the external global context.
  # At any point in a source file other files 'X' can be loaded through 'Require X'. When this happens, the
  # definitions of X that are reachable through its 'representative' field become available to all subsequent
  # definitions.

  status :union {
    # A definition can have different origins, which are encoded here

    original @3 :Void;
    # An object as originally inputted by the user.

    discharged @4 :NodeIndex;
    # a definition that was originally defined in a section and has now had the section
    # variables discharged into it. The node index references the original definition.

    substituted :group {
      # A definition that was obtained by performing some sort of module functor substitution.
      # We reference the original definition.

      depIndex @5 :DepIndex;
      # Indicates to which graph a node belongs. How this should be resolved is not specified here.
      # However, a value of zero always points to the 'current' graph.

      nodeIndex @6 :NodeIndex;
      # The index into `Graph.nodes` where this node can be found.
    }
  }

  union {
    # The kind of the definition.

    inductive @7 :NodeIndex;
    constructor @8 :NodeIndex;
    projection @9 :NodeIndex;
    # These definitions are part of a mutually recursive cluster. They hold a reference to another definition
    # that acts as the 'representative' of the mutually recursive cluster. The representative is chosen such
    # that all definitions of the cluster are reachable through its `previous` pointer. Additionally, all
    # definitions within the cluster have the same representative, and no definitions that are not part of the
    # cluster are interleaved within the chain of `previous` nodes.

    manualConstant @10 :Void;
    # A constant defined by directly inputting a term
    # In the future, we might augment such constants with tactical
    # refinement proofs that build the term iteratively.

    tacticalConstant @11 :List(ProofStep);
    # A constant that was either directly or indirectly generated by a tactical proof.
    # Note that for non-original constants, the proof step sequence may not be very accurate.

    manualSectionConstant @12 :Void;
    # A section variable or local section definition.

    tacticalSectionConstant @13 :List(ProofStep);
    # Local section definitions can also be defined using a tactical proof.
  }

  typeText @14 :Text;
  # A textual representation of the type of this definition.

  termText @15 :Text;
  # A textual representation of the body of this definition.
  # For inductives, constructors, projections, section variables and axioms the string is empty.
}

struct DataVersion {
  # Version info for the data schema. A version `x.y` has a major component and a minor component.
  # The major component `x` will be incremented to `x+1` when there are incompatible changes in the
  # schema that affect the `Dataset` struct.
  # The minor component `y` will be incremented to `y+1` when there are incompatible changes in the
  # communication protocol with Coq, but the dataset format remains unaffected.

  major @0 :Int64;

  minor @1 :Int64;
}

const currentVersion :DataVersion = ( major = 16, minor = 0 );


######################################################################################################
#
#             The schema for the dataset
#
######################################################################################################

struct Dataset {
  # Every file in the dataset contains a single message of type `Dataset`. Every file corresponds to
  # a Coq source file, and contains a representation of all definitions that have existed at any point
  # throughout the compilation of the source file.

  dataVersion @5 :DataVersion;
  # The version of the data stored in this dataset.

  dependencies @0 :List(File);
  # The graph contained in a file may reference nodes from the graph of other files. This field maps
  # a `DepIndex` into the a file that contains that particular node.
  # The first file in this list is always the current file. It is guaranteed that no cycles exist in
  # the dependency relation between files induced by this field (except for the self-reference of the file).

  graph @1 :Graph;

  representative @2 :NodeIndex;
  # The entry point of the global context of definitions that are available when this file is 'Required' by
  # another file. The full global context can be obtained by following the `previous` node of definitions.
  # If the compilation unit does not contain any 'super'-global definitions this is set to `len(graph.nodes)`

  definitions @3 :List(NodeIndex);
  # All of the definitions present in the graph.
  # Note that some of these nodes may not be part of the 'super-global' context that is reachable using the
  # `representative` field as an entry point. The reason is that the global context is a forest (list of tree's)
  # and the 'super-global' context is only the main spine of this forest.

  moduleName @4 :Text;
  # The name of the module defined by this file.
}


######################################################################################################
#
#             The schema for interacting through basic messages
#
######################################################################################################

struct GlobalContextAddition {
    # Start a context for making tactical predictions for proof search. The context includes the tactics
    # that are currently available, the definitions that are available.

    dataVersion @0 :DataVersion;
    # TODO: Move to a handshake message
    # The version number this message and subsequent messages is compatible with.

    stackSize @1 :Int32;
    # GlobalContextAddition messages can depend on previously sent GlobalContextAddition messages. These
    # messages form a stack. This field indicates the size of the stack that this message depends on (if
    # a message has no dependencies, this field is zero). If the current stack is larger than the stack
    # size of this message, then the items excess items on the stack should be discarded before adding
    # the current message to the stack. It is guaranteed that the excess items will never be referenced
    # again.
    #
    # The dependency indices of nodes contained in the graphs of the stack are indexed as follows:
    # A dependency index `i` found in the graph at stack height `j` is resolved to the graph at stack height
    # `j - i`. (This scheme keeps the guarantee that dependency index `0` always points to the current graph.)

    tactics @2 :List(AbstractTactic);
    # TODO: Move to a separate message
    # A list of tactics that Coq currently knows about.

    graph @3 :Graph;
    # The graph of this message. See `stackSize` on how to resolve dependency indexes in this graph.

    logAnnotation @4 :Text;
    # An annotation containing file and line information on where Coq is currently processing.

    representative @5 :NodeIndex;
    # Points to the last definition of the global context. All other definitions can be accessed by following
    # the `Definition.previous` chain starting from this definition. If the global context is empty
    # this is equal to `len(graph.nodes)`.
}

struct PredictionRequest {
  # Request a list of tactic predictions given the graph of a proof state.

  graph @0 :Graph;
  # The graph may reference definitions present in the stack of initialize messages. See
  # `GlobalContextAddition.stackSize` on how dependency indices can be resolved to a graph in the stack.

  state @1 :ProofState;
  # The proof state for which a prediction is requested.
}

struct Prediction {
  tactic @0 :Tactic;
  arguments @1 :List(Argument);
  confidence @2 :Float64;
}
struct TextPrediction {
  tacticText @0 :Text;
  confidence @1 :Float64;
}

struct PredictionProtocol {
  # This protocol works by exchanging raw messages over a socket. The protocol is fully linear.
  # Coq sends a `Request` and waits for a corresponding `Response` message. A message of a given
  # type should be responded with using the obviously corresponding response type.

  struct Request {
    union {
      initialize @0 :GlobalContextAddition;
      predict @1 :PredictionRequest;
      checkAlignment @2 :Void;
      # Request for the server to align the given tactics and definition to it's internal knowledge
      # and report back any tactics and definitions that were not found
    }
  }
  struct Response {
    # See Request for documentation.
    union {
      initialized @0 :Void;
      prediction @1 :List(Prediction);
      textPrediction @2 :List(TextPrediction);
      # Output is a list of predictions with a confidence. The list is expected to be
      # sorted by decreasing confidence.

      alignment :group {
        unalignedTactics @3 :List(TacticId);
        unalignedDefinitions @4 :List(Node);
      }
    }
  }
}


######################################################################################################
#
#             The schema for RPC-based interaction
#
######################################################################################################

struct Exception {
  # A list of things that can go wrong.
  union {
    noSuchTactic @0 :Void;
    mismatchedArguments @1 :Void;
    parseError @2 :Void;
    illegalArgument @3 :Void;
  }
}

struct ExecutionResult {
  # The result of executing a tactic on a proof state.

  union {
    failure @0 :Void;
    # The tactic execution failed. This is not an error condition, but rather the natural failure of the tactic.

    complete @1 :Void;
    # The proof has been completed.

    newState :group {
      # The tactic ran successfully and produced a new proof state.
      graph @2 :Graph;
      state @3 :ProofState;
      obj @4 :ProofObject;
      # The proof object can be used to run subsequent tactics on the new proof state.
    }

    protocolError @5 :Exception;
    # Indicates a programmer error.
  }
}

interface ProofObject {
  # Represents a single proof object (usually part of ExecutionResult) on which tactics can be executed.

  runTactic @0 (tactic: Tactic, arguments: List(Argument)) -> (result: ExecutionResult);
  runTextTactic @1 (tactic :Text) -> (result: ExecutionResult);
  # Run a tactic on the proof state. This function can be called repeatedly, and the given tactic will always be
  # executed on the same proof state.
}

interface PredictionServer {
  addGlobalContext @0 GlobalContextAddition -> ();
  requestPrediction @1 PredictionRequest -> (predictions :List(Prediction));
  requestTextPrediction @2 PredictionRequest -> (predictions :List(TextPrediction));
  checkAlignment @3 () -> (unalignedTactics :List(TacticId), unalignedDefinitions :List(Node));
  explore @4 (result :ExecutionResult);
  # An interface allowing a proof exploration session to be initiated by Coq. In this case, Coq decides
  # what lemma should be proved and immediately presents the agent with the initial execution result.
}


######################################################################################################
#
#             Common datastructures that are too long, cumbersome, and uninteresting
#             to put at the beginning of this file.
#
######################################################################################################

# Used for in-mermory space optimization. This allows us to make structs smaller by reusing space in
# the pointer section of a struct that would otherwise be allocated in the data section.
struct FloatP {
  value @0 :Float64;
}
struct IntP {
  value @0 :UInt64;
}

enum EdgeClassification {
  # Contexts
  contextElem @0;
  contextSubject @1;

  # Context elements
  contextDefType @2;
  contextDefTerm @3;

  # Constants
  constType @4;
  constUndef @5;
  constDef @6;
  constOpaqueDef @7;
  constPrimitive @8;

  # Inductives
  indType @9;
  indConstruct @10;
  indProjection @11;
  projTerm @12;
  constructTerm @13;

  # Casts
  castTerm @14;
  castType @15;

  # Products
  prodType @16;
  prodTerm @17;

  # Lambdas
  lambdaType @18;
  lambdaTerm @19;

  # LetIns
  letInDef @20;
  letInType @21;
  letInTerm @22;

  # Apps
  appFun @23;
  appArg @24;

  # Cases
  caseTerm @25;
  caseReturn @26;
  caseBranchPointer @27;
  caseInd @28;

  # CaseBranches
  cBConstruct @29;
  cBTerm @30;

  # Fixes
  fixMutual @31;
  fixReturn @32;

  # FixFuns
  fixFunType @33;
  fixFunTerm @34;

  # CoFixes
  coFixMutual @35;
  coFixReturn @36;

  # CoFixFuns
  coFixFunType @37;
  coFixFunTerm @38;

  # Back pointers
  relPointer @39;

  # Evars
  evarSubstPointer @40;
  evarSubstTerm @41;
  evarSubstTarget @42;
  evarSubject @43;
}

# Struct is needed to work around
# https://github.com/capnproto/capnp-ocaml/issues/81
struct ConflatableEdges {
  conflatable @0 :List(EdgeClassification);
}
const conflatableEdges :List(ConflatableEdges) =
[ ( conflatable = [contextDefType, constType, indType, castType, prodType, lambdaType, letInType, fixFunType, coFixFunType] )
, ( conflatable = [contextDefTerm, castTerm, prodTerm, lambdaTerm, letInTerm, fixFunTerm, coFixFunTerm] )
# Not conflatable: projTerm, constructTerm, caseTerm, cBTerm
];
const importantEdges :List(EdgeClassification) =
[ contextElem, contextSubject, contextDefType, contextDefTerm, constType, constDef, constOpaqueDef, indType, indConstruct, indProjection, constructTerm
, prodType, prodTerm, lambdaType, lambdaTerm, letInDef, letInType, letInTerm, appFun, appArg, relPointer ];
const lessImportantEdges :List(EdgeClassification) =
[ caseTerm, caseReturn, caseBranchPointer, caseInd, cBConstruct, cBTerm, fixMutual, fixReturn, fixFunType, fixFunTerm ];
const leastImportantEdges :List(EdgeClassification) =
[ constUndef, constPrimitive, projTerm, castTerm, castType, coFixReturn, coFixFunType, coFixFunTerm
, coFixMutual, evarSubstPointer, evarSubstTerm, evarSubstTarget ];

# WARNING: DO NOT USE
# This is just for visualization purposes in order to drastically reduce the number of edges. You should not use it in networks
const groupedEdges :List(ConflatableEdges) =
[ ( conflatable = [contextElem, contextSubject] )
, ( conflatable = [contextDefType, contextDefTerm] )
, ( conflatable = [constType, constUndef, constDef, constOpaqueDef, constPrimitive] )
, ( conflatable = [indType, indConstruct, indProjection] )
, ( conflatable = [projTerm] )
, ( conflatable = [constructTerm] )
, ( conflatable = [castType, castTerm] )
, ( conflatable = [prodType, prodTerm] )
, ( conflatable = [lambdaType, lambdaTerm] )
, ( conflatable = [letInDef, letInTerm, letInType] )
, ( conflatable = [appFun, appArg] )
, ( conflatable = [caseTerm, caseReturn, caseBranchPointer, caseInd] )
, ( conflatable = [cBConstruct, cBTerm] )
, ( conflatable = [fixMutual, fixReturn] )
, ( conflatable = [fixFunType, fixFunTerm] )
, ( conflatable = [coFixMutual, coFixReturn] )
, ( conflatable = [coFixFunType, coFixFunTerm] )
, ( conflatable = [relPointer] )
, ( conflatable = [evarSubject, evarSubstPointer] )
, ( conflatable = [evarSubstTerm, evarSubstTarget] )
];
