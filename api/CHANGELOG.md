# v15
Changes to the graph
- Fix a bug in the graph sharing algorithm. This causes the identity hash of nodes to be different from v14
- Proof states are now properly discharged at section end, instead of just a copy of the proof state
  inside of the section
- Improve the decomposition of the `destruct` and `induction` tactics
- Tactic identifiers have been changed to use a better hash function. The old hash function produced collisions.

Changes to the Capn'proto format:
- All `evar` nodes are now properly resolved towards a `proofState` node, even when that proof state is
  never solved using a tactic but rather through unification. This changes makes the `undefProofState` node
  redundant, and as such it has been removed.
- Moved the `ProofStateId` identifier of the `evar` node to the `proofState` node. This is a unique
  identifier to distinquish existential variables that have the same proof state but not the same identity.
  Note that this id is not currently taken into account in the graph sharing algorithm because it is too
  non-deterministic during proof search. This is a known deficiency.

Changes to the communication protocol:
- The global context can now be cached through the command `Tactician Neural Cache`. This command can be
  repeated multiple times and creates a stack of updated global context messages.

# v14
Changes to the Capn'proto format:
- Upgraded magic id to v14
- Introduced runtime version information to the format. This allows us to check if the version of a dataset
  conforms to the version of a library that is trying to read it. Version information is also transmitted
  by Coq to the prediction server.

Changes to the graph:
- Add any primitive projection definitions part of an inductive to the children of that inductive. This is
  mostly done because it simplifies the graph sharing algorithm and prevents some subtle bugs. This introduces
  a new edge-type `indProjection`.
- While calculating the hash of nodes, children reachable through a `constOpaqueDef` edge are now ignored.
  This allows us to compare hashes of definitions between the dataset and new definitions in Coq without
  having to calculate the full graph of opaque proof terms (which tends to be rather large).
- Add a non-anonymized version of the the string of a tactic. This is useful for oracles and possibly
  some language models.

# v13

Changes to the Capn'proto format:
- Upgraded magic id to v13
- Added a backwards-compatible field `Dataset.moduleName`
- Added a textual representation of hypothesis in `ProofState.contextText`.
- Added the `ProofStateId` to `evar` nodes, which can be cross-referenced with `ProofState.id`.

Changes to the graph:
- Fixed a bug in graph-sharing, where local context elements where shared based on a reversed index.
- The physical location of a node is now determined by the calculation of a physical hash that includes
  the global context of that node.
- The physical location of nodes now also includes a hash of the file of that node. This is needed
  because files may have diamond dependencies. This can cause two nodes that are physically equal to
  be located in two unrelated dependencies, violating the contract of having only one hash for one node.
  Adding the file to the hash resolves this.

# v12

Changes to the Capn'proto format:
- Upgraded magic id to v12
- Added the field `Graph.Node.identity`, which represents an identity of of any node in the graph
- Removed the field `Definition.hash`, which is now superseded by `Graph.Node.identity`.
- Make some node references that used to reference local nodes only global (consequence of node sharing)
- Inductives, constructors and projections now carry information about the mutually recursive cluster
  they are part of

Changes to the graph:
- Application nodes are now curried in favor of the previous uncurried approach. This choice was
  made for multiple reasons:
  1. Due to the graph sharing in this release, uncurried application nodes can look strange because
     part of the application structure can be shared between separate applications. Although this is
     not incorrect, it is certainly somewhat unexpected.
  2. Because of the ordering edges needed between arguments in the uncurried approach, the graph is
     a DAG in places where normally a tree (with backedges) would be expected. Particularly, this happens
     inside strongly connected components. This is problematic for the graph sharing algorithm because
     unfolding a DAG into a tree leads to exponential blowup. This is a problem in size calculations of
     terms, causing integer overflows. To avoid an exponential blowup in the uncurried form, the
     complexity of the sharing algorithm is O(n log n log n) which could otherwise be O(n log n).

  A downside of the curried approach is that the graph has now become deeper. That is, the primary
  function of an application with many arguments is now fairly deep in the tree.
- Proof state assumption no longer carry their name, because this clashes with the sharing algorithm,
  which does not use the name (it uses index instead). Names of assumptions are now encoded in
  `ProofState.contextNames` struct.
- A bug was fixed that caused fixpoints that had additional binders in scope to resolve de Bruijn
  indices wrong.
- Definitions that are not original, but are discharged from a section of substituted from a module
  functor are now ordered in the global context in the same order as their original counterparts.

Memory layout changes:
- With the help of `Graph.Node.identity`, nodes with the same identity are now shared in the dataset.

Some statistics on the number of nodes and edges in different variations of sharing:
- v11: nodes 259685547 edges 503759399
- v12 unshared uncurried: nodes 259727629 edges 503838873
- v12 unshared with currying: nodes 157953135 edges 294678745
- v12 sharing within definitions only and currying: nodes 22751158 edges 50097138
- v12 sharing within files and currying: nodes 20458599 edges 45496760
- v12 sharing within dependencies and currying: nodes 18343407 edges 40848033

# stdlib-lgraph-intermediate-v11-global

Changes to the Capn'proto format:
- Upgraded magic id to v11
- The first definition in a file now has it's `previous` field set to `len(graph.nodes)`. Previously,
  the field was set to point to the definition itself.
- Fixed a bug that caused internal definitions and subproofs generated by the `abstract` tactic to become
  duplicated. This reduces the total definitions from 73873 to 73595.
  
Memory layout changes:

These changes modify the ordering in which nodes and edges are placed in their storage array. It's purpose is
to improve the locality of reference within the dataset. This should improve speeds when reading small parts of
the dataset using `mmap` due to improved caching (both in RAM and CPU caches) and pre-fetch predictability.
None of these changes break the public API of the format. The only observable change is a speed improvement.
- Reverse the ordering of the `graph.edges` array to improve pre-fetch predictability.
- Move the nodes of a definitions body before the node of its type. This improves locality for readers that are
  not interested in opaque bodies.
- Do not entangle the nodes of different definitions.
- Layout definition nodes in one cluster at the beginning of the nodes array. This allows a clever OS to keep this
  block permanently into memory because it is used often.

Changes to the dataset organization:
- Capn'proto `.bin` files now contain plain, non-packed messages. This increases the size of the dataset
  but facilitates random access to the graph by `mmap`ing the files.
- The dataset is now distributed as a compressed SquashFS image instead of a tarball. This should
  compensate for the increased size of the non-packed messages. Advantages of this approach:
  + The SquashFS image can be mounted, allowing the on-the-fly decompression. This saves disk space
    and may make the random access faster because the hard-disk has to do less work. Note however that
    currently the image is compressed using `xz`. Such heavy compression may make the CPU the bottleneck.
    Experimentation with cheaper compression may be needed.
  For using the SquashFS image there are several options in order of preference:
  + When you have root access: Mount the image using `mount dataset.squ mountpoint/`
  + Without root access: On some machines you may be able to mount using `udisksctl` (depending on the
    configuration). Otherwise, you can mount in userspace by installing `squashfuse` and running
    `squashfuse dataset.squ /mountpoint`. An userspace mount has the disadvantage that it is slower due to
    the usage of Fuse and the lack of mutli-core decompression.
  + If all else fails, you can unpack the image using `unsquashfs dataset.squ`.

Misc changes:
- Many modifications to upstream Tactician in preparation for larger datasets. This includes improvements
  to the tactical decomposition and possibly some changes in the hashes of tactics.

# stdlib-lgraph-intermediate-v10-global
Buggy, do not use

# stdlib-lgraph-intermediate-v9-global

Textual representations:
- Definitions now feature a textual representation of their type and term.
- Proof terms that witness outcomes have are textually represented.

Proofs, proof states and proof terms:
- We now encode the tactic script itself as a (hyper-)graph. Every proof step (the execution of a tactic)
  has a list of outcomes. An outcome is the transition of one proof state into zero or mere other proof states.
  For every outcome there is additionally a proof term which was generated by the tactic and acts as a witness
  for the outcome. Before states, after states and proof terms reference each other like they should in the
  existential calculus of constructions.
- There are some tactics that we cannot or do not want to record. Examples of this are unsafe tactics (tactics
  that can produce ill-typed proof terms) and tactics executed through Coq's 'Proof with tac' mechanism.
  Previously, such tactics were simply omitted from the proof script. However, because we now encode the entire
  proof as a graph, this is no longer possible. Therefore, some tactics are now marked as 'unknown'.

Introduction of the global context:
- Every definition now has a `previous` field that indicates which definition comes before it in the global context.
- We now include every definition that has ever existed at any time-point during the compilation of a file.
  Definitions now have a `status` field that indicates they are either (1) an `original` definition as inputted
  by the user, (2) a `discharged` definition which is the result of a section being closed or (3) a substituted
  definition which is the result of a module being instantiated. In the last two cases, we cross-reference to
  the original definition.
- Every file in the dataset has a `representative` field, which points to the definition that is the end of the
  'super-global' context. The super-global context is the collection of all definitions that become available when
  a file is `Require`d into another file.
- Every definition has a field `externalPrevious`, which contains a list of files that have been `Require`d right
  before the definition was inputted by the user.
- A python utility `pytact-visualize` has been created to visualize the global context of a file.
- The main entry points of a file have been changed. Entry points now consists of `definitions`, a list of all
  definitions in the file, and `representative`, the definition that represents the super-global context of a file.

Misc changes to the graph:
- We now deal in a more principle way with section variables. Previously, a definition or proof state that referred
  to a section variable had a local context associated to it that included that variable. This way, different
  definitions/proof states that referred to the same section variable had instead a local copy of that variable,
  which is arguably incorrect because a model will not know that such copies are actually the same object.

  The new situation is that section variables are treated as axioms and local section declarations are treated as
  normal definitions. This seems to be the best encoding. Note, however, that this very much goes against how
  section variables are encoded internally in Coq (and even how they are presented to users).
  A positive consequence of this is that definitions now no longer have a local context associated to them, which
  was a bit weird.
- The node-label `var` and the edge-label `varPointer` have been removed. They created a structure that was analogous
  to what `rel` and `relPointer` did for bound variables, but instead pointing to local context variables.
  
  For bound variables, such the indirection  through `rel` is needed because otherwise the graph is not isomorphic
  to its CIC-term anymore. In particular, the removal of the `rel` node will cause the graph to become bisimilar to
  potentially infinite unfoldings of itself, which is quite clearly wrong.
  
  For free variables bound to the local context no such isomorphism issues exist, however.
  Hence, the `var` node was removed. With this change, local context elements have become extremely similar to
  global definitions in behavior. The only difference is that the root of the proof state contains a pointer to
  all of its local variables. As such, in the future, it might be considered to merge the nodes for local contexts
  into the nodes for definitions.
- Names of definitions are now their full path (including sections and modules).
  
# stdlib-lgraph-intermediate-v8-global

The main goal of this release is to align the tactics in the dataset to tactics that can be read and interpreted
by Coq during interactive proof search. As such, the hashes of the base tactics have changed, and the way that
arguments are extracted is also different. These changes are internal to the Coq plugin and the Capnp API is not
meaningfully changed. For every tactic, it has been checked that we can substitute the extracted arguments back
to obtain the same result as is represented textually by the `intermText` field.
Note that this does not mean that such tactics represent exactly what the user originally wrote!

As a result, the amount of unique tactics and related statistics have changed slightly. However, the most
significant change is that the number of unresolvable arguments has increased from 3809 to 5770. It is not
clear as of yet which change caused this increase (but it is likely unavoidable).

Additionally, the number of proofs we can faithfully represent has decreased from 6258 to 6205.

Changes to the Capn'proto format:
- Upgraded the magic id
- Tactics now have a flag `exact` which indicates whether or not the representation faithfully represents
  the original tactic. This comes with a caveat, please read the corresponding note in the `.capnp` API file.

# stdlib-lgraph-intermediate-v7-global

Changes to the Capn'proto format:
- Upgraded the magic id
- The graph representation now uses one big edge array for children of nodes, instead of many small array.
  This results in significant space savings, both in the memory representations and the on-disk representations.

# stdlib-lgraph-intermediate-v6-global

Changes to the Capn'proto format:
- Upgraded the magic id
- The storage format of the graph has been changed from an edge-list to an adjacency-list, giving us a much more natural representation.
  This should allow consumers of the graph to implement graph-algorithms that operate directly on the capn'proto datastructure instead of
  first loading the graph into an intermediate format. This should help with efficiency.
  However, the new format does cause a significant space overhead, ever after optimization of the formt.
  The dataset goes from 1.3GB to 1.7GB.
- Improved in-memory storage requirements by wrapping some integers and floats into structs.
- For tactic arguments, the `GlobalNode` struct has been inlined.

Changes to the graph representation:
- Fixed a bug that caused mutual (co)fixpoints to be cross-connected (unclear wether or not this bug was observable in datasets).
- Fixed a bug causing section contexts variables to be children of inappropriate nodes. This was likely not observable in previous datasets.
- We are generating less superfluous nodes (526) and edges (87392). Note, however, that this still does not guarantee the absence of garbage.
  One should still take care to only access nodes that are reachable through forward graph traversal.
- Switched the orientation of order-indicating edges between arguments of function application nodes and existential-variable substitution nodes.
  In the current dataset, this change is expected to have little to no impact.
  However, the current orientation is incorrect nonetheless. This incorrectness will/would be visible when we start performing node-sharing in the graph.

Other changes:
- The code to generate the older 'graph' and 'dag' datasets have been removed. The maintenance burden was to great.
  Now only the 'labelled graph' remains. Many of the advantages of the 'dag' version have now been integrated into 'labelled_graph', and the labelled graph
  can relatively easily be modified to be acyclic. The 'graph' version has been removed due to lack of interest.
- Now that we do no longer have to distinguish between 'graph' and 'labelled graph', we rename all modules to not mention 'labelled' anymore.

# stdlib-lgraph-intermediate-v5-global

Changes w.r.t. `v5-local` are:
- Tactical argument now also include global references. Global references are given priority over local references.
- The capnp magic number has *not* been upgraded in this version, because v5-local and v5-global share the same API.

# stdlib-lgraph-intermediate-v5-local

Changes in this dataset w.r.t. `v3` are:
- It can be generated by everyone
- The tactical decomposition is slightly more conservative in `v5` than in `v3`. This is so little that it is probably undetectable though.
- As a result of the modified decomposition, the basic statistics of the dataset have also been changed to a small degree: 
```
Nodes total 60220300
Edges total 108697004
Tactics total 985
Tactics entropy (bits) 5.512928911238009
Tactics base text total 912
Tactics base intermtext total 9202
Tactical definitions total 11348
Proof steps total 197090
```
- Dependency references now point to the actual `.bin` files in the dataset, instead of the bogus corresponding `.v` files (this was a bug)
- Starting with version v4 we will version the capnp protocol through the magic id at the top of the `.capnp` file. Every new incompatible version will get a new hash
- Tactical arguments are now wrapped in a variant type. Arguments that cannot be resolved are encoded using the `unresolvable` variant (a `None`-type)

# stdlib-lgraph-intermediate-v4-local
Buggy, do not use

# stdlib-lgraph-intermediate-v3

Changes w.r.t the previous version:
- Reversed the order of the context in the textual representation of proof states to be consistent with Coq (bug found by Jason)
- Nodes in the graph that represent an element from the local context now have their textual name attached (requested by Jason)
- This dataset features a much more aggressive tactical decomposition than the previous one
  + The number of unique base tactics has been reduced from (approximately) 2700 to 987
  + As a consequence, the number of recorded proof states has increased from 150k (approximately) to 197k
  + Note that the number of unique textual representations of tactics is 914, a bit lower than 987 because the textual representation is not always precise
  + The tactical decomposition is still a work in progress, but we are now reaching diminishing returns. One might think that 987 tactics is a lot, but two-third of those occur less than 10 times in the dataset. There are still many tactics that can be decomposed (I estimate about 300), but I don't think it is currently worth spending time on.
  + One goal of the decomposition is to not have any tactics that generate arbitrary names. For example, we convert a tactic like intro `my_fancy_variable_name` to `intros ?` in order to let Coq invent the name for us. This is also still a work in progress, but we are also reaching diminishing returns here. There are currently about 5000 instances of generative variables that have not been properly anonymized yet.
- The dataset now encodes arguments of tactics as follows:
  + The number of parameters of each base tactic is fixed (if not, it is a bug, please report).
  + For each argument of a tactic, we look up the first free variable referencing the local context inside of that argument. Then we replace the whole argument with that variable.
  + If an argument does not reference anything from the local context, the argument is replaced with a pointer to node 0 (yes I know that a `None`` type would be better but I'm to lazy for that). Note that arguments that represent generative names also point to node 0. As explained above, this happens about 5000 times.
- There are now three textual representations of tactics:
  + `text`: The full text representation of the tactic, including the full original arguments
  + `baseText`: A textual representation of the base tactic without any arguments
  + `intermText`: A textual representation of the tactic where parameters are restricted to the local context, directly mirroring the encoding of the parameters form the previous bullet-point

# stdlib-lgraph-intermediate-v2

Changes:
- Proofs are now grouped by lemma
- Definitions are grouped, have a hash, and have a name (string)
- Tactics now have an id, and arguments that include things from the local context and the global context. We cannot always resolve all arguments yet (in particular arguments given to intros), in which case their node-id is zero. We do not yet have full graphs of term arguments. Term arguments are currently thrown away, keeping only the constants inside those arguments. In order to keep the amount of arguments under control, we only add opaque definitions to the arguments (opaque definitions correspond loosely to lemmas).
- Tactics now come with a string representation. Note that this is not a 1-to-1 mapping to the tactic representation above, because in the string representation full term arguments are present.
- Proof states now also come with a string representation.
- The amount of proof states has been reduced from 250k to 150k. The reason for this is fairly technical, I'll explain during the meeting.
- Tactics now have attributes text and baseText. The first corresponds to the fully printed text of the tactical. The second one corresponds roughly to the text of the base tactic without arguments. The correspondence is rough, because Coq's printing facility does not reflect 100% of the internal tactical AST. So while there are about 2700 unique tactic bases, there are only 2600 unique corresponding strings.

# stdlib-lgraph-intermediate-v1
Buggy, do not use.
