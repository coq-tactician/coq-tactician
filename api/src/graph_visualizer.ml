open Graph_extractor
open Graph_def

let order_option = Goptions.declare_bool_option_and_ref
      ~depr:false ~name:"order graph nodes"
      ~key:["Tactician"; "Neural"; "Visualize"; "Ordered"]
      ~value:true

let label_option = Goptions.declare_bool_option_and_ref
    ~depr:false ~name:"order graph nodes"
    ~key:["Tactician"; "Neural"; "Visualize"; "Labels"]
    ~value:false

let debug_option = Goptions.declare_bool_option_and_ref
    ~depr:false ~name:"order graph nodes"
    ~key:["Tactician"; "Neural"; "Visualize"; "Debug"]
    ~value:false

type vertex = { tag : int; label : Graph.Graphviz.DotAttributes.vertex list }
module G = Graph.Persistent.Digraph.ConcreteLabeled(
  struct
    type t = vertex
    let compare x y = Int.compare x.tag y.tag
    let hash x = Int.hash x.tag
    let equal x y = Int.equal x.tag y.tag
  end)(
  struct type t = edge_type
    let compare = compare
    let default = ContextSubject
  end)

module GraphvizGraph = struct
  include G

  let vertex_name x = string_of_int @@ (V.label x).tag

  let arrow_heads = [ `Dot; `Inv; `Odot; `Invdot; `Invodot ]

  let graph_attributes _ = (if order_option () then [`OrderingOut] else []) @
                           [`Fontname "Helvetica"; `Ranksep 0.3]
  let default_vertex_attributes _ = [`Fontname "Helvetica"; `Style `Filled; `Penwidth 0.]
  let vertex_attributes n = (V.label n).label
  let default_edge_attributes _ = [`Fontname "Helvetica"; `Arrowsize 0.5; `Penwidth 0.6]
  let edge_attributes e =
    (if label_option () then [ `Label Graph_def.(show_edge_type @@ E.label e) ] else []) @
    [ `Dir `Both
    ; `Arrowtail (List.nth arrow_heads @@ edge_type_int_mod @@ E.label e)]
  let get_subgraph _ = None

  let mk_edge g sort ~source ~target = add_edge_e g (E.create source sort target)
  let mk_node g label =
    let n = V.create { tag = nb_vertex g; label } in
    n, add_vertex g n
end

module Dot = Graph.Graphviz.Dot(GraphvizGraph)

(* TODO: Probably not the most beautiful and efficient solution *)
let cic_graph_to_dot_graph transform ns root =
  (* We cannot just dump the nodes and edges into graphviz in random order, because then the graph
     will be printed strangely. We have to traverse the graph in-order for it to look decently. *)
  let ns = ns (fun ~node_count:_ ~edge_count:_ -> DList.nil) (fun ns nl ch -> DList.cons (nl, ch) ns) in
  let ns = Array.of_list @@ DList.to_list ns in
  let rec traverse visited g tag n =
    match Int.Map.find_opt n visited with
    | Some node -> visited, g, tag, node
    | None ->
      let label, children = ns.(n) in
      let source = { tag; label = transform label } in
      let g = GraphvizGraph.add_vertex g source in
      let visited = Int.Map.add n source visited in
      let visited, g, tag = List.fold_left (fun (visited, g, tag) (label, i) ->
          let visited, g, tag, target = traverse visited g tag i in
          visited, GraphvizGraph.mk_edge g label ~source ~target, tag) (visited, g, tag + 1) children in
      visited, g, tag, source
  in
  let _, g, _, _ = traverse Int.Map.empty GraphvizGraph.empty 0 root in g

let make_graph transform graph root =
  let graph = cic_graph_to_dot_graph transform graph root in
  let chan = open_out "graph.dot" in
  Dot.output_graph chan graph;
  close_out chan;
  ignore @@ Sys.command "dot -Tpdf graph.dot -o graph.pdf"

module Viz
    (G : sig
       type node'
       type final
       val final_to_string : final -> Graph.Graphviz.DotAttributes.vertex list
       type result = (final * (edge_type * int) list) DList.t
       val node_repr : node' -> int
       include GraphMonadType
         with type node = node'
          and type edge_label = edge_type
          and type node_label = node' node_type
          and type 'a repr_t =
                'a *
                ((node_count:int -> edge_count:int -> result) ->
                 (result -> final -> (edge_label * int) list -> result) ->
                 result)
     end) =
struct
  module GM = struct include CICGraphMonad(G) type node' = node end
  module Builder = GraphBuilder(GM)

  let make_global_graph ?def_depth x =
    let x =
      try
        Smartlocate.locate_global_with_alias x
      with Not_found -> CErrors.user_err (Pp.str "Invalid ident given") in
    let (_, root), ns = GM.run_empty ?def_depth
      (Builder.gen_globref (Global.env ()) (Names.Id.Map.empty, Names.Cmap.empty) x) in
    make_graph G.final_to_string ns @@ G.node_repr root

  let make_constr_graph ?def_depth c =
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let evd, c = Constrintern.interp_constr_evars env sigma c in
    let (_, root), ns = GM.run_empty ?def_depth @@
      GM.with_evar_map (sigma_to_proof_state_lookup evd) @@
      Builder.gen_constr (Global.env ()) (Names.Id.Map.empty, Names.Cmap.empty) (EConstr.to_constr evd c) in
    make_graph G.final_to_string ns @@ G.node_repr root

  let make_proof_graph ?def_depth state =
    let _ =
      Pfedit.solve (Goal_select.get_default_goal_selector ()) None
        (Proofview.tclBIND (Builder.gen_proof_state_tactic (Names.Id.Map.empty, Names.Cmap.empty)) (fun res ->
             let (_, ps), ns = GM.run_empty ?def_depth res in
             make_graph G.final_to_string ns @@ G.node_repr ps.root;
             Proofview.tclUNIT ()))
        (Proof_global.get_proof state) in ()

  end

let node_string_pretty = function
  | ContextDef (_, id) -> [`Shape `Ellipse; `Label (Names.Id.to_string id)]
  | ContextAssum (_, id) -> [`Shape `Ellipse; `Label (Names.Id.to_string id)]
  | Definition { path; _ } -> [`Shape `Box; `Label (Names.Id.to_string @@ Libnames.basename path)]
  | SortSProp -> [`Shape `Ellipse; `Label "SProp"]
  | SortProp -> [`Shape `Ellipse; `Label "Prop"]
  | SortSet -> [`Shape `Ellipse; `Label "Set"]
  | SortType -> [`Shape `Ellipse; `Label "Type"]
  | Rel -> [`Shape `Circle; `Label "↑"]
  | Evar -> [`Shape `Ellipse; `Label "Evar"]
  | Prod id -> [`Shape `Circle; `Label "∀"]
  | Lambda _ -> [`Shape `Circle; `Label "λ"]
  | LetIn _ -> [`Shape `Ellipse; `Label "let"]
  | App -> [`Shape `Circle; `Label "@"]
  | FixFun _ -> [`Shape `Ellipse; `Label "FixFun"]
  | CoFixFun _ -> [`Shape `Circle; `Label "CoFixFun"]
  | x -> [`Shape `Ellipse; `Label (Graph_def.show_node_type (fun _ _ -> ()) x)]


module SimpleCICGraph = struct
  type final = int node_type
  type node' = int
  let node_repr x = x
  type result = (final * (edge_type * int) list) DList.t
  let final_to_string nl =
    if debug_option () then
      [`Shape `Ellipse; `Label (Graph_def.show_node_type (fun _ _ -> ()) nl)]
    else node_string_pretty nl
  include SimpleGraph(
    struct
      type nonrec result = (final * (edge_type * int) list) DList.t
      type edge_label = edge_type
      type node_label = final
    end)
  type 'a repr_t =
    'a *
    ((node_count:int -> edge_count:int -> result) ->
     (result -> final -> (edge_label * int) list -> result) ->
     result)
end

module rec SimpleHashedCICGraph : sig
  type final = SimpleHashedCICGraph.node node_type * int64
  type node' = SimpleHashedCICGraph.node
  val node_repr : node' -> int
  type result = (final * (edge_type * int) list) DList.t
  val final_to_string : final -> Graph.Graphviz.DotAttributes.vertex list
  include GraphMonadType
    with type node_label = node' node_type
     and type edge_label = edge_type
     and type 'a repr_t =
           'a *
           ((node_count:int -> edge_count:int -> result) ->
            (result -> final -> (edge_label * int) list -> result) ->
            result)
end = struct
  type final = SimpleHashedCICGraph.node node_type * int64
  type node' = SimpleHashedCICGraph.node
  type result = (final * (edge_type * int) list) DList.t
  let final_to_string (nl, h) =
    if debug_option () then
      [`Shape `Ellipse; `Label (Graph_def.show_node_type (fun _ _ -> ()) nl ^ " : " ^ Int64.to_string h)]
    else node_string_pretty nl

  module rec Hasher :
    CICHasherType with type t = int64
                   and type node_label = node' node_type
                   and type edge_label = edge_label =
    CICHasher(XXHasher)
      (struct
        type node = node'
        let node_hash _ = XXHasher.with_state (fun s -> s)
      end)
  and HashMap : Hashtbl.S with type key = Hasher.t = Hashtbl.Make(Hasher)
  and GH : sig
    include GraphMonadType
      with type node_label = node' node_type
       and type edge_label = edge_type
       and type 'a repr_t =
             int HashMap.t ->
             'a *
             ((node_count:int -> edge_count:int -> result) ->
              (result -> final -> (edge_label * int) list -> result) ->
              result)
    val lower : node -> int * Hasher.t
  end
    = GraphHasher
      (struct
        type node_label = SimpleHashedCICGraph.node node_type
        type edge_label = edge_type
      end)
      (Hasher)(HashMap)
      (struct
        include SimpleGraph(
          struct
            type nonrec result = result
            type edge_label = edge_type
            type node_label = final
          end)
        let node_location _ = XXHasher.with_state @@ fun h -> h
      end
      )
  include GH
  type 'a repr_t =
    'a *
    ((node_count:int -> edge_count:int -> result) ->
     (result -> final -> (edge_label * int) list -> result) -> result)
  let run m = run m (HashMap.create 0)
  let node_repr x = fst @@ GH.lower x
end

module SimpleViz = Viz(SimpleCICGraph)
module SimpleHashedViz = Viz(SimpleHashedCICGraph)
