open Graph_def
open Names

type graph_state = { node_index : int; edge_index : int }

type 'a conversion_info =
  { node_depindex : 'a -> int
  ; node_local_index : 'a -> int }

module Writer(K : Graph_api.S) = struct

let write_proof_state ?(include_metadata=false) { node_depindex; node_local_index }
    capnp_state { root; context; ps_string; concl_string; evar } =
  let capnp_root = K.Builder.ProofState.root_init capnp_state in
  K.Builder.ProofState.Root.dep_index_set_exn capnp_root @@ node_depindex root;
  K.Builder.ProofState.Root.node_index_set_int_exn capnp_root @@ node_local_index root;
  let context_arr = K.Builder.ProofState.context_init capnp_state @@ List.length context in
  List.iteri (fun i { node; _ } ->
      let arri = Capnp.Array.get context_arr i in
      K.Builder.Node.dep_index_set_exn arri @@ node_depindex node;
      K.Builder.Node.node_index_set_int_exn arri @@ node_local_index node
    ) context;
  if include_metadata then begin
    ignore(K.Builder.ProofState.context_names_set_list capnp_state
              (List.map (fun { id; _ } -> Id.to_string id) context));
    ignore(K.Builder.ProofState.context_text_set_list capnp_state
              (List.map (fun { text; _ } -> text) context));
    K.Builder.ProofState.text_set capnp_state ps_string;
    K.Builder.ProofState.conclusion_text_set capnp_state concl_string
  end;
  K.Builder.ProofState.id_set_int_exn capnp_state @@ Evar.repr evar

let nt2nt ~include_metadata none_index ({ node_depindex; node_local_index } as ci) (nt : 'a node_type) cnt =
  let open K.Builder.Graph.Node.Label in
  match nt with
  | ProofState evar ->
    let ps = proof_state_init cnt in
    K.Builder.IntP.value_set ps @@ Stdint.Uint64.of_int @@ Evar.repr evar
  | ContextDef _ -> context_def_set cnt
  | ContextAssum _ -> context_assum_set cnt
  | Definition { previous; external_previous; def_type; path; status; type_text; term_text } ->
    let cdef = definition_init cnt in
    let open K.Builder.Definition in
    name_set cdef ((match def_type with | Proj _ -> "Projection:" | _ -> "") ^ Libnames.string_of_path path);
    if include_metadata then begin
      type_text_set cdef type_text;
      term_text_set cdef @@ Option.default "" term_text
    end;
    let capnp_status = status_init cdef in
    (match status with
     | DOriginal -> Status.original_set capnp_status
     | DDischarged n ->
       if node_depindex n <> 0 then
         CErrors.anomaly Pp.(str "discharged definition was not from the current file");
       Status.discharged_set_int_exn capnp_status @@ node_local_index n
     | DSubstituted n ->
       let capnp_node = Status.substituted_init capnp_status in
       Status.Substituted.dep_index_set_exn capnp_node @@ node_depindex n;
       Status.Substituted.node_index_set_int_exn capnp_node @@ node_local_index n);
    let write_proof arr proof =
      let write_outcome capnp { term; term_text; arguments; proof_state_before; proof_states_after } =
        let capnp_state_before = K.Builder.Outcome.before_init capnp in
        write_proof_state ~include_metadata ci capnp_state_before proof_state_before;
        let after_arr = K.Builder.Outcome.after_init capnp (List.length proof_states_after) in
        List.iteri (fun i ps ->
            let capnp_state = Capnp.Array.get after_arr i in
            write_proof_state ~include_metadata ci capnp_state ps;
          ) proof_states_after;
        let capnp_term = K.Builder.Outcome.term_init capnp in
        K.Builder.Outcome.Term.dep_index_set_exn capnp_term @@ node_depindex term;
        K.Builder.Outcome.Term.node_index_set_int_exn capnp_term @@ node_local_index term;
        if include_metadata then
          K.Builder.Outcome.term_text_set capnp @@ term_text;
        let arg_arr = K.Builder.Outcome.tactic_arguments_init capnp (List.length arguments) in
        List.iteri (fun i arg ->
            let arri = Capnp.Array.get arg_arr i in
            match arg with
            | None -> K.Builder.Argument.unresolvable_set arri
            | Some n ->
              let node = K.Builder.Argument.term_init arri in
              K.Builder.Argument.Term.dep_index_set_exn node @@ node_depindex n;
              K.Builder.Argument.Term.node_index_set_int_exn node @@ node_local_index n
          ) arguments in
      List.iteri (fun i { tactic; outcomes } ->
          let arri = Capnp.Array.get arr i in
          let capnp_tactic = K.Builder.ProofStep.tactic_init arri in
          (match tactic with
           | None -> K.Builder.ProofStep.Tactic.unknown_set capnp_tactic
           | Some { tactic; tactic_non_anonymous; base_tactic; interm_tactic; tactic_hash; tactic_exact } ->
             let capnp_tactic = K.Builder.ProofStep.Tactic.known_init capnp_tactic in
             K.Builder.Tactic.ident_set capnp_tactic tactic_hash;
             K.Builder.Tactic.exact_set capnp_tactic tactic_exact;
             if include_metadata then begin
               K.Builder.Tactic.text_set capnp_tactic tactic;
               K.Builder.Tactic.text_non_anonymous_set capnp_tactic tactic_non_anonymous;
               K.Builder.Tactic.base_text_set capnp_tactic base_tactic;
               K.Builder.Tactic.interm_text_set capnp_tactic interm_tactic
             end);
          let outcome_arr = K.Builder.ProofStep.outcomes_init arri (List.length outcomes) in
          List.iteri (fun i outcome ->
              let outcome_arri = Capnp.Array.get outcome_arr i in
              write_outcome outcome_arri outcome
            ) outcomes
        ) proof in
    (match previous with
     | None -> previous_set_int_exn cdef none_index;
     | Some previous ->
       if node_depindex previous <> 0 then
         CErrors.anomaly Pp.(str "previous definition was not from the current file");
       previous_set_int_exn cdef @@ node_local_index previous);
    ignore (external_previous_set_list cdef @@ List.map node_depindex external_previous);
    (match def_type with
     | TacticalConstant (c, proof) ->
       let arr = tactical_constant_init cdef (List.length proof) in
       write_proof arr proof
     | TacticalSectionConstant (id, proof) ->
       let arr = tactical_section_constant_init cdef (List.length proof) in
       write_proof arr proof
     | ManualConst c -> manual_constant_set cdef
     | ManualSectionConst id -> manual_section_constant_set cdef
     | Ind (representative, _) -> inductive_set_int_exn cdef @@ node_local_index representative
     | Construct (representative, _) -> constructor_set_int_exn cdef @@ node_local_index representative
     | Proj (representative, _) -> projection_set_int_exn cdef @@ node_local_index representative)
  | ConstEmpty -> const_empty_set cnt
  | SortSProp -> sort_s_prop_set cnt
  | SortProp -> sort_prop_set cnt
  | SortSet -> sort_set_set cnt
  | SortType -> sort_type_set cnt
  | Rel -> rel_set cnt
  | Evar -> evar_set cnt
  | EvarSubst -> evar_subst_set cnt
  | Cast -> cast_set cnt
  | Prod _ -> prod_set cnt
  | Lambda _ -> lambda_set cnt
  | LetIn _ -> let_in_set cnt
  | App -> app_set cnt
  | Case -> case_set cnt
  | CaseBranch -> case_branch_set cnt
  | Fix -> fix_set cnt
  | FixFun _ -> fix_fun_set cnt
  | CoFix -> co_fix_set cnt
  | CoFixFun _ -> co_fix_fun_set cnt
  | Int i ->
    let p = int_init cnt in
    K.Builder.IntP.value_set p @@ Stdint.Uint64.of_int @@ snd @@ Uint63.to_int2 i
  | Float f ->
    let p = float_init cnt in
    K.Builder.FloatP.value_set p @@ float64_to_float f
  | Primitive p -> primitive_set cnt (CPrimitives.to_string p)
let et2et (et : edge_type) =
  let open K.Builder.EdgeClassification in
  match et with
  | ContextElem -> ContextElem
  | ContextSubject -> ContextSubject
  | ContextDefType -> ContextDefType
  | ContextDefTerm -> ContextDefTerm
  | ConstType -> ConstType
  | ConstUndef -> ConstUndef
  | ConstDef -> ConstDef
  | ConstOpaqueDef -> ConstOpaqueDef
  | ConstPrimitive -> ConstPrimitive
  | IndType -> IndType
  | IndConstruct -> IndConstruct
  | IndProjection -> IndProjection
  | ProjTerm -> ProjTerm
  | ConstructTerm -> ConstructTerm
  | CastTerm -> CastTerm
  | CastType -> CastType
  | ProdType -> ProdType
  | ProdTerm -> ProdTerm
  | LambdaType -> LambdaType
  | LambdaTerm -> LambdaTerm
  | LetInDef -> LetInDef
  | LetInType -> LetInType
  | LetInTerm -> LetInTerm
  | AppFun -> AppFun
  | AppArg -> AppArg
  | CaseTerm -> CaseTerm
  | CaseReturn -> CaseReturn
  | CaseBranchPointer -> CaseBranchPointer
  | CaseInd -> CaseInd
  | CBConstruct -> CBConstruct
  | CBTerm -> CBTerm
  | FixMutual -> FixMutual
  | FixReturn -> FixReturn
  | FixFunType -> FixFunType
  | FixFunTerm -> FixFunTerm
  | CoFixMutual -> CoFixMutual
  | CoFixReturn -> CoFixReturn
  | CoFixFunType -> CoFixFunType
  | CoFixFunTerm -> CoFixFunTerm
  | RelPointer -> RelPointer
  | EvarSubstPointer -> EvarSubstPointer
  | EvarSubstTerm -> EvarSubstTerm
  | EvarSubstTarget -> EvarSubstTarget
  | EvarSubject -> EvarSubject

let write_graph ?(include_metadata=false)
    ~node_hash ~node_label ~node_lower ~node_dep_index ~node_local_index
    ~node_count ~edge_count nodes edges capnp_graph =
  let cnodes = K.Builder.Graph.nodes_init capnp_graph node_count in
  let cedges = K.Builder.Graph.edges_init capnp_graph edge_count in
  let _ = AList.fold (fun node_index (label, Graph_def.{ start; size }) ->
      let node = Capnp.Array.get cnodes node_index in
      nt2nt ~include_metadata node_count
        { node_depindex = (fun n -> node_dep_index @@ node_lower n)
        ; node_local_index = (fun n -> node_local_index @@ node_lower n) }
        (node_label label) (K.Builder.Graph.Node.label_init node);
      K.Builder.Graph.Node.children_count_set_exn node size;
      K.Builder.Graph.Node.children_index_set_int_exn node (if size = 0 then 0 else start);
      K.Builder.Graph.Node.identity_set node @@ node_hash label;
      node_index + 1)
      nodes 0 in
  let _ = AList.fold (fun ei (label, n) ->
      let et = Capnp.Array.get cedges ei in
      K.Builder.Graph.EdgeTarget.label_set et @@ et2et label;
      let ctarget = K.Builder.Graph.EdgeTarget.target_init et in
      K.Builder.Graph.EdgeTarget.Target.dep_index_set_exn ctarget @@ node_dep_index n;
      K.Builder.Graph.EdgeTarget.Target.node_index_set_int_exn ctarget @@ node_local_index n;
      ei + 1
    ) edges 0 in
  ()

end

