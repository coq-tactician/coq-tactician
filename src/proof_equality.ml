(** This file is heavily inspired by Proofview.tclPROGRESS *)

(** A copy of [Constr.compare_head_gen_leq_with], with the difference that it does not
    operate modulo alpha equivalence. For the purpose of proof equality, the names of
    terms are very important, as they can be referenced by tactics. Additionally, they
    will be used to determine the name of a hypothesis in the local context when it is
    introduced. *)
let compare_head_gen_leq_with kind1 kind2 eq_evar leq_universes leq_sorts eq leq nargs t1 t2 =
  let open Constr in
  let open Names in
  let open Context in
  let binder_equal id1 id2 = Name.equal id1.binder_name id2.binder_name in
  match kind_nocast_gen kind1 t1, kind_nocast_gen kind2 t2 with
  | Cast _, _ | _, Cast _ -> assert false (* kind_nocast *)
  | Rel n1, Rel n2 -> Int.equal n1 n2
  | Meta m1, Meta m2 -> Int.equal m1 m2
  | Var id1, Var id2 -> Id.equal id1 id2
  | Int i1, Int i2 -> Uint63.equal i1 i2
  | Float f1, Float f2 -> Float64.equal f1 f2
  | Sort s1, Sort s2 -> leq_sorts s1 s2
  | Prod (id1,t1,c1), Prod (id2,t2,c2) -> binder_equal id1 id2 && eq 0 t1 t2 && leq 0 c1 c2
  | Lambda (id1,t1,c1), Lambda (id2,t2,c2) -> binder_equal id1 id2 && eq 0 t1 t2 && eq 0 c1 c2
  | LetIn (id1,b1,t1,c1), LetIn (id2,b2,t2,c2) -> binder_equal id1 id2 && eq 0 b1 b2 && eq 0 t1 t2 && leq nargs c1 c2
  (* Why do we suddenly make a special case for Cast here? *)
  | App (c1, l1), App (c2, l2) ->
    let len = Array.length l1 in
    Int.equal len (Array.length l2) &&
    leq (nargs+len) c1 c2 && CArray.equal_norefl (eq 0) l1 l2
  | Proj (p1,c1), Proj (p2,c2) -> Projection.equal p1 p2 && eq 0 c1 c2
  | Evar (e1,l1), Evar (e2,l2) ->
    eq_evar e1 e2 && CArray.equal (eq 0) l1 l2
  | Const (c1,u1), Const (c2,u2) ->
    (* The args length currently isn't used but may as well pass it. *)
    Constant.equal c1 c2 && leq_universes (GlobRef.ConstRef c1) nargs u1 u2
  | Ind (c1,u1), Ind (c2,u2) ->
    eq_ind c1 c2 && leq_universes (GlobRef.IndRef c1) nargs u1 u2
  | Construct (c1,u1), Construct (c2,u2) ->
    eq_constructor c1 c2 && leq_universes (GlobRef.ConstructRef c1) nargs u1 u2
  | Case (_,p1,c1,bl1), Case (_,p2,c2,bl2) ->
    eq 0 p1 p2 && eq 0 c1 c2 && CArray.equal (eq 0) bl1 bl2
  | Fix ((ln1, i1),(ids1,tl1,bl1)), Fix ((ln2, i2),(ids2,tl2,bl2)) ->
    CArray.equal binder_equal ids1 ids2 &&
    Int.equal i1 i2 && CArray.equal Int.equal ln1 ln2
    && CArray.equal_norefl (eq 0) tl1 tl2 && CArray.equal_norefl (eq 0) bl1 bl2
  | CoFix(ln1,(ids1,tl1,bl1)), CoFix(ln2,(ids2,tl2,bl2)) ->
    CArray.equal binder_equal ids1 ids2 &&
    Int.equal ln1 ln2 && CArray.equal_norefl (eq 0) tl1 tl2 && CArray.equal_norefl (eq 0) bl1 bl2
  | (Rel _ | Meta _ | Var _ | Sort _ | Prod _ | Lambda _ | LetIn _ | App _
    | Proj _ | Evar _ | Const _ | Ind _ | Construct _ | Case _ | Fix _
    | CoFix _ | Int _ | Float _), _ -> false

let compare_head_gen_with kind1 kind2 eq_evar eq_universes eq_sorts eq nargs t1 t2 =
    compare_head_gen_leq_with kind1 kind2 eq_evar eq_universes eq_sorts eq eq nargs t1 t2

let evars_equal evd1 evd2 (equal : (Evar.t * Evar.t) list) =
  let open Evd in
  let evd_common = Evd.emit_side_effects (Evd.eval_side_effects evd1) evd2 in
  let evd_common = ref (merge_universe_context evd_common (evar_universe_context evd1)) in
  let left_evar_map = ref Evar.Map.empty in
  let right_evar_map = ref Evar.Map.empty in
  let rec eq_constr_univs_test t1 t2 =
    let t1 = EConstr.Unsafe.to_constr t1
    and t2 = EConstr.Unsafe.to_constr t2 in
    let eq_universes _ _ u1 u2 =
      let u1 = normalize_universe_instance !evd_common u1 in
      let u2 = normalize_universe_instance !evd_common u2 in
      try evd_common := add_universe_constraints !evd_common
            UnivProblem.(enforce_eq_instances_univs false u1 u2 Set.empty); true
      with Univ.UniverseInconsistency _ | UniversesDiffer -> false
    in
    let eq_sorts s1 s2 =
      if Sorts.equal s1 s2 then true
      else
        let u1 = Sorts.univ_of_sort s1 and u2 = Sorts.univ_of_sort s2 in
        try evd_common := add_universe_constraints !evd_common UnivProblem.(Set.singleton (UEq (u1, u2))); true
        with Univ.UniverseInconsistency _ | UniversesDiffer -> false
    in
    let kind1 = Evarutil.kind_of_term_upto evd1 in
    let kind2 = Evarutil.kind_of_term_upto evd2 in
    let rec eq_constr' nargs m n =
      compare_head_gen_with kind1 kind2 evar_equal eq_universes eq_sorts eq_constr' nargs m n
    in
    compare_head_gen_with kind1 kind2 evar_equal eq_universes eq_sorts eq_constr' 0 t1 t2

  (* equality function on hypothesis contexts *)
  and eq_named_context_val ctx1 ctx2 =
    let open Context.Named.Declaration in
    let c1 = EConstr.named_context_of_val ctx1 and c2 = EConstr.named_context_of_val ctx2 in
    let eq_named_declaration d1 d2 =
      match d1, d2 with
      | LocalAssum (i1,t1), LocalAssum (i2,t2) ->
        Context.eq_annot Names.Id.equal i1 i2 && eq_constr_univs_test t1 t2
      | LocalDef (i1,c1,t1), LocalDef (i2,c2,t2) ->
        Context.eq_annot Names.Id.equal i1 i2 && eq_constr_univs_test c1 c2
        && eq_constr_univs_test t1 t2
      | _ ->
        false
    in CList.equal eq_named_declaration c1 c2

  and eq_evar_body b1 b2 =
    match b1, b2 with
    | Evar_empty, Evar_empty -> true
    | Evar_defined t1, Evar_defined t2 ->
      eq_constr_univs_test t1 t2
    | _ -> false

  and eq_evar_info ei1 ei2 =
    (* TODO: Should we be checking equality on other types of evar kinds? *)
    let kinds_equal = match ei1.evar_source, ei2.evar_source with
      | (_, Evar_kinds.NamedHole id1), (_, Evar_kinds.NamedHole id2) -> Names.Id.equal id1 id2
      | (_, Evar_kinds.NamedHole _), _ | _, (_, Evar_kinds.NamedHole _) -> false
      | _, _ -> true in
    kinds_equal &&
    eq_constr_univs_test ei1.evar_concl ei2.evar_concl &&
    eq_named_context_val (Evd.evar_filtered_hyps ei1) (Evd.evar_filtered_hyps ei2) &&
    eq_evar_body ei1.evar_body ei2.evar_body

  (* Equality function on goals *)
  and evar_equal evar1 evar2 =
    match Evar.Map.find_opt evar1 !left_evar_map, Evar.Map.find_opt evar2 !right_evar_map with
    | Some evar2', Some evar1' when Evar.equal evar1 evar1' && Evar.equal evar2 evar2' ->
      true
    | None, None ->
      let evi1 = Evd.find evd1 evar1 in
      let evi2 = Evd.find evd2 evar2 in
      (match eq_evar_info evi1 evi2 with
       | true ->
         left_evar_map := Evar.Map.add evar1 evar2 !left_evar_map;
         right_evar_map := Evar.Map.add evar2 evar1 !right_evar_map;
         true
       | false -> false)
    | _, _ -> false
  in
  CList.for_all (fun (evar1, evar2) -> evar_equal evar1 evar2) equal

(** Compare the proof states after running [t1] and [t2] and taking their first result.
    If they are equal, we keep the (first) result of [t2]. Otherwise, run [t3].
    Because this is a tactic, comparison of proof states happens only on the focused goals. *)
let third_if_not_equal_tactic t1 t2 t3 =
  let exception Result_info of (Evd.evar_map * Evar.t list) in
  let exception Not_equal in
  let open Proofview in
  let open Notations in
  let t1_fail =
    tclONCE t1 >>= fun _ ->
    Goal.goals >>= Tactician_util.record_map (fun x -> x) >>= fun g1 ->
    let g1 = List.map Goal.goal g1 in
    tclEVARMAP >>= fun evd1 ->
    tclZERO (Result_info (evd1, g1)) in
  let t2 (e, info) =
    match e with
    | Result_info (evd1, g1) ->
      let t2_check =
        tclONCE t2 >>= fun res ->
        Goal.goals >>= Tactician_util.record_map (fun x -> x) >>= fun g2 ->
        let g2 = List.map Goal.goal g2 in
        tclEVARMAP >>= fun evd2 ->
        let test =
          try
            let equal = List.combine g1 g2 in
            evars_equal evd1 evd2 @@ equal
          with Invalid_argument _ -> false in
        if test then
          tclUNIT res
        else
           tclZERO Not_equal in
      tclOR t2_check (fun _ -> t3)
    | _ -> t3 in
  tclOR t1_fail t2

let pstate_equal ~pstate1 ~pstate2 =
  let goals p =
    let open Proof in
    let { sigma; goals; stack; shelf; given_up; _ } = data p in
    let goals = goals @ shelf @ given_up @ List.concat @@ List.map (fun (l, r) -> l@r) stack in
    let goals = List.filter_map (Evarutil.advance sigma) goals in
    sigma, goals in
  let sigma1, gs1 = goals pstate1 in
  let sigma2, gs2 = goals pstate2 in
  try
    let equal = List.combine gs1 gs2 in
    evars_equal sigma1 sigma2 @@ equal
  with Invalid_argument _ -> false

(** Compare the proof states after running [t1] and [t2] and taking their first result.
    If they are equal, we keep the (first) result of [t2]. Otherwise, run [t3].
    Comparison of the proof state happens on all unsolved goals. *)
let third_if_not_equal_command ~pstate t1 t2 t3 =
  let run t =
    let open Proof_global in
    map_proof (fun p ->
        fst @@ Pfedit.solve (Goal_select.get_default_goal_selector ()) None t p) pstate in
  try
    let p1 = run t1 in
    let p2 = run t2 in
    if pstate_equal ~pstate1:(Proof_global.get_proof p1) ~pstate2:(Proof_global.get_proof p2) then
       p2
    else
      run t3
  with
  | Logic_monad.TacticFailure e ->
    run t3
