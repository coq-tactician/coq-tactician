open Ltac_plugin
open Tacexpr
open Libobject
open CAst
open Equality
open Locus

type tac_ast = Then | Dispatch | Extend | Thens | Thens3parts | First | Complete | Solve | Or
             | Once | ExactlyOnce | IfThenCatch | Orelse | Do | Timeout | Repeat | Progress
             | Abstract | LetIn | Match | MatchGoal | Arg | Select | ML | Alias | Call
             | IntroPattern | Apply | Elim | Case | MutualFix | MutualCofix | Assert
             | Generalize | LetTac | InductionDestruct | Reduce | Change | Rewrite | RewriteMulti
             | Inversion

type tac_decomposition = Decompose | Keep | Both | Discard

module TacAstMap = Map.Make(struct
    type t = tac_ast
    let compare = compare
  end)
module StringMap = Map.Make(String)

type tac_ast_map = tac_decomposition TacAstMap.t
type tac_alias_ast_map = tac_decomposition Names.KNmap.t
type internal_tactics_map = Names.KerName.t StringMap.t

let tac_ast_map_ref = Summary.ref TacAstMap.empty ~name:"DecompositionMap"
let tac_ast_alias_map_ref = Summary.ref Names.KNmap.empty ~name:"AliasDecompositionMap"
let internal_tactics_ref = Summary.ref StringMap.empty ~name:"InternalTacticsMap"

let get_ast_settings () = !tac_ast_map_ref
let get_ast_alias_settings () = !tac_ast_alias_map_ref
let get_internal_tactics_settings () = !internal_tactics_ref

let tac_ast_setting : tac_ast_map -> obj =
  declare_object @@ global_object_nodischarge "TacticianDecompositionSetting"
    ~cache:(fun (_,m) -> tac_ast_map_ref := m)
    ~subst:None

let tac_alias_ast_setting : tac_alias_ast_map -> obj =
  declare_object @@ global_object_nodischarge "TacticianAliasDecompositionSetting"
    ~cache:(fun (_,m) -> tac_ast_alias_map_ref := m)
    ~subst:None

let internal_tactics_setting : internal_tactics_map -> obj =
  declare_object @@ global_object_nodischarge "TacticianInternalTacticsSetting"
    ~cache:(fun (_,m) -> internal_tactics_ref := m)
    ~subst:None

let ast_setting_lookup ast = Option.default Keep (TacAstMap.find_opt ast (get_ast_settings ()))

let ast_alias_setting_lookup kername = Option.default Keep (Names.KNmap.find_opt kername (get_ast_alias_settings ()))

let internal_tactics_ref_lookup str = StringMap.find str (get_internal_tactics_settings ())

let modify_ast_setting ast dec = Lib.add_anonymous_leaf
    (tac_ast_setting (TacAstMap.add ast dec (get_ast_settings ())))

let modify_ast_alias_setting tac dec =
  (match tac with
    | TacAlias CAst.{v=(kername, _); _} ->
      Lib.add_anonymous_leaf
        (tac_alias_ast_setting (Names.KNmap.add kername dec (get_ast_alias_settings ())))
    | _ -> CErrors.user_err (Pp.str "A stub of a tactic alias was expected but not found"));
  let tacstr = Pp.string_of_ppcmds @@
    Sexpr.format_oneline @@ Pptactic.pr_raw_tactic (Global.env ()) Evd.empty @@ tac in
  let tac = Tacintern.glob_tactic tac in
  let tacsexpr = Sexpr.sexpr_to_string @@ Tactic_sexpr.tactic_sexpr @@ tac in
  Feedback.msg_warning Pp.(str tacstr ++ str tacsexpr)

let modify_internal_tactics_setting str tac =
  match tac with
  | TacAlias CAst.{v=(kername, _); _} ->
    Lib.add_anonymous_leaf
      (internal_tactics_setting (StringMap.add str kername (get_internal_tactics_settings ())))
  | _ -> CErrors.user_err (Pp.str "A stub of a tactic alias was expected but not found")

let outer_record ast = match ast_setting_lookup ast with
  | Keep | Both -> true
  | Decompose | Discard -> false

let inner_record ast = match ast_setting_lookup ast with
  | Decompose | Both -> true
  | Keep | Discard -> false

let decompose_annotate (tac : glob_tactic_expr) (r : glob_tactic_expr -> glob_tactic_expr -> glob_tactic_expr) : glob_tactic_expr =
  let rself t = r t t in
  let mkatom loc atom =
    let t = TacAtom (CAst.make ?loc:loc atom) in
    rself t in
  let tacthenfirst t1 t2 = TacThens3parts (t1, Array.of_list [t2], TacId [], Array.of_list []) in
  let tacthenlast  t1 t2 = TacThens3parts (t1, Array.of_list [], TacId [], Array.of_list [t2]) in
  let mktmp i = Names.Id.of_string ("_tmp_tactician" ^ string_of_int i) in
  let clear xs =
    let clear = internal_tactics_ref_lookup "clear" in
    let xs = TacGeneric (Genarg.in_gen (Genarg.glbwit (Genarg.wit_list Stdarg.wit_var)) xs) in
    let tac = TacAlias (CAst.make (clear, [xs])) in
    rself tac in
  let rec expand_intro_pattern ?(def_name:Names.Id.t option) loc i eflg (p : _ Tactypes.intro_pattern_expr CAst.t)
    : _ Tactypes.intro_pattern_expr CAst.t * int * ((int -> glob_tactic_expr) -> int -> glob_tactic_expr) =
    let open Tactypes in
    let mktmp i =
      match def_name with
      | None -> mktmp i, i+1
      | Some id -> id, i in
    match p.v with
    | IntroForthcoming _ -> p, i, (fun cont i -> cont i)
    | IntroNaming _ -> p, i, (fun cont i -> cont i)
    | IntroAction a -> (match a with
        | IntroWildcard ->
          let id, i = mktmp i in
          (* The try is needed because in some cases other actions like IntroRewrite will already have removed the hyp *)
          let tac = TacTry (clear [CAst.make id]) in
          CAst.make ?loc:p.loc @@ IntroNaming (Namegen.IntroIdentifier id), i+1, (fun cont i -> TacThen (cont i, tac))
        | IntroOrAndPattern ps ->
          let id, i = mktmp i in
          let destruct ps = mkatom loc @@ TacInductionDestruct
              (false, false (* Intentionally set to false because edestruct does not delete the original variable *),
               ([(None, Tactics.ElimOnIdent (CAst.make id)),
                              (None, Some (ArgArg (CAst.make ps))), None], None)) in
          let destruct_then ps tacs =
            TacThens3parts (destruct ps, Array.of_list [], TacId [],
                            Array.of_list tacs) in
            (* TacThen (destruct ps, cont (CAst.make ?loc:p.loc @@ IntroNaming (Namegen.IntroIdentifier id)) i) in *)
          CAst.make ?loc:p.loc @@ IntroNaming (Namegen.IntroIdentifier id), i+1,
          (fun cont_final i ->
             match ps with
             | IntroOrPattern ps ->
               (match ps with
                (* The special pattern `[]` is very nasty and there does not seem a way to properly decompose it.
                   The reason is that we don't know how many subgoals it generates, and which of those are side-conditions.
                   This is a partial attempt where we assume that no side-conditions occur *)
                | [[]] ->
                  TacThen (destruct (IntroOrPattern [[]]), cont_final i)
                | _ ->
                  let expanded = List.map (fun ps -> expand_intro_patterns loc eflg i ps) ps in
                  let ps = IntroOrPattern (List.map (fun (ps, _, _) -> ps) expanded) in
                  destruct_then ps @@ List.map (fun (_, i, cont) -> cont cont_final i) expanded)
             | IntroAndPattern ps ->
               let ps, i, cont = expand_intro_patterns loc eflg i ps in
               let ps = IntroAndPattern ps in
               destruct_then ps @@ [cont cont_final i]
          )
        | IntroInjection ps ->
          let id, i = mktmp i in
          CAst.make ?loc:p.loc @@ IntroNaming (Namegen.IntroIdentifier id), i+1,
          (fun cont_final i ->
              let destr_arg = None, Tactics.ElimOnIdent (CAst.make id) in
              let destr_arg = TacGeneric (Genarg.in_gen (Genarg.glbwit Tacarg.wit_destruction_arg) destr_arg) in
              let injection =
                let injection = internal_tactics_ref_lookup "injection_x_as" in
                let ps, i, cont = expand_intro_patterns loc eflg i ps in
                let cont i = cont cont_final i in
                let ps = TacGeneric (Genarg.in_gen (Genarg.glbwit (Genarg.wit_list Tacarg.wit_simple_intropattern)) ps) in
                let injection = rself @@ TacAlias (CAst.make (injection, [destr_arg; ps])) in
                TacThen (injection, cont i) in
              let discriminate = internal_tactics_ref_lookup "discriminate_x" in
              let discriminate = rself @@ TacAlias (CAst.make (discriminate, [destr_arg])) in
              let hyp = TacGeneric (Genarg.in_gen (Genarg.glbwit Stdarg.wit_var) (CAst.make id)) in
              let intro_equality_clear = internal_tactics_ref_lookup "intro_equality_clear" in
              let intro_equality_clear = rself @@ TacAlias (CAst.make (intro_equality_clear, [hyp])) in
              let intro_equality_hnf = internal_tactics_ref_lookup "intro_equality_hnf" in
              let intro_equality_hnf = rself @@ TacAlias (CAst.make (intro_equality_hnf, [hyp])) in
              TacFirst
                [ TacThen (discriminate, cont_final i)
                ; injection (* Continuation already inserted *)
                ; TacThen (intro_equality_clear, cont_final i)
                ; TacThen (intro_equality_hnf, cont_final i)])
        | IntroApplyOn (t, p) ->
          let id, i = mktmp i in
          CAst.make ?loc:p.loc @@ IntroNaming (Namegen.IntroIdentifier id), i+1, (fun cont_final i -> 
              let p, i, cont = expand_intro_pattern ~def_name:id loc 0 eflg p in
              let cont = cont cont_final i in
              let apply = mkatom loc @@
                TacApply (true, eflg, [None, (t.v, NoBindings)], (Some (CAst.make id, Some p))) in
              let apply = tacthenfirst apply cont in
              let tac = TacThen (apply, TacTry (clear [CAst.make id])) in
              tac)
        | IntroRewrite d ->
          let id, i = mktmp i in
          let rewrite = if d then internal_tactics_ref_lookup "intropattern_subst_l"
            else internal_tactics_ref_lookup "intropattern_subst_r" in
          let hyp = TacGeneric (Genarg.in_gen (Genarg.glbwit Stdarg.wit_var) (CAst.make id)) in
          let rewrite = rself @@ TacAlias (CAst.make (rewrite, [hyp])) in
          CAst.make ?loc:p.loc @@ IntroNaming (Namegen.IntroIdentifier id), i+1,
          (fun cont i -> TacThen (rewrite, cont i))
      )
  and expand_intro_patterns loc eflg i (ps : _ Tactypes.intro_pattern_expr CAst.t list) :
    _ Tactypes.intro_pattern_expr CAst.t list * int * ((int -> glob_tactic_expr) -> int -> glob_tactic_expr) =
    let rec aux ps ps_acc expand_acc i =
      match ps with
      | [] -> List.rev ps_acc, i,
              (fun (cont : int -> glob_tactic_expr) ->
                 List.fold_left (fun acc expand ->
                     expand acc
                   ) cont expand_acc)
      | p::ps ->
        let (p, i, expand) = expand_intro_pattern loc i eflg p in
        aux ps (p::ps_acc) (expand::expand_acc) i in
    aux ps [] [] i
        (* let k = List.fold_right (fun CAst.{v=p; loc} (acc, (i, tac)) -> *)
    (*     let p, tac', i = expand_intro_pattern loc i eflg p cont in *)
    (*     let tac = match tac, tac' with *)
    (*       | None, None -> None *)
    (*       | None, Some t c' -> Some tac' *)
    (*       | Some tac, None -> Some tac *)
    (*       | Some tac, Some tac' -> Some (TacThen (tac', tac)) in *)
    (*     (CAst.make ?loc p)::acc, (i, tac)) *)
    (*     p ([], (i, None)) in *)
  in
  let decompose_single_apply aflg eflg intro loc s =
    let apply intro = mkatom loc @@
      TacApply (aflg, eflg, [s], intro) in
    match intro with
    | None -> apply None
    | Some (id, pat) -> (match pat with
        | None -> apply (Some (id, None))
        | Some ps ->
          let ps, i, cont = expand_intro_pattern ~def_name:id.v loc 0 eflg ps in
          let tac = cont (fun _ -> TacId []) i in
          tacthenfirst (apply (Some (id, Some ps))) tac
      ) in
  let decompose_apply aflg eflg intro loc (ls : 'trm with_bindings_arg list) =
    let intro' = Option.map (fun (n, _) -> (n, None)) intro in
    let combiner = match intro with | None -> tacthenlast | Some _ -> tacthenfirst in
    let rec aux = function
      | [] -> assert false
      | [s] -> decompose_single_apply aflg eflg intro loc s
      | s::ls -> combiner (decompose_single_apply aflg eflg intro' loc s) (aux ls)
    in aux ls in
  let decompose_generalize loc ls =
    let rec aux = function
      | [] -> assert false
      | [s] -> mkatom loc (TacGeneralize [s])
      | s::ls -> TacThen (mkatom loc (TacGeneralize [s]), aux ls)
    in aux ls in
  let decompose_single_destruct loc eflg (c, (eqn, asc), inc) =
    match eqn, inc, asc with
    | None, None, Some (ArgArg (CAst.{v=Tactypes.IntroAndPattern ps; _})) ->
      let ps, i, cont = expand_intro_patterns loc eflg 0 ps in
      let destruct = mkatom loc @@
        TacInductionDestruct (false, eflg,
                              ([c, (eqn, Some (ArgArg (CAst.make (Tactypes.IntroAndPattern ps)))), inc], None)) in
      let tac = cont (fun _ -> TacId []) i in
      TacThens3parts (destruct, Array.of_list [], TacId[],
                      Array.of_list @@ [tac])
    | None, None, Some (ArgArg (CAst.{v=Tactypes.IntroOrPattern ps; _})) ->
      let expanded = List.map (expand_intro_patterns loc eflg 0) ps in
      let ps = Tactypes.IntroOrPattern (List.map (fun (ps, _, _) -> ps) expanded) in
      let destruct =
        mkatom loc @@ TacInductionDestruct
          (false, eflg, ([c, (eqn, Some (ArgArg (CAst.make ps))), inc], None)) in
      let tacs = List.map (fun (_, i, cont) -> cont (fun _ -> TacId []) i) expanded in
      TacThens3parts (destruct, Array.of_list [], TacId[],
                      Array.of_list tacs)
    | _ ->
      mkatom loc @@ TacInductionDestruct (false, eflg, ([c, (eqn, asc), inc], None)) in
  let decompose_destruct loc eflg ls =
    let rec aux = function
      | [] -> assert false
      | [s] -> decompose_single_destruct loc eflg s
      | s::ls -> TacThen (decompose_single_destruct loc eflg s, aux ls)
    in
    let tac = aux ls in
    (* Feedback.msg_info (Pptactic.pr_glob_tactic (Global.env ()) tac); *)
    tac
    in
  let decompose_multi loc flg inc b trm by byorig mult = (* TODO: Maybe replace this with an OCaml-level tactic? *)
    let recname = CAst.make @@ Names.Id.of_string "rec" in
    let recname' = CAst.make @@ Names.Name.mk_name recname.v in
    let reccall = TacArg (CAst.make (Reference (ArgVar recname))) in
    (* TODO: Why can't we use the 'do' and 'repeat' tactics here again? *)
    let repeat tac = TacLetIn (true, [(recname', Tacexp (TacTry (tacthenfirst tac reccall)))], reccall) in
    let rec don n tac = if n > 0 then tacthenfirst tac (don (n-1) tac) else TacId [] in
    let onerewrite =
      let rew = mkatom loc @@ TacRewrite (flg, [(b, Precisely 1, trm)], inc, None) in
      match by with
      | None -> rew
      | Some by -> TacThens3parts (rew, Array.of_list [TacId []], TacSolve [by], Array.of_list [])in
    let at r = match mult with
      | Precisely 1 -> onerewrite
      | Precisely n -> r (don n (onerewrite))
      | RepeatStar -> r (repeat (onerewrite))
      | RepeatPlus -> r (tacthenfirst (onerewrite) (repeat (onerewrite)))
      | UpTo n -> r (don n (TacTry (onerewrite))) in
    let r = if outer_record RewriteMulti then r (TacAtom (CAst.make ?loc:loc (TacRewrite (flg, [(b, mult, trm)], inc, byorig)))) else fun x -> x in
    if inner_record RewriteMulti then at r else r (TacAtom (CAst.make ?loc:loc (TacRewrite (flg, [(b, mult, trm)], inc, byorig)))) in
  let decompose_rewrite loc flg inc ls by byorig =
    let rec aux = function
      | [] -> assert false
      | [(b, mult, trm)] -> decompose_multi loc flg inc b trm by byorig mult
      | (b, mult, trm)::ls -> tacthenfirst (decompose_multi loc flg inc b trm by byorig mult) (aux ls)
    in aux ls in
  let intro_patterns_convert eflg loc (ps : _ Tactypes.intro_pattern_expr CAst.t list) =
    let open Tacexpr in
    let open Tactypes in
    let rec aux ps i =
      match ps with
      | [] -> TacId []
      | p::ps ->
        let (p, i, expand) = expand_intro_pattern loc i eflg p in
        let cont i =
          aux ps i in
        let tac = expand cont i in
        let intro = mkatom loc @@ TacIntroPattern (eflg, [p]) in
        TacThen (intro, tac) in
    aux ps 0 in
    (* if n > 0 then *)
    (*   (\* TODO: The TacTry is not correct *\) *)
    (*   TacThen (intros, TacTry clear) *)
    (* else intros in *)
  let rec annotate_atomic a : glob_tactic_expr =
    let router ast t = if outer_record ast then r (TacAtom a) t else t in
    let at = TacAtom a in
    match a.v with
    | TacIntroPattern (eflg, ls) ->
      let at = if (inner_record IntroPattern) then
          intro_patterns_convert eflg a.loc ls
        else at in
      (* Feedback.msg_info (Pptactic.pr_glob_tactic (Global.env ()) at); *)
      router IntroPattern at
    | TacApply (aflg, eflg, ls, intro) ->
      let at = if (inner_record Apply) then decompose_apply aflg eflg intro a.loc ls else at in
      (* Feedback.msg_info (Pptactic.pr_glob_tactic (Global.env ()) at); *)
      router Apply at
    | TacElim _ -> router Elim at
    | TacCase _ -> router Case at
    | TacMutualFix _ -> router MutualFix at
    | TacMutualCofix _ -> router MutualCofix at
    | TacAssert (flg, b, by, pat, term) ->
      let tac = if inner_record Assert then
          match by with
          | None -> rself at (* pose proof *)
          | Some by -> match by with  (* pose and assert *)
            | None -> rself at (* Nothing to decompose *)
            | Some by ->
              let by = annotate by in
              tacthenfirst (mkatom a.loc @@ TacAssert (flg, b, Some None, pat, term)) by
        else
          at in
      router Assert tac
    | TacGeneralize gs ->
      let at = if inner_record Generalize then decompose_generalize a.loc (List.rev gs) else at in
      router Generalize at
    | TacLetTac _ -> router LetTac at
    (* This is induction .. using .., which is not decomposable *)
    | TacInductionDestruct (_, _, (_, Some _)) -> rself at
    (* TODO: induction a, b is not equal to induction a; induction b due to name mangling *)
    | TacInductionDestruct (true, _, _) -> rself at
    | TacInductionDestruct (false, eflg, (ts, None)) ->
      let at = if inner_record InductionDestruct then decompose_destruct a.loc eflg ts else at in
      router InductionDestruct at
    | TacReduce (expr, occ) ->
      let open Genredexpr in
      (match expr with
       | Unfold ls ->
         let at = if inner_record Reduce then
             List.fold_left (fun tac u ->
                 let unfold = mkatom a.loc @@ TacReduce (Unfold [u], occ) in
                 TacThen (tac, unfold)
               ) (TacId []) ls
           else at in
         router Reduce at
       | _ -> rself at)
    | TacChange _ -> router Change at
    | TacRewrite (flg1, ts, i, d) ->
      let at = if inner_record Rewrite then decompose_rewrite a.loc flg1 i ts (Option.map annotate d) d else at in
      router Rewrite at
    | TacInversion _ -> router Inversion at
  and annotate_arg x =
    match x with
    | TacGeneric _ -> x, r (* TODO: Deal with ssreflect stuff *)
    | ConstrMayEval _ -> x, r
    | Reference k ->
      (match k with
       | ArgArg _ -> x, r
       | ArgVar _ ->
         (* Feedback.msg_warning (Pp.str "reference encountered"); *)
         (* We intentionally do not record references. The assumption here is that the tactical expression
            they reference has already been instrumented. *)
         x, fun x _ -> x)
    | TacCall c -> (if inner_record Call then
        TacCall (CAst.map (fun (a, b) -> (a, List.map (fun a -> fst (annotate_arg x)) b)) c) else x), r
    | TacFreshId _ -> x, r
    | Tacexp t -> Tacexp (annotate t), fun x _ -> x
    | TacPretype _ -> x, r
    | TacNumgoals -> x, r
  (* TODO: Improve efficiency of the annotation recursion *)
  and annotate (tac : glob_tactic_expr) : glob_tactic_expr =
    let router ast t = if outer_record ast then r tac t else t in
    let rinner ast t = if inner_record ast then annotate t else t in
    match tac with
    | TacAtom a         ->                 annotate_atomic a
    | TacThen (t1, t2)  ->                 router Then (TacThen (rinner Then t1, rinner Then t2))
    | TacDispatch tl    ->                 router Dispatch (TacDispatch (List.map (rinner Dispatch) tl))
    | TacExtendTac (tl1, t, tl2) ->        router Extend (TacExtendTac (Array.map (rinner Extend) tl1,
                                                                        rinner Extend t,
                                                                        Array.map (rinner Extend) tl2))
    | TacThens (t1, tl) ->                 router Thens (TacThens (rinner Thens t1, List.map (rinner Thens) tl))
    | TacThens3parts (t1, tl1, t2, tl2) ->
      router Thens3parts (TacThens3parts (rinner Thens3parts t1,
                                           Array.map (rinner Thens3parts) tl1,
                                           rinner Thens3parts t2,
                                           Array.map (rinner Thens3parts) tl2))
    | TacFirst ts       ->                 router First (TacFirst (List.map (rinner First) ts))
    | TacComplete t     ->                 router Complete (TacComplete (rinner Complete t))
    | TacSolve ts       ->                 router Solve (TacSolve (List.map (rinner Solve) ts))
    | TacTry t          ->                 TacTry (annotate t) (* No need to record try *)
    | TacOr (t1, t2)    ->                 router Or (TacOr (rinner Or t1, rinner Or t2))
    | TacOnce t         ->                 router Once (TacOnce (rinner Once t))
    | TacExactlyOnce t  ->                 router ExactlyOnce (TacExactlyOnce (rinner ExactlyOnce t))
    | TacIfThenCatch (t1, t2, t3) ->       router IfThenCatch (TacIfThenCatch (rinner IfThenCatch t1,
                                                                               rinner IfThenCatch t2,
                                                                               rinner IfThenCatch t3))
    | TacOrelse (t1, t2) ->                router Orelse (TacOrelse (rinner Orelse t1, rinner Orelse t2))
    | TacDo (n, t) ->                      router Do (TacDo (n, rinner Do t)) (* TODO: Perform decomposition when n is a number *)
    | TacTimeout (n, t)      ->            router Timeout (TacTimeout (n, rinner Timeout t))
    | TacTime (s, t)         ->            TacTime (s, annotate t) (* No need to record try *)
    | TacRepeat t       ->                 router Repeat (TacRepeat (rinner Repeat t))
    | TacProgress t     ->                 router Progress (TacProgress (rinner Progress t))
    | TacShowHyps t     ->                 TacShowHyps (annotate t) (* No need to record infoH *)
    | TacAbstract (t, id) ->               router Abstract (TacAbstract (rinner Abstract t, id))
    | TacId _           ->                 tac (* No need to record id *)
    | TacFail _         ->                 tac (* No need to record fail *)
    | TacInfo t         ->                 TacInfo (annotate t) (* No need to record info *)
    | TacLetIn (false, args, t) ->
      (* let register tac name = *)
      (*   let fullname = {mltac_plugin = "recording"; mltac_tactic = name} in *)
      (*   Tacenv.register_ml_tactic fullname [| tac |] in *)
      (* let internal_tac args is = *)
      (*   Feedback.msg_warning (Pp.str "internal"); *)
      (*   Tacinterp.eval_tactic_ist is t *)
      (*   (\* (\\*let num = Tacinterp.Value.cast (Genarg.topwit Tacarg.wit_tactic) (List.hd args) in*\\) *\) *)
      (*   (\* let tac = Tacinterp.Value.cast (Genarg.topwit wit_glbtactic) (List.hd args) in *\) *)
      (*   (\* Feedback.msg_warning Pp.(str "Strict failure: " ++ Pptactic.pr_glob_tactic (Global.env ()) tac); *\) *)
      (*   (\* Proofview.tclUNIT () *\) in *)

      (* let () = register internal_tac "internal_tac" in *)
      (* let t : glob_tactic_expr = *)
      (*   TacML (CAst.make ({mltac_name = {mltac_plugin = "recording"; mltac_tactic = "internal_tac"}; mltac_index = 0}, *)
      (*                     [])) in *)
      let all_tacs = List.map (fun (id, arg) ->
          (match arg with
           | Tacexp _ -> true
           | _ -> false)) args in
      let all_tacs = List.fold_left (&&) true all_tacs in
      if all_tacs then
        let args = List.map (fun (a, b) -> (a, fst (annotate_arg b))) args in
        TacLetIn (false, args, annotate t)
      else
        rself tac
    | TacLetIn (true, args, t) ->
      router LetIn (TacLetIn (true, args, rinner LetIn t))
    | TacMatch (flg, t, ts) ->
      router Match (TacMatch (flg, rinner Match t,
                              List.map (function | All t -> All (rinner Match t)
                                                 | Pat (c, p, t) -> Pat (c, p, rinner Match t)) ts))
    | TacMatchGoal (flg, d, ts) ->
      router MatchGoal (TacMatchGoal (
          flg, d, List.map (function | All t -> All (rinner MatchGoal t)
                                     | Pat (c, p, t) -> Pat (c, p, rinner MatchGoal t)) ts))
    | TacFun (args, t) -> TacFun (args, annotate t) (* Probably not outer-recordable *)
    | TacArg x ->
      let x', r2 = if inner_record Arg then annotate_arg x.v else x.v, r in
      let res = r2 tac @@ TacArg (CAst.make ?loc:x.loc x') in
      if outer_record Arg then r tac res else res
    | TacSelect (i, t)       ->            router Select (TacSelect (i, rinner Select t))
    | TacML CAst.{loc; v=(e, args)} ->
      let args = if inner_record ML then List.map (fun a -> fst (annotate_arg a)) args else args in
      router ML (TacML (CAst.make ?loc (e, args))) (* TODO: Decompose interesting known tactics (such as ssreflect) *)
    | TacAlias CAst.{loc; v=(e, args)} ->
      let tactician_cache = CString.is_prefix "Tactician.Ltac1.Tactics.search_with_cache"
          (Names.KerName.to_string e) in
      let al = Tacenv.interp_alias e in
      match ast_alias_setting_lookup e with
      | Decompose | Both ->
        let args = List.map (fun a -> fst (annotate_arg a)) args in
        TacLetIn (false, List.map2 (fun x y ->
            (CAst.make (Names.Name.Name x)), y) al.Tacenv.alias_args args,
                  annotate al.Tacenv.alias_body)
      | Keep | Discard ->
        match e, args with
        | e, [TacGeneric term; TacGeneric pat] when Names.KerName.equal e @@ internal_tactics_ref_lookup "injection_x_as" ->
          let pat = Genarg.out_gen (Genarg.glbwit (Genarg.wit_list Tacarg.wit_simple_intropattern)) pat in
          let pat = match pat with
            (* This seems to be some bizarre syntactical special case *)
          | [CAst.{v=Tactypes.IntroAction (Tactypes.IntroInjection pat); loc}] -> pat
          | _ -> pat in
          let pat, i, cont = expand_intro_patterns loc false 0 pat in
          let pat = Genarg.in_gen (Genarg.glbwit (Genarg.wit_list Tacarg.wit_simple_intropattern)) pat in
          let cont = cont (fun _ -> TacId []) i in
          let tac = TacAlias (CAst.make ?loc (e, [TacGeneric term; TacGeneric pat])) in
          let tac = TacThen (rself tac, cont) in
          tac
        | e, [s; t; cls; TacGeneric by] when Names.KerName.equal e @@ internal_tactics_ref_lookup "replace_with_by" ->
          let by = Genarg.out_gen (Genarg.glbwit Extraargs.wit_by_arg_tac) by in
          let by' = TacGeneric (Genarg.in_gen (Genarg.glbwit Extraargs.wit_by_arg_tac) None) in
          let tac = TacAlias (CAst.make ?loc (e, [s; t; cls; by'])) in
          (match by with
          | None -> tac
          | Some by -> tacthenlast (rself tac) (annotate by))
        | e, [TacGeneric id;] when Names.KerName.equal e @@ internal_tactics_ref_lookup "intro_x" ->
          let id = Genarg.out_gen (Genarg.glbwit Stdarg.wit_ident) id in
          mkatom loc (TacIntroPattern (false, [CAst.make (Tactypes.IntroNaming (Namegen.IntroIdentifier id))]))
        | e, [] when Names.KerName.equal e @@ internal_tactics_ref_lookup "intro" ->
          mkatom loc (TacIntroPattern (false, [CAst.make (Tactypes.IntroNaming Namegen.IntroAnonymous)]))
        | _ ->
          let args = if inner_record Alias || tactician_cache then
              List.map (fun a -> fst (annotate_arg a)) args else args in
          let t = TacAlias (CAst.make ?loc (e, args)) in
          if outer_record Alias && not tactician_cache then r tac t else t
    in annotate tac
