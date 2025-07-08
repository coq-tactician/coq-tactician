open Ltac_plugin
open Monad_util
open Genarg
open Names
open Map_all_the_things

module CookTacticDef = struct
  module M = ReaderWriterMonad
      (struct type w = Id.Set.t * Cset.t * Mindset.t
        let id = Id.Set.empty, Cset.empty, Mindset.empty
        let comb (ids1, cs1, is1) (ids2, cs2, is2) =
          Id.Set.union ids1 ids2, Cset.union cs1 cs2, Mindset.union is1 is2 end)
      (struct type r = Id.Set.t end)
  include MapDefTemplate (M)
  let map_sort = "cook-tactic"
  let warnProblem wit =
    Feedback.msg_warning (Pp.(str "Tactician is having problems with " ++
                              str "the following tactic. Please report. " ++
                              pr_argument_type wit))
  let default wit = { raw = (fun _ -> warnProblem (ArgumentType wit); id)
                    ; glb = (fun _ -> warnProblem (ArgumentType wit); id)}
  let with_binders ids' a cont =
    map (fun x -> (fun x -> x), x) @@
    M.local (fun ids -> List.fold_left (fun ids id -> Id.Set.add id ids) ids ids') @@ cont a
end
module CookTacticMapper = MakeMapper(CookTacticDef)
open CookTacticDef

let tell_id id = M.tell (Id.Set.singleton id, Cset.empty, Mindset.empty)
let tell_const c = M.tell (Id.Set.empty, Cset.singleton c, Mindset.empty)
let tell_ind m = M.tell (Id.Set.empty, Cset.empty, Mindset.singleton m)

let empty_ltac_context =
  Ltac_pretype.{ ltac_constrs = Id.Map.empty
               ; ltac_uconstrs = Id.Map.empty
               ; ltac_idents = Id.Map.empty
               ; ltac_genargs = Id.Map.empty }

let detype env evd avoid c =
  (* During term interpretation, new evars may have been created. We want those evars to be turned (back)
     into holes. That is what the code below is trying to do (in a rather convoluted way). *)
  let rec add_names (evd, idc) c = match EConstr.kind evd c with
    | Constr.Evar (e, _) ->
      (match Evd.evar_ident e evd with
       | None ->
         Evd.rename e (Id.of_string_soft ("__hole_evar" ^ string_of_int idc)) evd, (idc + 1)
       | Some _ -> evd, idc)
    | _ -> EConstr.fold evd add_names (evd, idc) c in
  let evd', _ = add_names (evd, 0) c in
  let c = Detyping.detype Detyping.Now true avoid env evd' c in
  let rec evar_to_hole c = match DAst.get c with
    | Glob_term.GEvar (id, _) ->
      (try
        let _ = Evd.evar_key id evd in
        c
      with Not_found ->
        DAst.make (Glob_term.GHole (snd @@ Evd.evar_source (Evd.evar_key id evd') evd',
                                    Namegen.IntroAnonymous, None)))
    | _ -> Glob_ops.map_glob_constr evar_to_hole c in
  evar_to_hole c

let warn env t =
  Feedback.msg_warning Pp.(str "Tactic could not be properly discharged: " ++
                           Pptactic.pr_glob_tactic env t)

let mapper orig env evd worklist cook_cs cook_is =
  { CookTacticDef.default_mapper with
    variable = (fun id -> tell_id id >> return id)
  ; constant = (fun c -> tell_const c >> return c)
  ; mutind = (fun m -> tell_ind m >> return m)
  ; glob_constr_and_expr = (fun t c ->
      let* bound = M.ask in
      let* a, (ids, cs, is) = M.listen (c t) in
      if (not @@ Cset.is_empty @@ Cset.inter cook_cs cs ||
          not @@ Mindset.is_empty @@ Mindset.inter cook_is is) then
        if not @@ Id.Set.disjoint bound ids then
          (warn env orig;
           return a) else
          try
            let (evd, typed) = Pretyping.understand_ltac (Pretyping.no_classes_no_fail_inference_flags) env evd
                empty_ltac_context
                Pretyping.WithoutTypeConstraint (fst a) in
            let typed = EConstr.to_constr ~abort_on_undefined_evars:false evd typed in
            (* TODO: Consider writing a glob_term, constrexpr and pattern version of Cooking.expmod_constr.
               That way we no longer have to interpret terms and we will get better accuracy. *)
            let typed = Cooking.expmod_constr worklist typed in
            let detyped = detype env evd bound (EConstr.of_constr typed) in
            return (detyped, None)
          with
          | CErrors.Timeout as e ->
            raise e
          | _ ->
            warn env orig;
            return a
      else return a
    )
  ; glob_constr_pattern_and_expr = (fun t c ->
      let* bound = M.ask in
      let* a, (ids, cs, is) = M.listen (c t) in
      let (pids, (r, _), _) = t in
      if (not @@ Cset.is_empty @@ Cset.inter cook_cs cs ||
          not @@ Mindset.is_empty @@ Mindset.inter cook_is is) then
        if not @@ Id.Set.disjoint bound ids then
          (warn env orig;
           return a) else
          try
            let (evd', typed) = Pretyping.understand_ltac (Pretyping.no_classes_no_fail_inference_flags) env evd
                empty_ltac_context
                Pretyping.WithoutTypeConstraint r in
            let typed' = EConstr.to_constr ~abort_on_undefined_evars:false evd' typed in
            let r = detype env evd' bound typed in
            let t = (pids, (r, None), Patternops.pattern_of_constr env evd' typed') in
            return t
          with
          | CErrors.Timeout as e ->
            raise e
          | _ ->
            warn env orig;
            return t
      else return t)
  }

let discharge t env evd worklist =
  let cook_cs = Cmap.domain @@ fst worklist in
  let cook_is = Mindmap.domain @@ snd worklist in
  let (_, _, _), t' = M.run (CookTacticMapper.glob_tactic_expr_map (mapper t env evd worklist cook_cs cook_is) t)
      Id.Set.empty in
  t'
