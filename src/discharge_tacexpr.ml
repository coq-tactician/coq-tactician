open Ltac_plugin
open Monad_util
open Genarg
open Names
open Map_all_the_things
(* open Cooking *)

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
  (* modified in 8.18 *)
  (* ~avoid:(Namegen.Generator.idset,avoid) introduced in 9.0 *)
  let c = Detyping.detype Detyping.Now ~isgoal:true ~avoid:(Namegen.Generator.idset,avoid) env evd' c in
  let rec evar_to_hole c = match DAst.get c with
    | Glob_term.GEvar (id, _) ->
      (try
        let _ = Evd.evar_key id.v evd in
        c
      with Not_found ->
        (* Introduced in 8.17: (Evd.find evd' (Evd.evar_key id.v evd')) is a evar_info *)
        match Evd.find evd' (Evd.evar_key id.v evd') with 
        | EvarInfo ei -> 
          (* Introduced in 8.18 *)
          (* DAst.make (Glob_term.GHole (snd @@ Evd.evar_source ei,
          (* DAst.make (Glob_term.GHole (snd @@ Evd.evar_source (Evd.evar_key id.v evd') evd', *)
                                      Namegen.IntroAnonymous))) *)
          (* Introduced in 8.19 *)
          DAst.make (Glob_term.GHole Evar_kinds.GInternalHole)
          )
    | _ -> Glob_ops.map_glob_constr evar_to_hole c in
  evar_to_hole c

let warn env t =
  Feedback.msg_warning Pp.(str "Tactic could not be properly discharged: " ++
                           Pptactic.pr_glob_tactic env t)

let expmod_constr info c =
  let c = Cooking.abstract_as_body info c in
  let rels = Cooking.rel_context_of_cooking_cache info in
  let n_assums = Context.Rel.length rels in
  let _, c = Term.decompose_lambda_n_decls n_assums c in
  let args = List.map (fun d -> Constr.mkVar @@ Context.Named.Declaration.get_id d) @@
    List.map (Context.Named.Declaration.of_rel_decl (function
      | Names.Name.Anonymous -> assert false
      | Names.Name.Name id -> id)) rels in
  Vars.substl args c

let constr_pattern_to_uninstantiated_pattern_gen f : Util.Empty.t Pattern.constr_pattern_r -> 'b Pattern.constr_pattern_r = function
  | PApp (p,pl) -> PApp (f p, Array.map f pl)
  | PSoApp (n,pl) -> PSoApp (n, List.map f pl)
  | PLambda (n,a,b) -> PLambda (n,f a,f b)
  | PProd (n,a,b) -> PProd (n,f a,f b)
  | PLetIn (n,a,t,b) -> PLetIn (n,f a,Option.map f t,f b)
  | PIf (c,b1,b2) -> PIf (f c,f b1,f b2)
  | PCase (ci,po,p,pl) ->
    let map_branch (i, n, c) = (i, n, f c) in
    let po = Option.map (fun (nas, po) -> nas, (f po)) po in
    PCase (ci,po,f p, List.map map_branch pl)
  | PProj (p,pc) -> PProj (p, f pc)
  | PFix (lni,(lna,tl,bl)) ->
     PFix (lni,(lna,Array.map f tl,Array.map f bl))
  | PCoFix (ln,(lna,tl,bl)) ->
     PCoFix (ln,(lna,Array.map f tl,Array.map f bl))
  | PArray (t,def,ty) -> PArray (Array.map f t, f def, f ty)
  | PEvar (ev,ps) -> PEvar (ev, List.map f ps)
  | PExtra x -> Util.Empty.abort x
  (* Non recursive *)
  | (PVar _ | PRel _ | PRef _  | PSort _  | PMeta _ | PInt _
    | PFloat _ | PString _ as x) -> x

let rec constr_pattern_to_uninstantiated_pattern pt = constr_pattern_to_uninstantiated_pattern_gen constr_pattern_to_uninstantiated_pattern pt

let mapper orig env evd worklist =
  { CookTacticDef.default_mapper with
    variable = (fun id -> tell_id id >> return id)
  ; constant = (fun c -> tell_const c >> return c)
  ; mutind = (fun m -> tell_ind m >> return m)
  ; glob_constr_and_expr = (fun t c -> 
      let* bound = M.ask in
      let* a, (ids, cs, is) = M.listen (c t) in
      (* if (not @@ Cset.is_empty @@ Cset.inter cook_cs cs ||
          not @@ Mindset.is_empty @@ Mindset.inter cook_is is) then *)
        if not @@ Id.Set.disjoint bound ids then
          (warn env orig;
           (* Feedback.msg_warning (Pp.(str "normal here")); *)
           return a) else
          try
            let (evd, typed) = Pretyping.understand_ltac (Pretyping.no_classes_no_fail_inference_flags) env evd
                empty_ltac_context
                Pretyping.WithoutTypeConstraint (fst a) in
            let typed = EConstr.to_constr ~abort_on_undefined_evars:false evd typed in
            (* TODO: Consider writing a glob_term, constrexpr and pattern version of Cooking.expmod_constr.
               That way we no longer have to interpret terms and we will get better accuracy. *)
            let typed = expmod_constr worklist typed in
            let detyped = detype env evd bound (EConstr.of_constr typed) in
            return (detyped, None)
          with
          | Control.Timeout as e ->
            raise e
          | _ ->
            (* Feedback.msg_warning (Pp.(str "exception here")); *)
            warn env orig;
            return a
      (* else return a *)
    )
  ; glob_constr_pattern_and_expr = (fun t c ->
      let* bound = M.ask in
      let* a, (ids, cs, is) = M.listen (c t) in
      let (pids, (r, _), _) = t in
      (* if (not @@ Cset.is_empty @@ Cset.inter cook_cs cs ||
          not @@ Mindset.is_empty @@ Mindset.inter cook_is is) then *)
        if not @@ Id.Set.disjoint bound ids then
          (warn env orig;
           return a) else
          try
            let (evd', typed) = Pretyping.understand_ltac (Pretyping.no_classes_no_fail_inference_flags) env evd
                empty_ltac_context
                Pretyping.WithoutTypeConstraint r in
            let typed' = EConstr.to_constr ~abort_on_undefined_evars:false evd' typed in
            (* TODO 8.16: put expmod_constr here *)
            let r = detype env evd' bound typed in
            (* uninstantiated_pattern introduced in dev : Aug 13 2025 *)
            let uninst = constr_pattern_to_uninstantiated_pattern @@ Patternops.pattern_of_constr env evd' (EConstr.of_constr typed') in 
            let t = (pids, (r, None), uninst) in
            return t
          with
          | Control.Timeout as e ->
            raise e
          | _ ->
            warn env orig;
            return t
      (* else return t *)
      )
  }

(* let discharge t env evd worklist = *)
let discharge t env evd (cache : Cooking.cooking_cache) =
  (* let cook_cs = Cmap.domain @@ fst worklist in
  let cook_is = Mindmap.domain @@ snd worklist in *)
  (* let cache = Cooking.create_cache info in *)
  (* let x = Section. in *)
  let (_, _, _), t' = M.run (CookTacticMapper.glob_tactic_expr_map (mapper t env evd cache) t)
      Id.Set.empty in
  t'
