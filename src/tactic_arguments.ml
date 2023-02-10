open Map_all_the_things
open Names
open Monad_util
open Glob_term
open Ltac_plugin

module ArgumentsDef = struct
  module M = ReaderStateWriterMonad
      (struct type r = Id.Set.t end)
      (struct type s = Evd.evar_map end)
      (struct
        type w = Constr.t option list * Id.Set.t
        let id = [], Id.Set.empty
        let comb (ts1, ids1) (ts2,ids2) = List.append ts1 ts2, Id.Set.union ids1 ids2 end)
  include MapDefTemplate (M)
  let with_binders ids a cont = map (fun x -> (fun x -> x), x) @@ M.local
      (fun ids' -> Id.Set.union (Id.Set.of_list ids) ids') @@ cont a
end
module ArgumentsMapper = MakeMapper(ArgumentsDef)
open ArgumentsDef

let add_var env id =
  M.(ask >>= fun ids ->
     (if Id.Set.mem id ids || not @@ List.exists
           (fun pt -> Id.equal (Context.Named.Declaration.get_id pt) id) @@ Environ.named_context env then
        tell ([None], Id.Set.singleton id)
      else
        tell ([Some (Constr.mkVar id)], Id.Set.singleton id)) >> return id)

let add_constr tac env c =
  let* bound = M.ask in
  let* evd = M.get in
  let* c, (_, ids_used) = M.listen @@ M.censor (fun (_, ids) -> [], ids) c in
  (if not @@ Id.Set.disjoint bound ids_used then (
     Feedback.msg_notice Pp.(str "Tactic argument not interpreted due to a bound variable: Tactic: " ++
                             Pptactic.pr_glob_tactic env tac ++ str " Arg: " ++
                             Printer.pr_glob_constr_env env (fst c));
     M.tell ([None], Id.Set.empty))
   else
     try
       let evd, typed = Pretyping.understand_ltac (Pretyping.no_classes_no_fail_inference_flags) env evd
           Discharge_tacexpr.empty_ltac_context
           Pretyping.WithoutTypeConstraint (fst c) in
       let typed = EConstr.to_constr ~abort_on_undefined_evars:false evd typed in
       M.put evd >>
       M.tell ([Some typed], Id.Set.empty)
     with
     | CErrors.Timeout as e -> raise e
     | e ->
       Feedback.msg_notice Pp.(str "Tactic argument interning error: Tactic: " ++
                               Pptactic.pr_glob_tactic env tac ++ str " Arg: " ++
                               Printer.pr_glob_constr_env env (fst c) ++ str " Error: " ++
                               CErrors.print e);
       M.tell ([None], Id.Set.empty)) >> return c

let mapper tac env =
  { ArgumentsDef.default_mapper with
    variable = (fun id -> add_var env id)
  ; constant = (fun c ->
        M.(tell ([Some (Constr.mkConst c)], Id.Set.empty) >> return c))
  ; glob_constr_and_expr = (fun c cont -> add_constr tac env @@ cont c)
  ; glob_constr = (fun c cont ->
      (* We assume that any glob_constr is also processed by glob_constr_and_expr.
         Counter-examples welcome. *)
    cont c)
  ; constr_expr = (fun c cont ->
      (* The assumption is that our tactic is strict, so we are not interested in this *)
      return c)
  ; constr_pattern = (fun c cont ->
      (* Too difficult to deal with *)
      return c)
  }

let tactic_arguments env evd t =
  let evd, ((arguments, _), _) = M.run (ArgumentsMapper.glob_tactic_expr_map (mapper t env) t) Id.Set.empty evd in
  evd, arguments

let marker = Names.Id.of_string_soft "__argument_marker__"
let placeholder () = match Coqlib.lib_ref "tactician.private_constant_placeholder" with
  | Names.GlobRef.ConstRef const -> const
  | _ -> assert false

module SubstituteDef = struct
  module M = ReaderStateMonadT(MaybeMonad)
      (struct type r = Id.Set.t end)
      (struct type s = Constr.t list end)
  include MapDefTemplate (M)
  let with_binders ids' a cont =
    map (fun x -> (fun x -> x), x) @@
    M.local (fun ids -> List.fold_left (fun ids id -> Id.Set.add id ids) ids ids') @@ cont a
end
module SubstituteMapper = MakeMapper(SubstituteDef)
open SubstituteDef
open ReaderMonad(struct type r = Id.t list end)

type 'a k = (Id.t list -> 'a)

let fail = M.lift MaybeMonad.empty

let retrieve_variable =
  let open M in
  let open WithMonadNotations(M) in
  let* vars = get in
  match vars with
  | [] -> fail
  | x::vars ->
    put vars >> return x

let mapper env evd =
  let open WithMonadNotations(M) in
  { SubstituteDef.default_mapper with
    variable = (fun id ->
        if not (Id.equal id marker) then return id else
          let* c = retrieve_variable in
          if Constr.isVar c then return (Constr.destVar c) else fail)
  ; constant = (fun c ->
        if not (Constant.equal c (placeholder ())) then return c else
          let* c = retrieve_variable in
          if Constr.isConst c then return (fst @@ Constr.destConst c) else fail
      )
  ; glob_constr_and_expr = (fun c cont ->
      match DAst.get (fst c) with
      | GHole (Evar_kinds.NamedHole id, _, _) when Id.equal id marker ->
        let* bound = M.ask in
        let* c = retrieve_variable in
        let c = Discharge_tacexpr.detype env evd bound (EConstr.of_constr c) in
        return (c, None)
      | _ -> return c)
  ; glob_constr_pattern_and_expr = (fun c cont ->
      let+ (_, (c, _), _) = cont c in
      let _, pat = Patternops.pattern_of_glob_constr c in
      let bound = Glob_ops.bound_glob_vars c in
      bound, (c, None), pat)
  }

let tactic_substitute env evd ls t =
  Option.cata (fun (rem, t) -> if rem = [] then Some t else None) None @@
  MaybeMonad.run @@ M.run (SubstituteMapper.glob_tactic_expr_map (mapper env evd) t) Id.Set.empty ls

open Mapping_helpers
module StripDef = struct
  include MapDefTemplate(IdentityMonad)
end
module StripMapper = MakeMapper(StripDef)
open StripDef
open Helpers(StripDef)

let mapper = { StripDef.default_mapper with
               glob_constr_and_expr = (fun (expr, _) g -> g (expr, None))
             ; glob_constr_pattern_and_expr = (fun (_, expr, pat) g -> g (Names.Id.Set.empty, expr, pat))
             ; variable = (fun id -> return marker)
             ; constant = (fun c -> return (placeholder ()))
             ; constr_pattern = (fun _ _ -> return @@ Pattern.PMeta None)
             ; constr_expr = (fun c _ -> return c)
             ; glob_constr = (fun _ _ ->
                 return @@ Glob_term.GHole (Evar_kinds.NamedHole marker, IntroAnonymous, None))
             }

let tactic_strip t = StripMapper.glob_tactic_expr_map mapper t
