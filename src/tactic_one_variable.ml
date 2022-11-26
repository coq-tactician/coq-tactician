open Map_all_the_things
open Names
open Monad_util
open Glob_term

type var_type =
  | TVar of Id.t
  | TRef of GlobRef.t
  | TOther

module OneVariableDef = struct
  module M = ReaderWriterMonad
      (struct
        (* Bool indicates whether or not the variables are exact.
           Note that this assumes that the tactic is strict. For non-strict tactics, all bets are off. *)
        type w = var_type list * bool
        let id = [], true
        let comb (ls1, b1) (ls2, b2) = List.append ls1 ls2, b1 && b2 end)
      (struct type r = Id.t list end)
  include MapDefTemplate (M)
  let with_binders ids = M.local (fun ids' -> (ids@ids'))
end
module OneVariableMapper = MakeMapper(OneVariableDef)
open OneVariableDef

let find_variable ls =
  match ls with
  | [x] -> x, true
  | _ ->
    let cs = List.filter (function
        | TRef (GlobRef.VarRef _) | TVar _ | TOther -> false
        | TRef _ -> true) ls in
    let ss = List.filter (function
        | TRef (GlobRef.VarRef _) -> true
        | TRef _ | TVar _ | TOther -> false) ls in
    let vs = List.filter (function
        | TVar _ -> true
        | TRef _ | TOther -> false
        ) ls in
    (if not (cs = []) then List.hd cs else
     if not (ss = []) then List.hd ss else
     if not (vs = []) then List.hd vs else
      TOther), false

let curtail c =
    M.censor (fun (ls, exact) -> let x, exact' = find_variable ls in [x], exact && exact') @@ c

let mapper = { OneVariableDef.default_mapper with
               variable = (fun id ->
                   M.(ask >>= fun ids ->
                      if List.exists (Id.equal id) ids then
                        tell ([TOther], false) >> return (Id.of_string_soft "_")
                      else
                        tell ([TVar id], true) >> return id))
             ; constant = (fun c ->
                   M.(tell ([TRef (GlobRef.ConstRef c)], true) >> return c))
             ; glob_constr_and_expr = (fun c cont ->
                   M.censor (function
                       | [], _ -> [TOther], false
                       | x -> x) @@
                   let+ c, _ = cont c in
                   c, None
                 )
             ; glob_constr = (fun c cont ->
                 curtail @@
                 match c with
                 | GRef (id, _) ->
                   M.(tell ([TRef id], true)) >> return c
                 | GVar id ->
                   M.(ask >>= fun ids ->
                      if List.exists (Id.equal id) ids then
                        tell ([TOther], false) >> return (GHole (Evar_kinds.GoalEvar, IntroAnonymous, None))
                      else
                        tell ([TVar id], true) >> return c)
                 | _ ->
                   M.tell ([], false) >> (* Here, we are always inexact *)
                   let+ c, (w, _) = M.listen (cont c) in
                   let v, _ = find_variable w in
                   match v with
                   | TRef c -> GRef (c, None)
                   | TVar id -> GVar id
                   | TOther -> GHole (Evar_kinds.GoalEvar, IntroAnonymous, None)
               )
             ; constr_expr = (fun c cont ->
                 (* The assumption is that our tactic is strict, so we are not interested in this *)
                 return c)
             ; constr_pattern = (fun c cont ->
                 (* Patterns will be reconstructed below, so we are not interested in this *)
                 return c)
             ; glob_constr_pattern_and_expr = (fun c cont ->
                 let+ (_, (c, _), _) = cont c in
                 let _, pat =
                   Tactician_util.with_flag "-cast-in-pattern"
                     (fun () -> Patternops.pattern_of_glob_constr c) in
                 let bound = Glob_ops.bound_glob_vars c in
                 bound, (c, None), pat)
             }

let tactic_one_variable t =
  M.run (OneVariableMapper.glob_tactic_expr_map mapper t) []

let marker = Names.Id.of_string_soft "__argument_marker__"
let placeholder () = match Coqlib.lib_ref "tactician.private_constant_placeholder" with
  | Names.GlobRef.ConstRef const -> const
  | _ -> assert false

module SubstituteDef = struct
  module M = StateMonadT(MaybeMonad)
      (struct type s = var_type list end)
  include MapDefTemplate (M)
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

let mapper =
  let open WithMonadNotations(M) in
  { SubstituteDef.default_mapper with
    variable = (fun id ->
        if not (Id.equal id marker) then return id else
          let* var = retrieve_variable in
          match var with
          | TRef (GlobRef.VarRef id) -> return id
          | TVar id -> return id
          | TOther -> return (Id.of_string_soft "_")
          | _ -> fail)
  ; constant = (fun c ->
        if not (Constant.equal c (placeholder ())) then return c else
          let* var = retrieve_variable in
          match var with
          | TRef (GlobRef.ConstRef c) -> return c
          | _ -> fail
      )
  ; glob_constr_and_expr = (fun c cont ->
      match DAst.get (fst c) with
      | GHole (Evar_kinds.NamedHole id, _, _) when Id.equal id marker ->
        (let* var = retrieve_variable in
         match var with
         | TRef c -> return (DAst.make (GRef (c, None)), None)
         | TVar id -> return (DAst.make (GVar id), None)
         | TOther -> return (DAst.make (GHole (Evar_kinds.GoalEvar, IntroAnonymous, None)), None))
      | _ -> return c)
  ; glob_constr_pattern_and_expr = (fun c cont ->
      let+ (_, (c, _), _) = cont c in
      let _, pat = Patternops.pattern_of_glob_constr c in
      let bound = Glob_ops.bound_glob_vars c in
      bound, (c, None), pat)
  }

let tactic_substitute ls t =
  Option.cata (fun (rem, t) -> if rem = [] then Some t else None) None @@
  MaybeMonad.run @@ M.run (SubstituteMapper.glob_tactic_expr_map mapper t) ls

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
