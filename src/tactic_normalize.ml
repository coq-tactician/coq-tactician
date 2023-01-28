open Ltac_plugin
open Monad_util
open Map_all_the_things
open Mapping_helpers
open Names
open Locus
open Tacexpr

(* TODO: Proper hashconsing *)

module NormalizeDef = struct
  include MapDefTemplate (IdentityMonad)
end
module NormalizeMapper = MakeMapper(NormalizeDef)
open NormalizeDef
open Helpers(NormalizeDef)

type 'a k = 'a NormalizeDef.t

module KerNameHash = Hashset.Make (struct
    type t = KerName.t
    let eq = KerName.equal
  end)
let t : KerNameHash.t = KerNameHash.create 99

let lookup id = KerNameHash.repr (KerName.hash id) id t

(* TODO: This hashing seems entirely wrong *)
let mapper = { NormalizeDef.default_mapper with
               cast = (fun (CAst.{v; _}) -> CAst.make ?loc:None v)
             ; located = (fun (_, x) -> None, x)
             ; constant = (fun x -> ignore(Constant.hash x); return x)
             ; mutind = (fun x -> ignore(MutInd.hash x); return x)
             ; glob_tactic_arg = (fun t g -> match g t with
                 | Reference (ArgArg (_, n)) ->
                   Reference (ArgArg (None, lookup n))
                 | TacCall CAst.{v=(ArgArg (_, n), ls); _} ->
                   TacCall (CAst.make (ArgArg (None, lookup n), ls))
                 | x -> x)
             ; glob_tactic = (fun t g -> kername_map lookup (g t))
             ; raw_tactic = (fun t g -> kername_map lookup (g t))
             ; short_name = (fun _ -> None) }

let tactic_normalize = NormalizeMapper.glob_tactic_expr_map mapper

let mapper = { NormalizeDef.default_mapper with
               glob_constr_and_expr = (fun (expr, _) g -> g (expr, None))
             ; glob_constr_pattern_and_expr = (fun c cont ->
                   let (bound, (c, _), pat) = cont c in
                   match pat with
                   | PRel 0 ->
                     (* This is a dummy inserted for non-strict tactics. Therefore, we have to convert it. *)
                     let _, pat =
                       Tactician_util.with_flag "-cast-in-pattern"
                         (fun () -> Patternops.pattern_of_glob_constr c) in
                     let bound = Glob_ops.bound_glob_vars c in
                     bound, (c, None), pat
                   | _ -> bound, (c, None), pat
                 )
             }

let tactic_strict = NormalizeMapper.glob_tactic_expr_map mapper
