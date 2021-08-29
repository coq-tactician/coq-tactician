open Ltac_plugin
open Tactician_util
open Map_all_the_things
open Genarg
open Mapping_helpers
open Names
open Locus
open Tacexpr

(* TODO: Proper hashconsing *)

module NormalizeDef = struct
  include MapDefTemplate (IdentityMonad)
  let map_sort = "normalize"
  let warnProblem wit =
    Feedback.msg_warning (Pp.(str "Tactician is having problems with " ++
                              str "the following tactic. Please report. " ++
                              pr_argument_type wit))
  let default wit = { raw = (fun _ -> warnProblem (ArgumentType wit); id)
                    ; glb = (fun _ -> warnProblem (ArgumentType wit); id)}
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
             ; constant = (fun x -> ignore(Environ.QConstant.hash Environ.empty_env x); return x)
             ; mutind = (fun x -> ignore(Environ.QMutInd.hash Environ.empty_env x); return x)
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
