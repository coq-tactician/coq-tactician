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

let mapper = { NormalizeDef.default_mapper with
               cast = (fun (CAst.{v}) -> CAst.make ?loc:None v)
             ; located = (fun _ -> None)
             ; constant = (fun x -> ignore(Constant.hash x); return x)
             ; mutind = (fun x -> ignore(MutInd.hash x); return x)
             ; glob_tactic_arg = (fun x -> match x with
                 | Reference (ArgArg (_, n)) ->
                   Reference (ArgArg (None, lookup n))
                 | TacCall CAst.{v=(ArgArg (_, n), ls)} ->
                   TacCall (CAst.make (ArgArg (None, lookup n), ls))
                 | x -> x)
             ; glob_tactic = kername_map lookup
             ; raw_tactic = kername_map lookup
             ; short_name = (fun _ -> None) }

let tactic_normalize = NormalizeMapper.glob_tactic_expr_map mapper
