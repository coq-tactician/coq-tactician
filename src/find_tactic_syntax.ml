open Ltac_plugin
open Monad_util
open Map_all_the_things
open Genarg
open Tacexpr

module TacticFinderDef = struct
  module M = WriterMonad
      (struct type w = bool let id = false let comb = Bool.(||) end)
  include MapDefTemplate (M)
  let map_sort = "tactic-finder"
  let warnProblem wit =
    Feedback.msg_warning (Pp.(str "Tactician is having problems with " ++
                              str "the following tactic. Please report. " ++
                              pr_argument_type wit))
  let default wit = { raw = (fun _ -> warnProblem (ArgumentType wit); id)
                    ; glb = (fun _ -> warnProblem (ArgumentType wit); id)}
end
module TacticFinderMapper = MakeMapper(TacticFinderDef)
open TacticFinderDef

let contains_ml_tactic ml t =
  let rec contains_ml_tactic_ltac k =
    let tac = Tacenv.interp_ltac k in
    TacticFinderMapper.glob_tactic_expr_map mapper tac
  and contains_ml_tactic_alias k =
    let tac = Tacenv.interp_alias k in
    TacticFinderMapper.glob_tactic_expr_map mapper tac.alias_body
  and mapper = { TacticFinderDef.default_mapper with
                 glob_tactic_arg = (fun a c -> (match a with
                     | TacCall CAst.{ v=(ArgArg (_, k), args); _} ->
                       let* _ = contains_ml_tactic_ltac k in
                       c a
                     | _ -> c a))
               ; glob_tactic = (fun t c -> (match t with
                     | TacML CAst.{ v=(e, args); _} ->
                       let* () = if ml = e then M.tell true else return () in
                       c t
                     | TacAlias CAst.{ v=(k, args); _} ->
                       let* _ = contains_ml_tactic_alias k in
                       c t
                     | _ -> c t)) } in
  fst @@ M.run @@ TacticFinderMapper.glob_tactic_expr_map mapper t
