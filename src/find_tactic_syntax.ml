open Ltac_plugin
open Monad_util
open Map_all_the_things
open Tacexpr
open Names

module TacticFinderDef = struct
  module M = WriterMonad
      (struct type w = bool let id = false let comb = Bool.(||) end)
  include MapDefTemplate (M)
end
module TacticFinderMapper = MakeMapper(TacticFinderDef)
open TacticFinderDef

let contains_ml_tactic ml t =
  let seen = ref KNset.empty in
  let rec contains_ml_tactic_ltac k =
    if KNset.mem k !seen then
      return ()
    else
      let tac = Tacenv.interp_ltac k in
      seen := KNset.add k !seen;
      map (fun _ -> ()) @@ TacticFinderMapper.glob_tactic_expr_map mapper tac
  and contains_ml_tactic_alias k =
    if KNset.mem k !seen then
      return ()
    else
      let tac = Tacenv.interp_alias k in
      seen := KNset.add k !seen;
      map (fun _ -> ()) @@ TacticFinderMapper.glob_tactic_expr_map mapper tac.alias_body
  and mapper = { TacticFinderDef.default_mapper with
                 glob_tactic_arg = (fun a c -> (match a with
                     | TacCall CAst.{ v=(ArgArg (_, k), _args); _} ->
                       let* _ = contains_ml_tactic_ltac k in
                       c a
                     | _ -> c a))
               ; glob_tactic = (fun t c -> (match t with
                     | TacML CAst.{ v=(e, _args); _} ->
                       let* () = if ml = e then M.tell true else return () in
                       c t
                     | TacAlias CAst.{ v=(k, _args); _} ->
                       let* () = contains_ml_tactic_alias k in
                       c t
                     | _ -> c t)) } in
  fst @@ M.run @@ TacticFinderMapper.glob_tactic_expr_map mapper t
