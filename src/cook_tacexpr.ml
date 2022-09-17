open Ltac_plugin
open Tacexpr
open Monad_util
open Locus
open Names
open Map_all_the_things

module CookTacticDef = struct
  module M = WriterMonad
      (struct type w = KNset.t let id = KNset.empty let comb = KNset.union end)
  include MapDefTemplate (M)
end
module CookTacticMapper = MakeMapper(CookTacticDef)
open CookTacticDef

let correct_kername id =
  try
    let _ = Tacenv.interp_ltac id in return (ArgArg (None, id))
  with Not_found ->
    let kername_tolname id = CAst.make (Label.to_id (KerName.label id)) in
    let+ () = M.tell (KNset.singleton id) in
    ArgVar (kername_tolname id)

let mapper = { CookTacticDef.default_mapper with
                 glob_tactic_arg = (fun a c ->
                   let* a =  c a in
                   match a with
                   | Reference (ArgArg (_, id)) ->
                     let* id = correct_kername id in
                     return (Reference id)
                   | TacCall CAst.{v=(id, args); _} ->
                     let* id = match id with
                       | Locus.ArgArg (_, id) -> correct_kername id
                       | Locus.ArgVar _ -> return id in
                     return (TacCall (CAst.make (id, args)))
                   | _ -> return a)
               ; glob_tactic = (fun t c ->
                     let* t = c t in
                     match t with
                     | TacAlias (id, args) ->
                       if Tacenv.check_alias id then return t else
                         let lid = CAst.make (Label.to_id (KerName.label id)) in
                         let+ () = M.tell (KNset.singleton id) in
                         TacArg (TacCall (CAst.make (ArgVar lid, args)))
                     | _ -> return t) }
let rebuild t =
  M.run @@ CookTacticMapper.glob_tactic_expr_map mapper t
