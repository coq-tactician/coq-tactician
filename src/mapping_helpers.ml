open Ltac_plugin
open Map_all_the_things
open Tacexpr

module Helpers (M : MapDef) = struct
  open M

  let cast_map f CAst.{loc; v} =
    let+ v = f v in CAst.make ?loc v

  (* Maps only bare kernames, not GlobRef.t, Constant.t or MutInd.t *)
  let kername_map f = function
    | TacAlias (name, args) ->
      let+ name = f name in
      TacAlias (name, args)
    | x -> return x
end
