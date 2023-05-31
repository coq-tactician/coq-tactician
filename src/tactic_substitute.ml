open Map_all_the_things
open Names
open Monad_util

module FreeVarsDef = struct
  module M = WriterMonad
      (struct type w = Id.t list let id = [] let comb = List.append end)
  include MapDefTemplate (M)
  let with_binders ids = M.censor (fun w -> List.filter (fun id -> not @@ List.exists (Id.equal id) ids) w)
end
module FreeVarsMapper = MakeMapper(FreeVarsDef)
open FreeVarsDef
open WriterMonad(struct type w = Id.t list let id = [] let comb = List.append end)

type 'a w = Id.t list * 'a

let mapper = { FreeVarsDef.default_mapper with
               variable = (fun id -> M.(tell [id] >> return id))
             }

let tactic_free_variables t : Id.t list =
  let vars, _ = M.run @@ FreeVarsMapper.glob_tactic_expr_map mapper t in vars

module SubstituteDef = struct
  module M = ReaderMonad(struct type r = Id.t list end)
  include MapDefTemplate (M)
  let with_binders ids = M.local (fun ids' -> (ids@ids'))
end
module SubstituteMapper = MakeMapper(SubstituteDef)
open SubstituteDef
open ReaderMonad(struct type r = Id.t list end)

type 'a k = (Id.t list -> 'a)

let mapper f = { SubstituteDef.default_mapper with
                 variable = (fun id -> M.(ask >>= fun ids ->
                            if List.exists (Id.equal id) ids then return id else return (f id)))
               }

let tactic_substitute f t = M.run (SubstituteMapper.glob_tactic_expr_map (mapper f) t) []
