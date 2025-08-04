open Map_all_the_things
open Names
open Monad_util

module FreeVarsDef = struct
  module M = WriterMonad
      (struct type w = Id.Set.t let id = Id.Set.empty let comb = Id.Set.union end)
  include MapDefTemplate (M)
  let with_binders ids a cont = map (fun x -> (fun x -> x), x) @@
    M.censor (fun w -> Id.Set.filter (fun id -> not @@ List.exists (Id.equal id) ids) w) @@ cont a
end
module FreeVarsMapper = MakeMapper(FreeVarsDef)
open FreeVarsDef

let mapper = { FreeVarsDef.default_mapper with
               variable = (fun id -> M.(tell (Id.Set.singleton id) >> return id))
             }

let tactic_free_variables t : Id.Set.t =
  let vars, _ = M.run @@ FreeVarsMapper.glob_tactic_expr_map mapper t in vars
let glob_constr_free_variables t : Id.Set.t =
  let vars, _ = M.run @@ FreeVarsMapper.glob_constr_map mapper t in vars

module SubstituteDef = struct
  module M = ReaderMonad(struct type r = Id.Set.t end)
  include MapDefTemplate (M)
  let with_binders ids a cont = M.map (fun x -> (fun x -> x), x) @@
    M.local (fun ids' -> Id.Set.union (Id.Set.of_list ids) ids') @@ cont a
end
module SubstituteMapper = MakeMapper(SubstituteDef)
open SubstituteDef

let mapper f = { SubstituteDef.default_mapper with
                 variable = (fun id -> M.(ask >>= fun ids ->
                            if Id.Set.mem id ids then return id else return (f id)))
               }

(* Converts a _free_variables.
   Assumes that the target variables are fresh. If the expression contains a binder with the same name,
   the variables might get captured. *)
let alpha_convert f t = M.run (SubstituteMapper.glob_tactic_expr_map (mapper f) t) Id.Set.empty
