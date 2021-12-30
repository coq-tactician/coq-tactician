open Map_all_the_things
open Genarg
open Names
open Tactician_util
open Glob_term

module FreeVarsDef = struct
  module M = ReaderWriterMonad
      (struct type r = Id.t list type w = Id.t option list let id = [] let comb = List.append end)
  include MapDefTemplate (M)
  let map_sort = "one_free_variable"
  let warnProblem wit =
    Feedback.msg_warning (Pp.(str "Tactician is having problems with " ++
                              str "the following tactic. Please report. " ++
                              pr_argument_type wit))
  let default wit = { raw = (fun _ -> warnProblem (ArgumentType wit); id)
                    ; glb = (fun _ -> warnProblem (ArgumentType wit); id)}

  let with_binders ids = M.local (fun ids' -> (ids@ids'))
end
module FreeVarsMapper = MakeMapper(FreeVarsDef)
open FreeVarsDef

let curtail c =
    M.censor (function
        | [] -> []
        | x::_ -> [x]
      ) @@ c

let mapper = { FreeVarsDef.default_mapper with
               variable = (fun id ->
                   M.(ask >>= fun ids ->
                      (if List.exists (Id.equal id) ids then return () else tell [Some id]) >> return id))
             ; glob_constr_and_expr = (fun c cont ->
                   M.censor (function
                       | [] -> [None]
                       | x -> x) @@
                   let+ c, _ = cont c in
                   c, None
                 )
             ; glob_constr = (fun c cont ->
                 curtail @@ let+ c, w = M.listen @@ cont c in
                 match w with
                 | Some id::_ -> GVar id
                 | _ -> GHole (Evar_kinds.GoalEvar, IntroAnonymous, None)
               )
             ; constr_expr = (fun c cont -> M.censor (fun _ -> []) @@ cont c)
             }

let tactic_one_variable t =
  M.run [] @@ FreeVarsMapper.glob_tactic_expr_map mapper t
