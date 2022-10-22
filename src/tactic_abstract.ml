open Map_all_the_things
open Names
open Monad_util

module M = ReaderStateMonad
  (struct type r = Id.t list end) (struct type s = (Id.t * Id.t) list end)
module AbstractDef = struct
  include MapDefTemplate(M)
  open M
  let with_binders ids x = local (fun ids' -> (ids@ids')) x
end
module AbstractMapper = MakeMapper(AbstractDef)
open AbstractDef
open M

type 'a k = (Id.t list -> Id.t list * 'a)

let mapper = { AbstractDef.default_mapper with
               variable = (fun id -> ask >>= fun ids -> get >>= fun args ->
                           if List.exists (Id.equal id) ids then return id else
                             let n = List.length args in
                             let id' = Id.of_string ("t" ^ string_of_int n) in
                             put ((id, id')::args) >> return id')
             }

let tactic_abstract t =
  let args, t = M.run (AbstractMapper.glob_tactic_expr_map mapper t) [] [] in
  List.rev args, t

module M2 = WriterMonad
  (struct type w = Constant.t list let comb = List.append let id = [] end)
module ConstantsDef = struct
  include MapDefTemplate(M2)
  let with_binders _ids x = x
end
module ConstantsMapper = MakeMapper(ConstantsDef)
open ConstantsDef
open M2

let mapper = { ConstantsDef.default_mapper with
               constant = (fun c ->
                   let body = (Global.lookup_constant c).const_body in
                   (match body with
                    | Declarations.OpaqueDef _ ->
                      tell [c] >> return c
                    | _ -> return c)
                 )
             }

let tactic_constants t =
  let cs, _ = M2.run @@ ConstantsMapper.glob_tactic_expr_map mapper t in
  List.rev cs
