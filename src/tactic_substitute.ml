open Map_all_the_things
open Genarg
open Names

module ReaderMonad (R : sig type r end) = struct
  open R
  type 'a t = r -> 'a
  let return x = fun _ -> x
  let (>>=) x f = fun r -> f (x r) r
  let (>>) x y = fun r -> let () = x r in y r
  let map f x = fun r -> f (x r)

  let ask x = x
  let local f x = fun r -> x (f r)
end

module WriterMonad (R : sig type w val id : w val comb : w -> w -> w end) = struct
  open R
  type 'a t = w * 'a
  let return x = (id, x)
  let (>>=) (w, x) f = let (w', y) = f x in (comb w w', y)
  let (>>) (w, ()) (w', x) = (comb w w', x)
  let map f (w, x) = w, f x

  let tell l = ([l], ())
  let censor f (w, x) = (f w, x)
end

module FreeVarsDef = struct
  include MapDefTemplate (WriterMonad
                            (struct type w = Id.t list let id = [] let comb = List.append end))
  let map_sort = "freevars"
  let warnProblem wit =
    Feedback.msg_warning (Pp.(str "Tactician is having problems with " ++
                              str "the following tactic. Please report. " ++
                              pr_argument_type wit))
  let default wit = { raw = (fun _ -> warnProblem (ArgumentType wit); id)
                    ; glb = (fun _ -> warnProblem (ArgumentType wit); id)}
end
module FreeVarsMapper = MakeMapper(FreeVarsDef)
open FreeVarsDef
open WriterMonad(struct type w = Id.t list let id = [] let comb = List.append end)

type 'a w = Id.t list * 'a

let mapper = { FreeVarsDef.default_mapper with
               variable = (fun id -> tell id >> return id)
             }

let tactic_free_variables t : Id.t list =
  let vars, _ = FreeVarsMapper.glob_tactic_expr_map mapper t in vars

(* module SubstituteDef = struct
 *   include MapDefTemplate (ReaderMonad(struct type r = Id.t list end))
 *   let map_sort = "substitute"
 *   let warnProblem wit =
 *     Feedback.msg_warning (Pp.(str "Tactician is having problems with " ++
 *                               str "the following tactic. Please report. " ++
 *                               pr_argument_type wit))
 *   let default wit = { raw = (fun _ -> warnProblem (ArgumentType wit); id)
 *                     ; glb = (fun _ -> warnProblem (ArgumentType wit); id)}
 * end
 * module SubstituteMapper = MakeMapper(SubstituteDef)
 * open SubstituteDef
 * open ReaderMonad(struct type r = Id.t list end)
 * 
 * type 'a k = (Id.t list -> 'a) *)

(* let glob_constr_map : ([ `any ] glob_constr_r) map = fun x ids ->
 *   match x with
 *   | GVar id -> ask >>= fun (x : Id.t list) -> Feedback.msg_warning Pp.(str "for " ++ Id.print id); List.iter (fun id -> Feedback.msg_warning (Id.print id)) x; return x
 *   | GLambda (_, _, _, _) -> (??)
 *   | GProd (_, _, _, _) -> (??)
 *   | GLetIn (_, _, _, _) -> (??)
 *   | GCases (_, _, _, _) -> (??)
 *   | GLetTuple (_, _, _, _) -> (??)
 *   | GIf (_, _, _, _) -> (??)
 *   | GRec (_, _, _, _, _) -> (??)
 *   | GSort _ -> (??)
 *   | GHole (_, _, _) -> (??)
 *   | GCast (_, _) -> (??)
 *   | GInt _ -> (??)
 *   | GFloat _ -> (??)
 * 
 * let mapper = { NormalizeDef.default_mapper with
 *                cast = (fun (CAst.{v; _}) -> CAst.make ?loc:None v)
 *              ; located = (fun _ -> None)
 *              ; constant = (fun x -> ignore(Constant.hash x); return x)
 *              ; mutind = (fun x -> ignore(MutInd.hash x); return x)
 *              ; glob_tactic_arg = (fun x -> match x with
 *                  | Reference (ArgArg (_, n)) ->
 *                    Reference (ArgArg (None, lookup n))
 *                  | TacCall CAst.{v=(ArgArg (_, n), ls); _} ->
 *                    TacCall (CAst.make (ArgArg (None, lookup n), ls))
 *                  | x -> x)
 *              ; glob_tactic = kername_map lookup
 *              ; raw_tactic = kername_map lookup
 *              ; short_name = (fun _ -> None) }
 * 
 * let tactic_normalize = NormalizeMapper.glob_tactic_expr_map mapper *)
