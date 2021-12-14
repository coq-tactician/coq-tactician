open Map_all_the_things
open Genarg
open Names
open Tactician_util
open Glob_term
open Constrexpr
open Ltac_plugin
open Tacexpr

module SubstituteDef = struct
  include MapDefTemplate (ReaderMonad(struct type r = Id.t list end))
  let map_sort = "substitute2"
  let warnProblem wit =
    Feedback.msg_warning (Pp.(str "Tactician is having problems with " ++
                              str "the following tactic. Please report. " ++
                              pr_argument_type wit))
  let default wit = { raw = (fun _ -> warnProblem (ArgumentType wit); id)
                    ; glb = (fun _ -> warnProblem (ArgumentType wit); id)}

  let with_binders ids f = fun ids' -> f (ids@ids')
end
module SubstituteMapper = MakeMapper(SubstituteDef)
open SubstituteDef
open ReaderMonad(struct type r = Id.t list end)

type 'a k = (Id.t list -> 'a)

let mapper env evd f =
  { SubstituteDef.default_mapper with
    variable = (fun id ->
        ask >>= fun bound ->
        return @@ match List.exists (Id.equal id) bound with
        | true -> id
        | false ->
          match f id with
          | None -> id
          | Some c ->
            match EConstr.isVar evd c with
            | true -> EConstr.destVar evd c
            | false ->
              (* Unsolvable case *)
              Names.Id.of_string "__tactician_unsolvable__"
      )
  ; glob_constr = (fun c cont ->
        ask >>= fun bound ->
        match c with
        | GVar id when not @@ List.exists (Id.equal id) bound ->
          (match f id with
           | None -> return c
           | Some c ->
             let c = Detyping.detype Detyping.Now true (Id.Set.of_list bound) env evd c in
             return @@ DAst.get c
          )
        | _ -> cont c
      )
  ; constr_expr = (fun c cont ->
      match c with
      | CRef (id, _) when Libnames.qualid_is_ident id ->
        let _, id = Libnames.repr_qualid id in
        ask >>= fun bound ->
        (match List.exists (Id.equal id) bound with
         | true -> return c
         | false ->
           (match f id with
            | None -> return c
            | Some c ->
              let c = Detyping.detype Detyping.Now true (Id.Set.of_list bound) env evd c in
              let c = Constrextern.extern_glob_constr (Id.Set.of_list bound) c in
              return @@ CAst.(c.v)))
      | _ ->
        cont c
    )
  ; glob_atomic_tactic = (fun t cont ->
      ask >>= fun bound ->
      let t = match t with
        (* Special case for destruct H, where H is a variable *)
      | TacInductionDestruct (rflg, eflg, (cls, using)) ->
        let cls = List.map (fun ((cflg, trm), x, y) ->
            let trm = match trm with
              | Tactics.ElimOnIdent id when not @@ List.exists (Id.equal id.v) bound ->
                (match f id.v with
                 | None -> trm
                 | Some c ->
                   let c = Detyping.detype Detyping.Now true (Id.Set.of_list bound) env evd c in
                   let c = (c, None), Tactypes.NoBindings in
                   Tactics.ElimOnConstr c)
              | _ -> trm
            in
            (cflg, trm), x, y) cls in
        TacInductionDestruct (rflg, eflg, (cls, using))
      | _ -> t in
      cont t
    )
  }

let tactic_substitute env evd f t = SubstituteMapper.glob_tactic_expr_map (mapper env evd f) t []
