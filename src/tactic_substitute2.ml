open Map_all_the_things
open Genarg
open Names
open Monad_util
open Glob_term
open Constrexpr
open Ltac_plugin
open Tacexpr

module SubstituteDef = struct
  module M = ReaderMonad(struct type r = Id.Set.t end)
  include MapDefTemplate (M)
  let map_sort = "substitute2"
  let warnProblem wit =
    Feedback.msg_warning (Pp.(str "Tactician is having problems with " ++
                              str "the following tactic. Please report. " ++
                              pr_argument_type wit))
  let default wit = { raw = (fun _ -> warnProblem (ArgumentType wit); id)
                    ; glb = (fun _ -> warnProblem (ArgumentType wit); id)}

  let with_binders ids x f = M.map (fun x -> (fun x -> x), x) @@
    M.local (fun ids' -> Id.Set.union (Id.Set.of_list ids) ids') (f x)
end
module SubstituteMapper = MakeMapper(SubstituteDef)
open SubstituteDef

let mapper env evd f =
  let open M in
  { SubstituteDef.default_mapper with
    variable = (fun id ->
        ask >>= fun bound ->
        return @@ match Id.Set.mem id bound with
        | true -> id
        | false ->
          match f id with
          | None -> id
          | Some c ->
            match EConstr.isVar evd c with
            | true -> EConstr.destVar evd c
            | false ->
              (* Unsolvable case *)
              Id.of_string "__tactician_unsolvable__"
      )
  ; glob_constr = (fun c cont ->
        ask >>= fun bound ->
        match c with
        | GVar id when not @@ Id.Set.mem id bound ->
          (match f id with
           | None -> return c
           | Some c ->
             let c = Detyping.detype Detyping.Now true Id.Set.empty env evd c in
             return @@ DAst.get c
          )
        | _ -> cont c
      )
  ; constr_expr = (fun c cont ->
      match c with
      | CRef (id, _) when Libnames.qualid_is_ident id ->
        let _, id = Libnames.repr_qualid id in
        ask >>= fun bound ->
        (match Id.Set.mem id bound with
         | true -> return c
         | false ->
           (match f id with
            | None -> return c
            | Some c ->
              let c = Detyping.detype Detyping.Now true Id.Set.empty env evd c in
              let c = Constrextern.extern_glob_constr Id.Set.empty c in
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
              | Tactics.ElimOnIdent id when not @@ Id.Set.mem id.v bound ->
                (match f id.v with
                 | None -> trm
                 | Some c ->
                   let c = Detyping.detype Detyping.Now true Id.Set.empty env evd c in
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

let non_avoiding_substitute env evd f t =
  M.run (SubstituteMapper.glob_tactic_expr_map (mapper env evd f) t) Id.Set.empty

module CaptureAvoidDef = struct
  type r =
    | Conv of Id.Set.t
    | Rename of (Id.t -> Id.t)
  type w =
    { convert : Id.Set.t
    ; avoid   : Id.Set.t }
  module M = ReaderWriterMonad
      (struct
        type nonrec w = w
        let id = { convert = Id.Set.empty; avoid = Id.Set.empty }
        let comb a b = { convert = Id.Set.union a.convert b.convert; avoid = Id.Set.union a.avoid b.avoid }
      end)
      (struct type nonrec r = r end)
  include MapDefTemplate (M)
  let map_sort = "captureavoid"
  let warnProblem wit =
    Feedback.msg_warning (Pp.(str "Tactician is having problems with " ++
                              str "the following tactic. Please report. " ++
                              pr_argument_type wit))
  let default wit = { raw = (fun _ -> warnProblem (ArgumentType wit); id)
                    ; glb = (fun _ -> warnProblem (ArgumentType wit); id)}

  let with_binders ids a cont =
    M.ask >>= function
    | Conv bndrs ->
      M.listen (M.local (fun _ -> Conv (Id.Set.union (Id.Set.of_list ids) bndrs)) @@ cont a)
      >>= fun (a, { convert; avoid }) ->
      if List.for_all (fun id -> not @@ Id.Set.mem id convert) ids then return ((fun x -> x), a) else
        let rename id =
          if Id.Set.mem id convert && List.exists (Id.equal id) ids then
            Namegen.next_ident_away_from id
              (fun id' -> Id.Set.mem id' convert || Id.Set.mem id' avoid || List.exists (Id.equal id') ids)
          else id in
        M.map (fun a -> rename, a) @@ M.local (fun _ -> Rename rename) @@ cont a
    | Rename f ->
      M.map (fun a -> (fun x -> x), a) @@
      M.local (fun _ -> Rename (fun id -> if List.exists (Id.equal id) ids then id else f id)) @@ cont a
end
module CaptureAvoidMapper = MakeMapper(CaptureAvoidDef)
open CaptureAvoidDef

let mapper future_conv =
  { CaptureAvoidDef.default_mapper with
    variable = (fun id -> M.(
        ask >>= function
        | Conv bndrs ->
          (match Id.Set.mem id bndrs, future_conv id with
          | true, _ | false, None ->
            tell { convert = Id.Set.empty; avoid = Id.Set.singleton id }
          | false, Some convert ->
            tell { convert; avoid = Id.Set.empty }) >> return id
        | Rename f ->
          let id = f id in
          tell { convert = Id.Set.empty; avoid = Id.Set.singleton id } >> return id
      ))
  }

let tactic_substitute env evd subst t =
  let future_conv id =
    Option.map (fun c -> Tactic_substitute.glob_constr_free_variables @@
                Detyping.detype Detyping.Now true Id.Set.empty env evd c) @@ subst id in
  let t = snd @@ M.run (CaptureAvoidMapper.glob_tactic_expr_map (mapper future_conv) t) (Conv Id.Set.empty) in
  non_avoiding_substitute env evd subst t
