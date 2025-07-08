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

let detype env evd avoid c =
  Flags.with_option Detyping.print_universes
  (Detyping.detype Detyping.Now true avoid env) evd c
let extern_glob_constr avoid c =
  Flags.with_options Constrextern.[ print_implicits; print_coercions; print_universes; print_no_symbol ]
  (Constrextern.extern_glob_constr avoid) c

let unsolvable = "__tactician_unsolvable__"
let mk_unsolvable id =
  Id.of_string (unsolvable ^ Id.to_string id)
let recognize_unsolvable id =
  let id = Id.to_string id in
  if CString.is_prefix unsolvable id then
    let unsolvable_l = CString.length unsolvable in
    Some (Id.of_string @@ CString.sub id unsolvable_l (CString.length id - unsolvable_l))
  else None

let mapper env evd avoid f =
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
              mk_unsolvable id
      )
  ; glob_constr = (fun c cont ->
        ask >>= fun bound ->
        match c with
        | GVar id when not @@ Id.Set.mem id bound ->
          (match f id with
           | None -> return c
           | Some c ->
             let c = detype env evd avoid c in
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
              let c = detype env evd avoid c in
              let c = extern_glob_constr avoid c in
              return @@ CAst.(c.v)))
      | _ ->
        cont c
    )
  ; glob_atomic_tactic = (fun t cont ->
      ask >>= fun bound ->
      cont t >>= fun t ->
      match t with
      (* Special case for destruct H, where H is a variable *)
      | TacInductionDestruct (rflg, eflg, (cls, using)) ->
        let cls = List.map (fun ((cflg, trm), x, y) ->
            let trm = match trm with
              | Tactics.ElimOnIdent id ->
                (match recognize_unsolvable id.v with
                 | Some id when not @@ Id.Set.mem id bound ->
                   (match f id with
                    | None -> trm
                    | Some c ->
                      let c = detype env evd avoid c in
                      let c = (c, None), Tactypes.NoBindings in
                      Tactics.ElimOnConstr c)
                 | _ -> trm
                )
              | _ -> trm
            in
            (cflg, trm), x, y) cls in
        return @@ TacInductionDestruct (rflg, eflg, (cls, using))
      | _ -> return t
    )
  ; glob_tactic_arg = (fun t cont ->
      ask >>= fun bound ->
      cont t >>= fun t ->
      match t with
      (* Special case for references that have become bound *)
      | Reference Locus.ArgVar CAst.{v=id; _} ->
        (match recognize_unsolvable id with
         | Some id when not @@ Id.Set.mem id bound ->
           (match f id with
            | None -> return t
            | Some c ->
              let c = detype env evd avoid c in
              let c = c, None in
              return @@ ConstrMayEval (Genredexpr.ConstrTerm c))
         | _ -> return t)
      | _ -> return t
    )
  }

let non_avoiding_substitute env evd avoid f t =
  M.run (SubstituteMapper.glob_tactic_expr_map (mapper env evd avoid f) t) Id.Set.empty

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

let tactic_substitute env evd avoid subst t =
  let future_conv id =
    Option.map (fun c -> Tactic_substitute.glob_constr_free_variables @@
                detype env evd avoid c) @@ subst id in
  let t = snd @@ M.run (CaptureAvoidMapper.glob_tactic_expr_map (mapper future_conv) t) (Conv Id.Set.empty) in
  non_avoiding_substitute env evd avoid subst t
