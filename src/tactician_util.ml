let mapi f s : 'a IStream.t =
  let rec mapi_node f i = function
    | IStream.Nil -> IStream.Nil
    | IStream.Cons (x, s) -> Cons (f i x, mapi f (i + 1) s)
  and mapi f i s = IStream.thunk (fun () -> mapi_node f i (IStream.peek s))
  in mapi f 0 s

let rec to_list n s = match n, IStream.peek s with
  | _, Nil | 0, _ -> []
  | n, Cons (x, s) -> x :: (to_list (n - 1) s)

exception PredictionsEnd
exception DepthEnd

let record_map (f : Proofview.Goal.t -> 'a)
    (gls : Proofview.Goal.t Proofview.tactic list) : 'a list Proofview.tactic =
  let rec aux gls acc =
    let open Proofview.Notations in
    match gls with
    | [] -> Proofview.tclUNIT (acc)
    | gl::gls' -> gl >>= fun gl' -> aux gls' (f gl' :: acc) in
  aux gls []

let proof_state_to_string hyps goal env evar_map =
  let constr_str t = Sexpr.format_oneline (Printer.pr_econstr_env env evar_map t) in
  let goal = constr_str goal in
  let hyps = List.map (function
      | Context.Named.Declaration.LocalAssum (id, typ) ->
        let id_str = Names.Id.print id.binder_name in
        let typ_str = constr_str typ in
        Pp.(id_str ++ str " : " ++ typ_str)
      | Context.Named.Declaration.LocalDef (id, term, typ) ->
        let id_str = Names.Id.print id.binder_name in
        let term_str = Pp.(str " := " ++ constr_str term) in
        let typ_str = constr_str typ in
        Pp.(id_str ++ term_str ++ str " : " ++ typ_str)
    ) hyps in
  Pp.(prlist_with_sep (fun () -> str ", ") (fun x -> x) hyps ++ str " |- " ++ goal)

let pr_proof_tac () =
  let open Proofview in
  let open Notations in
  Goal.goals >>= record_map (fun x -> x) >>= fun gls ->
  let gls_string = List.map (fun gl ->
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      let hyps = Goal.hyps gl in
      let goal = Goal.concl gl in
      proof_state_to_string hyps goal env sigma)
      gls in
  List.iter Feedback.msg_notice gls_string; tclUNIT ()

let safe_index0 f x l = try Some (CList.index0 f x l) with Not_found -> None

let constr_size c =
  let rec aux c =
    Constr.fold (fun i c -> i + aux c + 1) 1 c in
  aux c

let econstr_size evd c = constr_size @@ EConstr.to_constr evd c

let goal_size (gl : Proofview.Goal.t) =
  let open Proofview in
  let open Notations in
  let sigma = Proofview.Goal.sigma gl in
  let hyps = Goal.hyps gl in
  let goal = Goal.concl gl in
  let hyps = Context.Named.fold_inside (fun i d ->
      Context.Named.Declaration.fold_constr (fun c i -> i + econstr_size sigma c) d i
    ) ~init:0 hyps in
  let goal = econstr_size sigma goal in
  hyps + goal

(* Find the current file name *)
open Loadpath

let select_v_file ~warn loadpath base =
  let find ext =
    let loadpath = List.map fst loadpath in
    try
      let name = Names.Id.to_string base ^ ext in
      let lpath, file =
        System.where_in_path ~warn loadpath name in
      Some (lpath, file)
    with Not_found -> None in
  match find ".v" with
  | None ->
    Error LibNotFound
  | Some res ->
    Ok res

let load_path_to_physical t =
  let printed = pp t in
  let path = match Pp.repr printed with
  | Pp.Ppcmd_box (_, k) -> (match Pp.repr k with
    | Pp.Ppcmd_glue ks -> (match Pp.repr (List.nth ks 2) with
      | Pp.Ppcmd_string s -> s
      | _ -> assert false)
    | _ -> assert false)
  | _ -> assert false in
  path

let filter_path f =
  let rec aux = function
  | [] -> []
  | p :: l ->
    if f (logical p) then (load_path_to_physical p, logical p) :: aux l
    else aux l
  in
  aux (get_load_paths ())

let locate_absolute_library dir : CUnix.physical_path locate_result =
  (* Search in loadpath *)
  let pref, base = Libnames.split_dirpath dir in
  let loadpath = filter_path (fun dir -> Names.DirPath.equal dir pref) in
  match loadpath with
  | [] -> Error LibUnmappedDir
  | _ ->
    match select_v_file ~warn:false loadpath base with
    | Ok (_, file) -> Ok file
    | Error fail -> Error fail

let try_locate_absolute_library dir =
  match locate_absolute_library dir with
  | Ok res -> Some res
  | Error LibUnmappedDir ->
    None
  | Error LibNotFound ->
    None

let base_filename =
  let dirpath = Global.current_dirpath () in
  Option.map (fun f -> Filename.remove_extension f) (try_locate_absolute_library dirpath)
