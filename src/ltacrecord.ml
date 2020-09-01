open Ltac_plugin

open Util
open Pp
open Tacexpr
open Tacenv
open Context
open Loadpath
open Tactic_learner_internal
open Learner_helper
open Geninterp

open Pknnmax
module Knn = ConversionModule

let append file str =
  let oc = open_out_gen [Open_creat; Open_text; Open_append] 0o640 file in
  output_string oc str;
  close_out oc

let open_permanently file =
  open_out_gen [Open_creat; Open_text; Open_trunc; Open_wronly] 0o640 file

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

let benchmarking = ref None
let featureprinting = ref false

let base_filename =
  let dirpath = Global.current_dirpath () in
  Option.map (fun f -> Filename.remove_extension f) (try_locate_absolute_library dirpath)

let feat_file =
  let file = ref None in
  (fun () ->
    match !file with
      | None -> let filename = Option.default "" base_filename ^ ".feat" in
        let k = open_permanently filename in
        file := Some k;
        k
      | Some f -> f)

let eval_file =
  let file = ref None in
  (fun () ->
     match !file with
     | None -> let filename = Option.default "" base_filename ^ ".bench" in
       let k = open_permanently filename in
       file := Some k;
       k
     | Some f -> f)

let print_to_feat str =
  output_string (feat_file ()) str;
  flush (feat_file ())

let print_to_eval str =
  output_string (eval_file ()) str;
  flush (eval_file ())

let benchoptions = Goptions.{optdepr = false;
                             optname = "Tactician benchmark time";
                             optkey = ["Tactician"; "Benchmark"];
                             optread = (fun () -> !benchmarking);
                             optwrite = (fun b -> benchmarking := b;
                                          match b with
                                          | Some _ -> (match base_filename with
                                              | None -> Feedback.msg_notice (
                                                  Pp.str "No source file could be found. Disabling benchmarking.");
                                                benchmarking := None
                                              | Some f -> ignore (eval_file ()))
                                          | _ -> ())}
let featureoptions = Goptions.{optdepr = false;
                               optname = "Tactician feature outputting";
                               optkey = ["Tactician"; "Output"; "Features"];
                               optread = (fun () -> !featureprinting);
                               optwrite = (fun b -> featureprinting := b; if b then
                                              (match base_filename with
                                              | None -> Feedback.msg_notice (
                                                  Pp.str "No source file could be found. Disabling feature writing.");
                                                benchmarking := None
                                              | Some f -> ignore (feat_file ())))}

let _ = Goptions.declare_int_option benchoptions
let _ = Goptions.declare_bool_option featureoptions

let _ = Random.self_init ()

let dbsingle = Knn.create ()

let db_test : Knn.t ref = ref dbsingle
let just_classified = ref false
let current_int64 = ref Int64.minus_one

(* TODO: In interactive mode this is a memory leak, but it seems difficult to properly clean this table *)
type semilocaldb = (int list * (glob_tactic_expr * string) * proof_state list) list
let int64_to_knn : (Int64.t, semilocaldb) Hashtbl.t = Hashtbl.create 10

let current_name = ref (Names.Id.of_string "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")

type data_in = int list * (glob_tactic_expr * string)
let rec ref_tag ?(freeze=fun ~marshallable r -> r) ~name x =
  let _ = Summary.(declare_summary_tag name
    { freeze_function = (fun ~marshallable -> freeze ~marshallable !db_test);
      unfreeze_function = (fun a -> db_test := a);
      init_function = (fun () -> (* print_endline "hehe"; *) db_test := x) }) in ()

and ref2 ?freeze ~name x = ref_tag ?freeze ~name x

let in_db : data_in -> Libobject.obj = Libobject.(declare_object { (default_object "LTACRECORD") with
  cache_function = (fun (_,((feat, obj) : data_in)) ->
    db_test := Knn.add2 !db_test feat obj);
  load_function = (fun i (name, (feat, obj)) ->
    db_test := Knn.add2 !db_test feat obj; (*print_endline "load"*));
  open_function = (fun i (name, (feat, obj)) ->
    () (*;db_test := Knn.add !db_test feat obj*) (*;print_endline "open"*));
  classify_function = (fun data -> (*print_endline "classify";*) Libobject.Keep data);
  subst_function = (fun (s, data) -> print_endline "subst"; data);
  discharge_function = (fun (obj, data) -> (*print_endline "discharge";*) Some data);
  rebuild_function = (fun a -> (*print_endline "rebuild";*) a)
})

let add_to_db (x : data_in) =
  Lib.add_anonymous_leaf (in_db x)

let features term = List.map Hashtbl.hash (Features.extract_features (Hh_term.hhterm_of (Hh_term.econstr_to_constr term)))

let goal_to_features gl =
       let goal = Proofview.Goal.concl gl in
       let hyps = Proofview.Goal.hyps gl in
       let hyps_features =
          List.map
            (fun pt -> match pt with
                 | Context.Named.Declaration.LocalAssum (id, typ) ->
                   features typ
                 | Context.Named.Declaration.LocalDef (id, term, typ) ->
                   List.append (features term) (features typ))
            hyps in
       let feats = (List.append (features goal) (List.concat hyps_features)) in
       (*let feats = List.map Hashtbl.hash feats in*)
       List.sort(*_uniq*) Int.compare feats

let record_map (f : Proofview.Goal.t -> 'a)
    (gls : Proofview.Goal.t Proofview.tactic list) : 'a list Proofview.tactic =
  let rec aux gls acc =
    let open Proofview.Notations in
    match gls with
    | [] -> Proofview.tclUNIT (acc)
    | gl::gls' -> gl >>= fun gl' -> aux gls' (f gl' :: acc) in
  aux gls []

let add_to_db2 ((before, obj) : Proofview.Goal.t * (glob_tactic_expr * string))
                (after : Proofview.Goal.t list) =
  let feat = goal_to_features before in
  add_to_db (feat, obj);
  let db = Hashtbl.find int64_to_knn !current_int64 in
  Hashtbl.replace int64_to_knn !current_int64 ((feat, obj, [])::db);
  if !featureprinting then (
    let h s = string_of_int (Hashtbl.hash s) in
    (* let l2s fs = "[" ^ (String.concat ", " (List.map (fun x -> string_of_int x) fs)) ^ "]" in *)
    let p2s x = "" in
    let entry (before, (raw_tac, obj), after) =
      "{\"before\": " ^ p2s before ^
      ", \"tacid\": " ^ (*Base64.encode_string*) h obj ^
      ", \"after\": [" ^ String.concat ", " (List.map p2s after) ^ "]}\n" in
    print_to_feat (entry (before, obj, after)))

let _ = ref2 ~name:"ltacrecord-db" dbsingle

(* let () = Vernacentries.requirehook := (fun files ->
 *   let newrequires = List.map (fun (pair) -> CUnix.canonical_path_name (snd pair)) files in
 *   let newrequires = List.map (fun (file) -> (String.sub file 0 (String.length file - 2)) ^ "feat") newrequires in
 *   requires := List.append newrequires !requires
 * ) *)

let firstn n l =
  let rec aux acc n l =
    match n, l with
    | 0, _ -> List.rev acc
    | n, h::t -> aux (h::acc) (pred n) t
    | _ -> List.rev acc
  in
  aux [] n l

let get_k_str ranking comp =
    let rec get_k' acc ranking =
    match ranking with
    | (_, f, o) :: r -> if String.equal o comp then acc else get_k' (1 + acc) r
    | [] -> -1
    in get_k' 0 ranking

let mk_ml_tac tac = fun args is -> tac

let register tac name =
  let fullname = {mltac_plugin = "recording"; mltac_tactic = name} in
  register_ml_tactic fullname [| tac |]

let run_ml_tac name = TacML (CAst.make ({mltac_name = {mltac_plugin = "recording"; mltac_tactic = name}; mltac_index = 0}, []))

let print_rank env rank =
  let rank = firstn 10 rank in
  let tac_pp tac = format_oneline (Pptactic.pr_glob_tactic env tac) in
  let strs = List.map (fun (x, t) -> (*(Pp.str (Printf.sprintf "%.4f" x)) ++*) (Pp.str " ") ++ (tac_pp t) ++ (Pp.str "\n")) rank in
  Pp.seq strs

(** Goal printing tactic *)

let print_goal = Proofview.Goal.enter
    (fun gl ->
       let env = Proofview.Goal.env gl in
       let sigma = Proofview.Goal.sigma gl in
       let goal = Proofview.Goal.concl gl in
       let hyps = Proofview.Goal.hyps gl in
       let hyps_str =
          List.map
            (fun pt -> match pt with
                 | Context.Named.Declaration.LocalAssum (id, typ) ->
                   (Pp.str "\n") ++ (Names.Id.print id.binder_name) ++
                   (Pp.str " : ") ++ (Printer.pr_econstr_env env sigma typ)
                 | Context.Named.Declaration.LocalDef (id, term, typ) ->
                   (Pp.str "\n") ++ (Names.Id.print id.binder_name) ++ (Pp.str "term") ++
                   (Pp.str " : ") ++ (Printer.pr_econstr_env env sigma typ)) (* TODO: Deal with the term in this case *)
            hyps in
       Proofview.tclTHEN
       (Proofview.tclLIFT (Proofview.NonLogical.print_warning (Printer.pr_econstr_env env sigma (goal))))
       (Proofview.tclTHEN
        (Proofview.tclLIFT (Proofview.NonLogical.print_warning (Pp.seq hyps_str)))
        (Proofview.tclLIFT (Proofview.NonLogical.print_warning (Pp.seq (List.map (fun s -> Pp.pr_comma () ++ (Pp.str (string_of_int s))) (goal_to_features gl)))))))

(* Running predicted tactics *)

exception PredictionsEnd

let parse_tac tac =
    try
      Tacinterp.eval_tactic tac
    with
    e -> print_endline (Printexc.to_string e); flush_all (); assert false

let rec tclFairJoin (tacs : 'a Proofview.tactic Proofview.tactic) : 'a Proofview.tactic =
    let open Proofview in
    let open Notations in
    tclCASE tacs >>= function
    | Fail (iexn, info) -> tclZERO ~info:info iexn
    | Next (tac1, resttacs) ->
      tclCASE tac1 >>= function
      | Fail e -> (tclFairJoin (resttacs e))
      | Next (a, tac1') ->
        tclOR (tclUNIT a)
              (fun e -> (tclFairJoin (tclOR (resttacs e)
                                            (fun e -> tclUNIT (tac1' e)))))

let tclInterleave tac1 tac2 =
    let open Proofview in
    let open Notations in
    tclFairJoin ((tclUNIT tac1) <+> (tclUNIT tac2))

let tclInterleaveList (tacs : 'a Proofview.tactic list) : 'a Proofview.tactic =
    let open Proofview in
    let open Notations in
    tclFairJoin
      (List.fold_right (fun tac acc -> (tclUNIT tac) <+> acc) tacs (tclZERO PredictionsEnd))

let rec tclInterleaveCaseTacsSpecial start (tacs : bool Proofview.case Proofview.tactic) =
    let open Proofview in
    let open Notations in
    tclCASE tacs >>= function
    | Fail (iexn, info) -> tclZERO ~info:info iexn
    | Next (tac1case, resttacs) ->
      match tac1case with
      | Fail e -> (tclInterleaveCaseTacsSpecial start (resttacs e))
      | Next (b, tac1') ->
        if (start && b) then Tacticals.New.tclZEROMSG (Pp.str "Ran out of tactics") else
        tclOR (if b then tclUNIT () else Tacticals.New.tclCOMPLETE (tclUNIT ()))
              (fun e -> (tclInterleaveCaseTacsSpecial b (tclOR (resttacs e)
                                                               (fun e -> (tclCASE (tac1' e))))))

let rec tclInfiniteTrue () =
    let open Proofview in
    tclOR (tclUNIT true) (fun _ -> tclInfiniteTrue ())

let tclInterleaveListSpecial (tacs : unit Proofview.tactic list) : unit Proofview.tactic =
    let open Proofview in
    let open Notations in
    let tacs = List.map (fun t -> t <*> tclUNIT false) tacs in
    tclInterleaveCaseTacsSpecial true
      (List.fold_right (fun tac acc -> (tclCASE tac) <+> acc) tacs (tclCASE (tclInfiniteTrue ())))

let tclInterleaveSpecial tac1 tac2 =
    tclInterleaveListSpecial [tac1; tac2]

let rec tclInterleaveWrong tac1 tac2 =
    let open Proofview in
    let open Notations in
    tclCASE tac1 >>= function
    | Fail iexn -> tac2
    | Next ((), tac1') -> tclOR (tclUNIT ()) (fun e -> (tclInterleaveWrong tac2 (tac1' e)))

module IntMap = Stdlib.Map.Make(struct type t = string
                                       let compare = String.compare end)

let removeDups ranking =
    let ranking_map = List.fold_left
      (fun map (score, (fl, tac, str)) ->
        IntMap.update
          str
          (function
            | None -> Some (score, fl, tac)
            | Some (lscore, lfl, ltac) -> if score > lscore then Some (score, fl, tac) else Some (lscore, lfl, ltac)
          )
          map
      )
      IntMap.empty
      ranking
    in
    let new_ranking = List.map (fun (str, (score, fl, tac)) -> (score, (fl, tac, str))) (IntMap.bindings ranking_map) in
    List.sort (fun (x, _) (y, _) -> Float.compare y x) new_ranking

let predict gl =
  let feat = goal_to_features gl in
  let r = Knn.knn !db_test feat in
  let r = List.map (fun (a, b, (c, d)) -> (a, (b, c, d))) r in
  let r = removeDups r in
  List.map (fun (a, (b, c, d)) -> (c, d)) r

let print_goal_short = Proofview.Goal.enter
    (fun gl ->
       let env = Proofview.Goal.env gl in
       let sigma = Proofview.Goal.sigma gl in
       let goal = Proofview.Goal.concl gl in
       (Proofview.tclLIFT (Proofview.NonLogical.print_info (Printer.pr_econstr_env env sigma (goal)))))

type blaat = | Intermediate | Complete | No_goal

let rec tclFold tac : blaat Proofview.tactic =
    let open Proofview in
    let open Notations in
    tclFOCUS ~nosuchgoal:(tclUNIT No_goal) 1 1 tac >>=
    (function
     | No_goal -> tclUNIT Complete
     | Complete -> tclFold tac
     | Intermediate -> tclUNIT Intermediate)

let rec tclSearchBFS () mark : blaat Proofview.tactic =
    let open Proofview in
    tclFold (Goal.enter_one (fun gl ->
        let predictions = List.map fst (predict gl) in
        (tclSearchGoalBFS predictions mark)))
and tclSearchGoalBFS ps mark =
    let open Proofview in
    let open Notations in
      tclUNIT Intermediate <+> tclInterleaveList
        (List.mapi (fun i t ->
          let tac2 = Tacinterp.eval_tactic t in
          (
           (tclLIFT (NonLogical.print_info (Pp.str "------------------------------"))) <*>
           (tclLIFT (NonLogical.print_info (Pp.str (mark ^ "." ^ string_of_int i)))) <*>
           (tclLIFT (NonLogical.print_info (Pp.app (Pp.str "Exec: ") (Pptactic.pr_glob_tactic Environ.empty_env t)))) <*>
           print_goal_short <*>
           tclPROGRESS tac2 <*>
           (*print_goal_short <*>*)
           tclSearchBFS () (mark ^ "." ^ string_of_int i))
       ) ps)

exception DepthEnd

let tclFoldList tacs =
  let rec tclFoldList' tacs depth =
    let open Proofview in
    match tacs with
    | [] -> tclZERO (if depth then DepthEnd else PredictionsEnd)
    | tac::tacs' -> tclOR tac
                      (fun e ->
                         let depth = depth || (match e with
                           | (DepthEnd, _) -> true
                           | _ -> false) in
                         tclFoldList' tacs' depth) in
  tclFoldList' tacs false

let synthesize_tactic (env : Environ.env) tcs =
  let tac_pp env t = Pp.string_of_ppcmds (format_oneline (Pptactic.pr_glob_tactic env t)) in
  let tcs = List.map (tac_pp env) tcs in
  let res = Pp.string_of_ppcmds (Pp.h 0 (Pp.str "search" ++ Pp.ws 1 ++ Pp.str "failing" ++ Pp.ws 1 ++
                                         Pp.str "ltac2:(x|--" ++ (Pp.prlist_with_sep
                                                                    (fun () -> Pp.str "-")
                                                                    (fun t -> Pp.str "ltac1:(" ++ Pp.str t ++ Pp.str ")")
                                                                    (Stdlib.List.rev tcs)) ++ Pp.str ("--|x)."))) in
  if String.contains res '\n' then (print_endline res; assert false) else res

let tclDebugTac t i mark env tcs debug =
    let open Proofview in
    let open Notations in
    let tac2 = parse_tac t in
    (* let tac2 = tclUNIT () >>= fun () ->
     *     try
     *         tac2 >>= (fun () -> CErrors.user_err (Pp.str "blaat"))
     *     with e -> print_endline (Printexc.to_string e); print_endline "hahahah dom"; assert false; Tacticals.New.tclZEROMSG (Pp.str "Tactic error")
     * in *)
    if debug then
    (
     (tclLIFT (NonLogical.print_info (Pp.str "------------------------------"))) <*>
     (tclLIFT (NonLogical.print_info (Pp.str (mark ^ "." ^ string_of_int i)))) <*>
     (tclLIFT (NonLogical.print_info (Pp.str (synthesize_tactic env tcs)))) <*>
     (tclLIFT (NonLogical.print_info (Pp.app (Pp.str "Exec: ") (Pptactic.pr_glob_tactic env t)))) <*>
     print_goal_short <*>
     tclPROGRESS tac2)
    else tclPROGRESS tac2

let rec tclFold2 (d : 'a) (tac : 'a -> 'a Proofview.tactic) : 'a Proofview.tactic =
    let open Proofview in
    let open Notations in
    (tclFOCUS ~nosuchgoal:(tclUNIT None) 1 1 (tac d >>= (fun x -> tclUNIT (Some x)))) >>=
    (function
     | None -> tclUNIT d
     | Some x -> tclFold2 x tac)


let rec tclSearchDiagonalDFS depth mark tcs : (int * string * glob_tactic_expr list) Proofview.tactic =
    let open Proofview in
    let open Notations in
    tclFold2 (depth, mark, tcs) (fun (depth, mark, tcs) -> Goal.enter_one (fun gl ->
        let predictions = predict gl in
        tclFoldList
            (List.mapi
                 (fun i (t, ts) ->
                      let ndepth = depth - i in
                      if ndepth <= 0 then tclZERO DepthEnd else
                        (tclDebugTac t i mark Environ.empty_env tcs false <*>
                         (tclSearchDiagonalDFS (ndepth - 1) (mark ^ "." ^ string_of_int i) (t::tcs))))
                 predictions)
        ))

let rec tclSearchDiagonalIterative d : (string * glob_tactic_expr list) Proofview.tactic =
    let open Proofview in
    let open Notations in
    (* (tclLIFT (NonLogical.print_info (Pp.str ("Iterative depth: " ^ string_of_int d)))) <*> *)
    tclOR
        (tclSearchDiagonalDFS d "" [] >>= (fun (d, m, tcs) -> tclUNIT (m, tcs)))
        (function
        | (PredictionsEnd, _) -> Tacticals.New.tclZEROMSG (Pp.str "Tactician failed: there are no more tactics left")
        | _ -> tclSearchDiagonalIterative (d + 1))

(* TODO: Doesn't compile anymore and is probably wrong
let rec tclSearch () mark curr : blaat Proofview.tactic =
    let open Proofview in
    tclFold (Goal.enter_one (fun gl ->
        let predictions = List.map fst (predict gl) in
        (tclSearchGoal predictions mark curr)))
and tclSearchGoal ps mark curr =
    let open Proofview in
    let open Notations in
    match ps with
    | [] -> Tacticals.New.tclZEROMSG (Pp.str "No more predicted tactics")
    | tac::ps' ->
      let tac2 = parse_tac tac in
      tclUNIT Intermediate <+> tclInterleave
        (tclSearchGoal ps' mark (curr + 1))
        (
         (tclLIFT (NonLogical.print_info (Pp.str "------------------------------"))) <*>
         (tclLIFT (NonLogical.print_info (Pp.str (mark ^ "." ^ string_of_int curr)))) <*>
         (tclLIFT (NonLogical.print_info (Pp.app (Pp.str "Exec: ") (Pptactic.pr_raw_tactic Environ.empty_env Evd.empty tac)))) <*>
         print_goal_short <*>
         tclPROGRESS tac2 <*>
         print_goal_short <*>
         tclSearch () (mark ^ "." ^ string_of_int curr) 0)
*)

  let tclTIMEOUT2 n t =
    Proofview.tclOR
      (Timeouttac.ptimeout n t)
      begin function (e, info) -> match e with
        | Logic_monad.Tac_Timeout -> Tacticals.New.tclZEROMSG (Pp.str "timout")
        | e -> Tacticals.New.tclZEROMSG (Pp.str "haha")
      end

let searched = ref false

let contains s1 s2 =
    let re = Str.regexp_string s2
    in
        try ignore (Str.search_forward re s1 0); true
        with Not_found -> false

let rec tclInfiniteUnit () =
    let open Proofview in
    tclOR (tclUNIT ()) (fun _ -> tclInfiniteUnit ())

let commonSearch () =
    let open Proofview in
    let open Notations in
    tclLIFT (NonLogical.make (fun () -> CWarnings.get_flags ())) >>= (fun oldFlags ->
        let setFlags () = tclLIFT (NonLogical.make (fun () ->
          Dumpglob.continue (); CWarnings.set_flags (oldFlags))) in
        tclLIFT (NonLogical.make (fun () -> Dumpglob.pause(); CWarnings.set_flags ("-all"))) <*>
        tclOR
          (tclONCE (Tacticals.New.tclCOMPLETE (tclSearchDiagonalIterative 1)) >>=
           fun m -> setFlags () <*> tclUNIT m)
          (fun (e, i) -> setFlags () <*> tclZERO ~info:i e))

let benchmarkSearch () : unit Proofview.tactic =
    let open Proofview in
    let open Notations in
    let modpath = Global.current_modpath () in
    let time = match !benchmarking with
      | None -> assert false
      | Some t -> t in
    let full_name = Names.ModPath.to_string modpath ^ "." ^ Names.Id.to_string !current_name in
    let print_success (m, tcs) =
        let open NonLogical in
        let tstring = synthesize_tactic Environ.empty_env tcs in
        (make (fun () -> print_to_eval ("\t" ^ m ^ "\t" ^ tstring))) >>
        (print_info (Pp.str ("Proof found for " ^ full_name ^ "!"))) in
    let print_name = NonLogical.make (fun () ->
        print_to_eval ("\n" ^ (full_name) ^ "\t" ^ string_of_int time)) in
    if !searched then Tacticals.New.tclZEROMSG (Pp.str "Already searched") else
      (searched := true;
       tclTIMEOUT2 time (tclLIFT (NonLogical.print_info (Pp.str ("Start proof search for " ^ full_name))) <*>
                              tclLIFT print_name <*>
                              commonSearch () >>=
                              fun m -> tclLIFT (print_success m)) <*>
       Tacticals.New.tclZEROMSG (Pp.str "Proof benchmark search does not actually find proofs"))

let userPredict = Proofview.tclUNIT ()

let userSearch =
    let open Proofview in
    let open Notations in
    commonSearch () >>= (fun (tr, tcs) ->
        tclLIFT (NonLogical.print_info (
            Pp.str ("Tactician found a proof! The following tactic caches the proof:\n" ^ synthesize_tactic Environ.empty_env tcs))))

(* Name globalization *)

(*
let id_of_global env = function
  | ConstRef kn -> Label.to_id (Constant.label kn)
  | IndRef (kn,0) -> Label.to_id (MutInd.label kn)
  | IndRef (kn,i) ->
    (Environ.lookup_mind kn env).mind_packets.(i).mind_typename
  | ConstructRef ((kn,i),j) ->
    (Environ.lookup_mind kn env).mind_packets.(i).mind_consnames.(j-1)
  | VarRef v -> v

let rec dirpath_of_mp = function
  | MPfile sl -> sl
  | MPbound uid -> DirPath.make [MBId.to_id uid]
  | MPdot (mp,l) ->
    Libnames.add_dirpath_suffix (dirpath_of_mp mp) (Label.to_id l)

let dirpath_of_global = function
  | ConstRef kn -> dirpath_of_mp (Constant.modpath kn)
  | IndRef (kn,_) | ConstructRef ((kn,_),_) ->
    dirpath_of_mp (MutInd.modpath kn)
  | VarRef _ -> DirPath.empty

let qualid_of_global env r =
  Libnames.make_qualid (dirpath_of_global r) (id_of_global env r)
*)

(* End name globalization *)

(* Returns true if tactic execution should be skipped *)
let pre_vernac_solve pstate id =
  let new_name = Proof_global.get_proof_name pstate in
  if not (Names.Id.equal !current_name new_name) then (
    (* if !featureprinting then print_to_feat ("#lemma " ^ (Names.Id.to_string new_name) ^ "\n"); *)

    (* TODO: For purposes of benchmarking we want to know when a new proof is started
     * Note that this only works in batch mode, when no undo/back commands are issued. *)
    if (not (!benchmarking == None)) && not (contains (Names.Id.to_string new_name) "_subproof") then
      searched := false
  );
  current_name := new_name;
  current_int64 := id;
  (* print_endline ("db_test: " ^ string_of_int (Knn.count !db_test));
   * print_endline ("id: " ^ (Int64.to_string id)); *)
  if not !just_classified then (
    List.iter (fun (fl, obj, _) -> add_to_db (fl, obj))
      (Hashtbl.find int64_to_knn id);
    Hashtbl.remove int64_to_knn id;
    true
  ) else (
    Hashtbl.add int64_to_knn id [];
    false
  )

(* Structures for local database in evar_map during tactic execution *)
type localdb = (Proofview.Goal.t list * glob_tactic_expr * Proofview.Goal.t list) list
type local_stack = Proofview.Goal.t list list
type tactic_trace = glob_tactic_expr list

let localdb_field : localdb Evd.Store.field = Evd.Store.field ()
let local_stack_field : local_stack Evd.Store.field = Evd.Store.field ()
let tactic_trace_field : local_stack Evd.Store.field = Evd.Store.field ()

let modify_field fi g =
  let open Proofview in
  let open Notations in
  tclEVARMAP >>= fun evm ->
  let store = Evd.get_extra_data evm in
  let data = Option.get (Evd.Store.get store fi) in
  let data', ret = g data in
  let evm' = Evd.set_extra_data (Evd.Store.set store fi data') evm in
  Unsafe.tclEVARS evm' <*> tclUNIT ret

let set_field fi d =
  let open Proofview in
  let open Notations in
  tclEVARMAP >>= fun evm ->
  let store = Evd.get_extra_data evm in
  let evm' = Evd.set_extra_data (Evd.Store.set store fi d) evm in
  Unsafe.tclEVARS evm'

(*
let modify_field_goals fi g =
  let open Proofview in
  let open Notations in
  tclEVARMAP >>= fun evm ->
  let store = Evd.get_extra_data evm in
  let data = Option.get (Evd.Store.get store fi) in
  let data', ret = g data in
  let evm' = Evd.set_extra_data (Evd.Store.set store fi data') evm in
  Unsafe.tclEVARS evm' <*> tclUNIT ret

let set_field_goals fi d =
  let open Proofview in
  let open Notations in
  tclEVARMAP >>= fun evm ->
  let store = Evd.get_extra_data evm in
  let evm' = Evd.set_extra_data (Evd.Store.set store fi d) evm in
  Unsafe.tclEVARS evm'
   *)

let push_local_stack gl =
  modify_field local_stack_field (fun st -> gl::st, ())

let pop_local_stack () =
  modify_field local_stack_field (fun st -> List.tl st, List.hd st)

let init_local_stack () =
  set_field local_stack_field []

let push_localdb x =
  modify_field localdb_field (fun db -> x::db, ())

let get_localdb () =
  modify_field localdb_field (fun db -> [], db)

let init_localdb () =
  set_field localdb_field []

let push_tactic_trace tac =
  modify_field local_stack_field (fun tr -> tac::tr, ())

(*
let get_tactic_trace () =
  modify_field localdb_field (fun tr -> [], tr)

let init_tactic_trace () =
  set_field tactic_trace_field []
*)

(* Tactic recording tactic *)

let val_tag wit = val_tag (Genarg.topwit wit)
let register_interp0 wit f =
  let open Ftactic.Notations in
  let interp ist v =
    f ist v >>= fun v -> Ftactic.return (Val.inject (val_tag wit) v)
  in
  Geninterp.register_interp0 wit interp

let (wit_glbtactic : (Empty.t, glob_tactic_expr, glob_tactic_expr) Genarg.genarg_type) =
  let wit = Genarg.create_arg "glbtactic" in
  let () = register_val0 wit None in
  wit

let () = register_interp0 wit_glbtactic (fun ist v -> Ftactic.return v)

let push_state_tac () =
  let open Proofview in
  let open Notations in
  Goal.goals >>= record_map (fun x -> x) >>= fun gls -> push_local_stack gls

let record_tac2 (tac2 : glob_tactic_expr) : unit Proofview.tactic =
  let open Proofview.Notations in
  let tac_pp t = format_oneline (Pptactic.pr_glob_tactic Environ.empty_env t) in
  let tac = Pp.string_of_ppcmds (tac_pp tac2) in
  pop_local_stack () >>= fun before_gls ->
  if (String.equal tac "suggest" || String.equal tac "search") then Proofview.tclUNIT () else
    Proofview.Goal.goals >>= record_map (fun x -> x) >>= fun after_gls ->
    push_localdb (before_gls, tac2, after_gls)
        (*let tac_str = Pp.string_of_ppcmds (Pptactic.pr_glob_tactic env tac) in*)

        (* Make predictions *)
        (*let r = Predictor.knn db feat in
           let r = List.map (fun (x, y, (z, q)) -> (x, y, q)) r in
           let pp_str = Pp.int (get_k_str r tac) ++ (*(Pp.str " ") ++ (Pptactic.pr_raw_tactic tac) ++*) (Pp.str "\n") in
           append "count.txt" (Pp.string_of_ppcmds pp_str);*)

let ml_record_tac args is =
  (*let num = Tacinterp.Value.cast (Genarg.topwit Tacarg.wit_tactic) (List.hd args) in*)
  let tac = Tacinterp.Value.cast (Genarg.topwit wit_glbtactic) (List.hd args) in
  record_tac2 tac

let ml_push_state_tac args is =
  push_state_tac ()

let () = register ml_record_tac "recordtac"
let () = register ml_push_state_tac "pushstatetac"

let run_record_tac (tac : glob_tactic_expr) : glob_tactic_expr =
  let enc = Genarg.in_gen (Genarg.glbwit wit_glbtactic) tac in
  TacML (CAst.make ({mltac_name = {mltac_plugin = "recording"; mltac_tactic = "recordtac"}; mltac_index = 0},
                    [TacGeneric enc]))

let run_pushs_state_tac (): glob_tactic_expr =
  (*let tac_glob = Tacintern.intern_pure_tactic*)
  TacML (CAst.make ({mltac_name = {mltac_plugin = "recording"; mltac_tactic = "pushstatetac"}; mltac_index = 0},
                []))

let record_tac_complete tac : glob_tactic_expr =
  TacThen (run_pushs_state_tac (), TacThen (tac, run_record_tac tac))

let recorder (tac : glob_tactic_expr) : unit Proofview.tactic =
  let open Proofview in
  let open Notations in
  let rec annotate (tcom : glob_tactic_expr) : glob_tactic_expr =
    match tcom with
    | TacAtom _         ->                 record_tac_complete tcom (*TacAtom (intros, destruct, etc)*)
    | TacThen (t1, t2)  ->                 TacThen (annotate t1, annotate t2) (*TacThen (a; b)*)
    | TacDispatch tl    ->                 TacDispatch (List.map annotate tl) (*TacDispatch ([> a | b | c])*)
    | TacExtendTac (tl1, t, tl2) ->        TacExtendTac (Array.map annotate tl1, annotate t, Array.map annotate tl2)
                                           (*TacExtendTac ([> a | b .. | c])*)
    | TacThens (t1, tl) ->                 TacThens (annotate t1, List.map annotate tl) (*TacThens (a; [b | c| d])*)
    | TacThens3parts (t1, tl1, t2, tl2) -> TacThens3parts (annotate t1, Array.map annotate tl1,
                                                           annotate t2, Array.map annotate tl2)
                                           (*TacThens3parts (a; [b | c .. | d])*)
    | TacFirst _        ->                 record_tac_complete tcom (*TacFirst (first [a | b | c])*)
    | TacComplete _     ->                 assert false (*TacComplete ?*)
    | TacSolve _        ->                 record_tac_complete tcom (*TacSolve (solve [auto])*)
    | TacTry _          ->                 record_tac_complete tcom (*TacTry (try intros)*)
    | TacOr _           ->                 record_tac_complete tcom (*TacOr (intros + intros)*)
    | TacOnce _         ->                 record_tac_complete tcom (*TacOnce (once intros)*)
    | TacExactlyOnce _  ->                 record_tac_complete tcom (*TacExactlyOnce (exactly_once intros)*)
    | TacIfThenCatch _  ->                 record_tac_complete tcom (*TacIfThenCatch (tryif intros then intros else intros)*)
    | TacOrelse _       ->                 record_tac_complete tcom (*TacOrelse (intros || intros)*)
    | TacDo _           ->                 record_tac_complete tcom (*TacDo (do 5 intros)*)
    | TacTimeout _      ->                 record_tac_complete tcom (*TacTimeout (timeout 5 intros)*)
    | TacTime _         ->                 record_tac_complete tcom (*TacTime (time intros)*)
    | TacRepeat _       ->                 record_tac_complete tcom (*TacRepeat (repeat intros)*)
    | TacProgress _     ->                 record_tac_complete tcom (*TacProgress (progress intros)*)
    | TacShowHyps _     ->                 assert false (*TacShowHyps ?*)
    | TacAbstract _     ->                 record_tac_complete tcom (*TacAbstract (abstract auto)*)
    | TacId _           ->                 record_tac_complete tcom (*TacId (idtac)*)
    | TacFail _         ->                 record_tac_complete tcom (*TacFail (fail)*)
    | TacInfo _         ->                 record_tac_complete tcom (*TacInfo (info auto)*)
    | TacLetIn _        ->                 record_tac_complete tcom (*TacLetIn (let x:= intros in x)*)
    | TacMatch _        ->                 record_tac_complete tcom (*TacMatch (match False with _ => intros end)*)
    | TacMatchGoal _    ->                 record_tac_complete tcom (*TacMatchGoal (match goal with |- _ => intros end)*)
    | TacFun _          ->                 record_tac_complete tcom (*TacFun (fun x => intros)*)
    | TacArg _          ->                 record_tac_complete tcom (*TacArg (split, fresh, context f [_], eval simpl in 5, type of 5, type_term 5, numgoals)*)
    | TacSelect _       ->                 assert false (*TacSelect (only 1: intros)*)
    | TacML _           ->                 record_tac_complete tcom (*TacML ?*)
    | TacAlias _        ->                 record_tac_complete tcom (*TacAlias (guard 1<=1, auto, assert_fails auto, assert_succeeds auto)*)
  in
  let save_db (db : localdb) =
      let tac_pp t = format_oneline (Pptactic.pr_glob_tactic Environ.empty_env t) in
      let string_tac t = Pp.string_of_ppcmds (tac_pp t) in
      let raw_tac t = Pcoq.parse_string Pltac.tactic_eoi t in
      let tryadd (before_gls, tac, after_gls) =
        let s = string_tac tac in
        let s = Str.global_replace (Str.regexp "change_no_check") "change" s in
        try
          (* TODO: Fix parsing bugs and remove parsing *)
          let _ = raw_tac s in
          List.iter (fun x -> add_to_db2 (x, (tac, s)) after_gls) before_gls
        with
        | Stream.Error txt -> append "parse_errors.txt" (txt ^ " : " ^ s ^ "\n")
        | CErrors.UserError (_, txt)  -> append "parse_errors.txt" (Pp.string_of_ppcmds txt ^ " : " ^ s ^ "\n") in
      List.iter (fun trp -> tryadd trp) db; tclUNIT () in
  let rtac = annotate tac in
  let ptac = Tacinterp.eval_tactic rtac in
  let ptac = init_local_stack () <*> init_localdb () <*> ptac <*> get_localdb () >>= save_db in
  match !benchmarking with
  | None -> ptac
  | Some _ -> (tclUNIT () >>= fun () -> benchmarkSearch ()) <+> ptac

let hide_interp_t global t ot =
  let open Proofview in
  let open Notations in
  let hide_interp env =
    let ist = Genintern.empty_glob_sign env in
    let te = Tacintern.intern_pure_tactic ist t in
    let t = recorder te in
    match ot with
    | None -> t
    | Some t' -> Tacticals.New.tclTHEN t t'
  in
  if global then
    Proofview.tclENV >>= fun env ->
    hide_interp env
  else
    Proofview.Goal.enter begin fun gl ->
      hide_interp (Proofview.Goal.env gl)
    end
