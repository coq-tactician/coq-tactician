open Ltac_plugin

open Util
open Pp
open Tacexpr
open Tacenv
open Context
open Loadpath

open Pknnmax
module TacticNaiveKnn = MakeNaiveKnn (struct
                                          type feature = int
                                          type obj = (Tacexpr.raw_tactic_expr * string)
                                          let compare = Int.compare
                                          let equal = Int.equal
                                          let hash = Hashtbl.hash
                                      end)
module Knn = TacticNaiveKnn

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
let int64_to_knn : (Int64.t, Knn.t) Hashtbl.t = Hashtbl.create 10

let current_name = ref (Names.Id.of_string "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")

type data_in = int list * (Tacexpr.raw_tactic_expr * string)
let rec ref_tag ?(freeze=fun ~marshallable r -> r) ~name x =
  let _ = Summary.(declare_summary_tag name
    { freeze_function = (fun ~marshallable -> freeze ~marshallable !db_test);
      unfreeze_function = (fun a -> db_test := a);
      init_function = (fun () -> print_endline "hehe"; db_test := x) }) in ()

and ref2 ?freeze ~name x = ref_tag ?freeze ~name x

let in_db : data_in -> Libobject.obj = Libobject.(declare_object { (default_object "LTACRECORD") with
  cache_function = (fun (_,((feat, obj) : data_in)) ->
    db_test := Knn.add !db_test feat obj);
  load_function = (fun i (name, (feat, obj)) ->
    db_test := Knn.add !db_test feat obj; (*print_endline "load"*));
  open_function = (fun i (name, (feat, obj)) ->
    () (*;db_test := Knn.add !db_test feat obj*) (*;print_endline "open"*));
  classify_function = (fun data -> (*print_endline "classify";*) Libobject.Keep data);
  subst_function = (fun (s, data) -> print_endline "subst"; data);
  discharge_function = (fun (obj, data) -> (*print_endline "discharge";*) Some data);
  rebuild_function = (fun a -> (*print_endline "rebuild";*) a)
})

let add_to_db (x : data_in) =
  Lib.add_anonymous_leaf (in_db x)

let add_to_db2 ((feat, obj) : data_in) =
  add_to_db (feat, obj);
  let db = Hashtbl.find int64_to_knn !current_int64 in
  Hashtbl.replace int64_to_knn !current_int64 (Knn.add db feat obj);
  if !featureprinting then (
    let h s = string_of_int (Hashtbl.hash s) in
    let l2s fs = "[" ^ (String.concat ", " (List.map (fun x -> string_of_int x) fs)) ^ "]" in
    let entry (feats, (raw_tac, obj)) =
      l2s feats ^ " : " ^ (*Base64.encode_string*) h obj ^ "\n" in
    print_to_feat (entry (feat, obj)))

let _ = ref2 ~name:"ltacrecord-db" dbsingle
(* let _ = ref3 ~name:"ltacrecord-db-tmp" dbsingle *)

(*let db = Knn.create ()*)

(* let requires : string list ref = ref [] *)

let lmax ls = List.fold_left (fun m c -> if Stateid.newer_than c m then c else m) (List.hd ls) ls

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

let features term = List.map Hashtbl.hash (Features.extract_features (Hh_term.hhterm_of (Hh_term.econstr_to_constr term)))

let print_rank rank =
    let rank = firstn 10 rank in
    let strs = List.map (fun (x, f, o) -> (Pp.str (Printf.sprintf "%.4f" x)) ++ (Pp.str " ") ++ (Pp.str o) ++ (Pp.str "\n")) rank in
    Pp.seq strs

(** Goal printing tactic *)

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

let () = register (mk_ml_tac print_goal) "printgoal"

let ml_print_goal () = run_ml_tac "printgoal"

let hash_hash : (int, string) Hashtbl.t = Hashtbl.create 100

let add_hash_hash tac = Hashtbl.replace hash_hash (Hashtbl.hash tac) tac; (Hashtbl.hash tac)

let find_tac num = Hashtbl.find hash_hash num

(* Tactic printing tactic *)

let print_tac tac =
  Proofview.tclLIFT (Proofview.NonLogical.print_warning (Pp.str tac))

let print_tac tac_num = print_tac (find_tac tac_num)

let ml_print_tac args is =
  let str = Tacinterp.Value.cast (Genarg.topwit Stdarg.wit_int) (List.hd args) in
  print_tac str

let () = register ml_print_tac "printtac"

(*let () = append "count.txt" "newfile\n"**)

let run_print_tac tac =
  let hash = add_hash_hash tac in
  let enc = Genarg.in_gen (Genarg.rawwit Stdarg.wit_int) hash in
  TacML (CAst.make ({mltac_name = {mltac_plugin = "recording"; mltac_tactic = "printtac"}; mltac_index = 0},
                [TacGeneric enc]))

(* Running predicted tactics *)

exception PredictionsEnd

let parse_tac tac =
    try
       Tacinterp.hide_interp false tac None
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

let listEq ls1 ls2 = match ls1, ls2 with
| [], [] -> true
| [], _::_ -> false
| _::_, [] -> false
| (f1, (_, _, s1))::ls1', (f2, (_, _, s2))::ls2' -> if Float.equal f1 f2 && String.equal s1 s2 then true else false

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
          let tac2 = parse_tac t in
          (
           (tclLIFT (NonLogical.print_info (Pp.str "------------------------------"))) <*>
           (tclLIFT (NonLogical.print_info (Pp.str (mark ^ "." ^ string_of_int i)))) <*>
           (tclLIFT (NonLogical.print_info (Pp.app (Pp.str "Exec: ") (Pptactic.pr_raw_tactic Environ.empty_env Evd.empty t)))) <*>
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

let synthesize_tactic tcs =
    let res = Pp.string_of_ppcmds (Pp.h 0 (Pp.str "search" ++ Pp.ws 1 ++ Pp.str "failing" ++ Pp.ws 1 ++
        Pp.str "ltac2:([#" ++ (Pp.prlist_with_sep
        (fun () -> Pp.str "#")
        (fun t -> Pp.str "ltac1:(" ++ Pp.str t ++ Pp.str ")")
        (Stdlib.List.rev tcs)) ++ Pp.str ("#])."))) in
    if String.contains res '\n' then (print_endline res; assert false) else res

let tclDebugTac t i mark tcs debug =
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
     (tclLIFT (NonLogical.print_info (Pp.str (synthesize_tactic tcs)))) <*>
     (tclLIFT (NonLogical.print_info (Pp.app (Pp.str "Exec: ") (Pptactic.pr_raw_tactic Environ.empty_env Evd.empty t)))) <*>
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


let rec tclSearchDiagonalDFS depth mark tcs : (int * string * string list) Proofview.tactic =
    let open Proofview in
    let open Notations in
    tclFold2 (depth, mark, tcs) (fun (depth, mark, tcs) -> Goal.enter_one (fun gl ->
        let predictions = predict gl in
        tclFoldList
            (List.mapi
                 (fun i (t, ts) ->
                      let ndepth = depth - i in
                      if ndepth <= 0 then tclZERO DepthEnd else
                        (tclDebugTac t i mark tcs false <*>
                         (tclSearchDiagonalDFS (ndepth - 1) (mark ^ "." ^ string_of_int i) (ts::tcs))))
                 predictions)
        ))

let rec tclSearchDiagonalIterative d : (string * string list) Proofview.tactic =
    let open Proofview in
    let open Notations in
    (* (tclLIFT (NonLogical.print_info (Pp.str ("Iterative depth: " ^ string_of_int d)))) <*> *)
    tclOR
        (tclSearchDiagonalDFS d "" [] >>= (fun (d, m, tcs) -> tclUNIT (m, tcs)))
        (function
        | (PredictionsEnd, _) -> Tacticals.New.tclZEROMSG (Pp.str "Tactician failed: there are no more tactics left")
        | _ -> tclSearchDiagonalIterative (d + 1))

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
        let setFlags () = tclLIFT (NonLogical.make (fun () -> CWarnings.set_flags (oldFlags))) in
        tclLIFT (NonLogical.make (fun () -> CWarnings.set_flags ("-all"))) <*>
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
    let print_success (m, tcs) =
        let open NonLogical in
        let tstring = synthesize_tactic tcs in
        (make (fun () -> print_to_eval ("\t" ^ m ^ "\t" ^ tstring))) >>
        (print_info (Pp.str "Proof found!")) >>
        (make (fun () -> print_endline tstring)) in
    let print_name = NonLogical.make (fun () ->
        print_to_eval ("\n" ^ (Names.ModPath.to_string modpath ^ "." ^ Names.Id.to_string !current_name) ^ "\t" ^ string_of_int time)) in
    if !searched then Tacticals.New.tclZEROMSG (Pp.str "Already searched") else
      (searched := true;
       tclTIMEOUT2 time (tclLIFT (NonLogical.print_info (Pp.str "Proof search start")) <*>
                              tclLIFT print_name <*>
                              commonSearch () >>=
                              fun m -> tclLIFT (print_success m)) <*>
       Tacticals.New.tclZEROMSG (Pp.str "Proof benchmark search does not actually find proofs"))

let userPredict = Proofview.Goal.enter
    (fun gl ->
    let feat = goal_to_features gl in
    (* print_endline (String.concat " : " (List.map string_of_int feat)); *)
    (* Make predictions *)
    let r = Knn.knn !db_test feat in
    let r = List.map (fun (x, y, (z, q)) -> (x, (y, z, q))) r in
    let r = removeDups r in
    let r = List.map (fun (x, (y, z, q)) -> (x, z, q)) r in
    (* Print predictions *)
    (Proofview.tclLIFT (Proofview.NonLogical.print_info (print_rank r))))

let userSearch =
    let open Proofview in
    let open Notations in
    commonSearch () >>= (fun (tr, tcs) ->
        tclLIFT (NonLogical.print_info (
            Pp.str ("Tactician found a proof! The following tactic caches the proof:\n" ^ synthesize_tactic tcs))))

let ml_benchmarkSearch args is = benchmarkSearch ()

let () = register ml_benchmarkSearch "benchmarksearchtac"

let run_benchmarkSearch =
  TacML (CAst.make ({mltac_name = {mltac_plugin = "recording";
                                   mltac_tactic = "benchmarksearchtac"};
                     mltac_index = 0}, []))

(* Tactic recording tactic *)

let record_tac (tac : string) = Proofview.Goal.enter
    (fun gl ->
       (*let tac_str = Pp.string_of_ppcmds (Pptactic.pr_glob_tactic env tac) in*)
       if (String.equal tac "suggest" || String.equal tac "search") then Proofview.tclUNIT () else
         let feat = goal_to_features gl in

         (* Make predictions *)
         (*let r = Knn.knn db feat in
           let r = List.map (fun (x, y, (z, q)) -> (x, y, q)) r in
           let pp_str = Pp.int (get_k_str r tac) ++ (*(Pp.str " ") ++ (Pptactic.pr_raw_tactic tac) ++*) (Pp.str "\n") in
           append "count.txt" (Pp.string_of_ppcmds pp_str);*)

         (* Parse into raw tactic and store in db *)
         try
           let raw_tac = Pcoq.parse_string Pltac.tactic_eoi tac in
           add_to_db2 (feat, (raw_tac, tac));
           Proofview.tclUNIT ()
         with
         | Stream.Error txt -> append "parse_errors.txt" (txt ^ " : " ^ tac ^ "\n"); Proofview.tclUNIT ())

    (* Print predictions *)
    (*(Proofview.tclTHEN (Proofview.tclLIFT (Proofview.NonLogical.print_info (pp_str)))
                      (Proofview.tclLIFT (Proofview.NonLogical.print_info (print_rank r))))))*)

(*
let wit_ours : (raw_tactic_expr, glob_tactic_expr, glob_tactic_expr) genarg_type =
  make0 "ours"

let lift intern = (); fun ist x -> (ist, intern ist x)

let out_ty : glob_tactic_expr Geninterp.Val.typ = Geninterp.Val.create "leave_me_alone"

let lifts f = (); fun ist x -> Ftactic.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let (sigma, v) = f ist env sigma x in
  Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
  (Ftactic.return v)
end

let () =
  Genintern.register_intern0 wit_ours (lift Tacintern.intern_tactic_or_tacarg);
  Genintern.register_subst0 wit_ours Tacsubst.subst_tactic;
  register_interp0 wit_ours (lifts  (fun _ _ sigma gtac -> (sigma, gtac)));
  register_val0 wit_ours None

let my_ty : glob_tactic_expr Geninterp.Val.typ = Geninterp.Val.create "leave_me_alone"
let in_f c = Geninterp.Val.Dyn (my_ty, c)

let prj : Val.t -> glob_tactic_expr =
fun v -> let Val.Dyn (t', x) = v in
  match Val.eq my_ty t' with
  | None -> assert false
  | Some Refl -> x

let ml_record_tac args is =
  let t = prj (List.hd args) in record_tac t
*)

let record_tac tac_num = record_tac (find_tac tac_num)

let ml_record_tac args is =
  (*let num = Tacinterp.Value.cast (Genarg.topwit Tacarg.wit_tactic) (List.hd args) in*)
  let num = Tacinterp.Value.cast (Genarg.topwit Stdarg.wit_int) (List.hd args) in
  record_tac num

let () = register ml_record_tac "recordtac"

let rec format_oneline t =
  let open Pp in
  let d = repr t in
  let d' = match d with
  | Ppcmd_glue ls -> Ppcmd_glue (List.map format_oneline ls)
  | Ppcmd_force_newline -> Ppcmd_print_break (1, 0)
  | Ppcmd_box (bl, d') -> Ppcmd_box (bl, format_oneline d')
  | Ppcmd_tag (tag, d') -> Ppcmd_tag (tag, format_oneline d')
  | Ppcmd_comment _ -> assert false (* not expected *)
  | Ppcmd_string s -> if String.contains s '\n' then (print_endline s; assert false) (* can happen but is problematic *) else d
  | _ -> d in
  h 0 (unrepr d')

let run_record_tac env (tac : glob_tactic_expr) : glob_tactic_expr =
  (*let tac_glob = Tacintern.intern_pure_tactic*)
  let tac_pp = format_oneline (Pptactic.pr_glob_tactic env tac) in
  let tac_str = Pp.string_of_ppcmds tac_pp in
  if String.contains tac_str '\n' then print_endline ("Found!\n" ^ tac_str ^ "\n" ^ (Pp.db_string_of_pp tac_pp));
  let hash = add_hash_hash tac_str in
  let enc = Genarg.in_gen (Genarg.glbwit Stdarg.wit_int) hash in
  TacML (CAst.make ({mltac_name = {mltac_plugin = "recording"; mltac_tactic = "recordtac"}; mltac_index = 0},
                [TacGeneric enc]))

let record_tac_complete env tac : glob_tactic_expr =
  let record_tmp = TacThen (run_record_tac env tac, tac) in
  match !benchmarking with
  | None -> record_tmp
  | Some _ -> TacOr (run_benchmarkSearch, record_tmp)

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
    if !featureprinting then print_to_feat ("#lemma " ^ (Names.Id.to_string new_name) ^ "\n");

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
    List.iter (fun (fl, obj) -> add_to_db (fl, obj))
      (Knn.tolist (Hashtbl.find int64_to_knn id));
    Hashtbl.remove int64_to_knn id;
    true
  ) else (
    Hashtbl.add int64_to_knn id (Knn.create ());
    false
  )

let hide_interp_t global t ot transform =
  let open Proofview.Notations in
  let hide_interp env =
    let ist = Genintern.empty_glob_sign env in
    let te = Tacintern.intern_pure_tactic ist t in
    let te = transform env te in
    let t = Tacinterp.eval_tactic te in
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

let recorder env tac :  glob_tactic_expr =
  (*let extern_ref ?loc vars r =
      try CAst.make ?loc @@ Libnames.Qualid (qualid_of_global env r)
      with Not_found -> print_endline "error"; CAst.make (Libnames.Qualid (Libnames.qualid_of_string "blupblupblup")) in
  Constrextern.set_extern_reference extern_ref;*)
  (*let tac = Globalize.globalize_glob_tactic_expr tac in*)
  (*print_endline (Pp.string_of_ppcmds (Pptactic.pr_glob_tactic env tac));*)
  let record_tac_complete tac = record_tac_complete env tac in
  let rec annotate tcom : glob_tactic_expr =
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
  annotate tac
