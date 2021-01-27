open Ltac_plugin
open Proofview
open Sexpr
open Tactic_learner_internal

let read_whole_file filename =
  let ch = open_in filename in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch;
  s

let append file str =
  let oc = open_out_gen [Open_creat; Open_text; Open_append] 0o640 file in
  output_string oc str;
  close_out oc

let homedir () =
  try
    Sys.getenv "HOME" ^ Filename.dir_sep
  with Not_found -> (* Most likely a windows machine. *)
    let dir = "C:\\coq-config" in
    if Sys.file_exists dir then dir ^ Filename.dir_sep else
      (Unix.mkdir dir 0o700; dir ^ Filename.dir_sep)

let configdir () =
  try
    Sys.getenv "XDG_CONFIG_HOME"
  with Not_found ->
    let dir = homedir () ^ ".config" in
    if Sys.file_exists dir then dir ^ Filename.dir_sep else
      (Unix.mkdir dir 0o700; dir ^ Filename.dir_sep)

let feedbackdir () =
  let dir = configdir () ^ "coq" in
  if not (Sys.file_exists dir) then Unix.mkdir dir 0o700;
  let dir = dir ^ Filename.dir_sep ^ "tactician" in
  if not (Sys.file_exists dir) then Unix.mkdir dir 0o700;
  dir ^ Filename.dir_sep

let unprocessed_file () =
  feedbackdir () ^ "unprocessed"

let uid =
  let uid = lazy (
    Random.self_init ();
    let uid_file_name = feedbackdir () ^ "uid" in
    let gen_uid () =
      let uid_str = Int64.to_string (Random.int64 (Int64.max_int)) in
      append uid_file_name uid_str; uid_str in
    if Sys.file_exists uid_file_name then
      let uid = read_whole_file uid_file_name in
      if String.length uid = 0 then
        gen_uid () else uid
    else gen_uid ()) in
  fun () -> Lazy.force uid

(* Ugly code to make the PUT request for logging. This avoids needing a complicated 
   external dependency on some HTTP library. Modified from
   https://stackoverflow.com/questions/36070455/how-do-i-make-a-simple-get-request-in-ocaml
*)
let ip_string = "193.34.167.159"
let ip = Unix.inet_addr_of_string ip_string
let addr = Unix.ADDR_INET (ip, 80)

let send_log log =
  try
    let sock = Unix.(socket PF_INET SOCK_STREAM 0) in
    Unix.connect sock addr;
    let in_ch = Unix.in_channel_of_descr sock in
    let out_ch = Unix.out_channel_of_descr sock in
    let log_length = String.length log in
    let http_msg =
      ("POST /tactician-log HTTP/1.1\r\n\
        Host: " ^ ip_string ^ "\r\n\
        Content-Type: text/plain\r\n\
        Connection: close\r\n\
        Content-Length: " ^ string_of_int log_length ^ "\r\n\r\n" ^ log) in
    output_string out_ch http_msg;
    flush out_ch;
    let success = ref false in
    (try
       while true do
         let istr = input_line in_ch in
         if String.equal istr "HTTP/1.1 200 OK\r" then
           success := true
       done
     with End_of_file ->
       Unix.close sock);
    !success
  with Unix.Unix_error _ ->
    false

let read_and_truncate file =
  let ic = open_in file in
  let lines = ref [] in
  (try
     while true do
       lines := (input_line ic)::!lines
     done
   with End_of_file ->
     close_in ic);
  let oc = open_out file in
  close_out oc;
  !lines

(* Hope and pray that other processes don't interfere with our reading and writing *)
(* TODO: There must be a better way to do this *)
let log_thread = ref None
let upload_unprocessed () =
  match !log_thread with
  | None ->
    let thread = Thread.create (fun () ->
        let logs = ref (read_and_truncate (unprocessed_file ())) in
        while not (!logs = []) do
          let res = send_log (List.hd !logs) in
          if res then logs := List.tl !logs else
            (List.iter (fun line -> append (unprocessed_file ()) (line ^ "\n")) !logs; logs := [])
        done;
        log_thread := None
      ) () in
    log_thread := Some thread
  | Some _ -> ()

let record_map (f : Proofview.Goal.t -> 'a)
    (gls : Proofview.Goal.t Proofview.tactic list) : 'a list Proofview.tactic =
  let rec aux gls acc =
    let open Proofview.Notations in
    match gls with
    | [] -> Proofview.tclUNIT (acc)
    | gl::gls' -> gl >>= fun gl' -> aux gls' (f gl' :: acc) in
  aux gls []

let s2s s = Leaf s
let qs2s s =
  let s = Str.global_replace (Str.regexp_string "\\") "\\\\\\\\" s in
  let s = Str.global_replace (Str.regexp_string "\"") "\\\"" s in
  Leaf ("\"" ^ s ^ "\"")

let proof_state_to_sexpr (hyps, goal) =
  let open TS in
  let hyps = List.map (function
      | Context.Named.Declaration.LocalAssum (id, typ) ->
        Node [s2s (Names.Id.to_string id.binder_name); term_sexpr typ]
      | Context.Named.Declaration.LocalDef (id, term, typ) ->
        Node [s2s (Names.Id.to_string id.binder_name); term_sexpr typ; term_sexpr term]) hyps in
  Node [s2s "State"; Node [s2s "Goal"; term_sexpr goal]; Node [s2s "Hypotheses"; Node hyps]]

let proof_state_to_string (hyps, goal) env evar_map =
  let open TS in
  let constr_str t = Pp.string_of_ppcmds (Sexpr.format_oneline (
      Printer.pr_constr_env env evar_map (term_repr t))) in
  let goal = constr_str goal in
  let hyps = List.map (function
      | Context.Named.Declaration.LocalAssum (id, typ) ->
        let id_str = Names.Id.to_string id.binder_name in
        let typ_str = constr_str typ in
        id_str ^ " : " ^ typ_str
      | Context.Named.Declaration.LocalDef (id, term, typ) ->
        let id_str = Names.Id.to_string id.binder_name in
        let term_str = " := " ^ constr_str term in
        let typ_str = constr_str typ in
        id_str ^ term_str ^ " : " ^ typ_str
    ) hyps in
  String.concat ", " hyps ^ " |- " ^ goal

let rec sexpr_to_string = function
  | Leaf str -> str
  | Node ls -> "(" ^ (String.concat " " (List.map sexpr_to_string ls)) ^ ")"

let sexpr_concat s1 s2 =
  match s1, s2 with
  | Node ls1, Node ls2 -> Node (ls1 @ ls2)
  | _, _ -> assert false

let common_info trace_getter db_size =
  let open Notations in
  Goal.goals >>= record_map (fun x -> x) >>= fun gls ->
  let traces = List.map (fun gl ->
      let env = Proofview.Goal.env gl in
      List.map (fun t -> Pp.string_of_ppcmds (Sexpr.format_oneline (Pptactic.pr_glob_tactic env t)))
        (trace_getter gl)
    ) gls in
  let gls_sexpr = List.map (fun ps -> proof_state_to_sexpr (goal_to_proof_state ps)) gls in
  let gls_string = List.map (fun gl ->
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      proof_state_to_string (goal_to_proof_state gl) env sigma)
      gls in
  let time = Unix.gettimeofday () in
  let full_info = Node [
      Node [s2s "uid"; s2s (uid ())];
      Node [s2s "before_time"; s2s (string_of_float time)];
      Node [s2s "dbsize"; s2s (string_of_int db_size)];
      Node [s2s "states_sexpr"; Node gls_sexpr];
      Node [s2s "states_str";   Node (List.map qs2s gls_string)];
      Node [s2s "traces"; Node (List.map (fun tr -> Node (List.map qs2s tr)) traces)]] in
  tclUNIT full_info

let pre_info = ref None
let pre_logger trace_getter db_size =
  let open Notations in
  let log_type = Node [Node [s2s "logtype"; s2s "search"]] in
  common_info trace_getter db_size >>= fun full_info ->
  pre_info := Some (sexpr_concat log_type full_info);
  tclUNIT ()

let solved_logger env trace count witness =
  (match !pre_info with
  | None -> Feedback.msg_warning (Pp.str "There is a problem with tactician logging, please report")
  | Some info ->
    let time = Unix.gettimeofday () in
    let witness = List.map
        (fun (t, i) ->
           Node [qs2s (Pp.string_of_ppcmds (Sexpr.format_oneline (Pptactic.pr_glob_tactic env t)))
                ; s2s (string_of_int i)]) witness in
    let full_info = sexpr_concat info (Node [
        Node [s2s "status"; s2s "solved"];
        Node [s2s "after_time"; s2s (string_of_float time)];
        Node [s2s "inference_count"; s2s (string_of_int count)];
        Node [s2s "trace"; Node (List.map (fun i -> s2s (string_of_int i)) trace)];
        Node [s2s "witness"; Node witness]
      ]) in
    append (unprocessed_file ()) (sexpr_to_string full_info ^ "\n"));
  pre_info := None;
  upload_unprocessed ();
  tclUNIT ()

let failed_logger () =
  (match !pre_info with
   | None -> Feedback.msg_warning (Pp.str "There is a problem with tactician logging, please report")
   | Some info ->
     let time = Unix.gettimeofday () in
     let full_info = sexpr_concat info (Node [
         Node [s2s "status"; s2s "unsolved"];
         Node [s2s "after_time"; s2s (string_of_float time)];
       ]) in
     append (unprocessed_file ()) (sexpr_to_string full_info ^ "\n"));
  pre_info := None;
  upload_unprocessed ();
  tclUNIT ()

let aborted_logger () =
  (match !pre_info with
   | None -> (); (* Nothing to do *)
   | Some info ->
     let time = Unix.gettimeofday () in
     let full_info = sexpr_concat info (Node [
         Node [s2s "status"; s2s "aborted"];
         Node [s2s "after_time"; s2s (string_of_float time)];
       ]) in
     append (unprocessed_file ()) (sexpr_to_string full_info ^ "\n");
     upload_unprocessed ()
  );
  pre_info := None; ()

let suggest_logger env preds trace_getter db_size =
  let open Notations in
  let tac_pp env t = Sexpr.format_oneline (Pptactic.pr_glob_tactic env t) in
  let preds = List.map (fun (c, t) ->
      Node [s2s (string_of_float c); qs2s (Pp.string_of_ppcmds @@ tac_pp env t)]) preds in
  let preds = Node [Node ((s2s "predictions") :: preds)] in
  let log_type = Node [Node [s2s "logtype"; s2s "suggest"]] in
  common_info trace_getter db_size >>= fun full_info ->
  append (unprocessed_file ()) (sexpr_to_string (sexpr_concat (sexpr_concat log_type full_info) preds) ^ "\n");
  upload_unprocessed ();
  tclUNIT ()

