(* These datastructures have to be kept in sync with the bencher *)
type pre_bench_info =
  { exec   : string
  ; args   : string array
  ; env    : string array
  ; dir    : string
  ; lemmas : string list
  ; time   : float }

type bench_result =
  | Should of string
  | Found of
      { lemma : string
      ; trace : int list
      ; time : float
      ; witness : string
      ; inferences : int }

type bench_response =
  | Skip
  | Bench of int

let declare_option name d =
  let var = ref d in
  Goptions.declare_int_option Goptions.{
      optdepr = false;
      optkey = name;
      optread = (fun () -> !var);
      optwrite = (fun v -> var := v)
    };
  var

let port = declare_option ["Tactician"; "Prebench"; "Port"] None

let info =
  { exec = Sys.executable_name
  ; args = Array.copy Sys.argv
  ; env = Unix.environment ()
  ; dir = Sys.getcwd ()
  ; lemmas = []
  ; time = Unix.gettimeofday () }

let lemmas = ref Libnames.Spmap.empty

let add_lemma l =
  lemmas := Libnames.Spmap.add l () !lemmas

let write_info () =
  match !port with
  | None -> ()
  | Some p ->
    let info = { info with
                 lemmas = List.map Libnames.string_of_path @@ List.map fst @@ Libnames.Spmap.bindings !lemmas
               ; time = Unix.gettimeofday () -. info.time } in
    let s = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
    Unix.connect s @@ Unix.ADDR_INET (Unix.inet_addr_loopback, p);
    let c = Unix.out_channel_of_descr s in
    Marshal.to_channel c info [];
    flush c;
    (* We intentionally keep the socket open. It is closed when the process exits. This way, the receiving process can know when
       all .vo files have been written. *)
    (* close_out c *) ()

let () = Declaremods.append_end_library_hook write_info

let benchmarking = ref None
let deterministic = ref false

let benchoptions =
  Goptions.{ optdepr = false
           ; optkey = ["Tactician"; "Benchmark"]
           ; optread = (fun () -> Option.cata (fun _ -> true) false !benchmarking)
           ; optwrite = (fun b ->
                match !benchmarking with
                | Some _ -> ()
                | None ->
                  match b with
                  | true ->
                    (match Tactician_util.base_filename with
                     | None -> CErrors.user_err Pp.(str "No source file could be found. No Benchmarking possible.")
                     | Some _ ->
                       let ic = Unix.in_channel_of_descr Unix.stdin in
                       let oc = Unix.out_channel_of_descr Unix.stdin in
                       benchmarking := Some (ic, oc);
                       Tactic_learner_internal.disable_queue ())
                  | false -> ())}

let deterministicoptions =
  Goptions.{optdepr = false;
            optkey = ["Tactician"; "Benchmark"; "Deterministic"];
            optread = (fun () -> !deterministic);
            optwrite = (fun b -> deterministic := b)}

let () = Goptions.declare_bool_option benchoptions
let () = Goptions.declare_bool_option deterministicoptions

let should_benchmark name =
  match !benchmarking with
  | Some (ic, oc) ->
    Marshal.to_channel oc (Should (Libnames.string_of_path name)) [];
    flush oc;
    let resp : bench_response = Marshal.from_channel ic in
    (match resp with
     | Skip -> None
     | Bench time ->
       Some (time, !deterministic))
  | None -> None

let send_bench_result (res : bench_result) =
  match !benchmarking with
  | None -> CErrors.anomaly Pp.(str "Should be benchmarking")
  | Some (_, oc) ->
    Marshal.to_channel oc res [];
    flush oc
