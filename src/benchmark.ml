(* These datastructures have to be kept in sync with the bencher *)
type pre_bench_info =
  { exec   : string
  ; args   : string array
  ; env    : string array
  ; dir    : string
  ; lemmas : string list }

type bench_request =
  { lemmas : string list }

type bench_result =
  | Started of string
  | Found of
      { lemma : string
      ; trace : int list
      ; time : float
      ; witness : string
      ; inferences : int }

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
  ; lemmas = [] }

let lemmas = ref Libnames.Spmap.empty

let add_lemma l =
  lemmas := Libnames.Spmap.add l () !lemmas

let write_info () =
  match !port with
  | None -> ()
  | Some p ->
    let info = { info with lemmas = List.map Libnames.string_of_path @@ List.map fst @@ Libnames.Spmap.bindings !lemmas } in
    let s = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
    Unix.connect s @@ Unix.ADDR_INET (Unix.inet_addr_loopback, p);
    let c = Unix.out_channel_of_descr s in
    Marshal.to_channel c info [];
    (* We intentionally keep the socket open. It is closed when the process exits. This way, the receiving process can know when
       all .vo files have been written. *)
    (* close_out c *) ()

let () = Declaremods.append_end_library_hook write_info

let benchmarking = ref None
let featureprinting = ref false
let deterministic = ref false

let benchoptions =
  Goptions.{optdepr = false;
            optkey = ["Tactician"; "Benchmark"];
            optread = (fun () ->
                match !benchmarking with
                | None -> None
                | Some (time, _, _) -> Some time);
            optwrite = (fun b ->
                match !benchmarking with
                | Some _ -> ()
                | None ->
                  match b with
                  | Some time -> (match Tactician_util.base_filename with
                      | None -> CErrors.user_err Pp.(str "No source file could be found. No Benchmarking possible.")
                      | Some _ ->
                        let ic = Unix.in_channel_of_descr Unix.stdin in
                        let { lemmas } : bench_request = Marshal.from_channel ic in
                        let lemmas = List.map Libnames.path_of_string lemmas in
                        let oc = Unix.out_channel_of_descr Unix.stdin in
                        benchmarking := Some (time, lemmas, oc);
                        Tactic_learner_internal.disable_queue ())
                  | _ -> ())}

let deterministicoptions =
  Goptions.{optdepr = false;
            optkey = ["Tactician"; "Benchmark"; "Deterministic"];
            optread = (fun () -> !deterministic);
            optwrite = (fun b -> deterministic := b)}

let () = Goptions.declare_int_option benchoptions
let () = Goptions.declare_bool_option deterministicoptions

let should_benchmark name =
  match !benchmarking with
  | Some (time, lemmas, _) when List.exists (Libnames.eq_full_path name) lemmas ->
    Some (time, !deterministic)
  | _ -> None

let send_bench_result (res : bench_result) =
  match !benchmarking with
  | None -> CErrors.anomaly Pp.(str "Should be benchmarking")
  | Some (_, _, oc) ->
    Marshal.to_channel oc res [];
    flush oc
