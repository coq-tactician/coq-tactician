(* These datastructures have to be kept in sync with the bencher *)
type pre_bench_info =
  { exec   : string
  ; args   : string array
  ; env    : string array
  ; dir    : string
  ; lemmas : string list }

let declare_option name d =
  let var = ref d in
  Goptions.declare_int_option Goptions.{
      optdepr = false;
      optname = String.concat " " name;
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
    let info = Marshal.to_bytes info [] in
    let s = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
    Unix.connect s @@ Unix.ADDR_INET (Unix.inet_addr_loopback, p);
    let c = Unix.out_channel_of_descr s in
    output_bytes c info;
    close_out c

let () = Declaremods.append_end_library_hook write_info
