(* The purpose of this module is load recursively the transitive
   dynamical ocaml plugin dependencies (Dynload *.cmxs objects) before
   upstream Coq implements properly recursive loading of ocaml plugin
   dependencies.

   This tool takes three arguments: ARG1 ARG2 ARG3

   ARG1 is the filename of input dune file to process and extract libraries depenencies
   included one per line between the start_watermark and finish_watermark regexp

   ARG2 is the filename of the ouput .v file

   ARG3 is the filename of the output injection-flags file

 *)


(* CONFIG SECTION *)

let start_watermark = Str.regexp ".*;__dep_extract_start__.*"
let finish_watermark = Str.regexp ".*;__dep_extract_finish__.*"

(* list of hardlinked libraries to coq *)
let core_linked = ["unix"; "str"] 

(* list of package with bugs in META:  https://github.com/ocaml/Zarith/issues/102 *)
let bad_meta_pkg_list = ["zarith"]   
let bad_meta_sub_map = [ ("zarith.cmxa", "zarith") ] (* replacement map for bad cases *)

(* list of META package predicates we search for *)
let preds = ["native"; "ppx_driver"; "mt"; "mt_posix"]

(* DEBUG CONFIG SECTION *)
(* switch off debug when we know this works *)

let debug_msg = Printf.eprintf "%s\n" 

(* CODE SECTION *)

let strip_cmxs s =
  let open String in
  let n = length s in if n >=5 && sub s (n - 5) 5  = ".cmxs" then  sub s 0 (n - 5)
                      else raise (Invalid_argument ("Error: library filename " ^ s ^ " does not end in *.cmxs"))


let strip_ext s =
  match List.find_opt (fun (k,v)  -> k = s) bad_meta_sub_map with
  | Some (k,v) -> v
  | None ->  strip_cmxs s

let quote s = "\"" ^ s ^ "\""

let write_loader_line dir filename =
  "Add ML Path " ^ (quote dir) ^ ". Declare ML Module " ^ (quote filename) ^ ".\n"

let write_injection_flag_line dir =
  "-I " ^ dir ^ " "


let print_two_streams out1 out2 dir filename = (
    debug_msg ("Recording object: " ^ dir ^ "/" ^ filename);
    Printf.fprintf out1 "%s" (write_loader_line dir (strip_ext filename));
    Printf.fprintf out2 "%s" (write_injection_flag_line dir);
  )

let in_words s = Str.split (Str.regexp "[ \t\n\r,]+") s (* https://github.com/ocaml/ocamlfind/src/findlib/fl_split.ml#L7 *)

let load_pkg printer pkg =
  if not (Findlib.is_recorded_package pkg) then (
     let dir = Findlib.package_directory pkg in
     let preds = Findlib.recorded_predicates() in
     let archive =
       try
         Findlib.package_property preds pkg "plugin"
       with
         | Not_found ->
              try
                let v, fpreds =
                  Findlib.package_property_2 ("plugin"::preds) pkg "archive" in
                let need_plugin =
                  List.mem "native" preds in
                if need_plugin
                   && not (List.mem (`Pred "plugin") fpreds)
                   && not (List.mem pkg bad_meta_pkg_list) then   (debug_msg @@ "Skipping object: " ^ v; "")
                else v
              with Not_found -> "" in
     let files = in_words archive in
     List.iter (printer dir) files;
     Findlib.record_package Findlib.Record_load pkg
  )


let extract_dune dune_filename =
  let shared = ref false in
  let dune_ch = open_in dune_filename in
  let res = ref [] in
  try
    while true do
      let line = input_line dune_ch in
      if !shared then
        if Str.string_match finish_watermark line 0 then
          shared := false
        else
          let trimmed_line = String.trim line in
          debug_msg ("Extracted dependency: " ^ trimmed_line);
          res := trimmed_line :: !res
      else
        if Str.string_match start_watermark line 0 then
          shared := true
    done; !res
  with End_of_file ->
    close_in dune_ch; !res

(* MAIN PROCESS *) 

let () =
  if (Array.length Sys.argv) != 4 then (
    debug_msg "usage: ocaml plugin_deps_generate_conf.ml dune \
               TacticianApiDepLoader.v injection-flags ";
    exit 1)
  else (
    (* get libraries from dune, using watermark cut *)
    let pkgs = extract_dune Sys.argv.(1) in

    Findlib.init ();
    debug_msg "Using findlib search path:";
    List.iter (debug_msg) (Findlib.search_path ());

    (* record coq-core-linked packages *)
    List.iter (Findlib.record_package Findlib.Record_core) core_linked;

    (* resolve dependencies *)
    let resolved_pkgs = Findlib.package_deep_ancestors preds pkgs in
    Findlib.record_package_predicates preds;

    (* record result *)
    let out1 = open_out Sys.argv.(2) in
    let out2 = open_out Sys.argv.(3) in
    List.iter (load_pkg (print_two_streams out1 out2)) resolved_pkgs;
    close_out out1;
    close_out out2;
  )
