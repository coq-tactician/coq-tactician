open Printf

let usage () = print_endline "\
This is a utility for Tactician that will help you configure it correctly.
Options:

- To enable Tactician, run
  tactician enable

- To disable Tactician, run
  tactician disable

- To inject tactician into the installation or build of Coq packages, run
  eval $(tactician inject)

- After you have installed or removed the package coq-tactician-stdlib run the
  following command to help you with recompilation of other packages:
  tactician recompile
"

let coqrc_string = "From Tactician Require Import Ltac1.\n"

let syscall cmd =
  let ic, oc = Unix.open_process cmd in
  let buf = Buffer.create 16 in
  (try
     while true do
       Buffer.add_channel buf ic 1
     done
   with End_of_file -> ());
  let _ = Unix.close_process (ic, oc) in
  (Buffer.contents buf)

let rec question str =
  printf "%s [y/n]\n" str;
  let answer = read_line () in
  match answer with
  | "y" -> true
  | "n" -> false
  | _ -> print_endline "No valid answer"; question str

(* Taken from coq envars.ml *)
let getenv_else s dft = try Sys.getenv s with Not_found -> dft ()
let home ~warn =
  getenv_else "HOME" (fun () ->
      try (Sys.getenv "HOMEDRIVE") ^ (Sys.getenv "HOMEPATH") with Not_found ->
        getenv_else "USERPROFILE" (fun () ->
            warn ("Cannot determine user home directory, using '.' .");
            Filename.current_dir_name))
let homedir () =
  home ~warn:print_endline ^ Filename.dir_sep

let configdir () =
  try
    Sys.getenv "XDG_CONFIG_HOME"
  with Not_found -> homedir () ^ ".config" ^ Filename.dir_sep

let find_exists files =
  let exists = List.map Sys.file_exists files in
  let exists_text = List.map (fun b -> if b then "exists" else "does not exist") exists in
  List.iter2 (fun f e -> printf "File %s %s\n" f e) files exists_text;
  let combined = List.map2 (fun a b -> (a, b)) files exists in
  let coqrcs = List.filter (fun (f, e) -> e) combined in
  List.map fst coqrcs

let find_coqrc_files () =
  let homedir = homedir () in
  let configdir = configdir () in
  let coqbin =
    try
      Sys.getenv "COQBIN" ^ Filename.dir_sep
    with Not_found -> "" in
  let coqversion =
    let tmp = syscall (coqbin ^ "coqc -print-version") in
    List.hd (String.split_on_char ' ' tmp) in
  printf "\nYour coq version is %s\n" coqversion;
  let files = [configdir ^ "coq/coqrc." ^ coqversion
              ; homedir ^ ".coqrc." ^ coqversion
              ; homedir ^ ".coqrc" ] in
  find_exists files

let check_file f str =
  let rec aux chan =
    try
      let line = input_line chan in
      if String.equal (String.trim line) (String.trim str) then true else aux chan
    with End_of_file -> false in
  let chan = open_in f in
  let ans = aux chan in
  close_in chan;
  ans

let check_coqrc_file f = check_file f coqrc_string

let append file str =
  let oc = open_out_gen [Open_creat; Open_text; Open_append] 0o640 file in
  output_string oc str;
  close_out oc

let install_rcfile () =
  let string1 = "\
In order to load Tactician, the following snippet needs to be in your coqrc file:

From Tactician Require Import Ltac1.

We strongly recommend that you do not include this snippet directly in your developments,
as this would create issues with the build reproducibility of your project. If you are
creating a package of your development, it should instead depend on the dummy version of
Tactician, coq-tactician-dummy. You can load the dummy tactics through

From Tactician Require Import Ltac1Dummy.

During development, you can still use Tactician as normal.
" in
  print_endline string1;
  match find_coqrc_files () with
  | [] ->
    let ans = question "\nNo coqrc file appears to exist on your system.\n\
                        Would you like us to create and populate the file ~/.coqrc?" in
    if ans then (
      append (homedir () ^ ".coqrc")  coqrc_string;
      print_endline "File created!"
    )
  | f::_ ->
    let already_installed = check_coqrc_file f in
    if already_installed then
      print_endline ("\nIt appears that your coqrc file " ^ f ^ " already properly loads Tactician")
    else
      let ans = question ("\nWould you like tactician to modify the coqrc file " ^ f ^ " for you?") in
      if ans then (
        append f coqrc_string;
        print_endline "File patched!"
      )

let write f lines =
  let rec aux chan lines =
    match lines with
    | [] -> close_out chan
    | l::lines' -> fprintf chan "%s\n" l; aux chan lines' in
  let chan = open_out f in
  aux chan lines

let remove_from_file f str =
  let rec aux chan acc =
    try
      let line = input_line chan in
      if String.equal (String.trim line) (String.trim str) then aux chan acc else aux chan (line::acc)
    with End_of_file -> write f acc in
  let chan = open_in f in
  aux chan [];
  close_in chan

let remove_rcfile () =
  let string1 = "\
In order to disable Tactician, the following snippet needs to be removed from your coqrc files:

From Tactician Require Import Ltac1.
" in
  print_endline string1;
  let ans = question "Would you like to proceed?" in
  if ans then (
    let coqrcs = find_coqrc_files () in
    List.iter (fun f -> remove_from_file f coqrc_string) coqrcs;
    print_endline "Files patched!"
  )

let inject () =
  print_endline "COQEXTRAFLAGS='-rifrom Tactician Ltac1.Record'; export COQEXTRAFLAGS;"

let string_in str ls =
  let filtered = List.filter (fun s -> String.equal s str) ls in
  match filtered with
  | [] -> false
  | _ -> true

let stdlib () =
  let installed = not (String.equal "" (String.trim (syscall "opam list -i coq-tactician-stdlib --short"))) in
  if not installed then (
    print_endline "This utility helps you recompile packages if you have just installed or removed";
    print_endline "the package coq-tactician-stdlib. Otherwise, you do not have to run this command"
  )
  else (
    print_endline "If you just installed coq-tactician-stdlib, you should recompile all Coq packages.";
    let packages = String.split_on_char '\n' (String.trim (syscall ("opam list -i --depends-on coq --short"))) in
    let blacklist = ["coqide"; "coq-tactician"; "coq-tactician-dummy"; "coq-tactician-stdlib" ] in
    let packages = List.filter (fun p -> not (string_in p blacklist)) packages in
    if packages == [] then
      print_endline "However, it appears that you do not have any packages installed. No actions are needed."
    else (
      print_endline "The following relevant Coq packages are installed:";
      print_endline (String.concat " " packages);
      let ans = question "Would you like to reinstall them?" in
      if ans then
        ignore (Sys.command ("opam reinstall " ^ (String.concat " " packages)))
    )
  )

let () =
  let args = Sys.argv in
  if Array.length args == 1 then
    usage ()
  else if Array.length args > 2 then (
    printf "Error: Only one argument is expected\n\n";
    usage ()
  )
  else (
    let arg = Sys.argv.(1) in
    match arg with
    | "inject" -> inject ()
    | "enable" -> install_rcfile ()
    | "disable" -> remove_rcfile ()
    | "recompile" -> stdlib ()
    | "--help" | "-h" | "help" -> usage ()
    | _ -> printf "Error: Unknown subcommand '%s'\n\n" arg; usage ()
  );
