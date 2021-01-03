open Printf
open OpamConfigCommand
open Cmdliner

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
  let coqrcs = List.filter (fun (_, e) -> e) combined in
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
  printf "Your coq version is %s\n" coqversion;
  let files = [configdir ^ "coq" ^ Filename.dir_sep ^ "coqrc." ^ coqversion
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
  let success = "\nFile patched! Run 'tactician disable' to reverse this command" in
  (match find_coqrc_files () with
  | [] ->
    let ans = OpamConsole.confirm
        ("\nNo coqrc file appears to exist on your system. Would you like to create and \
          populate the file ~/.coqrc for Tactician support?") in
    if ans then (
      append (homedir () ^ ".coqrc")  coqrc_string;
      print_endline success
    )
  | f::_ ->
    let already_installed = check_coqrc_file f in
    if already_installed then
      print_endline
        ("\nIt appears that the coqrc file " ^ f ^ " already properly loads Tactician")
    else
      let ans = OpamConsole.confirm
          "\nWould you like to modify the coqrc file %s for Tactician support?" f in
      if ans then (
        append f coqrc_string;
        print_endline success
      )); `Ok ()

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
  let ans = OpamConsole.confirm "Would you like to rmove Tactician support from your coqrc files?" in
  if ans then (
    let coqrcs = find_coqrc_files () in
    List.iter (fun f -> remove_from_file f coqrc_string) coqrcs;
    print_endline "\nFile patched! Run 'tactician enable' to reverse this command"
  ); `Ok ()

let string_in str ls =
  let filtered = List.filter (fun s -> String.equal s str) ls in
  match filtered with
  | [] -> false
  | _ -> true

let recompile_packages no_pkgs_msg pkgs_msg confirm_msg =
  let packages = String.split_on_char '\n' (String.trim (syscall ("opam list -i --depends-on coq --short"))) in
  let blacklist = ["coqide"; "coq-tactician"; "coq-tactician-dummy"; "coq-tactician-stdlib" ] in
  let packages = List.filter (fun p -> not (string_in p blacklist)) packages in
  if packages == [] then
    print_endline no_pkgs_msg
  else (
    print_endline pkgs_msg;
    print_endline (String.concat " " packages);
    let ans = OpamConsole.confirm confirm_msg in
    if ans then
      ignore (Sys.command ("opam reinstall " ^ (String.concat " " packages)))
  )

let opam_init_no_lock f =
  OpamClientConfig.opam_init ();
  OpamGlobalState.with_ `Lock_none f

let config_add_remove gt ?st name value =
  let st = set_opt_switch gt ?st name (`Remove value) in
  set_opt_switch gt ?st name (`Add value)

let wrap_command = "[\"with-tactician\"] {coq-tactician:installed}"
let pre_build_command = "[\"tactician-patch\" name version] {coq-tactician:installed}"

let inject () =
  opam_init_no_lock @@ fun gt ->
  let st = config_add_remove gt "wrap-build-commands" wrap_command in
  let _ = config_add_remove gt ?st "pre-build-commands" pre_build_command in
  print_endline "\nTactician will now instrument Coq packages installed through opam.";
  print_endline "Run tactician eject to reverse this command.";
  recompile_packages ""
    "\nThe following Coq packages are installed on your system:"
    "Would you like to recompile them with the new settings?";
  `Ok ()

let eject () =
  OpamClientConfig.opam_init ();
  OpamGlobalState.with_ `Lock_none @@ fun gt ->
  let st = set_opt_switch gt "wrap-build-commands" (`Remove wrap_command) in
  let _ = set_opt_switch gt ?st "pre-build-commands" (`Remove pre_build_command) in
  print_endline "\nTactician will no longer instrument packages installed through opam.";
  print_endline "Run tactician inject to re-inject.";
  recompile_packages ""
    "\nThe following Coq packages are installed on your system:"
    "Would you like to recompile them with the new settings?";
  `Ok ()

let stdlib () =
  (* let installed = not (String.equal "" (String.trim (syscall "opam list -i coq-tactician-stdlib --short"))) in
   * if not installed then (
   *   print_endline
   *     "This utility helps you recompile packages if you have just installed or removed \
   *      the package coq-tactician-stdlib. Otherwise, you do not have to run this command"
   * )
   * else ( *)
  print_endline "This utility helps you recompile all your Coq packages. \
                 You only need to do this when:\n\n\
                 (1) You have injected/ejected Tactician and want to recompile \
                 all packages with/without Tactician support.\n\
                 (2) You have installed/removed the package `coq-tactician-stdlib`.\n";
  recompile_packages "It appears that you do not have any packages installed. No actions are needed."
    "The following relevant Coq packages are installed:"
    "Would you like to reinstall them?";
  `Ok ()

let exec_command cmd args =
  (* TODO: Use internal opam API to retrieve this *)
  let lib = String.trim @@ syscall ("opam var coq-tactician:lib") in
  let wt = Filename.concat lib "with-tactician" in
  Unix.execv wt (Array.of_list (wt::cmd::args))

(* Command line interface *)

let enable =
  let doc = "Modify your coqrc file to load Tactician when Coq is started." in
  let man =
    [ `P "Tactician can be activated in a Coq source file, with the following load command."
    ; `P coqrc_string
    ; `P "However, it is not recommended to add this snippet in your developments. Instead, this utility \
         will add it to your 'coqrc' file, which gets executed every time Coq is started. The reason for \
         this is that you might not want Tactician as an explicit dependency of your developments pakcage. \
         This would result in reproducibility issues when people install your package (and they would have \
         to install Tactician them self). Instead, your package should rely on a dummy version of Tactician \
         in found in the plugin coq-tactician-dummy. This package contains shims for all of Tacticians \
         tactics that do nothing except for 'search with cache ..', which simply executes the cached tactic. \
         This way, you can use the real Tactician while developing without needing a dependency on it."
    ] in
  Term.(ret (const install_rcfile $ const ())),
  Term.info "enable" ~doc ~man

let disable =
  let doc = "Remove the script that loads Tactician on Coq startup from your coqrc files." in
  let man =
    [ `P "This utility removes the following snippet from your 'coqrc' files, thereby disabling Tactician."
    ; `P coqrc_string
    ] in
  Term.(ret (const remove_rcfile $ const ())),
  Term.info "disable" ~doc ~man

let inject =
  let doc = "Add hooks to Opam that allow Tactician to instrument the installation of Coq packages \
             for learning purposes." in
  let man =
    [ `P "This utility modifies Opam's configuration file with hooks that add Tactician support during \
         installation of Coq packages. This command can be reversed by running 'tactician eject'."
    ] in
  Term.(ret (const inject $ (const ()))),
  Term.info "inject" ~doc ~man

let eject =
  let doc = "Remove hooks to Opam that allow Tactician to instrument the installation of Coq packages \
             for learning purposes." in
  let man = [ `P "This utility modifies Opam's configuration file to remove hooks that have been added by \
                  'tactician inject'. After this, newly installed packages will no longer be instrumented \
                 by Tactician."
            ] in
  Term.(ret (const eject $ const ())),
  Term.info "eject" ~doc ~man

let recompile =
  let doc = "Find and recompile all installed Coq packages. This is mainly needed when you install or remove\
             the package 'coq-tactician-stdlib', which recompiles Coq's standard library." in
  let man = [ `P "The package 'coq-tactician-stdlib' will recompile Coq's standard library with \
                  Tactician support. After that, all other packages also need to be reinstalled in order \
                  to be consistent with the new standard library. This utility will take care of that."
            ] in
  Term.(ret (const stdlib $ const ())),
  Term.info "recompile" ~doc ~man

let command =
  let doc = "The command to execute" in
  Arg.(required & pos 0 (some string) None & info [] ~docv:"cmd" ~doc)

let args =
  let doc = "Arguments of the command to execute" in
  Arg.(value & pos_right 0 string [] & info [] ~docv:"arg" ~doc)

let exec =
  let doc = "Run a command in an environment where Tactician is injected into Coq. Useful for executing \
             build commands." in
  let man = [ `P "Executes the specified command, with optional parameters, within an environment where \
                  Tactician is injected into calls to coqc. This is useful when working on Coq developments \
                  were tactician is used. The standard usage is for the command to build the entire project."
            ; `S Manpage.s_examples
            ; `Pre ("tactician exec make")
            ; `Pre ("tactician exec dune build")
            ] in
  Term.(ret (const exec_command $ command $ args)),
  Term.info "exec" ~doc ~man

let default_cmd =
  let doc = "Management utilities for the Tactician tactic learner and prover." in
  let sdocs = Manpage.s_common_options in
  let man_xrefs = [ `Cmd "enable"; `Cmd "disable"; `Cmd "inject"; `Cmd "eject"; `Cmd "recompile" ] in
  Term.(ret (const (`Help (`Pager, None)))),
  Term.info "tactician" ~doc ~sdocs ~man_xrefs

let cmds = [enable; disable; inject; eject; recompile; exec]
let () = Term.(exit @@ eval_choice default_cmd cmds)
