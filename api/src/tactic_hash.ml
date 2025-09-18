open Ltac_plugin
open Tactician_ltac1_record_plugin
open Monad_util
open Map_all_the_things
open Tacexpr
open Names

module TacticFinderDef = struct
  module M = WriterMonad
      (struct type w = bool let id = false let comb = Bool.(||) end)
  include MapDefTemplate (M)
end
module TacticFinderMapper = MakeMapper(TacticFinderDef)
open TacticFinderDef

let ssr_dirpath = DirPath.make [Id.of_string "ssreflect"; Id.of_string "ssr"; Id.of_string "Coq"]
let rec is_ssr_tactic t =
  let is_ssr_kername k =
    DirPath.equal ssr_dirpath @@ ModPath.dp @@ KerName.modpath k in
  let mapper =
    { TacticFinderDef.default_mapper with
      glob_tactic_arg = (fun a c -> (match a with
          | TacCall CAst.{ v=(ArgArg (_, k), _args); _} ->
            let* () = M.tell (is_ssr_kername k) in
            c a
          | Reference (ArgArg (_, k)) ->
            let* () = M.tell (is_ssr_kername k) in
            c a
          | _ -> c a))
    ; glob_tactic = (fun t c ->
          (match t with
           | TacML CAst.{ v=({ mltac_name = { mltac_plugin = "ssreflect_plugin"; _ };  _ }, _args); _} ->
             let* () = M.tell true in
             c t
           | TacAlias CAst.{ v=(k, _args); _} ->
             let* () = if is_ssr_kername k then
                 M.tell true
               else
                 let al = Tacenv.interp_alias k in
                 M.tell (is_ssr_tactic al.alias_body) in
             c t
           | _ -> c t))
    ; raw_tactic = (fun t c ->
        (match t with
         | TacML CAst.{ v=({ mltac_name = { mltac_plugin = "ssreflect_plugin"; _ };  _ }, _args); _} ->
           let* () = M.tell true in
           c t
         | TacAlias CAst.{ v=(k, _args); _} ->
           let* () = if is_ssr_kername k then
               M.tell true
             else
               let al = Tacenv.interp_alias k in
               M.tell (is_ssr_tactic al.alias_body) in
           c t
         | _ -> c t))
    } in
  fst @@ M.run @@ TacticFinderMapper.glob_tactic_expr_map mapper t

let tactic_hash env t =
  (* TODO: This is an ugly hack:

     We cannot currently properly deal with ssreflect tactics. As such, we don't care to much about them
     But we still expect some properties to hold, such as no collisions. The Hashtbl.hash algorithm only
     processes a fixed number of elements before giving up. Some ssreflect tactics embed the entire
     environment into their AST, however. This causes the hash algorithm to bail out and produce collisions.

     Our solution is to hash together with the string of the tactic for ssreflect tactics.
     We don't do that for normal tactics, because string representations do not map 1-to-1 to AST representations.
  *)
  let open Graph_def in
  let pr_tac t =
    try
      Pp.string_of_ppcmds @@ Sexpr.format_oneline (Pptactic.pr_glob_tactic env t)
    with e when CErrors.noncritical e || CErrors.is_anomaly e -> "" in
  if is_ssr_tactic t then
    XXHasher.with_state (fun s -> XXHasher.update_int (Hashtbl.hash_param 255 255 t) @@
                          XXHasher.update_string (Digest.string @@ pr_tac t) s)
  else
    XXHasher.with_state (fun s -> XXHasher.update_string (Marshal.to_string t [Marshal.No_sharing]) s)
