open Ltac_plugin
open Gendischarge
open Cook_tacexpr

open Ssrmatching_plugin
open Ssreflect_plugin
open Stdarg
open Extraargs
open Tacarg
open Taccoerce
open Ssrparser
open Ssrmatching
open G_auto
open Ground_plugin
open G_ground
open G_rewrite
open Recdef_plugin
open G_indfun

module OList = List
open DischargeMonad

(* This is a list of generic argument witnesses that do not contain KerNames, and therefore don't need to be
   discharged *)
let at wit = register_discharge0 wit (fun _ arg -> return arg)
let _ = [
  (* Stdarg *)
  at wit_unit; at wit_bool; at wit_int; at wit_string; at wit_pre_ident; at wit_int_or_var; at wit_ident;
  at wit_var; at wit_ref; at wit_sort_family; at wit_constr; at wit_uconstr; at wit_open_constr;
  at wit_clause_dft_concl;

  (* Extraargs *)
  at wit_orient; at wit_rename; at wit_natural; at wit_glob; at wit_lconstr; at wit_casted_constr;
  at wit_hloc; (* wit_by_arg_tac *) at wit_test_lpar_id_colon; at wit_in_clause; at wit_occurrences;

  (* Tacarg *)
  at wit_intro_pattern; at wit_simple_intropattern; at wit_quant_hyp;
  at wit_constr_with_bindings; at wit_open_constr_with_bindings; at wit_bindings;
  (* wit_tactic *) (* at with_ltac *) at wit_destruction_arg;

  (* Taccoerce *)
  at wit_constr_context; at wit_constr_under_binders;

  (* G_auto *)
  at wit_auto_using; at wit_hintbases;

  (* G_ground *)
  at wit_firstorder_using;

  (* G_rewrite *)
  at wit_glob_constr_with_bindings;

  (* G_indfun *)
  at wit_fun_ind_using; at wit_with_names;

  (* Ssrparser *)
  (* wit_ssrtacarg, *) (* wit_ssrtclarg *) at wit_ssrseqdir; (* wit_ssrseqarg *) (* wit_ssrintrosarg *)
  (* wit_ssrsufffwd *) at wit_ssripatrep; at wit_ssrarg; at wit_ssrrwargs; at wit_ssrclauses; at wit_ssrcasearg;
  at wit_ssrmovearg; at wit_ssrapplyarg; (* wit_ssrhavefwdwbinders *) at wit_ssrcongrarg;
  at wit_ssrfwdid; at wit_ssrsetfwd; (* wit_ssrdoarg *) (* wit_ssrhint *) at wit_ssrhpats; at wit_ssrhpats_nobs;
  at wit_ssrhpats_wtransp; at wit_ssrposefwd; at wit_ssrrpat; at wit_ssrterm; at wit_ssrunlockarg;
  at wit_ssrunlockargs; at wit_ssrwgen; at wit_ssrwlogfwd; at wit_ssrfixfwd; at wit_ssrfwd; at wit_ssrfwdfmt;
  at wit_ssrcpat; at wit_ssrdgens; at wit_ssrdgens_tl; at wit_ssrdir; at wit_ssrexactarg;

  (* Ssrmatching *)
  at Internal.wit_rpatternty

  (* TODO: See if there is something that can be done for Ltac2 *)
]

let at wit = register_discharge0 wit (fun ids v -> cook ids v)
let _ = [at wit_tactic; at wit_ltac; at wit_ssrtacarg; at wit_ssrtclarg]

let option_map f = function
  | None -> return None
  | Some t -> let+ res = f t in Some res

let _ =
  register_discharge0 wit_by_arg_tac
    (fun ids v -> option_map (cook ids) v)

let _ =
  register_discharge0 wit_ssrseqarg
    (fun ids (a, ((e, ls), d)) ->
       let+ ls = List.map (option_map (cook ids)) ls
       and+ d = option_map (cook ids) d in
       (a, ((e, ls), d)))

let _ =
  register_discharge0 wit_ssrintrosarg
    (fun ids (t, p) -> let+ t = cook ids t in t, p)

let _ =
  register_discharge0 wit_ssrsufffwd
    (fun ids (p, (q, (r, ls))) ->
       let+ ls = List.map (option_map (cook ids)) ls in
       (p, (q, (r, ls))))

let _ =
  register_discharge0 wit_ssrhavefwdwbinders
    (fun ids (p, (q, (r, (t, ls)))) ->
       let+ ls = List.map (option_map (cook ids)) ls in
       (p, (q, (r, (t, ls)))))

let _ =
  register_discharge0 wit_ssrdoarg
    (fun ids ((p, (q, ls)), r)->
       let+ ls = List.map (option_map (cook ids)) ls in
       ((p, (q, ls)), r))

let _ =
  register_discharge0 wit_ssrhint
    (fun ids (p, ls) ->
       let+ ls = List.map (option_map (cook ids)) ls in
       (p, ls))

let _ =
  register_discharge0 wit_ssrhintarg
    (fun ids (p, ls) ->
       let+ ls = List.map (option_map (cook ids)) ls in
       (p, ls))
