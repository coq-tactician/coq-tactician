open Ltac_plugin
open Gendischarge
open Cook_tacexpr

open Stdarg
open Extraargs
open Tacarg
open Taccoerce
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
  at wit_hyp; at wit_ref; at wit_sort_family; at wit_constr; at wit_uconstr; at wit_open_constr;
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

  (* TODO: See if there is something that can be done for Ltac2 *)
]

let at wit = register_discharge0 wit (fun ids v -> cook ids v)
let _ = [at wit_tactic; at wit_ltac]

let option_map f = function
  | None -> return None
  | Some t -> let+ res = f t in Some res

let _ =
  register_discharge0 wit_by_arg_tac
    (fun ids v -> option_map (cook ids) v)
