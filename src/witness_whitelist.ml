open Ltac_plugin
open Ssrmatching_plugin
open Ssreflect_plugin
open Stdarg
open Extraargs
open Tacarg
open Taccoerce
open Ssrparser
open Ssrmatching
open Genarg
open Tacexpr

(**
This is a list of generic argument witnesses that are non-dangerous in when discharging a section.
*)
let at wit = ArgumentType wit
let whitelist = [
  (* Stdarg *)
  at wit_unit; at wit_bool; at wit_int; at wit_string; at wit_pre_ident; at wit_int_or_var; at wit_ident;
  at wit_var; at wit_ref; at wit_sort_family; at wit_constr; at wit_uconstr; at wit_open_constr;
  at wit_clause_dft_concl;

  (* Extraargs *)
  at wit_orient; at wit_rename; at wit_natural; at wit_glob; at wit_lconstr; at wit_casted_constr;
  at wit_hloc; (* wit_by_arg_tac *) at wit_test_lpar_id_colon;

  (* Tacarg *)
  at wit_intro_pattern; at wit_simple_intropattern; at wit_intropattern; at wit_quant_hyp;
  at wit_constr_with_bindings; at wit_open_constr_with_bindings; at wit_bindings; at wit_quantified_hypothesis;
  (* wit_tactic *) (* at with_ltac *) at wit_destruction_arg;

  (* Taccoerce *)
  at wit_constr_context; at wit_constr_under_binders;

  (* Ssrparser *)
  (* wit_ssrtacarg, *) (* wit_ssrtclarg *) at wit_ssrseqdir; (* wit_ssrseqarg *) (* wit_ssrintrosarg *)
  (* wit_ssrsufffwd *) at wit_ssripatrep; at wit_ssrarg; at wit_ssrrwargs; at wit_ssrclauses; at wit_ssrcasearg;
  at wit_ssrmovearg; at wit_ssrapplyarg; (* wit_ssrhavefwdwbinders *) at wit_ssrapplyarg; at wit_ssrcongrarg;
  at wit_ssrfwdid; at wit_ssrsetfwd; (* wit_ssrdoarg *) (* wit_ssrhint *) at wit_ssrhpats; at wit_ssrhpats_nobs;
  at wit_ssrhpats_wtransp; at wit_ssrposefwd; at wit_ssrrpat; at wit_ssrterm; at wit_ssrunlockarg;
  at wit_ssrunlockargs; at wit_ssrwgen; at wit_ssrwlogfwd; at wit_ssrfixfwd; at wit_ssrfwd; at wit_ssrfwdfmt;
  at wit_ssrcpat; at wit_ssrdgens; at wit_ssrdgens_tl; at wit_ssrdir;

  (* Ssrmatching *)
  at Internal.wit_rpatternty

  (* TODO: See if there is something that can be done for Ltac2 *)
]

exception UnknownWitnessError of argument_type

let fold_genarg_extra_tactic
    (f : 'a -> glob_tactic_expr -> ('a * glob_tactic_expr))
    ((GenArg (Glbwit wit, _)) as g : glevel generic_argument)
    s : 'a * glevel generic_argument =
  let wat = ArgumentType wit in
  let option_fold s = function
    | None -> s, None
    | Some t -> let s, res = f s t in s, (Some res) in
  let is_safe = List.exists (fun w -> argument_type_eq wat w) whitelist in
  if is_safe then s, g else
  if has_type g (glbwit wit_by_arg_tac) then
    let v = out_gen (glbwit wit_by_arg_tac) g in
    let s, res = option_fold s v in s, in_gen (glbwit wit_by_arg_tac) res
  else if has_type g (glbwit wit_tactic) then
    let v = out_gen (glbwit wit_tactic) g in
    let s, res = f s v in s, in_gen (glbwit wit_tactic) res
  else if has_type g (glbwit wit_ltac) then
    let v = out_gen (glbwit wit_ltac) g in
    let s, res = f s v in s, in_gen (glbwit wit_ltac) res
  else if has_type g (glbwit wit_ssrtacarg) then
    let v = out_gen (glbwit wit_ssrtacarg) g in
    let s, res = f s v in s, in_gen (glbwit wit_ssrtacarg) res
  else if has_type g (glbwit wit_ssrtclarg) then
    let v = out_gen (glbwit wit_ssrtclarg) g in
    let s, res = f s v in s, in_gen (glbwit wit_ssrtclarg) res
  else if has_type g (glbwit wit_ssrseqarg) then
    let (a, ((e, ls), d)) = out_gen (glbwit wit_ssrseqarg) g in
    let s, ls = List.fold_right (fun t (s, acc) ->
        let s, res = option_fold s t in s, res::acc) ls (s, []) in
    let s, d = option_fold s d in
    s, in_gen (glbwit wit_ssrseqarg) (a, ((e, ls), d))
  else if has_type g (glbwit wit_ssrintrosarg) then
    let (t, p) = out_gen (glbwit wit_ssrintrosarg) g in
    let s, t = f s t in
    s, in_gen (glbwit wit_ssrintrosarg) (t, p)
  else if has_type g (glbwit wit_ssrsufffwd) then
    let (p, (q, (r, ls))) = out_gen (glbwit wit_ssrsufffwd) g in
    let s, ls = List.fold_right (fun t (s, acc) ->
        let s, res = option_fold s t in s, res::acc) ls (s, []) in
    s, in_gen (glbwit wit_ssrsufffwd) (p, (q, (r, ls)))
  else if has_type g (glbwit wit_ssrhavefwdwbinders) then
    let (p, (q, (r, (t, ls)))) = out_gen (glbwit wit_ssrhavefwdwbinders) g in
    let s, ls = List.fold_right (fun t (s, acc) ->
        let s, res = option_fold s t in s, res::acc) ls (s, []) in
    s, in_gen (glbwit wit_ssrhavefwdwbinders) (p, (q, (r, (t, ls))))
  else if has_type g (glbwit wit_ssrdoarg) then
    let ((p, (q, ls)), r) = out_gen (glbwit wit_ssrdoarg) g in
    let s, ls = List.fold_right (fun t (s, acc) ->
        let s, res = option_fold s t in s, res::acc) ls (s, []) in
    s, in_gen (glbwit wit_ssrdoarg) ((p, (q, ls)), r)
  else if has_type g (glbwit wit_ssrhint) then
    let (p, ls) = out_gen (glbwit wit_ssrhint) g in
    let s, ls = List.fold_right (fun t (s, acc) ->
        let s, res = option_fold s t in s, res::acc) ls (s, []) in
    s, in_gen (glbwit wit_ssrhint) (p, ls)
  else raise (UnknownWitnessError (ArgumentType wit))

  let fold_genarg_tactic
      (f : 'a -> glob_tactic_expr -> ('a * glob_tactic_expr))
      ((GenArg (Glbwit wit, _)) as g : glevel generic_argument)
      s : 'a * glevel generic_argument =
    let rec aux s ((GenArg (Glbwit wit, _)) as g) = match wit with
      | ListArg wit as witl ->
        let ls = out_gen (Glbwit witl) g in
        let s, ls = List.fold_right (fun x (s, acc) ->
            let s, res = aux s (in_gen (Glbwit wit) x) in
            s, out_gen (Glbwit wit) res::acc) ls (s, []) in
        s, in_gen (Glbwit witl) ls
      | OptArg wit as wito ->
        let e = out_gen (Glbwit wito) g in
        let s, e = match e with
          | None -> s, None
          | Some e -> let s, e = aux s (in_gen (Glbwit wit) e) in
            s, Some (out_gen (Glbwit wit) e) in
        s, in_gen (Glbwit wito) e
      | PairArg (wit1, wit2) as witp ->
        let e1, e2 = out_gen (Glbwit witp) g in
        let s, e1 = aux s (in_gen (Glbwit wit1) e1) in
        let e1 = out_gen (Glbwit wit1) e1 in
        let s, e2 = aux s (in_gen (Glbwit wit2) e2) in
        let e2 = out_gen (Glbwit wit2) e2 in
        s, in_gen (Glbwit witp) (e1, e2)
      | ExtraArg _ -> fold_genarg_extra_tactic f g s
    in aux s g
