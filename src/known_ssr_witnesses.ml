open Tactician_ltac1_record_plugin
open Gendischarge
open Cook_tacexpr
open Known_witnesses
open Ssrmatching_plugin
open Ssreflect_plugin
open Ssrparser
open Ssrmatching

module OList = List
open DischargeMonad

let at wit = register_discharge0 wit (fun _ arg -> return arg)
let _ = [
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
let _ = [at wit_ssrtacarg; at wit_ssrtclarg]

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
