open Ltac_plugin
open Tacexpr_functor
open Glob_term_functor
open Constrexpr_functor
open Pattern_functor
open Tactician_util
open Coq_ast_monadic_map
open Coq_ast_sequence
open Genarg

module IdM = Mapper(IdentityMonad)

module MapDef (M : Monad.Def) = struct
  open WithMonadNotations(M)

  open Tacexpr
  open Glob_term
  open Constrexpr

  type generic_obj =
    < cases_pattern_g    : cases_pattern map
    ; cases_pattern_expr : cases_pattern_expr map
    ; glob_constr_g      : glob_constr map
    ; pattern            : g_pat map
    ; glob_tacarg        : glob_tactic_arg map
    ; glob_tacexpr       : glob_tactic_expr map
    ; raw_tacarg         : raw_tactic_arg map
    ; raw_tacexpr        : raw_tactic_expr map
    ; g_term             : g_trm map
    ; constr_expr        : constr_expr map >
end

module type GenMap = sig
  type raw
  type glob
  module M : functor (M : Monad.Def) -> sig
    open MapDef(M)
    open M
    val raw_map : generic_obj -> raw -> raw t
    val glob_map : generic_obj -> glob -> glob t
  end
end

let generic_identity_cata (type r) (type g)
    (_ : (r, g, 't) genarg_type) : (module GenMap with type raw = r and type glob = g) =
  (module struct
    type raw = r
    type glob = g
    module M = functor (M : Monad.Def) -> struct
      open M
      let raw_map _ r = return r
      let glob_map _ r = return r
    end
  end)

module MapObj =
struct
  type ('raw, 'glb, 'top) obj = (module GenMap with type raw = 'raw and type glob = 'glb) option
  let name = "cata"
  let default _ = Some None
end

module Map = Register(MapObj)

let generic_map = Map.obj
let register_generic_cata w k = Map.register0 w (Some k)
let register_generic_cata_identity w =
  register_generic_cata w (generic_identity_cata w)

module Cata (M: Monad.Def) = struct
  include WithMonadNotations(M)
  open Monad.Make(M)
  open MapDef(M)
  open Sequence(M)
  module MM = Mapper(M)

  type ('raw, 'glb) gen_map =
    { raw : generic_obj  -> 'raw map
    ; glb : generic_obj -> 'glb map }

  let ident_gen_map =
    { raw = (fun _ -> return)
    ; glb = (fun _ -> return) }

  module MapObj =
  struct
    type ('raw, 'glb, 'top) obj = ('raw, 'glb) gen_map option
    let name = "cata2"
    let default _ = Some None
  end

  module Map = Register (MapObj)

  let map (type r) (type g) wit =
    match Map.obj wit with
    | None ->
      (match generic_map wit with
       | None ->
         Feedback.msg_warning Pp.(str "Tactician cannot find a mapping object for " ++
                                  str "the generic argument " ++
                                  pr_argument_type (ArgumentType wit) ++
                                  str ". Please report. ");
         ident_gen_map
      | Some (module G : GenMap with type raw = r and type glob = g) ->
        let module M = G.M(M) in
        let x =  {raw = M.raw_map; glb = M.glob_map} in
        Map.register0 wit (Some x); x)
    | Some x -> x

  let generic_raw_map obj g
    : rlevel generic_argument t =
    let rec aux ((GenArg (Rawwit wit, v)) as g) = match wit with
      | ListArg wit as witl ->
        let ls = out_gen (Rawwit witl) g in
        let+ ls = List.map (fun x ->
            let+ res = aux (in_gen (Rawwit wit) x)
            in out_gen (Rawwit wit) res) ls in
        in_gen (Rawwit witl) ls
      | OptArg wit as wito ->
        let e = out_gen (Rawwit wito) g in
        let+ e = match e with
          | None -> return None
          | Some e -> let+ e = aux (in_gen (Rawwit wit) e) in
            Some (out_gen (Rawwit wit) e) in
        in_gen (Rawwit wito) e
      | PairArg (wit1, wit2) as witp ->
        let e1, e2 = out_gen (Rawwit witp) g in
        let+ e1 = aux (in_gen (Rawwit wit1) e1)
        and+ e2 = aux (in_gen (Rawwit wit2) e2) in
        let e1 = out_gen (Rawwit wit1) e1 in
        let e2 = out_gen (Rawwit wit2) e2 in
        in_gen (Rawwit witp) (e1, e2)
      | ExtraArg _ ->
        let+ v =((map wit).raw obj v) in
        in_gen (rawwit wit) v
    in aux g

  let generic_glob_map obj g
    : glevel generic_argument t =
    let rec aux ((GenArg (Glbwit wit, v)) as g) = match wit with
      | ListArg wit as witl ->
        let ls = out_gen (Glbwit witl) g in
        let+ ls = List.map (fun x ->
            let+ res = aux (in_gen (Glbwit wit) x)
            in out_gen (Glbwit wit) res) ls in
        in_gen (Glbwit witl) ls
      | OptArg wit as wito ->
        let e = out_gen (Glbwit wito) g in
        let+ e = match e with
          | None -> return None
          | Some e -> let+ e = aux (in_gen (Glbwit wit) e) in
            Some (out_gen (Glbwit wit) e) in
        in_gen (Glbwit wito) e
      | PairArg (wit1, wit2) as witp ->
        let e1, e2 = out_gen (Glbwit witp) g in
        let+ e1 = aux (in_gen (Glbwit wit1) e1)
        and+ e2 = aux (in_gen (Glbwit wit2) e2) in
        let e1 = out_gen (Glbwit wit1) e1 in
        let e2 = out_gen (Glbwit wit2) e2 in
        in_gen (Glbwit witp) (e1, e2)
      | ExtraArg _ ->
        let+ v =((map wit).glb obj v) in
        in_gen (glbwit wit) v
    in aux g

  type sequence_record =
    { cases_pattern_g : cases_pattern_t      -> cases_pattern t
    ; cases_pattern_r : cases_pattern_expr_t -> cases_pattern_expr t
    ; constr_expr     : constr_expr_t        -> constr_expr t
    ; constr_pattern  : constr_pattern_t     -> constr_pattern t
    ; glob_constr     : glob_constr_t        -> glob_constr t
    ; glob_tacarg     : glob_tactic_arg_t    -> glob_tactic_arg t
    ; glob_tacexpr    : glob_tactic_expr_t   -> glob_tactic_expr t
    ; raw_tacarg      : raw_tactic_arg_t     -> raw_tactic_arg t
    ; raw_tacexpr     : raw_tactic_expr_t    -> raw_tactic_expr t }

  type sequence_obj =
    < cases_pattern_g : cases_pattern_t      -> cases_pattern t
    ; cases_pattern_r : cases_pattern_expr_t -> cases_pattern_expr t
    ; constr_expr     : constr_expr_t        -> constr_expr t
    ; constr_pattern  : constr_pattern_t     -> constr_pattern t
    ; glob_constr     : glob_constr_t        -> glob_constr t
    ; glob_tacarg     : glob_tactic_arg_t    -> glob_tactic_arg t
    ; glob_tacexpr    : glob_tactic_expr_t   -> glob_tactic_expr t
    ; raw_tacarg      : raw_tactic_arg_t     -> raw_tactic_arg t
    ; raw_tacexpr     : raw_tactic_expr_t    -> raw_tactic_expr t >

  let default_sequence_record =
    { cases_pattern_g = cases_pattern_g_sequence
    ; cases_pattern_r = cases_pattern_r_sequence
    ; constr_expr = constr_expr_sequence
    ; constr_pattern = constr_pattern_sequence
    ; glob_constr = glob_constr_sequence
    ; glob_tacarg = glob_tacarg_sequence
    ; glob_tacexpr = glob_tacexpr_sequence
    ; raw_tacarg = raw_tacarg_sequence
    ; raw_tacexpr = raw_tacexpr_sequence }

  let mk_sequence_obj
      { cases_pattern_g; cases_pattern_r; constr_expr; constr_pattern
      ; glob_constr; glob_tacarg; glob_tacexpr; raw_tacarg; raw_tacexpr }
    : sequence_obj =
    object
      method cases_pattern_g = cases_pattern_g
      method cases_pattern_r = cases_pattern_r
      method constr_expr = constr_expr
      method constr_pattern = constr_pattern
      method glob_constr = glob_constr
      method glob_tacarg = glob_tacarg
      method glob_tacexpr = glob_tacexpr
      method raw_tacarg = raw_tacarg
      method raw_tacexpr = raw_tacexpr
    end

  let mk = mk_sequence_obj

  let rec globobj (m : sequence_obj) = object
    method term = g_trm_cata' m
    method dterm = g_trm_cata' m
    method pattern = g_pat_cata' m
    method constant = return
    method reference = return
    method name = return
    method tacexpr = glob_tactic_expr_cata' m
    method tacarg = glob_tactic_arg_cata' m
    method genarg = generic_glob_map (generic_obj m);
    method cases_pattern_g = cases_pattern_g_cata' m;
    method glob_constr_g = glob_constr_cata' m;
  end
  and rawobj (m : sequence_obj) = object
    method term = constr_expr_cata' m
    method dterm = constr_expr_cata' m
    method pattern = constr_expr_cata' m
    method constant = return
    method reference = return
    method name = return
    method tacexpr = raw_tactic_expr_cata' m
    method tacarg = raw_tactic_arg_cata' m
    method genarg = generic_raw_map (generic_obj m);
    method cases_pattern_expr = cases_pattern_r_cata' m;
    method constr_expr = constr_expr_cata' m
  end
  and glob_tactic_expr_cata' (m : sequence_obj) (t : glob_tactic_expr) =
    m#glob_tacexpr @@ IdM.gen_tactic_expr_map (globobj m) t
  and glob_tactic_arg_cata' m (t : glob_tactic_arg) =
    m#glob_tacarg @@ IdM.gen_tactic_arg_map (globobj m) t
  and raw_tactic_expr_cata' m (t : raw_tactic_expr) =
    m#raw_tacexpr @@ IdM.gen_tactic_expr_map (rawobj m) t
  and raw_tactic_arg_cata' m (t : raw_tactic_arg) =
    m#raw_tacarg @@ IdM.gen_tactic_arg_map (rawobj m) t
  and glob_constr_cata' m (t : glob_constr) =
    m#glob_constr @@ IdM.dast_map (IdM.glob_constr_r_map (globobj m)) t
  and cases_pattern_g_cata' m (t : cases_pattern) =
    m#cases_pattern_g @@ IdM.dast_map (IdM.cases_pattern_r_map (globobj m)) t
  and constr_expr_cata' m (t : constr_expr) =
    m#constr_expr @@ CAst.map (IdM.constr_expr_r_map (rawobj m)) t
  and cases_pattern_r_cata' m (t : cases_pattern_expr) =
    m#cases_pattern_r @@ CAst.map (IdM.cases_pattern_expr_r_map (rawobj m)) t
  and g_trm_cata' m ((gt, ct) : g_trm) =
    let+ gt = glob_constr_cata' m gt
    and+ ct = MM.option_map (constr_expr_cata' m) ct in
    gt, ct
  and constr_pattern_cata' m (t : constr_pattern) =
    m#constr_pattern @@ IdM.constr_pattern_r_map (constr_pattern_cata' m) t
  and g_pat_cata' m ((ids, gtrm, pat) : g_pat) =
    let+ gtrm = g_trm_cata' m gtrm
    and+ pat = constr_pattern_cata' m pat in
    ids, gtrm, pat

  and generic_obj (m : sequence_obj) = object
    method cases_pattern_g = cases_pattern_g_cata m;
    method cases_pattern_expr = cases_pattern_r_cata m;
    method glob_constr_g = glob_constr_cata m;
    method pattern = g_pat_cata m
    method glob_tacarg = glob_tactic_arg_cata m
    method glob_tacexpr = glob_tactic_expr_cata m
    method raw_tacexpr = raw_tactic_expr_cata m
    method raw_tacarg = raw_tactic_arg_cata m
    method g_term = g_trm_cata m
    method constr_expr = constr_expr_cata m
  end
  and glob_tactic_expr_cata m t =
    let t = Tacexpr_convert.glob_tactic_expr_to_glob_tactic_expr t in
    let+ t = glob_tactic_expr_cata' m t in
    Tacexpr_convert.glob_tactic_expr_to_glob_tactic_expr2 t
  and glob_tactic_arg_cata m t =
    let t = Tacexpr_convert.glob_tactic_arg_to_glob_tactic_arg t in
    let+ t = glob_tactic_arg_cata' m t in
    Tacexpr_convert.glob_tactic_arg_to_glob_tactic_arg2 t
  and raw_tactic_expr_cata m t =
    let t = Tacexpr_convert.raw_tactic_expr_to_raw_tactic_expr t in
    let+ t = raw_tactic_expr_cata' m t in
    Tacexpr_convert.raw_tactic_expr_to_raw_tactic_expr2 t
  and raw_tactic_arg_cata m t =
    let t = Tacexpr_convert.raw_tactic_arg_to_raw_tactic_arg t in
    let+ t = raw_tactic_arg_cata' m t in
    Tacexpr_convert.raw_tactic_arg_to_raw_tactic_arg2 t
  and glob_constr_cata m t =
    let t = Glob_term_convert.glob_constr_to_glob_constr t in
    let+ t = glob_constr_cata' m t in
    Glob_term_convert.glob_constr_to_glob_constr2 t
  and cases_pattern_g_cata m t =
    let t = Glob_term_convert.cases_pattern_to_cases_pattern t in
    let+ t = cases_pattern_g_cata' m t in
    Glob_term_convert.cases_pattern_to_cases_pattern2 t
  and constr_expr_cata m t =
    let t = Constrexpr_convert.constr_expr_to_constr_expr t in
    let+ t = constr_expr_cata' m t in
    Constrexpr_convert.constr_expr_to_constr_expr2 t
  and cases_pattern_r_cata m t =
    let t = Constrexpr_convert.cases_pattern_expr_to_cases_pattern_expr t in
    let+ t = cases_pattern_r_cata' m t in
    Constrexpr_convert.cases_pattern_expr_to_cases_pattern_expr2 t
  and g_trm_cata m t =
    let t = Tacexpr_convert.g_trm_to_g_trm t in
    let+ t = g_trm_cata' m t in
    Tacexpr_convert.g_trm_to_g_trm2 t
  and constr_pattern_cata m t =
    let t = Pattern_convert.constr_pattern_to_constr_pattern t in
    let+ t = constr_pattern_cata' m t in
    Pattern_convert.constr_pattern_to_constr_pattern2 t
  and g_pat_cata m t =
    let t = Tacexpr_convert.g_pat_to_g_pat t in
    let+ t = g_pat_cata' m t in
    Tacexpr_convert.g_pat_to_g_pat2 t

  let glob_tactic_expr_cata m = glob_tactic_expr_cata (mk m)
  let glob_tactic_arg_cata m = glob_tactic_arg_cata (mk m)
  let raw_tactic_expr_cata m = raw_tactic_expr_cata (mk m)
  let raw_tactic_arg_cata m = raw_tactic_arg_cata (mk m)
  let glob_constr_cata m = glob_constr_cata (mk m)
  let cases_pattern_g_cata m = cases_pattern_g_cata (mk m)
  let constr_expr_cata m = constr_expr_cata (mk m)
  let cases_pattern_r_cata m = cases_pattern_r_cata (mk m)
  let g_trm_cata m = g_trm_cata (mk m)
  let constr_pattern_cata m = constr_pattern_cata (mk m)
  and g_pat_cata m = g_pat_cata (mk m)
end

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
open Constrexpr
open Genintern
open Tactypes
open Tactics
open Tacexpr

let at wit = register_generic_cata_identity wit
let _ = [
  (* Stdarg *)
  at wit_unit; at wit_bool; at wit_int; at wit_string; at wit_pre_ident;
  at wit_sort_family;

  (* Extraargs *)
  at wit_orient; at wit_natural; at wit_test_lpar_id_colon;

  (* Taccoerce *)
  at wit_constr_context; at wit_constr_under_binders;

  (* G_auto *)
  at wit_hintbases;

  at wit_ident; at wit_var; at wit_ref; at wit_quant_hyp; at wit_int_or_var; at wit_clause_dft_concl; at wit_rename; at wit_hloc;
  at wit_in_clause; at wit_occurrences; at wit_firstorder_using

  (* TODO: See if there is something that can be done for Ltac2 *)
]

let at wit = register_generic_cata wit (module struct
    type raw = constr_expr
    type glob = glob_constr_and_expr
    module M = functor (M : Monad.Def) -> struct
      let raw_map m = m#constr_expr
      let glob_map m = m#g_term
    end
  end)
let _ = [at wit_uconstr; at wit_open_constr; at wit_constr; at wit_glob; at wit_lconstr; at wit_casted_constr]

let at wit = register_generic_cata wit (module struct
    type raw = constr_expr intro_pattern_expr CAst.t
    type glob = glob_constr_and_expr intro_pattern_expr CAst.t
    module M = functor (M : Monad.Def) -> struct
      module MM = Mapper(M)
      let raw_map m = MM.cast_map (MM.intro_pattern_expr_map m#constr_expr)
      let glob_map m = MM.cast_map (MM.intro_pattern_expr_map m#g_term)
    end
  end)
let _ = [at wit_intro_pattern; at wit_simple_intropattern]

let at wit = register_generic_cata wit (module struct
    type raw = constr_expr with_bindings
    type glob = glob_constr_and_expr with_bindings
    module M = functor (M : Monad.Def) -> struct
      module MM = Mapper(M)
      let raw_map m = MM.with_bindings_map m#constr_expr
      let glob_map m = MM.with_bindings_map m#g_term
    end
  end)
let _ = [at wit_constr_with_bindings; at wit_open_constr_with_bindings; at wit_glob_constr_with_bindings]

let _ = register_generic_cata wit_bindings (module struct
    type raw = constr_expr bindings
    type glob = glob_constr_and_expr bindings
    module M = functor (M : Monad.Def) -> struct
      module MM = Mapper(M)
      let raw_map m = MM.bindings_map m#constr_expr
      let glob_map m = MM.bindings_map m#g_term
    end
  end)

let _ = register_generic_cata wit_destruction_arg (module struct
    type raw = constr_expr with_bindings destruction_arg
    type glob = glob_constr_and_expr with_bindings destruction_arg
    module M = functor (M : Monad.Def) -> struct
      module MM = Mapper(M)
      let raw_map m = MM.destruction_arg_map (MM.with_bindings_map m#constr_expr)
      let glob_map m = MM.destruction_arg_map (MM.with_bindings_map m#g_term)
    end
  end)

let _ = register_generic_cata wit_auto_using (module struct
    type raw = constr_expr list
    type glob = glob_constr_and_expr list
    module M = functor (M : Monad.Def) -> struct
      open Monad.Make(M)
      let raw_map m = List.map m#constr_expr
      let glob_map m = List.map m#g_term
    end
  end)

let _ = register_generic_cata wit_fun_ind_using (module struct
    type raw = constr_expr with_bindings option
    type glob = glob_constr_and_expr with_bindings option
    module M = functor (M : Monad.Def) -> struct
      module MM = Mapper(M)
      let raw_map m = MM.option_map (MM.with_bindings_map m#constr_expr)
      let glob_map m = MM.option_map (MM.with_bindings_map m#g_term)
    end
  end)

let _ = register_generic_cata wit_with_names (module struct
    type raw = constr_expr intro_pattern_expr CAst.t option
    type glob = glob_constr_and_expr intro_pattern_expr CAst.t option
    module M = functor (M : Monad.Def) -> struct
      module MM = Mapper(M)
      let raw_map m = MM.option_map (MM.cast_map (MM.intro_pattern_expr_map m#constr_expr))
      let glob_map m = MM.option_map (MM.cast_map (MM.intro_pattern_expr_map m#g_term))
    end
  end)

let at wit = register_generic_cata wit (module struct
    type raw = raw_tactic_expr
    type glob = glob_tactic_expr
    module M = functor (M : Monad.Def) -> struct
      let raw_map m = m#raw_tacexpr
      let glob_map m = m#glob_tacexpr
    end
  end)
let _ = [at wit_tactic; at wit_ltac]

let _ = register_generic_cata wit_by_arg_tac (module struct
    type raw = raw_tactic_expr option
    type glob = glob_tactic_expr option
    module M = functor (M : Monad.Def) -> struct
      module MM = Mapper(M)
      let raw_map m = MM.option_map m#raw_tacexpr
      let glob_map m = MM.option_map m#glob_tacexpr
    end
  end)
