open Ltac_plugin
open Map_all_the_things

open Stdarg
open Extraargs
open Tacarg
open Taccoerce
open G_auto
open Firstorder_plugin
open G_ground
open G_rewrite
open Funind_plugin
open G_indfun
open Constrexpr
open Genintern
open Libnames
open Locus
open Names
open Loc
open Tactypes
open Tactics
open Tacexpr
open Tacred

module OList = List

let at wit = register_generic_map_identity wit
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

  (* TODO: See if there is something that can be done for Ltac2 *)
]

let _ = register_generic_map wit_ident (module struct
    type raw = Id.t
    type glob = Id.t
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.variable_map
      let glob_map m = m.variable_map
    end
  end)

let _ = register_generic_map wit_hyp (module struct
    type raw = lident
    type glob = lident
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.cast_map m.variable_map
      let glob_map m = m.cast_map m.variable_map
    end
  end)

let _ = register_generic_map wit_uconstr (module struct
    type raw = constr_expr
    type glob = glob_constr_and_expr
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.constr_expr_map
      let glob_map m = m.glob_constr_and_expr_map
    end
  end)

let _ = register_generic_map wit_open_constr (module struct
    type raw = constr_expr
    type glob = glob_constr_and_expr
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.constr_expr_map
      let glob_map m = m.glob_constr_and_expr_map
    end
  end)

let _ = register_generic_map wit_constr (module struct
    type raw = constr_expr
    type glob = glob_constr_and_expr
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.constr_expr_map
      let glob_map m = m.glob_constr_and_expr_map
    end
  end)

let _ = register_generic_map wit_ref (module struct
    type raw = qualid
    type glob = GlobRef.t located or_var
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.qualid_map
      let glob_map m = m.or_var_map (m.located_map m.globref_map)
    end
  end)

let _ = register_generic_map wit_quant_hyp (module struct
    type raw = quantified_hypothesis
    type glob = quantified_hypothesis
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.quantified_hypothesis_map
      let glob_map m = m.quantified_hypothesis_map
    end
  end)

let _ = register_generic_map wit_int_or_var (module struct
    type raw = int or_var
    type glob = int or_var
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.or_var_map id
      let glob_map m = m.or_var_map id
    end
  end)

let _ = register_generic_map wit_nat_or_var (module struct
    type raw = int or_var
    type glob = int or_var
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.or_var_map id
      let glob_map m = m.or_var_map id
    end
  end)

let _ = register_generic_map wit_clause_dft_concl (module struct
    type raw = lident clause_expr
    type glob = lident clause_expr
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.clause_expr_map (m.cast_map m.variable_map)
      let glob_map m = m.clause_expr_map (m.cast_map m.variable_map)
    end
  end)

let _ = register_generic_map wit_rename (module struct
    type raw = Id.t * Id.t
    type glob = Id.t * Id.t
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = fun (a, b) ->
        let+ a = m.variable_map a
        and+ b = m.variable_map b in
        (a, b)
      let glob_map m = fun (a, b) ->
        let+ a = m.variable_map a
        and+ b = m.variable_map b in
        (a, b)
    end
  end)

let _ = register_generic_map wit_hloc (module struct
    type raw = loc_place
    type glob = loc_place
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.option_map (fun (a, b) -> let+ a = m.cast_map m.variable_map a in a, b)
      let glob_map m = m.option_map (fun (a, b) -> let+ a = m.cast_map m.variable_map a in a, b)
    end
  end)

let at wit = register_generic_map wit (module struct
    type raw = constr_expr
    type glob = glob_constr_and_expr
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.constr_expr_map
      let glob_map m = m.glob_constr_and_expr_map
    end
  end)
let _ = [at wit_glob; at wit_lglob]

let _ = register_generic_map wit_lconstr (module struct
    type raw = constr_expr
    type glob = glob_constr_and_expr
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.constr_expr_map
      let glob_map m = m.glob_constr_and_expr_map
    end
  end)

let _ = register_generic_map wit_in_clause (module struct
    type raw = lident clause_expr
    type glob = lident clause_expr
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.clause_expr_map (m.cast_map m.variable_map)
      let glob_map m = m.clause_expr_map (m.cast_map m.variable_map)
    end
  end)

let _ = register_generic_map wit_occurrences (module struct
    type raw = int list or_var
    type glob = int list or_var
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.or_var_map id
      let glob_map m = m.or_var_map id
    end
  end)

let _ = register_generic_map wit_intro_pattern (module struct
    type raw = constr_expr intro_pattern_expr CAst.t
    type glob = glob_constr_and_expr intro_pattern_expr CAst.t
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.cast_map (m.intro_pattern_expr_map m.constr_expr_map)
      let glob_map m = m.cast_map (m.intro_pattern_expr_map m.glob_constr_and_expr_map)
    end
  end)

let _ = register_generic_map wit_simple_intropattern (module struct
    type raw = constr_expr intro_pattern_expr CAst.t
    type glob = glob_constr_and_expr intro_pattern_expr CAst.t
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.cast_map (m.intro_pattern_expr_map m.constr_expr_map)
      let glob_map m = m.cast_map (m.intro_pattern_expr_map m.glob_constr_and_expr_map)
    end
  end)

let _ = register_generic_map wit_constr_with_bindings (module struct
    type raw = constr_expr with_bindings
    type glob = glob_constr_and_expr with_bindings
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.with_bindings_map m.constr_expr_map
      let glob_map m = m.with_bindings_map m.glob_constr_and_expr_map
    end
  end)

let _ = register_generic_map wit_open_constr_with_bindings (module struct
    type raw = constr_expr with_bindings
    type glob = glob_constr_and_expr with_bindings
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.with_bindings_map m.constr_expr_map
      let glob_map m = m.with_bindings_map m.glob_constr_and_expr_map
    end
  end)

let _ = register_generic_map wit_bindings (module struct
    type raw = constr_expr bindings
    type glob = glob_constr_and_expr bindings
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.bindings_map m.constr_expr_map
      let glob_map m = m.bindings_map m.glob_constr_and_expr_map
    end
  end)

let _ = register_generic_map wit_destruction_arg (module struct
    type raw = constr_expr with_bindings destruction_arg
    type glob = glob_constr_and_expr with_bindings destruction_arg
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.destruction_arg_map (m.with_bindings_map m.constr_expr_map)
      let glob_map m = m.destruction_arg_map (m.with_bindings_map m.glob_constr_and_expr_map)
    end
  end)

let _ = register_generic_map wit_auto_using (module struct
    type raw = constr_expr list
    type glob = glob_constr_and_expr list
    module M = functor (M : MapDef) -> struct
      open M
      open Monad.Make(M)
      let raw_map m = List.map m.constr_expr_map
      let glob_map m = List.map m.glob_constr_and_expr_map
    end
  end)

let _ = register_generic_map wit_firstorder_using (module struct
    type raw = qualid list
    type glob = GlobRef.t located or_var list
    module M = functor (M : MapDef) -> struct
      open M
      open Monad.Make(M)
      let raw_map m = List.map (m.qualid_map)
      let glob_map m = List.map (m.or_var_map (m.located_map m.globref_map))
    end
  end)

let _ = register_generic_map wit_glob_constr_with_bindings (module struct
    type raw = constr_expr with_bindings
    type glob = glob_constr_and_expr with_bindings
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.with_bindings_map m.constr_expr_map
      let glob_map m = m.with_bindings_map m.glob_constr_and_expr_map
    end
  end)

let _ = register_generic_map wit_rewstrategy (module struct
    type raw = raw_strategy
    type glob = glob_strategy
    module M = functor (M : MapDef) -> struct
      open Rewrite
      open M
      open Monad.Make(M)
      let rec strategy_map f g = function
        | StratId | StratFail | StratRefl as s -> return s
        | StratUnary (s, str) ->
          let+ str = strategy_map f g str in
          StratUnary (s, str)
        | StratBinary (s, str, str') ->
          let+ str = strategy_map f g str
          and+ str' = strategy_map f g str' in
          StratBinary (s, str, str')
        | StratNAry (s, strs) ->
          let+ strs = List.map (strategy_map f g) strs in
          StratNAry (s, strs)
        | StratConstr (c, b) ->
          let+ c = f c in
          StratConstr (c, b)
        | StratTerms l ->
          let+ l = List.map f l in
          StratTerms l
        | StratHints _ as s -> return s
        | StratEval r ->
          let+ r = g r in
          StratEval r
        | StratFold c ->
          let+ c = f c in
          StratFold c
      let or_by_notation_r_map f = function
        | AN x -> let+ x = f x in AN x
        | ByNotation x -> return (ByNotation x)
      let and_short_name_map m f (x, n) =
        let+ x = f x
        and+ n = m.short_name_map n in
        (x, n)
      let evaluable_global_reference_map m = function
        | EvalConstRef c ->
          let+ c = m.constant_map c in
          EvalConstRef c
        | EvalVarRef id ->
          let+ id = m.variable_map id in
          EvalVarRef id
      let raw_map m = strategy_map m.constr_expr_map
          (m.red_expr_gen_map m.constr_expr_map
             (m.cast_map (or_by_notation_r_map m.qualid_map))
             m.constr_expr_map)
      let glob_map m = strategy_map m.glob_constr_and_expr_map
          (m.red_expr_gen_map m.glob_constr_and_expr_map
             (m.or_var_map (and_short_name_map m (evaluable_global_reference_map m)))
             m.glob_constr_pattern_and_expr_map)
    end
  end)

let _ = register_generic_map wit_fun_ind_using (module struct
    type raw = constr_expr with_bindings option
    type glob = glob_constr_and_expr with_bindings option
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.option_map (m.with_bindings_map m.constr_expr_map)
      let glob_map m = m.option_map (m.with_bindings_map m.glob_constr_and_expr_map)
    end
  end)

let _ = register_generic_map wit_with_names (module struct
    type raw = constr_expr intro_pattern_expr CAst.t option
    type glob = glob_constr_and_expr intro_pattern_expr CAst.t option
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.option_map (m.cast_map (m.intro_pattern_expr_map m.constr_expr_map))
      let glob_map m = m.option_map (m.cast_map (m.intro_pattern_expr_map m.glob_constr_and_expr_map))
    end
  end)

let at wit = register_generic_map wit (module struct
    type raw = raw_tactic_expr
    type glob = glob_tactic_expr
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.raw_tactic_expr_map
      let glob_map m = m.glob_tactic_expr_map
    end
  end)

let _ = [at wit_tactic; at wit_ltac]

let _ = register_generic_map wit_by_arg_tac (module struct
    type raw = raw_tactic_expr option
    type glob = glob_tactic_expr option
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.option_map m.raw_tactic_expr_map
      let glob_map m = m.option_map m.glob_tactic_expr_map
    end
  end)
