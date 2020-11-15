open Ltac_plugin
open Map_all_the_things

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
open Libnames
open Locus
open Names
open Loc
open Tactypes
open Tactics
open Tacexpr

module OList = List

let at wit = register_generic_map_identity wit
let _ = [
  (* Stdarg *)
  at wit_unit; at wit_bool; at wit_int; at wit_string; at wit_pre_ident; at wit_ident;
  at wit_sort_family;

  (* Extraargs *)
  at wit_orient; at wit_rename; at wit_natural; at wit_test_lpar_id_colon;

  (* Tacarg *)
  at wit_quant_hyp;

  (* Taccoerce *)
  at wit_constr_context; at wit_constr_under_binders;

  (* G_auto *)
  at wit_hintbases;

  (* TODO: See if there is something that can be done for Ltac2 *)
]

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
      let raw_map m = m.cast_map id
      let glob_map m = m.or_var_map (m.located_map id)
    end
  end)

let _ = register_generic_map wit_hyp (module struct
    type raw = lident
    type glob = lident
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.cast_map id
      let glob_map m = m.cast_map id
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

let _ = register_generic_map wit_clause_dft_concl (module struct
    type raw = lident clause_expr
    type glob = lident clause_expr
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.clause_expr_map (m.cast_map id)
      let glob_map m = m.clause_expr_map (m.cast_map id)
    end
  end)

let _ = register_generic_map wit_hloc (module struct
    type raw = loc_place
    type glob = loc_place
    module M = functor (M : MapDef) -> struct
      open M
      let location_map f g = function
        | HypLocation x -> let+ x = f x in HypLocation x
        | ConclLocation x -> let+ x = g x in ConclLocation x
      let raw_map m = location_map (fun (a, b) -> let+ a = m.cast_map id a in a, b) id
      let glob_map m = location_map (fun (a, b) -> let+ a = m.cast_map id a in a, b) id
    end
  end)

let _ = register_generic_map wit_glob (module struct
    type raw = constr_expr
    type glob = glob_constr_and_expr
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.constr_expr_map
      let glob_map m = m.glob_constr_and_expr_map
    end
  end)

let _ = register_generic_map wit_lconstr (module struct
    type raw = constr_expr
    type glob = glob_constr_and_expr
    module M = functor (M : MapDef) -> struct
      open M
      let raw_map m = m.constr_expr_map
      let glob_map m = m.glob_constr_and_expr_map
    end
  end)

let _ = register_generic_map wit_casted_constr (module struct
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
      let raw_map m = m.clause_expr_map (m.cast_map id)
      let glob_map m = m.clause_expr_map (m.cast_map id)
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
      let raw_map m = List.map (m.cast_map id)
      let glob_map m = List.map (m.or_var_map (m.located_map id))
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
