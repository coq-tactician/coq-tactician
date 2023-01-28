open Proofview

type prediction = Search_strategy_internal.prediction =
  { confidence : float
  ; focus      : int
  ; tactic     : float tactic }

(* TODO: Modify this with a more failsafe contract *)
type cont_tactic = Search_strategy_internal.cont_tactic = Cont of cont_tactic tactic
type search_strategy = Search_strategy_internal.search_strategy

let register_search_strategy = Search_strategy_internal.register_search_strategy
