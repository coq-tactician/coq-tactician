open Proofview

type prediction =
  { confidence : float
  ; focus      : int
  ; tactic     : float tactic }

(* TODO: Modify this with a more failsafe contract *)
type cont_tactic = Cont of cont_tactic tactic
type with_update_learner = { f : 'a. 'a tactic -> 'a tactic }
type search_strategy = (unit -> bool) -> prediction IStream.t tactic -> with_update_learner -> cont_tactic

let null_strategy _ _ _ = Cont (Tacticals.New.tclZEROMSG (Pp.str "No search strategy registered"))

let strategy : search_strategy ref = ref null_strategy
let register_search_strategy _str strat = strategy := strat

let search_with_strategy x = !strategy x
