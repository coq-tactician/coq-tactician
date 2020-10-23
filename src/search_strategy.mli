open Proofview

type prediction =
  { confidence : float
  ; focus      : int
  ; tactic     : float tactic }

(* TODO: Modify this with a more failsafe contract *)
type search_strategy = prediction Stream.t tactic -> unit tactic

val register_search_strategy : string -> search_strategy -> unit
