open Proofview

type prediction =
  { confidence : float
  ; focus      : int
  ; tactic     : float tactic }

(* TODO: Modify this with a more failsafe contract *)
(* TODO: Remove (unit -> bool) this is a hack *)
type search_strategy = (unit -> bool) -> prediction IStream.t tactic -> unit tactic

val register_search_strategy : string -> search_strategy -> unit
