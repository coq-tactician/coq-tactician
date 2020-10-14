open Genarg
open Names

type log = KNset.t
type to_discharge = KNset.t

type 'a discharged = 'a * log

(* Ad-hoc writer monad on KerName sets *)
module DischargeMonadDef = struct
  type 'a t = 'a * log
  let return x = x, KNset.empty
  let map f (x, l) = f x, l

  let (>>=) (x, l) f =
    let (x', l') = f x in
    x', KNset.union l l'
  let (>>) ((), l1) (x, l2) = x, KNset.union l1 l2
end

module DischargeMonad = struct
  include Monad.Make(DischargeMonadDef)
  let ap (f, l1) (x, l2) = f x, KNset.union l1 l2
  let log name = (), KNset.singleton name
  let bind (x, l) f =
    let (x', l') = f x in
    x', KNset.union l l'
  let product (x, l1) (y, l2) = (x, y), KNset.union l1 l2
  let (<*>) a b     = ap a b
  let (let+) x f    = map f x
  let (and+) o1 o2  = product o1 o2
  let (let*) x f    = bind x f
end

(* The to_discharge input is not really needed because one can just look a name up with
   Tacenv.interp_ltac and see if it can be found. But there might be a future circumstance where we cannot
   do that. *)
type 'glb discharge_fun = to_discharge -> 'glb -> 'glb discharged
module DischargeObj =
struct
  type ('raw, 'glb, 'top) obj = 'glb discharge_fun
  let name = "discharge"
  let default _ = None
end

module Discharge = Register (DischargeObj)

let discharge = Discharge.obj
let register_discharge0 = Discharge.register0

exception UnknownWitnessError of argument_type

let generic_discharge names (GenArg (Glbwit wit, v)) =
  try
    let v', names' = discharge wit names v in
    in_gen (glbwit wit) v', names'
  with e when CErrors.is_anomaly e -> raise (UnknownWitnessError (ArgumentType wit))
(* We catch anomalies here, because we can by definition not discharge all generic arguments.
   For the ones we miss, there is a "printing tick", and if that does not work, we just don't record
   that tactic. *)

