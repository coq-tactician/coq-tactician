open Ltac_plugin
open Tacexpr
open Constr
open Context
open Sexpr
open Proofview

module Id = Names.Id

type id = Id.t

module IdMap = Map.Make(struct
    type t = Id.t
    let compare = Names.Id.compare
  end)
type id_map = Id.t IdMap.t

module type TacticianStructures = sig
  type term
  val term_sexpr : term -> sexpr
  val term_repr  : term -> constr

  type proof_state
  val proof_state_hypotheses  : proof_state -> (id * term option * term) list
  val proof_state_goal        : proof_state -> term
  val proof_state_equal       : proof_state -> proof_state -> bool
  val proof_state_independent : proof_state -> bool

  type tactic
  val tactic_sexpr           : tactic -> sexpr
  val tactic_repr            : tactic -> glob_tactic_expr
  val tactic_make            : glob_tactic_expr -> tactic
  val tactic_hash            : tactic -> int
  val tactic_local_variables : tactic -> id list
  val tactic_substitute      : tactic -> id_map -> tactic
  val tactic_globally_equal  : tactic -> tactic -> bool

  (* Proof tree with sharing. Behaves as a Directed Acyclic Tree. *)
  type proof_dag =
    | End
    | Step of proof_step
  and proof_step =
    { executions : (proof_state * proof_dag) list
    ; tactic     : tactic }

  type situation =
    { parents  : (proof_state * proof_step) list
    ; siblings : proof_dag
    ; state    : proof_state }
  type outcome =
    { parents  : (proof_state * proof_step) list
    ; siblings : proof_dag
    ; before   : proof_state
    ; after    : proof_state list }

  type prediction =
    { confidence : float
    ; focus      : int
    ; tactic     : tactic }
end

module TS = struct

  type term = constr
  let term_sexpr t = constr2s t
  let term_repr t = t

  type proof_state = (id * term option * term) list * term

  let proof_state_hypotheses ps = fst ps

  let proof_state_goal ps = snd ps

  let proof_state_equal ps1 ps2 = false
  let proof_state_independent ps = false

  type tactic = glob_tactic_expr * int
  let tactic_sexpr (tac, _) = s2s (Pp.string_of_ppcmds (Sexpr.format_oneline (
      Pptactic.pr_glob_tactic Environ.empty_env tac)))
  let tactic_repr (tac, _) = tac
  let tactic_make tac = tac, Hashtbl.hash tac
  let tactic_hash (_, hash) = hash
  let tactic_local_variables (tac, _) = []
  let tactic_substitute tac ls = tac
  let tactic_globally_equal tac1 tac2 = false

  (* Proof tree with sharing. Behaves as a Directed Acyclic Tree. *)
  type proof_dag =
    | End
    | Step of proof_step
  and proof_step =
    { executions : (proof_state * proof_dag) list
    ; tactic     : tactic }

  type situation =
    { parents  : (proof_state * proof_step) list
    ; siblings : proof_dag
    ; state    : proof_state }
  type outcome =
    { parents  : (proof_state * proof_step) list
    ; siblings : proof_dag
    ; before   : proof_state
    ; after    : proof_state list }

  type prediction =
    { confidence : float
    ; focus      : int
    ; tactic     : tactic }
end

let goal_to_proof_state ps =
  let map = Goal.sigma ps in
  let to_term t = EConstr.to_constr ~abort_on_undefined_evars:false map t in
  let goal = to_term (Goal.concl ps) in
  let hyps = List.map (function
      | Context.Named.Declaration.LocalAssum (id, typ) ->
        (id.binder_name, None, to_term typ)
      | Context.Named.Declaration.LocalDef (id, term, typ) ->
        (id.binder_name, Some (to_term term), to_term typ))
      (Proofview.Goal.hyps ps) in
  (hyps, goal)

module type TacticianOnlineLearnerType =
  functor (TS : TacticianStructures) -> sig
    open TS
    type model
    val empty    : unit -> model
    val learn    : model -> outcome list -> tactic -> model (* TODO: Add lemma dependencies *)
    val predict  : model -> situation list -> prediction Stream.t (* TODO: Add global environment *)
    val evaluate : model -> outcome -> tactic -> float * model
  end

module type TacticianOfflineLearnerType =
  functor (TS : TacticianStructures) -> sig
    open TS
    type model
    val add      : outcome list -> tactic -> unit (* TODO: Add lemma dependencies *)
    val train    : unit -> model
    val predict  : model -> situation list -> prediction Stream.t (* TODO: Add global environment *)
    val evaluate : model -> outcome -> tactic -> float
  end

let new_database name (module Learner : TacticianOnlineLearnerType) =
  let module Learner = Learner(TS) in
  let db = Summary.ref ~name:("tactician-db-" ^ name) (Learner.empty ()) in
  ( (fun exes tac -> db := Learner.learn !db exes tac)
  , (fun t -> Learner.predict !db t)
  , (fun outcome tac -> let f, db' = Learner.evaluate !db outcome tac in
    db := db'; f))

module NullLearner : TacticianOnlineLearnerType = functor (_ : TacticianStructures) -> struct
  type model = unit
  let empty () = ()
  let learn  () _ _ = ()
  let predict () _ = Stream.sempty
  let evaluate () _ _ = 0., ()
end

let current_learner = ref (new_database "null" (module NullLearner : TacticianOnlineLearnerType))

let learner_learn p    = let x, _, _ = !current_learner in x p
let learner_predict p  = let _, x, _ = !current_learner in x p
let learner_evaluate p = let _, _, x = !current_learner in x p

let register_online_learner name learner : unit =
  current_learner := new_database name learner

let register_offline_learner name learner : unit = ()
