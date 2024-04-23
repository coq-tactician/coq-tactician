open Ltac_plugin
open Tacexpr
open Constr
open Context
open Sexpr
open Proofview
open Tactic_normalize
open Names

type id = Id.t

module IdMap = Map.Make(struct
    type t = Id.t
    let compare = Names.Id.compare
  end)
type id_map = Id.t IdMap.t

let tactic_make tac = tac, Lazy.from_val (Hashtbl.hash_param 255 255 (tactic_normalize tac))

module type TacticianStructures = sig
  type term
  type relevance
  type named_context = (term, term, relevance) Named.pt
  val term_sexpr : term -> sexpr
  val term_repr  : term -> constr

  type proof_state
  val proof_state_hypotheses  : proof_state -> named_context
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
  type relevance = Sorts.relevance
  type named_context = Constr.named_context
  let term_sexpr t = constr2s t
  let term_repr t = t

  type proof_state = named_context * term

  let proof_state_hypotheses ps = fst ps

  let proof_state_goal ps = snd ps

  let proof_state_equal _ps1 _ps2 = false
  let proof_state_independent _ps = false

  type tactic = glob_tactic_expr * int Lazy.t
  let tactic_sexpr (tac, _) = s2s (Pp.string_of_ppcmds (Sexpr.format_oneline (
      Pptactic.pr_glob_tactic Environ.empty_env tac)))
  let tactic_repr (tac, _) = tac
  let tactic_make tac = tactic_make tac
  let tactic_hash (_, hash) = Lazy.force hash
  let tactic_local_variables (_tac, _) = []
  let tactic_substitute tac _ls = tac
  let tactic_globally_equal _tac1 _tac2 = false

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

let calculate_deps sigma acc e =
  let rec aux e acc =
    if Evar.Set.mem e acc then acc else
      Evar.Set.fold aux
        (Evd.evars_of_filtered_evar_info sigma @@ Evd.find_undefined sigma e)
        (Evar.Set.add e acc)
  in aux e acc

let goal_to_proof_state ps =
  let map = Goal.sigma ps in
  let to_term t = EConstr.to_constr ~abort_on_undefined_evars:false map t in
  let goal = to_term (Goal.concl ps) in
  let hyps = EConstr.Unsafe.to_named_context (Proofview.Goal.hyps ps) in
  (hyps, goal)

type data_status =
  | Original
  | QedTime
  | Substituted of Libnames.full_path (* path of the substituted constant (does not exist) *)
  | Discharged of Libnames.full_path (* path of the substituted constant (does not exist) *)

type origin = KerName.t * Libnames.full_path * data_status

type data_in = { outcomes : TS.outcome list; tactic : TS.tactic ; name : Constant.t; status : data_status; path : Libnames.full_path }

module type TacticianOnlineLearnerType =
  functor (TS : TacticianStructures) -> sig
    open TS
    type model
    val empty    : unit -> model
    val learn    : model -> origin -> outcome list -> tactic -> model (* TODO: Add lemma dependencies *)
    val predict  : model -> situation list -> prediction IStream.t (* TODO: Add global environment *)
    val evaluate : model -> outcome -> tactic -> float * model
  end

module type TacticianOfflineLearnerType =
  functor (TS : TacticianStructures) -> sig
    open TS
    type model
    val add      : origin -> outcome list -> tactic -> unit (* TODO: Add lemma dependencies *)
    val train    : unit -> model
    val predict  : model -> situation list -> prediction IStream.t (* TODO: Add global environment *)
    val evaluate : model -> outcome -> tactic -> float
  end

type functional_learner =
  { learn : origin -> TS.outcome list -> TS.tactic -> functional_learner
  ; predict : unit -> TS.situation list -> TS.prediction IStream.t
  ; evaluate : TS.outcome -> TS.tactic -> functional_learner * float }

type imperative_learner =
  { imp_learn : origin -> TS.outcome list -> TS.tactic -> unit
  ; imp_predict : unit -> TS.situation list -> TS.prediction IStream.t
  ; imp_evaluate : TS.outcome -> TS.tactic -> float
  ; functional : unit -> functional_learner }

let new_learner name (module Learner : TacticianOnlineLearnerType) =
  let module Learner = Learner(TS) in
  let rec functional model =
    { learn = (fun origin exes tac ->
          functional @@ Learner.learn model origin exes tac)
    ; predict = (fun () ->
          let predictor = Learner.predict model in
          fun t -> predictor t)
    ; evaluate = (fun outcome tac ->
          let f, model = Learner.evaluate model outcome tac in
          functional @@ model, f) } in

  (* Note: This is lazy to give people a chance to set GOptions before a learner gets initialized *)
  let model = Summary.ref
      ~name:("tactician-model-" ^ name)
      (lazy (Learner.empty ())) in

  { imp_learn = (fun origin exes tac ->
        model := Lazy.from_val @@ Learner.learn (Lazy.force !model) origin exes tac)
  ; imp_predict = (fun () ->
        let predict = Learner.predict (Lazy.force !model) in
        fun t -> predict t)
  ; imp_evaluate = (fun outcome tac ->
        let f, m = Learner.evaluate (Lazy.force !model) outcome tac in
        model := Lazy.from_val m; f)
  ; functional = (fun () -> functional (Lazy.force !model)) }

module NullLearner : TacticianOnlineLearnerType = functor (_ : TacticianStructures) -> struct
  type model = unit
  let empty () = ()
  let learn  () _ _ _ = ()
  let predict () _ = IStream.empty
  let evaluate () _ _ = 0., ()
end

let current_learner = ref (new_learner "null-learner" (module NullLearner : TacticianOnlineLearnerType))

let queue_enabled = Summary.ref ~name: "tactician-queue-enabled" true
let queue = Summary.ref ~name:"tactician-queue" []

let learner_learn status outcomes tactic =
  !current_learner.imp_learn status outcomes tactic

let process_queue () =
  List.iter (fun (s, o, t) -> learner_learn s o t) (List.rev !queue); queue := []

let learner_get () =
  process_queue ();
  !current_learner.functional ()

let learner_learn s o t =
  if !queue_enabled then
    queue := (s, o, t)::!queue
  else
    learner_learn s o t

let disable_queue () =
  process_queue (); queue_enabled := false

let register_online_learner name learner : unit =
  current_learner := new_learner name learner

let register_offline_learner _name _learner : unit = ()
