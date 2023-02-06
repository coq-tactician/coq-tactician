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
  type named_context = (term, term) Named.pt
  val term_sexpr : term -> sexpr
  val term_repr  : term -> constr

  type proof_state
  val proof_state_hypotheses  : proof_state -> named_context
  val proof_state_goal        : proof_state -> term
  val proof_state_evar        : proof_state -> Evar.t
  val proof_state_sigma       : proof_state -> Evd.evar_map
  val proof_state_dependent   : proof_state -> Evar.t -> proof_state
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

  type tactic_result
  val tactic_result_term      : tactic_result -> term
  val tactic_result_sigma     : tactic_result -> Evd.evar_map
  val tactic_result_dependent : tactic_result -> Evar.t -> proof_state
  val tactic_result_states    : tactic_result -> proof_state list

  (* Proof tree with sharing. Behaves as a Directed Acyclic Tree. *)
  type proof_dag =
    | End
    | Step of proof_step
  and proof_step =
    { executions : (proof_state * proof_dag) list
    ; tactic     : tactic option }

  type situation =
    { parents  : (proof_state * proof_step) list
    ; siblings : proof_dag
    ; state    : proof_state }
  type outcome =
    { parents  : (proof_state * proof_step) list
    ; siblings : proof_dag
    ; before   : proof_state
    ; result   : tactic_result }

  type prediction =
    { confidence : float
    ; focus      : int
    ; tactic     : tactic }
end

module TS = struct

  type term = constr
  type named_context = Constr.named_context
  let term_sexpr t = constr2s t
  let term_repr t = t

  type hyps_origin = Id.t Id.Map.t
  type single_proof_state =
    { hyps : named_context
    ; goal : term
    ; evar : Evar.t
    ; hyps_origin : hyps_origin }
  type proof_state = single_proof_state Evar.Map.t * UState.t * single_proof_state
  type tactic_result = term * single_proof_state Evar.Map.t * UState.t * single_proof_state list

  let proof_state_hypotheses (_, _, { hyps; _ }) = hyps
  let proof_state_goal (_, _, { goal; _}) = goal
  let proof_state_evar (_, _, { evar; _}) = evar
  let proof_state_hyps_origin (_, _, { hyps_origin; _}) = hyps_origin
  let proof_state_dependent (map, ustate, _) var = map, ustate, Evar.Map.find var map
  let proof_state_sigma ((map, ustate, _) : proof_state) =
    Evar.Map.fold (fun e { hyps; goal; _} evd ->
        Evd.add evd e @@ Evd.make_evar (Environ.val_of_named_context hyps) (EConstr.of_constr goal)) map @@
    Evd.set_universe_context Evd.empty ustate

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

  let tactic_result_term (t, _, _, _) = t
  let tactic_result_sigma (_, map, ustate, _) =
    Evar.Map.fold (fun e { hyps; goal; _} evd ->
        Evd.add evd e @@ Evd.make_evar (Environ.val_of_named_context hyps) (EConstr.of_constr goal)) map @@
    Evd.set_universe_context Evd.empty ustate
  let tactic_result_dependent (_, map, ustate, _) var = map, ustate, Evar.Map.find var map
  let tactic_result_states (_, map, ustate, ls) = List.map (fun ps -> map, ustate, ps) ls

  (* Proof tree with sharing. Behaves as a Directed Acyclic Tree. *)
  type proof_dag =
    | End
    | Step of proof_step
  and proof_step =
    { executions : (proof_state * proof_dag) list
    ; tactic     : tactic option }

  type situation =
    { parents  : (proof_state * proof_step) list
    ; siblings : proof_dag
    ; state    : proof_state }
  type outcome =
    { parents  : (proof_state * proof_step) list
    ; siblings : proof_dag
    ; before   : proof_state
    ; result   : tactic_result }

  type prediction =
    { confidence : float
    ; focus      : int
    ; tactic     : tactic }
end

let evars_of_term sigma acc c =
  let rec evrec acc c =
    match EConstr.kind sigma c with
    | Evar (n, l) -> Evar.Map.add n l (Array.fold_left evrec acc l)
    | _ -> EConstr.fold sigma evrec acc c
  in
  evrec acc c

let evars_of_named_context sigma acc nc =
  Context.Named.fold_outside
    (Context.Named.Declaration.fold_constr (fun constr acc -> evars_of_term sigma acc constr))
    nc
    ~init:acc

let evars_of_filtered_evar_info sigma acc evi =
    let acc = evars_of_term sigma acc Evd.(evi.evar_concl) in
    let acc = match evi.evar_body with
     | Evar_empty -> acc
     | Evar_defined b -> evars_of_term sigma acc b in
    evars_of_named_context sigma acc (Evd.evar_filtered_context evi)

let update_hyps_origin sigma hyps_origin substs hyps =
  let dest = Array.map
      (fun c ->
         try
           let hyp = EConstr.destVar sigma c in
           Names.Id.Map.find_opt hyp hyps_origin
         with Constr.DestKO -> None) substs in
  List.fold_left2 (fun m source dest ->
      match dest with
      | None -> m
      | Some dest -> Names.Id.Map.add (Context.Named.Declaration.get_id source) dest m)
    Names.Id.Map.empty hyps (Array.to_list dest)

let calculate_deps sigma acc e hyps_origin =
  let rec aux e hyps_origin acc =
    if Evar.Map.mem e acc then acc else
      let evars = evars_of_filtered_evar_info sigma Evar.Map.empty @@ Evd.find_undefined sigma e in
      let evars = Evar.Map.mapi (fun e substs ->
          update_hyps_origin sigma hyps_origin substs
            (Evd.evar_filtered_context @@ Evd.find_undefined sigma e)) evars in
      Evar.Map.fold aux
        evars
        (Evar.Map.add e hyps_origin acc)
  in aux e hyps_origin acc

let evar_to_proof_state sigma evar hyps_origin =
  let info = Evd.find_undefined sigma evar in
  let to_term t = EConstr.to_constr ~abort_on_undefined_evars:false sigma t in
  let hyps = List.map (Tactician_util.map_named to_term) @@ Evd.evar_filtered_context info in
  let goal = to_term @@ Evd.evar_concl info in
  TS.{ hyps; goal; evar; hyps_origin }

type parent_info =
  { hyps_origin : Names.Id.t Names.Id.Map.t
  ; parent_goal : Proofview.Goal.t }
let parent_info_field : parent_info Proofview_monad.StateStore.field = Proofview_monad.StateStore.field ()

let get_hyps_origin ps =
  let state = Goal.state ps in
  match Proofview_monad.StateStore.get state parent_info_field with
  | None -> Names.Id.Map.empty
  | Some { hyps_origin; _ } -> hyps_origin

let goal_to_proof_state ps =
  let e = Goal.goal ps in
  let sigma = Goal.sigma ps in
  let hyps_origin = get_hyps_origin ps in
  let ctx = calculate_deps sigma Evar.Map.empty e hyps_origin in
  let ctx = Evar.Map.mapi (evar_to_proof_state sigma) ctx in
  ctx, Evd.evar_universe_context sigma, Evar.Map.find e ctx

let make_result before term sigma pss =
  let evars = evars_of_term sigma Evar.Map.empty term in
  let hyps_origin = get_hyps_origin before in
  let evars = Evar.Map.mapi (fun e substs ->
      update_hyps_origin sigma hyps_origin substs
        (Evd.evar_filtered_context @@ Evd.find_undefined sigma e)) evars in
  let evars = Evar.Map.fold (fun e ho acc -> calculate_deps sigma acc e ho) evars Evar.Map.empty in
  (* NOTE: This should not be necessary, because all proof states should be reachable from the proof term.
     However, Coq8.11 contains some tactics that wrongly associate some proof states to the wrong tactic.
     In addition the `unshelve` tactic is screwed up. *)
  let evars = List.fold_left
      (fun acc ps -> calculate_deps sigma acc (Goal.goal ps) (get_hyps_origin ps)) evars pss in
  let evars = Evar.Map.mapi (evar_to_proof_state sigma) evars in
  let term = EConstr.to_constr ~abort_on_undefined_evars:false sigma term in
  term, evars, Evd.evar_universe_context sigma, List.map (fun ps -> Evar.Map.find (Goal.goal ps) evars) pss

type data_status =
  | Original
  | QedTime
  | Substituted of Libnames.full_path (* path of the substituted constant (does not exist) *)
  | Discharged of Libnames.full_path (* path of the substituted constant (does not exist) *)

type origin = KerName.t * Libnames.full_path * data_status

type data_in = { outcomes : TS.outcome list; tactic : TS.tactic option ; name : Constant.t; status : data_status; path : Libnames.full_path; sec_vars : Names.Id.Set.t }

module type TacticianOnlineLearnerType =
  functor (TS : TacticianStructures) -> sig
    open TS
    type model
    val empty    : unit -> model
    (* Sometimes we are unable to trace which tactic was executed. Then it is None *)
    val learn    : model -> origin -> outcome list -> tactic option -> model (* TODO: Add lemma dependencies *)
    val predict  : model -> situation list -> prediction IStream.t (* TODO: Add global environment *)
    val evaluate : model -> outcome -> tactic -> float * model
  end

module type TacticianOfflineLearnerType =
  functor (TS : TacticianStructures) -> sig
    open TS
    type model
    (* Sometimes we are unable to trace which tactic was executed. Then it is None *)
    val add      : origin -> outcome list -> tactic option -> unit (* TODO: Add lemma dependencies *)
    val train    : unit -> model
    val predict  : model -> situation list -> prediction IStream.t (* TODO: Add global environment *)
    val evaluate : model -> outcome -> tactic -> float
  end

type functional_learner =
  { learn : origin -> TS.outcome list -> TS.tactic option -> functional_learner
  ; predict : unit -> TS.situation list -> TS.prediction IStream.t
  ; evaluate : TS.outcome -> TS.tactic -> functional_learner * float }

type imperative_learner =
  { imp_learn : origin -> TS.outcome list -> TS.tactic option -> unit
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
