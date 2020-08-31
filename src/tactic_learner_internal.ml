open Ltac_plugin
open Context
open Names

module Id = Names.Id

type id = Id.t

module IdMap = Map.Make(struct
    type t = Id.t
    let compare = Names.Id.compare
  end)
type id_map = Id.t IdMap.t

type sentence = Node of sentence list | Leaf of string

type proof_state =
{ hypotheses : (id * sentence) list
; goal       : sentence }

type tactic = Ltac_plugin.Tacexpr.glob_tactic_expr
let tactic_sentence t =  Leaf (Pp.string_of_ppcmds (Pptactic.pr_glob_tactic Environ.empty_env t))
let local_variables t = []
let substitute t map = t

module type TacticianLearnerType = sig
  type t
  val create  : unit -> t
  val add     : t -> memory:tactic list ->
                     before:proof_state list ->
                            tactic ->
                      after:proof_state list -> t
  val predict : t -> proof_state list -> (float * bool list * tactic) list
end

module NullLearner : TacticianLearnerType = struct
    type t = unit
    let create () = ()
    let add db ~memory:_ ~before:_ tac ~after:_ = ()
    let predict db ls = []
  end

let new_database name (module Learner : TacticianLearnerType) =
  let db = Summary.ref ~name:("tactician-db-" ^ name) (Learner.create ()) in
  ( (fun ~memory:m ~before:b tac ~after:a -> db := Learner.add !db ~memory:m ~before:b tac ~after:a)
  , (fun t -> Learner.predict !db t))

let current_learner = ref (new_database "null" (module NullLearner : TacticianLearnerType))

let learner_add ~memory:m ~before:b tac ~after:a = fst !current_learner ~memory:m ~before:b tac ~after:a
let learner_predict ps  = snd !current_learner ps

let register_learner (name : string) (learner : (module TacticianLearnerType)) : unit =
  current_learner := new_database name learner

let features term = List.map Hashtbl.hash (Features.extract_features
                                             (Hh_term.hhterm_of (Hh_term.econstr_to_constr term)))

let s2s s = Leaf s

let id2s id = s2s (Id.to_string id)

let name2s = function
  | Anonymous -> s2s "_"
  | Name id   -> id2s id

let goal_to_proof_state_feats gl =
  let features_sentence typ = Node (List.map (fun x -> s2s (string_of_int x)) (features typ)) in
  let goal = features_sentence (Proofview.Goal.concl gl) in
  let hyps =
    List.map (function
           | Context.Named.Declaration.LocalAssum (id, typ) ->
             (id.binder_name,
              Node [s2s "LocalAssum"; features_sentence typ])
           | Context.Named.Declaration.LocalDef (id, term, typ) ->
             (id.binder_name,
              Node [s2s "LocalDef"; features_sentence term; features_sentence typ]))
      (Proofview.Goal.hyps gl) in
  {hypotheses = hyps; goal = goal}
