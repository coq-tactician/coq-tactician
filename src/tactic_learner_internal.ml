open Ltac_plugin
open Names
open Constr
open Sorts
open Context
open EConstr

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

type tactic = Ltac_plugin.Tacexpr.glob_tactic_expr * int
let tactic_sentence t =  Leaf (Pp.string_of_ppcmds (Pptactic.pr_glob_tactic Environ.empty_env (fst t)))
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

let s2s s = Leaf s

let id2s id = s2s (Id.to_string id)

let name2s = function
  | Anonymous -> s2s "_"
  | Name id   -> id2s id

let rec format_oneline t =
  let open Pp in
  let d = repr t in
  let d' = match d with
  | Ppcmd_glue ls -> Ppcmd_glue (List.map format_oneline ls)
  | Ppcmd_force_newline -> Ppcmd_print_break (1, 0)
  | Ppcmd_box (bl, d') -> Ppcmd_box (bl, format_oneline d')
  | Ppcmd_tag (tag, d') -> Ppcmd_tag (tag, format_oneline d')
  | Ppcmd_comment _ -> assert false (* not expected *)
  (* can happen but is problematic *)
  | Ppcmd_string s -> if String.contains s '\n' then (print_endline s; assert false) else d
  | _ -> d in
  h 0 (unrepr d')

let global2s g = s2s (Libnames.string_of_path (Nametab.path_of_global (Globnames.canonical_gr g)))

let esorts2s s map =
  match EConstr.ESorts.kind map s with
  | SProp  -> [s2s "SProp"]
  | Prop   -> [s2s "Prop"]
  | Set    -> [s2s "Set"]
  | Type l -> [s2s "Type"; (* TODO: Printing is not optimal here *)
               s2s (Pp.string_of_ppcmds (format_oneline (Univ.Universe.pr l)))]

let einstance2s i map =
  let levels = Univ.Instance.to_array (EInstance.kind map i) in
  Array.to_list (Array.map (fun l -> s2s (Univ.Level.to_string l)) levels)

let cast_kind2s = function
  | VMcast -> s2s "VMcast"
  | NATIVEcast -> s2s "NATIVEcast"
  | DEFAULTcast -> s2s "DEFAULTcast"
  | REVERTcast -> s2s "REVERTcast"

let relevance2s = function
  | Relevant -> s2s "Relevant"
  | Irrelevant -> s2s "Irrelevant"

let constant2s c = global2s (GlobRef.ConstRef c)

let inductive2s i = global2s (GlobRef.IndRef i)

let constructor2s c =
  [global2s (GlobRef.ConstructRef c); inductive2s (fst c)]

let case_info2s {ci_ind; ci_npar; ci_cstr_ndecls; ci_cstr_nargs; ci_relevance; ci_pp_info} =
  inductive2s ci_ind (* TODO: More info? *)

let econstr_to_glob_constr t env sigma =
  Detyping.detype Detyping.Later false Id.Set.empty env sigma t

(* Note: De Bruijn calculations may be different from Coq's calculations *)
let rec debruijn_to_id n ls = if (n - 1) > 0 then debruijn_to_id (n - 1) (List.tl ls) else if ls == [] then (print_endline (string_of_int n); Names.Name.mk_name (Names.Id.of_string "kAK")) else List.hd ls

let econstr2s t map =
  let rec aux (ls : Name.t list) t =
    match EConstr.kind map t with
    (* TODO: Verify correctness of debruijn_to_id *)
    | Rel n -> Node [s2s "Rel"; s2s (string_of_int n); name2s (debruijn_to_id n ls)]
    | Var id -> Node [s2s "Var"; id2s id]
    | Meta n -> Node [s2s "Meta"; s2s (string_of_int n)]
    | Evar (evar, constrs) ->
      (* I would think that `constrs` is always empty *)
      let sentences = Array.to_list (Array.map (aux ls) constrs) in
      Node (s2s "Evar" :: s2s (string_of_int (Evar.repr evar)) :: sentences)
    | Sort s -> Node (s2s "Sort" :: esorts2s s map)
    | Cast (t', kind, typ) -> Node [s2s "Cast"; aux ls t'; cast_kind2s kind; aux ls typ]
    | Prod (id, typ, body) ->
      Node [ s2s "Prod"; name2s id.binder_name; relevance2s id.binder_relevance; aux ls typ
           ; aux (id.binder_name::ls) body]
    | Lambda (id, typ, body) ->
      Node [ s2s "Lambda"; name2s id.binder_name; relevance2s id.binder_relevance; aux ls typ
           ; aux (id.binder_name::ls) body]
    | LetIn (id, body1, typ, body2) ->
      Node [ s2s "LetIn"; name2s id.binder_name; relevance2s id.binder_relevance
           ; aux ls body1; aux ls typ; aux (id.binder_name::ls) body2]
    | App (head, args) -> Node (s2s "App" :: aux ls head :: Array.to_list (Array.map (aux ls) args))
    | Const (c, u) -> Node (s2s "Const" :: constant2s c :: einstance2s u map)
    | Ind (i, u) -> Node (s2s "Ind" :: inductive2s i :: einstance2s u map)
    | Construct (c, u) -> Node (s2s "Construct" :: constructor2s c @ einstance2s u map)
    | Case (info, t1, t2, bodies) ->
      Node (s2s "Case" :: case_info2s info :: aux ls t1 :: aux ls t2
           :: Array.to_list (Array.map (aux ls) bodies))
    | Fix (_, pd) -> Node (s2s "Fix" :: prec_declaration2s ls pd)
    | CoFix (_, pd) -> Node (s2s "CoFix" :: prec_declaration2s ls pd)
    | Proj (proj, trm) -> Node [s2s "Proj"; constant2s (Projection.constant proj); aux ls trm] (* TODO: Improve *)
    | Int n -> Node [s2s "Int"; s2s (Uint63.to_string n)]
    | Float n -> Node [s2s "Float"; s2s (Float64.to_string n)]
  and prec_declaration2s ls (ns, typs, trms) =
    let ids = Array.to_list (Array.map (fun n -> n.binder_name) ns) in
    [ Node (List.map name2s ids)
    ; Node (Array.to_list (Array.map (aux ls) typs))
    (* TODO: Check if this ordering of bound variables is correct *)
    ; Node (Array.to_list (Array.map (aux (ids@ls)) trms))] in
  aux [] t

let goal_to_proof_state gl =
  let map = Proofview.Goal.sigma gl in
  let goal = econstr2s (Proofview.Goal.concl gl) map in
  let hyps =
    List.map (function
           | Context.Named.Declaration.LocalAssum (id, typ) ->
             (id.binder_name,
              Node [s2s "LocalAssum"; econstr2s typ map])
           | Context.Named.Declaration.LocalDef (id, term, typ) ->
             (id.binder_name,
              Node [s2s "LocalDef"; econstr2s term map; econstr2s typ map]))
      (Proofview.Goal.hyps gl) in
  {hypotheses = hyps; goal = goal}

let quote s = "\"" ^ s ^ "\""


let rec sentence_to_sexpr = function
  | Leaf str -> str
  | Node ls -> "(" ^ (String.concat " " (List.map sentence_to_sexpr ls)) ^ ")"

let assoc_list_to_json ls pa pb =
  "{" ^ String.concat ", " (List.map (fun (x, y) -> pa x ^ ": " ^ pb y) ls) ^ "}"

let rec sentence_to_json = function
  | Leaf str -> quote str
  | Node ls -> "[" ^ String.concat ", " (List.map sentence_to_json ls) ^ "]"

let proof_state_to_json {hypotheses; goal} =
  "{\"hypotheses\": " ^ assoc_list_to_json hypotheses
    (fun id -> quote (Id.to_string id)) sentence_to_json ^
  ", \"goal\": " ^ sentence_to_json goal ^ "}"

let features term = List.map Hashtbl.hash (Features.extract_features
                                             (Hh_term.hhterm_of (Hh_term.econstr_to_constr term)))

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
