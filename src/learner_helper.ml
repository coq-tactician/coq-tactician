open Tactic_learner
open Sorts
open EConstr
open Constr
open Names
open Context

let rec format_oneline t =
  let open Pp in
  let d = repr t in
  let d' = match d with
  | Ppcmd_glue ls -> Ppcmd_glue (List.map format_oneline ls)
  | Ppcmd_force_newline -> Ppcmd_print_break (1, 0)
  | Ppcmd_box (bl, d') -> Ppcmd_box (bl, format_oneline d')
  | Ppcmd_tag (tag, d') -> Ppcmd_tag (tag, format_oneline d')
  | Ppcmd_comment _ -> assert false (* not expected *)
  | Ppcmd_string s -> if String.contains s '\n' then (print_endline s; assert false) (* can happen but is problematic *) else d
  | _ -> d in
  h 0 (unrepr d')

let string_to_sentence str = Node (str, [])

let global_to_sentence g =
  string_to_sentence (Libnames.string_of_path (Nametab.path_of_global (Globnames.canonical_gr g)))

let esorts_to_sentences s map =
  match EConstr.ESorts.kind map s with
  | SProp  -> [string_to_sentence "SProp"]
  | Prop   -> [string_to_sentence "Prop"]
  | Set    -> [string_to_sentence "Set"]
  | Type l -> [string_to_sentence "Type"; (* TODO: Printing is not optimal here *)
               string_to_sentence (Pp.string_of_ppcmds (format_oneline (Univ.Universe.pr l)))]

let einstance_to_sentences i map =
  let levels = Univ.Instance.to_array (EInstance.kind map i) in
  Array.to_list (Array.map (fun l -> string_to_sentence (Univ.Level.to_string l)) levels)

let cast_kind_to_sentence = function
  | VMcast -> string_to_sentence "VMcast"
  | NATIVEcast -> string_to_sentence "NATIVEcast"
  | DEFAULTcast -> string_to_sentence "DEFAULTcast"
  | REVERTcast -> string_to_sentence "REVERTcast"

let relevance_to_sentence = function
  | Relevant -> string_to_sentence "Relevant"
  | Irrelevant -> string_to_sentence "Irrelevant"

let name_to_sentence = function (* TODO: This may not be optimal *)
  | Name.Anonymous -> string_to_sentence "_"
  | Name.Name id -> string_to_sentence (Id.to_string id)

let constant_to_sentence c = global_to_sentence (GlobRef.ConstRef c)

let inductive_to_sentences i =
  [global_to_sentence (GlobRef.IndRef i); string_to_sentence (string_of_int (snd i))]

let constructor_to_sentences c =
  global_to_sentence (GlobRef.ConstructRef c) :: inductive_to_sentences (fst c)

let case_info_to_sentences {ci_ind; ci_npar; ci_cstr_ndecls; ci_cstr_nargs; ci_relevance; ci_pp_info} =
  inductive_to_sentences ci_ind (* TODO: More info? *)

let econstr_to_sentence t map =
  let rec aux t =
    match EConstr.kind map t with
    | Rel n -> Node ("Rel", [string_to_sentence (string_of_int n)]) (* TODO: Add name and De Bruijn index *)
    | Var id -> Node ("Var", [string_to_sentence (Id.to_string id)])
    | Meta n -> Node ("Meta", [string_to_sentence (string_of_int n)])
    | Evar (evar, constrs) ->
      let sentences = Array.to_list (Array.map aux constrs) in
      Node ("Evar", string_to_sentence (string_of_int (Evar.repr evar)) :: sentences)
    | Sort s -> Node ("Sort", esorts_to_sentences s map)
    | Cast (t', kind, typ) -> Node ("Cast", [aux t'; cast_kind_to_sentence kind; aux typ])
    | Prod (id, typ, body) ->
      Node ("Prod", [ name_to_sentence id.binder_name; relevance_to_sentence id.binder_relevance
                    ; aux typ; aux body])
    | Lambda (id, typ, body) ->
      Node ("Lambda", [ name_to_sentence id.binder_name; relevance_to_sentence id.binder_relevance
                      ; aux typ; aux body])
    | LetIn (id, body1, typ, body2) ->
      Node ("LetIn", [ name_to_sentence id.binder_name; relevance_to_sentence id.binder_relevance
                     ; aux body1; aux typ; aux body2])
    | App (head, args) -> Node ("App", aux head :: Array.to_list (Array.map aux args))
    | Const (c, u) -> Node ("Const", constant_to_sentence c :: einstance_to_sentences u map)
    | Ind (i, u) -> Node ("Ind", inductive_to_sentences i @ einstance_to_sentences u map)
    | Construct (c, u) -> Node ("Construct", constructor_to_sentences c @ einstance_to_sentences u map)
    | Case (info, t1, t2, bodies) ->
      Node ("Case", case_info_to_sentences info @ [aux t1; aux t2] @ Array.to_list (Array.map aux bodies))
    | Fix (_, pd) -> Node ("Fix", prec_declaration_to_sentences pd)
    | CoFix (_, pd) -> Node ("CoFix", prec_declaration_to_sentences pd)
    | Proj (proj, trm) -> Node ("Proj", [string_to_sentence (Projection.to_string proj); aux trm]) (* TODO: Improve *)
    | Int n -> Node ("Int", [string_to_sentence (Uint63.to_string n)])
    | Float n -> Node ("Float", [string_to_sentence (Float64.to_string n)])
  and prec_declaration_to_sentences (ns, typs, trms) =
    [ Node ("Names", Array.to_list (Array.map (fun n -> name_to_sentence (n.binder_name)) ns))
    ; Node ("Types", Array.to_list (Array.map aux typs))
    ; Node ("Terms", Array.to_list (Array.map aux trms))] in
  aux t

let goal_to_proof_state gl =
  let map = Proofview.Goal.sigma gl in
  let goal = econstr_to_sentence (Proofview.Goal.concl gl) map in
  let hyps =
    List.map (function
           | Context.Named.Declaration.LocalAssum (id, typ) ->
             (mk_id id.binder_name,
              Node ("LocalAssum", [econstr_to_sentence typ map]))
           | Context.Named.Declaration.LocalDef (id, term, typ) ->
             (mk_id id.binder_name,
              Node ("LocalDef", [econstr_to_sentence term map; econstr_to_sentence typ map])))
      (Proofview.Goal.hyps gl) in
  {hypotheses = hyps; goal = goal}

let quote s = "\"" ^ s ^ "\""

let rec sentence_to_sexpr = function
  | Node (str, []) -> str
  | Node (str, ls) -> "(" ^ str ^ " " ^ (String.concat " " (List.map sentence_to_sexpr ls)) ^ ")"

let assoc_list_to_json ls pa pb =
  "{" ^ String.concat ", " (List.map (fun (x, y) -> pa x ^ ": " ^ pb y) ls) ^ "}"

let rec sentence_to_json = function
  | Node (str, []) -> quote str
  | Node (str, ls) ->
    "{" ^ quote str ^ ": [" ^ String.concat ", " (List.map sentence_to_json ls) ^ "]}"

let proof_state_to_json {hypotheses; goal} =
  "{\"hypotheses\": " ^ assoc_list_to_json hypotheses
    (fun id -> quote (Names.Id.to_string (id_mk id))) sentence_to_json ^
  ", \"goal\": " ^ sentence_to_json goal ^ "}"

let features term = List.map Hashtbl.hash (Features.extract_features (Hh_term.hhterm_of (Hh_term.econstr_to_constr term)))

let goal_to_proof_state_feats gl =
  let features_sentence typ = List.map (fun x -> string_to_sentence (string_of_int x)) (features typ) in
  let goal = features_sentence (Proofview.Goal.concl gl) in
  let hyps =
    List.map (function
           | Context.Named.Declaration.LocalAssum (id, typ) ->
             (mk_id id.binder_name,
              Node ("LocalAssum", features_sentence typ))
           | Context.Named.Declaration.LocalDef (id, term, typ) ->
             (mk_id id.binder_name,
              Node ("LocalDef", features_sentence term @ features_sentence typ)))
      (Proofview.Goal.hyps gl) in
  {hypotheses = hyps; goal = Node ("Goal", goal)}

(* open Ser_eConstr
 * 
 * let sexp_of_constr_tes = sexp_of_constr *)
