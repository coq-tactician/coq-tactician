open Tactic_learner
open Context

module L (TS: TacticianStructures) = struct
  open TS

  let rec sexpr_to_string = function
    | Leaf str -> str
    | Node ls -> "(" ^ (String.concat " " (List.map sexpr_to_string ls)) ^ ")"

  let warn term = Feedback.msg_warning (Pp.str ("Tactician did not know how to handle something. Please report."
                                                ^ sexpr_to_string term))

  let replicate x n =
    let rec aux n ls =
      if n <= 0 then ls else aux (n - 1) (x::ls) in
    aux n []

  let rec last = function
    | [] -> assert false
    | [x] -> x
    | _::ls -> last ls

  let rec removelast = function
    | [] -> assert false
    | [x] -> []
    | x::ls -> x :: removelast ls

  let term_sexpr_to_features maxlength term =
    let atomtypes = ["Evar"; "Rel"; "Construct"; "Ind"; "Const"; "Var"; "Int"; "Float"] in
    let is_atom nodetype = List.exists (String.equal nodetype) atomtypes in
    let atom_to_string atomtype content = match atomtype, content with
      | "Rel", _ -> "R"
      | "Evar", (Leaf i :: _) -> "E"
      | "Construct", Leaf c :: _
      | "Ind", Leaf c :: _
      | "Var", Leaf c :: _
      | "Const", Leaf c :: _ -> c
      | "Int", Leaf c :: _ -> "i" ^ c
      | "Float", Leaf c :: _ -> "f" ^ c
      | _, _ -> warn (Leaf "KAK"); "*"
    in

    (* for a tuple `(interm, acc)`:
       - `interm` is an intermediate list of list of features that are still being assembled
         invariant: `forall i ls, 0<i<=maxlength -> In ls (List.nth (i - 1)) -> List.length ls = i`
       - `acc`: accumulates features that are fully assembled *)
    let add_atom atomtype content (interm, acc) =
      let atom = atom_to_string atomtype content in
      let interm' = [[atom]] :: List.map (List.map (fun fs -> atom::fs)) interm in
      (removelast interm', List.flatten interm' @ acc) in

    let set_interm (interm, acc) x = x, acc in
    let start = replicate [] (maxlength - 1) in
    let reset_interm f = set_interm f start in
    let rec aux_reset f term = reset_interm (aux (reset_interm f) term)
    and aux_reset_fold f terms = List.fold_left aux_reset f terms
    and aux ((interm, acc) as f) term = match term with

      (* Interesting leafs *)
      | Node (Leaf nt :: ls) when is_atom nt ->
        add_atom nt ls f

      (* Uninteresting leafs *)
      | Node (Leaf "Sort" :: _)
      | Node (Leaf "Meta" :: _) -> f

      (* Recursion for grammar we don't handle *)
      (* TODO: Handle binders with feature substitution *)
      | Node [Leaf "LetIn"; id; _; body1; typ; body2] ->
        aux_reset_fold f [body1; typ; body2]
      | Node (Leaf "Case" :: _ :: term :: typ :: cases) ->
        aux_reset_fold f (term::typ::cases)
      | Node [Leaf "Fix"; _; Node types; Node terms]
      | Node [Leaf "CoFix"; _ ; Node types; Node terms] ->
        aux_reset_fold f (terms @ types)
      (* TODO: Handle implication separately *)
      | Node [Leaf "Prod"  ; _; _; typ; body]
      | Node [Leaf "Lambda"; _; _; typ; body] -> aux_reset_fold f [typ; body]

      (* The golden path *)
      | Node [Leaf "Proj"; p; term] -> aux (add_atom "Const" [p] f) term
      | Node (Leaf "App" :: head :: args) ->
        let interm', _ as f' = aux f head in
        (* We reset back to `interm'` for every arg *)
        reset_interm (List.fold_left (fun f' t -> set_interm (aux f' t) interm') f' args)
      | Node [Leaf "Cast"; term; _; typ] ->
        (* We probably want to have the type of the cast, but isolated *)
        aux (set_interm (aux (reset_interm f) typ) interm) term

      (* Hope and pray *)
      | term -> warn term; f
    in
    let _, res = aux (start, []) term in
    List.map (String.concat "-") res

  let proof_state_to_features max_length ps =
    let hyps = proof_state_hypotheses ps in
    let goal = proof_state_goal ps in
    let mkfeats t = term_sexpr_to_features max_length (term_sexpr t) in
    (* TODO: distinquish goal features from hyp features *)
    let hyp_feats = List.map (function
        | Named.Declaration.LocalAssum (_, typ) ->
          mkfeats typ
        | Named.Declaration.LocalDef (_, term, typ) ->
          mkfeats typ @ mkfeats term)
        hyps in
    mkfeats goal @ List.flatten hyp_feats

  let context_map f g =
    List.map (function
        | Named.Declaration.LocalAssum (id, typ) ->
          Named.Declaration.LocalAssum (id, f typ)
        | Named.Declaration.LocalDef (id, term, typ) ->
          Named.Declaration.LocalDef (id, g term, f typ))
      
  let context_features max_length ctx =
    let mkfeats t = term_sexpr_to_features max_length (term_sexpr t) in
    context_map mkfeats mkfeats ctx

  let s2s s = Leaf s

  let proof_state_to_sexpr ps =
    let goal = proof_state_goal ps in
    let hyps = proof_state_hypotheses ps in
    let hyps = List.map (function
        | Named.Declaration.LocalAssum (id, typ) ->
          Node (s2s (Names.Id.to_string id.binder_name) :: term_sexpr typ :: [])
        | Named.Declaration.LocalDef (id, term, typ) ->
          Node (s2s (Names.Id.to_string id.binder_name) :: term_sexpr typ :: [term_sexpr term]))
         hyps in
    Node [s2s "State"; Node [s2s "Goal"; term_sexpr goal]; Node [s2s "Hypotheses"; Node hyps]]

  let proof_state_to_string ps env evar_map =
    let constr_str t = Pp.string_of_ppcmds (Sexpr.format_oneline (
        Printer.pr_constr_env env evar_map (term_repr t))) in
    let goal = constr_str (proof_state_goal ps) in
    let hyps = proof_state_hypotheses ps in
    let id_str id = Names.Id.to_string id.binder_name in
    let hyps = List.map (function
        | Named.Declaration.LocalAssum (id, typ) ->
          id_str id ^ " : " ^ constr_str typ
        | Named.Declaration.LocalDef (id, term, typ) ->
          id_str id ^ " := " ^ constr_str term ^ " : " ^ constr_str typ
      ) hyps in
    String.concat ", " hyps ^ " |- " ^ goal
end
