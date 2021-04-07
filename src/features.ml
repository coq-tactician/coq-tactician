open Tactic_learner
open Context
open Learner_helper

type feat_kind = Struct | Seman | Verti
type proof_state_part = Goal | Hyps
(* int means the depth of the beginning of the semantic features *)

module F (TS: TacticianStructures) = struct
  module LH = L(TS)
  open LH
  open TS

  let term_sexpr_to_simple_features maxlength term =
    let atomtypes = ["Evar"; "Rel"; "Construct"; "Ind"; "Const"; "Var"; "Int"; "Float"] in
    let is_atom nodetype = List.exists (String.equal nodetype) atomtypes in
    let atom_to_string atomtype content = match atomtype, content with
      | "Rel", _ -> "R"
      | "Evar", (Leaf _ :: _) -> "E"
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

    let set_interm (_interm, acc) x = x, acc in
    let start = replicate [] (maxlength - 1) in
    let reset_interm f = set_interm f start in
    let rec aux_reset f term = reset_interm (aux (reset_interm f) term)
    and aux_reset_fold f terms = List.fold_left aux_reset f terms
    and aux ((interm, _acc) as f) term = match term with

      (* Interesting leafs *)
      | Node (Leaf nt :: ls) when is_atom nt ->
        add_atom nt ls f

      (* Uninteresting leafs *)
      | Node (Leaf "Sort" :: _)
      | Node (Leaf "Meta" :: _) -> f

      (* Recursion for grammar we don't handle *)
      (* TODO: Handle binders with feature substitution *)
      | Node [Leaf "LetIn"; _id; _; body1; typ; body2] ->
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

  let disting_hyps_goal ls symbol =
    List.map (fun (feat_kind, feat) -> feat_kind, symbol ^ feat) ls

  let get_top_interm interm =
    let flat_interm = List.flatten interm in
    if flat_interm <> [] then
      List.nth flat_interm (List.length flat_interm -1)
    else
      []
    (* List.hd (List.rev flat_interm)  *)
  let rep_elem n elem =
    let rec rep_elem_aux acc n elem =
      if n = 0 then acc else rep_elem_aux (elem :: acc) (n-1) elem
    in
    rep_elem_aux [] n elem

  let proof_state_to_simple_features max_length ps =
    let hyps = proof_state_hypotheses ps in
    let goal = proof_state_goal ps in
    let mkfeats t = term_sexpr_to_simple_features max_length (term_sexpr t) in
    (* TODO: distinquish goal features from hyp features *)
    let hyp_feats = List.map (function
        | Named.Declaration.LocalAssum (_, typ) ->
          mkfeats typ
        | Named.Declaration.LocalDef (_, term, typ) ->
          mkfeats typ @ mkfeats term)
        hyps in
    mkfeats goal @ List.flatten hyp_feats

  let context_simple_features max_length ctx =
    let mkfeats t = term_sexpr_to_simple_features max_length (term_sexpr t) in
    context_map mkfeats mkfeats ctx

  let proof_state_to_simple_ints ps =
    let feats = proof_state_to_simple_features 2 ps in
    (* print_endline (String.concat ", " feats); *)

    (* Tail recursive version of map, because these lists can get very large. *)
    let feats = List.rev (List.rev_map Hashtbl.hash feats) in
    List.sort_uniq Int.compare feats



(*TODO: Every variable is renamed to a textual representation of its type*)

  let term_sexpr_to_complex_features maxlength term =
    let atomtypes = ["Evar"; "Rel"; "Construct"; "Ind"; "Const"; "Var"; "Int"; "Float"] in
    let is_atom nodetype = List.exists (String.equal nodetype) atomtypes in
    let atom_to_string atomtype content = match atomtype, content with
      | "Rel", _ -> "R"
      | "Evar", (Leaf _ :: _) -> "E"
      | "Construct", Leaf c :: _
      | "Ind", Leaf c :: _ -> c
      | "Var", Leaf c :: _ -> c
      | "Const", Leaf c :: _ -> c
      | "Int", Leaf c :: _ -> "i" ^ c
      | "Float", Leaf c :: _ -> "f" ^ c
      | _, _ -> warn (Leaf "KAK"); "*"
    in
    let wrap_partness str_list = ["("] @ str_list @ [")"] in
    let node_type = ["Sort"; "Meta"; "LetIn"; "Case"; "Fix"; "CoFix";"Prod"; "Lambda"; "Proj"; "App";"Cast"] in
    let is_correct_node node =
      if List.mem node node_type
      then true
      else false in
    let rec aux_struct term depth =
      if depth > 2 then
        match term with
        | Node (Leaf nt :: _) when is_atom nt -> ["X"]
        | Node (Leaf node :: _)  ->
          if is_correct_node node then ["X"] else (warn term; ["Error"])
        | _ -> warn term; ["Error"]
      else
        match term with
        (* Interesting leafs *)
        | Node (Leaf nt :: _) when is_atom nt ->
          ["X"]
        (* Uninteresting leafs *)
        | Node (Leaf "Sort" :: _)
        | Node (Leaf "Meta" :: _) -> []
        | Node [Leaf "LetIn"; _; _; body1; typ; body2] ->
          struct_feat_fold "LetIn" [body1; typ; body2] depth
        | Node (Leaf "Case" :: _ :: term :: typ :: cases) ->
          struct_feat_fold "Case" (term::typ::cases) depth
        | Node [Leaf "Fix"; _; Node types; Node terms] ->
          struct_feat_fold "Fix" (types@terms) depth
        | Node [Leaf "CoFix"; _ ; Node types; Node terms] ->
          struct_feat_fold "CoFix" (types@terms) depth
        | Node [Leaf "Prod"  ; _; _; typ; body] ->
          struct_feat_fold "Prod" [typ;body] depth
        | Node [Leaf "Lambda"; _; _; typ; body] ->
          struct_feat_fold "Lambda" [typ;body] depth
        | Node [Leaf "Proj"; p; term] ->
          struct_feat_fold "Proj" [p; term] depth
        | Node (Leaf "App" :: head :: args) ->
          (* List.length args in let *)
          let arg_num = List.length args in
          let func_feat = (aux_struct head (depth + 1)) @ [Stdlib.string_of_int arg_num] in
          let arg_feat = List.fold_left
            (fun struct_feats curr_term -> struct_feats @ aux_struct curr_term (depth + 1))
            [] args in
          wrap_partness ("App" :: (func_feat@arg_feat))
          (* struct_feat_fold "App" (head :: args) depth *)
        | Node [Leaf "Cast"; term; _; typ] ->
          struct_feat_fold "Cast" [term; typ] depth
        (* Hope and pray *)
        | _ -> warn term; ["Error"]
    and struct_feat_fold binder term_list depth =
      wrap_partness
        (List.fold_left (fun struct_feats curr_term -> struct_feats @ aux_struct curr_term (depth + 1))
      [binder] term_list)
    in
    (* for a tuple `(interm, acc)`:
       - `interm` is an intermediate list of list of features that are still being assembled
         invariant: `forall i ls, 0<i<=maxlength -> In ls (List.nth (i - 1)) -> List.length ls = i`
       - `acc`: accumulates features that are fully assembled *)
    let get_atom_with_role atomtype content role =
      let atom = (atom_to_string atomtype content) in
      atom ^":"^role
    in
    let add_atom atomtype content (interm, acc) role =
      let atom_with_role = get_atom_with_role atomtype content role in
      let interm' = [[atom_with_role]] ::
        List.map (List.map (fun fs -> fs @ [atom_with_role])) interm in
      (* use removelast to control the length of terms *)
      (removelast interm', (List.flatten interm' @ acc)) in
    let set_interm (_, acc) x = x, acc in
    let start = replicate [] (maxlength - 1) in
    let reset_interm f = set_interm f start in
    let verti_atom atomtype content (interm, acc) role =
      let atom_with_role = get_atom_with_role atomtype content role in
      let new_interm = interm @ [atom_with_role] in
      (new_interm, acc @ [new_interm]) in
    let rec vert_next_level f term role =
    (* if next node is atom, then add the role to the atom node directly, else
       add role to the current path  *)
      let (original_interm, original_acc) = f in
      match term with
      | Node (Leaf nt :: ls ) when is_atom nt ->
        let _, new_acc = verti_atom nt ls f role in
        (* for f(a,b), interm of (a) should not affect (b). Only acc is changed *)
        (original_interm, new_acc)
      | _ ->
        let new_interm = original_interm @ [role] in
        let f' = (new_interm, original_acc) in
        aux_vert f' term
    and vert_next_level_fold f terms roles =
    List.fold_left (fun f' (term, role) -> vert_next_level f' term role) f (List.combine terms roles)
    and aux_vert f term =
    match term with
      (* Interesting leafs *)
      | Node (Leaf nt :: ls) when is_atom nt ->
        verti_atom nt ls f "Id"
      (* Uninteresting leafs *)
      | Node (Leaf "Sort" :: _)
      | Node (Leaf "Meta" :: _) -> f
      (* Recursion for grammar we don't handle *)
      (* TODO: Handle binders with feature substitution *)
      | Node [Leaf "LetIn"; _; _; body1; typ; body2] ->
        let roles = ["LetVarBody"; "LetVarType"; "LetBody"] in
        vert_next_level_fold f [body1; typ; body2] roles
      | Node (Leaf "Case" :: _ :: term :: typ :: cases) ->
        let roles = (["MatchTerm"; "MatchTermType"] @ (rep_elem (List.length cases) "Case")) in
        vert_next_level_fold f (term::typ::cases) roles
      | Node [Leaf "Fix"; _; Node types; Node terms] ->
        let roles = (rep_elem (List.length terms) "FixTerm")
          @ (rep_elem (List.length types) "FixType") in
        vert_next_level_fold f (terms @ types) roles
      | Node [Leaf "CoFix"; _ ; Node types; Node terms] ->
        let roles = (rep_elem (List.length terms) "CoFixTerm")
          @ (rep_elem (List.length types) "CoFixType") in
        vert_next_level_fold f (terms @ types) roles
      (* TODO: Handle implication separately *)
      | Node [Leaf "Prod"  ; _; _; typ; body] ->
        vert_next_level_fold f [typ; body] ["ProdType"; "ProdBody"]
      | Node [Leaf "Lambda"; _; _; typ; body] ->
        vert_next_level_fold f [typ; body] ["LambdaType"; "LambdaBody"]
      (* The golden path *)
      | Node [Leaf "Proj"; p; term] ->
        let roles = ["ProjConst"; "ProjTerm"] in
        vert_next_level_fold f [p; term] roles
      | Node (Leaf "App" :: head :: args) ->
        let roles = "AppFun" :: (rep_elem (List.length args) "AppArg") in
        vert_next_level_fold f (head::args) roles
      | Node [Leaf "Cast"; term; _; typ] ->
        let roles = ["CastTerm"; "CastType"] in
        vert_next_level_fold f [term; typ] roles
      (* Hope and pray *)
      | term -> warn term; f
    in
    let remove_ident seman_feats =
      List.fold_left (fun acc feat -> if List.length feat < 2 then acc else
      acc @ [feat] ) [] seman_feats
    in
    let rec aux_seman_reset f term role = reset_interm (aux_seman (reset_interm f) term role)
    and aux_seman_reset_fold f terms roles =
    List.fold_left (fun f' (term, role) -> aux_seman_reset f' term role) f (List.combine terms roles)
    and aux_seman ((interm, _) as f) term role=
    match term with
      (* Interesting leafs *)
      | Node (Leaf nt :: ls) when is_atom nt ->
        add_atom nt ls f role
      (* Uninteresting leafs *)
      | Node (Leaf "Sort" :: _)
      | Node (Leaf "Meta" :: _) -> f
      (* Recursion for grammar we don't handle *)
      (* TODO: Handle binders with feature substitution *)
      | Node [Leaf "LetIn"; _; _; body1; typ; body2] ->
        let roles = ["LetVarBody"; "LetVarType"; "LetBody"] in
        aux_seman_reset_fold f [body1; typ; body2] roles
      | Node (Leaf "Case" :: _ :: term :: typ :: cases) ->
        let roles = (["MatchTerm"; "MatchTermType"] @ (rep_elem (List.length cases) "Case")) in
        aux_seman_reset_fold f (term::typ::cases) roles
      | Node [Leaf "Fix"; _; Node types; Node terms] ->
        let roles = (rep_elem (List.length terms) "FixTerm")
          @ (rep_elem (List.length types) "FixType") in
        aux_seman_reset_fold f (terms @ types) roles
      | Node [Leaf "CoFix"; _ ; Node types; Node terms] ->
        let roles = (rep_elem (List.length terms) "CoFixTerm")
          @ (rep_elem (List.length types) "CoFixType") in
        aux_seman_reset_fold f (terms @ types) roles
        (* TODO: Handle implication separately *)
      | Node [Leaf "Prod"  ; _; _; typ; body] ->
        (* let f' = aux_seman f typ "ProdType" in
        aux_seman f' body "ProdBody" *)
        aux_seman_reset_fold f [typ; body] ["ProdType"; "ProdBody"]
      | Node [Leaf "Lambda"; _; _; typ; body] ->
        aux_seman_reset_fold f [typ; body] ["LambdaType"; "LambdaBody"]
        (* The golden path *)
      | Node [Leaf "Proj"; p; term] ->
        aux_seman (add_atom "Const" [p] f "Proj") term "Proj"
      | Node (Leaf "App" :: head :: args) ->
        let interm', _ as f' = aux_seman f head "AppFun" in
        (* We reset back to `interm'` for every arg *)
        reset_interm
          (List.fold_left (fun f' t -> set_interm (aux_seman f' t "AppArg") interm') f' args)
      | Node [Leaf "Cast"; term; _; typ] ->
        (* We probably want to have the type of the cast, but isolated *)
        aux_seman (set_interm (aux_seman (reset_interm f) typ "CastType") interm) term "CastTerm"
      (* Hope and pray *)
      | term -> warn term; f
    in
    let _, vert_feats = aux_vert ([], []) term  in
    let vert_feats = List.map (fun feat -> Verti, "Verti" :: feat) (remove_ident vert_feats) in
    let struct_feats = Struct, "Struct" :: (aux_struct term 0) in
    let _, seman_feats = (aux_seman (start, []) term "Init_Constr") in
    let seman_feats = List.map (fun feat -> Seman, "Seman" :: feat) seman_feats in
    List.map (fun (feat_kind, feats) -> feat_kind, String.concat "-" feats) ((struct_feats::vert_feats) @ seman_feats)

  let proof_state_to_complex_features max_length ps =
    let hyps = proof_state_hypotheses ps in
    let goal = proof_state_goal ps in
    let mkfeats t = term_sexpr_to_complex_features max_length (term_sexpr t) in
    let hyp_id_typ_feats = List.map (function
        | Named.Declaration.LocalAssum (id, typ) ->
          (Names.Id.to_string id.binder_name), (sexpr_to_string (term_sexpr typ)), (mkfeats typ)
        | Named.Declaration.LocalDef (id, term, typ) ->
          (Names.Id.to_string id.binder_name),(sexpr_to_string (term_sexpr typ)), (mkfeats typ @ mkfeats term))
        hyps in
    let hyp_feats = List.map (fun (_, _, feats) -> feats) hyp_id_typ_feats in
    let goal_feats = mkfeats goal in
    (* seperate the goal from the local context *)
    (disting_hyps_goal goal_feats "GOAL-") @ (disting_hyps_goal (List.flatten hyp_feats) "HYPS-")

  let context_features_complex max_length ctx =
    let mkfeats t = term_sexpr_to_complex_features max_length (term_sexpr t) in
    context_map mkfeats mkfeats ctx

  let count_dup l =
    let sl = List.sort compare l in
    match sl with
    | [] -> []
    | hd::tl ->
      let acc,x,c = List.fold_left (fun (acc,x,c) y ->
          if y = x then acc,x,c+1 else (x,c)::acc, y,1) ([],hd,1) tl in
      (x,c)::acc

  let proof_state_to_complex_ints ps =
    let feats = proof_state_to_complex_features 3 ps in
    let feats_with_count_pair = count_dup feats in
    let feats_with_count = List.map (fun ((feat_kind, feat), count) -> feat_kind, feat ^ "-" ^ (Stdlib.string_of_int count))
        feats_with_count_pair in
    (* print_endline (String.concat ", "  (List.map Stdlib.snd feats_with_count)); *)
    (* Tail recursive version of map, because these lists can get very large. *)
    let feats = List.rev (List.rev_map (fun (feat_kind, feat) -> feat_kind, Hashtbl.hash feat) feats_with_count) in
    List.sort_uniq (fun (_, feat1) (_, feat2) -> Int.compare feat1 feat2) feats

  let tfidf size freqs ls1 ls2 =
    let inter = intersect compare ls1 ls2 in
    List.fold_left (+.) 0.
      (List.map
         (fun f -> Float.log ((Float.of_int (1 + size)) /.
                              (Float.of_int (1 + (default 0 (Frequencies.find_opt f freqs))))))
         inter)

  let remove_feat_kind l =
    List.map Stdlib.snd l

  let manually_weighed_tfidf size freq ls1 ls2 =
    let inter = intersect (fun x y -> compare (snd x) y) ls1 ls2 in
    let similarity_for_one_feat feat =
      Float.log ((Float.of_int (1 + size)) /.
                 (Float.of_int (1 + (default 0 (Frequencies.find_opt feat freq)))))
    in
    List.fold_left (+.) 0.
      (List.map
         (fun (feat_kind, f) ->
            if feat_kind == Struct
            then (Float.of_int(2) *. similarity_for_one_feat f)
            else similarity_for_one_feat f)
         inter)

end
