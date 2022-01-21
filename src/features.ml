open Tactic_learner
open Context
open Learner_helper

type feat_kind = Struct | Seman | Verti
type semantic_features = {interm:string list list list; acc:string list list}
(*for `f(g(a), b)` and go to `a`
  walk: the walk from root to `a`
  walk_to_sibiling: walk from root to f such that we can calculate the walk to `b` basing on it*) 
type vertical_features = {walk:string list; acc:string list list} 
type features = {semantic : semantic_features; structure : string list; vertical: vertical_features}

module F (TS: TacticianStructures) = struct
  module LH = L(TS)
  open LH
  open TS

  let warn lterm oterm =
    Feedback.msg_warning (Pp.str ("Tactician did not know how to handle something. Please report. "
                                  ^ sexpr_to_string lterm ^ " : " ^sexpr_to_string oterm))

  let term_sexpr_to_simple_features maxlength oterm =
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
      | _, _ -> warn (Leaf "KAK") oterm; "*"
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
      | term -> warn term oterm; f
    in
    let _, res = aux (start, []) oterm in
    (* We use tail-recursive rev_map instead of map to avoid stack overflows on large proof states *)
    List.rev_map (String.concat "-") res

  let disting_hyps_goal ls symbol =
    (* We use tail-recursive rev_map instead of map to avoid stack overflows on large proof states *)
    List.rev_map (fun (feat_kind, feat) -> feat_kind, symbol ^ feat) ls

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
    let mkfeats t =
      let x = term_sexpr t in
      term_sexpr_to_simple_features max_length (x) in
    (* TODO: distinquish goal features from hyp features *)
    let hyp_feats = List.map (function
        | Named.Declaration.LocalAssum (_, typ) ->
          mkfeats typ
        | Named.Declaration.LocalDef (_, term, typ) ->
          mkfeats typ @ mkfeats term)
        hyps in
    let x = mkfeats goal in
    x @ List.flatten hyp_feats

  let context_simple_features max_length ctx =
    let mkfeats t = term_sexpr_to_simple_features max_length (term_sexpr t) in
    context_map mkfeats mkfeats ctx

  let context_simple_ints ctx =
    let ctx = context_simple_features 2 ctx in

    (* Tail recursive version of map, because these lists can get very large. *)
    let to_ints feats = List.sort_uniq Int.compare (List.rev_map Hashtbl.hash feats) in
    context_map to_ints to_ints ctx

  let proof_state_to_simple_ints ps =
    let feats = proof_state_to_simple_features 2 ps in
    (* print_endline (String.concat ", " feats); *) 
    (* Tail recursive version of map, because these lists can get very large. *)
    let feats = List.rev_map Hashtbl.hash feats in
    List.sort_uniq Int.compare feats
  
  let count_dup l =
    let sl = List.sort compare l in
    match sl with
    | [] -> []
    | hd::tl ->
      let acc,x,c = List.fold_left (fun (acc,x,c) y ->
          if y = x then acc,x,c+1 else (x,c)::acc, y,1) ([],hd,1) tl in
      (x,c)::acc    
      
  let term_sexpr_to_complex_features maxlength oterm =
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
      | _, _ -> warn (Leaf "KAK") oterm; "*"
    in
    (* for a tuple `(interm, acc)`:
       - `interm` is an intermediate list of list of features that are still being assembled
         invariant: `forall i ls, 0<i<=maxlength -> In ls (List.nth (i - 1)) -> List.length ls = i`
       - `acc`: accumulates features that are fully assembled *)
    let add_atom atomtype content features =
      let interm, acc = features.semantic.interm, features.semantic.acc in
      let atom = atom_to_string atomtype content in
      (* `interm` contains term tree walks to maximal depth, maximal depth - 1,..., 1 *)
      let interm' = [[atom]] :: List.map (List.map (fun fs -> atom::fs)) interm in
      (* Remove the last item to keep the maximal depth constraint. 
        The length of `interm` = the maximal depth constraint. 
        The initial `interm` is [[walk],[],...,[]]; thus, `removelast` will remove [] in the beginning *)
      {interm = removelast interm'; acc = List.flatten interm' @ acc} 
    in
    let set_interm features x = {features with semantic = {features.semantic with interm = x}} in
    let set_walk features x = {features with vertical = {features.vertical with walk = x}} in 
    let start = replicate [] (maxlength - 1) in
    let init_features = {semantic = {interm = replicate [] (maxlength - 1); acc = []} ; 
      structure = []; vertical = {walk = []; acc = []}} in
    let reset_interm features = set_interm features start in
    let start_structure features role =
      {features with structure = features.structure @ ["(" ; role]}  
    in 
    let end_structure features =
       {features with structure = features.structure @ [")"] }
    in    
    let verti_atom atomtype content features role =
      if List.length features.vertical.walk == 1 then
        features
      else  
        let atom_with_role = (atom_to_string atomtype content) ^":"^role in 
        {features with vertical = {
          features.vertical with acc = 
          (features.vertical.walk@[atom_with_role]) :: features.vertical.acc 
        }} 
    in  
    let calculate_vertical_features term role features =
      match term with
      | Node (Leaf nt :: ls ) when is_atom nt ->
        let features' = verti_atom nt ls features role in
        features'
      | _ ->
        {features with vertical = {
          features.vertical with walk = (features.vertical.walk@[role])}}
    in    
    let rec aux_reset features (term, role) depth walk =
      let reset_features = reset_interm features in 
      let reset_features = set_walk reset_features walk in
      let features' = aux reset_features term role depth in
      reset_interm features'
    and aux_reset_fold features term_role_pairs depth = 
      let walk = features.vertical.walk in
      let next_level_depth = depth + 1 in
      List.fold_left (fun features' term_role_pair-> 
        aux_reset features' term_role_pair next_level_depth walk) features term_role_pairs 
    and aux features term role depth = 
      let features = calculate_vertical_features term role features in
      let features = match term with
        (* Interesting leafs *)
        | Node (Leaf nt :: ls) when is_atom nt ->
          if depth > 2 then
            {features with semantic = add_atom nt ls features}
          else
            {semantic = add_atom nt ls features;
            structure = features.structure @ ["X"]; 
            vertical = features.vertical}
        (* Uninteresting leafs *)
        (* TODO: features for Sort because A:Prop has empty features *)
        | Node (Leaf "Sort" :: _)
        | Node (Leaf "Meta" :: _) -> features
        (* Recursion for grammar we don't handle *)
        | Node [Leaf "LetIn"; _id; _; body1; typ; body2] ->
          let roles = ["LetVarBody"; "LetVarType"; "LetBody"] in
          end_structure (aux_reset_fold (start_structure features "LetIn") 
          (List.combine [body1; typ; body2] roles) depth)
        | Node (Leaf "Case" :: _ :: term :: typ :: cases) ->
          let roles = (["MatchTerm"; "MatchTermType"] @ (rep_elem (List.length cases) "Case")) in
          end_structure (aux_reset_fold (start_structure features "Case") 
          (List.combine (term::typ::cases) roles) depth)
        | Node [Leaf "Fix"; _; Node types; Node terms] ->
          let roles = (rep_elem (List.length terms) "FixTerm") @ (rep_elem (List.length types) "FixType") in
          end_structure (aux_reset_fold (start_structure features "Fix") (List.combine (terms @ types) roles) depth) 
        | Node [Leaf "CoFix"; _ ; Node types; Node terms] ->
          let roles = (rep_elem (List.length terms) "CoFixTerm") @ (rep_elem (List.length types) "CoFixType") in
          end_structure (aux_reset_fold (start_structure features "CoFix") (List.combine (terms @ types) roles) depth) 
        | Node [Leaf "Prod"  ; _; _; typ; body] ->
          let roles = ["ProdType"; "ProdBody"] in
          end_structure(aux_reset_fold (start_structure features "Prod") (List.combine [typ; body] roles) depth) 
        | Node [Leaf "Lambda"; _; _; typ; body] -> 
          let roles = ["LambdaType"; "LambdaBody"] in
          end_structure(aux_reset_fold (start_structure features "Lambda") (List.combine [typ; body] roles) depth) 
        (* The golden path *)
        | Node [Leaf "Proj"; p; term] -> 
          let features' = start_structure {features with semantic = add_atom "Const" [p] features} "Proj"
          in end_structure (aux features' term "ProjTerm" (depth + 1))
        | Node (Leaf "App" :: head :: args) ->
          let walk = features.vertical.walk in
          let arg_num = List.length args in
          let features_with_head = aux (start_structure features "App") head "AppFun" (depth + 1) in
          let features_with_head_and_arg_num = 
            {features_with_head with structure = features_with_head.structure @ [Stdlib.string_of_int arg_num]} in
          let feature' = List.fold_left (fun features arg ->
            let features = set_walk features walk in
            let features_this_arg = aux features arg "AppArg" (depth + 1) in
            (* We reset back to `interm` of `features_with_head_and_arg_num` for every arg *)
            set_interm features_this_arg features_with_head_and_arg_num.semantic.interm) 
            features_with_head_and_arg_num args 
          in
          end_structure(reset_interm feature')
        | Node [Leaf "Cast"; term; _; typ] ->
          (* We probably want to have the type of the cast, but isolated *)
          let features_reset = reset_interm features in
          let features_with_type = aux (start_structure features_reset "Cast") typ "CastType" (depth + 1) in
          let feature' = set_interm features_with_type features.semantic.interm in
          end_structure (aux feature' term "CastTerm" (depth + 1)) 
        (* Hope and pray *)
        | term -> warn term oterm; features
      in
      if depth == 3 then
        (* break the maximal depth constraint*) 
        {features with structure = features.structure@["X"]}
      else features 
    in
    let features = aux init_features oterm "Root" 0 in
    (* We use tail-recursive rev_map instead of map to avoid stack overflows on large proof states *)
    let add_feature_kind features kind = List.rev_map (fun feature -> kind, feature) features in
    List.rev_map (fun (feat_kind, feats) -> feat_kind, String.concat "-" feats) (
      (Struct, features.structure) :: 
      ((add_feature_kind features.semantic.acc Seman) @ 
      (add_feature_kind features.vertical.acc Verti)))

    let proof_state_to_complex_features max_length ps =
      let hyps = proof_state_hypotheses ps in
      let goal = proof_state_goal ps in
      let mkfeats t = term_sexpr_to_complex_features max_length (term_sexpr t) in
      let hyp_id_typ_feats = List.rev_map (function
          | Named.Declaration.LocalAssum (id, typ) ->
            (Names.Id.to_string id.binder_name), (sexpr_to_string (term_sexpr typ)), (mkfeats typ)
          | Named.Declaration.LocalDef (id, term, typ) ->
            (Names.Id.to_string id.binder_name),(sexpr_to_string (term_sexpr typ)), (mkfeats typ @ mkfeats term))
          hyps in
      let hyp_feats = List.rev_map (fun (_, _, feats) -> feats) hyp_id_typ_feats in
      let goal_feats = mkfeats goal in
      (* seperate the goal from the local context *)  
      (List.rev_map (fun (kind, feat) -> kind, "GOAL-"^ feat) goal_feats) @  
      (List.rev_map (fun (kind, feat) -> kind, "HYPS-"^ feat) (List.flatten hyp_feats)) 

  let proof_state_to_complex_ints ps =
    let complex_feats = proof_state_to_complex_features 2 ps in
    let feats_with_count_pair = count_dup complex_feats in 
    (* Tail recursive version of map, because these lists can get very large. *)
    let feats_with_count = List.rev_map (fun ((kind, feat), count) -> kind, feat ^ "-" ^ (Stdlib.string_of_int count))
        feats_with_count_pair in 
    (* print_endline (String.concat ", "  (List.map Stdlib.snd complex_feats)); *)
    let feats = List.rev_map (fun (kind, feat) ->  kind, Hashtbl.hash feat) feats_with_count in
    List.sort_uniq (fun (_kind1, feat1) (_kind2, feat2) -> Int.compare feat1 feat2) feats

  let context_complex_features max_length ctx =
    let mkfeats t = term_sexpr_to_complex_features max_length (term_sexpr t) in
    context_map mkfeats mkfeats ctx

  let context_complex_ints ctx =
    let ctx = context_complex_features 2 ctx in
    let feats_with_count_pair = context_map count_dup count_dup ctx in
    (* Tail recursive version of map, because these lists can get very large. *)
    let feats_with_count_f pair = List.rev_map (fun ((feat_kind, feat), count) -> feat_kind, feat ^ "-" ^ (Stdlib.string_of_int count))
        pair in
    let feats_with_count = context_map feats_with_count_f feats_with_count_f feats_with_count_pair in
    (* print_endline (String.concat ", "  (List.map Stdlib.snd feats_with_count)); *)
    (* Tail recursive version of map, because these lists can get very large. *)
    let feats f = List.rev_map (fun (feat_kind, feat) -> feat_kind, Hashtbl.hash feat) f in
    let feats = context_map feats feats feats_with_count in
    let sort f = List.sort_uniq (fun (_, feat1) (_, feat2) -> Int.compare feat1 feat2) f in
    context_map sort sort feats

  let tfidf size freqs ls1 ls2 =
    let inter = intersect compare ls1 ls2 in
    List.fold_left (+.) 0.
      (List.map
         (fun f -> Float.log ((Float.of_int (1 + size)) /.
                              (Float.of_int (1 + (default 0 (Frequencies.find_opt f freqs))))))
         inter)

  let remove_feat_kind l =
    List.rev_map Stdlib.snd l

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
            then (Float.of_int(1) *. similarity_for_one_feat f)
            else similarity_for_one_feat f)
         inter)

end
