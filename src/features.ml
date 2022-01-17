open Tactic_learner
open Context
open Learner_helper
open Names

type feat_kind = Struct | Seman | Verti
type 'a semantic_features = { interm: 'a list list; acc: 'a list}
(*for `f(g(a), b)` and go to `a`
  walk: the walk from root to `a`
  walk_to_sibiling: walk from root to f such that we can calculate the walk to `b` basing on it*)
type ('a, 'b) vertical_features =
  { walk : 'a
  ; acc : 'b list}
type ('a, 'b, 'c, 'd) features =
  { semantic : 'a semantic_features
  ; structure : 'b
  ; vertical: ('c, 'd) vertical_features }

type ('a, 'b, 'c, 'd) features2 =
  { semantic2 : 'a list list
  ; structure2 : 'b
  ; vertical2 : 'c
  ; store : 'd }

let global2s g =
  let a = Globnames.canonical_gr g in
  let b = Nametab.path_of_global (a) in
  Libnames.string_of_path b
let constant2s c = global2s (GlobRef.ConstRef c)
let inductive2s i = global2s (GlobRef.IndRef i)
let constructor2s c =
  global2s (GlobRef.ConstructRef c)
let id2s id = Id.to_string id

type semantic_token =
  | TRel
  | TEvar
  | TConstruct of constructor
  | TInd of inductive
  | TVar of variable
  | TConst of Constant.t
  | TInt of Uint63.t
  | TFloat of Float64.t
type role_token =
  | TRoot
  | TLetVarBody
  | TLetVarType
  | TLetBody
  | TMatchTerm
  | TMatchTermType
  | TFixTerm
  | TFixType
  | TCoFixTerm
  | TCoFixType
  | TProdType
  | TProdBody
  | TLambdaType
  | TLambdaBody
  | TCase
  | TProjTerm
  | TAppFun
  | TAppArg
  | TCastType
  | TCastTerm
  | TLetIn
  | TFix
  | TCoFix
  | TProd
  | TLambda
  | TProj
  | TApp
  | TCast
type vertical_token =
  | TAtom of semantic_token * role_token
  | TNonAtom of role_token
type structural_token =
  | TOpenParen
  | TCloseParen
  | TAppArgs of int
  | TRole of role_token
  | TEnd

let semantic_token_to_string = function
  | TRel -> "R"
  | TEvar -> "E"
  | TConstruct c -> constructor2s c
  | TInd i -> inductive2s i
  | TVar id -> "$" ^ id2s id
  | TConst c -> constant2s c
  | TInt n -> "i" ^ Uint63.to_string n
  | TFloat n -> "f" ^ Float64.to_string n
let role_token_to_string = function
  | TRoot -> "Root"
  | TLetVarBody -> "LetVarBody"
  | TLetVarType -> "LetVarType"
  | TLetBody -> "LetBody"
  | TMatchTerm -> "MatchTerm"
  | TMatchTermType -> "MatchTermType"
  | TFixTerm -> "FixTerm"
  | TFixType -> "FixType"
  | TCoFixTerm -> "CoFixTerm"
  | TCoFixType -> "CoFixType"
  | TProdType -> "ProdType"
  | TProdBody -> "ProdBody"
  | TLambdaType -> "LambdaType"
  | TLambdaBody -> "LambdaBody"
  | TCase -> "Case"
  | TProjTerm -> "ProjTerm"
  | TAppFun -> "AppFun"
  | TAppArg -> "AppArg"
  | TCastType -> "CastType"
  | TCastTerm -> "CastTerm"
  | TLetIn -> "LetIn"
  | TFix -> "Fix"
  | TCoFix -> "CoFix"
  | TProd -> "Prod"
  | TLambda -> "Lambda"
  | TProj -> "Proj"
  | TApp -> "App"
  | TCast -> "Cast"
let vertical_token_to_string = function
  | TAtom (sm, rl) -> semantic_token_to_string sm ^ ":" ^ role_token_to_string rl
  | TNonAtom rl -> role_token_to_string rl
let structural_token_to_string = function
  | TOpenParen -> "("
  | TCloseParen -> ")"
  | TAppArgs n -> string_of_int n
  | TRole rl -> role_token_to_string rl
  | TEnd -> "X"

(* WARNING: Be careful to make sure that these hashes don't collide. OCaml's buit-in hash function collides
   on constructors of different variants with the same index (even if they have different names). This is
   dangerous. *)
let semantic_token_to_int =
  function
  | TRel -> Int.hash 1001
  | TEvar -> Int.hash 1002
  | TConstruct c -> constructor_hash c
  | TInd i -> ind_hash i
  | TVar id -> Id.hash id
  | TConst c -> Constant.CanOrd.hash c
  | TInt n -> Uint63.hash n
  | TFloat n -> Float64.hash n
let role_token_to_int = function
  | TRoot -> Int.hash 1003
  | TLetVarBody -> Int.hash 1004
  | TLetVarType -> Int.hash 1005
  | TLetBody -> Int.hash 1006
  | TMatchTerm -> Int.hash 1007
  | TMatchTermType -> Int.hash 1008
  | TFixTerm -> Int.hash 1009
  | TFixType -> Int.hash 1010
  | TCoFixTerm -> Int.hash 1011
  | TCoFixType -> Int.hash 1012
  | TProdType -> Int.hash 1013
  | TProdBody -> Int.hash 1014
  | TLambdaType -> Int.hash 1015
  | TLambdaBody -> Int.hash 1016
  | TCase -> Int.hash 1017
  | TProjTerm -> Int.hash 1018
  | TAppFun -> Int.hash 1019
  | TAppArg -> Int.hash 1020
  | TCastType -> Int.hash 1021
  | TCastTerm -> Int.hash 1022
  | TLetIn -> Int.hash 1023
  | TFix -> Int.hash 1024
  | TCoFix -> Int.hash 1025
  | TProd -> Int.hash 1026
  | TLambda -> Int.hash 1027
  | TProj -> Int.hash 1028
  | TApp -> Int.hash 1029
  | TCast -> Int.hash 1030
let vertical_token_to_int = function
  | TAtom (sm, rl) -> Hashset.Combine.combine (semantic_token_to_int sm) (role_token_to_int rl)
  | TNonAtom rl -> Hashset.Combine.combine (Int.hash 1031) (role_token_to_int rl)
let structural_token_to_int = function
  | TOpenParen -> Int.hash 1032
  | TCloseParen -> Int.hash 1033
  | TAppArgs n -> Hashset.Combine.combine (Int.hash 1034) (Int.hash n)
  | TRole rl -> Hashset.Combine.combine (Int.hash 1035) (role_token_to_int rl)
  | TEnd -> Int.hash 1036

module F (TS: TacticianStructures) = struct
  module LH = L(TS)
  open LH
  open TS

  let term_sexpr_to_simple_features
      ~gen_feat:(init, comb)
      ~store_feat:(empty, add)
      maxlength (oterm : Constr.t) =
    let open Constr in

    (* for a tuple `(interm, acc)`:
       - `interm` is an intermediate list of list of features that are still being assembled
         invariant: `forall i ls, 0<i<=maxlength -> In ls (List.nth (i - 1)) -> List.length ls = i`
       - `acc`: accumulates features that are fully assembled *)
    let add_atom atom (interm, acc) =
      let atom = init atom in
      let interm' = [atom] :: List.map (List.map (comb atom)) interm in
      (removelast interm', List.fold_left add acc @@ List.flatten interm') in
    let set_interm (_interm, acc) x = x, acc in
    let start = replicate [] (maxlength - 1) in
    let reset_interm f = set_interm f start in
    let rec aux_reset f term = reset_interm (aux (reset_interm f) term)
    and aux_reset_fold f terms = List.fold_left aux_reset f terms
    and aux ((interm, _acc) as f) (term : constr) =
      match kind term with
      (* Interesting leafs *)
      | Rel _ -> add_atom TRel f
      | Evar _ -> add_atom TEvar f
      | Construct (c, u) -> add_atom (TConstruct c) f
      | Ind (i, u) -> add_atom (TInd i) f
      | Var id -> add_atom (TVar id) f
      | Const (c, u) -> add_atom (TConst c) f
      | Int n -> add_atom (TInt n) f
      | Float n -> add_atom (TFloat n) f

      (* Uninteresting leafs *)
      | Sort _
      | Meta _ -> f

      (* Recursion for grammar we don't handle *)
      (* TODO: Handle binders with feature substitution *)
      | LetIn (id, body1, typ, body2) ->
        aux_reset_fold f [body1; typ; body2]
      | Case (_, term, typ, cases) ->
        aux_reset_fold f (term::typ::(Array.to_list cases))
      | Fix (_, (_, typs, trms))
      | CoFix (_, (_, typs, trms)) ->
        aux_reset_fold f (Array.to_list trms @ Array.to_list typs)
      (* TODO: Handle implication separately *)
      | Prod (_, typ, body)
      | Lambda (_, typ, body) ->
        aux_reset_fold f [typ; body]

      (* The golden path *)
      | Proj (proj, trm) ->
        aux (add_atom (TConst (Projection.constant proj)) f) trm
      | App (head, args) ->
        let interm', _ as f' = aux f head in
        (* We reset back to `interm'` for every arg *)
        reset_interm (List.fold_left (fun f' t -> set_interm (aux f' t) interm') f' @@ Array.to_list args)
      | Cast (term, _, typ) ->
        (* We probably want to have the type of the cast, but isolated *)
        aux (set_interm (aux (reset_interm f) typ) interm) term
    in
    snd @@ aux (start, empty) oterm

  let proof_state_to_simple_features ~gen_feat ~store_feat:(acc, add) max_length ps =
    let hyps = proof_state_hypotheses ps in
    let goal = proof_state_goal ps in
    let mkfeats t acc =
      let x = term_repr t in
      term_sexpr_to_simple_features
        ~gen_feat
        ~store_feat:(acc, add) max_length x in
    (* TODO: distinquish goal features from hyp features *)
    let acc = List.fold_left (fun a b -> Named.Declaration.fold_constr mkfeats b a) acc hyps in
    mkfeats goal acc

  let context_simple_ints ctx =
    let mkfeats t = term_sexpr_to_simple_features
        ~gen_feat:(semantic_token_to_int, Hashset.Combine.combine)
        ~store_feat:(Int.Set.empty, (fun a b -> Int.Set.add b a))
        2 (term_repr t) in
    let to_ints t = Int.Set.elements (mkfeats t) in
    context_map to_ints to_ints ctx

  let proof_state_to_simple_ints ps =
    let feats = proof_state_to_simple_features
        ~gen_feat:(semantic_token_to_int, Hashset.Combine.combine)
        ~store_feat:(Int.Set.empty, (fun a b -> Int.Set.add b a))
        2 ps in
    Int.Set.elements feats

  let proof_state_to_simple_strings ps =
    let feats = proof_state_to_simple_features
        ~gen_feat:(semantic_token_to_string, (fun s1 s2 -> s1 ^ "-" ^ s2))
        ~store_feat:(CString.Set.empty, (fun a b -> CString.Set.add b a))
        2 ps in
    CString.Set.elements feats

  let rep_elem n elem =
    let rec rep_elem_aux acc n elem =
      if n = 0 then acc else rep_elem_aux (elem :: acc) (n-1) elem
    in
    rep_elem_aux [] n elem

  let warn lterm oterm =
    Feedback.msg_warning (Pp.str ("Tactician did not know how to handle something. Please report. "
                                  ^ sexpr_to_string lterm ^ " : " ^sexpr_to_string oterm))
  let term_sexpr_to_complex_features maxlength oterm =
    let atomtypes = ["Evar"; "Rel"; "Construct"; "Ind"; "Const"; "Var"; "Int"; "Float"] in
    let is_atom nodetype = List.exists (String.equal nodetype) atomtypes in
    let atom_to_string atomtype content = match atomtype, content with
      | "Rel", _ -> "R"
      | "Evar", (Leaf _ :: _) -> "E"
      | "Var", Leaf c :: _ -> "$" ^ c
      | "Construct", Leaf c :: _
      | "Ind", Leaf c :: _
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
    let add_feature_kind features kind = List.map (fun feature -> kind, feature) features in
    List.rev_map (fun (feat_kind, feats) -> feat_kind, String.concat "-" feats) (
      (Struct, features.structure) ::
      ((add_feature_kind features.semantic.acc Seman) @
       (add_feature_kind features.vertical.acc Verti)))


  let term_sexpr_to_complex_features2
      ~gen_semantic:(seman_init, seman_comb, seman_add)
      ~gen_structural:(struct_init, struct_comb, struct_add)
      ~gen_vertical:(vert_init, vert_comb, vert_add)
      ~store_feat:empty
      maxlength (oterm : Constr.t) =
    let open Constr in
    (* for a tuple `(interm, acc)`:
       - `interm` is an intermediate list of list of features that are still being assembled
         invariant: `forall i ls, 0<i<=maxlength -> In ls (List.nth (i - 1)) -> List.length ls = i`
       - `acc`: accumulates features that are fully assembled *)
    let add_atom atom ({ semantic2; store; _ } as features) =
      let atom = seman_init atom in
      (* `interm` contains term tree walks to maximal depth, maximal depth - 1,..., 1 *)
      let semantic2 = [atom] :: List.map (List.map (seman_comb atom)) semantic2 in
      (* Remove the last item to keep the maximal depth constraint.
        The length of `interm` = the maximal depth constraint.
        The initial `interm` is [[walk],[],...,[]]; thus, `removelast` will remove [] in the beginning *)
      { features with
        semantic2 = removelast semantic2
      ; store = List.fold_left seman_add store @@ List.flatten semantic2 }
    in
    let add_struct x ({ structure2; _ } as features) =
      { features with structure2 = struct_comb x structure2 } in
    let set_interm features semantic2 = { features with semantic2 } in
    let set_walk features vertical2 = { features with vertical2 } in
    let start = replicate [] (maxlength - 1) in
    let init_features =
      { semantic2 = replicate [] (maxlength - 1)
      ; structure2 = struct_init
      ; vertical2 = 0, vert_init
      ; store = empty } in
    let add_walk w ({ vertical2 = l, x; _ } as features) =
      { features with
        vertical2 = l+1, vert_comb w x } in
    let reset_interm features = set_interm features start in
    let start_structure ({ structure2; _} as features) role =
      { features with
        structure2 =
          struct_comb (TRole role) @@ struct_comb TOpenParen structure2 }
    in
    let end_structure ({ structure2; _ } as features) =
       { features with structure2 = struct_comb TCloseParen structure2 }
    in
    let verti_atom atom features role =
      if fst features.vertical2 == 1 then
        features
      else
        let atom_with_role = TAtom (atom, role) in
        { features with
          store =
            vert_add (vert_comb atom_with_role @@ snd features.vertical2) features.store
        }
    in
    let calculate_vertical_features (term : constr) role features =
      match kind term with
      | Rel _ -> verti_atom TRel features role
      | Evar _ -> verti_atom TEvar features role
      | Construct (c, _) -> verti_atom (TConstruct c) features role
      | Ind (c, _) -> verti_atom (TInd c) features role
      | Var id -> verti_atom (TVar id) features role
      | Const (c, u) -> verti_atom (TConst c) features role
      | Int n -> verti_atom (TInt n) features role
      | Float n -> verti_atom (TFloat n) features role
      | _ ->
        add_walk (TNonAtom role) features
    in
    let rec aux_reset features (term, role) depth walk =
      let reset_features = reset_interm features in
      let reset_features = set_walk reset_features walk in
      let features' = aux reset_features term role depth in
      reset_interm features'
    and aux_reset_fold features term_role_pairs depth =
      let walk = features.vertical2 in
      let next_level_depth = depth + 1 in
      List.fold_left (fun features' term_role_pair ->
          aux_reset features' term_role_pair next_level_depth walk) features term_role_pairs
    and aux features (term : constr) role depth =
      let features = calculate_vertical_features term role features in
      let process_atom atom =
        if depth > 2 then
          add_atom atom features
        else
          add_struct TEnd @@ add_atom atom features
      in
      let features = match kind term with
        (* Interesting leafs *)
        | Rel _ -> process_atom TRel
        | Evar _ -> process_atom TEvar
        | Construct (c, _) -> process_atom (TConstruct c)
        | Ind (c, _) -> process_atom (TInd c)
        | Var id -> process_atom (TVar id)
        | Const (c, u) -> process_atom (TConst c)
        | Int n -> process_atom (TInt n)
        | Float n -> process_atom (TFloat n)

        (* Uninteresting leafs *)
        | Sort _
        | Meta _ -> features

        (* Recursion for grammar we don't handle *)
        | LetIn (_, body1, typ, body2) ->
          let cont = [body1, TLetVarBody; typ, TLetVarType; body2, TLetBody] in
          end_structure (aux_reset_fold (start_structure features TLetIn) cont depth)
        | Case (_, term, typ, cases) ->
          let cases = Array.to_list cases in
          let cont = [term, TMatchTerm; typ, TMatchTermType] @ (List.map (fun c -> c, TCase) cases) in
          end_structure (aux_reset_fold (start_structure features TCase) cont depth)
        | Fix (_, (_, types, terms)) ->
          let terms = Array.to_list terms in
          let types = Array.to_list types in
          let cont = (List.map (fun c -> c, TFixTerm) terms) @ (List.map (fun c -> c, TFixType) types) in
          end_structure (aux_reset_fold (start_structure features TFix) cont depth)
        | CoFix (_, (_, types, terms)) ->
          let terms = Array.to_list terms in
          let types = Array.to_list types in
          let cont = (List.map (fun c -> c, TCoFixTerm) terms) @ (List.map (fun c -> c, TCoFixType) types) in
          end_structure (aux_reset_fold (start_structure features TCoFix) cont depth)
        | Prod (_, typ, body) ->
          let cont = [typ, TProdType; body, TProdBody] in
          end_structure(aux_reset_fold (start_structure features TProd) cont depth)
        | Lambda (_, typ, body) ->
          let cont = [typ, TLambdaType; body, TLambdaBody] in
          end_structure(aux_reset_fold (start_structure features TLambda) cont depth)

        (* The golden path *)
        | Proj (p, term) ->
          let p = Projection.constant p in
          let features' = start_structure (add_atom (TConst p) features) TProj
          in end_structure (aux features' term TProjTerm (depth + 1))
        | App (head, args) ->
          let walk = features.vertical2 in
          let args = Array.to_list args in
          let arg_num = List.length args in
          let features_with_head = aux (start_structure features TApp) head TAppFun (depth + 1) in
          let features_with_head_and_arg_num = add_struct (TAppArgs arg_num) features_with_head in
          let feature' = List.fold_left (fun features arg ->
              let features = set_walk features walk in
              let features_this_arg = aux features arg TAppArg (depth + 1) in
              (* We reset back to `interm` of `features_with_head_and_arg_num` for every arg *)
              set_interm features_this_arg features_with_head_and_arg_num.semantic2)
              features_with_head_and_arg_num args
          in
          end_structure(reset_interm feature')
        | Cast (term, _, typ) ->
          (* We probably want to have the type of the cast, but isolated *)
          let features_reset = reset_interm features in
          let features_with_type = aux (start_structure features_reset TCast) typ TCastType (depth + 1) in
          let feature' = set_interm features_with_type features.semantic2 in
          end_structure (aux feature' term TCastTerm (depth + 1))
      in
      if depth == 3 then
        (* break the maximal depth constraint*)
        add_struct TEnd features
      else features
    in
    let features = aux init_features oterm TRoot 0 in
    struct_add features.structure2 features.store

  let inc x = function
    | None -> Some (x, 1)
    | Some (x, i) -> Some (x, i+1)

  let term_sexpr_to_complex_strings2 prefix max_length acc term =
    let combine a b = if a = "" then b else a ^ "-" ^ b in
    let combine2 f a b = if b = "" then f a else b ^ "-" ^ f a in
    term_sexpr_to_complex_features2
      ~gen_semantic:(semantic_token_to_string, combine,
                     (fun ls x -> CString.Map.update (prefix^x) (inc Seman) ls))
      ~gen_structural:("", combine2 structural_token_to_string,
                       (fun x ls -> CString.Map.update (prefix^x) (inc Struct) ls))
      ~gen_vertical:("", combine2 vertical_token_to_string,
                     (fun x ls -> CString.Map.update (prefix^x) (inc Verti) ls))
      ~store_feat:acc
      max_length term

  let term_sexpr_to_complex_ints2 prefix max_length acc term =
    let combine a b = Hashset.Combine.combine a b in
    let combine2 f a b = Hashset.Combine.combine (f a) b in
    term_sexpr_to_complex_features2
      ~gen_semantic:(semantic_token_to_int, combine,
                     (fun ls x -> Int.Map.update (combine prefix x) (inc Seman) ls))
      ~gen_structural:(0, combine2 structural_token_to_int,
                       (fun x ls -> Int.Map.update (combine prefix x) (inc Struct) ls))
      ~gen_vertical:(0, combine2 vertical_token_to_int,
                     (fun x ls -> Int.Map.update (combine prefix x) (inc Verti) ls))
      ~store_feat:acc
      max_length term

  let term_sexpr_to_complex_ints_no_kind2 prefix max_length acc term =
    let combine a b = Hashset.Combine.combine a b in
    let combine2 f a b = Hashset.Combine.combine (f a) b in
    let inc = function
      | None -> Some 1
      | Some i -> Some (i+1) in
    term_sexpr_to_complex_features2
      ~gen_semantic:(semantic_token_to_int, combine,
                     (fun ls x -> Int.Map.update (combine prefix x) inc ls))
      ~gen_structural:(0, combine2 structural_token_to_int,
                       (fun x ls -> Int.Map.update (combine prefix x) inc ls))
      ~gen_vertical:(0, combine2 vertical_token_to_int,
                     (fun x ls -> Int.Map.update (combine prefix x) inc ls))
      ~store_feat:acc
      max_length term

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
    (List.map (fun (kind, feat) -> kind, "GOAL-"^ feat) goal_feats) @
    (List.map (fun (kind, feat) -> kind, "HYPS-"^ feat) (List.flatten hyp_feats))

  let proof_state_to_complex_strings2 max_length ps =
    let hyps = proof_state_hypotheses ps in
    let goal = proof_state_goal ps in
    let mkfeats prefix t acc = term_sexpr_to_complex_strings2 prefix max_length acc (term_repr t) in
    let feats = List.fold_left (fun a b -> Named.Declaration.fold_constr (mkfeats "HYPS-") b a)
        CString.Map.empty hyps in
    let feats = mkfeats "GOAL-" goal feats in
    let feats_with_count = CString.Map.fold
        (fun feat (kind, count) acc -> (kind, feat ^ "-" ^ string_of_int count) :: acc)
        feats [] in
    (* TODO: In the current fomulation, this resorting is needed. However, this is rather expensive.
             We should consider not adding feature counts to the featues itself. This is likely to be
             suboptimal for the model anyways. *)
    List.sort_uniq (fun (_kind1, feat1) (_kind2, feat2) -> String.compare feat1 feat2) feats_with_count

  let proof_state_to_complex_strings2 ps = proof_state_to_complex_strings2 2 ps

  let proof_state_to_complex_ints2 max_length ps =
    let hyps = proof_state_hypotheses ps in
    let goal = proof_state_goal ps in
    let mkfeats prefix t acc = term_sexpr_to_complex_ints2 prefix max_length acc (term_repr t) in
    let feats = List.fold_left (fun a b -> Named.Declaration.fold_constr (mkfeats (Int.hash 2000)) b a)
        Int.Map.empty hyps in
    let feats = mkfeats (Int.hash 2001) goal feats in
    let feats_with_count = Int.Map.fold
        (fun feat (kind, count) acc -> (kind, Hashset.Combine.combine feat count) :: acc)
        feats [] in
    (* TODO: In the current fomulation, this resorting is needed. However, this is rather expensive.
             We should consider not adding feature counts to the featues itself. This is likely to be
             suboptimal for the model anyways. *)
    List.sort_uniq (fun (_kind1, feat1) (_kind2, feat2) -> Int.compare feat1 feat2) feats_with_count

  let proof_state_to_complex_ints2 ps = proof_state_to_complex_ints2 2 ps

  let proof_state_to_complex_ints_no_kind2 max_length ps =
    let hyps = proof_state_hypotheses ps in
    let goal = proof_state_goal ps in
    let mkfeats prefix t acc = term_sexpr_to_complex_ints_no_kind2 prefix max_length acc (term_repr t) in
    let feats = List.fold_left (fun a b -> Named.Declaration.fold_constr (mkfeats (Int.hash 2000)) b a)
        Int.Map.empty hyps in
    let feats = mkfeats (Int.hash 2001) goal feats in
    let feats_with_count = Int.Map.fold
        (fun feat count acc -> Hashset.Combine.combine feat count :: acc)
        feats [] in
    (* TODO: In the current fomulation, this resorting is needed. However, this is rather expensive.
             We should consider not adding feature counts to the featues itself. This is likely to be
             suboptimal for the model anyways. *)
    List.sort_uniq Int.compare feats_with_count

  let proof_state_to_complex_ints_no_kind2 ps = proof_state_to_complex_ints_no_kind2 2 ps

  let count_dup l =
    let sl = List.sort compare l in
    match sl with
    | [] -> []
    | hd::tl ->
      let acc,x,c = List.fold_left (fun (acc,x,c) y ->
          if y = x then acc,x,c+1 else (x,c)::acc, y,1) ([],hd,1) tl in
      (x,c)::acc

  let proof_state_to_complex_ints ps =
    let complex_feats = proof_state_to_complex_features 2 ps in
    let feats_with_count_pair = count_dup complex_feats in
    (* Tail recursive version of map, because these lists can get very large. *)
    let feats_with_count = List.rev_map (fun ((kind, feat), count) -> kind, feat ^ "-" ^ (Stdlib.string_of_int count))
        feats_with_count_pair in
    (* print_endline (String.concat ", "  (List.map Stdlib.snd complex_feats)); *)
    let feats = List.rev_map (fun (kind, feat) ->  kind, Hashtbl.hash feat) feats_with_count in
    List.sort_uniq (fun (_kind1, feat1) (_kind2, feat2) -> Int.compare feat1 feat2) feats

  let proof_state_to_complex_strings ps =
    let complex_feats = proof_state_to_complex_features 2 ps in
    let feats_with_count_pair = count_dup complex_feats in
    (* Tail recursive version of map, because these lists can get very large. *)
    let feats_with_count = List.rev_map (fun ((kind, feat), count) -> kind, feat ^ "-" ^ (Stdlib.string_of_int count))
        feats_with_count_pair in
    (* print_endline (String.concat ", "  (List.map Stdlib.snd complex_feats)); *)
    List.sort_uniq (fun (_kind1, feat1) (_kind2, feat2) -> String.compare feat1 feat2) feats_with_count

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
                              (Float.of_int (1 + (Option.default 0 (Frequencies.find_opt f freqs))))))
         inter)

  let remove_feat_kind l =
    List.map snd l

  let manually_weighed_tfidf size freq ls1 ls2 =
    let inter = intersect (fun x y -> compare (snd x) y) ls1 ls2 in
    let similarity_for_one_feat feat =
      Float.log ((Float.of_int (1 + size)) /.
                 (Float.of_int (1 + (Option.default 0 (Frequencies.find_opt feat freq)))))
    in
    List.fold_left (+.) 0.
      (List.map
         (fun (feat_kind, f) ->
            if feat_kind == Struct
            then (1. *. similarity_for_one_feat f)
            else similarity_for_one_feat f)
         inter)

end
