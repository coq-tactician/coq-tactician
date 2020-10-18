open Names
open Tactic_learner_internal
open Glob_term
open Constr
open Evar_kinds
open Sexpr

let global_type2s = function
  | GlobRef.ConstRef _     -> s2s "ConstRef"
  | GlobRef.IndRef _       -> s2s "IndRef"
  | GlobRef.ConstructRef _ -> s2s "ConstructRef"
  | GlobRef.VarRef _       -> s2s "VarRef"

let glob_sort_name2s = function
  | GSProp  -> s2s "SProp"
  | GProp   -> s2s "Prop"
  | GSet    -> s2s "Set"
  | GType l -> Node [s2s "Type"; s2s (Libnames.string_of_qualid l)]

let glob_sort_expr2s f = function
  | UAnonymous { rigid = true  } -> Node [s2s "Anonymous"; s2s "Rigid"]
  | UAnonymous { rigid = false } -> Node [s2s "Anonymous"; s2s "Flexible"]
  | UNamed x                     -> f x

let glob_level2s = glob_sort_expr2s glob_sort_name2s

let glob_sort2s = glob_sort_expr2s (fun ls ->
    Node (List.map (fun (na, n) -> Node [glob_sort_name2s na; s2s (string_of_int n)]) ls))

let binding_kind2s = function
  | Explicit -> s2s "Explicit"
  | MaxImplicit -> s2s "MaxImplicit"
  | NonMaxImplicit -> s2s "NonMaxImplicit"

let case_style2s = function
  | LetStyle        -> s2s "LetStyle"
  | IfStyle         -> s2s "IfStyle"
  | LetPatternStyle -> s2s "LetPatternStyle"
  | MatchStyle      -> s2s "MatchStyle"
  | RegularStyle    -> s2s "RegularStyle"

let rec cases_pattern2s p = match DAst.get p with
  | PatVar id -> name2s id, [id]
  | PatCstr (cstr, pats, asid) ->
    let sub_cases, ls = List.split (List.map cases_pattern2s pats) in
    Node (constructor2s cstr @ [Node sub_cases; name2s asid]), List.flatten ls

let glob_fix_kind2s = function
  | GFix (arr, n) ->
    [ s2s "Fix"
    ; Node (Array.to_list (Array.map s2s (Array.map (Option.default "_") (Array.map (Option.map string_of_int) arr))))
    ; s2s (string_of_int n)]
  | GCoFix n -> [s2s "Cofix"; s2s (string_of_int n)]

let matching_var_kind2s = function
  | FirstOrderPatVar id -> [s2s "FirstOrderPatVar"; id2s id]
  | SecondOrderPatVar id -> [s2s "SecondOrderPatVar"; id2s id]

let evar_kind2s = function
  | ImplicitArg (re, (n, id), b) -> Node [s2s "ImplicitArg"; global2s re; s2s (string_of_int n)]
  | BinderType id -> Node [s2s "BinderType"; name2s id]
  | NamedHole id  -> Node [s2s "NamedHole" ; id2s   id]
  | QuestionMark { qm_name = id } -> Node [s2s "QuestionMark"; name2s id]
  | CasesType _ -> Node [s2s "CasesType"]
  | InternalHole -> Node [s2s "InternalHole"]
  | TomatchTypeParameter (ind, n) -> Node [s2s "TomatchTypeParameter"; inductive2s ind]
  | GoalEvar -> Node [s2s "GoalEvar"]
  | ImpossibleCase -> Node [s2s "ImpossibleCase"]
  | MatchingVar mv -> Node (s2s "MatchingVar" :: matching_var_kind2s mv)
  | VarInstance id -> Node [s2s "VarInstance"; id2s id]
  | SubEvar (sk, var) -> Node [s2s "SubEvar"; s2s (string_of_int (Evar.repr var))]

let intro_pattern_naming_expr2s = function
  | Namegen.IntroIdentifier id -> Node [s2s "IntroIdentifier"; id2s id]
  | Namegen.IntroAnonymous -> Node [s2s "IntroAnonymous"]
  | Namegen.IntroFresh id -> Node [s2s "IntroFresh"; id2s id]

let cast_type2s f = function
  | CastConv x ->   Node [s2s "CastConv"; f x]
  | CastVM x   ->   Node [s2s "CastVM"; f x]
  | CastCoerce ->   Node [s2s "CastCoerce"]
  | CastNative x -> Node [s2s "CastNative"; f x]

(* Note: De Bruijn calculations are not necessarily equal to those of the kernel *)
let id_to_debruijn id ls =
  let rec aux ls n =
    match ls with
    | [] -> None
    | Name id'::_ when Id.equal id id' -> Some n
    | _::ls' -> aux ls' (n + 1) in
  aux ls 0

let glob_constr2s ls (t: glob_constr) : sexpr =
  let rec constr2s ls = function
    | GRef (id, levels) ->
      Node [s2s "GRef"; global2s id; global_type2s id
           ; Node (s2s "Levels" :: Option.default [] (Option.map (List.map glob_level2s) levels))]
    | GVar id -> let ids = Id.to_string id in
      Node (s2s "GVar" ::
      match id_to_debruijn id ls with
      | None   -> [s2s "Free";  s2s ids]
      | Some n -> [s2s "Bound"; s2s ids; s2s (string_of_int n)])
    | GEvar (id, map) -> Node ([s2s "GEvar"; id2s id] @ List.map (fun (id, t') -> Node [id2s id; dast2s ls t]) map)
    | GPatVar mv  -> Node (s2s "GPatVar" :: matching_var_kind2s mv)
    | GApp (t1, tarr) -> Node ([s2s "GApp"; dast2s ls t1] @ List.map (dast2s ls) tarr)
    | GLambda (id, bk, ty, te) ->
      Node [s2s "GLambda"; name2s id; binding_kind2s bk; dast2s ls ty; dast2s (id::ls) te]
    | GProd (id, bk, ty, te) ->
      Node [s2s "GProd"; name2s id; binding_kind2s bk; dast2s ls ty; dast2s (id::ls) te]
    | GLetIn (id, te1, ty, te2) ->
      Node [s2s "GLetIn"; dast2s ls te1; (Option.default (Node []) (Option.map (dast2s ls) ty)); dast2s (id::ls) te2]
    | GCases (cs, r, tur, cc) ->
      let return_vars = List.flatten (List.map (fun (_, (id, p)) ->
          id :: Option.default [] (Option.map (CAst.with_val snd) p)) tur) in
      Node [ s2s "GCases"; case_style2s cs
           ; Node (s2s "Match" :: tomach_tuples2s ls tur)
           ; Node (s2s "Return" :: Option.default [] (Option.map (fun t -> [dast2s (return_vars @ ls) t]) r))
           ; Node (s2s "With" :: cases_clauses2s ls cc)]
    | GLetTuple (ids, (asid, r), t1, t2) ->
      Node [ s2s "GLetTuple"
           ; Node [s2s "Match"; dast2s ls t1; name2s asid]
           ; Node (s2s "Return" :: Option.default [] (Option.map (fun t -> [dast2s (asid::ls) t]) r))
           ; Node [s2s "Width"; Node (List.map name2s ids); dast2s (ids @ ls) t2]]
    | GIf (t1, (asid, r), t2, t3) ->
      Node [ s2s "GIf"
           ; Node [s2s "Match"; dast2s ls t1; name2s asid]
           ; Node (s2s "Return" :: Option.default [] (Option.map (fun t -> [dast2s (asid::ls) t]) r))
           ; Node [s2s "Width"; dast2s ls t2; dast2s ls t3]]
    | GRec (fk, ids, decls, trms, args) ->
      let names = List.map Name.mk_name (Array.to_list ids) in
      Node (s2s "GRec" :: glob_fix_kind2s fk @ [ Node (Array.to_list (Array.map id2s ids));
                                                 Node (Array.to_list (Array.map (glob_decls2s ls) decls))
                                               ; Node (Array.to_list (Array.map (dast2s (names @ ls)) trms))
                                               ; Node (Array.to_list (Array.map (dast2s ls) args))])
    | GSort s -> glob_sort2s s
    (* TODO: Do something with 'gen' argument *)
    | GHole (kind, intro, gen) -> Node [s2s "GHole"; evar_kind2s kind; intro_pattern_naming_expr2s intro]
    | GCast (t, ct) -> Node [s2s "GCast"; dast2s ls t; cast_type2s (dast2s ls) ct]
    | GInt i -> Node [s2s "GInt"; s2s (Uint63.to_string i)]
    | GFloat f -> Node [s2s "GFloat"; s2s (Float64.to_string f)]
  and glob_decl2s ls (id, bk, def, ty) =
    Node (name2s id :: binding_kind2s bk :: dast2s ls ty ::
          Option.default [] (Option.map (fun t -> [dast2s ls t]) def))
  and glob_decls2s ls decls = Node (List.map (glob_decl2s ls) decls)
  and predicate_pattern2s ls (ind, ids) = Node (inductive2s ind :: List.map (fun id -> name2s id) ids)
  and tomach_tuple2s ls (t, (id, ins)) =
    Node ([dast2s ls t; name2s id] @
         Option.default [] (Option.map (CAst.with_val (fun p -> [predicate_pattern2s ls p])) ins))
  and tomach_tuples2s ls tur = List.map (tomach_tuple2s ls) tur
  and cases_clause2s ls (_, pts, t) =
    let sub_cases, ids = List.split (List.map cases_pattern2s pts) in
    Node [Node sub_cases; dast2s (List.flatten ids @ ls) t]
  and cases_clauses2s ls cc = List.map (CAst.with_val (cases_clause2s ls)) cc
  and dast2s ls t = constr2s ls (DAst.get t)
  in
  dast2s ls t
