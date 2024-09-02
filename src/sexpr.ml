open Names
open Constr
open Sorts
open Context

type sexpr = Node of sexpr list | Leaf of string

let rec sexpr_to_string = function
  | Leaf str -> str
  | Node ls -> "(" ^ (String.concat " " (List.map sexpr_to_string ls)) ^ ")"

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
  | Ppcmd_string s -> Ppcmd_string (String.concat "\\n" @@ String.split_on_char '\n' s)
  | _ -> d in
  h (unrepr d')

let global2s g =
  let a = Globnames.canonical_gr g in
  let b = Nametab.path_of_global (a) in
  s2s (Libnames.string_of_path b)

let sorts2s = function
  | SProp  -> [s2s "SProp"]
  | Prop   -> [s2s "Prop"]
  | Set    -> [s2s "Set"]
  | Type l -> [s2s "Type"; (* TODO: Printing is not optimal here *)
               s2s (Pp.string_of_ppcmds (format_oneline (Univ.Universe.raw_pr l)))]
  | QSort (v, l) -> [s2s "QSort";
                     s2s (Pp.string_of_ppcmds (QVar.raw_pr v));
                     s2s (Pp.string_of_ppcmds (format_oneline (Univ.Universe.raw_pr l)))]

let instance2s i =
  let qs, levels = UVars.Instance.to_array i in
  (* todo handle qualities *)
  Array.to_list (Array.map (fun l -> s2s (Univ.Level.to_string l)) levels)

let cast_kind2s = function
  | VMcast -> s2s "VMcast"
  | NATIVEcast -> s2s "NATIVEcast"
  | DEFAULTcast -> s2s "DEFAULTcast"

let relevance2s = function
  | Relevant -> s2s "Relevant"
  | Irrelevant -> s2s "Irrelevant"
  | RelevanceVar v -> Node [s2s "RelevanceVar"; s2s (Pp.string_of_ppcmds (QVar.raw_pr v))]

let constant2s c = global2s (GlobRef.ConstRef c)

let inductive2s i = global2s (GlobRef.IndRef i)

let constructor2s c =
  [global2s (GlobRef.ConstructRef c); inductive2s (fst c)]

let case_info2s {ci_ind; _} =
  inductive2s ci_ind (* TODO: More info? *)

let constr_to_glob_constr t env sigma =
  Detyping.detype Detyping.Later env sigma t

(* Note: De Bruijn calculations may be different from Coq's calculations *)
let rec debruijn_to_id n ls = if (n - 1) > 0 then debruijn_to_id (n - 1) (List.tl ls) else if ls == [] then (print_endline (string_of_int n); Names.Name.mk_name (Names.Id.of_string "kAK")) else List.hd ls

let constr2s t =
  let rec aux (ls : Name.t list) t =
    match kind t with
    (* TODO: Verify correctness of debruijn_to_id *)
    | Rel n -> Node [s2s "Rel"; s2s (string_of_int n); name2s (debruijn_to_id n ls)]
    | Var id -> Node [s2s "Var"; id2s id]
    | Meta n -> Node [s2s "Meta"; s2s (string_of_int n)]
    | Evar (evar, constrs) ->
      let sentences = List.map (aux ls) @@ List.filter_map (fun x -> x) @@ SList.to_list constrs in
      Node (s2s "Evar" :: s2s (string_of_int (Evar.repr evar)) :: sentences)
    | Sort s -> Node (s2s "Sort" :: sorts2s s)
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
    | Const (c, u) -> Node (s2s "Const" :: constant2s c :: instance2s u)
    | Ind (i, u) -> Node (s2s "Ind" :: inductive2s i :: instance2s u)
    | Construct (c, u) -> Node (s2s "Construct" :: constructor2s c @ instance2s u)
    | Case (a, b, c, d, e, f, g) ->
      let (info, (t1,_), inv, t2, bodies) = (* TODO: Use inv *)
        (* We assume here that the current environment is an extension of the environment where
           the term was defined. *)
        (* TODO: This crashes when the inducive was defined in a section that is now closed.
                 This makes the s-expressions basically useless. The only proper fix seems to be fixing
                 https://github.com/coq-tactician/coq-tactician/issues/28 *)
        Inductive.expand_case (Global.env ()) (a, b, c, d, e, f, g) in
      Node (s2s "Case" :: case_info2s info :: aux ls t1 :: aux ls t2
           :: Array.to_list (Array.map (aux ls) bodies))
    | Fix (_, pd) -> Node (s2s "Fix" :: prec_declaration2s ls pd)
    | CoFix (_, pd) -> Node (s2s "CoFix" :: prec_declaration2s ls pd)
    | Proj (proj, _, trm) -> Node [s2s "Proj"; constant2s (Projection.constant proj); aux ls trm] (* TODO: Improve *)
    | Int n -> Node [s2s "Int"; s2s (Uint63.to_string n)]
    | Float n -> Node [s2s "Float"; s2s (Float64.to_string n)]
    | String s -> Node [s2s "String"; s2s (Pstring.to_string s)]
    | Array (u, cs, c, ty) ->
      Node [s2s "Array"; aux ls c; Node (Array.to_list (Array.map (aux ls) cs)); aux ls ty; Node (instance2s u)]
  and prec_declaration2s ls (ns, typs, trms) =
    let ids = Array.to_list (Array.map (fun n -> n.binder_name) ns) in
    [ Node (List.map name2s ids)
    ; Node (Array.to_list (Array.map (aux ls) typs))
    (* TODO: Check if this ordering of bound variables is correct *)
    ; Node (Array.to_list (Array.map (aux (ids@ls)) trms))] in
  aux [] t
