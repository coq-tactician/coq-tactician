open Names
open Constr
open Sorts
open Context

type sexpr = Node of sexpr list | Leaf of string

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

let global2s g =
  let a = Globnames.canonical_gr g in
  let b = try
      (* TODO: While moving from 8.11 to 8.12, this became problematic when using the
         `abstract` tactic (possibly in combination with `unshelve`). It seems that subproofs
         created by `abstract` are not available when replaying at Qed-time. This happens in the
         stdlib in Reals/Realanalysis5.v on line 1141. *)
      Nametab.path_of_global (a)
    with e ->
      Feedback.msg_warning (Pp.str "A recoverable error was raised in Tactician. Please report.");
      Libnames.make_path DirPath.empty (Id.of_string "a") in
  s2s (Libnames.string_of_path b)

let sorts2s = function
  | SProp  -> [s2s "SProp"]
  | Prop   -> [s2s "Prop"]
  | Set    -> [s2s "Set"]
  | Type l -> [s2s "Type"; (* TODO: Printing is not optimal here *)
               s2s (Pp.string_of_ppcmds (format_oneline (Univ.Universe.pr l)))]

let instance2s i =
  let levels = Univ.Instance.to_array i in
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

let constr_to_glob_constr t env sigma =
  Detyping.detype Detyping.Later false Id.Set.empty env sigma t

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
      (* I would think that `constrs` is always empty *)
      let sentences = Array.to_list (Array.map (aux ls) constrs) in
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
