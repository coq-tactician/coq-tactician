open Tactic_learner
open Context

type feature = int
module FeatureOrd = struct
  type t = feature
  let compare = Int.compare
end
module Frequencies = Map.Make(FeatureOrd)

module IntMap = Stdlib.Map.Make(struct type t = int
    let compare = Int.compare end)


module L (TS: TacticianStructures) = struct
  open TS

  let rec sexpr_to_string = function
    | Leaf str -> str
    | Node ls -> "(" ^ (String.concat " " (List.map sexpr_to_string ls)) ^ ")"

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
    | [_] -> []
    | x::ls -> x :: removelast ls

  let context_map f g =
    List.map (function
        | Named.Declaration.LocalAssum (id, typ) ->
          Named.Declaration.LocalAssum (id, f typ)
        | Named.Declaration.LocalDef (id, term, typ) ->
          Named.Declaration.LocalDef (id, g term, f typ))

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

  let remove_dups_and_sort ranking =
    let ranking_map = List.fold_left
        (fun map (score, tac) ->
           IntMap.update
             (tactic_hash tac)
             (function
               | None -> Some (score, tac)
               | Some (lscore, ltac) ->
                 if score > lscore then Some (score, tac) else Some (lscore, ltac)
             )
             map
        )
        IntMap.empty
        ranking
    in
    let new_ranking = List.map (fun (_hash, (score, tac)) -> (score, tac)) (IntMap.bindings ranking_map) in
    List.sort (fun (x, _) (y, _) -> Float.compare y x) new_ranking

  (* TODO: This doesn't work on multisets *)
  let intersect cmp l1 l2 =
    let rec intersect l1 l2 =
      match l1 with
      | [] -> []
      | h1::t1 -> (
          match l2 with
          | [] -> []
          | h2::_ when cmp h1 h2 < 0 -> intersect t1 l2
          | h2::t2 when cmp h1 h2 > 0 -> intersect l1 t2
          | _::t2 -> (
              match intersect t1 t2 with
              | [] -> [h1]
              | h3::_ as l when h3 = h1 -> l
              | _::_ as l -> h1::l
            )
        ) in
    intersect l1 l2

  let default d opt = match opt with | None -> d | Some x -> x

end
