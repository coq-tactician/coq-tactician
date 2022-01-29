open Ltac_plugin
open Tacexpr
open Tactypes

let no_nested_pattern (p : _ intro_pattern_expr) = match p with
  | IntroForthcoming _ -> true
  | IntroNaming _ -> true
  | IntroAction _ -> false
let no_nested_patterns (ps : _ intro_pattern_expr CAst.t list) =
  List.fold_left (&&) true @@ List.map (fun p -> no_nested_pattern CAst.(p.v)) ps

let tactic_name_remove (t : glob_tactic_expr) : glob_tactic_expr = match t with
  | TacAtom CAst.{v; _} -> TacAtom (CAst.make (match v with
      | TacIntroPattern (flg, [CAst.{v=IntroNaming _; loc}]) ->
        TacIntroPattern (flg, [CAst.make ?loc (IntroNaming Namegen.IntroAnonymous)])
      | TacInductionDestruct (rflg, eflg, (cls, None)) ->
        let cls = List.map (fun (c, (eqn, asc), inc) ->
            let asc = match asc with
              | None -> None
              | Some asc -> (match asc with
                  | Locus.ArgArg CAst.{v; _} ->
                    (match v with
                    | IntroOrPattern ps ->
                      if List.fold_left (&&) true @@ List.map no_nested_patterns ps then None else Some asc
                    | IntroAndPattern ps ->
                      if no_nested_patterns ps then None else Some asc)
                  | Locus.ArgVar _ -> None) in
            c, (eqn, asc), inc
          ) cls in
        TacInductionDestruct (rflg, eflg, (cls, None))
      | TacAssert (flg, b, by, Some pat, term) when no_nested_pattern pat.v ->
        TacAssert (flg, b, by, None, term)
      | _ -> v))
  | TacAlias CAst.{loc; v=(e, args)} ->
    (match e, args with
     | e, [TacGeneric term; TacGeneric pat] when Names.KerName.equal e @@ Tactic_annotate.internal_tactics_ref_lookup "injection_x_as" ->
       let pat = Genarg.out_gen (Genarg.glbwit (Genarg.wit_list Tacarg.wit_simple_intropattern)) pat in
       let pat = if no_nested_patterns pat then [] else pat in
       let pat = Genarg.in_gen (Genarg.glbwit (Genarg.wit_list Tacarg.wit_simple_intropattern)) pat in
       TacAlias (CAst.make ?loc (e, [TacGeneric term; TacGeneric pat]))
     | _ -> t)
  | _ -> t
