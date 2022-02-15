open Ltac_plugin
open Tactypes
open Coq_ast_cata
open Monad_util
open Tacexpr_functor
open Constrexpr_functor
open Coq_ast_monadic_map
open Names

module CAst (M : Monad.Def) = struct
  open Cata(M)
  open M
  open WithMonadNotations(M)
  module Mapper = Mapper(M)
  open Monad.Make(M)

  (* let recursion_order_lident_map f = function *)
  (*     | CStructRec x -> *)
  (*       let+ x = f x in *)
  (*       CStructRec x *)
  (*     | CWfRec (a, b) -> *)
  (*       let+ a = f a in *)
  (*       CWfRec (a, b) *)
  (*     | CMeasureRec (a, b, c) -> *)
  (*       let+ a = Mapper.option_map f a in *)
  (*       CMeasureRec (a, b, c) *)
  (* let fix_expr_lident_map f ((a, b, c, d, e) : _ fix_expr) = *)
  (*   let+ a = f a *)
  (*   and+ b = Mapper.option_map (Mapper.cast_map (recursion_order_lident_map f)) b in *)
  (*   a, b, c, d, e *)
  (* let cofix_expr_lident_map f ((a, b, c, d) : _ cofix_expr) = *)
  (*   let+ a = f a in *)
  (*   a, b, c, d *)
  (* let constr_expr_lident_map (f : lident -> lident t) (t : constr_expr) = *)
  (*   Mapper.cast_map (fun t -> *)
  (*     match t with *)
  (*     | CRef (a, b) -> _ *)
  (*     | CFix (a, b) -> *)
  (*       let+ a = f a *)
  (*       and+ b = List.map (fix_expr_lident_map f) b in *)
  (*       CFix (a, b) *)
  (*     | CCoFix (a, b) -> *)
  (*       let+ a = f a *)
  (*       and+ b = List.map (cofix_expr_lident_map f) b in *)
  (*       CCoFix (a, b) *)
  (*     | CProdN (_, _) -> _ *)
  (*     | CLambdaN (_, _) -> _ *)
  (*     | CLetIn (_, _, _, _) -> _ *)

  (*     | CAppExpl (_, _) -> _ *)
  (*     | CApp (_, _) -> _ *)
  (*     | CRecord _ -> _ *)
  (*     | CCases (_, _, _, _) -> _ *)
  (*     | CLetTuple (_, _, _, _) -> _ *)
  (*     | CIf (_, _, _, _) -> _ *)
  (*     | CHole (_, _, _) -> _ *)
  (*     | CPatVar _ -> _ *)
  (*     | CEvar (_, _) -> _ *)
  (*     | CSort _ -> _ *)
  (*     | CCast (_, _) -> _ *)
  (*     | CNotation (_, _) -> _ *)
  (*     | CGeneralization (_, _, _) -> _ *)
  (*     | CPrim _ -> _ *)
  (*     | CDelimiters (_, _) -> _ *)
  (*   ) t *)

  (* let with_lident_map (f : lident -> lident t) (m : sequence_record) : sequence_record  = *)
  (*   let constr_expr_map (t : constr_expr) = Mapper.cast_map (fun t -> *)
  (*       match t with *)
  (*       | CRef (a, b) -> _ *)
  (*       | CFix (a, b) -> *)
  (*         let+ a = f a *)
  (*         and+ b = List.map (fun (a, b, c, d, e) -> *)
  (*             let+ a = f a *)
  (*             and+ b = Mapper.option_map (Mapper.cast_map (function *)
  (*                 | CStructRec x -> *)
  (*                   let+ x = f x in *)
  (*                   CStructRec x *)
  (*                 | CWfRec (a, b) -> *)
  (*                   let+ a = f a in *)
  (*                   CWfRec (a, b) *)
  (*                 | CMeasureRec (a, b, c) -> *)
  (*                   let+ a = Mapper.option_map f a in *)
  (*                   CMeasureRec (a, b, c) *)
  (*               )) b in *)
  (*             a, b, c, d, e) b in *)
  (*         CFix (a, b) *)
  (*       | CCoFix (_, _) -> _ *)
  (*       | CProdN (_, _) -> _ *)
  (*       | CLambdaN (_, _) -> _ *)
  (*       | CLetIn (_, _, _, _) -> _ *)
  (*       | CAppExpl (_, _) -> _ *)
  (*       | CApp (_, _) -> _ *)
  (*       | CRecord _ -> _ *)
  (*       | CCases (_, _, _, _) -> _ *)
  (*       | CLetTuple (_, _, _, _) -> _ *)
  (*       | CIf (_, _, _, _) -> _ *)
  (*       | CHole (_, _, _) -> _ *)
  (*       | CPatVar _ -> _ *)
  (*       | CEvar (_, _) -> _ *)
  (*       | CSort _ -> _ *)
  (*       | CCast (_, _) -> _ *)
  (*       | CNotation (_, _) -> _ *)
  (*       | CGeneralization (_, _, _) -> _ *)
  (*       | CPrim _ -> _ *)
  (*       | CDelimiters (_, _) -> _ *)
  (*     ) t in *)
  (*   let cases_pattern_expr_map (t : cases_pattern_expr) = obj#f t in *)
  (*   { m with *)
  (*     glob_tacexpr = (fun t -> *)
  (*       let* t = m.glob_tacexpr t in *)
  (*       tacexpr_map t) *)
  (*   ; raw_tacexpr = (fun t -> *)
  (*         let* t = m.raw_tacexpr t in *)
  (*         tacexpr_map t) *)
  (*   ; glob_intro_pattern_action_expr = (fun t -> *)
  (*       let* t = m.glob_intro_pattern_action_expr t in *)
  (*       intro_pattern_action_expr_map t) *)
  (*   ; raw_intro_pattern_action_expr = (fun t -> *)
  (*       let* t = m.raw_intro_pattern_action_expr t in *)
  (*       intro_pattern_action_expr_map t) *)
  (*   ; glob_or_and_intro_pattern_expr = (fun t -> *)
  (*       let* t = m.glob_or_and_intro_pattern_expr t in *)
  (*       or_and_intro_pattern_expr_map t) *)
  (*   ; raw_or_and_intro_pattern_expr = (fun t -> *)
  (*       let* t = m.raw_or_and_intro_pattern_expr t in *)
  (*       or_and_intro_pattern_expr_map t) *)
  (*   ; constr_expr = (fun t -> *)
  (*       let* t = m.constr_expr t in *)
  (*     constr_expr_map t) *)
  (*   ; cases_pattern_r = (fun t -> *)
  (*       let* t = m.cases_pattern_r t in *)
  (*       cases_pattern_expr_map t) *)
  (*   } *)
  let with_cast_map (obj : <f : 'a. 'a CAst.t -> 'a CAst.t t>) (m : sequence_record) : sequence_record  =
    let cast_map f x =
      let* x = obj#f x in
      Mapper.cast_map f x in
    let intro_pattern_action_expr_map = function
      | IntroInjection ls ->
        let+ ls = List.map obj#f ls in
        IntroInjection ls
      | IntroApplyOn (x, y) ->
        let+ x = obj#f x
        and+ y = obj#f y in
        IntroApplyOn (x, y)
      | x -> return x
    in
    let or_and_intro_pattern_expr_map = function
      | IntroOrPattern ls ->
        let+ ls = List.map (List.map obj#f) ls in
        IntroOrPattern ls
      | IntroAndPattern ls ->
        let+ ls = List.map obj#f ls in
        IntroAndPattern ls
    in
    let tacexpr_map t =
      match t with
      | TacAtom x ->
        let* x = obj#f x in
        let+ x = Mapper.cast_map (function
            | TacIntroPattern (x, ls) ->
              let+ ls = List.map obj#f ls in
              TacIntroPattern (x, ls)
            | TacApply (a, b, c, d) ->
              let+ d = Mapper.option_map (fun (a, b) ->
                  let+ b = Mapper.option_map obj#f b in
                  a, b) d in
              TacApply (a, b, c, d)
            | TacAssert (a, b, c, d, e) ->
              let+ d = Mapper.option_map obj#f d in
              TacAssert (a, b, c, d, e)
            | TacLetTac (a, b, c, d, e, f) ->
              let+ f = Mapper.option_map obj#f f in
              TacLetTac (a, b, c, d, e, f)
            | TacInductionDestruct (a, b, (c, d)) ->
              let+ c = List.map (fun (a, (b, c), d) ->
                  let+ b = Mapper.option_map obj#f b
                  and+ c = Mapper.option_map (Mapper.or_var_map obj#f) c in
                  a, (b, c), d
                ) c in
              TacInductionDestruct (a, b, (c, d))
            | TacInversion (a, b) ->
              let+ a = match a with
                | NonDepInversion (a, b, c) ->
                  let+ c = Mapper.option_map (Mapper.or_var_map obj#f) c in
                  NonDepInversion (a, b, c)
                | DepInversion (a, b, c) ->
                  let+ c = Mapper.option_map (Mapper.or_var_map obj#f) c in
                  DepInversion (a, b, c)
                | InversionUsing (a, b) ->
                  return @@ InversionUsing (a, b) in
              TacInversion (a, b)
            | x -> return x
          ) x in
        TacAtom x
      | TacArg x ->
        let+ x = obj#f x in
        TacArg x
      | TacML x ->
        let+ x = obj#f x in
        TacML x
      | TacAlias x ->
        let+ x = obj#f x in
        TacAlias x
      | _ -> return t
    in
    let constr_expr_map (t : constr_expr) = cast_map (fun t ->
        match t with
        | CRef (a, b) ->
          let+ a = obj#f a in
          CRef (a, b)
        | CFix (a, b) ->
          let+ a = obj#f a
          and+ b = List.map (fun (b, (c : constr_dispatch recursion_order_expr option), d, e, f) ->
              let+ b = obj#f b
              and+ c = Mapper.option_map (cast_map (function
                  | CStructRec x ->
                    let+ x = obj#f x in
                    CStructRec x
                  | CWfRec (a, b) ->
                    let+ a = obj# f a in
                    CWfRec (a, b)
                  | CMeasureRec (a, b, c) ->
                    let+ a = Mapper.option_map obj#f a in
                    CMeasureRec (a, b, c)
                )) c in
            b, c, d, e, f) b in
          CFix (a, b)
        (* | CCoFix (_, _) -> _ *)
        (* | CProdN (_, _) -> _ *)
        (* | CLambdaN (_, _) -> _ *)
        (* | CLetIn (_, _, _, _) -> _ *)
        (* | CAppExpl (_, _) -> _ *)
        (* | CApp (_, _) -> _ *)
        (* | CRecord _ -> _ *)
        (* | CCases (_, _, _, _) -> _ *)
        (* | CLetTuple (_, _, _, _) -> _ *)
        (* | CIf (_, _, _, _) -> _ *)
        (* | CHole (_, _, _) -> _ *)
        (* | CPatVar _ -> _ *)
        (* | CEvar (_, _) -> _ *)
        (* | CSort _ -> _ *)
        (* | CCast (_, _) -> _ *)
        (* | CNotation (_, _) -> _ *)
        (* | CGeneralization (_, _, _) -> _ *)
        (* | CPrim _ -> _ *)
        (* | CDelimiters (_, _) -> _ *)
        | x -> return x
      ) t in
    let cases_pattern_expr_map (t : cases_pattern_expr) = obj#f t in
    { m with
      glob_tacexpr = (fun t ->
        let* t = m.glob_tacexpr t in
        tacexpr_map t)
    ; raw_tacexpr = (fun t ->
          let* t = m.raw_tacexpr t in
          tacexpr_map t)
    ; glob_intro_pattern_action_expr = (fun t ->
        let* t = m.glob_intro_pattern_action_expr t in
        intro_pattern_action_expr_map t)
    ; raw_intro_pattern_action_expr = (fun t ->
        let* t = m.raw_intro_pattern_action_expr t in
        intro_pattern_action_expr_map t)
    ; glob_or_and_intro_pattern_expr = (fun t ->
        let* t = m.glob_or_and_intro_pattern_expr t in
        or_and_intro_pattern_expr_map t)
    ; raw_or_and_intro_pattern_expr = (fun t ->
        let* t = m.raw_or_and_intro_pattern_expr t in
        or_and_intro_pattern_expr_map t)
    ; constr_expr = (fun t ->
        let* t = m.constr_expr t in
      constr_expr_map t)
    ; cases_pattern_r = (fun t ->
        let* t = m.cases_pattern_r t in
        cases_pattern_expr_map t)
    }

end
