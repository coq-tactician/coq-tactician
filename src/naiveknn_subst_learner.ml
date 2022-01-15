open Tactic_learner
open Learner_helper
open Features
open Context
open Names

module NaiveKnnSubst (SF : sig type second_feat end) = functor (TS : TacticianStructures) -> struct
  module LH = L(TS)
  open TS
  open LH
  open SF

    type db_entry =
      { features : feature list;
        context  : (second_feat list, second_feat list) Context.Named.pt;
        obj      : tactic;
        substituted_hash : int
      }
    type database =
      { entries     : db_entry list
      ; length      : int
      ; frequencies : int Frequencies.t}

    type model = database

    let empty () = {entries = []; length = 0; frequencies = Frequencies.empty}

    let rec deletelast = function
      | [] -> assert false
      | [x] -> (x.features, [])
      | x::ls' -> let (last, lsn) = deletelast ls' in (last, x::lsn)

    let decl2id = function
      | Named.Declaration.LocalAssum (id, _) -> id.binder_name
      | Named.Declaration.LocalDef (id, _, _) -> id.binder_name

    let find_decl ctx id =
      List.find_opt (function
          | Named.Declaration.LocalAssum (id', _) -> Id.equal id id'.binder_name
          | Named.Declaration.LocalDef (id', _, _) -> Id.equal id id'.binder_name
        ) ctx

    let decl2feats = function
      | Named.Declaration.LocalAssum (_, typ) -> typ
      | Named.Declaration.LocalDef (_, _, typ) -> typ

    let tactic_simplified_hash ctx tac =
      let tac = Tactic_substitute.tactic_substitute (fun id ->
          match find_decl ctx id with
          | None -> Id.of_string "__knnpl"
          | Some _ -> id)
          (tactic_repr tac) in
      Feedback.msg_info (Pp.str (sexpr_to_string (tactic_sexpr (tactic_make tac))));
      tactic_hash (tactic_make tac)

    let add db b obj ps_to_feat ctx_to_feat =
      let feats = ps_to_feat b in
      let ctx = ctx_to_feat (proof_state_hypotheses b) in
      let sh = tactic_simplified_hash ctx obj in
      let comb = {features = feats; context = ctx; obj = obj; substituted_hash = sh} in
      let newfreq = List.fold_left
          (fun freq f ->
             Frequencies.update f (fun y -> Some ((Option.default 0 y) + 1)) freq)
          db.frequencies
          feats in
      let max = 1000 in
      let last, purgedentries = if db.length >= max then deletelast db.entries else ([], db.entries) in
      let newfreq = List.fold_left
          (fun freq f ->
             Frequencies.update f (fun y -> Some ((Option.default 1 y) - 1)) freq)
          newfreq
          last in
      (* TODO: Length needs to be adjusted if we want to use multisets  *)
      let l = if db.length >= max then db.length else db.length + 1 in
      {entries = comb::purgedentries; length = l; frequencies = newfreq}

    let learn db _status outcomes tac ps_to_feat ctx_to_feat =
      List.fold_left (fun db out -> add db out.before tac ps_to_feat ctx_to_feat) db outcomes

    let remove_dups ranking =
      let ranking_map = List.fold_left
          (fun map (score, ({obj; substituted_hash; _} as entry)) ->
             (* TODO: this is a total hack *)
             IntMap.update
               (substituted_hash (* (tactic_make tac') *))
               (function
                 | None -> Some (score, entry)
                 | Some (lscore, ltac) ->
                   if score > lscore then Some (score, entry) else Some (lscore, ltac)
               )
               map
          )
          IntMap.empty
          ranking
      in
      List.map (fun (_hash, (score, tac)) -> (score, tac)) (IntMap.bindings ranking_map)

    let predict db f ps_to_feat ctx_to_feat tfidf =
      if f = [] then IStream.empty else
        let ps = (List.hd f).state in
        let ctx = ctx_to_feat (proof_state_hypotheses ps) in
        let feats = ps_to_feat ps in
        let tdidfs = List.map
            (fun ent -> let x = tfidf db.length db.frequencies feats ent.features in (x, ent))
            db.entries in
        let deduped = remove_dups tdidfs in
        let sorted = List.stable_sort (fun (x, _) (y, _) -> Float.compare y x) deduped in
        let subst (_, {context; obj; _}) =
            let subst id =
              match find_decl context id with
              | None -> id
              | Some decl ->
                let feats = decl2feats decl in
                let ids_scored = List.map
                    (fun decl -> let x = tfidf db.length db.frequencies feats (decl2feats decl) in (x, decl2id decl))
                    ctx in
                let ids_sorted = List.sort (fun (x, _) (y, _) -> Float.compare y x) ids_scored in
                match ids_sorted with
                | [] -> id
                | (_, id)::_ -> id
            in
            let tactic = tactic_make (Tactic_substitute.tactic_substitute subst (tactic_repr obj)) in
            {confidence = Float.neg_infinity; focus = 0; tactic} in
        let out = List.map (fun (a, entry) -> { confidence = a; focus = 0; tactic = entry.obj }) sorted in
        let subst_stream = IStream.map
            (fun (s, p) ->
               let ts = subst (s, p) in
               if (tactic_hash p.obj) = (tactic_hash ts.tactic) then
                 {confidence = Float.neg_infinity; focus = 0; tactic = tactic_make (TacId []) } else ts
            )
            (IStream.of_list sorted) in
        IStream.app (IStream.of_list out) subst_stream

    let evaluate db _ _ = 1., db

  end

module SimpleNaiveSubstKnn : TacticianOnlineLearnerType = functor (TS : TacticianStructures) -> struct
  module NaiveKnnSubst = NaiveKnnSubst(struct type second_feat = int end)(TS)
  include NaiveKnnSubst
  module FH = F(TS)
  open FH
  let learn db _status outcomes tac = learn db _status outcomes tac proof_state_to_simple_ints context_simple_ints
  let predict db f = predict db f proof_state_to_simple_ints context_simple_ints tfidf
end

module ComplexNaiveSubstKnn : TacticianOnlineLearnerType = functor (TS : TacticianStructures) -> struct
  module NaiveKnnSubst = NaiveKnnSubst(struct type second_feat = Features.feat_kind * int end)(TS)
  include NaiveKnnSubst
  module FH = F(TS)
  module LH = L(TS)
  open FH
  open LH
  let learn db _status outcomes tac = learn db _status outcomes tac
      (fun x -> remove_feat_kind @@ proof_state_to_complex_ints x)
      context_complex_ints
  let predict db f = predict db f proof_state_to_complex_ints
      (fun x -> context_map remove_feat_kind remove_feat_kind @@ context_complex_ints x)
      manually_weighed_tfidf

end

(* let () = register_online_learner "simple-naive-knn-subst" (module SimpleNaiveSubstKnn) *)
(* let () = register_online_learner "complex-naive-knn-subst" (module ComplexNaiveSubstKnn) *)
