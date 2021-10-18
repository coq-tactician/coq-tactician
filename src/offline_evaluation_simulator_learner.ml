open Tactic_learner
open Naiveknn_learner

let data_file =
  let file = ref None in
  (fun () ->
     match !file with
     | None -> let filename = Option.default "" Ltacrecord.base_filename ^ ".eval" in
       let k = Ltacrecord.open_permanently filename in
       file := Some k;
       k
     | Some f -> f)

module OfflineEvaluationSimulatorLearner : TacticianOnlineLearnerType = functor (TS : TacticianStructures) -> struct
  module LH = Learner_helper.L(TS)
  open TS
  module Learner = ComplexNaiveKnn(TS)

  type model = { model : Learner.model
               ; data : (data_status * Names.Constant.t * (outcome list * tactic) list) list; last_hash : int }

  let last_model = Summary.ref ~name:"offline-evaluation-simulator-learner-lastmodel" []
  let persistent_data = ref []
  let hashes = ref Int.Set.empty

  let empty () = { model = Learner.empty (); data = []; last_hash = 0 }

  let cache_type name =
    let dirp = Global.current_dirpath () in
    if Libnames.is_dirpath_prefix_of dirp (Names.ModPath.dp @@ Names.Constant.modpath name) then `File else `Dependency

  let calculate_k model outcome tac =
    (* TODO: Fill in *)
    let preds = Learner.predict model [{parents = []; siblings = End; state = outcome.before}] in
    let preds = IStream.to_list preds in
    let preds = List.map (fun p -> p.tactic) preds in
    let k = Tactician_util.safe_index0 (fun x y -> tactic_hash x = tactic_hash y) tac preds in
    Option.default (-1) k

  let next_knn model status name ls =
      List.fold_left (fun model (outcomes, tac) -> Learner.learn model status name outcomes tac) model ls

  let eval_intra_step acc (status, name, ls) =
    match cache_type name with
    | `File ->
      List.fold_left (fun acc (outcomes, tac) ->
          List.fold_left (fun (model, acc) outcome ->
              let k = calculate_k model outcome tac in
              Learner.learn model status name [outcome] tac, k::acc
            ) acc outcomes
        ) acc ls
    | `Dependency -> next_knn (fst acc) status name ls, snd acc

  let eval_intra data =
    List.rev @@ snd @@ List.fold_left eval_intra_step (Learner.empty (), []) data

  let eval_intra_partial_step acc (status, name, ls) =
    match cache_type name with
    | `File ->
      List.fold_left (fun (model, acc) (outcomes, tac) ->
          let acc = List.fold_left (fun (acc) outcome ->
              let k = calculate_k model outcome tac in
              k::acc
            ) acc outcomes in
          Learner.learn model status name outcomes tac, acc
        ) acc ls
    | `Dependency -> next_knn (fst acc) status name ls, snd acc

  let eval_intra_partial data =
    List.rev @@ snd @@ List.fold_left eval_intra_partial_step (Learner.empty (), []) data

  let eval_inter_step (model, acc) (status, name, ls) =
    let next_knn = next_knn model status name ls in
    match cache_type name with
    | `File ->
      let acc = List.fold_left (fun acc (outcomes, tac) ->
          List.fold_left (fun acc outcome ->
              calculate_k model outcome tac :: acc
            ) acc outcomes
        ) acc ls in
      next_knn, acc
    | `Dependency -> next_knn, acc

  let eval_inter data =
    List.rev @@ snd @@ List.fold_left eval_inter_step (Learner.empty (), []) data

  let learn db status name outcomes tac =
    let hash = Hashtbl.hash_param 255 255 (db.last_hash, Names.Constant.hash name, tactic_hash tac) in
    let model = match db.data with
    | (pstatus, pname, ls)::_ when not @@ Names.Constant.equal name pname ->
      next_knn db.model pstatus pname ls
    | _ -> db.model
    in
    let data = match db.data with
      | (pstatus, pname, ls)::data when Names.Constant.equal name pname ->
        (pstatus, pname, (outcomes, tac)::ls)::data
      | _ -> (status, name, [outcomes, tac])::db.data in
    last_model := data;
    (match cache_type name, status with
     | `File, Original ->
       if not @@ Int.Set.mem hash !hashes then begin
         let persistent = List.rev_map (fun outcome ->
             calculate_k model outcome tac
           ) outcomes in
         (* print_endline (String.concat ", " @@ List.map string_of_int persistent); *)
         (* (match status with *)
         (*  | Original -> print_endline "original" *)
         (*  | Substituted -> print_endline "substituted" *)
         (*  | Discharged -> print_endline "discharged"); *)
         hashes := Int.Set.add hash !hashes;
         persistent_data := persistent @ !persistent_data;
       end;
     | _ -> ());
    { model; data; last_hash = hash }
  let predict db situations = IStream.empty
  let evaluate db _ _ = 0., db

  (* We have to do some reversals before the evaluation *)
  let preprocess model =
    List.rev_map (fun (state, name, ls) -> state, name, List.rev ls) model

  let rec transpose lss long =
    let row = List.map (fun ls -> List.nth_opt ls 0) lss in
    match Option.List.flatten row with
    | [] -> if long then print_endline "LONG"; []
    | _ ->
      let long = long || Option.List.map (fun x -> x) row = None in
      let row = String.concat "\t" @@
        List.map (fun x -> Option.default "" @@ Option.map string_of_int x) row in
      let tail ls = match ls with
        | [] -> []
        | _::ls -> ls in
      let rem = List.map tail lss in
      (row ^ "\n") :: transpose rem long

  let endline_hook () = print_endline "evaluating";
    let persistent_data = List.rev !persistent_data in
    let data = preprocess !last_model in
    let eval = transpose [eval_intra data; eval_intra_partial data; eval_inter data; persistent_data] false in
    List.iter (output_string (data_file ())) eval

  let () = Declaremods.append_end_library_hook endline_hook
end

(* let () = register_online_learner "offline-evaluation-simulator-learner" (module OfflineEvaluationSimulatorLearner) *)
(* let () = Tactic_learner_internal.disable_queue () *)
