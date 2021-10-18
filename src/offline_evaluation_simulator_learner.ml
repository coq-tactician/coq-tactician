open Tactic_learner
open Names

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
  module Learner = Lshf_learner.ComplexLSHF

  type dynamic_learner =
    { learn : data_status -> Constant.t -> outcome list -> TS.tactic -> dynamic_learner
    ; predict : situation list -> prediction IStream.t
    ; evaluate : outcome -> tactic -> dynamic_learner * float }

  let new_learner (module Learner : TacticianOnlineLearnerType) =
    let module Learner = Learner(TS) in
    let rec recurse model =
      { learn = (fun status loc exes tac ->
            recurse @@ Lazy.from_val @@ Learner.learn (Lazy.force model) status loc exes tac)
      ; predict = (fun t ->
            Learner.predict (Lazy.force model) t)
      ; evaluate = (fun outcome tac ->
            let f, model = Learner.evaluate (Lazy.force model) outcome tac in
            recurse @@ Lazy.from_val model, f) } in
    (* Note: This is lazy to give people a chance to set GOptions before a learner gets initialized *)
    recurse (lazy (Learner.empty ()))

  let learners : (module TacticianOnlineLearnerType) list =
    [
      (module Naiveknn_learner.SimpleNaiveKnn)
    ; (module Naiveknn_learner.ComplexNaiveKnn)
    ; (module Lshf_learner.SimpleLSHF)
    ; (module Lshf_learner.ComplexLSHF)
    ]

  let new_learners () = List.map new_learner learners

  type model = { learners : dynamic_learner list
               ; data : (data_status * Names.Constant.t * (outcome list * tactic) list) list; last_hash : int }

  let last_model = Summary.ref ~name:"offline-evaluation-simulator-learner-lastmodel" []
  let persistent_data = ref (List.init (List.length learners) (fun _ -> []))
  let hashes = ref Int.Set.empty

  let empty () = { learners = new_learners (); data = []; last_hash = 0 }

  let cache_type name =
    let dirp = Global.current_dirpath () in
    if Libnames.is_dirpath_prefix_of dirp (Names.ModPath.dp @@ Names.Constant.modpath name) then `File else `Dependency

  let calculate_k learner outcome tac =
    (* TODO: Fill in parents and other info *)
    let preds = learner.predict [{parents = []; siblings = End; state = outcome.before}] in
    let preds = IStream.to_list preds in
    let preds = List.map (fun p -> p.tactic) preds in
    let k = Tactician_util.safe_index0 (fun x y -> tactic_hash x = tactic_hash y) tac preds in
    Option.default (-1) k

  let next_knn learner status name ls =
      List.fold_left (fun learner (outcomes, tac) -> learner.learn status name outcomes tac) learner ls

  let eval_intra_step acc (status, name, ls) =
    match cache_type name with
    | `File ->
      List.fold_left (fun acc (outcomes, tac) ->
          List.fold_left (fun (learner, acc) outcome ->
              let k = calculate_k learner outcome tac in
              learner.learn status name [outcome] tac, k::acc
            ) acc outcomes
        ) acc ls
    | `Dependency -> next_knn (fst acc) status name ls, snd acc

  let eval_intra data learner =
    List.rev @@ snd @@ List.fold_left eval_intra_step (learner, []) data

  let eval_intra_partial_step acc (status, name, ls) =
    match cache_type name with
    | `File ->
      List.fold_left (fun (learner, acc) (outcomes, tac) ->
          let acc = List.fold_left (fun (acc) outcome ->
              let k = calculate_k learner outcome tac in
              k::acc
            ) acc outcomes in
          learner.learn status name outcomes tac, acc
        ) acc ls
    | `Dependency -> next_knn (fst acc) status name ls, snd acc

  let eval_intra_partial data learner =
    List.rev @@ snd @@ List.fold_left eval_intra_partial_step (learner, []) data

  let eval_inter_step (learner, acc) (status, name, ls) =
    let next_knn = next_knn learner status name ls in
    match cache_type name with
    | `File ->
      let acc = List.fold_left (fun acc (outcomes, tac) ->
          List.fold_left (fun acc outcome ->
              calculate_k learner outcome tac :: acc
            ) acc outcomes
        ) acc ls in
      next_knn, acc
    | `Dependency -> next_knn, acc

  let eval_inter data learner =
    List.rev @@ snd @@ List.fold_left eval_inter_step (learner, []) data

  let learn db status name outcomes tac =
    let hash = Hashtbl.hash_param 255 255 (db.last_hash, Names.Constant.hash name, tactic_hash tac) in
    let update_learner learner = match db.data with
    | (pstatus, pname, ls)::_ when not @@ Names.Constant.equal name pname ->
      next_knn learner pstatus pname ls
    | _ -> learner
    in
    let learners = List.map update_learner db.learners in
    let data = match db.data with
      | (pstatus, pname, ls)::data when Names.Constant.equal name pname ->
        (pstatus, pname, (outcomes, tac)::ls)::data
      | _ -> (status, name, [outcomes, tac])::db.data in
    last_model := data;
    (match cache_type name, status with
     | `File, Original ->
       if not @@ Int.Set.mem hash !hashes then begin
         persistent_data := List.map2 (fun pdata learner ->
             List.fold_left (fun pdata outcome ->
                 calculate_k learner outcome tac :: pdata
               ) pdata outcomes
           ) !persistent_data learners;
         (* print_endline (String.concat ", " @@ List.map string_of_int persistent); *)
         (* (match status with *)
         (*  | Original -> print_endline "original" *)
         (*  | Substituted -> print_endline "substituted" *)
         (*  | Discharged -> print_endline "discharged"); *)
         hashes := Int.Set.add hash !hashes;
       end;
     | _ -> ());
    { learners; data; last_hash = hash }
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
    let persistent_data = List.map List.rev !persistent_data in
    let data = preprocess !last_model in
    let eval_schemes = [eval_intra; eval_intra_partial; eval_inter] in
    let eval = List.flatten @@ List.map2
        (fun learner persistent -> persistent :: List.map (fun f -> f data learner) eval_schemes)
        (new_learners ()) persistent_data in
    let eval = transpose (eval @ persistent_data) false in
    List.iter (output_string (data_file ())) eval

  let () = Declaremods.append_end_library_hook endline_hook
end

let () = register_online_learner "offline-evaluation-simulator-learner" (module OfflineEvaluationSimulatorLearner)
let () = Tactic_learner_internal.disable_queue ()
