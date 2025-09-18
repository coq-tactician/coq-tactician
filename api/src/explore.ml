open Tactician_ltac1_record_plugin
open Names
open Ltac_plugin
open Graph_def

module Api = Graph_api.MakeRPC(Capnp_rpc_lwt)
module W = Graph_capnp_generator.Writer(Api)
open Capnp_rpc_lwt

module G = Neural_learner.G
module CICGraph = Neural_learner.CICGraphMonad
open Neural_learner.GB

module TacticMap = Neural_learner.TacticMap


exception NoSuchTactic
exception MismatchedArguments
exception IllegalArgument
exception ParseError

let write_execution_result env res ps obj =
  let module ExecutionResult = Api.Builder.ExecutionResult in
  let module Graph = Api.Builder.Graph in
  let module ProofState = Api.Builder.ProofState in
  let module Node = Api.Builder.Node in

  (* Obtain the graph *)
  let (_, ps), { def_count; node_count; edge_count; defs; nodes; edges } =
    CICGraph.run_empty ps
      (G.HashMap.create 100) G.builder_nil 0 in
  let node_local_index (_, (def, i)) =
    if def then i else def_count + i in
  let context_map = List.fold_left (fun map { id; node; _ } ->
      let (p, n), _ = G.lower node in
      Id.Map.add id (p, node_local_index (p, n)) map) Id.Map.empty ps.context in
  let context_map_inv = Names.Id.Map.fold_left (fun id (_, node) m -> Int.Map.add node id m) context_map Int.Map.empty in

  (* Write graph to capnp structure *)
  let new_state = ExecutionResult.new_state_init res in
  let capnp_graph = ExecutionResult.NewState.graph_init new_state in
  let node_hash n = snd @@ G.transform_node_type n in
  let node_label n = fst @@ G.transform_node_type n in
  W.write_graph
    ~node_hash ~node_label ~node_lower:(fun n -> fst @@ G.lower n)
    ~node_dep_index:(fun _ -> 0) ~node_local_index
    ~node_count:(def_count + node_count) ~edge_count (Graph_def.AList.append defs nodes) edges capnp_graph;
  let state = ExecutionResult.NewState.state_init new_state in
  W.write_proof_state
    { node_depindex = (fun n -> 0)
    ; node_local_index = (fun n -> node_local_index (fst @@ G.lower n)) } state ps;
  let capability = obj context_map_inv in
  ExecutionResult.NewState.obj_set new_state (Some capability);
  Capability.dec_ref capability

let write_execution_result env res obj =
  let open Proofview in
  let open Notations in
  let complete =
    let module ExecutionResult = Api.Builder.ExecutionResult in
    tclUNIT () >>= fun () ->
    ExecutionResult.complete_set res; tclUNIT () in
  tclFOCUS ~nosuchgoal:complete 1 1 @@
  (Tactician_util.pr_proof_tac () >>= fun () ->
   gen_proof_state_tactic (Names.Id.Map.empty, Names.Cmap.empty) >>= fun ps ->
   write_execution_result env res ps obj; tclUNIT ())

let write_execution_result env state res obj =
  ignore (Pfedit.solve Goal_select.SelectAll None (write_execution_result env res obj) state)

let find_tactic tacs id =
  match TacticMap.find_opt id tacs with
  | None -> raise NoSuchTactic
  | Some x -> x

let find_argument context id =
  match Int.Map.find_opt id context with
  | None -> raise MismatchedArguments
  | Some x -> Tactic_one_variable.TVar x

let pp_tac tac = Sexpr.format_oneline (Pptactic.pr_glob_tactic (Global.env ()) tac)

let rec proof_object env state tacs context_map =
  let module ProofObject = Api.Service.ProofObject in
  let module ExecutionResult = Api.Builder.ExecutionResult in
  let module Exception = Api.Builder.Exception in
  let module Tactic = Api.Reader.Tactic in
  let module Argument = Api.Reader.Argument in
  ProofObject.local @@ object
    inherit ProofObject.service

    method run_tactic_impl params release_param_caps =
      release_param_caps ();
      let open ProofObject.RunTactic in
      let response, results = Service.Response.create Results.init_pointer in
      let res = Results.result_init results in
      let tac = Params.tactic_get params in
      let tac_id = Tactic.ident_get tac in
      let tac_args = Params.arguments_get_list params in
      begin
        try
          let tac_args = List.map (fun arg ->
              match Argument.get arg with
              | Argument.Undefined _ | Argument.Unresolvable -> raise IllegalArgument
              | Argument.Term t -> t
            ) tac_args in
          let tac_args = List.map (fun a -> Stdint.Uint32.to_int (Argument.Term.node_index_get a)) tac_args in
          let tac, params = find_tactic tacs tac_id in
          if params <> List.length tac_args then raise MismatchedArguments;
          let tac_args = List.map (find_argument context_map) tac_args in
          let tac = Tactic_one_variable.tactic_substitute tac_args tac in
          let tac = match tac with
            | None -> raise MismatchedArguments
            | Some tac -> tac in

          let prtac = pp_tac tac in
          Feedback.msg_notice @@ Pp.(str "run tactic " ++ prtac);

          let tac = Ltacrecord.parse_tac tac in
          let nosuchgoal = Proofview.tclZERO (Proof_bullet.SuggestNoSuchGoals (1, state)) in
          let tac = Proofview.tclFOCUS ~nosuchgoal 1 1 tac in
          try
            let state', _safe = Pfedit.solve Goal_select.SelectAll None tac state in
            write_execution_result env state' res (proof_object env state' tacs)
          with Logic_monad.TacticFailure e ->
            ExecutionResult.failure_set res
        with
        | NoSuchTactic ->
          let exc = ExecutionResult.protocol_error_init res in
          Exception.no_such_tactic_set exc
        | MismatchedArguments ->
          let exc = ExecutionResult.protocol_error_init res in
          Exception.mismatched_arguments_set exc
        | IllegalArgument ->
          let exc = ExecutionResult.protocol_error_init res in
          Exception.illegal_argument_set exc
      end;
      Service.return response
    method run_text_tactic_impl params release_param_caps =
      release_param_caps ();
      let open ProofObject.RunTextTactic in
      let response, results = Service.Response.create Results.init_pointer in
      let res = Results.result_init results in
      let tac = Params.tactic_get params in
      begin
        try
          let tac = try
            Tacinterp.interp @@ Pcoq.parse_string Pltac.tactic_eoi tac
          with e when CErrors.noncritical e ->
            raise NoSuchTactic in
          let nosuchgoal = Proofview.tclZERO (Proof_bullet.SuggestNoSuchGoals (1, state)) in
          let tac = Proofview.tclFOCUS ~nosuchgoal 1 1 tac in
          try
            let state', _safe = Pfedit.solve Goal_select.SelectAll None tac state in
            write_execution_result env state' res (proof_object env state' tacs)
          with Logic_monad.TacticFailure e ->
            ExecutionResult.failure_set res
        with
        | NoSuchTactic ->
          let exc = ExecutionResult.protocol_error_init res in
          Exception.no_such_tactic_set exc
        | MismatchedArguments ->
          let exc = ExecutionResult.protocol_error_init res in
          Exception.mismatched_arguments_set exc
        | IllegalArgument ->
          let exc = ExecutionResult.protocol_error_init res in
          Exception.illegal_argument_set exc
      end;
      Service.return response
  end


(* let available_tactics tacs = *)
(*   let module AvailableTactics = Api.Service.AvailableTactics in *)
(*   AvailableTactics.local @@ object *)
(*     inherit AvailableTactics.service *)

(*     method tactics_impl params release_param_caps = *)
(*       let open AvailableTactics.Tactics in *)
(*       release_param_caps (); *)
(*       let response, results = Service.Response.create Results.init_pointer in *)
(*       let tac_arr = Results.tactics_init results (TacticMap.cardinal tacs) in *)
(*       List.iteri (fun i (hash, (_tac, params)) -> *)
(*           let arri = Capnp.Array.get tac_arr i in *)
(*           Api.Builder.AbstractTactic.ident_set arri hash; *)
(*           Api.Builder.AbstractTactic.parameters_set_exn arri params) *)
(*         (TacticMap.bindings tacs); *)
(*       Service.return response *)

(*     method print_tactic_impl params release_param_caps = *)
(*       let open AvailableTactics.PrintTactic in *)
(*       release_param_caps (); *)
(*       let response, results = Service.Response.create Results.init_pointer in *)
(*       let id = Params.tactic_get params in *)
(*       let tac, params = find_tactic tacs id in *)
(*       let str = *)
(*         try Pp.string_of_ppcmds @@ pp_tac tac *)
(*         with NoSuchTactic -> "NoSuchTactic" in *)
(*       Results.tactic_set results str; *)
(*       Service.return response *)
(*   end *)

(* let pull_reinforce = *)
(*   let module Reinforce = Api.Service.PullReinforce in *)
(*   Reinforce.local @@ object *)
(*     inherit Reinforce.service *)

(*     method reinforce_impl params release_param_caps = *)
(*       let open Reinforce.Reinforce in *)
(*       release_param_caps (); *)
(*       let response, results = Service.Response.create Results.init_pointer in *)

(*       Tactic_learner_internal.process_queue (); *)
(*       let tacs = Neural_learner.(!last_model) in *)
(*       print_endline (string_of_int (TacticMap.cardinal tacs)); *)
(*       let capability = available_tactics tacs in *)
(*       Results.available_set results (Some capability); *)
(*       Capability.dec_ref capability; *)

(*       let res = Results.result_init results in *)
(*       begin try *)
(*           let lemm_str = Params.lemma_get params in *)
(*           let evd, c = try *)
(*               let lemm_constr_expr = Pcoq.parse_string Pcoq.Constr.lconstr lemm_str in *)
(*               Constrintern.interp_constr_evars (Global.env ()) Evd.empty lemm_constr_expr *)
(*             with e when CErrors.noncritical e -> *)
(*               raise ParseError in *)

(*           let env = Global.env () in *)
(*           let start = Proof.start ~name:(Names.Id.of_string "dummy") ~poly:false evd [env, c] in *)
(*           write_execution_result env start res (proof_object env start tacs) *)
(*         with ParseError -> *)
(*           let exc = Api.Builder.ExecutionResult.protocol_error_init res in *)
(*           Api.Builder.Exception.parse_error_set exc *)
(*       end; *)
(*       Service.return response *)
(*   end *)

let () =
  Logs.set_level (Some Logs.Warning);
  Logs.set_reporter (Logs_fmt.reporter ())

(* let reinforce file_descr = *)
(*   let service_name = Capnp_rpc_net.Restorer.Id.public "" in *)
(*   Lwt_main.run @@ *)
(*   (Lwt_switch.with_switch @@ fun switch -> *)
(*    let endpoint = Capnp_rpc_unix.Unix_flow.connect (Lwt_unix.of_unix_file_descr file_descr) *)
(*                   |> Capnp_rpc_net.Endpoint.of_flow (module Capnp_rpc_unix.Unix_flow) *)
(*                     ~peer_id:Capnp_rpc_net.Auth.Digest.insecure *)
(*                     ~switch in *)
(*    let restore = Capnp_rpc_net.Restorer.single service_name pull_reinforce in *)
(*    let t : Capnp_rpc_unix.CapTP.t = Capnp_rpc_unix.CapTP.connect ~restore endpoint in *)
(*    Capnp_rpc_unix.CapTP.disconnect *)
(*    let w, f = Lwt.wait () in *)
(*    Lwt_switch.add_hook (Some switch) (fun () -> Lwt.return @@ Lwt.wakeup f ()); *)
(*    w); *)
(*   let total_memory (a,b,c) = 8 * (int_of_float (a -. b +. c)) in *)
(*   Feedback.msg_notice Pp.(str "Proving session finished with " *)
(*                           ++ int (total_memory @@ Gc.counters ()) ++ str " allocated, requesting GC.full_major"); *)
(*   Gc.full_major (); *)
(*   Feedback.msg_notice Pp.(str "Proving session finished with memory allocated: " *)
(*                           ++ int (total_memory @@ Gc.counters ())) *)

let reinforce_stdin () = ()
  (* reinforce Unix.stdin *)

let reinforce_tcp ip_addr port = ()
  (* Feedback.msg_notice Pp.(str "connecting to prover to " ++ str ip_addr ++ str ":" ++ int port); *)
  (* let my_socket = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in *)
  (* let server_addr = Unix.ADDR_INET (Unix.inet_addr_of_string ip_addr, port) in *)
  (* (try *)
  (*   Unix.connect my_socket server_addr; *)
  (*   Feedback.msg_notice Pp.(str "connected to prover"); *)
  (*   reinforce my_socket; *)
  (* with *)
  (* | Unix.Unix_error (Unix.ECONNREFUSED,s1,s2) -> *)
  (*      Feedback.msg_notice Pp.(str "connection to prover refused"); *)
  (* | ex -> *)
  (*    ( *)
  (*      Feedback.msg_notice Pp.(str "exception caught, closing connection to prover"); *)
  (*    Unix.close my_socket; *)
  (*    raise ex)); *)
  (*   Unix.close my_socket *)
