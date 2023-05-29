(** fork_timeout implements timeout using fork and sleep *)
let fork_timeout n f =
  let pid = Unix.fork () in
  if pid = 0 then
    begin (* the worker *)
      Fun.protect ~finally:(fun () -> exit 0) (fun () -> f (); exit 0)
    end
  else
    begin
      let pid2 = Unix.fork () in
      if pid2 = 0 then
        begin (* the watchdog *)
          Unix.sleep n;
          (try Unix.kill pid Sys.sigterm with _ -> ());
          exit 0
        end
      else
        let clean () =
          try Unix.kill pid2 Sys.sigterm with _ -> ()
        in
        let (_, status) = Unix.waitpid [] pid in
        let msg = match status with
          | Unix.WEXITED 0 -> clean (); None
          | Unix.WEXITED n -> Some (Pp.(str "Forked process exited with code " ++ int n))
          | Unix.WSIGNALED n -> Some (Pp.(str "Forked process exited with signal " ++ int n))
          | Unix.WSTOPPED _ -> assert false in
        ignore (Unix.waitpid [] pid2);
        msg
    end
