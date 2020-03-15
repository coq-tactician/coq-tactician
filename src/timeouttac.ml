(* Proofview.tclTIMEOUT is incorrect because of a bug in OCaml
   runtime. This file contains a timeout implementation based on
   Unix.fork and Unix.sleep. See:

   https://caml.inria.fr/mantis/view.php?id=7709
   https://caml.inria.fr/mantis/view.php?id=4127
   https://github.com/coq/coq/issues/7430
   https://github.com/coq/coq/issues/7408

*)

(* ptimeout implements timeout using fork and sleep *)
let ptimeout n tac =
  let pid = Unix.fork () in
  if pid = 0 then
    begin (* the worker *)
      Proofview.tclOR
        (Proofview.tclBIND tac (fun _ -> exit 0))
        (fun _ -> exit 0)
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
        begin
          let clean () =
            try Unix.kill pid2 Sys.sigterm with _ -> ()
          in
          try
            let (_, status) = Unix.waitpid [] pid in
            (match status with
            | Unix.WEXITED 0 -> clean ();
            | _ -> (match status with
                | Unix.WEXITED n -> (); (* assert false *)
                | Unix.WSIGNALED n -> if n != -11 then () (* assert false *) else ()
                | Unix.WSTOPPED n -> () (* assert false *)));
            ignore (Unix.waitpid [] pid2);
            Proofview.tclUNIT ()
          with
          | e -> raise e
        end
    end
