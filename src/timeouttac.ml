open Control

(* TODO: This is a hack to support high resulution timers. Partially taken from `Control`. *)
(* This function assumes it is the only function calling [setitimer] *)
let unix_timeout n f x =
  let open Unix in
  let timeout_handler _ = raise CErrors.Timeout in
  let old_timer = getitimer ITIMER_REAL in
  (* Here we assume that the existing timer will also interrupt us. *)
  if old_timer.it_value > 0. && old_timer.it_value <= n then Some (f x) else
    let psh = Sys.signal Sys.sigalrm (Sys.Signal_handle timeout_handler) in
    let old_timer = setitimer ITIMER_REAL {it_interval = 0.; it_value = n} in
    let restore_timeout () =
      let timer_status = getitimer ITIMER_REAL in
      let old_timer_value = old_timer.it_value -. n +. timer_status.it_value in
      let old_timer_value = if old_timer_value <= 0. then 0. else old_timer_value in
      let _ = setitimer ITIMER_REAL { old_timer with it_value = old_timer_value } in
      Sys.set_signal Sys.sigalrm psh
    in
    try
      let res = f x in
      restore_timeout ();
      Some res
    with CErrors.Timeout ->
      restore_timeout ();
      None

let interrupt = ref false

let windows_timeout n f x =
  let killed = ref false in
  let exited = ref false in
  let thread init =
    while not !killed do
      let cur = Unix.gettimeofday () in
      if n <= cur -. init then begin
        interrupt := true;
        exited := true;
        Thread.exit ()
      end;
      Thread.delay 0.5
    done
  in
  let init = Unix.gettimeofday () in
  let _id = CThread.create thread init in
  try
    let res = f x in
    let () = killed := true in
    let cur = Unix.gettimeofday () in
    (* The thread did not interrupt, but the computation took longer than
       expected. *)
    let () = if n <= cur -. init then begin
        exited := true;
        raise Sys.Break
      end in
    Some res
  with
  | Sys.Break ->
    (* Just in case, it could be a regular Ctrl+C *)
    if not !exited then begin killed := true; raise Sys.Break end
    else None
  | e ->
    let () = killed := true in
    let e = Backtrace.add_backtrace e in
    Exninfo.iraise e

let unix_timeout n f x e =
  match unix_timeout (float_of_int n) f x with
  | None -> raise e
  | Some x -> x

let windows_timeout n f x e =
  match windows_timeout (float_of_int n) f x with
  | None -> raise e
  | Some x -> x

let timeout_fun = match Sys.os_type with
  | "Unix" | "Cygwin" -> { timeout = unix_timeout }
  | _ -> { timeout = windows_timeout }

let () = Control.set_timeout timeout_fun
