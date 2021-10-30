let mapi f s : 'a IStream.t =
  let rec mapi_node f i = function
    | IStream.Nil -> IStream.Nil
    | IStream.Cons (x, s) -> Cons (f i x, mapi f (i + 1) s)
  and mapi f i s = IStream.thunk (fun () -> mapi_node f i (IStream.peek s))
  in mapi f 0 s

let rec to_list n s = match n, IStream.peek s with
  | _, Nil | 0, _ -> []
  | n, Cons (x, s) -> x :: (to_list (n - 1) s)

exception PredictionsEnd
exception DepthEnd

module type MonadNotations = sig
  include Monad.Def
  type 'a map = 'a -> 'a t
  val id : 'a map
  val (<*>) : ('a -> 'b) t -> 'a -> 'b t
  val (let+) : 'a t -> ('a -> 'b) -> 'b t
  val (and+) : 'a t -> 'b t -> ('a * 'b) t
  val (let*) : 'a t -> ('a -> 'b t) -> 'b t
end

module WithMonadNotations (M : Monad.Def) = struct
  include M
  type 'a map = 'a -> 'a t
  let id = return
  let (<*>) f x     = f >>= fun f -> return (f x)
  let (let+) x f    = map f x
  let (and+) o1 o2  = o1 >>= fun o1 -> o2 >>= fun o2 -> return (o1, o2)
  let (let*) x f    = x >>= f
end

module IdentityMonad = struct
  type 'a t = 'a
  let return x = x
  let (>>=) x f = f x
  let (>>) () x = x
  let map f x = f x
end

module ReaderMonad (R : sig type r end) = struct
  open R
  type 'a t = r -> 'a
  let return x = fun _ -> x
  let (>>=) x f = fun r -> f (x r) r
  let (>>) x y = fun r -> let () = x r in y r
  let map f x = fun r -> f (x r)

  let ask = fun r -> r
  let local f x = fun r -> x (f r)
end

module WriterMonad (R : sig type w val id : w val comb : w -> w -> w end) = struct
  open R
  type 'a t = w * 'a
  let return x = (id, x)
  let (>>=) (w, x) f = let (w', y) = f x in (comb w w', y)
  let (>>) (w, ()) (w', x) = (comb w w', x)
  let map f (w, x) = w, f x

  let tell l = ([l], ())
  let censor f (w, x) = (f w, x)
end

module StateMonad (R : sig type s end) = struct
  open R
  type 'a t = s -> s * 'a
  let return x = fun s -> (s, x)
  let (>>=) x f = fun s -> let s', a = x s in f a s'
  let (>>) x y = fun s -> let s', () = x s in y s'
  let map f x = fun s -> let s', a = x s in s', f a

  let get = fun s -> s, s
  let put s = fun _ -> s, ()
end

module ReaderWriterMonad
  (R : sig type r type w val id : w val comb : w -> w -> w end) = struct
  open R
  type 'a t = r -> w * 'a
  let return x = fun _ -> (id, x)
  let (>>=) k f = fun r ->
    let (w, x) = k r in
    let (w', y) = f x r in (comb w w', y)
  let (>>) k l = fun r ->
    let (w, ()) = k r in
    let (w', x) = l r in
    (comb w w', x)
  let map f k = fun r ->
    let (w, x) = k r in w, f x

  let tell l = fun _ -> ([l], ())
  let censor f (w, x) = fun _ -> (f w, x)

  let ask = fun r -> id, r
  let local f x = fun r -> x (f r)
end

module ReaderStateMonad
  (R : sig type r type s end) = struct
  open R
  type 'a t = r -> s -> s * 'a
  let return x = fun _ s -> (s, x)
  let (>>=) k f = fun r s ->
    let (s, x) = k r s in
    f x r s
  let (>>) k l = fun r s ->
    let (s, ()) = k r s in
    l r s
  let map f k = fun r s ->
    let (s, x) = k r s in s, f x

  let get = fun _ s -> s, s
  let put s = fun _ _ -> s, ()

  let ask = fun r s -> s, r
  let local f x = fun r s -> x (f r) s
end

let record_map (f : Proofview.Goal.t -> 'a)
    (gls : Proofview.Goal.t Proofview.tactic list) : 'a list Proofview.tactic =
  let rec aux gls acc =
    let open Proofview.Notations in
    match gls with
    | [] -> Proofview.tclUNIT (acc)
    | gl::gls' -> gl >>= fun gl' -> aux gls' (f gl' :: acc) in
  aux gls []

let proof_state_to_string hyps goal env evar_map =
  let constr_str t = Sexpr.format_oneline (Printer.pr_econstr_env env evar_map t) in
  let goal = constr_str goal in
  let hyps = List.map (function
      | Context.Named.Declaration.LocalAssum (id, typ) ->
        let id_str = Names.Id.print id.binder_name in
        let typ_str = constr_str typ in
        Pp.(id_str ++ str " : " ++ typ_str)
      | Context.Named.Declaration.LocalDef (id, term, typ) ->
        let id_str = Names.Id.print id.binder_name in
        let term_str = Pp.(str " := " ++ constr_str term) in
        let typ_str = constr_str typ in
        Pp.(id_str ++ term_str ++ str " : " ++ typ_str)
    ) hyps in
  Pp.(prlist_with_sep (fun () -> str ", ") (fun x -> x) hyps ++ str " |- " ++ goal)

let pr_proof_tac () =
  let open Proofview in
  let open Notations in
  Goal.goals >>= record_map (fun x -> x) >>= fun gls ->
  let gls_string = List.map (fun gl ->
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      let hyps = Goal.hyps gl in
      let goal = Goal.concl gl in
      proof_state_to_string hyps goal env sigma)
      gls in
  List.iter Feedback.msg_notice gls_string; tclUNIT ()

let safe_index0 f x l = try Some (CList.index0 f x l) with Not_found -> None

let constr_size c =
  let rec aux c =
    Constr.fold (fun i c -> i + aux c + 1) 1 c in
  aux c

let econstr_size evd c = constr_size @@ EConstr.to_constr evd c

let goal_size (gl : Proofview.Goal.t) =
  let open Proofview in
  let open Notations in
  let sigma = Proofview.Goal.sigma gl in
  let hyps = Goal.hyps gl in
  let goal = Goal.concl gl in
  let hyps = Context.Named.fold_inside (fun i d ->
      Context.Named.Declaration.fold_constr (fun c i -> i + econstr_size sigma c) d i
    ) ~init:0 hyps in
  let goal = econstr_size sigma goal in
  hyps + goal
