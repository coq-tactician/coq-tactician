let stream_mapi f stream =
  let next i =
    try Some (f i (Stream.next stream))
    with Stream.Failure -> None in
  Stream.from next

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

(* There does not appear to be a decent method to decide if two tactics are equal.
   Taking the hash of the syntax tree appears to either under or over-approximate
   depending on the depth of the hash calculation. The most decent method I can
   think of is to *)
(* let tac_pp t = Pptactic.pr_glob_tactic (Global.env ()) t *)
let tac_pp t = Sexpr.format_oneline (Pptactic.pr_glob_tactic Environ.empty_env t)
let string_tac t = Pp.string_of_ppcmds (tac_pp t)
let with_hash t = t, lazy (Hashtbl.hash (tac_pp t))
