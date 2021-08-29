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

  let ask x = x
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

  let get x = fun s -> s, s
  let put s = fun _ -> s, ()
end

(* Taken from CString.is_prefix in Coq 8.11 *)
let string_is_sub p s off =
  let lp = String.length p in
  let ls = String.length s in
  if ls < off + lp then false
  else
    let rec aux i =
      if lp <= i then true
      else
        let cp = String.unsafe_get p i in
        let cs = String.unsafe_get s (off + i) in
        if cp = cs then aux (succ i) else false
    in
    aux 0

let string_is_prefix p s =
  string_is_sub p s 0
