(** Design is inspired by Haskell transformers and Monadic: https://github.com/Denommus/monadic
    This is a simplified version that also interfaces with Coq's monads. *)

module type MonadTransformerType = sig
  include Monad.Def
  type 'a wrapped
  type 'a repr_t

  val lift : 'a wrapped -> 'a t
  val run : 'a t -> 'a repr_t

  val unrun : 'a repr_t -> 'a t
  (** Escape hatch. Use with care. *)
end

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

module ReaderMonadT (Wrapped : Monad.Def) (R : sig type r end) : sig
  open R
  include MonadTransformerType
    with type 'a wrapped = 'a Wrapped.t
     and type 'a repr_t = r -> 'a Wrapped.t
  val ask : r t
  val local : (r -> r) -> 'a t -> 'a t

  val mapT : ('a Wrapped.t -> 'b Wrapped.t) -> 'a t -> 'b t
end = struct
  open R
  type 'a t = r -> 'a Wrapped.t
  type 'a wrapped = 'a Wrapped.t
  type 'a repr_t = 'a t

  open WithMonadNotations(Wrapped)
  let return x = fun _ -> Wrapped.return x
  let (>>=) x f = fun r ->
    let* x = x r in
    f x r
  let (>>) x y = fun r ->
    let* () = x r in
    y r
  let map f x = fun r ->
    let+ x = x r in
    f x

  let mapT f x = fun r ->
    let x = x r in
    f x

  let ask = fun r -> Wrapped.return r
  let local f x = fun r -> x (f r)

  let lift x = fun _ -> x
  let run m = m [@@inline]
  let unrun m = m [@@inline]
end
module ReaderMonad = ReaderMonadT(IdentityMonad)

module WriterMonadT (Wrapped : Monad.Def) (R : sig type w val id : w val comb : w -> w -> w end) : sig
  open R
  include MonadTransformerType
    with type 'a wrapped = 'a Wrapped.t
     and type 'a repr_t = (w * 'a) Wrapped.t
  val tell : w -> unit t
  val pass : ('a * (w -> w)) t -> 'a t
  val listen : 'a t -> ('a * w) t
  val censor : (w -> w) -> 'a t -> 'a t
  (** [censor f m = pass (map (fun x -> x, f) m)] *)

  val mapT : ((w * 'a) Wrapped.t -> (w * 'b) Wrapped.t) -> 'a t -> 'b t
end = struct
  open R
  type 'a t = (w * 'a) Wrapped.t
  type 'a wrapped = 'a Wrapped.t
  type 'a repr_t = 'a t

  open WithMonadNotations(Wrapped)
  let return x = Wrapped.return (R.id, x)
  let (>>=) x f =
    let* w, x = x in
    let+ w', x = f x in
    comb w w', x
  let (>>) x y =
    let+ w, () = x
    and+ w', x = y in
    comb w w', x
  let map f x =
    let+ w, x = x in
    w, f x

  let mapT f x = f x

  let tell l = Wrapped.return (comb R.id l, ())
  let pass x =
    let+ w, (x, f) = x in
    f w, x
  let listen x =
    let+ w, x = x in
    w, (x, w)
  let censor f x =
    let+ w, x = x in
    f w, x

  let lift x =
    let+ x = x in
    R.id, x
  let run m = m [@@inline]
  let unrun m = m [@@inline]
end
module WriterMonad = WriterMonadT(IdentityMonad)

module StateMonadT (Wrapped : Monad.Def) (R : sig type s end) : sig
  open R
  include Monad.Def
  include MonadTransformerType
    with type 'a wrapped = 'a Wrapped.t
     and type 'a repr_t = s -> (s * 'a) Wrapped.t
  val get : s t
  val put : s -> unit t
  val modify : (s -> s) -> unit t
  (** [modify f = get >>= fun s -> put (f s)]*)

  val mapT : ((s * 'a) Wrapped.t -> (s * 'b) Wrapped.t) -> 'a t -> 'b t
end = struct
  open R
  type 'a t = s -> (s * 'a) Wrapped.t
  type 'a wrapped = 'a Wrapped.t
  type 'a repr_t = 'a t

  open WithMonadNotations(Wrapped)
  let return x = fun s -> Wrapped.return (s, x)
  let (>>=) (x : 'a repr_t) f = fun (s : R.s) ->
    let* s', a = x s in
    f a s'
  let (>>) x y = fun s ->
    let* s', () = x s in
    y s'
  let map f x = fun s ->
    let+ s', a = x s in
    s', f a

  let mapT f x = fun s ->
    let x = x s in
    f x

  let get = fun s -> Wrapped.return (s, s)
  let put s = fun _ -> Wrapped.return (s, ())
  let modify f = fun s -> Wrapped.return (f s, ())

  let lift m = fun s ->
    let+ m = m in
    s, m
  let run m = m [@@inline]
  let unrun m = m [@@inline]
end
module StateMonad = StateMonadT(IdentityMonad)

(** Combinations of reader, writer and state monads for convenience *)
module ReaderWriterMonadT
    (Wrapped : Monad.Def)(W : sig type w val id : w val comb : w -> w -> w end)(R : sig type r end) : sig
  open W
  open R
  include Monad.Def
  include MonadTransformerType
    with type 'a wrapped = 'a Wrapped.t
     and type 'a repr_t = r -> (w * 'a) Wrapped.t
  val ask : r t
  val local : (r -> r) -> 'a t -> 'a t
  val tell : w -> unit t
  val pass : ('a * (w -> w)) t -> 'a t
  val listen : 'a t -> ('a * w) t
  val censor : (w -> w) -> 'a t -> 'a t

  val mapT : ((w * 'a) Wrapped.t -> (w * 'b) Wrapped.t) -> 'a t -> 'b t
end = struct
  open W
  open R
  module RM = ReaderMonadT(Wrapped)(R)
  include WriterMonadT(RM)(W)
  type 'a wrapped = 'a Wrapped.t
  type 'a repr_t = r -> (w * 'a) Wrapped.t

  let ask = lift RM.ask
  let local f m = mapT (RM.local f) m

  let lift x = lift @@ RM.lift x
  let mapT f m = mapT (RM.mapT f) m
  let run m = RM.run @@ run m
  let unrun m = unrun @@ RM.unrun m
end
module ReaderWriterMonad = ReaderWriterMonadT(IdentityMonad)

module ReaderStateMonadT
    (Wrapped : Monad.Def)(R : sig type r end)(S : sig type s end) : sig
  open R
  open S
  include Monad.Def
  include MonadTransformerType
    with type 'a wrapped = 'a Wrapped.t
     and type 'a repr_t = r -> s -> (s * 'a) Wrapped.t
  val ask : r t
  val local : (r -> r) -> 'a t -> 'a t
  val get : s t
  val put : s -> unit t
  val modify : (s -> s) -> unit t

  val mapT : ((s * 'a) Wrapped.t -> (s * 'b) Wrapped.t) -> 'a t -> 'b t
end = struct
  open R
  open S
  module SM = StateMonadT(Wrapped)(S)
  include ReaderMonadT(SM)(R)
  type 'a wrapped = 'a Wrapped.t
  type 'a repr_t = r -> s -> (s * 'a) Wrapped.t

  let modify f = lift (SM.modify f)
  let put s = lift (SM.put s)
  let get = lift SM.get

  let lift x = lift @@ SM.lift x
  let mapT f m = mapT (SM.mapT f) m
  let run m r s = SM.run (run m r) s
  let unrun m = unrun (fun r -> SM.unrun (m r))
end
module ReaderStateMonad = ReaderStateMonadT(IdentityMonad)

module StateWriterMonadT
    (Wrapped : Monad.Def)(S : sig type s end)(W : sig type w val id : w val comb : w -> w -> w end) : sig
  open S
  open W
  include Monad.Def
  include MonadTransformerType
    with type 'a wrapped = 'a Wrapped.t
     and type 'a repr_t = s -> (s * (w * 'a)) Wrapped.t
  val get : s t
  val put : s -> unit t
  val modify : (s -> s) -> unit t
  val tell : w -> unit t
  val pass : ('a * (w -> w)) t -> 'a t
  val listen : 'a t -> ('a * w) t
  val censor : (w -> w) -> 'a t -> 'a t

  val mapT : ((s * (w * 'a)) Wrapped.t -> (s * (w * 'b)) Wrapped.t) -> 'a t -> 'b t
end = struct
  open S
  open W
  module SM = StateMonadT(Wrapped)(S)
  include WriterMonadT(SM)(W)
  type 'a wrapped = 'a Wrapped.t
  type 'a repr_t = s -> (s * (w * 'a)) Wrapped.t

  let modify f = lift (SM.modify f)
  let put s = lift (SM.put s)
  let get = lift SM.get

  let lift x = lift @@ SM.lift x
  let mapT f m = mapT (SM.mapT f) m
  let run m s = SM.run (run m) s
  let unrun m = unrun @@ SM.unrun m
end
module StateWriterMonad = StateWriterMonadT(IdentityMonad)

module ReaderStateWriterMonadT
    (Wrapped : Monad.Def)(R : sig type r end)(S : sig type s end)(W : sig type w val id : w val comb : w -> w -> w end) : sig
  open R
  open S
  open W
  include Monad.Def
  include MonadTransformerType
    with type 'a wrapped = 'a Wrapped.t
     and type 'a repr_t = r -> s -> (s * (w * 'a)) Wrapped.t
  val ask : r t
  val local : (r -> r) -> 'a t -> 'a t
  val get : s t
  val put : s -> unit t
  val modify : (s -> s) -> unit t
  val tell : w -> unit t
  val pass : ('a * (w -> w)) t -> 'a t
  val listen : 'a t -> ('a * w) t
  val censor : (w -> w) -> 'a t -> 'a t

  val mapT : ((s * (w * 'a)) Wrapped.t -> (s * (w * 'b)) Wrapped.t) -> 'a t -> 'b t
end = struct
  open R
  open S
  open W
  module RSM = ReaderStateMonadT(Wrapped)(R)(S)
  include WriterMonadT(RSM)(W)
  type 'a wrapped = 'a Wrapped.t
  type 'a repr_t = r -> s -> (s * (w * 'a)) Wrapped.t

  let local f m = mapT (RSM.local f) m
  let ask = lift RSM.ask
  let modify f = lift (RSM.modify f)
  let put s = lift (RSM.put s)
  let get = lift RSM.get

  let lift x = lift @@ RSM.lift x
  let mapT f m = mapT (RSM.mapT f) m
  let run m r s = RSM.run (run m) r s
  let unrun m = unrun @@ RSM.unrun m
end
module ReaderStateWriterMonad = ReaderStateWriterMonadT(IdentityMonad)
