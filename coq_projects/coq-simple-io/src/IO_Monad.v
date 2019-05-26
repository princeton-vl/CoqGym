(**
  The [IO] monad.
*)

(* begin hide *)
From Coq.extraction Require Import
     Extraction
     ExtrOcamlBasic.

From ExtLib.Structures Require Import
     Functor Applicative Monad MonadFix.

Set Warnings "-extraction-opaque-accessed,-extraction".
(* end hide *)

(** * Main interface *)

(** The IO monad. *)
Parameter IO : Type -> Type.

(** The result type of [unsafe_run].

    For example, to extract a program [main : IO unit] to
    a file named [main.ml]:

[[
  Definition exe : io_unit := unsafe_run main.
  Extraction "main.ml" exe.
]]
 *)
Parameter io_unit : Type.

(* All identifiers are meant to be used qualified. *)
Module IO.

(** ** Functions *)

Parameter ret : forall {a}, a -> IO a.
Parameter bind : forall {a b}, IO a -> (a -> IO b) -> IO b.

(** Fixpoint combinator. *)
Parameter fix_io : forall {a b},
    ((a -> IO b) -> (a -> IO b)) -> a -> IO b.

(** Delay eager evaluation.

    Some IO actions can be expensive closures.
    [delay_io] allows the computation of the closure to
    happen during execution, instead of eagerly during the
    definition of the IO action.
 *)
Parameter delay_io : forall {a}, (unit -> IO a) -> IO a.

(** Apply a pure function to the result of an action. *)
Definition map {a b} : (a -> b) -> IO a -> IO b :=
  fun f m => bind m (fun a => ret (f a)).

(** Infinite stateful loop. *)
Definition loop : forall {a void}, (a -> IO a) -> (a -> IO void) :=
  fun _ _ f => fix_io (fun k x => bind (f x) k).

(** While loop. Stops once the output is [None]. *)
Definition while_loop : forall {a}, (a -> IO (option a)) -> (a -> IO unit) :=
  fun _ f => fix_io (fun k x => bind (f x) (fun y' =>
    match y' with
    | None => ret tt
    | Some y => k y
    end)).

(** ** Notations *)

Module Notations.

Delimit Scope io_scope with io.

Notation "c >>= f" := (bind c f)
(at level 50, left associativity) : io_scope.

Notation "f =<< c" := (bind c f)
(at level 51, right associativity) : io_scope.

Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
(at level 100, c1 at next level, right associativity) : io_scope.

Notation "e1 ;; e2" := (_ <- e1%io ;; e2%io)%io
(at level 100, right associativity) : io_scope.

Notation delay io := (delay_io (fun _ => io)).

Open Scope io_scope.

End Notations.

(** ** Equations *)

Axiom fixpoint_io : forall {a b} f, @fix_io a b f = f (fix_io f).

(** *** Monad laws *)

Axiom bind_ret :
  forall {a b} (x : a) (k : a -> IO b), bind (ret x) k = k x.
Axiom ret_bind : forall {a} (m : IO a), bind m ret = m.
Axiom bind_bind :
  forall {a b c} (m : IO a) (k : a -> IO b) (h : b -> IO c),
    bind (bind m k) h = bind m (fun x => bind (k x) h).
Axiom bind_ext : forall {a b} (m : IO a) (k k' : a -> IO b),
    (forall x, k x = k' x) -> bind m k = bind m k'.

(** ** Run! *)

(** Run an IO action. See [io_unit] for usage.

    Hiding the result in [io_unit] limits the breakage of
    referential transparency somewhat. *)
Parameter unsafe_run : IO unit -> io_unit.

(** Run an IO action, ignoring the result. *)
Parameter unsafe_run' : forall {a}, IO a -> io_unit.

(** Run an IO action to produce a result.

    This can break referential transparency quite badly. *)
Parameter very_unsafe_eval : forall {a}, IO a -> a.

(** * Extraction *)

(* CPS prevents stack overflows. *)
(* [forall r, (a -> r) -> r] *)
Extract Constant IO "'a" => "('a -> Obj.t) -> Obj.t".
Extract Constant ret => "fun a k -> k a".
Extract Constant bind => "fun io_a io_b k -> io_a (fun a -> io_b a k)".
Extract Constant fix_io => "fun f -> let rec go a k = f go a k in go".
Extract Constant delay_io => "fun f k -> f () k".

Extract Inlined Constant io_unit => "unit".
Extract Constant unsafe_run => "fun io -> Obj.magic io (fun () -> ())".
Extract Constant unsafe_run' => "fun io -> Obj.magic io (fun _ -> ())".
Extract Constant very_unsafe_eval => "fun io -> Obj.magic io (fun x -> x)".

End IO.

(** * Instances *)

Instance Functor_IO : Functor IO := {
  fmap _ _ := IO.map;
}.

Instance Applicative_IO : Applicative IO := {
  pure _ := IO.ret;
  ap _ _ iof iox :=
    IO.bind iof (fun f =>
    IO.bind iox (fun x =>
    IO.ret (f x)));
}.

Instance Monad_IO : Monad IO := {
  ret _ := IO.ret;
  bind _ _ := IO.bind;
}.

Instance MonadFix_IO : MonadFix IO := {
  mfix _ _ := IO.fix_io;
}.
