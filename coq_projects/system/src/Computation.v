(** The definition of a computation, used to represent concurrent programs. *)
Require Import Coq.Lists.List.
Require Import Events.

Import ListNotations.

(** A list of types to specify the shared memory. *)
Module Signature.
  Definition t := list Type.
End Signature.

(** The shared memory. *)
Module Memory.
  (** The shared memory is a list of typed cells. *)
  Inductive t : Signature.t -> Type :=
  | Nil : t []
  | Cons : forall (A : Type) (sig : Signature.t), A -> t sig -> t (A :: sig).
  
  (** The first shared memory cell. *)
  Definition head {A : Type} {sig : Signature.t} (mem : t (A :: sig)) : A :=
    match mem with
    | Cons _ _ x _ => x
    end.
  
  (** The tail of the shared memory. *)
  Definition tail {A : Type} {sig : Signature.t} (mem : t (A :: sig)) : t sig :=
    match mem with
    | Cons _ _ _ mem => mem
    end.
End Memory.

(** A reference to a shared memory cell. *)
Module Ref.
  Class C (A : Type) (sig : Signature.t) : Type := New {
    read : Memory.t sig -> A;
    write : Memory.t sig -> A -> Memory.t sig }.

  Instance cons_left (A : Type) (sig : Signature.t) : C A (A :: sig) := {
    read mem := Memory.head mem;
    write mem x := Memory.Cons _ _ x (Memory.tail mem) }.

  Instance cons_right (A B : Type) (sig : Signature.t) (I : C A sig)
    : C A (B :: sig) := {
    read mem := read (Memory.tail mem);
    write mem x :=
      Memory.Cons _ _ (Memory.head mem) (write (Memory.tail mem) x) }.
End Ref.

(** Definition of a computation. *)
Module C.
  (** A computation is a free monad with some primitives. *)
  Inductive t (sig : Signature.t) : Type -> Type :=
  | Ret : forall (A : Type), A -> t sig A
  | Bind : forall (A B : Type), t sig A -> (A -> t sig B) -> t sig B
  | Read : forall (A : Type), `{Ref.C A sig} -> t sig A
    (** Read the value of a reference (atomic). *)
  | Write : forall (A : Type), `{Ref.C A sig} -> A -> t sig unit
    (** Write a value in a reference (atomic). *)
  | Send : forall (A : Type) (command : Command.t), Command.request command ->
    A -> (A -> Command.answer command -> t sig (option A)) -> t sig unit
    (** Sends a request to the operating system, and react to answers with the
        handler. *)
  | Exit : forall (A : Type), t sig A
    (** Terminate the program. *).
  (* We force the `sig` argument to be implicit. *)
  Arguments Ret {sig A} _.
  Arguments Bind {sig A B} _ _.
  Arguments Read {sig A} _.
  Arguments Write {sig A} _.
  Arguments Send {sig A} _ _ _ _.
  Arguments Exit {sig A}.

  (** Monadic notation. *)
  Module Notations.
    Notation "'let!' X ':=' A 'in' B" := (Bind A (fun X => B))
      (at level 200, X ident, A at level 100, B at level 200).

    Notation "'let!' X ':' T ':=' A 'in' B" := (Bind (A := T) A (fun X => B))
      (at level 200, X ident, A at level 100, T at level 200, B at level 200).

    Notation "'do!' A 'in' B" := (Bind A (fun _ => B))
      (at level 200, B at level 200).
  End Notations.
End C.
