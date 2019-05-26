Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Data.PPair.
Require Import ExtLib.Data.Monads.IdentityMonad.

Require Import Coq.Program.Basics. (* for (∘) *)

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Universe Polymorphism.

Set Printing Universes.

Section WriterType.
  Polymorphic Universe s d c.
  Variable S : Type@{s}.

  Record writerT (Monoid_S : Monoid@{s} S) (m : Type@{d} -> Type@{c})
         (t : Type@{d}) : Type := mkWriterT
  { runWriterT : m (pprod t S)%type }.

  Variable Monoid_S : Monoid S.
  Variable m : Type@{d} -> Type@{c}.
  Context {M : Monad m}.

  Arguments mkWriterT _ [_ _] _.

  Definition execWriterT {T} (c : writerT Monoid_S m T) : m S :=
    bind (runWriterT c) (fun (x : pprod T S) => ret (psnd x)).

  Definition evalWriterT {T} (c : writerT Monoid_S m T) : m T :=
    bind (runWriterT c) (fun (x : pprod T S) => ret (pfst x)).

  Local Notation "( x , y )" := (ppair x y).

  Global Instance Monad_writerT : Monad (writerT Monoid_S m) :=
  { ret := fun _ x => mkWriterT _ (@ret _ M _ (x, monoid_unit Monoid_S))
  ; bind := fun _ _ c1 c2 =>
    mkWriterT _ (
      @bind _ M _ _ (runWriterT c1) (fun v =>
        bind (runWriterT (c2 (pfst v))) (fun v' =>
        ret (pfst v', monoid_plus Monoid_S (psnd v) (psnd v')))))
  }.

  Global Instance Writer_writerT : MonadWriter Monoid_S (writerT Monoid_S m) :=
  { tell   := fun x => mkWriterT _ (ret (tt, x))
  ; listen := fun _ c => mkWriterT _ (bind (runWriterT c)
                                        (fun x => ret (pair (pfst x) (psnd x), psnd x)))
  ; pass   := fun _ c => mkWriterT _ (bind (runWriterT c)
                                        (fun x => ret (let '(ppair (pair x ss) s) := x in (x, ss s))))
  }.

  Global Instance MonadT_writerT : MonadT (writerT Monoid_S m) m :=
  { lift := fun _ c => mkWriterT _ (bind c (fun x => ret (x, monoid_unit Monoid_S)))
  }.

  Global Instance Reader_writerT {S'} (MR : MonadReader S' m) : MonadReader S' (writerT Monoid_S m) :=
  { ask := mkWriterT _ (bind ask (fun v => @ret _ M _ (v, monoid_unit Monoid_S)))
  ; local := fun _ f c =>
    mkWriterT _ (local f (runWriterT c))
  }.

  Global Instance State_writerT {S'} (MR : MonadState S' m) : MonadState S' (writerT Monoid_S m) :=
  { get := lift get
  ; put := fun v => lift (put v)
  }.

  Global Instance Zero_writerT (MZ : MonadZero m) : MonadZero (writerT Monoid_S m) :=
  { mzero := fun _ => lift mzero }.

  Global Instance Exception_writerT {E} (ME : MonadExc E m) : MonadExc E (writerT Monoid_S m) :=
  { raise := fun _ v => lift (raise v)
  ; catch := fun _ c h => mkWriterT _ (catch (runWriterT c) (fun x => runWriterT (h x)))
  }.

  Global Instance Writer_writerT_pass {T} {MonT : Monoid T} {M : Monad m} {MW : MonadWriter MonT m}
  : MonadWriter MonT (writerT Monoid_S m) :=
  { tell   := fun x => mkWriterT _ (bind (tell x)
                                             (fun x => ret (x, monoid_unit Monoid_S)))
  ; listen := fun _ c => mkWriterT _ (bind (m:=m) (@listen _ _ _ MW  _ (runWriterT c))
                                        (fun x => let '(pair (ppair a t) s) := x in
                                               ret (m:=m) (pair a s,t)))
  ; pass   := fun _ c => mkWriterT _ (@pass _ _ _ MW _
                                         (bind (m:=m) (runWriterT c)
                                               (fun x => let '(ppair (pair a t) s) := x in
                                                      ret (m:=m) (pair (ppair a s) t))))
  }.

End WriterType.

Arguments mkWriterT {_} _ {_ _} _.
Arguments runWriterT {S} {Monoid_S} {m} {t} _.
Arguments evalWriterT {S} {Monoid_S} {m} {M} {T} _.
Arguments execWriterT {S} {Monoid_S} {m} {M} {T} _.

Local Open Scope program_scope.

Section MapWriterT.
  Variable W W': Type.
  Variable Monoid_W : Monoid W.
  Variable Monoid_W' : Monoid W'.
  Variable m n : Type -> Type.
  Variable A B: Type.

  (** Map both the return value and output of a computation using the given function.
        [[ 'runWriterT' ('mapWriterT' f m) = f ('runWriterT' m) ]]
   *)
  Definition mapWriterT (f: m (pprod A W) -> n (pprod B W'))
  : writerT Monoid_W m A -> writerT Monoid_W' n B :=
    mkWriterT Monoid_W' ∘ f ∘ runWriterT.

End MapWriterT.

Section CastWriterT.
  Variable W : Type.
  Variable Monoid_W Monoid_W': Monoid W.
  Variable m : Type -> Type.
  Variable A : Type.

  (* Special case of mapWriterT where mapping function is identity
   * Note: This function changes the `Monoid` instance.
   *)
  Definition castWriterT
  : writerT Monoid_W m A -> writerT Monoid_W' m A :=
    mkWriterT Monoid_W' ∘ runWriterT.

End CastWriterT.


(** Simple wrapper around `writerT` specializing the underlying monad to `Identity`
 ** which yields the `writer` monad.
 **)
Section WriterMonad.

  Variable W: Type.
  Variable Monoid_W : Monoid W.
  Variable A: Type.

  Definition writer : Type -> Type :=
    writerT Monoid_W ident.
  Definition runWriter : writer A -> pprod A W :=
    unIdent ∘ (@runWriterT W Monoid_W ident A).
  Definition execWriter : writer A -> W :=
    psnd ∘ runWriter.
  Definition evalWriter : writer A -> A :=
    pfst ∘ runWriter.

End WriterMonad.

Section MapWriter.
  Variable W W' : Type.
  Variable Monoid_W: Monoid W.
  Variable Monoid_W': Monoid W'.
  Variable A B: Type.

  (** Map both the return value and output of a computation using the given function.
        [[ 'runWriter' ('mapWriter' f m) = f ('runWriter' m) ]]
   *)
  Definition mapWriter (f: pprod A W -> pprod B W')
  : writer Monoid_W A -> writer Monoid_W' B :=
    mapWriterT Monoid_W' ident B (mkIdent ∘ f ∘ unIdent).

End MapWriter.

Section CastWriter.
  Variable W : Type.
  Variable Monoid_W Monoid_W': Monoid W.
  Variable A : Type.

  (* Special case of mapWriter where mapping function is identity *)
  Definition castWriter
  : writer Monoid_W A -> writer Monoid_W' A :=
    castWriterT Monoid_W' (m:=ident).

End CastWriter.
