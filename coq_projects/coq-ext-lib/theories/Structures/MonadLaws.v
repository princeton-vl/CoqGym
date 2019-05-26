Require Import Setoid.
Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Unit.

Set Implicit Arguments.
Set Strict Implicit.

(*
Section MonadLaws.
  Variable m : Type@{d} -> Type.
  Variable M : Monad m.

  (** This <= relation is a computational <= relation based on the ideas
   ** of domain theory. It generalizes the usual equivalence relation by,
   ** enabling the relation to talk about computations that are "more defined"
   ** than others.
   **
   ** This generalization is done to support the fixpoint law.
   **)
  Variable meq : forall {T : Type@{d}}, type T -> type (m T).
  Variable meqOk : forall {T : Type@{d}} (tT : type T), typeOk tT -> typeOk (meq tT).

(*
  (** This states when an element is a proper element under an equivalence
   ** relation.
   **)
  Variable Proper_m : forall T, Proper T -> Proper (m T).
*)

  Class MonadLaws : Type :=
  { bind_of_return : forall {A B : Type@{d}} (eA : type A) (eB : type B),
    typeOk eA -> typeOk eB ->
    forall (a:A) (f:A -> m B),
    proper a -> proper f ->
    equal (bind (ret a) f) (f a)
  ; return_of_bind : forall {A : Type@{d}} (eA : type A),
    typeOk eA ->
    forall (aM:m A) (f:A -> m A),
    (forall x, equal (f x) (ret x)) ->
    proper aM ->
    equal (bind aM f) aM
  ; bind_associativity :
    forall {A B C : Type@{d}} (eA : type A) (eB : type B) (eC : type C),
      typeOk eA -> typeOk eB -> typeOk eC ->
      forall (aM:m A) (f:A -> m B) (g:B -> m C),
      proper aM ->
      proper f ->
      proper g ->
      equal (bind (bind aM f) g) (bind aM (fun a => bind (f a) g))

  ; ret_proper :> forall {A:Type@{d}} (eA : type A), typeOk eA ->
    proper ret
  ; bind_proper :> forall {A B:Type@{d}} (eA : type A) (eB : type B),
    typeOk eA -> typeOk eB ->
    proper (@bind m _ A B)
  }.

(*
  Add Parametric Morphism T U (tT : type T) (tU : type U) (tokT : typeOk tT) (tokU : typeOk tU) (ML : MonadLaws) : (@bind _ _ T U)
    with signature (equal ==> (equal ==> equal) ==> equal)
      as bind_morph.
  Proof. eapply bind_proper; auto. Qed.

  Add Parametric Morphism T U (tT : type T) (tU : type U) (tokT : typeOk tT) (tokU : typeOk tU) (ML : MonadLaws) (c : m T) (Pc : proper c) : (@bind _ _ T U c)
    with signature ((equal ==> equal) ==> equal)
      as bind_1_morph.
  Proof.
    eapply bind_proper; auto. eapply preflexive; [ | eapply Pc ].
    eapply equiv_prefl; auto.
  Qed.

  Global Instance ret_morph T (tT : type T) (tokT : typeOk tT) (ML : MonadLaws)
  : Proper (equal ==> equal) (@ret _ _ T).
  Proof. eapply ret_proper; auto. Qed.
*)
(*
  Add Parametric Morphism T (tT : type T) (tokT : typeOk tT) (ML : MonadLaws) : (@ret _ _ T)
    with signature (equal ==> equal)
      as ret_morph.
*)


  Class MonadTLaws (n : Type@{d} -> Type) (Pn : forall T (R : type T), type (n T)) (nM : Monad n) (MT : MonadT m n) : Type :=
  { lift_ret  : forall {T : Type@{d}} (eT : type T),
    typeOk eT ->
    forall x : T,
    proper x ->
    equal (lift (ret x)) (ret x)
  ; lift_bind : forall {T U : Type@{d}} (eT : type T) (eU : type U),
    typeOk eT -> typeOk eU ->
    forall (c : n T) (f : T -> n U),
    proper c -> proper f ->
    equal (lift (bind c f)) (bind (lift c) (fun x => lift (f x)))
  ; lift_proper : forall {T : Type@{d}} (tT : type T), typeOk tT -> proper lift
  }.

  Section with_state.
    Context {S : Type} (tS : type S) {tokS : typeOk tS}.

(*
    Polymorphic Definition promote {A : Type@{a}} : Type@{b} := A.

    Polymorphic Class MonadStateLaws  (MS : MonadState S m) : Type :=
    { get_put : @equal (m unit) (meq type_unit) (bind get put) (ret tt) }.
    ; put_get : forall x, proper x ->
      equal (bind (put x) (fun _ => get)) (bind (put x) (fun _ => ret x))
    }.
    ; put_put : forall {A:Type@{d}} (tA : type A), typeOk tA ->
      forall (x y : S) (f : unit -> m A), proper x -> proper y -> proper f ->
      equal (bind (put x) (fun _ => bind (put y) f)) (bind (put y) f)
    ; get_get : forall {A:Type@{d}} (tA : type A), typeOk tA ->
      forall (f : S -> S -> m A), proper f ->
      equal (bind get (fun s => bind get (f s))) (bind get (fun s => f s s))
    ; get_ignore : forall {A:Type@{d}} (tA : type A), typeOk tA ->
      forall (aM : m A), proper aM ->
      equal (bind get (fun _ => aM)) aM
    ; get_proper :> proper get
    ; put_proper :> proper put
    }.
*)

    Class MonadReaderLaws (MR : MonadReader S m) : Type :=
    { ask_local : forall f, proper f ->
      equal (local f ask) (bind ask (fun x => ret (f x)))
    ; local_bind : forall {A B:Type@{d}} (tA : type A) (tB : type B),
        typeOk tA -> typeOk tB ->
        forall aM f (g : A -> m B),
          proper aM -> proper f -> proper g ->
          equal (local f (bind aM g)) (bind (local f aM) (fun x => local f (g x)))
    ; local_ret : forall {A:Type@{d}} (tA : type A),
        typeOk tA ->
        forall (x : A) f,
          proper x -> proper f ->
          equal (local f (ret x)) (ret x)
    ; local_local : forall {T:Type@{d}} (eA : type T),
      typeOk eA ->
      forall (s s' : S -> S) (c : m T),
        proper s -> proper s' -> proper c ->
        equal (local s (local s' c)) (local (fun x => s' (s x)) c)
    ; local_proper :> forall {T:Type@{d}} (tT : type T), typeOk tT -> proper (@local _ _ _ T)
    ; ask_proper :> proper ask
    }.

  End with_state.

  Class MonadZeroLaws (MZ : MonadZero m) : Type :=
  { bind_zero : forall {A B:Type@{d}} (tA : type A) (tB : type B),
    typeOk tA -> typeOk tB ->
    forall (f : A -> m B),
    proper f ->
    equal (bind mzero f) mzero
  ; zero_proper :> forall {A:Type@{d}} (rA : type A), typeOk rA ->
    proper mzero
  }.

  Class MonadFixLaws (MF : MonadFix m) : Type :=
  { mleq : forall {T:Type@{d}}, relation T -> relation (m T)
  ; mfix_monotonic : forall {T U:Type@{d}} (rT : type T) (rU : type U),
    typeOk rT -> typeOk rU ->
    forall (F : (T -> m U) -> T -> m U),
    respectful equal (mleq equal) (mfix F) (F (mfix F))
  ; mfix_proper :> forall {T U:Type@{d}} (rT : type T) (rU : type U),
    typeOk rT -> typeOk rU ->
    proper (@mfix _ _ T U)
  }.

End MonadLaws.
*)