Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import Coq.Classes.Morphisms.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrnat.
Require Import Sets GenLow Tactics.
Require Import Recdef.
Require Import List.

Require Import ZArith ZArith.Znat Arith.

Import GenLow.

Set Bullet Behavior "Strict Subproofs".

(** Apply a function n times *)
Fixpoint appn {A} (f : A -> A) (n : nat) : A ->  A :=
  fun x =>
    match n with
      | 0%nat => x
      | S n' => f (appn f n' x)
    end.

Infix "^" := appn (at level 30, right associativity) : fun_scope.


(** Instance Hierarchy  

   GenSized 
      |
      |
     Gen   Shrink
       \    /
        \  /
      Arbitrary
*)

(** * Generator-related classes *)

(* begin gen_sized_class *)
  Class GenSized (A : Type) := { arbitrarySized : nat -> G A }.
(* end gen_sized_class *)

(* begin gen_class *)
  Class Gen (A : Type) := { arbitrary : G A }.
(* end gen_class *)

(** Shrink class *)
Class Shrink (A : Type) :=
  { shrink : A -> list A }.

(** Arbitrary Class *)
Class Arbitrary (A : Type) `{Gen A} `{Shrink A}.

(** * Sizes of types *)
  
Class Sized (A : Type) :=
  { size : A -> nat }.

Class CanonicalSized (A : Type) `{Sized A} :=
  {
    zeroSized : set A;
    succSized : set A -> set A;

    zeroSized_spec : zeroSized <--> [ set x : A | size x = 0 ];
    succSized_spec :
      forall n, succSized [ set x : A | size x <= n ] <--> [ set x : A | size x <= S n ]
 
  }.

Lemma size_ind (A : Type) `{Hyp : Sized A} :
  forall (P : A -> Prop), (forall y, (forall x, size x < size y -> P x) -> P y) -> (forall x, P x).
Proof.
  intros P H1.
  intros x.
  assert (Hin : [ set y :  A | size y <= size x] x); eauto.
  revert Hin.
  generalize (size x). intros n.
  revert x. induction n.
  - intros x Hl. apply H1. intros x1 Hlt. ssromega.
  - intros x Hleq. eapply H1. intros x1 Hlt.
    eapply IHn. ssromega.
Qed.

Lemma size_lfp (A : Type) `{Hyp : CanonicalSized A} :
  [set x : A | True ] <--> \bigcup_(s : nat) [set x : A | size x <= s ].
Proof.
  intros a; split; eauto. intros _.
  exists (size a). split; eauto. constructor.
Qed.

Lemma succ_lfp (A : Type) `{Hyp : CanonicalSized A}
      `{Proper _ (respectful set_eq set_eq) succSized} s :
  [set x : A | size x <= s ] <-->  (succSized ^ s) zeroSized.
Proof.
  induction s.
  simpl.
  - rewrite zeroSized_spec.
    split; intros; ssromega.
  - simpl. rewrite <- succSized_spec.
    rewrite IHs. reflexivity.
Qed.

(* Lemma succ_lfp' (A : Type) `{Hyp : CanonicalSized A} : *)
(*   \bigcup_(s : nat)  (succSized ^ s) zeroSized <--> [ set x : A | True ]. *)
(* Proof. *)
(*   intros. split; eauto. *)
(*   intros _. *)
(*   eapply set_eq_trans. *)
(*   Focus 2. symmetry. *)
(*   eapply succ_lfp. *)
(*   simpl.  *)
(*   rewrite succ_lfp at 2. *)
(* split. *)
(*     split. rewrite IHs. firstorder. *)
(*     IHs. *)
(*   firstorder. reflexivity. split; intros; eauto. *)
(*   exists (size a). *)
(*   remember (size a) as s. *)
(*   revert a Heqs. induction s; intros. *)
(*   - split. constructor. *)
(*     simpl. eapply zeroSized_spec. now eauto. *)
(*   - split. constructor. *)
(*     simpl. *)
(*     eapply (succSized_spec. *)
(*     eassumption. *)
(*   eapply size_ind. *)
  
(*   [set x : A | True ] <-->  . *)

(** * Correctness classes *)

(** Correctness of sized generators *)
Class SizedCorrect {A : Type} `{Sized A} (g : nat -> G A) :=
  {
    arbitrarySizedCorrect : forall s, semGen (g s) <--> [set x : A | size x <= s ]
  }.

(** Correctness of generators *)
Class Correct (A : Type) (g : G A)  :=
  {
    arbitraryCorrect : semGen g <--> [set : A]
  }.

(** * Monotonic generators *)

(** Monotonicity of size parametric generators *)
Class GenSizedMonotonic (A : Type) `{GenSized A}
      `{forall s, SizeMonotonic (arbitrarySized s)}.

(** Monotonicity of size parametric generators v2 *)
Class GenSizedSizeMonotonic (A : Type) `{GenSized A} `{SizedMonotonic A arbitrarySized}.

Class GenMonotonic (A : Type) `{Gen A} `{SizeMonotonic A arbitrary}.

(** * Correct generators *)

Class GenSizedCorrect (A : Type) `{GenSized A} `{SizedCorrect A arbitrarySized}.

Class GenCorrect (A : Type) `{Gen A} `{Correct A arbitrary}.
 
(* Monotonic and Correct generators *)
Class GenMonotonicCorrect (A : Type)
      `{Gen A} `{SizeMonotonic A arbitrary} `{Correct A arbitrary}.

(** Coercions *)
  
Instance GenSizedMonotonicOfSizeMonotonic
         (A : Type) (Hgen : GenSized A) (Hmon : forall s, @SizeMonotonic A (arbitrarySized s))
: @GenSizedMonotonic A Hgen Hmon.
  
Instance GenMonotonicOfSizeMonotonic
         (A : Type) (Hgen : Gen A) (Hmon : @SizeMonotonic A arbitrary)
: @GenMonotonic A Hgen Hmon.

Instance GenSizedCorrectOfSizedCorrect
         (A : Type) (Hgen : GenSized A) `{Hcor : SizedCorrect A arbitrarySized}
: @GenSizedCorrect A Hgen _ Hcor.

Instance GenCorrectOfCorrect
         (A : Type) (Hgen : Gen A) `{Hcor : Correct A arbitrary}
: @GenCorrect A Hgen Hcor.

Instance GenSizedSizeMonotonicOfSizedMonotonic
         (A : Type) (Hgen : GenSized A) (Hmon : @SizedMonotonic A arbitrarySized)
: @GenSizedSizeMonotonic A Hgen Hmon.

(* Zoe : Is global really needed here? *)
Global Instance GenOfGenSized {A} `{GenSized A} : Gen A :=
  {| arbitrary := sized arbitrarySized |}.

Global Instance ArbitraryOfGenShrink {A} `{Gen A} `{Shrink A} : Arbitrary A.

Generalizable Variables PSized PMon PSMon PCorr.

Instance GenMonotonicOfSized (A : Type)
         {H : GenSized A}
         `{@GenSizedMonotonic A H PMon}
         `{@GenSizedSizeMonotonic A H PSMon}
: GenMonotonic A.

Instance GenCorrectOfSized (A : Type)
         {H : GenSized A}
         `{@GenSizedMonotonic A H PMon}
         `{@GenSizedSizeMonotonic A H PSMon}
         `{@GenSizedCorrect A H PSized PCorr} : Correct A arbitrary.
Proof.
  constructor. unfold arbitrary, GenOfGenSized. 
  eapply set_eq_trans.
  - eapply semSized_alt; eauto with typeclass_instances.
  - setoid_rewrite arbitrarySizedCorrect.
    split. intros [n H3]. constructor; eauto.
    intros H4. eexists; split; eauto.
Qed.

Lemma nat_set_ind (A : Type) `{GenSized A} `{Hyp : CanonicalSized A} :
  (semGen (arbitrarySized 0) <--> zeroSized) ->
  (forall (s : nat) (elems : set A),
     semGen (arbitrarySized s) <--> elems ->
     semGen (arbitrarySized (s.+1)) <--> succSized elems) ->
  (forall s : nat, semGen (arbitrarySized s) <--> (fun x : A => size x <= s)).
Proof.
  intros HO IH. intros n; induction n.
  - eapply set_eq_trans with (B := (fun x : A => size x = 0)).
    rewrite -zeroSized_spec //=.
    intros s. destruct (size s). now firstorder.
    split; intros; ssromega.
  - rewrite -succSized_spec. eauto.
Qed.
