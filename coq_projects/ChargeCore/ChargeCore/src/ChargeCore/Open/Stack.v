Require Import Coq.Logic.FunctionalExtensionality.

Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.Consider.

Set Implicit Arguments.
Unset Strict Implicit.
Set Primitive Projections.

Set Maximal Implicit Insertion.
Set Universe Polymorphism.

Class ValNull (val : Type) := {
  null : val
}.

Section Defs.
  Context {A val : Type}.
  Context {HA : RelDec (@eq A)} {HR : RelDec_Correct HA}.
  Context {VNB : ValNull val}.

  Definition stack := A -> val.

  Definition stack_empty : stack := fun x => null.

  Definition stack_get (x : A) : stack -> val  := fun s => s x.

  Definition stack_add x v s : stack :=
    fun x' => if x' ?[ eq ] x then v else s x'.

  Lemma stack_lookup_add (s : stack) (x : A) (v : val) :
      ((stack_add x v s) : stack) x = v.
  Proof.
    unfold stack_add; consider (x ?[ eq ] x); intros H; [reflexivity|congruence].
  Qed.

  Lemma stack_lookup_add2 (x y : A) (v : val) (s : stack) (Hneq: x <> y) :
    (stack_add x v s) y = s y.
  Proof.
    unfold stack_add. consider (y ?[ eq ] x); intros; [congruence|reflexivity].
  Qed.

  Lemma stack_add_same (s: stack) x:
    stack_add x (s x) s = s.
  Proof.
    apply functional_extensionality.
    intro x'. unfold stack_add.
    consider (x' ?[ eq ] x); intros; subst; reflexivity.
  Qed.

  Lemma stack_add_overwrite (s: stack) x v v':
    stack_add x v (stack_add x v' s) = stack_add x v s.
  Proof.
    apply functional_extensionality.
    intro x'. unfold stack_add.
    consider (x' ?[ eq ] x); intros; reflexivity.
  Qed.

  Lemma stack_add_val_eq (s : stack) (x : A) v1 v2 (Hs : stack_add x v1 s = stack_add x v2 s) :
  	v1 = v2.
  Proof.
    assert (stack_add x v1 s x = stack_add x v2 s x).
    rewrite Hs. reflexivity.
    do 2 rewrite stack_lookup_add in H. apply H.
  Qed.

End Defs.

Arguments stack _ _ : clear implicits, assert.
Arguments stack_empty A val {_}.

Hint Rewrite @stack_lookup_add
             @stack_add_same
             @stack_add_overwrite : stack.

Hint Rewrite @stack_lookup_add2 using solve [auto] : stack.