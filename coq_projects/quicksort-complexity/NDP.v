Set Implicit Arguments.

Require Import List.
Require Import monads.
Require Import monoid_monad_trans.
Require qs_definitions.
Import qs_definitions.mon_nondet.
Require ne_tree_monad.
Require Import Plus.
Require Import monoid_tree_monad.

Section contents.

  Variable E: sort_order.E.

  Definition M: Monad := MonoidMonadTrans.M NatAddMonoid ne_tree_monad.ext.

  Definition cmp (x y: E): M comparison :=
    @ret ne_tree_monad.M _ (1%nat, sort_order.Ecmp E x y).

  Definition pick := monoid_tree_monad.pick NatAddMonoid.

  Lemma Mext: extMonad M.
  Proof MonoidMonadTrans.Mext NatAddMonoid ne_tree_monad.ext.

  Lemma partition d l: partition M cmp d l = ne_tree.Leaf (length l, qs_definitions.simplerPartition E d l).
  Proof with auto.
    induction l...
    simpl.
    rewrite (@mon_assoc (ne_tree_monad.M)).
    rewrite IHl.
    simpl.
    rewrite plus_0_r...
  Qed.

  Definition qs := qs cmp pick.

End contents.
