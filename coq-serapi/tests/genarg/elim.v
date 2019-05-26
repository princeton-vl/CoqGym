Require Import ZArith.
Require Import ZArith.Zmax.
Require Import ssr.ssreflect.

Open Scope Z_scope.

Section BinaryTree.

Inductive Tree : Set :=
| leaf : Tree
| node : Tree -> Tree -> Tree.           

Definition max := Z.max.

Fixpoint height (t : Tree) : Z := 
match t with 
| leaf => 0
| node t1 t2 => 1 + (max (height t1) (height t2))
end.

Fixpoint numleaves (t : Tree) : Z :=
match t with 
| leaf => 1
| node t1 t2 => numleaves t1 + numleaves t2
end.

Inductive complete : Tree -> Prop :=
| complete_leaf : complete leaf
| complete_node : 
    forall t1 t2, 
      complete t1 -> 
      complete t2 -> 
      height t1 = height t2 ->
      complete (node t1 t2).

Lemma height_nonnegative : forall t, height t >= 0.
Proof.
elim => //=.
move => t1 Ht1 t2 Ht2.
have H0: height (node t1 t2) = 1 + max (height t1) (height t2) by auto.
have H1: height t1 <= max (height t1) (height t2) by apply Z.le_max_l.
have H2: 1 + max (height t1) (height t2) >= 0 by auto with zarith.
by [].
Qed.

Theorem complete_numleaves_height : forall t, complete t -> numleaves t = 2^(height t).
Proof.
elim => //=.
move => t1 IHt1 t2 IHt2 Hc.
have H1: complete t1 by inversion Hc.
have H2: complete t2 by inversion Hc.
have H3: (height t1 = height t2) by inversion Hc; auto.
apply IHt1 in H1.
apply IHt2 in H2.
have H6: (1 >= 0) by intuition.
have H7: (height t1 >= 0) by apply height_nonnegative.
have H8: (height t1 = max (height t1) (height t1)) by erewrite Zmax_idempotent.
simpl numleaves.
rewrite H1 H2.
rewrite -H3.
have Hh: 2 ^ height t1 + 2 ^ height t1 = (2 * 2^(height t1)) by auto with zarith.
rewrite Hh.
have Hh': (2 * 2^(height t1)) = (2^1 * 2^(height t1)) by auto with zarith.
rewrite Hh'.
have Hh'': 2^(1 + height t1) = (2^1 * 2^(height t1)).
  by apply (Zpower_exp 2 1 (height t1) H6 H7).
by rewrite -Hh'' {1}H8.
Qed.

End BinaryTree.
