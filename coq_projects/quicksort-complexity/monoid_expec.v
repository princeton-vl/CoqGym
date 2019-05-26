Set Implicit Arguments.

Require Import expec.
Require Import monoid_monad_trans.
Require Import monoid_tree_monad.
Require Import Rdefinitions.
Require Import monads.
Require Import util.
Require Import Bool.
Require Import sums_and_averages.
Require Import List.
Require Import list_utils.
Require Import Rbase.
Require ne_tree_monad.

Arguments fst {A B}.

Definition map_fst (A B C: Set) (f: A -> B) (p: A * C): B * C := (f (fst p), snd p).

Section contents.

  Variables (m: Monoid) (ms: m -> nat).

  Definition monoid_expec {A: Set}:
    MonoidMonadTrans.M m ne_tree_monad.ext A -> R
      := expec (ms ∘ (fst (B:=_:Set))).

  Lemma monoid_expec_bind_leaf (X Y: Set) (f: X -> MonoidMonadTrans.M m ne_tree_monad.ext Y)
    (n: prod m X):
    monoid_expec (@bind (MonoidMonadTrans.M m ne_tree_monad.ext) _ _ (ne_tree.Leaf n) f) =
    expec (ms ∘ monoid_mult m (fst n) ∘ (fst (B:=_:Set))) (f (snd n)).
  Proof.
    intros.
    unfold monoid_expec.
    rewrite MonoidMonadTrans.bind_toLower'.
    rewrite ne_tree_monad.bind_Leaf.
    simpl @ret.
    simpl mon.
    rewrite expec_bind_leaf.
    reflexivity.
  Qed.

  Hypothesis mh: monoidHomo m NatAddMonoid ms.

  Definition monoid_expec_sum (T U: Set)
  (g: T -> MonoidMonadTrans.M m ne_tree_monad.ext U): list T -> R
    := Rsum ∘ map (monoid_expec ∘ g).

  Lemma monoid_expec_sum_ext (T U: Set)
    (f g: T -> MonoidMonadTrans.M m ne_tree_monad.ext U):
      ext_eq f g ->
      ext_eq (monoid_expec_sum f) (monoid_expec_sum g).
  Proof with auto.
    unfold monoid_expec_sum.
    intros.
    intro.
    unfold compose.
    f_equal.
    apply map_ext.
    intro.
    f_equal.
    apply H.
  Qed.

  Lemma monoid_expec_Node_map (A B: Set) (f: A -> MonoidMonadTrans.M m ne_tree_monad.ext B) (l: ne_list.L A):
    monoid_expec (ne_tree.Node (ne_list.map f l)) =
    monoid_expec_sum f l / INR (length l).
  Proof with auto.
    unfold monoid_expec, monoid_expec_sum.
    intros.
    rewrite expec_Node.
    rewrite ne_list.map_map.
    unfold Ravg.
    rewrite ne_list.map_length.
    unfold monoid_expec.
    rewrite ne_list.plain_map...
  Qed.

  Lemma monoid_expec_ret (A: Set) (a: A): monoid_expec (ret a) = 0.
  Proof with auto.
    intros.
    simpl.
    unfold monoid_expec.
    unfold expec, compose.
    simpl.
    rewrite (monoidHomo_zero mh)...
  Qed.

  Lemma monoid_expec_bind_leaf_plus (X Y: Set) (f: X -> MonoidMonadTrans.M m ne_tree_monad.ext Y)
    (n: prod m X):
    monoid_expec (@bind (MonoidMonadTrans.M m ne_tree_monad.ext) _ _ (ne_tree.Leaf n) f) =
       INR (ms (fst n)) + monoid_expec (f (snd n)).
  Proof with auto.
    intros.
    rewrite monoid_expec_bind_leaf.
    unfold monoid_expec.
    rewrite (@expec_ext _ (ms ∘ monoid_mult m (fst n) ∘ fst (A:=m) (B:=Y)) (plus (ms (fst n)) ∘ ms ∘ fst)).
      rewrite <- comp_ass.
      rewrite (ext_eq_rw (expec_plus_c (ms ∘ fst (A:=m) (B:=Y)) (ms (fst n)))).
      reflexivity.
    intro.
    repeat rewrite comp_apply.
    apply (monoidHomo_mult mh).
  Qed.

  Lemma monoid_expec_bind_det (X: Set) (v: prod m X) (x: MonoidMonadTrans.M m ne_tree_monad.ext X):
    ne_tree_monad.deterministic x v -> forall (Y: Set) (f: X -> MonoidMonadTrans.M m ne_tree_monad.ext Y), monoid_expec (x >>= f) = monoid_expec x + monoid_expec (f (snd v)).
  Proof with auto with real.
    intros.
    rewrite H.
    rewrite monoid_expec_bind_leaf_plus.
    unfold monoid_expec.
    rewrite expec_Leaf.
    reflexivity.
  Qed.

  Hint Resolve ne_tree.In_head.

  Lemma monoid_expec_plus (A B: Set)
    (f: MonoidMonadTrans.M m ne_tree_monad.ext A)
    (g: A -> MonoidMonadTrans.M m ne_tree_monad.ext B) :
    forall (gc: forall x y, ne_tree.In x f -> ne_tree.In y f ->
     monoid_expec (g (snd x)) = monoid_expec (g (snd y))),
      monoid_expec (f >>= g) = monoid_expec f + monoid_expec (g (snd (ne_tree.head f))).
  Proof with auto with real.
    revert f.
    induction f.
        rewrite (@monoid_expec_bind_det _ n)...
        unfold ne_tree_monad.deterministic...
      unfold monoid_expec in *.
      rewrite MonoidMonadTrans.bind_toLower in *.
      rewrite ne_tree_monad.bind_Node_one.
      repeat rewrite expec_Node_one.
      intros.
      rewrite IHf...
    unfold monoid_expec in *.
    rewrite MonoidMonadTrans.bind_toLower in *.
    rewrite expec_Node_cons.
    rewrite expec_bind_cons.
    intros.
    rewrite IHf...
    rewrite IHf0.
      simpl ne_tree.head.
      repeat rewrite S_INR.
      rewrite (gc (ne_tree.head (ne_list.head l)) (ne_tree.head f))...
        simpl.
        unfold ne_tree_monad.C.
        field...
      apply ne_tree.InNode. apply ne_tree.InTail.
      destruct l...
    intros.
    inversion_clear H. inversion_clear H0.
    apply gc...
  Qed.

  Lemma monoid_expec_map_fst_monoid_mult (A: Set) (g: m) (t: MonoidMonadTrans.M m ne_tree_monad.ext A):
    monoid_expec (ne_tree.map (map_fst (monoid_mult m g)) t) =
    INR (ms g) + monoid_expec t.
  Proof with auto.
    intros.
    unfold monoid_expec.
    unfold expec.
    rewrite comp_apply.
    rewrite ne_tree.map_map.
    assert (ext_eq
      (INR ∘ (ms ∘ fst (A:=m) (B:=A)) ∘ map_fst (C:=A) (monoid_mult m g))
      (INR ∘ plus (ms g) ∘ mult 1 ∘ (ms ∘ fst (A:=m) (B:=A)))).
      intro.
      unfold compose.
      simpl.
      rewrite (monoidHomo_mult mh).
      simpl.
      rewrite plus_0_r...
    rewrite (ne_tree.map_ext H).
    rewrite <- ne_tree.map_map.
    cset (lin_nat 1 (ms g) (ne_tree.map (ms ∘ fst (A:=m) (B:=A)) t)).
    rewrite comp_apply in H0.
    rewrite H0.
    repeat rewrite comp_apply.
    simpl INR.
    rewrite Rmult_1_l.
    rewrite ne_tree.map_map...
  Qed.

  Lemma monoid_expec_bind_0_r (A B: Set)
    (g: A -> MonoidMonadTrans.M m ne_tree_monad.ext B)
    (gc: forall x, monoid_expec (g x) = 0)
    (f: MonoidMonadTrans.M m ne_tree_monad.ext A):
      monoid_expec (f >>= g) = monoid_expec f.
  Proof with auto with real.
    intros.
    rewrite monoid_expec_plus.
      rewrite gc.
      apply Rplus_0_r.
    intros.
    do 2 rewrite gc...
  Qed.

End contents.
