Set Implicit Arguments.
Unset Standard Proposition Elimination Names.

Require Import List.
Require Import list_utils.
Require Import Bool.
Require Import expec.
Require Import util.
Require Import sums_and_averages.
Require Import Rbase.

Arguments length {A}.

Section contents.

  Variables (X: Set) (eq_X_dec: forall (x y: X), { x = y } + { x <> y }).
  Definition beq_X (x y: X): bool := unsum_bool (eq_X_dec x y).

  Lemma counts_0_length_0 (l: list X): (forall i, count (beq_X i) l = 0%nat) -> length l = 0%nat.
  Proof with auto.
    destruct l; simpl...
    intros.
    elimtype False.
    specialize (H x).
    unfold beq_X in H.
    destruct (eq_X_dec x x)...
    simpl in H.
    discriminate.
  Qed.

  Lemma counts_0_expec_length_0 t:
    (forall i, expec (count (beq_X i)) t = 0) -> expec (@length (_:Set)) t = 0.
  Proof with auto.
    intros.
    replace 0 with (INR 0)...
    apply expec_constant.
    intros.
    apply counts_0_length_0.
    intros.
    apply (expec_0_inv (count (beq_X i))) with t...
  Qed.

  Lemma exp_list_sum_le (fr: X -> R) (q: list X) (t: ne_tree.T (list X)):
    (forall i, In i q -> expec (count (beq_X i)) t <= fr i) ->
    (forall i, ~ In i q -> expec (count (beq_X i)) t = 0) ->
    expec (@length (_:Set)) t <= Rsum (map fr q).
  Proof with auto with real.
    induction q in t |- *.
      simpl.
      intros.
      rewrite counts_0_expec_length_0...
    simpl.
    intros.
    rewrite (@expec_ext _ (@length (_:Set)) (fun x => plus (count (beq_X a) x) (count (negb ∘ beq_X a) x)) ).
      Focus 2.
      intro.
      apply length_excl_counts.
    rewrite expec_plus.
    apply Rle_trans with (fr a + expec (count (fun t0: X => negb (beq_X a t0))) t)...
    apply Rplus_le_compat_l.
    apply Rle_trans with (expec (@length (_:Set)) (ne_tree.map (filter (fun x: X => negb (beq_X a x))) t)).
      rewrite expec_map.
      apply expec_le.
      intros.
      rewrite comp_apply.
      rewrite length_filter...
    apply IHq...
      intros.
      rewrite expec_map.
      destruct (eq_X_dec a i).
        subst.
        apply Rle_trans with (expec (count (beq_X i)) t)...
        apply expec_le.
        intros.
        repeat rewrite comp_apply.
        apply count_filter_le.
      apply Rle_trans with (expec (count (beq_X i)) t).
        apply expec_le.
        intros.
        repeat rewrite comp_apply.
        apply count_filter_le.
      apply H.
      right...
    intros.
    rewrite expec_map.
    destruct (eq_X_dec a i).
      subst.
      replace 0 with (INR 0)...
      apply expec_constant.
      intros.
      rewrite comp_apply.
      apply count_filtered.
      intros.
      destruct (beq_X i x0)...
    apply Rle_antisym.
      apply Rle_trans with (expec (count (beq_X i)) t).
        apply expec_le.
        intros.
        rewrite comp_apply.
        apply count_filter_le.
      rewrite H0...
      intro.
      destruct H2...
    apply expec_nonneg.
  Qed.

End contents.
