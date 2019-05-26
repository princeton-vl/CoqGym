Set Implicit Arguments.

Require Import util.
Require Import Le.
Require Import Plus.
Require Import Lt.
Require Import List.
Require Import monads.
Require Import monoid_monad_trans.
Require Import nat_seqs.
Require Import Compare_dec.
Require qs_definitions.
Require qs_parts.
Require U.
Require Import expec.
Require Import arith_lems.
Require Import list_utils.
Require Import indices.
Require Import sort_order.
Require Import nat_below.
Require Import skip_list.
Require Import Bvector.

Section contents.

  Variables (ee: E) (ol: list ee).

  Import qs_definitions.mon_nondet.

  Lemma NeTree_In_Node_inv (A: Set) (r: A) (l: ne_list.L (ne_tree.T A)):
    ne_tree.In r (ne_tree.Node l) -> ne_tree.InL r l.
  Proof.
    intros.
    inversion H.
    assumption.
  Qed.

  Lemma pair_eq_inv (X Y: Set) (x x': X) (y y': Y): (x, y) = (x', y') -> x' = x /\ y' = y.
  Proof.
    intros.
    inversion H.
    split; reflexivity.
  Qed.

  Let qs := @U.qs ee ol.

  Theorem qs_sound_cmps_2: forall l,
    forall r, ne_tree.In r (qs l) ->
      forall i j, In (i, j) (fst r) -> IndexIn i l /\ IndexIn j l.
  Proof with auto with arith. (* simpler version of the one below. doesn't provide (i < j), and doesn't need NoDup l *)
    subst qs. unfold U.qs.
    intro.
    pattern l, (qs_definitions.mon_nondet.qs (U.cmp (e:=ee) (ol:=ol)) U.pick l).
    apply U.qs_ind.
      Focus 1.
      simpl.
      intros r H.
      inversion_clear H.
      simpl.
      intros.
      elimtype False...
    intros.
    cset (NeTree_In_Node_inv H0). clear H0.
    destruct (ne_tree.InL_map_inv _ _ H2). clear H2. destruct H0.
    destruct (ne_tree.In_map_inv _ _ H0). clear H0. destruct H3.
    subst r.
    unfold monoid_expec.map_fst in H1.
    unfold fst in H1.
    destruct (in_app_or _ _ _ H1); clear H1.
      destruct (In_map_inv H0). clear H0. destruct H1.
      unfold U.unordered_nat_pair in H0.
      unfold IndexIn.
      destruct (le_lt_dec x1 (vec.nth v x)); destruct (pair_eq_inv H0); split; subst; apply in_map.
            apply vec.remove_In with x...
          apply vec.In_nth.
        apply vec.In_nth.
      apply vec.remove_In with x...
    destruct (ne_tree_monad.In_bind_inv _ _ H3). clear H3. destruct H1.
    unfold U.M in H3.
    rewrite MonoidMonadTrans.bind_toLower in H3.
    rewrite (@mon_assoc ne_tree_monad.M ) in H3.
    destruct (ne_tree_monad.In_bind_inv _ _ H3). clear H3. destruct H4.
    revert H0.
    rewrite (@mon_assoc ne_tree_monad.M) in H4.
    rewrite MonoidMonadTrans.ret_toLower in H4.
    rewrite (@mon_lunit ne_tree_monad.M) in H4.
    simpl @fst in H4.
    rewrite (@mon_lunit ne_tree_monad.M) in H4.
    simpl @fst in H4.
    unfold snd in H4.
    inversion_clear H4.
    simpl.
    rewrite app_nil_r.
    intros.
    assert (forall k cr, IndexIn k (filter (fun f: Index ee ol => unsum_bool (cmp_cmp (Ecmp ee (subscript f) (subscript (vec.nth v x))) cr)) (vec.remove v x)) -> IndexIn k v).
      intros.
      unfold IndexIn in *.
      apply (incl_In _ H4).
      apply incl_map.
      apply incl_trans with (vec.remove v x)...
      apply SkipList_incl.
      apply vec.SkipList_remove.
    destruct (in_app_or _ _ _ H0).
      destruct (H x Lt x1 H1 _ _ H5).
      split; apply H4 with Lt...
    destruct (H x Gt x2 H3 _ _ H5).
    split; apply H4 with Gt...
  Qed.

  Theorem qs_sound_cmps: forall l,
    forall r, ne_tree.In r (qs l) -> NoDup l ->
      forall i j, In (i, j) (fst r) -> i < j.
  Proof with auto with arith.
    subst qs. unfold U.qs.
    intro.
    pattern l, (qs_definitions.mon_nondet.qs (U.cmp (e:=ee) (ol:=ol)) U.pick l).
    apply U.qs_ind.
      simpl.
      intros r H.
      inversion_clear H.
      simpl.
      intros.
      elimtype False...
    intros.
    cset (NeTree_In_Node_inv H0). clear H0.
    destruct (ne_tree.InL_map_inv _ _ H3). clear H3. destruct H0.
    destruct (ne_tree.In_map_inv _ _ H0). clear H0. destruct H4.
    subst r.
    unfold monoid_expec.map_fst in H2.
    unfold fst in H2.
    destruct (in_app_or _ _ _ H2); clear H2.
      destruct (In_map_inv H0). clear H0. destruct H2.
      unfold U.unordered_nat_pair in H0.
      destruct (le_lt_dec x1 (vec.nth v x)); destruct (pair_eq_inv H0)...
        subst.
        apply ne_le_impl_lt...
        intro.
        rewrite (vec.List_Permutation (vec.perm_sym (vec.remove_perm x v))) in H1.
        inversion_clear H1.
        apply H6.
        cset(natBelow_unique _ _ H5).
        subst x1...
      subst...
    destruct (ne_tree_monad.In_bind_inv _ _ H4). clear H4. destruct H2.
    unfold U.M in H4.
    rewrite MonoidMonadTrans.bind_toLower in H4.
    rewrite (@mon_assoc ne_tree_monad.M ) in H4.
    destruct (ne_tree_monad.In_bind_inv _ _ H4). clear H4. destruct H5.
    revert H0.
    rewrite (@mon_assoc ne_tree_monad.M) in H5.
    rewrite MonoidMonadTrans.ret_toLower in H5.
    rewrite (@mon_lunit ne_tree_monad.M) in H5.
    simpl @fst in H5.
    rewrite (@mon_lunit ne_tree_monad.M) in H5.
    simpl @fst in H5.
    unfold snd in H5.
    inversion_clear H5.
    simpl.
    rewrite app_nil_r.
    intros.
    assert (forall cr, NoDup (filter (fun f: Index ee ol => unsum_bool (cmp_cmp (Ecmp ee (subscript f) (subscript (vec.nth v x))) cr)) (vec.remove v x))).
      intros.
      apply NoDup_SkipList with v...
      apply SkipList_trans with (vec.remove v x).
        apply SkipList_filter.
      apply vec.SkipList_remove.
    assert (forall k cr, IndexIn k (filter (fun f: Index ee ol => unsum_bool (cmp_cmp (Ecmp ee (subscript f) (subscript (vec.nth v x))) cr)) (vec.remove v x)) -> IndexIn k v).
      intros.
      unfold IndexIn in *.
      apply (incl_In _ H6).
      apply incl_map.
      apply incl_trans with (vec.remove v x)...
      apply SkipList_incl.
      apply vec.SkipList_remove.
    destruct (in_app_or _ _ _ H0).
      apply H with x Lt x1...
    apply H with x Gt x2...
  Qed.

  Require Import monoid_expec.
  Require Import Rbase.

  Lemma sound_cmp_expec_0 i j (l: list (Index ee ol)):
    (~ In i l \/ ~ In j l) -> monoid_expec (U.ijcount i j) (qs l) = 0.
  Proof with auto.
    intros.
    unfold monoid_expec.
    replace 0 with (INR 0)...
    apply (expec_constant).
    intros.
    unfold compose.
    apply U.ijcount_0.
    intro.
    destruct (qs_sound_cmps_2 l H0 i j )...
    destruct H.
      apply H.
      unfold IndexIn in H2.
      destruct (In_map_inv H2).
      destruct H4.
      cset (natBelow_unique _ _ H4).
      subst...
    apply H.
    unfold IndexIn in H3.
    destruct (In_map_inv H3).
    destruct H4.
    cset (natBelow_unique _ _ H4).
    subst...
  Qed.

End contents.
