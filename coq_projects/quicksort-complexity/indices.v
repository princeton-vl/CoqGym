
Set Implicit Arguments.

Require Import util.
Require Import Le.
Require Import arith_lems.
Require Import Plus.
Require Import Minus.
Require Import Lt.
Require Import Arith.
Require Import Recdef.
Require Import Bool_nat.
Require Import List.
Require Import list_utils.
Require Import Omega.
Require Import Arith.
Require Import Bool.
Require Import EqNat.
Require Import nat_seqs.
Require Import sort_order.
Require Vector.
Require Import Relations.
Require Import nat_below.
Require vec.
Require Import Compare_dec.

Section contents.

  Variables (T: E) (ol: list T).

  Definition Index := natBelow (length ol).

  Definition subscript: Index -> T := vec.nth (vec.insertion_sort (@Ele T) (@Ele_le_dec T) ol).

  Definition UE: E :=
    Build_E (fun x y: Index => Ecmp T (subscript x) (subscript y))
      (fun x y => Ecmp_sym T (subscript x) (subscript y))
      (fun x y z => Ecmp_trans T (subscript x) (subscript y) (subscript z))
      (fun x y z => Ecmp_eq_trans_l T (subscript x) (subscript y) (subscript z)).

  Definition IndexIn (i: nat) (l: list Index): Prop := In i (map nb_val l).

  Definition IndexSeq (b: nat) (l: list Index): Prop :=
    forall i, b <= i -> i < b + length l -> IndexIn i l.

  Definition IndexSeq_above (b: nat) (l: list Index): Prop := IndexSeq (b - length l) l.

  Lemma IndicesCorrect e e': Ecmp UE e e' = Lt -> e < e'.
  Proof.
    unfold UE. simpl.
    unfold subscript.
    intros.
    apply (vec.sorted_lt_values_lt_indices (@EO T) (vec.insertion_sort_sorts (@Ele T) (@Ele_le_dec T) ol)).
    unfold vec.Xlt.
    unfold Ele in *.
    rewrite H.
    rewrite Ecmp_sym.
    rewrite H.
    simpl.
    firstorder; try intro; discriminate.
  Qed.

  Lemma IndicesCorrect_inv (x y: Index): x < y -> @Ele UE x y.
  Proof with try assumption.
    repeat intro.
    apply lt_asym with (nb_val x) (nb_val y)...
    apply IndicesCorrect.
    apply Ecmp_apply_sym...
  Qed.

  Lemma IndexSeq_nil b: IndexSeq b nil.
  Proof. do 3 intro. elimtype False. apply (lt_irrefl i). simpl in H0. omega. Qed.

  Hint Resolve IndexSeq_nil.

  Lemma IndexSeq_perm: forall (b: nat) (l: list Index), IndexSeq b l -> forall l', Permutation.Permutation l' l -> IndexSeq b l'.
  Proof with auto.
    unfold IndexSeq.
    intros.
    rewrite (Permutation.Permutation_length H0) in H2.
    unfold IndexIn.
    apply incl_In with (map (nb_val (n:=length ol)) l)...
      apply H...
    apply Permutation_incl.
    apply Permutation.Permutation_sym...
  Qed.

  Definition IndexSeq_uncons l b:
    IndexSeq b l -> l <> nil -> exists l', exists p: Index, nb_val p = b /\ Permutation.Permutation (p :: l') l.
  Proof with auto.
    destruct l; intros.
      intros.
      elimtype False...
    assert (b < b + length (i :: l)).
      simpl. omega.
    specialize (H b (le_refl _) H1).
    unfold IndexIn in H.
    destruct (In_map_inv H). clear H.
    destruct H2.
    subst b.
    destruct (In_inv_perm _ _ H2).
    eauto.
  Qed.

  Lemma IndexSeq_cons_inv (b: Index) (l: list Index): IndexSeq b (b :: l) -> IndexSeq (S b) l.
  Proof with auto.
    do 4 intro.
    assert (b <= i) by omega.
    assert (i < b + S (length l)). omega.
    cset (H i H2 H3).
    unfold IndexIn in *.
    destruct (In_map_inv H4). clear H4.
    destruct H5.
    subst i.
    apply in_map.
    inversion_clear H5...
    subst.
    elimtype False.
    apply (le_Sn_n x)...
  Qed.

  Lemma vec_IndexSeq_nats_perm b n (v: Vector.t Index n): IndexSeq b v ->
    vec.Permutation (vec.map nb_val v) (vec.nb_nats b n).
  Proof with auto.
    unfold vec.nb_nats.
    intros.
    apply vec.perm_sym.
    apply vec.NoDup_incl_Permutation.
      rewrite <- vec.List_map.
      apply NoDup_map.
        intros.
        apply natBelow_unique...
      apply vec.NoDup_nats.
    do 2 intro.
    rewrite <- vec.List_map in H0.
    destruct (In_map_inv H0). clear H0.
    destruct H1. subst.
    destruct (vec.In_nats_inv _ _ _ H1). clear H1.
    rewrite <- vec.List_map.
    apply H...
    rewrite vec.length.
    omega.
  Qed.

  Lemma nats_Permutation_IndexSeq' b n (l: Vector.t Index n):
    vec.Permutation (vec.map nb_val l) (vec.nb_nats b n) -> IndexSeq b l.
  Proof with auto.
    intros.
    unfold IndexSeq.
    intros.
    unfold IndexIn.
    apply Permutation.Permutation_in with (vec.to_list (vec.nb_nats b n)).
      apply Permutation.Permutation_sym.
      cset (vec.List_Permutation H).
      rewrite <- vec.List_map in H2...
    rewrite vec.length in H1.
    apply vec.In_nb_nats'...
  Qed.

  Definition IndexSeq_NoDup b l: IndexSeq b l -> NoDup l.
  Proof with auto.
    rewrite <- (vec.list_round_trip l).
    cset (vec.from_list l).
    intro.
    apply (NoDup_map_inv' (@nb_val (length ol))).
    rewrite vec.List_map.
    assert (Permutation.Permutation (vec.map nb_val H) (vec.to_list (vec.nb_nats b (length l)))).
      apply vec.List_Permutation, vec_IndexSeq_nats_perm...
    rewrite H1.
    unfold vec.nb_nats.
    rewrite <- vec.List_map.
    apply NoDup_map.
      intros.
      apply natBelow_unique...
    apply vec.NoDup_nats.
  Qed.

  Lemma IndexSeq_inv l: forall b, IndexSeq b l -> forall t, In t l -> b <= t < b + length l.
  Proof with auto with arith.
    rewrite <- (vec.list_round_trip l).
    cset (vec.from_list l).
    intros.
    assert (In (nb_val t) (map nb_val (vec.to_list H))).
      apply in_map...
    rewrite vec.List_map in H2.
    assert (In (nb_val t) (vec.nb_nats b (length l))).
      apply Permutation.Permutation_in with (vec.to_list (vec.map (nb_val (n:=length ol)) H))...
      apply vec.List_Permutation.
      apply (vec_IndexSeq_nats_perm H H0).
    rewrite vec.length.
    rewrite plus_comm.
    apply (vec.In_nb_nats_inv _ _ _ H3).
  Qed.

  Hint Resolve in_map.

  Lemma IndexSeq_base_lowest_value' (b: Index) l: IndexSeq b l -> forall e, In e l -> @Ele UE b e.
  Proof with auto.
    unfold UE. unfold Ele. simpl.
    intros.
    intro.
    apply lt_irrefl with b.
    apply le_lt_trans with e.
      destruct (IndexSeq_inv H e H0)...
    rewrite Ecmp_sym in H1.
    case_eq (Ecmp T (subscript e) (subscript b)); intro; rewrite H2 in H1.
        discriminate.
      apply (IndicesCorrect e b H2).
    discriminate.
  Qed.

  Lemma IndexSeq_cons (b: Index) l: IndexSeq (S b) l -> IndexSeq b (b :: l).
  Proof with auto.
    intros.
    do 3 intro.
    destruct (le_lt_or_eq b i H0).
      intros.
      unfold IndexSeq in H.
      right.
      apply H...
      simpl in H1.
      omega.
    subst.
    left...
  Qed.

  Lemma indices: exists tl, ol = map subscript tl /\ IndexSeq 0 tl.
  Proof with auto.
    intros.
    destruct (vec.Permutation_mapping (vec.perm_sym (vec.insertion_sort_permutes (@Ele T) (@Ele_le_dec T) ol))).
    destruct H.
    exists (vec.to_list x).
    split.
      rewrite vec.List_map...
      apply vec.eq_list.
      symmetry...
    unfold IndexSeq.
    intros.
    unfold IndexIn.
    rewrite vec.length in H2.
    simpl in H2.
    destruct (lt_exists_plus H2). clear H2.
    clear H0.
    revert H.
    revert x.
    rewrite H3. clear H3. intros.
    cut (In (mkNatBelow i x0) (vec.to_list x))...
    intros.
    apply (in_map nb_val _ _ H0).
  Qed.

  Lemma IndexSeq_filterLt e n : forall b l, length l = n ->
    IndexSeq b l -> IndexSeq b (filter (fun f => unsum_bool (cmp_cmp (Ecmp UE f e) Lt)) l).
  Proof with auto with arith.
    unfold UE.
    simpl.
    induction n.
      intros.
      destruct l.
        simpl.
        apply IndexSeq_nil.
      discriminate.
    intros.
    assert (l <> nil). intro. subst. discriminate.
    destruct (IndexSeq_uncons H0 H1).
    destruct H2.
    destruct H2.
    subst b.
    replace n with (length x) in *.
      Focus 2.
      cset (Permutation.Permutation_length H3).
      simpl in H2.
      unfold Index in H, H2.
      rewrite H in H2.
      inversion H2...
    apply IndexSeq_perm with (filter (fun f => unsum_bool (cmp_cmp (Ecmp T (subscript f) (subscript e)) Lt)) (x0 :: x))...
      Focus 2.
      apply filter_perm.
      repeat intro...
      apply Permutation.Permutation_sym...
    assert (In x0 (x0 :: x)).
      left...
    cset (IndexSeq_base_lowest_value' _ (IndexSeq_perm H0 H3) ).
    simpl.
    case_eq (Ecmp T (subscript x0) (subscript e)); intro.
        rewrite (proj1_conj (filter_none (fun f: Index => unsum_bool (cmp_cmp (Ecmp T (subscript f) (subscript e)) Lt)) x))...
        intros.
        case_eq (Ecmp T (subscript x1) (subscript e))...
        intros.
        elimtype False.
        unfold UE, Ele in H4. simpl in H4.
        apply H4 with x1.
          right...
        apply Ecmp_apply_sym.
        simpl.
        apply Ecmp_eq_trans_r with (subscript e)...
        apply Ecmp_apply_sym...
      simpl.
      apply IndexSeq_cons...
      apply IHn...
      apply (IndexSeq_cons_inv (IndexSeq_perm H0 H3)).
    rewrite (proj1_conj (filter_none (fun f: Index => unsum_bool (cmp_cmp (Ecmp T (subscript f) (subscript e)) Lt)) x))...
    intros.
    case_eq (Ecmp T (subscript x1) (subscript e))...
    intros.
    elimtype False.
    apply H4 with x1.
      right...
    apply Ecmp_apply_sym.
    simpl.
    apply Ecmp_trans with (subscript e)...
    apply Ecmp_apply_sym...
  Qed.

  Lemma IndexSeq_filterGt e l: forall b, IndexSeq b l ->
    IndexSeq_above (b + length l) (filter (fun f => unsum_bool (cmp_cmp (Ecmp UE f e) Gt)) l).
  Proof with auto.
    set (length l).
    assert (n = length l)...
    clearbody n.
    revert H. revert l.
    induction n.
      intros.
      destruct l.
        simpl.
        unfold IndexSeq_above.
        apply IndexSeq_nil.
      discriminate.
    intros.
    assert (l <> nil). intro. subst l. discriminate.
    destruct (IndexSeq_uncons H0 H1).
    destruct H2.
    destruct H2.
    subst b.
    cut (IndexSeq_above (x0 + S n) (filter (fun f: Index => unsum_bool (cmp_cmp (Ecmp T (subscript f) (subscript e)) Gt)) (x0 :: x))).
      unfold IndexSeq_above.
      intro.
      rewrite length_filter in *.
      rewrite <- (count_perm_simple _ H3).
      apply IndexSeq_perm with (filter (fun f: Index => unsum_bool (cmp_cmp (Ecmp T (subscript f) (subscript e)) Gt)) (x0 :: x))...
      apply filter_perm.
        repeat intro...
      apply Permutation.Permutation_sym...
    simpl filter.
    replace n with (length x) in *.
      Focus 2.
      cset (Permutation.Permutation_length H3).
      simpl in H2.
      rewrite <- H in H2.
      inversion H2...
    assert (IndexSeq_above (x0 + S (length x)) (filter (fun f: Index => unsum_bool (cmp_cmp (Ecmp T (subscript f) (subscript e)) Gt)) x)).
      rewrite <- plus_Snm_nSm.
      apply IHn...
      apply IndexSeq_cons_inv.
      apply IndexSeq_perm with l...
    case_eq (Ecmp T (subscript x0) (subscript e)); intro...
    simpl.
    unfold IndexSeq_above.
    assert (IndexSeq (S x0) x).
      apply IndexSeq_cons_inv.
      apply IndexSeq_perm with l...
    rewrite filter_all.
      simpl @length.
      rewrite plus_comm.
      rewrite minus_plus.
      apply IndexSeq_perm with l...
    intros.
    replace (Ecmp T (subscript x1) (subscript e)) with Gt...
    rewrite Ecmp_sym.
    replace (Ecmp T (subscript e) (subscript x1)) with Lt...
    assert (In x1 l).
      cut (In x1 (x0 :: x)).
        intro.
        apply (Permutation.Permutation_in _ H3 H7).
      right...
    cset (IndexSeq_base_lowest_value' x0 H0 x1 H7).
    unfold Ele, UE in H8. simpl in H8.
    fold (@Ele T (subscript x0) (subscript x1)) in H8.
    symmetry.
    apply Ecmp_lt_le_trans with (subscript x0)...
    rewrite Ecmp_sym.
    rewrite H4...
  Qed.

  Lemma InvIndexSeq_filterGt' e l b:
    IndexSeq b (e :: l) -> IndexSeq_above (b + S (length l)) (filter (fun f => unsum_bool (cmp_cmp (Ecmp UE f e) Gt)) l).
  Proof with auto.
    intros.
    cset (IndexSeq_filterGt e H).
    simpl filter in H0.
    rewrite Ecmp_refl in H0.
    simpl in H0...
  Qed.

End contents.
