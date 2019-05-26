Require Export MSets.
Require Import Arith.
Require Import NArith.
Require Import Notations.
Require Import Sorting.
Require Import Coq.Program.Equality.
Require Export GeoCoq.Tactics.Coinc.tactics_axioms.

Module S := MSetList.Make PositiveOrderedTypeBits.
(*
We choose to use lists as it is as fast as AVLs for a limited number of points but they are easier to debug.
Module S := MSetAVL.Make PositiveOrderedTypeBits.
*)

Module SWP := WPropertiesOn PositiveOrderedTypeBits S.

Module SetOfSetsOfPositiveOrderedType <: OrderedType.

  Definition t := S.t.

  Definition eq := S.Equal.

  Include IsEq.

  Definition eqb := S.equal.

  Definition eqb_eq := S.equal_spec.

  Include HasEqBool2Dec.

  Definition lt := S.lt.

  Instance lt_compat : Proper (eq==>eq==>iff) lt.
  Proof.
  apply S.lt_compat.
 Qed.

  Instance lt_strorder : StrictOrder lt.
  Proof.
  apply S.lt_strorder.
 Qed.

  Definition compare := S.compare.

  Definition compare_spec := S.compare_spec.

End SetOfSetsOfPositiveOrderedType.

Module SS := MSetList.Make SetOfSetsOfPositiveOrderedType.
(*
Module SS := MSetAVL.Make SetOfSetsOfPositiveOrderedType.
*)

Definition fstpp (pair : (positive * positive)) :=
  match pair with
    |(a,b) => Pos.min a b
  end.

Definition sndpp (pair : (positive * positive)) :=
  match pair with
    |(a,b) => Pos.max a b
  end.

Module SetOfPairsOfPositiveOrderedType <: OrderedType.

  Definition t:= (positive * positive).

  Definition eq (t1 t2 : t) :=
    Pos.eq (fstpp(t1)) (fstpp(t2)) /\ Pos.eq (sndpp(t1)) (sndpp(t2)).

  Include IsEq.

  Definition eqb (t1 t2 : t) :=
    Pos.eqb (fstpp(t1)) (fstpp(t2)) && Pos.eqb (sndpp(t1)) (sndpp(t2)).

  Lemma eqb_eq : forall t1 t2, eqb t1 t2 = true <-> eq t1 t2.
  Proof.
  intros.
  unfold eqb; unfold eq.
  split; intro H.

    apply andb_true_iff in H.
    induction H.
    split; apply Pos.eqb_eq; assumption.

    induction H.
    apply andb_true_iff.
    split; apply Pos.eqb_eq; assumption.
 Qed.

  Include HasEqBool2Dec.

  Definition lt (t1 t2 : t) :=
    let ft1 := fstpp(t1) in
    let ft2 := fstpp(t2) in
    let st1 := sndpp(t1) in
    let st2 := sndpp(t2) in
    if Pos.eqb ft1 ft2 then Pos.lt st1 st2
                       else Pos.lt ft1 ft2.

  Lemma lt_irrefl : Irreflexive lt.
  Proof.
  assert (HIP : Irreflexive Pos.lt)
    by (apply StrictOrder_Irreflexive; assumption).
  unfold Irreflexive in *.
  unfold Reflexive in *.
  unfold complement in *.
  intro x.
  unfold lt.
  assert (HEq : Pos.eqb (fstpp(x)) (fstpp(x)) = true)
    by (apply Pos.eqb_eq; intuition).
  rewrite HEq.
  apply HIP.
 Qed.

  Lemma lt_antiref : forall x, ~ lt x x.
  Proof.
  assert (HIL : Irreflexive lt) by (apply lt_irrefl).
  unfold Irreflexive in *.
  unfold Reflexive in *.
  unfold complement in *.
  intros x H.
  apply HIL with x.
  apply H.
 Qed.

  Lemma lt_trans : Transitive lt.
  Proof.
  assert (HTP : Transitive Pos.lt) by (apply StrictOrder_Transitive; assumption).
  unfold Transitive in *.
  intros x y z.
  unfold lt.
  case_eq (Pos.eqb (fstpp(x)) (fstpp(y))).

    intro HEqXY.
    case_eq (Pos.eqb (fstpp(y)) (fstpp(z))).

      intro HEqYZ.
      assert (HEqXZ : Pos.eqb (fstpp(x)) (fstpp(z)) = true)
        by (apply Pos.eqb_eq in HEqXY; rewrite HEqXY; assumption).
      rewrite HEqXZ.
      apply HTP.

      intro HNEqYZ.
      assert (HNEqXZ : Pos.eqb (fstpp(x)) (fstpp(z)) = false)
        by (apply Pos.eqb_eq in HEqXY; rewrite HEqXY; assumption).
      rewrite HNEqXZ.
      apply Pos.eqb_eq in HEqXY; rewrite HEqXY.
      intro.
      intuition.

    intro HNEqXY.
    case_eq (Pos.eqb (fstpp(y)) (fstpp(z))).

      intro HEqYZ.
      assert (HNEqXZ : Pos.eqb (fstpp(x)) (fstpp(z)) = false)
        by (apply Pos.eqb_eq in HEqYZ; rewrite <- HEqYZ; assumption).
      rewrite HNEqXZ.
      apply Pos.eqb_eq in HEqYZ; rewrite HEqYZ.
      intros.
      assumption.

      intro HNEqYZ.
      case_eq (Pos.eqb (fstpp(x)) (fstpp(z))).

        intro HEqXZ.
        intros.
        assert (HLtXZ : Pos.ltb (fstpp(x)) (fstpp(z)) = true)
          by (apply Pos.ltb_lt; apply HTP with (fstpp(y)); assumption).
        apply Pos.eqb_eq in HEqXZ; rewrite HEqXZ in HLtXZ.
        assert (HIP : Irreflexive Pos.lt)
          by (apply StrictOrder_Irreflexive; assumption).
        unfold Irreflexive in HIP.
        unfold Reflexive in HIP.
        unfold complement in HIP.
        exfalso.
        apply HIP with (fstpp(z)).
        apply Pos.ltb_lt in HLtXZ.
        assumption.

        intro HNEqXZ.
        intros.
        apply HTP with (fstpp(y)); assumption.
 Qed.

  Instance lt_compat : Proper (eq==>eq==>iff) lt.
  Proof.
  intros x y HXY x' y' HX'Y'.
  unfold lt; unfold eq in *.
  elim HXY; intros HXYF HXYS.
  elim HX'Y'; intros HX'Y'F HX'Y'S.
  clear HXY; clear HX'Y'.
  unfold Pos.eq in *.
  case_eq (Pos.eqb (fstpp(x)) (fstpp(x'))); intro HXX'F.

    assert (HYY'F : Pos.eqb (fstpp(y)) (fstpp(y')) = true).
    apply Pos.eqb_eq in HXX'F.
    apply Pos.eqb_eq.
    rewrite <- HXYF.
    rewrite <- HX'Y'F.
    assumption.

    rewrite HYY'F.
    case_eq (Pos.eqb (sndpp(x)) (sndpp(x'))); intro HXX'S.

      apply Pos.eqb_eq in HXX'S.
      assert (HYY'S : Pos.eqb (sndpp(y)) (sndpp(y')) = true).
      apply Pos.eqb_eq.
      rewrite <- HXYS.
      rewrite <- HX'Y'S.
      assumption.

      apply Pos.eqb_eq in HYY'S.
      rewrite HYY'S.
      rewrite HXX'S.
      rewrite HX'Y'S.
      intuition.

      rewrite HXYS.
      rewrite HX'Y'S.
      intuition.

    assert (HYY'F : Pos.eqb (fstpp(y)) (fstpp(y')) = false).
    rewrite <- HXYF.
    rewrite <- HX'Y'F.
    assumption.

    rewrite HYY'F.
    rewrite HXYF.
    rewrite HX'Y'F.
    intuition.
 Qed.

  Instance lt_strorder : StrictOrder lt.
  Proof.
  apply Build_StrictOrder.
  apply lt_irrefl.
  apply lt_trans.
 Qed.

  Definition compare t1 t2 :=
    let ft1 := fstpp(t1) in
    let ft2 := fstpp(t2) in
    let st1 := sndpp(t1) in
    let st2 := sndpp(t2) in
    match (Pos.compare ft1 ft2) with
      | Lt => Lt
      | Eq => Pos.compare st1 st2
      | Gt => Gt
    end.

  Lemma compare_spec : forall t1 t2, CompSpec eq lt t1 t2 (compare t1 t2).
  Proof.
  intros t1 t2.
  case_eq (Pos.eqb (fstpp(t1)) (fstpp(t2))); intro HF.

    apply Pos.eqb_eq in HF.
    case_eq (Pos.eqb (sndpp(t1)) (sndpp(t2))); intro HS.

      apply Pos.eqb_eq in HS.
      unfold CompSpec.

      assert (HC : compare t1 t2 = Eq).
      unfold compare.

      assert (HCF : Pos.compare (fstpp(t1)) (fstpp(t2)) = Eq).
      unfold Pos.compare.
      rewrite HF.
      apply Pos.compare_cont_refl.

      assert (HCS : Pos.compare (sndpp(t1)) (sndpp(t2)) = Eq).
      unfold Pos.compare.
      rewrite HS.
      apply Pos.compare_cont_refl.

      rewrite HCF; rewrite HCS.
      intuition.

      rewrite HC.
      apply CompEq.
      unfold eq.
      rewrite HF; rewrite HS; split; intuition.

      case_eq (Pos.ltb (sndpp(t1)) (sndpp(t2))); intro HLS.

        assert (HC : compare t1 t2 = Lt).
        unfold compare.

        assert (HCF : Pos.compare (fstpp(t1)) (fstpp(t2)) = Eq).
        unfold Pos.compare.
        rewrite HF.
        apply Pos.compare_cont_refl.

        assert (HCS : Pos.compare (sndpp(t1)) (sndpp(t2)) = Lt).
        unfold Pos.compare.
        apply Pos.ltb_lt in HLS.
        apply Pnat.nat_of_P_lt_Lt_compare_complement_morphism.
        apply Pnat.Pos2Nat.inj_lt.
        assumption.

        rewrite HCF; rewrite HCS.
        intuition.

        rewrite HC.
        apply CompLt.
        unfold lt.
        apply Pos.eqb_eq in HF.
        rewrite HF.
        apply Pos.ltb_lt in HLS.
        assumption.

        assert (HLS2 : Pos.ltb (sndpp(t2)) (sndpp(t1)) = true).
        apply Pos.ltb_nlt in HLS.
        apply Pos.le_nlt in HLS.
        apply Pos.lt_eq_cases in HLS.
        elim HLS; intro HLS2.
        apply Pos.ltb_lt.
        assumption.
        apply Pos.eqb_neq in HS.
        rewrite HLS2 in HS.
        intuition.

        assert (HC : compare t1 t2 = Gt).
        unfold compare.

        assert (HCF : Pos.compare (fstpp(t1)) (fstpp(t2)) = Eq).
        unfold Pos.compare.
        rewrite HF.
        apply Pos.compare_cont_refl.

        assert (HCS : Pos.compare (sndpp(t1)) (sndpp(t2)) = Gt).
        unfold Pos.compare.
        apply Pos.ltb_lt in HLS2.
        apply Pnat.nat_of_P_gt_Gt_compare_complement_morphism.
        apply Pnat.Pos2Nat.inj_gt.
        apply Pos.gt_lt_iff.
        assumption.

        rewrite HCF; rewrite HCS.
        intuition.

        rewrite HC.
        apply CompGt.
        unfold lt.
        apply Pos.eqb_eq in HF.
        rewrite Pos.eqb_sym in HF.
        rewrite HF.
        apply Pos.ltb_lt in HLS2.
        assumption.

      case_eq (Pos.ltb (fstpp(t1)) (fstpp(t2))); intro HLF.

        assert (HC : compare t1 t2 = Lt).
        unfold compare.

        assert (HCF : Pos.compare (fstpp(t1)) (fstpp(t2)) = Lt).
        unfold Pos.compare.
        apply Pos.ltb_lt in HLF.
        apply Pnat.nat_of_P_lt_Lt_compare_complement_morphism.
        apply Pnat.Pos2Nat.inj_lt.
        assumption.

        rewrite HCF.
        intuition.

        rewrite HC.
        apply CompLt.
        unfold lt.
        rewrite HF.
        apply Pos.ltb_lt in HLF.
        assumption.

        assert (HLF2 : Pos.ltb (fstpp(t2)) (fstpp(t1)) = true).
        apply Pos.ltb_nlt in HLF.
        apply Pos.le_nlt in HLF.
        apply Pos.lt_eq_cases in HLF.
        elim HLF; intro HLF2.
        apply Pos.ltb_lt.
        assumption.
        apply Pos.eqb_neq in HF.
        rewrite HLF2 in HF.
        intuition.

        assert (HC : compare t1 t2 = Gt).
        unfold compare.

        assert (HCF : Pos.compare (fstpp(t1)) (fstpp(t2)) = Gt).
        unfold Pos.compare.
        apply Pos.ltb_lt in HLF2.
        apply Pnat.nat_of_P_gt_Gt_compare_complement_morphism.
        apply Pnat.Pos2Nat.inj_gt.
        apply Pos.gt_lt_iff.
        assumption.

        rewrite HCF.
        intuition.

        rewrite HC.
        apply CompGt.
        unfold lt.
        rewrite Pos.eqb_sym in HF.
        rewrite HF.
        apply Pos.ltb_lt in HLF2.
        assumption.
 Qed.

End SetOfPairsOfPositiveOrderedType.

Module SP := MSetList.Make SetOfPairsOfPositiveOrderedType.
(*
Module SP := MSetAVL.Make SetOfPairsOfPositiveOrderedType.
*)

Module PosOrder <: TotalLeBool.

  Definition t := positive.

  Definition leb := Pos.leb.

  Lemma leb_total : forall p1 p2,
    leb p1 p2 = true \/ leb p2 p1 = true.
  Proof.
  intros.
  do 2 (rewrite Pos.leb_le).
  do 2 (rewrite Pos.le_lteq).
  assert (HElim := Pos.lt_total p1 p2).
  elim HElim; clear HElim; intro HElim.
  left; left; assumption.
  elim HElim; clear HElim; intro HElim.
  left; right; assumption.
  right; left; assumption.
 Qed.

  Lemma leb_dec : forall p1 p2,
    leb p1 p2 = true \/ leb p1 p2 = false.
  Proof.
  intros.
  elim Pos.eq_dec with p1 p2.

    intro; subst.
    left; apply POrderedType.Positive_as_DT.leb_refl.

    intro HNeq.
    elim leb_total with p1 p2; intro Hp1p2.

      left; assumption.

        right.
        rewrite Positive_as_DT.leb_gt.
        rewrite Positive_as_DT.leb_le in Hp1p2.
        rewrite Pos.lt_eq_cases in Hp1p2.
        elim Hp1p2; intro.

          assumption.

          subst; intuition.
 Qed.

End PosOrder.

Module Import PosSort := Sort PosOrder.

Definition OCPAux {n : nat} (cp : cartesianPower positive (S (S n))) := (PosSort.sort (CPToList cp)).

Lemma OCPALengthOK {n : nat} : forall (cp : cartesianPower positive (S (S n))), (length (OCPAux cp)) = (S (S n)).
Proof.
intro cp.
unfold OCPAux.
assert (HPerm := Permuted_sort (CPToList cp)).
apply Permutation.Permutation_length in HPerm.
rewrite <- HPerm.
apply eq_sym.
apply lengthOfCPToList.
Defined.

Lemma OCPSortedTl :
  forall (l : list positive),
  StronglySorted (fun x x0 : positive => is_true (x <=? x0)%positive) l ->
  StronglySorted (fun x x0 : positive => is_true (x <=? x0)%positive) (tl l).
Proof.
intros l HSorted.
induction l.
simpl; apply SSorted_nil.
clear IHl.
simpl; apply StronglySorted_inv in HSorted; destruct HSorted as [HSorted Hhd].
assumption.
Qed.

Lemma PermSorted : forall (l l' : list positive),
  Permutation.Permutation l l' ->
  StronglySorted (fun x x0 : positive => is_true (x <=? x0)%positive) l ->
  StronglySorted (fun x x0 : positive => is_true (x <=? x0)%positive) l' ->
  l = l'.
Proof.
intro l; induction l.

  intro l'; induction l'.

    reflexivity.

    intro HPerm.
    apply Permutation.Permutation_nil_cons in HPerm.
    intuition.

  intro l'; induction l'.

    intro HPerm.
    apply Permutation.Permutation_sym in HPerm.
    apply Permutation.Permutation_nil_cons in HPerm.
    intuition.

    intros HPerm Hl Hl'.
    assert (HIna' : In a (a :: l)) by (apply in_eq).
    assert (HIna : In a (a0 :: l')) by (apply Permutation.Permutation_in with (a :: l); assumption).
    assert (HIna0' : In a0 (a0 :: l')) by (apply in_eq).
    assert (HIna0 : In a0 (a :: l))
      by (apply Permutation.Permutation_in with (a0 :: l'); apply Permutation.Permutation_sym in HPerm;assumption).
    clear HIna'; clear HIna0'; apply in_inv in HIna; apply in_inv in HIna0.
    elim HIna; clear HIna; intro HIna; elim HIna0; clear HIna0; intro HIna0;
    try (rewrite HIna in *); try (rewrite <- HIna0 in *).

      assert (HPerm' : Permutation.Permutation l l')
        by (apply Permutation.Permutation_app_inv_l with (a :: nil); simpl; assumption).
      apply OCPSortedTl in Hl; apply OCPSortedTl in Hl'.
      apply IHl in HPerm'; try assumption.
      rewrite HPerm'; reflexivity.

      assert (HPerm' : Permutation.Permutation l l')
        by (apply Permutation.Permutation_app_inv_l with (a :: nil); simpl; assumption).
      apply OCPSortedTl in Hl; apply OCPSortedTl in Hl'.
      apply IHl in HPerm'; try assumption.
      rewrite HPerm'; reflexivity.

      assert (HPerm' : Permutation.Permutation l l')
        by (apply Permutation.Permutation_app_inv_l with (a :: nil); simpl; assumption).
      apply OCPSortedTl in Hl; apply OCPSortedTl in Hl'.
      apply IHl in HPerm'; try assumption.
      rewrite HPerm'; reflexivity.

      assert (Hle1 := Hl); assert (Hle2 := Hl').
      apply StronglySorted_inv in Hle1; apply StronglySorted_inv in Hle2.
      destruct Hle1 as [Hclear Hle1]; clear Hclear; destruct Hle2 as [Hclear Hle2]; clear Hclear.
      assert (Haa0 : (forall x, In x l -> is_true (Pos.leb a x))) by (apply Forall_forall; assumption).
      assert (Ha0a : (forall x, In x l' -> is_true (Pos.leb a0 x))) by (apply Forall_forall; assumption).
      apply Ha0a in HIna.
      apply Haa0 in HIna0.
      unfold is_true in *.
      apply Pos.leb_le in HIna; apply Pos.leb_le in HIna0.
      assert (H := Pos.le_antisym a0 a HIna HIna0).
      rewrite H in *.
      assert (HPerm' : Permutation.Permutation l l')
        by (apply Permutation.Permutation_app_inv_l with (a :: nil); simpl; assumption).
      apply OCPSortedTl in Hl; apply OCPSortedTl in Hl'.
      apply IHl in HPerm'; try assumption.
      rewrite HPerm'; reflexivity.
Qed.

Definition OCP {n : nat} (cp : cartesianPower positive (S (S n))) : cartesianPower positive (S (S n)).
Proof.
assert (H := OCPALengthOK cp).
rewrite <- H.
exact (ListToCP (OCPAux cp) (fst cp)).
Defined.

Lemma OCPSortedAux {n : nat} :
  forall (cp : cartesianPower positive (S (S n))),
  StronglySorted (fun x x0 : positive => is_true (x <=? x0)%positive) (CPToList (OCP cp)).
Proof.
intros cp.
unfold OCP.
unfold OCPAux.
elim_eq_rect; simpl.
rewrite CPLOK.
apply StronglySorted_sort.
intros x1 x2 x3.
unfold is_true.
intros Hx1x2 Hx2x3.
apply Pos.leb_le in Hx1x2.
apply Pos.leb_le in Hx2x3.
apply Pos.leb_le.
transitivity x2; assumption.
Qed.

Lemma OCPPerm {n : nat} :
  forall (cp : cartesianPower positive (S (S n))),
  Permutation.Permutation (CPToList cp) (CPToList (OCP cp)).
Proof.
intro cp.
unfold OCP.
unfold OCPAux.
elim_eq_rect; simpl.
rewrite CPLOK.
apply Permuted_sort.
Qed.

Lemma CPLOCPTlOK {n : nat} :
  forall (cp : cartesianPower positive (S (S (S n)))),
  headCP cp = headCP (OCP cp) ->
  CPToList (OCP (tailCP cp)) = CPToList (tailCP (OCP cp)).
Proof.
intros cp Hhd.
apply PermSorted.

  assert (H := OCPPerm cp).
  rewrite CPToListOK in H.
  apply Permutation.Permutation_sym in H.
  rewrite CPToListOK in H.
  rewrite <- Hhd in H.
  apply Permutation.Permutation_app_inv_l with ((headCP cp) :: nil).
  assert (H' : (headCP cp :: nil) ++ CPToList (OCP (tailCP cp)) = headCP cp :: (CPToList (OCP (tailCP cp))))
    by (simpl; reflexivity); rewrite H'; clear H'.
  assert (H' : (headCP cp :: nil) ++ CPToList (tailCP (OCP cp)) = headCP cp :: (CPToList (tailCP (OCP cp))))
    by (simpl; reflexivity); rewrite H'; clear H'.
  apply Permutation.Permutation_sym in H.
  apply Permutation.perm_trans with (headCP cp :: CPToList (tailCP cp)); try assumption; clear H.
  assert (H := OCPPerm (tailCP cp)).
  apply Permutation.Permutation_sym in H.
  apply Permutation.perm_skip.
  assumption.

  apply OCPSortedAux.

  rewrite <- CPToListTl2.
  apply OCPSortedTl.
  apply OCPSortedAux.
Qed.

Lemma OCPTlOK {n : nat} :
  forall (cp : cartesianPower positive (S (S (S n)))),
  headCP cp = headCP (OCP cp) ->
  OCP (tailCP cp) = tailCP (OCP cp).
Proof.
intros cp Hhd.
apply CPLOCPTlOK in Hhd.
apply CPLCP; assumption.
Qed.

Lemma InCPOCP {n : nat} : forall p (cp : cartesianPower positive (S (S n))),
  InCP p cp <-> InCP p (OCP cp).
Proof.
intros p cp.
unfold OCP.
unfold OCPAux.
unfold InCP.
elim_eq_rect; simpl.
induction n.

  rewrite CPLOK.
  assert (HPerm1 := Permuted_sort (CPToList cp)); simpl in HPerm1.
  assert (HPerm2 := HPerm1); apply Permutation.Permutation_sym in HPerm2.
  assert (HInOK : In p (sort (fst cp :: snd cp :: nil)) <-> In p (fst cp :: snd cp :: nil))
    by (split; intro HIn; try (apply Permutation.Permutation_in with (sort (fst cp :: snd cp :: nil)); assumption);
                          apply Permutation.Permutation_in with (fst cp :: snd cp :: nil); assumption).
  split; intro HIn.

    apply HInOK; simpl; assumption.

    apply HInOK in HIn; simpl in HIn; assumption.

  clear IHn.
  rewrite CPLOK.
  set (sscp := (nat_rect (fun n : nat => cartesianPower positive (S n) -> list positive)
                       (fun cp0 : cartesianPower positive 1 => cp0 :: nil)
                       (fun (n : nat) (IHn : cartesianPower positive (S n) -> list positive)
                       (cp0 : cartesianPower positive (S (S n))) =>
                       fst cp0 :: IHn (tailCP cp0)) n (tailCP (snd cp)))).
  assert (HPerm := Permuted_sort (fst cp :: fst (snd cp) :: sscp)).
  split; intro HIn.

    elim HIn; clear HIn; intro HIn.

      subst.
      apply Permutation.Permutation_in with (fst cp :: fst (snd cp) :: sscp); try assumption.
      apply in_eq.

      elim HIn; clear HIn; intro HIn.

        subst.
        apply Permutation.Permutation_in with (fst cp :: fst (snd cp) :: sscp); try assumption.
        apply in_cons.
        apply in_eq.

        apply Permutation.Permutation_in with (fst cp :: fst (snd cp) :: sscp); try assumption.
        do 2 (apply in_cons).
        assumption.

    apply Permutation.Permutation_sym in HPerm.
    assert (HInOKAux := Permutation.Permutation_in).
    assert (HInOK := HInOKAux positive (sort (fst cp :: fst (snd cp) :: sscp))
                                       (fst cp :: fst (snd cp) :: sscp) p HPerm HIn); clear HInOKAux; clear HIn.
    rename HInOK into HIn.
    assumption.
Qed.


Section Set_of_tuple_of_positive.

  Context {Ar : Arity}.

  Fixpoint eqList (l1 l2 : list positive) :=
    match l1, l2 with
      | nil, nil => True
      | (hd1 :: tl1), (hd2 :: tl2) => (Pos.eq hd1 hd2) /\ (eqList tl1 tl2)
      | _, _ => False
    end.

  Lemma eqListRefl : forall l, eqList l l.
  Proof.
    intro l; induction l; simpl.

      trivial.

      split; try assumption.
      reflexivity.
  Qed.

  Lemma eqListSym : forall l l', eqList l l' -> eqList l' l.
  Proof.
    intro l; induction l.

      intro l'; induction l'; auto.

      intro l'; induction l'; auto.
      simpl.
      intro H.
      destruct H as [Haa0 Hll'].
      split; intuition.
  Qed.

  Lemma eqListTrans : forall l1 l2 l3, eqList l1 l2 -> eqList l2 l3 -> eqList l1 l3.
  Proof.
    intro l1; induction l1.

      intro l2; induction l2.

        intro l3; induction l3.

          simpl; trivial.

          simpl; intuition.

        simpl; intuition.

      intro l2; induction l2.

        intro l3; induction l3.

          simpl; trivial.

          simpl; intuition.

        intro l3; induction l3.

          simpl; trivial.

          simpl.
          intros Hl1l2 Hl2l3.
          destruct Hl1l2 as [Haa0 Hl1l2].
          destruct Hl2l3 as [Ha0a1 Hl2l3].
          split.

            transitivity a0; assumption.

            apply IHl1 with l2; assumption.
  Qed.

  Definition tST := cartesianPower positive (S (S n)).

  Definition eqST (cp1 cp2 : tST) :=
    eqList (PosSort.sort (CPToList cp1)) (PosSort.sort (CPToList cp2)).

  Lemma eqListSortOCP : forall (cp : tST), eqList (CPToList (OCP cp)) (PosSort.sort (CPToList cp)).
  Proof.
    intro cp.
    unfold OCP.
    unfold OCPAux.
    elim_eq_rect.
    simpl.
    rewrite CPLOK.
    apply eqListRefl.
  Qed.

  Fixpoint eqbList (l1 l2 : list positive) :=
    match l1, l2 with
      | nil         , nil          => true
      | (hd1 :: tl1), (hd2 :: tl2) => (Pos.eqb hd1 hd2) && (eqbList tl1 tl2)
      | _           , _            => false
    end.

  Lemma eqbListEqList : forall l1 l2, eqbList l1 l2 = true <-> eqList l1 l2.
  Proof.
    intro l1.
    induction l1.

      intro l2.
      induction l2.

        simpl; unfold eqList.
        intuition.

        simpl; unfold eqList.
        split; intro; intuition; discriminate.

      intro l2.
      induction l2.

        simpl; unfold eqList.
        split; intro; intuition; discriminate.

        split; intro H.

          unfold eqbList in H.
          apply andb_true_iff in H.
          destruct H as [Hhd Htl].
          fold eqbList in Htl.
          assert (H := IHl1 l2).
          rewrite H in Htl.
          unfold eqList.
          split; try assumption.
          rewrite PositiveSet.E.eqb_eq in Hhd.
          subst; reflexivity.

          apply andb_true_iff.
          rewrite PositiveSet.E.eqb_eq; fold eqbList.
          unfold eqList in H.
          destruct H as [Hhd Htl].
          fold eqList in Htl.
          assert (H := IHl1 l2).
          rewrite <- H in Htl.
          split; assumption.
  Qed.

  Definition eqbST (cp1 cp2 : tST) :=
    eqbList (PosSort.sort (CPToList cp1)) (PosSort.sort (CPToList cp2)).

  Lemma eqbST_eqST : forall cp1 cp2, eqbST cp1 cp2 = true <-> eqST cp1 cp2.
  Proof. intros; unfold eqbST, eqST; apply eqbListEqList. Qed.

  Fixpoint ltList (l1 l2 : list positive) :=
    match l1, l2 with
      | nil, nil => False
      | (hd1 :: tl1), (hd2 :: tl2) => if (Pos.ltb hd1 hd2) then True
                                      else if (Pos.ltb hd2 hd1) then False
                                           else (ltList tl1 tl2)
      | nil, _ => True
      | _, nil => False
    end.

  Lemma lengthOne : forall (l : list positive),
    length l = 1 -> exists a, l = a :: nil.
  Proof.
    intros l Hl.
    induction l.

      simpl in Hl; discriminate.

      induction l.

        exists a; reflexivity.

      simpl in Hl; discriminate.
  Qed.

  Lemma lengthAtLeastOne : forall (l : list positive) n,
    length l = (S n) -> exists a0 l0, l = a0 :: l0.
  Proof.
    intros l n Hl.
    induction l.

      simpl in Hl; discriminate.

      exists a; exists l; reflexivity.
  Qed.

  Lemma ltListTrans : forall m x y z,
    length x = (S m) ->
    length y = (S m) ->
    length z = (S m) ->
    ltList x y -> ltList y z -> ltList x z.
  Proof.
    intro m; induction m; intros x y z lx ly lz Hxy Hyz.

      assert (Hx := lengthOne x lx); destruct Hx as [hdx Hx].
      assert (Hy := lengthOne y ly); destruct Hy as [hdy Hy].
      assert (Hz := lengthOne z lz); destruct Hz as [hdz Hz].
      subst; simpl in *.
      assert (H : Pos.ltb hdx hdz = true).

        rewrite Pos.ltb_lt.
        transitivity hdy.

          rewrite <- Pos.ltb_lt.
          induction (Pos.ltb hdx hdy); intuition.
          induction (Pos.ltb hdy hdx); intuition.

          rewrite <- Pos.ltb_lt.
          induction (Pos.ltb hdy hdz); intuition.
          induction (Pos.ltb hdz hdy); intuition.

        rewrite H; trivial.

      assert (Hx := lengthAtLeastOne x (S m) lx); destruct Hx as [hdx [tlx Hx]].
      assert (Hy := lengthAtLeastOne y (S m) ly); destruct Hy as [hdy [tly Hy]].
      assert (Hz := lengthAtLeastOne z (S m) lz); destruct Hz as [hdz [tlz Hz]].
      subst; simpl in *.
      assert (HEqxy := Pos.compare_eq hdx hdy).
      assert (HEqyz := Pos.compare_eq hdy hdz).
      assert (HLtxy := Pos.compare_nge_iff hdx hdy).
      assert (HLtyz := Pos.compare_nge_iff hdy hdz).
      assert (HGtxy := Pos.compare_gt_iff hdx hdy).
      assert (HGtyz := Pos.compare_gt_iff hdy hdz).
      induction (Pos.compare hdx hdy); induction (Pos.compare hdy hdz).

        assert (H : Eq = Eq) by reflexivity.
        apply HEqxy in H; clear HEqxy; clear HLtxy; clear HGtxy.
        assert (H' : Eq = Eq) by reflexivity.
        apply HEqyz in H'; clear HEqyz; clear HLtyz; clear HGtyz.
        subst.
        assert (H := Pos.ltb_irrefl hdz).
        rewrite H in *; clear H.
        apply eq_add_S in lx.
        apply eq_add_S in ly.
        apply eq_add_S in lz.
        apply IHm with tly; assumption.

        assert (H : Eq = Eq) by reflexivity.
        apply HEqxy in H; clear HEqxy; clear HLtxy; clear HGtxy.
        assert (H' : Lt = Lt) by reflexivity.
        apply HLtyz in H'; clear HEqyz; clear HLtyz; clear HGtyz.
        subst.
        rewrite <- Pos.lt_nle in H'.
        rewrite <- Pos.ltb_lt in H'.
        rewrite H' in *.
        trivial.

        assert (H : Eq = Eq) by reflexivity.
        apply HEqxy in H; clear HEqxy; clear HLtxy; clear HGtxy.
        assert (H' : Gt = Gt) by reflexivity.
        apply HGtyz in H'; clear HEqyz; clear HLtyz; clear HGtyz.
        subst.
        rewrite <- Pos.ltb_lt in H'.
        rewrite H' in *.
        trivial.

        assert (H : Lt = Lt) by reflexivity.
        apply HLtxy in H; clear HEqxy; clear HLtxy; clear HGtxy.
        assert (H' : Eq = Eq) by reflexivity.
        apply HEqyz in H'; clear HEqyz; clear HLtyz; clear HGtyz.
        subst.
        rewrite <- Pos.lt_nle in H.
        rewrite <- Pos.ltb_lt in H.
        rewrite H in *.
        trivial.

        assert (H : Lt = Lt) by reflexivity.
        apply HLtxy in H; clear HEqxy; clear HLtxy; clear HGtxy.
        assert (H' : Lt = Lt) by reflexivity.
        apply HLtyz in H'; clear HEqyz; clear HLtyz; clear HGtyz.
        rewrite <- Pos.lt_nle in H.
        rewrite <- Pos.lt_nle in H'.
        assert (H'' : Pos.lt hdx hdz) by (transitivity hdy; assumption).
        rewrite <- Pos.ltb_lt in H''.
        rewrite H''.
        trivial.

        clear HEqxy; clear HLtxy; clear HGtxy.
        assert (H : Gt = Gt) by reflexivity.
        apply HGtyz in H; clear HEqyz; clear HLtyz; clear HGtyz.
        rewrite <- Pos.ltb_lt in H.
        rewrite H in *.
        rewrite Pos.ltb_lt in H.
        rewrite Pos.lt_nle in H.
        assert (H' : Pos.ltb hdy hdz = false).

          rewrite Pos.ltb_nlt.
          intro H'.
          apply H.
          apply Pos.lt_eq_cases.
          left; assumption.

        rewrite H' in *.
        intuition.

        clear HEqyz; clear HLtyz; clear HGtyz.
        assert (H : Gt = Gt) by reflexivity.
        apply HGtxy in H; clear HEqxy; clear HLtxy; clear HGtxy.
        rewrite <- Pos.ltb_lt in H.
        rewrite H in *.
        rewrite Pos.ltb_lt in H.
        rewrite Pos.lt_nle in H.
        assert (H' : Pos.ltb hdx hdy = false).

          rewrite Pos.ltb_nlt.
          intro H'.
          apply H.
          apply Pos.lt_eq_cases.
          left; assumption.

        rewrite H' in *.
        intuition.

        clear HEqyz; clear HLtyz; clear HGtyz.
        assert (H : Gt = Gt) by reflexivity.
        apply HGtxy in H; clear HEqxy; clear HLtxy; clear HGtxy.
        rewrite <- Pos.ltb_lt in H.
        rewrite H in *.
        rewrite Pos.ltb_lt in H.
        rewrite Pos.lt_nle in H.
        assert (H' : Pos.ltb hdx hdy = false).

          rewrite Pos.ltb_nlt.
          intro H'.
          apply H.
          apply Pos.lt_eq_cases.
          left; assumption.

        rewrite H' in *.
        intuition.

        clear HEqyz; clear HLtyz; clear HGtyz.
        assert (H : Gt = Gt) by reflexivity.
        apply HGtxy in H; clear HEqxy; clear HLtxy; clear HGtxy.
        rewrite <- Pos.ltb_lt in H.
        rewrite H in *.
        rewrite Pos.ltb_lt in H.
        rewrite Pos.lt_nle in H.
        assert (H' : Pos.ltb hdx hdy = false).

          rewrite Pos.ltb_nlt.
          intro H'.
          apply H.
          apply Pos.lt_eq_cases.
          left; assumption.

        rewrite H' in *.
        intuition.
  Qed.

  Lemma sortOK : forall m l, length l = m -> length (sort l) = m.
  Proof.
    intros m l Hl.
    assert (H := Permuted_iter_merge l nil).
    apply Permutation.Permutation_length in H.
    unfold flatten_stack in H.
    simpl in H.
    rewrite <- Hl.
    rewrite H.
    unfold sort.
    reflexivity.
  Qed.

  Definition ltST (cp1 cp2 : tST) :=
    ltList (PosSort.sort (CPToList cp1)) (PosSort.sort (CPToList cp2)).

  Lemma ltTrans : Transitive ltST.
  Proof.
    unfold lt.
    intros x y z Hxy Hyz.

    assert (lx : (S (S n)) = (S (S n))) by reflexivity.
    assert (lx' := lengthOfCPToList x).
    assert (lx'' := sortOK (S (S n)) (CPToList x)).
    rewrite <- lx' in lx''; clear lx'.
    apply lx'' in lx; clear lx''.

    assert (ly : (S (S n)) = (S (S n))) by reflexivity.
    assert (ly' := lengthOfCPToList y).
    assert (ly'' := sortOK (S (S n)) (CPToList y)).
    rewrite <- ly' in ly''; clear ly'.
    apply ly'' in ly; clear ly''.

    assert (lz : (S (S n)) = (S (S n))) by reflexivity.
    assert (lz' := lengthOfCPToList z).
    assert (lz'' := sortOK (S (S n)) (CPToList z)).
    rewrite <- lz' in lz''; clear lz'.
    apply lz'' in lz; clear lz''.

    assert (H := ltListTrans (S n) (sort (CPToList x)) (sort (CPToList y)) (sort (CPToList z))).
    apply H; assumption.
  Qed.

  Lemma ltListIrrefl : forall l, ltList l l -> False.
  Proof.
    intro l.
    induction l.

      simpl; intuition.

      assert (H := Pos.lt_irrefl a).
      rewrite <- Pos.ltb_nlt in H.
      simpl.
      rewrite H.
      apply IHl.
  Qed.

  Lemma eqListOK : forall l1 l2, eqList l1 l2 -> l1 = l2.
  Proof.
    intro l1.
    induction l1.

      intro l2.
      induction l2.

        trivial.

        simpl; intuition.

      intro l2.
      induction l2.

        simpl; intuition.

        simpl.
        intro HEq.
        destruct HEq as [Hhd Htl].
        unfold Pos.eq in Hhd.
        apply IHl1 in Htl.
        subst.
        reflexivity.
  Qed.

  Fixpoint compareList (l1 l2 : list positive) :=
    match l1, l2 with
    | nil, nil => Eq
    | (hd1 :: tl1), (hd2 :: tl2) => match Pos.compare hd1 hd2 with
                                    | Lt => Lt
                                    | Eq => compareList tl1 tl2
                                    | Gt => Gt
                                    end
    | nil, _ => Lt
    | _, nil => Gt
    end.

  Lemma compareListSpec : forall l1 l2,
    CompSpec eqList ltList l1 l2 (compareList l1 l2).
  Proof.
    intro l1.
    unfold eqST; unfold lt.
    induction l1.

      intro l2.
      induction l2.

        simpl.
        apply CompEq.
        simpl; trivial.

        simpl.
        apply CompLt.
        simpl; trivial.

      intro l2.
      induction l2.

        simpl.
        apply CompGt.
        simpl; trivial.

        clear IHl2.
        assert (HEq := Pos.compare_eq a a0).
        assert (HLt := Pos.compare_nge_iff a a0).
        assert (HGt := Pos.compare_gt_iff a a0).
        induction (Pos.compare a a0).

          assert (H : Eq = Eq) by reflexivity.
          apply HEq in H; clear HEq; clear HLt; clear HGt.
          subst.
          simpl.
          rewrite POrderedType.Positive_as_OT.compare_refl.
          assert (H := IHl1 l2); clear IHl1.
          induction H.

            apply CompEq.
            simpl; split; auto; apply Pos.eq_refl.

            apply CompLt.
            simpl; rewrite Pos.ltb_irrefl; auto.

            apply CompGt.
            simpl; rewrite Pos.ltb_irrefl; auto.

          assert (H : Lt = Lt) by reflexivity.
          apply HLt in H; clear HEq; clear HLt; clear HGt.
          rewrite <- Pos.lt_nle in H.
          apply Pos.compare_lt_iff in H.
          simpl.
          rewrite H.
          apply CompLt.
          rewrite Pos.compare_lt_iff in H.
          rewrite <- Pos.ltb_lt in H.
          simpl.
          rewrite H.
          trivial.

          assert (H : Gt = Gt) by reflexivity.
          apply HGt in H; clear HEq; clear HLt; clear HGt.
          apply Pos.compare_gt_iff in H.
          simpl.
          rewrite H.
          apply CompGt.
          rewrite Pos.compare_gt_iff in H.
          rewrite <- Pos.ltb_lt in H.
          simpl.
          rewrite H.
          trivial.
  Qed.

  Definition compareST (cp1 cp2 : tST) :=
    compareList (PosSort.sort (CPToList cp1)) (PosSort.sort (CPToList cp2)).

  Lemma compare_spec : forall cp1 cp2,
    CompSpec eqST ltST cp1 cp2 (compareST cp1 cp2).
  Proof.
    intros cp1 cp2.
    unfold eqST, ltST, compareST.
    apply compareListSpec.
  Qed.
(*
TODO: try to see if using sorted lists would not make the tactic faster.
*)
  Definition STelt := tST.

  Definition STt := list tST.

  Definition STempty : STt := nil.

  Lemma eqST_dec : forall x y, {eqST x y} + {~ eqST x y}.
  Proof.
    intros x y; case_eq (eqbST x y); intro HEq.

      apply eqbST_eqST in HEq; left; auto.

      right; intro HEqST; apply eqbST_eqST in HEqST; rewrite HEq in *; discriminate.
  Qed.

  Definition STadd (x : STelt) (s : STt) := cons x s.

  Fixpoint STexists_ (f : STelt -> bool) (s : STt) :=
    match s with
      | nil      => false
      | hd :: tl => f hd || STexists_ f tl
    end.

  Fixpoint STmem elt l :=
    match l with
      | nil      => false
      | hd :: tl => if eqST_dec hd elt then true else STmem elt tl
    end.

  Lemma STempty_b : forall y : STelt, STmem y STempty = false.
  Proof. intros. reflexivity. Qed.

  Lemma STexists_mem_4 :
    forall f (s : STt),
      STexists_ f s = true ->
      exists x : STelt ,  STmem x s = true /\ f x = true.
  Proof.
    intros f s HEx; induction s;
    simpl in *; [discriminate|].
    case_eq (f a); intro Hfa; rewrite Hfa in *; simpl in *.

      exists a; elim (eqST_dec a a);
      [intuition|intro H; exfalso; apply H; unfold eqST; apply eqListRefl].

      destruct (IHs HEx) as [x [Hmem Hfx]]; exists x.
      elim (eqST_dec a x); intro; intuition.
  Qed.

  Lemma STadd_iff : forall (s : STt) (x y : STelt),
    STmem y (STadd x s) = true <-> (eqST x y \/ STmem y s = true).
  Proof. intros; simpl; elim (eqST_dec x y);intro;intuition. Qed.

End Set_of_tuple_of_positive.
