Require Import Recdef.
Require Import NArith.
Require Import Sorting.
Require Import GeoCoq.Tactics.Coinc.Permutations.
Require Import GeoCoq.Utils.general_tactics.
Require Import GeoCoq.Utils.sets.

Module SSWP := WPropertiesOn SetOfSetsOfPositiveOrderedType SS.

Module SSWEqP := WEqPropertiesOn SetOfSetsOfPositiveOrderedType SS.

Module Import PosSort := Sort PosOrder.

Section Coinc_refl.

Context {AR : Arity}.

Definition pick_variety_auxCP {m : nat} (s : SS.elt) (cp : cartesianPower positive (S (S m))) : bool.
Proof.
induction m.
exact ((S.mem (fst cp) s) && (S.mem (snd cp) s)).
exact ((S.mem (fst cp) s) && (IHm (tailCP cp))).
Defined.

Definition pick_variety_aux (s : SS.elt) (t : tST) := pick_variety_auxCP s t.

Lemma pick_variety_auxCP_forallT {m : nat} :
  forall s (cp : cartesianPower positive (S (S m))),
  pick_variety_auxCP s cp = true <-> (forall p, InCP p cp -> S.mem p s = true).
Proof.
induction m; intros s cp; [unfold InCP|]; simpl; split.

  {
  intro Hmem; apply andb_true_iff in Hmem; destruct Hmem as [Hmem1 Hmem2].
  intros p H; do 2 (try (elim H; clear H; intro; subst)); auto.
  }

  {
  intro H; apply andb_true_iff; split;
  [apply (H (fst cp))|apply (H (snd cp))]; auto.
  }

  {
  intro Hmem; apply andb_true_iff in Hmem; destruct Hmem as [Hmem1 Hmem2].
  intros p H; apply InCPOK in H; elim H; clear H; intro HIn; subst; simpl; auto.
  destruct (IHm s (tailCP cp)) as [H _]; apply H; auto.
  }

  {
  destruct (IHm s (tailCP cp)) as [_ H]; clear IHm; rename H into IHm.
  intro H; apply andb_true_iff; split;
  [apply (H (fst cp))|apply IHm; intros p HIn; apply H]; apply InCPOK; auto.
  }
Qed.

Lemma pick_variety_auxCP_existsF {m : nat} :
  forall s (cp : cartesianPower positive (S (S m))),
  pick_variety_auxCP s cp = false <-> (exists p, InCP p cp /\ S.mem p s = false).
Proof.
induction m; intros s cp; [unfold InCP|]; simpl; split.

  {
  intro H; apply andb_false_iff in H; elim H; clear H; intro H;
  [exists (fst cp)|exists (snd cp)]; auto.
  }

  {
  intro H; destruct H as [p [H Hmem]]; apply andb_false_iff.
  do 2 (try (elim H; clear H; intro H; subst)); intuition.
  }

  {
  intro H; apply andb_false_iff in H.
  destruct (IHm s (tailCP cp)) as [H' _]; clear IHm; rename H' into IHm.
  elim H; clear H; intro Hmem.

    {
    exists (fst cp); unfold InCP; simpl; auto.
    }

    {
    destruct (IHm Hmem) as [p [HIn Hmem']]; exists p;
    split; try apply InCPOK; auto.
    }
  }

  {
  destruct (IHm s (tailCP cp)) as [_ H]; clear IHm; rename H into IHm.
  intro H; destruct H as [p [HIn Hmem]]; apply InCPOK in HIn; apply andb_false_iff.
  elim HIn; clear HIn; intro HIn; subst; auto.
  right; apply IHm; exists p; auto.
  }
Qed.

Lemma proper_00 :
  forall s,
  Proper
  ((fun (t1 t2 : tST) =>
     eqST t1 t2) ==> eq)
  (fun t : tST => pick_variety_aux s t).
Proof.
unfold pick_variety_aux, eqST.
intros s t1 t2 HEq.
case_eq (pick_variety_auxCP s t1); intro Ht1.

  {
  destruct (pick_variety_auxCP_forallT s t1) as [H1 H2]; clear H2.
  assert (H := H1 Ht1); clear H1; clear Ht1; rename H into Ht1.
  destruct (pick_variety_auxCP_forallT s t2) as [H1 H2]; clear H1.
  rewrite H2; try reflexivity; clear H2; intros p HIn; apply Ht1.
  clear Ht1; apply InCPOCP; apply InCPOCP in HIn.
  assert (H : eqList (CPToList (OCP t1)) (CPToList (OCP t2))).
    {
    assert (Ht1 := eqListSortOCP t1).
    assert (Ht2 := eqListSortOCP t2).
    apply eqListTrans with (PosSort.sort (CPToList t1)); try assumption.
    apply eqListTrans with (PosSort.sort (CPToList t2)); try assumption.
    apply eqListSym; assumption.
    }
  clear HEq; rename H into HEq; apply eqListOK in HEq.
  unfold InCP in *; rewrite HEq; auto.
  }

  {
  destruct (pick_variety_auxCP_existsF s t1) as [H1 H2]; clear H2.
  assert (H := H1 Ht1); clear H1; clear Ht1; rename H into Ht1.
  destruct (pick_variety_auxCP_existsF s t2) as [H1 H2]; clear H1.
  rewrite H2; try reflexivity; clear H2.
  destruct Ht1 as [p [HIn Hmem]]; exists p; split; auto.
  apply InCPOCP; apply InCPOCP in HIn.
  assert (H : eqList (CPToList (OCP t1)) (CPToList (OCP t2))).
    {
    assert (Ht1 := eqListSortOCP t1).
    assert (Ht2 := eqListSortOCP t2).
    apply eqListTrans with (PosSort.sort (CPToList t1)); try assumption.
    apply eqListTrans with (PosSort.sort (CPToList t2)); try assumption.
    apply eqListSym; assumption.
    }
  clear HEq; rename H into HEq; apply eqListOK in HEq.
  unfold InCP in *; rewrite <- HEq; auto.
  }
Qed.

Definition pick_variety (s : SS.elt) (st : STt) :=
  STexists_ (fun t => pick_variety_aux s t) st.

Lemma proper_0 :
  Proper (S.Equal ==> eq ==> eq) pick_variety.
Proof.
intros x1 y1 HXY1.
intros x2 y2 HXY2.
rewrite HXY2; clear HXY2; clear x2.
unfold pick_variety; unfold pick_variety_aux.
unfold STexists_.

  induction y2; try reflexivity.

    rewrite IHy2; clear IHy2.
    assert (HEqMem : forall e, S.mem e x1 = S.mem e y1)
      by (intro; apply SWP.Dec.F.mem_m; intuition); clear HXY1.
    assert (HF : forall n a,
               (fix F (n : nat) : cartesianPower positive (S (S n)) -> bool :=
                 match n as n0 return (cartesianPower positive (S (S n0)) -> bool) with
                 | 0 => fun t0 : cartesianPower positive 2 => S.mem (fst t0) x1 && S.mem (snd t0) x1
                 | S n0 => fun t0 : cartesianPower positive (S (S (S n0))) =>
                             S.mem (headCP t0) x1 && F n0 (tailCP t0)
                 end) n a =
               (fix F (n : nat) : cartesianPower positive (S (S n)) -> bool :=
                  match n as n0 return (cartesianPower positive (S (S n0)) -> bool) with
                  | 0 => fun t0 : cartesianPower positive 2 => S.mem (fst t0) y1 && S.mem (snd t0) y1
                  | S n0 => fun t0 : cartesianPower positive (S (S (S n0))) =>
                              S.mem (headCP t0) y1 && F n0 (tailCP t0)
                  end) n a)
      by (induction n; try (intro; do 2 (rewrite HEqMem); reflexivity);
          intro ; rewrite HEqMem; rewrite IHn; reflexivity).
    unfold pick_variety_auxCP.
    rewrite HF; reflexivity.
Qed.

Lemma proper_1 : forall s1 st,
  Proper (S.Equal ==> eq)
  (fun s2 : SS.elt => pick_variety (S.inter s1 s2) st).
Proof.
intros s1 st.
intros x y HXY.
assert (HEqI : S.Equal (S.inter s1 x) (S.inter s1 y))
  by (apply SWP.inter_equal_2; assumption).
apply proper_0; auto.
Qed.

Definition exists_witness (f : SS.elt -> bool) (s : SS.t) : option SS.elt :=
  SS.choose (SS.filter f s).

Lemma exists_witness_ok : forall e f s,
  Proper (S.Equal ==> eq) f ->
  exists_witness f s = Some e -> SS.In e s.
Proof.
intros e f s HP H.
unfold exists_witness in H.
apply SSWEqP.MP.Dec.F.mem_2.
apply SSWEqP.choose_mem_1 in H.
rewrite SSWEqP.filter_mem in H; try assumption.
apply andb_true_iff in H.
induction H.
assumption.
Qed.

Definition pick_varieties_aux (s1 : SS.elt) (ss : SS.t) (st : STt)
                              : (option (SS.elt * SS.elt)) :=
  match ((exists_witness (fun s2 => let i := S.inter s1 s2 in
                                    pick_variety i st)) ss) with
    | None => None
    | Some s2 => Some(s1,s2)
  end.

Definition pick_varieties (ss : SS.t) (st : STt)
                          : (option (SS.elt * SS.elt)) :=
  match (exists_witness (fun s =>
                           match (pick_varieties_aux s (SS.remove s ss) st) with
                             | None => false
                             | _ => true
                           end) ss) with
    | None => None
    | Some s1 => pick_varieties_aux s1 (SS.remove s1 ss) st
  end.

Definition eqop (p1 p2 : option SS.elt) :=
  match p1,p2 with
    | None, None => True
    | Some s1, Some s2 => True
    | _, _ => False
  end.

Lemma proper_2 : forall (f1 f2 : SS.elt -> bool) (s1 s2 : SS.t),
  Proper (S.Equal ==> eq) f1 ->
  Proper (S.Equal ==> eq) f2 ->
  (forall x, f1 x = f2 x) ->
  SS.Equal s1 s2 ->
  eqop (exists_witness f1 s1) (exists_witness f2 s2).
Proof.
intros f1 f2 s1 s2.
intros H1 H2 H3 H4.
unfold eqop.
unfold exists_witness in *.
assert (SS.Equal (SS.filter f1 s1) (SS.filter f2 s2)) by (apply SSWEqP.MP.Dec.F.filter_ext; assumption).
case_eq (SS.choose (SS.filter f1 s1)); case_eq (SS.choose (SS.filter f2 s2)).

  intuition.

  intros HCN e HCS.
  apply SS.choose_spec1 in HCS.
  apply SS.choose_spec2 in HCN.
  rewrite H in HCS.
  apply SSWEqP.MP.empty_is_empty_1 in HCN.
  rewrite HCN in HCS.
  rewrite <- SSWEqP.MP.Dec.F.empty_iff.
  eassumption.

  intros e HCS HCN.
  apply SS.choose_spec1 in HCS.
  apply SS.choose_spec2 in HCN.
  rewrite H in HCN.
  apply SSWEqP.MP.empty_is_empty_1 in HCN.
  rewrite HCN in HCS.
  rewrite <- SSWEqP.MP.Dec.F.empty_iff.
  eassumption.

  intuition.
Qed.

Definition eqopp (p1 p2 : option (SS.elt * SS.elt)) :=
  match p1,p2 with
    | None, None => True
    | Some s1, Some s2 => True
    | _, _ => False
  end.

Lemma proper_3 : Proper (S.Equal ==> SS.Equal ==> eq ==> eqopp) pick_varieties_aux.
Proof.
intros x1 y1 HXY1.
intros x2 y2 HXY2.
intros x3 y3 HXY3.
unfold pick_varieties_aux.
rewrite HXY3.
assert (eqop (exists_witness (fun s2 : SS.elt => pick_variety (S.inter x1 s2) y3) x2)
             (exists_witness (fun s2 : SS.elt => pick_variety (S.inter y1 s2) y3) y2)).

  apply proper_2.

    apply proper_1.

    apply proper_1.

    intro; apply proper_0; try reflexivity.

      apply SWP.inter_equal_1; assumption.

      assumption.

case_eq (exists_witness (fun s2 : SS.elt => pick_variety (S.inter y1 s2) y3) y2);
case_eq (exists_witness (fun s2 : SS.elt => pick_variety (S.inter x1 s2) y3) x2).

  simpl; intuition.

  intros HCN e HCS.
  simpl in *.
  rewrite HCS in H; rewrite HCN in H.
  simpl in *.
  intuition.

  intros e HCS HCN.
  simpl in *.
  rewrite HCS in H; rewrite HCN in H.
  simpl in *.
  intuition.

  intuition.
Qed.

Lemma pick_varieties_ok_1 : forall s1 s2 ss st,
  pick_varieties ss st = Some(s1,s2) ->
  SS.In s1 ss.
Proof.
intros s1 s2 ss st H.
unfold pick_varieties in H.
case_eq (exists_witness (fun s : SS.elt => match pick_varieties_aux s
                          (SS.remove s ss) st with | Some _ => true | None => false end) ss).

  intros e1 HEW1.
  rewrite HEW1 in H.
  unfold pick_varieties_aux in H.
  case_eq (exists_witness (fun s2 : SS.elt => pick_variety (S.inter e1 s2) st) (SS.remove e1 ss)).

    intros e2 HEW2.
    rewrite HEW2 in H.
    assert (HEq1 : e1 = s1) by (injection H; intros; assumption).
    rewrite HEq1 in *.
    assert (HEq2 : e2 = s2) by (injection H; intros; assumption).
    rewrite HEq2 in *.
    apply exists_witness_ok with (fun s : SS.elt =>
      match pick_varieties_aux s (SS.remove s ss) st with | Some _ => true | None => false end).
    intros x y HXY.
    assert (SS.Equal (SS.remove x ss) (SS.remove y ss))
      by (apply SSWP.Dec.F.remove_m; try assumption; reflexivity).
    assert (eqopp (pick_varieties_aux x (SS.remove x ss) st) (pick_varieties_aux y (SS.remove y ss) st))
      by (apply proper_3; auto).
    case_eq (pick_varieties_aux x (SS.remove x ss) st);
      intros;
      case_eq (pick_varieties_aux y (SS.remove y ss) st);
      intros.

      reflexivity.

      rewrite H2 in H1; rewrite H3 in H1.
      unfold eqop in H1; simpl in H1.
      intuition.

      rewrite H2 in H1; rewrite H3 in H1.
      unfold eqop in H1; simpl in H1.
      intuition.

      reflexivity.

    assumption.

    intro HEW2.
    rewrite HEW2 in H.
    discriminate.

  intro HEW.
  rewrite HEW in H.
  discriminate.
Qed.

Lemma pick_varieties_ok_2 : forall s1 s2 ss st,
  pick_varieties ss st = Some(s1,s2) ->
  SS.In s2 (SS.remove s1 ss).
Proof.
intros s1 s2 ss st H.
unfold pick_varieties in H.
case_eq (exists_witness (fun s : SS.elt => match pick_varieties_aux s
                          (SS.remove s ss) st with | Some _ => true | None => false end) ss).

  intros e1 HEW1.
  rewrite HEW1 in H.
  unfold pick_varieties_aux in H.
  case_eq (exists_witness (fun s2 : SS.elt => pick_variety (S.inter e1 s2) st) (SS.remove e1 ss)).

    intros e2 HEW2.
    rewrite HEW2 in H.
    assert (HEq1 : e1 = s1) by (injection H; intros; assumption).
    rewrite HEq1 in *.
    assert (HEq2 : e2 = s2) by (injection H; intros; assumption).
    rewrite HEq2 in *.
    apply exists_witness_ok with (fun s2 : SS.elt => pick_variety (S.inter s1 s2) st).
    intros x y HXY.
    apply proper_1; assumption.
    assumption.

    intro HEW2.
    rewrite HEW2 in H.
    discriminate.

  intro HEW.
  rewrite HEW in H.
  discriminate.
Qed.

Function identify_varieties (ss : SS.t) (st : STt) {measure SS.cardinal ss}
                                 : SS.t :=
  let varieties := pick_varieties ss st in
    match varieties with
      |None => ss
      |Some (s1,s2) => let auxsetofsets := SS.remove s2 (SS.remove s1 ss) in
                       let auxset := S.union s1 s2 in
                       let newss := SS.add auxset auxsetofsets in
                         identify_varieties newss st
    end.
Proof.
intros.
assert (S(SS.cardinal (SS.remove s1 ss)) = SS.cardinal ss).
apply SSWP.remove_cardinal_1.
apply pick_varieties_ok_1 with s2 st.
assumption.
assert (S(S(SS.cardinal (SS.remove s2 (SS.remove s1 ss)))) = S(SS.cardinal (SS.remove s1 ss))).
apply eq_S.
apply SSWP.remove_cardinal_1.
apply pick_varieties_ok_2 with st.
assumption.
assert (HR1 : S(S(SS.cardinal (SS.remove s2 (SS.remove s1 ss)))) = SS.cardinal ss).
transitivity (S(SS.cardinal (SS.remove s1 ss))); assumption.
elim (SSWP.In_dec (S.union s1 s2) (SS.remove s2 (SS.remove s1 ss))); intro HDec.

  assert (HR2 : SS.cardinal (SS.add (S.union s1 s2) (SS.remove s2 (SS.remove s1 ss))) = SS.cardinal (SS.remove s2 (SS.remove s1 ss))).
  apply SSWP.add_cardinal_1; assumption.
  rewrite HR2.
  rewrite <- HR1.
  apply le_S;apply le_n.

  assert (HR2 : SS.cardinal (SS.add (S.union s1 s2) (SS.remove s2 (SS.remove s1 ss))) = S( SS.cardinal (SS.remove s2 (SS.remove s1 ss)))).
  apply SSWP.add_cardinal_2; assumption.
  rewrite HR2.
  rewrite <- HR1.
  apply le_n.
Defined.

Definition memCPAux m (cp : cartesianPower positive (S (S m))) (s : SS.elt) : bool.
Proof.
induction m.
exact (S.mem (fst cp) s && S.mem (snd cp) s).
exact (S.mem (fst cp) s && (IHm (snd cp))).
Defined.

Lemma memCPAuxHdTl : forall m cp s,
  memCPAux (S m) cp s = S.mem (fst cp) s && memCPAux m (tailCP cp) s.
Proof.
induction m; unfold memCPAux; unfold nat_rect; reflexivity.
Qed.

Lemma memCPAuxProperOK : forall m, Proper (eq ==> S.Equal==> eq) (memCPAux m).
Proof.
intros m cp1 cp2 Hcp s1 s2 Hs.
rewrite Hcp; clear Hcp; clear cp1; rename cp2 into cp.
unfold memCPAux.
assert (H : forall p, S.mem p s1 = S.mem p s2) by (intro p; apply SWP.Dec.F.mem_m; trivial).
induction m.
simpl; do 2 (rewrite H); reflexivity.
simpl; rewrite H; rewrite IHm; reflexivity.
Qed.

Lemma memCPAuxOK : forall m cp s e,
  memCPAux m cp s = true -> InCP e cp -> S.mem e s = true.
Proof.
induction m.

  unfold memCPAux.
  intros cp s e Hmem HIn.
  unfold InCP in HIn.
  simpl in *.
  rewrite andb_true_iff in Hmem.
  do 2 (elim HIn; clear HIn; intro HIn; try (subst; spliter; auto)).

  intros cp s e Hmem HIn.
  apply InCPOK in HIn.
  elim HIn; clear HIn; intro HIn.

    subst.
    simpl in Hmem.
    rewrite andb_true_iff in Hmem.
    spliter.
    auto.

    apply IHm with (tailCP cp); try assumption.
    simpl in Hmem.
    rewrite andb_true_iff in Hmem.
    spliter.
    assumption.
Qed.

Lemma memMemCPAuxOK : forall m cp s,
  (forall e, InCP e cp -> S.mem e s = true) -> memCPAux m cp s = true.
Proof.
induction m.

  unfold memCPAux.
  simpl.
  intros cp s H.
  rewrite andb_true_iff.
  assert (HIn1 : InCP (fst cp) cp) by (unfold InCP; simpl; auto).
  assert (HIn2 : InCP (snd cp) cp) by (unfold InCP; simpl; auto).
  split; apply H; assumption.

  intros cp s H.
  rewrite memCPAuxHdTl.
  rewrite andb_true_iff.
  assert (HIn : InCP (fst cp) cp) by (unfold InCP; simpl; auto).
  split; try (apply H; assumption); clear HIn.
  apply IHm.
  intros e HIn.
  apply H.
  apply InCPOK.
  right.
  assumption.
Qed.

Lemma memCPAuxTlOK : forall m cp s,
  memCPAux (S m) cp s = true ->
  memCPAux m (tailCP cp) s = true.
Proof.
intros m cp s Hmemcp.
apply memMemCPAuxOK.
intros e HIn.
apply memCPAuxOK with (S m) cp; try assumption.
apply InCPOK.
right; assumption.
Qed.

Definition memCP (cp : cartesianPower positive (S (S (S n)))) (s : SS.elt) := memCPAux (S n) cp s.

Lemma memCPProper : Proper (eq ==> S.Equal==> eq) memCP.
Proof. apply memCPAuxProperOK. Qed.

Lemma memMemCPOK : forall cp s,
  (forall e, InCP e cp -> S.mem e s = true) -> memCP cp s = true.
Proof. apply memMemCPAuxOK. Qed.

Lemma memCPConsHd : forall p s x,
  S.mem p s = true ->
  memCPAux n x s = true ->
  memCP (consHeadCP p x) s = true.
Proof.
intros p s x Hmem Hmemcp.
apply memMemCPOK.
intros e HIn.
apply InCPOK in HIn.
simpl in HIn.
elim HIn; clear HIn; intro HIn.

  subst; assumption.

  apply memCPAuxOK with n x; assumption.
Qed.

Definition test_coinc (ss : SS.t) (st : STt) (cp : cartesianPower positive (S (S (S n)))) : bool :=
  let newss := identify_varieties ss st  in
    SS.exists_ (fun s => memCP cp s) newss.

Lemma pick_variety_aux_memCPAux1 : forall s1 s2 m (cp : cartesianPower positive (S (S m))),
  pick_variety_auxCP (S.inter s1 s2) cp = true ->
  memCPAux m cp s1 = true.
Proof.
intros s1 s2 m cp.
induction m; simpl; do 2 (rewrite andb_true_iff); intro Hhtspa.

  do 2 (rewrite SWP.FM.inter_b in Hhtspa).
  do 2 (rewrite andb_true_iff in Hhtspa).
  tauto.

  destruct Hhtspa as [Hmem Hhtspa].
  rewrite SWP.FM.inter_b in Hmem.
  rewrite andb_true_iff in Hmem.
  split; try (spliter; assumption).
  apply IHm; assumption.
Qed.

Lemma pick_variety_aux_memCPAux2 : forall s1 s2 m (cp : cartesianPower positive (S (S m))),
  pick_variety_auxCP (S.inter s1 s2) cp = true ->
  memCPAux m cp s2 = true.
Proof.
intros s1 s2 m cp.
induction m; simpl; do 2 (rewrite andb_true_iff); intro Hhtspa.

  do 2 (rewrite SWP.FM.inter_b in Hhtspa).
  do 2 (rewrite andb_true_iff in Hhtspa).
  tauto.

  destruct Hhtspa as [Hmem Hhtspa].
  rewrite SWP.FM.inter_b in Hmem.
  rewrite andb_true_iff in Hmem.
  split; try (spliter; assumption).
  apply IHm; assumption.
Qed.

Definition interp_CP {m : nat} (cp : cartesianPower positive (S m)) (interp: positive -> COINCpoint) : cartesianPower COINCpoint (S m).
Proof.
induction m.
exact (interp cp).
clear IHm.
induction m.
split.
exact (interp (headCP cp)).
exact (interp (tailCP cp)).
split.
exact (interp (headCP cp)).
exact (IHm (tailCP cp)).
Defined.

Lemma interp_CPHdOK {m : nat} : forall (cp : cartesianPower positive (S m)) interp,
  interp_CP (headCPbis cp) interp = headCP (interp_CP cp interp).
Proof.
induction m.

  unfold interp_CP; unfold nat_rect; simpl; reflexivity.

  induction m; unfold interp_CP; unfold nat_rect; simpl; reflexivity.
Qed.

Lemma interp_CPTlOK {m : nat} : forall (cp : cartesianPower positive (S (S m))) interp,
  interp_CP (tailCP cp) interp = tailCP (interp_CP cp interp).
Proof.
induction m; unfold interp_CP; unfold nat_rect; simpl; reflexivity.
Qed.

Lemma interp_CPOK {m : nat} : forall (cp : cartesianPower positive (S m)) (interp: positive -> COINCpoint),
  CPToList (interp_CP cp interp) = map interp (CPToList cp).
Proof.
induction m; intros cp interp.

  simpl.
  reflexivity.

  induction m; try (clear IHm0).

    simpl.
    reflexivity.

    rewrite CPToListOK.
    rewrite <- interp_CPHdOK.
    rewrite <- interp_CPTlOK.
    rewrite IHm.
    simpl.
    reflexivity.
Qed.

Context {COP : Coinc_predicates AR}.

Definition ss_ok (ss : SS.t) (interp: positive -> COINCpoint) :=
  forall s, SS.mem s ss = true ->
  forall cp, memCP cp s = true ->
    app coinc (interp_CP cp interp).

Lemma consHdInterpOK : forall (cp : cartesianPower positive 1) (x : tST) interp,
  consHeadCP (interp_CP cp interp) (interp_CP x interp) = interp_CP (consHeadCP cp x) interp.
Proof.
intros cp x interp.
apply CP_ind; simpl; reflexivity.
Qed.

Lemma ss_ok_inter_ok1 : forall ss interp s1 s2 x (p : cartesianPower positive 1),
  ss_ok ss interp ->
  SS.In s1 ss ->
  pick_variety_aux (S.inter s1 s2) x = true ->
  S.mem p s1 = true ->
  app_1_n coinc (interp_CP p interp) (interp_CP x interp).
Proof.
intros ss interp s1 s2 x p HSSOK HIn HInter Hmem.
apply app_app_1_n with (consHeadCP (interp_CP p interp) (interp_CP x interp)); try (simpl; reflexivity).
assert (Hmemcp : memCPAux n x s1 = true) by (apply pick_variety_aux_memCPAux1 with s2; assumption).
unfold ss_ok in HSSOK.
rewrite consHdInterpOK.
apply SSWEqP.MP.Dec.F.mem_1 in HIn.
apply HSSOK with s1; try assumption.
apply memCPConsHd; assumption.
Qed.

Lemma ss_ok_inter_ok2 : forall ss interp s1 s2 x (p : cartesianPower positive 1),
  ss_ok ss interp ->
  SS.In s2 ss ->
  pick_variety_aux (S.inter s1 s2) x = true ->
  S.mem p s2 = true ->
  app_1_n coinc (interp_CP p interp) (interp_CP x interp).
Proof.
intros ss interp s1 s2 x p HSSOK HIn HInter Hmem.
apply app_app_1_n with (consHeadCP (interp_CP p interp) (interp_CP x interp)); try (simpl; reflexivity).
assert (Hmemcp : memCPAux n x s2 = true) by (apply pick_variety_aux_memCPAux2 with s1; assumption).
unfold ss_ok in HSSOK.
rewrite consHdInterpOK.
apply SSWEqP.MP.Dec.F.mem_1 in HIn.
apply HSSOK with s2; try assumption.
apply memCPConsHd; assumption.
Qed.

Lemma mca_pick_variety_aux_pca : forall m cp s1 s2 ss x interp,
  ss_ok ss interp ->
  SS.In s1 ss ->
  SS.In s2 ss ->
  memCPAux (S m) cp (S.union s1 s2) = true ->
  pick_variety_aux (S.inter s1 s2) x = true ->
  pred_conj_aux coinc (S (S m)) (interp_CP cp interp) (interp_CP x interp).
Proof.
induction m; intros cp s1 s2 ss x interp HSSOK HIn1 HIn2 Hmemcp Hhtspa.

  unfold pred_conj_aux.
  unfold nat_rect.
  split.

    assert (HIn : InCP (headCP cp) cp) by (unfold InCP; simpl; auto).
    assert (HElim : S.mem (headCP cp) (S.union s1 s2) = true) by (apply memCPAuxOK with 1 cp; assumption).
    rewrite SWP.FM.union_b in HElim.
    apply orb_true_iff in HElim.
    elim HElim; clear HElim; intro HElim.

      apply ss_ok_inter_ok1 with ss s1 s2; assumption.

      apply ss_ok_inter_ok2 with ss s1 s2; assumption.

    split.

      assert (HIn : InCP (headCP (tailCP cp)) cp) by (unfold InCP; simpl; auto).
      assert (HElim : S.mem (headCP (tailCP cp)) (S.union s1 s2) = true) by (apply memCPAuxOK with 1 cp; assumption).
      rewrite SWP.FM.union_b in HElim.
      apply orb_true_iff in HElim.
      elim HElim; clear HElim; intro HElim.

        apply ss_ok_inter_ok1 with ss s1 s2; assumption.

        apply ss_ok_inter_ok2 with ss s1 s2; assumption.

      assert (HIn : InCP (tailCP (tailCP cp)) cp) by (unfold InCP; simpl; auto).
      assert (HElim : S.mem (tailCP (tailCP cp)) (S.union s1 s2) = true) by (apply memCPAuxOK with 1 cp; assumption).
      rewrite SWP.FM.union_b in HElim.
      apply orb_true_iff in HElim.
      elim HElim; clear HElim; intro HElim.

        apply ss_ok_inter_ok1 with ss s1 s2; assumption.

        apply ss_ok_inter_ok2 with ss s1 s2; assumption.

  rewrite pcaHdTl.
  split.

    assert (HIn : InCP (headCP cp) cp) by (unfold InCP; simpl; auto).
    assert (HElim : S.mem (headCP cp) (S.union s1 s2) = true) by (apply memCPAuxOK with (S (S m)) cp; assumption).
    rewrite SWP.FM.union_b in HElim.
    apply orb_true_iff in HElim.
    elim HElim; clear HElim; intro HElim.

      apply ss_ok_inter_ok1 with ss s1 s2; assumption.

      apply ss_ok_inter_ok2 with ss s1 s2; assumption.

    rewrite <- interp_CPTlOK.
    apply IHm with s1 s2 ss; try assumption.
    apply memCPAuxTlOK.
    assumption.
Qed.

Definition st_ok (st : STt) (interp: positive -> COINCpoint) :=
  forall t, STmem t st = true -> app wd (interp_CP t interp).

Context {COT : Coinc_theory AR COP}.

Lemma identify_varieties_ok : forall ss st interp,
  ss_ok ss interp -> st_ok st interp ->
  ss_ok (identify_varieties ss st) interp.
Proof.
intros ss st interp HSS HST.
apply (let P interp ss st newss :=
       ss_ok ss interp -> st_ok st interp -> ss_ok newss interp in
         identify_varieties_ind (P interp)); try assumption.

  intros.
  assumption.

  clear HSS; clear HST; clear ss; clear st.
  intros ss st varieties s1 s2 Hs1s2 auxsetofsets auxset newss H HSS HST.
  assert (Hs1 := Hs1s2).
  assert (Hs2 := Hs1s2).
  apply pick_varieties_ok_1 in Hs1.
  apply pick_varieties_ok_2 in Hs2.
  apply SSWEqP.MP.Dec.F.remove_3 in Hs2.
  apply H; try assumption; clear H.
  intros s Hmem cp Hmemcp.
  unfold newss in Hmem; clear newss.
  elim (SS.E.eq_dec auxset s); intro HEq.

    assert (HEq' : memCP cp auxset = memCP cp s) by (apply memCPProper; trivial).
    rewrite <- HEq in *; rewrite <- HEq' in *; clear HEq; clear HEq'; clear s.
    unfold varieties in Hs1s2; clear varieties.
    unfold pick_varieties in Hs1s2.
    case_eq (exists_witness
            (fun s : SS.elt =>
             match pick_varieties_aux s (SS.remove s ss) st with
             | Some _ => true
             | None => false
             end) ss); try (intro HEW; rewrite HEW in *; discriminate).
    intros e1 HEW; rewrite HEW in *; clear HEW.
    unfold pick_varieties_aux in *.
    case_eq (exists_witness
            (fun s2 : SS.elt => pick_variety (S.inter e1 s2) st)
            (SS.remove e1 ss)); try (intro HEW; rewrite HEW in *; discriminate).
    intros e2 HEW; rewrite HEW in *.
    injection Hs1s2; intros He2s2 He1s1.
    rewrite He2s2 in *; rewrite He1s1 in *; clear He2s2; clear He1s1; clear Hs1s2; clear e2; clear e1.
    case_eq (pick_variety (S.inter s1 s2) st).

      clear HEW; intro HEW.
      unfold pick_variety in HEW.
      apply STexists_mem_4 in HEW;
        try (intros x y Hxy; destruct Hxy as [Hxyfst Hxysnd]; rewrite Hxyfst; rewrite Hxysnd; reflexivity); try (apply proper_00).
      destruct HEW as [x [HmemST1 HmemST2]].
      apply HST in HmemST1.
      apply coinc_n with (interp_CP x interp); try assumption.
      unfold pred_conj.
      apply mca_pick_variety_aux_pca with s1 s2 ss; assumption.

      intro HEW2; unfold exists_witness in *; apply SS.choose_spec1 in HEW.
      apply SSWEqP.MP.Dec.F.filter_2 in HEW; try apply proper_1.
      rewrite HEW2 in *; discriminate.

    rewrite SSWP.Dec.F.add_neq_b in Hmem; try assumption.
    apply HSS with s.
    unfold auxsetofsets in *.
    apply SSWEqP.MP.Dec.F.mem_2 in Hmem.
    do 2 (apply SSWEqP.MP.Dec.F.remove_3 in Hmem).
    apply SSWEqP.MP.Dec.F.mem_1.
    assumption.
    assumption.
Qed.

Lemma test_coinc_ok : forall ss st interp cp,
  ss_ok ss interp -> st_ok st interp ->
  test_coinc ss st cp = true ->
  app coinc (interp_CP cp interp).
Proof.
intros ss st interp cp HSS HST HTC.
unfold test_coinc in *.
assert (HSS2 : ss_ok (identify_varieties ss st) interp)
  by (apply identify_varieties_ok; assumption).

unfold ss_ok in HSS2.
apply SSWEqP.MP.Dec.F.exists_2 in HTC.
unfold SS.Exists in HTC.
destruct HTC as [s [HIn Hmem]].
apply HSS2 with s.
apply SSWEqP.MP.Dec.F.mem_1.
assumption.
assumption.

intros x y Hxy.
apply memCPProper; trivial.
Qed.

Lemma ss_ok_empty : forall interp,
  ss_ok SS.empty interp.
Proof.
intros interp ss Hmem1 cp Hmem2.
rewrite SSWEqP.MP.Dec.F.empty_b in Hmem1.
discriminate.
Qed.

Lemma st_ok_empty : forall interp,
  st_ok STempty interp.
Proof.
intros.
unfold st_ok.
intros t Ht.
rewrite STempty_b in Ht.
discriminate.
Qed.

Definition CPToSS {m:nat} (cp : cartesianPower positive m) : SS.elt.
Proof.
induction m.
exact S.empty.
induction m.
exact (S.add cp S.empty).
exact (S.add (headCP cp) (IHm (tailCP cp))).
Defined.

Lemma CPToSSHdTl {m:nat} : forall (cp : cartesianPower positive (S (S m))),
  CPToSS cp = S.add (headCP cp) (CPToSS (tailCP cp)).
Proof. simpl; reflexivity. Qed.

Lemma memCPToSSOK {m : nat} : forall e (cp : cartesianPower positive (S m)),
  S.mem e (CPToSS cp) = true ->
  InCP e cp.
Proof.
induction m; intros e cp Hmem.

  unfold InCP.
  simpl in *.
  left.
  rewrite <- SWP.singleton_equal_add in Hmem.
  apply SWP.Dec.F.mem_2 in Hmem.
  apply SWP.Dec.F.singleton_1.
  assumption.

  apply InCPOK.
  rewrite CPToSSHdTl in Hmem.
  rewrite SWP.Dec.F.add_b in Hmem.
  rewrite <- SWP.Dec.F.singleton_b in Hmem.
  apply orb_true_iff in Hmem.
  elim Hmem; clear Hmem; intro Hmem.

    left.
    apply SWP.Dec.F.mem_2 in Hmem.
    apply SWP.Dec.F.singleton_1 in Hmem.
    intuition.

    right.
    apply IHm.
    assumption.
Qed.

Lemma CPToSSOKAux {m m' : nat} :
  forall (cp : cartesianPower positive (S (S m))) (cp' : cartesianPower positive (S (S m'))) e s,
  S.Equal (CPToSS cp) s ->
  memCPAux m' cp' s = true ->
  InCP e cp' ->
  InCP e cp.
Proof.
induction m'.

  induction m; intros cp cp' e s HEq Hmem HIn.

    unfold InCP in *.
    simpl in *.
    apply andb_true_iff in Hmem.
    destruct Hmem as [Hmem1 Hmem2].
    assert (HmemEq : S.mem (fst cp') (S.add (fst cp) (S.add (snd cp) S.empty)) = S.mem (fst cp') s)
      by (apply SWP.FM.mem_m; trivial); simpl in *;rewrite <- HmemEq in Hmem1; clear HmemEq.
    assert (HmemEq : S.mem (snd cp') (S.add (fst cp) (S.add (snd cp) S.empty)) = S.mem (snd cp') s)
      by (apply SWP.FM.mem_m; trivial); simpl in *;rewrite <- HmemEq in Hmem2; clear HmemEq; clear HEq.
    rewrite SWP.Dec.F.add_b in Hmem1.
    rewrite <- SWP.Dec.F.singleton_b in Hmem1.
    assert (HmemEq : S.mem (fst cp') (S.add (snd cp) S.empty) = S.mem (fst cp') (S.singleton (snd cp)))
      by (apply SWP.FM.mem_m; trivial; apply SWP.singleton_equal_add); simpl in *;rewrite HmemEq in Hmem1; clear HmemEq.
    rewrite SWP.Dec.F.add_b in Hmem2.
    rewrite <- SWP.Dec.F.singleton_b in Hmem2.
    assert (HmemEq : S.mem (snd cp') (S.add (snd cp) S.empty) = S.mem (snd cp') (S.singleton (snd cp)))
      by (apply SWP.FM.mem_m; trivial; apply SWP.singleton_equal_add); simpl in *;rewrite HmemEq in Hmem2; clear HmemEq.
    apply orb_true_iff in Hmem1.
    apply orb_true_iff in Hmem2.
    elim HIn; clear HIn; intro HIn.

      subst.
      elim Hmem1; clear Hmem1; clear Hmem2; intro HEq; apply SWP.Dec.F.mem_2 in HEq;
      apply SWP.Dec.F.singleton_1 in HEq; auto.

      elim HIn; clear HIn; intro HIn.

        subst.
        elim Hmem2; clear Hmem1; clear Hmem2; intro HEq; apply SWP.Dec.F.mem_2 in HEq;
        apply SWP.Dec.F.singleton_1 in HEq; auto.

        intuition.

    elim HIn; clear HIn; intro HIn.

      assert (HmemEq : memCPAux 0 cp' (CPToSS cp) = memCPAux 0 cp' s) by (apply memCPAuxProperOK; trivial);
      rewrite <- HmemEq in Hmem; clear HmemEq; clear HEq; clear IHm.
      subst.
      assert (HIn : InCP (headCP cp') cp') by (unfold InCP; simpl; auto).
      assert (H := memCPAuxOK 0 cp' (CPToSS cp) (headCP cp') Hmem HIn); clear HIn; clear Hmem; rename H into Hmem.
      apply memCPToSSOK.
      assumption.

      unfold InCP in HIn.
      simpl in HIn.
      elim HIn; clear HIn; intro HIn.

        assert (HmemEq : memCPAux 0 cp' (CPToSS cp) = memCPAux 0 cp' s) by (apply memCPAuxProperOK; trivial);
        rewrite <- HmemEq in Hmem; clear HmemEq; clear HEq; clear IHm.
        subst.
        assert (HIn : InCP (tailCP cp') cp') by (unfold InCP; simpl; auto).
        assert (H := memCPAuxOK 0 cp' (CPToSS cp) (tailCP cp') Hmem HIn); clear HIn; clear Hmem; rename H into Hmem.
        apply memCPToSSOK.
        assumption.

        intuition.

  intros cp cp' e s HEq Hmem HIn.
  apply InCPOK in HIn.
  elim HIn; clear HIn; intro HIn.

    subst.
    assert (HmemEq : memCPAux (S m') cp' (CPToSS cp) = memCPAux (S m') cp' s) by (apply memCPAuxProperOK; trivial);
    rewrite <- HmemEq in Hmem; clear HmemEq; clear HEq; clear IHm'.
    assert (HIn : InCP (headCP cp') cp') by (unfold InCP; simpl; auto).
    assert (H := memCPAuxOK (S m') cp' (CPToSS cp) (headCP cp') Hmem HIn); clear HIn; clear Hmem; rename H into Hmem.
    apply memCPToSSOK.
    assumption.

    apply IHm' with (tailCP cp') s; try assumption.
    apply memCPAuxTlOK; assumption.
Qed.

Lemma CPToSSOK : forall (cp cp' : cartesianPower positive (S (S (S n)))) s,
  S.Equal (CPToSS cp) s ->
  memCP cp' s = true ->
  incl (CPToList cp') (CPToList cp).
Proof.
unfold incl.
intros cp cp' s HEq Hmem e HIn.
assert (H := CPToSSOKAux cp cp' e s HEq Hmem).
unfold InCP in H.
apply H; assumption.
Qed.

Lemma CoappDupPerm {m : nat} :
  forall (cp : cartesianPower positive m),
  ~ List.NoDup (CPToList cp) ->
  exists e, exists l, Permutation.Permutation (CPToList (ListToCP (e :: e :: l) e)) (CPToList cp).
Proof.
intros cp HDup.
apply NotNoDupDup in HDup; try apply Pos.eq_dec.
destruct HDup as [e [l1 [l2 [HEq HIn]]]].
apply in_split in HIn.
destruct HIn as [l3 [l4 HEq']].
assert (HPerm := Permutation.Permutation_middle l1 l2 e).
rewrite <- HEq in HPerm; clear HEq.
rewrite HEq' in HPerm; clear HEq'; clear l1; clear l2; rename l3 into l1; rename l4 into l2.
assert (HPerm' := Permutation.Permutation_middle l1 l2 e).
apply (Permutation.perm_skip e) in HPerm'.
assert (HPerm'' := Permutation.perm_trans HPerm' HPerm); clear HPerm; clear HPerm'; rename HPerm'' into HPerm.
rewrite <- CPLOK with (e :: e :: l1 ++ l2) e in HPerm.
exists e; exists (l1 ++ l2); assumption.
Qed.

Lemma CoappDupAux {m : nat} :
  forall (cp : cartesianPower positive (S (S (S m)))),
  ~ List.NoDup (CPToList cp) ->
  exists e, exists (l : list positive), exists m', exists (cp' : cartesianPower positive (S (S (S m')))),
  Permutation.Permutation (CPToList cp') (CPToList cp) /\ headCP cp' = e /\ headCP (tailCP cp') = e.
Proof.
intros cp H.
apply CoappDupPerm in H.
destruct H as [e[l HPerm]].
assert (Hl := Permutation.Permutation_length HPerm).
rewrite CPLOK in Hl.
rewrite <- lengthOfCPToList in Hl.
induction l; try (simpl in Hl; discriminate); clear IHl.
exists e; exists (a :: l); exists (length l); exists (ListToCP (e :: e :: a :: l) e).
split; try assumption.
simpl.
split; reflexivity.
Qed.

Lemma CoappDup : forall cp interp,
  ~ List.NoDup (CPToList cp) ->
  app coinc (interp_CP cp interp).
Proof.
intros cp interp H.
apply CoappDupAux in H.
destruct H as [e [l [m' [cp' [HPerm [Hfst Hsnd]]]]]].
assert (Hmn := Permutation.Permutation_length HPerm).
apply Permutation.Permutation_map with positive COINCpoint interp (CPToList cp') (CPToList cp) in HPerm.
do 2 (rewrite <- interp_CPOK in HPerm).
do 2 (rewrite <- lengthOfCPToList in Hmn).
do 3 (apply eq_add_S in Hmn).
subst.
apply PermCoincOK with (interp_CP cp' interp); try assumption; clear HPerm.
apply app_2_n_app with (interp (headCP cp')) (interp (headCP (tailCP cp'))) (interp_CP (tailCP (tailCP cp')) interp).

  rewrite Hsnd.
  apply coinc_bd.

  rewrite <- interp_CPHdOK.
  reflexivity.

  rewrite <- interp_CPTlOK.
  rewrite <- interp_CPHdOK.
  reflexivity.

  do 2 (rewrite <- interp_CPTlOK).
  reflexivity.
Qed.

Lemma collect_coincs :
forall cp ss interp,
  app coinc (interp_CP cp interp) ->
  ss_ok ss interp -> ss_ok (SS.add (CPToSS cp) ss) interp.
Proof.
intros cp ss interp HCoapp HSS.
unfold ss_ok.
intros s Hs.
intros cp' Hmem.
apply SSWEqP.MP.Dec.F.mem_2 in Hs.
apply SSWEqP.MP.Dec.F.add_iff in Hs.
elim Hs; clear Hs; intro Hs.

  assert (HDup := NoDup_dec (CPToList cp') Pos.eq_dec).
  elim HDup; clear HDup; intro HDup.

    assert (Hincl := CPToSSOK cp cp' s Hs Hmem).
    assert (Hlength : length (CPToList cp') = length (CPToList cp)) by (do 2 (rewrite <- lengthOfCPToList); reflexivity).
    assert (HPerm := NoDupOK (CPToList cp') (CPToList cp) Hincl Hlength HDup).
    apply Permutation.Permutation_map with positive COINCpoint interp (CPToList cp') (CPToList cp) in HPerm.
    do 2 (rewrite <- interp_CPOK in HPerm); clear HDup; clear Hincl; clear Hlength.
    apply Permutation.Permutation_sym in HPerm.
    apply PermCoincOK with (interp_CP cp interp); assumption.

    apply CoappDup; assumption.

  unfold ss_ok in HSS.
  apply HSS with s; try assumption.
  apply SSWEqP.MP.Dec.F.mem_1; assumption.
Qed.

Lemma collect_wds :
  forall cp st interp,
  app wd (interp_CP cp interp) ->
  st_ok st interp -> st_ok (STadd cp st) interp.
Proof.
intros cp st interp HWd HST.
unfold st_ok.
intros cp' Hmem.
apply STadd_iff in Hmem.
elim Hmem; clear Hmem; intro Hmem; [|apply HST; apply Hmem].
assert (Hcp := sets.PosSort.Permuted_sort (CPToList cp)).
assert (Hcp' := sets.PosSort.Permuted_sort (CPToList cp')).
apply eqListOK in Hmem.
rewrite Hmem in Hcp.
apply PermWdOK with (interp_CP cp interp); try assumption.
do 2 (rewrite interp_CPOK).
apply Permutation.Permutation_map.
transitivity (PosSort.sort (CPToList cp')); try assumption.
apply Permutation.Permutation_sym; assumption.
Qed.

Definition list_assoc_inv :=
  (fix list_assoc_inv_rec (A:Type) (B:Set)
                          (eq_dec:forall e1 e2:B, {e1 = e2} + {e1 <> e2})
                          (lst : list (prodT A B)) {struct lst} : B -> A -> A :=
  fun (key:B) (default:A) =>
    match lst with
      | nil => default
      | cons (pairT v e) l =>
        match eq_dec e key with
          | left _ => v
          | right _ => list_assoc_inv_rec A B eq_dec l key default
        end
    end).

Lemma positive_dec : forall (p1 p2:positive), {p1=p2}+{~p1=p2}.
Proof.
decide equality.
Defined.

Definition interp (lvar : list (COINCpoint * positive)) (Default : COINCpoint) : positive -> COINCpoint := 
  fun p => list_assoc_inv COINCpoint positive positive_dec lvar p Default.

End Coinc_refl.

Ltac add_to_distinct_list x xs :=
  match xs with
    | nil     => constr:(x::xs)
    | x::_    => fail 1
    | ?y::?ys => let zs := add_to_distinct_list x ys in constr:(y::zs)
  end.

Ltac collect_points_list Tpoint xs :=
  match goal with
    | N : Tpoint |- _ => let ys := add_to_distinct_list N xs in
                           collect_points_list Tpoint ys
    | _               => xs
  end.

Ltac collect_points Tpoint := collect_points_list Tpoint (@nil Tpoint).

Ltac number_aux Tpoint lvar cpt :=
  match constr:(lvar) with
    | nil          => constr:(@nil (prodT Tpoint positive))
    | cons ?H ?T => let scpt := eval vm_compute in (Pos.succ cpt) in
                    let lvar2 := number_aux Tpoint T scpt in
                      constr:(cons (@pairT  Tpoint positive H cpt) lvar2)
  end.

Ltac number Tpoint lvar := number_aux Tpoint lvar (1%positive).

Ltac build_numbered_points_list Tpoint := let lvar := collect_points Tpoint in number Tpoint lvar.

Ltac List_assoc Tpoint elt lst :=
  match constr:(lst) with
    | nil => fail
    | (cons (@pairT Tpoint positive ?X1 ?X2) ?X3) =>
      match constr:(elt = X1) with
        | (?X1 = ?X1) => constr:(X2)
        | _ => List_assoc Tpoint elt X3
      end
  end.

Definition Tagged P : Prop := P.

Lemma PropToTagged : forall P : Prop, P -> Tagged P.
Proof. trivial. Qed.