Require Export List.

Definition all_equiv (l: list Prop) :=
  forall x y, In x l -> In y l -> (x <-> y).

Lemma all_equiv_chara : forall l,
  all_equiv l <-> forall x y, In x l -> In y l -> x -> y.
Proof.
  unfold all_equiv.
  intro l; split; [intros He x y Hx Hy; rewrite (He x y); auto|].
  intros Himp x y Hxl Hyl.
  split; apply Himp; assumption.
Qed.

Definition all_equiv'_aux (l: list Prop) : Prop.
induction l; [exact True|].
induction l; [exact True|].
exact ((a -> a0) /\ IHl).
Defined.

Lemma all_equiv'_auxP : forall l n1 n2 d1 d2,
  l <> nil -> all_equiv'_aux l ->
  n1 < length l -> n2 < length l -> n1 <= n2 ->
  nth n1 l d1 -> nth n2 l d2.
Proof.
intro l; elim l; [intros ? ? ? ? H; exfalso; apply H; auto|
                  clear l; intros a l _; revert a].
elim l; [intro a|clear l; intros b l IHl a]; intros n1 n2 d1 d2 _ H Hn1 Hn2 Hn.

  {
  simpl in Hn1, Hn2.
  apply PeanoNat.Nat.lt_1_r in Hn1; rewrite Hn1.
  apply PeanoNat.Nat.lt_1_r in Hn2; rewrite Hn2; simpl; auto.
  }

  {
  destruct H as [HI H]. revert dependent n2. revert dependent n1; intro n1.
  elim n1; [|clear n1; intros n1 IHn1]; intro Hn1.

    {
    intro n2; elim n2; [simpl; auto|clear n2; intros n2 IHn2 Hn2 _ Ha].
    simpl in Ha; apply HI in Ha; apply IHl with 0 d1; auto; simpl in *;
    [discriminate|apply PeanoNat.Nat.lt_0_succ|
     apply Lt.lt_S_n; auto|apply le_0_n].
    }

    {
    intro n2; elim n2;
    [intros _ HF; apply PeanoNat.Nat.nle_succ_0 in HF; intuition|
     clear n2; intros n2 IHn2 Hn2 HLe H'].
    assert (Hnth : forall n (l : list Prop) a d,
                     nth (S n) (a :: l) d = nth n l d)
      by (intro n; induction n; simpl; auto).
    rewrite Hnth; rewrite Hnth in H'; clear Hnth; apply IHl with n1 d1; auto;
    [discriminate|simpl in Hn1|simpl in Hn2|apply Le.le_S_n]; auto;
    apply Lt.lt_S_n; auto.
    }
  }
Qed.

Definition all_equiv' (l: list Prop) : Prop.
induction l; [exact True|].
exact ((last l a -> a) /\ all_equiv'_aux (a::l)).
Defined.
(*
Definition all_equiv' (l: list Prop) : Prop.
Proof.
induction l; [exact True|].
induction l; [exact True|].
exact ((a <-> a0) /\ IHl).
Defined.

Lemma all_equiv_equiv : forall l, all_equiv l <-> all_equiv' l.
Proof.
assert (IH : forall a a0 l,
  all_equiv' (a::a0::l) <-> (a <-> a0) /\ all_equiv' (a0::l))
  by (intros a a0 l; induction l; simpl; tauto).
unfold all_equiv; intro l; induction l; [simpl; tauto|].
induction l; [simpl|clear IHl0; rewrite IH; split]; clear IH.

  {
  split; [auto|intros _ x y Hx Hy].
  elim Hx; [clear Hx; intro Hx; rewrite <- Hx|intuition].
  elim Hy; [clear Hy; intro Hy; rewrite <- Hy|]; intuition.
  }

  {
  intro H; split; [apply H; simpl; tauto|].
  apply IHl; intros x y Hx Hy; apply H; right; assumption.
  }

  {
  intros [H Hl] x y [Ha|Hx] [Ha'|Hy];
  try (rewrite <- Ha; clear Ha);
  try (rewrite <- Ha'; clear Ha'); [tauto| | |];
  try (cut (a0 <-> y); [try tauto|apply IHl; try assumption; left; reflexivity]);
  try (cut (a0 <-> x); [tauto|apply IHl; try assumption; left; reflexivity]).
  }
Qed.
*)

Lemma all_equiv__equiv : forall l, all_equiv l <-> all_equiv' l.
Proof.
intro l; split.

  {
  elim l; [simpl; auto|clear l; intros a l _; revert a].
  elim l; [simpl; intros; split; auto|clear l; intros b l _ a H; split].

    {
    apply H; [apply in_eq|clear H; apply in_cons; revert b; revert a].
    elim l; [simpl; auto|clear l; intros b l IHl d a].
    assert (H : last (a :: b :: l) = last (b :: l))
      by (induction l; simpl; auto); rewrite H; apply in_cons; auto.
    }

    {
    revert H; revert b; revert a; elim l; [|clear l; intros c l IHl a b H];
    [simpl; intros a b H; split; auto; apply H; [apply in_cons|]; apply in_eq|].
    split; [apply H; [apply in_cons|]; apply in_eq|].
    apply IHl; intros x y Hx Hy; apply H; apply in_cons; auto.
    }
  }

  {
  elim l; [unfold all_equiv; simpl; tauto|clear l; intros a l _; revert a].
  elim l;[ unfold all_equiv; simpl; intros a _ x y Hx Hy;
           elim Hx; [clear Hx; intro Hx|tauto];
           elim Hy; [clear Hy; intro Hy|tauto];
           rewrite <- Hx; rewrite Hy; tauto|clear l; intros b l _ a H].
  intros x y Hx Hy; destruct H as [Hend Hbeg].
  destruct (In_nth _ _ a Hx) as [n1 Hn1]; clear Hx; destruct Hn1 as [Hn1 Hx].
  destruct (In_nth _ _ a Hy) as [n2 Hn2]; clear Hy; destruct Hn2 as [Hn2 Hy].
  assert (Hlast : nth (S (length l)) (a :: b :: l) a = last (b :: l) a).
    {
    transitivity (nth (length l) (b :: l) a); [simpl; auto|].
    revert dependent b. intros b _ _ _ _ _ _; clear n1 n2 x y.
    revert b; revert a; elim l; [simpl; auto|clear l; intros b l IHl d a].
    transitivity (nth (S (length l)) (a :: b :: l) d); [simpl; auto|].
    transitivity (nth (length l) (b :: l) d); [simpl; auto|].
    rewrite IHl; simpl; auto.
    }
  assert (HaE : a = nth 0 (a :: b :: l) a) by (simpl; auto).
  rewrite <- Hlast in Hend; clear Hlast; rewrite <- Hx; rewrite <- Hy.
  elim (PeanoNat.Nat.lt_ge_cases n1 n2); intro HLe; split;
  try solve[apply all_equiv'_auxP; auto;
            try apply PeanoNat.Nat.lt_le_incl; auto; discriminate];
  intro H; cut a; try (intro Ha; rewrite HaE in Ha; revert Ha);
  try(apply Hend; revert H); apply all_equiv'_auxP; auto; try discriminate;
  try apply PeanoNat.Nat.le_0_l; simpl in *; try apply PeanoNat.Nat.lt_0_succ;
  apply PeanoNat.Nat.lt_succ_r; auto.
  }
Qed.

Definition stronger (l1 l2 : list Prop) :=
  forall x y, In x l1 -> In y l2 -> (x -> y).

Definition all_equiv_under (l1 l2 : list Prop) :=
  forall x y z, In x l1 -> In y l2 -> In z l2 -> (x -> (y <-> z)).

Lemma all_equiv_under_chara : forall l1 l2,
  all_equiv_under l1 l2 <-> forall x, In x l1 -> x -> all_equiv l2.
Proof.
  unfold all_equiv_under, all_equiv.
  intros; split; intros; eauto.
Qed.

Lemma all_equiv2_impl__stronger : forall l1 l2 x y,
  all_equiv l1 -> all_equiv l2 -> In x l1 -> In y l2 -> (x -> y) -> stronger l1 l2.
Proof.
  intros l1 l2 x y Heq1 Heq2 HxIn HyIn Hxy x1 y1 Hx1In Hy1In.
  rewrite (Heq1 x1 x); [rewrite (Heq2 y1 y)|..]; assumption.
Qed.

Lemma stronger2__stronger_right : forall l1 l2 l2',
  stronger l1 l2 -> stronger l1 l2' -> stronger l1 (l2++l2').
Proof.
  intros l1 l2 l2' Hs Hs' x y Hx Hy.
  apply in_app_or in Hy.
  destruct Hy.
    apply Hs; assumption.
    apply Hs'; assumption.
Qed.

Lemma stronger2__stronger_left : forall l1 l1' l2,
  stronger l1 l2 -> stronger l1' l2 -> stronger (l1++l1') l2.
Proof.
  intros l1 l1' l2 Hs Hs' x y Hx Hy.
  apply in_app_or in Hx.
  destruct Hx.
    apply Hs; assumption.
    apply Hs'; assumption.
Qed.

Lemma stronger_transitivity : forall l1 l2 l3,
  stronger l1 l2 -> stronger l2 l3 -> l2 <> nil -> stronger l1 l3.
Proof.
  intros l1 l2 l3 Hs1 Hs2 Hl2 x z Hx Hz.
  destruct l2.
    intuition.
  unfold stronger in *.
  specialize Hs1 with x P.
  specialize Hs2 with P z.
  simpl in *.
  auto.
Qed.

Lemma all_equiv2_stronger2__all_equiv : forall l1 l2,
  all_equiv l1 -> all_equiv l2 ->
  stronger l1 l2 -> stronger l2 l1 ->
  all_equiv (l1++l2).
Proof.
  intros l1 l2 He1 He2 Hs1 Hs2 x y Hx Hy.
  apply in_app_or in Hx.
  apply in_app_or in Hy.
  destruct Hx; destruct Hy; auto; split.
    apply Hs1; assumption.
    apply Hs2; assumption.
    apply Hs2; assumption.
    apply Hs1; assumption.
Qed.

Lemma all_equiv3_stronger3__all_equiv : forall l1 l2 l3,
  l1 <> nil -> l2 <> nil -> l3 <> nil ->
  all_equiv l1 -> all_equiv l2 -> all_equiv l3 ->
  stronger l1 l2 -> stronger l2 l3 ->  stronger l3 l1 ->
  all_equiv (l1++l2++l3).
Proof.
  intros l1 l2 l3 H1 H2 H3 He1 He2 He3 Hs1 Hs2 Hs3.
  apply all_equiv2_stronger2__all_equiv.
    assumption.
    apply all_equiv2_stronger2__all_equiv; [..|apply stronger_transitivity with l1]; assumption.
    apply stronger2__stronger_right; [|apply stronger_transitivity with l2]; assumption.
    apply stronger2__stronger_left; [apply stronger_transitivity with l3|]; assumption.
Qed.

Lemma all_equiv2_impl2__all_equiv : forall l1 l2 x y x' y',
  all_equiv l1 -> all_equiv l2 ->
  In x l1 -> In y l2 -> (x -> y) ->
  In x' l2 -> In y' l1 -> (x' -> y') ->
  all_equiv (l1++l2).
Proof.
  intros l1 l2 x y x' y'; intros.
  apply all_equiv2_stronger2__all_equiv; trivial.
    apply all_equiv2_impl__stronger with x y; assumption.
    apply all_equiv2_impl__stronger with x' y'; assumption.
Qed.

Lemma all_equiv3_impl3__all_equiv : forall l1 l2 l3 x y x' y' x'' y'',
  all_equiv l1 -> all_equiv l2 -> all_equiv l3 ->
  In x l1 -> In y l2 -> (x -> y) ->
  In x' l2 -> In y' l3 -> (x' -> y') ->
  In x'' l3 -> In y'' l1 -> (x'' -> y'') ->
  all_equiv (l1++l2++l3).
Proof.
  intros l1 l2 l3 x y x' y' x'' y''; intros.
  apply all_equiv3_stronger3__all_equiv; trivial; try (intro He; rewrite He in *; auto).
    apply all_equiv2_impl__stronger with x y; assumption.
    apply all_equiv2_impl__stronger with x' y'; assumption.
    apply all_equiv2_impl__stronger with x'' y''; assumption.
Qed.

Lemma all_equiv_trivial : forall x, all_equiv (x::nil).
Proof.
  unfold all_equiv; simpl.
  induction 1;[|contradiction].
  induction 1;[|contradiction].
  subst; reflexivity.
Qed.

Lemma incl_preserves_all_equiv : forall l1 l2,
  incl l1 l2 -> all_equiv l2 -> all_equiv l1.
Proof.
  unfold all_equiv.
  intros; eauto.
Qed.

Lemma incl_preserves_stronger : forall l1 l2 l1' l2',
  incl l1 l1' -> incl l2 l2' -> stronger l1' l2' -> stronger l1 l2.
Proof.
  intros l1 l2 l1' l2' Hi1 Hi2 Hs x y Hxl1 Hyl2.
  apply Hs; auto.
Qed.

Ltac inlist := simpl; repeat (try (left; reflexivity); right).