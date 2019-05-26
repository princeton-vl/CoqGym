Require Export FiniteTypes.
Require Import InfiniteTypes.
Require Import CSB.
Require Import DecidableDec.
Require Export Relation_Definitions.
Require Import Relation_Definitions_Implicit.
Require Import Description.
Require Import Proj1SigInjective.
Require Import DependentTypeChoice.

Set Asymmetric Patterns.

Inductive CountableT (X:Type) : Prop :=
  | intro_nat_injection: forall f:X->nat, injective f -> CountableT X.

Lemma CountableT_is_FiniteT_or_countably_infinite:
  forall X:Type, CountableT X ->
      {FiniteT X} + {exists f:X->nat, bijective f}.
Proof.
intros.
apply exclusive_dec.
red; intro.
destruct H0 as [? [f ?]].
contradiction nat_infinite.
apply bij_finite with _ f; trivial.
apply bijective_impl_invertible; trivial.

case (classic (FiniteT X)).
left; trivial.
right.
apply infinite_nat_inj in H0.
destruct H.
destruct H0 as [g].
apply CSB with f g; trivial.
Qed.

Lemma countable_nat_product: CountableT (nat*nat).
Proof.
pose (sum_1_to_n := fix sum_1_to_n n:nat := match n with
  | O => O
  | S m => (sum_1_to_n m) + n
end).
exists (fun p:nat*nat => let (m,n):=p in
  (sum_1_to_n (m+n)) + n).
assert (forall m n:nat, m<n ->
  sum_1_to_n m + m < sum_1_to_n n).
intros.
induction H.
simpl.
auto with arith.
apply lt_trans with (sum_1_to_n m0).
assumption.
simpl.
assert (0 < S m0); auto with arith.
assert (sum_1_to_n m0 + 0 < sum_1_to_n m0 + S m0); auto with arith.
assert (sum_1_to_n m0 + 0 = sum_1_to_n m0); auto with arith.
rewrite H2 in H1; assumption.

red; intros.
destruct x1 as [x1 y1].
destruct x2 as [x2 y2].
Require Import Compare_dec.
case (lt_eq_lt_dec (x1+y1) (x2+y2)); intro.
case s; intro.
assert (sum_1_to_n (x1+y1) + y1 < sum_1_to_n (x2+y2) + y2).
apply le_lt_trans with (sum_1_to_n (x1+y1) + (x1+y1)).
assert (sum_1_to_n (x1+y1) + (x1+y1) =
  (sum_1_to_n (x1+y1) + y1) + x1).
Require Import ArithRing.
ring.
auto with arith.
apply lt_le_trans with (sum_1_to_n (x2+y2)).
apply H; trivial.
auto with arith.
rewrite H0 in H1.
contradict H1.
auto with arith.

assert (y1=y2).
rewrite e in H0.
Require Import Arith.
apply plus_reg_l in H0.
assumption.
f_equal; trivial.
rewrite H1 in e.
rewrite plus_comm in e.
rewrite (plus_comm x2 y2) in e.
apply plus_reg_l in e.
assumption.

assert (sum_1_to_n (x2+y2) + y2 < sum_1_to_n (x1+y1) + y1).
apply le_lt_trans with (sum_1_to_n (x2+y2) + (x2+y2)).
auto with arith.
apply lt_le_trans with (sum_1_to_n (x1+y1)); auto with arith.
rewrite H0 in H1.
contradict H1.
auto with arith.
Qed.

Lemma countable_sum: forall X Y:Type,
  CountableT X -> CountableT Y -> CountableT (X+Y).
Proof.
intros.
destruct H as [f].
destruct H0 as [g].
destruct countable_nat_product as [h].
exists (fun s:X+Y => match s with
  | inl x => h (0, f x)
  | inr y => h (1, g y)
end).
red; intros s1 s2 ?.
destruct s1 as [x1|y1]; destruct s2 as [x2|y2];
  apply H1 in H2; try discriminate H2;
  intros; f_equal; (apply H || apply H0); injection H2; trivial.
Qed.

Lemma countable_product: forall X Y:Type,
  CountableT X -> CountableT Y -> CountableT (X*Y).
Proof.
intros.
destruct H as [f].
destruct H0 as [g].
pose (fg := fun (p:X*Y) => let (x,y):=p in (f x, g y)).
destruct countable_nat_product as [h].
exists (fun p:X*Y => h (fg p)).
red; intros.
apply H1 in H2.
destruct x1 as [x1 y1].
destruct x2 as [x2 y2].
unfold fg in H2.
injection H2; intros.
apply H0 in H3.
apply H in H4.
f_equal; trivial.
Qed.

Require Import FunctionalExtensionality.

Lemma countable_exp: forall X Y:Type,
  FiniteT X -> CountableT Y -> CountableT (X->Y).
Proof.
intros.
induction H.
exists (fun _ => 0).
red; intros.
extensionality f.
destruct f.

destruct (countable_product (T->Y) Y); trivial.

exists (fun (g:option T->Y) =>
  f (fun x:T => g (Some x), g None)).
red; intros g1 g2 ?.
apply H1 in H2.
extensionality o.
destruct o.
injection H2; intros.
pose proof (equal_f H4).
simpl in H5.
apply H5.
injection H2; trivial.

destruct H1.
destruct IHFiniteT.
exists (fun (h:Y0->Y) => f0 (fun x:X => h (f x))).
red; intros h1 h2 ?.
apply H3 in H4.
pose proof (equal_f H4).
simpl in H5.
extensionality y.
rewrite <- (H2 y).
apply H5.
Qed.

Definition Countable {X:Type} (S:Ensemble X) : Prop :=
  CountableT {x:X | In S x}.

Lemma inj_countable: forall {X Y:Type} (f:X->Y),
  CountableT Y -> injective f -> CountableT X.
Proof.
intros.
destruct H as [g].
exists (fun x:X => g (f x)).
red; intros; auto.
Qed.

Lemma surj_countable: forall {X Y:Type} (f:X->Y),
  CountableT X -> surjective f -> CountableT Y.
Proof.
intros.
Require Import ClassicalChoice.

pose proof (choice (fun (y:Y) (x:X) => f x = y)).
destruct H1 as [finv].
exact H0.

apply inj_countable with finv.
assumption.
red; intros.
congruence.
Qed.

Lemma countable_downward_closed: forall {X:Type} (S T:Ensemble X),
  Countable T -> Included S T -> Countable S.
Proof.
intros.
destruct H.
exists (fun x:{x:X | In S x} => match x with
  | exist x0 i => f (exist _ x0 (H0 _ i))
  end).
red; intros.
destruct x1 as [x1].
destruct x2 as [x2].
apply H in H1.
injection H1; intros.
destruct H2.
destruct (proof_irrelevance _ i i0).
trivial.
Qed.

Lemma countable_img: forall {X Y:Type} (f:X->Y) (S:Ensemble X),
  Countable S -> Countable (Im S f).
Proof.
intros.
assert (forall x:X, In S x -> In (Im S f) (f x)).
auto with sets.
pose (fS := fun x:{x:X | In S x} =>
  match x return {y:Y | In (Im S f) y} with
  | exist x0 i => exist _ (f x0) (H0 x0 i)
  end).
apply surj_countable with fS; trivial.
red; intros.
destruct y.
destruct i.
exists (exist _ x i).
simpl.
generalize (H0 x i); intro.
generalize (Im_intro X Y S f x i y e); intro.
destruct e.
destruct (proof_irrelevance _ i0 i1).
trivial.
Qed.

Lemma countable_type_ensemble: forall {X:Type} (S:Ensemble X),
  CountableT X -> Countable S.
Proof.
intros.
red.
apply inj_countable with (@proj1_sig _ (fun x:X => In S x)).
assumption.
red; intros.
apply proj1_sig_injective.
assumption.
Qed.

Lemma FiniteT_impl_CountableT: forall X:Type,
  FiniteT X -> CountableT X.
Proof.
intros.
induction H.
exists (False_rect nat).
red; intros.
destruct x1.
destruct IHFiniteT.
exists (fun x:option T => match x with
  | Some x0 => S (f x0)
  | None => 0
end).
red; intros.
destruct x1; destruct x2; try (injection H1 || discriminate H1); trivial.
intro.
apply H0 in H2.
destruct H2; trivial.

destruct IHFiniteT as [g].
destruct H0 as [finv].
exists (fun y:Y => g (finv y)).
red; intros y1 y2 ?.
apply H1 in H3.
congruence.
Qed.

Lemma Finite_impl_Countable: forall {X:Type} (S:Ensemble X),
  Finite _ S -> Countable S.
Proof.
intros.
apply FiniteT_impl_CountableT.
apply Finite_ens_type; trivial.
Qed.

Require Export ZArith.

Lemma positive_countable: CountableT positive.
Proof.
exists nat_of_P.
red; intros.
apply nat_of_P_inj; trivial.
Qed.

Lemma Z_countable: CountableT Z.
Proof.
destruct (countable_nat_product) as [f].
destruct positive_countable as [g].
exists (fun n:Z => match n with
  | Z0 => f (0, 0)
  | Zpos p => f (1, g p)
  | Zneg p => f (2, g p)
end).
red; intros n1 n2 ?.
destruct n1 as [|p1|p1]; destruct n2 as [|p2|p2]; apply H in H1;
  try discriminate H1.
trivial.
injection H1; intro; f_equal; auto.
injection H1; intro; f_equal; auto.
Qed.

Require Export QArith.

Lemma Q_countable: CountableT Q.
Proof.
destruct countable_nat_product as [f].
destruct positive_countable as [g].
destruct Z_countable as [h].
exists (fun q:Q => match q with
  n # d => f (h n, g d)
end).
red; intros q1 q2 ?.
destruct q1 as [n1 d1]; destruct q2 as [n2 d2].
apply H in H2.
injection H2; intros.
f_equal; auto.
Qed.

Require Export IndexedFamilies.

Lemma countable_union: forall {X A:Type}
  (F:IndexedFamily A X), CountableT A ->
    (forall a:A, Countable (F a)) ->
    Countable (IndexedUnion F).
Proof.
intros.
destruct (choice_on_dependent_type (fun (a:A)
                               (f:{x:X | In (F a) x} -> nat) =>
  injective f)) as [choice_fun_inj].
intro.
destruct (H0 a).
exists f; trivial.

destruct (choice (fun (x:{x:X | In (IndexedUnion F) x}) (a:A) =>
  In (F a) (proj1_sig x))) as [choice_fun_a].
destruct x as [x [a]].
exists a.
assumption.

destruct countable_nat_product as [g].
destruct H as [h].
exists (fun x:{x:X | In (IndexedUnion F) x} =>
  g (h (choice_fun_a x), choice_fun_inj (choice_fun_a x)
                                   (exist _ (proj1_sig x) (H2 x)))).
red; intros.
apply H3 in H4.
injection H4; intros.
apply H in H6.
revert H5.
generalize (H2 x1).
generalize (H2 x2).
rewrite H6.
intros.
apply H1 in H5.
injection H5.
apply proj1_sig_injective.
Qed.
