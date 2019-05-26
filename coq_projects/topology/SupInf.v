Require Export Reals.
From ZornsLemma Require Import EnsemblesImplicit.
From ZornsLemma Require Import ImageImplicit.

Definition sup := completeness.

Open Scope R_scope.

Definition is_lower_bound (E:R->Prop) (m:R) :=
  forall x:R, E x -> x >= m.
Definition lower_bound (E:R->Prop) :=
  exists m:R, is_lower_bound E m.
Definition is_glb (E:R->Prop) (m:R) :=
  is_lower_bound E m /\ (forall b:R, is_lower_bound E b -> b <= m).

Definition inf: forall E:R->Prop, lower_bound E -> (exists x:R, E x) ->
  { m:R | is_glb E m }.
unshelve refine (fun E Hlb Hinh =>
  let H:=_ in let H0:=_ in
  exist _ (- (proj1_sig (sup (Im E Ropp) H H0))) _).
destruct Hlb as [m].
exists (-m).
red; intros.
destruct H0.
rewrite H1.
auto with real.

destruct Hinh as [x].
exists (-x).
exists x; trivial.

destruct sup as [m].
simpl.
split.
red; intros.
cut (-x <= m).
intros.
replace x with (--x) by ring.
auto with real.
apply i.
exists x; trivial.

intros.
cut (m <= -b).
intros.
replace b with (--b) by ring.
auto with real.
apply i.
red; intros.
cut (-x >= b).
intros.
replace x with (--x) by ring.
auto with real.
apply H1.
destruct H2.
rewrite H3.
replace (--x) with x by ring; trivial.
Qed.

Lemma lub_approx: forall (S:Ensemble R) (m:R) (eps:R),
  is_lub S m -> eps > 0 -> exists x:R, In S x /\
    m - eps < x <= m.
Proof.
intros.
assert (exists x:R, In S x /\ m - eps < x).
apply NNPP; intro.
pose proof (not_ex_all_not _ _ H1); clear H1.
simpl in H2.
assert (is_upper_bound S (m-eps)).
red; intros.
assert (~ x > m - eps).
red; intro.
contradiction (H2 x).
split; trivial.
destruct (total_order_T x (m-eps)) as [[?|?]|?]; auto with *.
contradiction H3; trivial.
destruct H.
pose proof (H3 _ H1).
apply Rle_minus in H4.
ring_simplify in H4.
assert (0 < 0).
apply Rlt_le_trans with eps; trivial.
revert H5; apply Rlt_irrefl.

destruct H1 as [x [? ?]].
exists x; repeat split; trivial.
destruct H.
apply H; trivial.
Qed.

Lemma glb_approx: forall (S:Ensemble R) (m:R) (eps:R),
  is_glb S m -> eps > 0 -> exists x:R, In S x /\ m <= x < m + eps.
Proof.
intros.
assert (exists x:R, In S x /\ x < m + eps).
apply NNPP; intro.
pose proof (not_ex_all_not _ _ H1); clear H1.
simpl in H2.
assert (is_lower_bound S (m+eps)).
red; intros.
assert (~ x < m + eps).
red; intro.
contradiction (H2 x).
split; trivial.
destruct (total_order_T x (m+eps)) as [[?|?]|?]; auto with *.
contradiction H3; trivial.
destruct H.
pose proof (H3 _ H1).
apply Rle_minus in H4.
ring_simplify in H4.
assert (0 < 0).
apply Rlt_le_trans with eps; trivial.
revert H5; apply Rlt_irrefl.

destruct H1 as [x [? ?]].
exists x; repeat split; trivial.
destruct H.
assert (x >= m).
apply H; trivial.
auto with *.
Qed.

Lemma lt_plus_epsilon_le: forall x y:R,
  (forall eps:R, eps > 0 -> x < y + eps) -> x <= y.
Proof.
intros.
destruct (total_order_T x y) as [[?|?]|?]; auto with *.
assert (x < y + (x - y)).
apply H.
apply Rgt_minus; trivial.
ring_simplify in H0.
contradict H0.
apply Rlt_irrefl.
Qed.

Lemma gt_minus_epsilon_ge: forall x y:R,
  (forall eps:R, eps > 0 -> x > y - eps) -> x >= y.
Proof.
intros.
destruct (total_order_T x y) as [[?|?]|?]; auto with *.
assert (x > y - (y - x)).
apply H.
apply Rgt_minus; trivial.
ring_simplify in H0.
contradict H0.
apply Rlt_irrefl.
Qed.
