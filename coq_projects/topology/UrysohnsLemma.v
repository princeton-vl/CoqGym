Set Asymmetric Patterns.

(* define nonnegative dyadic rationals *)
Inductive dyadic_rational : Type :=
  | m_over_2_to_n: forall m n:nat, dyadic_rational.
Inductive dr_eq : dyadic_rational -> dyadic_rational -> Prop :=
  | dr_eq_refl: forall x:dyadic_rational, dr_eq x x
  | dr_eq_sym: forall x y:dyadic_rational, dr_eq x y -> dr_eq y x
  | dr_eq_trans: forall x y z:dyadic_rational,
    dr_eq x y -> dr_eq y z -> dr_eq x z
  | dr_eq_scale: forall (m n:nat),
    dr_eq (m_over_2_to_n m n)
          (m_over_2_to_n (2*m) (S n)).
Inductive dr_lt : dyadic_rational -> dyadic_rational -> Prop :=
  | intro_dr_lt: forall m m' n:nat, m < m' ->
    dr_lt (m_over_2_to_n m n) (m_over_2_to_n m' n)
  | dr_lt_wd: forall x x' y y':dyadic_rational,
    dr_lt x y -> dr_eq x x' -> dr_eq y y' -> dr_lt x' y'.

Lemma dr_incr_denom: forall (m n n':nat), n<=n' ->
  exists m':nat, dr_eq (m_over_2_to_n m' n')
                       (m_over_2_to_n m n).
Proof.
induction 1.
exists m.
apply dr_eq_refl.
destruct IHle as [m'].
exists (2*m').
apply dr_eq_trans with (m_over_2_to_n m' m0); trivial.
apply dr_eq_sym.
apply dr_eq_scale.
Qed.

Lemma dr_total_order: forall x y:dyadic_rational,
  dr_lt x y \/ dr_eq x y \/ dr_lt y x.
Proof.
intros.
destruct x as [m n].
destruct y as [m' n'].
Require Import Arith.
destruct (le_or_lt n n').
destruct (dr_incr_denom m n n') as [m0]; trivial.
destruct (le_or_lt m0 m').
destruct (le_lt_or_eq _ _ H1).
left.
apply dr_lt_wd with
  (m_over_2_to_n m0 n') (m_over_2_to_n m' n'); trivial.
apply intro_dr_lt; trivial.
apply dr_eq_refl.
right; left.
apply dr_eq_trans with (m_over_2_to_n m0 n').
apply dr_eq_sym; trivial.
rewrite H2; apply dr_eq_refl.
right; right.
apply dr_lt_wd with
  (m_over_2_to_n m' n') (m_over_2_to_n m0 n'); trivial.
apply intro_dr_lt; trivial.
apply dr_eq_refl.

assert (n' <= n) by auto with arith.
destruct (dr_incr_denom m' n' n) as [m0]; trivial.
destruct (le_or_lt m m0).
destruct (le_lt_or_eq _ _ H2).
left.
apply dr_lt_wd with
  (m_over_2_to_n m n) (m_over_2_to_n m0 n).
apply intro_dr_lt; trivial.
apply dr_eq_refl.
trivial.
right; left.
apply dr_eq_trans with (m_over_2_to_n m0 n); trivial.
rewrite H3; apply dr_eq_refl.
right; right.
apply dr_lt_wd with
  (m_over_2_to_n m0 n) (m_over_2_to_n m n); trivial.
apply intro_dr_lt; trivial.
apply dr_eq_refl.
Qed.

Require Export QArith.
Local Notation " ' x " := (Zpos x) (at level 20, no associativity) : Z_scope.

Fixpoint pos_power2 (n:nat) : positive := match n with
  | O => 1%positive
  | S m => ((pos_power2 m)~0)%positive
end.

Definition dr2Q (x:dyadic_rational) : Q :=
  match x with
  | m_over_2_to_n m n => (Z_of_nat m) # (pos_power2 n)
  end.

Lemma dr2Q_wd: forall x y:dyadic_rational,
  dr_eq x y -> dr2Q x == dr2Q y.
Proof.
intros.
induction H.
auto with qarith.
auto with qarith.
transitivity (dr2Q y); trivial.
simpl.
unfold Qeq.
simpl.
replace ((' (pos_power2 n)~0)%Z) with
  ((2 * ' pos_power2 n)%Z) by trivial.
repeat rewrite inj_plus.
simpl Z_of_nat.
ring.
Qed.

Lemma dr2Q_incr: forall x y:dyadic_rational,
  dr_lt x y -> dr2Q x < dr2Q y.
Proof.
induction 1.
unfold dr2Q.
unfold Qlt.
simpl.
apply Zmult_lt_compat_r.
now unfold Zlt.
auto with zarith.

rewrite <- (dr2Q_wd _ _ H0).
rewrite <- (dr2Q_wd _ _ H1).
trivial.
Qed.

Lemma Qlt_dr_lt: forall x y:dyadic_rational,
  (dr2Q x < dr2Q y)%Q -> dr_lt x y.
Proof.
intros.
destruct (dr_total_order x y) as [|[|]]; trivial.
apply dr2Q_wd in H0.
contradict H0.
auto with qarith.
apply dr2Q_incr in H0.
contradict H0.
auto with qarith.
Qed.

Require Export Qreals.
Open Scope R_scope.
Lemma dyadic_rationals_dense_in_reals: forall x y:R,
  0 <= x < y -> exists q:dyadic_rational,
  x < Q2R (dr2Q q) < y.
Proof.
intros.
assert (forall m:Z, exists n:nat, ((m < ' pos_power2 n)%Z)).
intros.
case m; intros.
exists O.
unfold Zlt; trivial.
induction p.
destruct IHp as [n].
exists (S n).
unfold Zlt.
simpl. rewrite Pos.compare_xI_xO.
unfold Zlt in H0.
simpl in H0.
now rewrite H0.
destruct IHp as [n].
exists (S n).
unfold Zlt; simpl.
unfold Zlt in H0; simpl in H0.
trivial.
exists (1%nat).
unfold Zlt; trivial.
exists O.
unfold Zlt; trivial.

destruct (H0 (up (1/(y-x)))) as [n].
Require Import RationalsInReals.
destruct (rational_interpolation x y (pos_power2 n)) as [m].
apply H.
apply Rlt_trans with (IZR (up (1/(y-x)))).
apply archimed.
apply IZR_lt; trivial.

destruct m as [|m|].
unfold Q2R in H2.
simpl in H2.
replace (0 * _) with 0 in H2 by ring.
destruct H; destruct H2.
contradict H.
auto with real.

exists (m_over_2_to_n (nat_of_P m) n).
unfold dr2Q.
rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
trivial.

assert (x < 0).
apply Rlt_trans with (Q2R (Zneg p # pos_power2 n)).
apply H2.
replace 0 with (Q2R 0).
apply Qlt_Rlt.
auto with *.
unfold Q2R; simpl; ring.
destruct H.
contradict H.
auto with real.
Qed.

Section Urysohns_Lemma_construction.

Require Export TopologicalSpaces.
Require Export InteriorsClosures.

Variable X:TopologicalSpace.
Variable normal_sep_fun: forall F U:Ensemble (point_set X),
  closed F -> open U -> Included F U ->
  { V:Ensemble (point_set X) | open V /\ Included F V /\
    Included (closure V) U }.
Variable U0 U1:Ensemble (point_set X).
Hypothesis U0_open: open U0.
Hypothesis U1_open: open U1.
Hypothesis U0_in_U1: Included (closure U0) U1.

Definition Un (n:nat) : Ensemble (point_set X) :=
  match n with
  | O => U0
  | S O => U1
  | S (S _) => Full_set
  end.

Lemma Un_open: forall n:nat, open (Un n).
Proof.
destruct n as [|[|]]; trivial.
simpl.
apply open_full.
Qed.

Lemma Un_incr: forall n:nat, Included (closure (Un n))
                                    (Un (S n)).
Proof.
destruct n as [|].
simpl.
trivial.
simpl.
red; intros; constructor.
Qed.

Require Import Div2.
Require Import Even.
Definition expand_U_dyadic (f:nat->Ensemble (point_set X))
  (Hopen: forall n:nat, open (f n))
  (Hincr: forall n:nat, Included (closure (f n)) (f (S n)))
  (n:nat) : Ensemble (point_set X) :=
if (even_odd_dec n) then f (div2 n) else
let m := div2 n in proj1_sig
  (normal_sep_fun (closure (f m)) (f (S m))
     (closure_closed _) (Hopen _) (Hincr _)).

Lemma expand_U_dyadic_open: forall f Hopen Hincr n,
  open (expand_U_dyadic f Hopen Hincr n).
Proof.
intros.
unfold expand_U_dyadic.
destruct even_odd_dec.
apply Hopen.
destruct normal_sep_fun.
simpl.
apply a.
Qed.

Lemma expand_U_dyadic_incr: forall f Hopen Hincr n,
  Included (closure (expand_U_dyadic f Hopen Hincr n))
     (expand_U_dyadic f Hopen Hincr (S n)).
Proof.
intros.
unfold expand_U_dyadic.
simpl.
destruct even_odd_dec.
destruct normal_sep_fun.
simpl.
destruct n.
simpl.
apply a.
rewrite <- odd_div2.
apply a.
now inversion e.

simpl.
destruct normal_sep_fun.
simpl.
destruct o.
rewrite even_div2.
now apply a.
trivial.
Qed.

Definition packaged_expand_U_dyadic :
  { f:nat->Ensemble (point_set X) |
    (forall m:nat, open (f m)) /\
    (forall m:nat, Included (closure (f m)) (f (S m))) } ->
  { f:nat->Ensemble (point_set X) |
    (forall m:nat, open (f m)) /\
    (forall m:nat, Included (closure (f m)) (f (S m))) }.
refine (fun fsig => match fsig with
  | exist f (conj Hopen Hincr as a) => exist _ (expand_U_dyadic f Hopen Hincr) _
  end).
destruct a.
split.
apply expand_U_dyadic_open.
apply expand_U_dyadic_incr.
Defined.

Definition U_dyadic_level_n (n:nat) :
  { f:nat->Ensemble (point_set X) |
    (forall m:nat, open (f m)) /\
    (forall m:nat, Included (closure (f m)) (f (S m))) }.
refine (let lev_n := fix lev_n (n:nat) :
  { f:nat->Ensemble (point_set X) |
    (forall m:nat, open (f m)) /\
    (forall m:nat, Included (closure (f m)) (f (S m))) } :=
  match n with
  | O => exist _ Un _
  | S n' => packaged_expand_U_dyadic (lev_n n')
  end in lev_n n).
split.
apply Un_open.
apply Un_incr.
Defined.

Definition U_dyadic (x:dyadic_rational) :
  Ensemble (point_set X) :=
match x with
| m_over_2_to_n m n => (proj1_sig (U_dyadic_level_n n)) m
end.

Lemma U_dyadic_wd: forall x y:dyadic_rational, dr_eq x y ->
  U_dyadic x = U_dyadic y.
Proof.
intros.
induction H.
trivial.
auto.
transitivity (U_dyadic y); trivial.
simpl.
unfold packaged_expand_U_dyadic.
destruct U_dyadic_level_n.
destruct a.
simpl.
unfold expand_U_dyadic.
replace ((m + (m + 0))%nat) with ((2*m)%nat) by reflexivity.
rewrite div2_double.
assert (forall m:nat, even (2*m)).
induction m0.
constructor.
Require Import Arith.
replace ((2 * S m0)%nat) with ((S (S (2 * m0)))%nat) by ring.
constructor; constructor; trivial.
destruct even_odd_dec.
trivial.
contradiction not_even_and_odd with ((2 * m)%nat).
apply H.
Qed.

Lemma U_dyadic_open: forall x:dyadic_rational,
  open (U_dyadic x).
Proof.
intro.
destruct x.
unfold U_dyadic.
destruct U_dyadic_level_n.
simpl.
apply a.
Qed.

Lemma U_dyadic_incr: forall x y:dyadic_rational, dr_lt x y ->
  Included (closure (U_dyadic x)) (U_dyadic y).
Proof.
intros.
induction H.
induction H.
unfold U_dyadic.
destruct U_dyadic_level_n.
simpl.
apply a.
cut (Included (closure (U_dyadic (m_over_2_to_n m0 n)))
   (U_dyadic (m_over_2_to_n (S m0) n))).
intro.
pose proof (closure_inflationary
  (U_dyadic (m_over_2_to_n m0 n))).
auto with sets.
unfold U_dyadic.
destruct U_dyadic_level_n.
simpl.
apply a.

rewrite <- (U_dyadic_wd _ _ H0).
rewrite <- (U_dyadic_wd _ _ H1).
trivial.
Qed.

Require Export RTopology.
Definition Urysohns_Lemma_function : point_set X -> point_set RTop.
refine (fun x:point_set X => proj1_sig (inf
 (Add
  (Im [ alpha:dyadic_rational | In (U_dyadic alpha) x ]
      (fun alpha:dyadic_rational => Q2R (dr2Q alpha)))
  1)
  _ _)).
exists 0.
red; intros.
destruct H.
destruct H.
destruct x0.
simpl in H0.
rewrite H0.
replace 0 with (Q2R 0).
cut (Q2R 0 <= Q2R (Z_of_nat m # pos_power2 n)); auto with real.
apply Qle_Rle.
unfold Qle.
simpl.
auto with zarith.
unfold Q2R.
simpl.
ring.
destruct H.
left.
red.
auto with real.

exists 1.
right.
constructor.
Defined.

Lemma Urysohns_Lemma_function_range:
  forall x:point_set X, 0 <= Urysohns_Lemma_function x <= 1.
Proof.
intros.
unfold Urysohns_Lemma_function; destruct inf as [y].
simpl.
split.
apply i.
red; intros.
destruct H.
destruct H.
rewrite H0.
replace 0 with (Q2R 0).
cut (Q2R 0 <= Q2R (dr2Q x0)); auto with real.
apply Qle_Rle.
destruct x0.
unfold dr2Q.
unfold Qle.
simpl.
auto with zarith.
unfold Q2R.
simpl.
ring.
destruct H.
left.
red; auto with real.
cut (1 >= y); auto with real.
apply i.
right; constructor.
Qed.

Lemma Urysohns_Lemma_function_0: forall x:point_set X,
  In U0 x -> Urysohns_Lemma_function x = 0.
Proof.
intros.
apply Rle_antisym.
unfold Urysohns_Lemma_function; destruct inf as [y].
simpl.
cut (0 >= y); auto with real.
apply i.
left.
exists (m_over_2_to_n 0 0).
constructor.
simpl.
trivial.
simpl.
unfold Q2R.
simpl.
ring.
apply Urysohns_Lemma_function_range.
Qed.

Lemma Urysohns_Lemma_function_1: forall x:point_set X,
  ~ In U1 x -> Urysohns_Lemma_function x = 1.
Proof.
intros.
apply Rle_antisym.
apply Urysohns_Lemma_function_range.
unfold Urysohns_Lemma_function; destruct inf as [y].
simpl.
apply i.
red; intros.
destruct H0.
destruct H0.
destruct x0.
destruct H0.
assert (~ (m < (nat_of_P (pos_power2 n)))%nat).
intro.
assert (forall n:nat, dr_eq
  (m_over_2_to_n (nat_of_P (pos_power2 n)) n)
  (m_over_2_to_n 1 0)).
induction n0.
simpl.
unfold nat_of_P.
simpl.
apply dr_eq_refl.
apply dr_eq_trans with (2:=IHn0).
apply dr_eq_sym.
replace (nat_of_P (pos_power2 (S n0))) with
  ((2 * nat_of_P (pos_power2 n0))%nat).
apply dr_eq_scale.
simpl pos_power2.
symmetry. apply Pos2Nat.inj_xO.
assert (dr_lt (m_over_2_to_n m n) (m_over_2_to_n 1 0)).
apply dr_lt_wd with (m_over_2_to_n m n)
  (m_over_2_to_n (nat_of_P (pos_power2 n)) n).
apply intro_dr_lt.
exact H2.
apply dr_eq_refl.
apply H3.
pose proof (U_dyadic_incr _ _ H4).
simpl (U_dyadic (m_over_2_to_n 1 0)) in H5.
assert (Included (U_dyadic (m_over_2_to_n m n)) U1).
red; intros.
apply H5.
apply closure_inflationary; trivial.
contradiction H.
apply H6.
trivial.
assert ((m >= nat_of_P (pos_power2 n))%nat).
auto with *.
red in H3.
assert ((nat_of_P (pos_power2 n) < m \/
        (nat_of_P (pos_power2 n) = m))%nat).
apply le_lt_or_eq; trivial.
rewrite H1.
replace 1 with (Q2R (dr2Q (m_over_2_to_n 1 0))).
match goal with |- ?a >= ?b =>
  cut (b <= a); auto with real end.
apply Qle_Rle.
unfold dr2Q.
unfold Qle.
simpl.
ring_simplify.
rewrite Zpos_eq_Z_of_nat_o_nat_of_P.
auto with *.
simpl.
unfold Q2R.
simpl.
field.
destruct H0.
right; trivial.
Qed.

Lemma Urysohns_Lemma_function_continuous:
  continuous Urysohns_Lemma_function.
Proof.
apply continuous_subbasis with (order_topology_subbasis _ Rle).
apply Build_TopologicalSpace_from_subbasis_subbasis.
intros.
destruct H.

(* proving that inverse image of lower open interval is open *)
destruct (classic (x>1)).

(* if x>1, inverse image is everything *)
match goal with |- open ?U => assert (U = Full_set) end.
apply Extensionality_Ensembles; split; red; intros.
constructor.
constructor.
constructor.
cut (Urysohns_Lemma_function x0 < x); auto with real.
apply Rle_lt_trans with 1; trivial.
apply Urysohns_Lemma_function_range.
rewrite H0; apply open_full.

(* if x<=1, inverse image is union of U_alpha for alpha < x *)
assert (x<=1) by (apply Rnot_gt_le; trivial).
match goal with |- open ?U => assert (U =
  IndexedUnion (fun alpha:{alpha:dyadic_rational |
                           Q2R (dr2Q alpha) < x} =>
                U_dyadic (proj1_sig alpha))) end.
apply Extensionality_Ensembles; split; red; intros.
destruct H1.
destruct H1.
assert (Urysohns_Lemma_function x0 < x).
destruct H1.
destruct (Rdichotomy _ _ H2); trivial.
contradict H3.
auto with real.
clear H1.
remember (Urysohns_Lemma_function x0) as y.
unfold Urysohns_Lemma_function in Heqy.
destruct inf in Heqy; simpl in Heqy.
destruct Heqy.
destruct (glb_approx _ _ (x-y) i).
apply Rgt_minus; trivial.
destruct H1.
destruct H1.
destruct H1 as [alpha].
destruct H1.
destruct H3.
ring_simplify in H5.
rewrite H4 in H5.
exists (exist (fun beta:dyadic_rational => Q2R (dr2Q beta) < x)
  alpha H5).
trivial.
destruct H1.
destruct H3.
ring_simplify in H3.
contradiction H.

destruct H1 as [[alpha]].
simpl in H1.
constructor.
constructor.
cut (Urysohns_Lemma_function x0 < x); auto with real.
apply Rle_lt_trans with (2:=r).
unfold Urysohns_Lemma_function; destruct inf; simpl.
cut (Q2R (dr2Q alpha) >= x1); auto with real.
apply i.
left.
exists alpha; trivial.
constructor; trivial.

rewrite H1.
apply open_indexed_union.
intro.
apply U_dyadic_open.

(* proving that inverse image of upper open interval is open *)
destruct (classic (x<0)).
(* if x<0, inverse image is everything *)
match goal with |- open ?U => assert (U = Full_set) end.
apply Extensionality_Ensembles; split; red; intros.
constructor.
constructor.
constructor.
cut (x < Urysohns_Lemma_function x0); auto with real.
apply Rlt_le_trans with (1:=H).
apply Urysohns_Lemma_function_range.
rewrite H0; apply open_full.
assert (x >= 0) by now apply Rnot_lt_ge.
clear H.

(* if x>=1, inverse image is empty *)
destruct (classic (x>=1)).
match goal with |- open ?U => assert (U = Empty_set) end.
apply Extensionality_Ensembles; split; red; intros.
destruct H1.
destruct H1.
destruct H1.
assert (x < Urysohns_Lemma_function x0).
destruct (total_order_T x (Urysohns_Lemma_function x0)) as
  [[|]|]; trivial.
contradiction H2.
symmetry; trivial.
contradict r.
apply Rle_not_gt; trivial.
absurd (x < x).
apply Rlt_irrefl.
apply Rlt_le_trans with (Urysohns_Lemma_function x0); trivial.
apply Rle_trans with 1; auto with real.
apply Urysohns_Lemma_function_range.
destruct H1.
rewrite H1; apply open_empty.

(* if 0 <= x < 1, inverse image is union of
   Complement (closure U_alpha) for x < alpha < 1 *)
assert (x < 1) by now apply Rnot_ge_lt.
clear H.
match goal with |- open ?U => assert (U =
  IndexedUnion (fun alpha:{alpha:dyadic_rational |
                     x < Q2R (dr2Q alpha) < 1} =>
             (Complement (closure (U_dyadic (proj1_sig alpha))))))
 end.
apply Extensionality_Ensembles; split; red; intros.
destruct H.
destruct H.
destruct H.
remember (Urysohns_Lemma_function x0) as y.
assert (y <= 1) by (rewrite Heqy; apply Urysohns_Lemma_function_range).
unfold Urysohns_Lemma_function in Heqy;
  destruct inf in Heqy; simpl in Heqy.
destruct Heqy.
assert (x < y).
destruct (total_order_T x y) as [[|]|]; trivial.
contradiction H2.
symmetry; trivial.
contradict r.
apply Rle_not_gt; trivial.
destruct (dyadic_rationals_dense_in_reals x y) as [alpha].
split; auto with real.
assert (~ In (U_dyadic alpha) x0).
intro.
absurd (Q2R (dr2Q alpha) >= y).
destruct H5.
apply Rlt_not_ge; trivial.
apply i.
left.
exists alpha.
constructor; trivial.
trivial.
destruct (dyadic_rationals_dense_in_reals x (Q2R (dr2Q alpha)))
  as [beta].
split; auto with real.
apply H5.
assert (dr_lt beta alpha).
apply Qlt_dr_lt.
apply Rlt_Qlt.
apply H7.
pose proof (U_dyadic_incr _ _ H8).
assert (x < Q2R (dr2Q beta) < 1).
split.
apply H7.
apply Rlt_trans with (Q2R (dr2Q alpha)).
apply H7.
apply Rlt_le_trans with y; trivial.
apply H5.
exists (exist (fun alpha0:dyadic_rational =>
               x < Q2R (dr2Q alpha0) < 1)
        beta H10).
simpl.
intro.
contradiction H6.
apply H9; trivial.

destruct H.
destruct a as [alpha].
simpl in H.
constructor.
constructor.
cut (x < Urysohns_Lemma_function x0); auto with real.
apply Rlt_le_trans with (Q2R (dr2Q alpha)).
apply a.
unfold Urysohns_Lemma_function; destruct inf as [y]; simpl.
apply i.
red; intros.
destruct H2.
destruct H2 as [beta].
assert (dr_lt alpha beta \/ dr_eq alpha beta).
cut (~ dr_lt beta alpha).
destruct (dr_total_order alpha beta) as [|[|]]; auto.
intro.
contradiction H5.
intro.
pose proof (U_dyadic_incr _ _ H4).
destruct H2.
contradiction H.
apply closure_inflationary.
apply H5.
apply closure_inflationary; trivial.
destruct H4.
rewrite H3.
pose proof (dr2Q_incr _ _ H4).
cut (Q2R (dr2Q alpha) <= Q2R (dr2Q beta)); auto with *.
apply Qle_Rle.
auto with qarith.
rewrite H3.
cut (Q2R (dr2Q alpha) <= Q2R (dr2Q beta)); auto with *.
apply Qle_Rle.
pose proof (dr2Q_wd _ _ H4).
auto with *.
destruct H2.
destruct a.
auto with *.

rewrite H.
apply open_indexed_union.
intros.
apply closure_closed.
Qed.

End Urysohns_Lemma_construction.

Theorem UrysohnsLemma: forall X:TopologicalSpace, normal_sep X ->
  forall F G:Ensemble (point_set X),
  closed F -> closed G -> Intersection F G = Empty_set ->
  exists f:point_set X -> point_set RTop,
  continuous f /\ (forall x:point_set X, 0 <= f x <= 1) /\
  (forall x:point_set X, In F x -> f x = 0) /\
  (forall x:point_set X, In G x -> f x = 1).
Proof.
intros.
destruct H.
destruct (H3 F G H0 H1 H2) as [U [V [? [? [? [? ?]]]]]].
assert (Included (closure U) (Complement G)).
assert (Included (closure U) (Complement V)).
apply closure_minimal; trivial.
red; rewrite Complement_Complement; trivial.
red; intros.
intro.
absurd (In Empty_set x).
intro.
destruct H11.
rewrite <- H8; constructor; trivial.
assert (Included (Complement V) (Complement G)).
red; intros.
intro.
contradiction H10.
apply H7.
trivial.
auto with sets.

assert (inhabited (forall F U:Ensemble (point_set X), closed F ->
  open U -> Included F U ->
  { V:Ensemble (point_set X) | open V /\ Included F V /\
                               Included (closure V) U })).
Require Import ClassicalChoice.
destruct (choice (fun (FU_pair:
  {p:Ensemble (point_set X) * Ensemble (point_set X) |
   closed (fst p) /\ open (snd p) /\ Included (fst p) (snd p)})
  (V0:Ensemble (point_set X)) =>
   open V0 /\ Included (fst (proj1_sig FU_pair)) V0 /\
   Included (closure V0) (snd (proj1_sig FU_pair)))) as
  [pre_choice_fun].
intro p.
destruct p as [[F0 U0]].
simpl in a.
simpl.
destruct a as [? []].
destruct (H3 F0 (Complement U0)) as [U1 [V1 []]]; trivial.
red; rewrite Complement_Complement; trivial.
apply Extensionality_Ensembles; split; red; intros.
destruct H13.
contradiction H14.
apply H12; trivial.
destruct H13.
destruct H14 as [? [? []]].
exists U1.
repeat split; trivial.
assert (Included (closure U1) (Complement V1)).
apply closure_minimal; trivial.
red; rewrite Complement_Complement; trivial.
red; intros.
intro.
absurd (In Empty_set x).
intro H20; destruct H20.
rewrite <- H17; constructor; trivial.
assert (Included (Complement V1) U0).
red; intros.
apply NNPP; intro.
contradiction H19.
apply H16.
exact H20.
auto with sets.
exists.
intros.
exists (pre_choice_fun (exist _ (F0,U0)
  (conj H11 (conj H12 H13)))).
apply H10.
destruct H10 as [normal_sep_fun].

exists (Urysohns_Lemma_function _ normal_sep_fun
  U (Complement G) H4 H1 H9).
split.
apply Urysohns_Lemma_function_continuous.
split.
apply Urysohns_Lemma_function_range.
repeat split.
intros.
apply Urysohns_Lemma_function_0; auto.
intros.
apply Urysohns_Lemma_function_1; auto.
Qed.
