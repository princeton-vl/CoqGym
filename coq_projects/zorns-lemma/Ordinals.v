Require Import Classical.

Inductive Ordinal : Type :=
  | ordS : Ordinal -> Ordinal
  | ord_sup: forall {I:Type}, (I->Ordinal) -> Ordinal.

(*
Fixpoint ord_le (alpha beta:Ordinal) : Prop :=
  match alpha with
  | ordS alpha => 
                  (fix gt_alpha (beta:Ordinal) : Prop :=
                  match beta with
                  | ordS beta => ord_le alpha beta
                  | ord_sup J beta => exists j:J,
                    gt_alpha (beta j)
                  end) beta
  | ord_sup I0 alpha => forall i:I0, ord_le (alpha i) beta
  end.
*)

Inductive ord_le : Ordinal -> Ordinal -> Prop :=
  | ord_le_respects_succ: forall alpha beta:Ordinal,
    ord_le alpha beta -> ord_le (ordS alpha) (ordS beta)
  | ord_le_S_sup: forall (alpha:Ordinal) (J:Type)
    (beta:J->Ordinal) (j:J), ord_le (ordS alpha) (beta j) ->
    ord_le (ordS alpha) (ord_sup beta)
  | ord_sup_minimal: forall (I:Type) (alpha:I->Ordinal)
    (beta:Ordinal), (forall i:I, ord_le (alpha i) beta) ->
                    ord_le (ord_sup alpha) beta.

Definition ord_lt (alpha beta:Ordinal) :=
  ord_le (ordS alpha) beta.
Definition ord_eq (alpha beta:Ordinal) :=
  ord_le alpha beta /\ ord_le beta alpha.
Definition ord_ge (alpha beta:Ordinal) :=
  ord_le beta alpha.
Definition ord_gt (alpha beta:Ordinal) :=
  ord_lt beta alpha.

Delimit Scope ordinal_scope with Ordinal.
Open Scope ordinal_scope.
Notation "alpha < beta" := (ord_lt alpha beta) : ordinal_scope.
Notation "alpha <= beta" := (ord_le alpha beta) : ordinal_scope.
Notation "alpha == beta" := (ord_eq alpha beta)
  (at level 70) : ordinal_scope.
Notation "alpha > beta" := (ord_gt alpha beta) : ordinal_scope.
Notation "alpha >= beta" := (ord_ge alpha beta) : ordinal_scope.

Lemma ord_le_respects_succ_converse: forall alpha beta:Ordinal,
  ordS alpha <= ordS beta -> alpha <= beta.
Proof.
intros.
inversion_clear H.
assumption.
Qed.

Lemma ord_le_S_sup_converse: forall (alpha:Ordinal)
  (J:Type) (beta:J->Ordinal), ordS alpha <= ord_sup beta ->
  exists j:J, ordS alpha <= beta j.
Proof.
intros.
inversion H.
exists j.
assumption.
Qed.

Lemma ord_sup_minimal_converse: forall (I:Type)
  (alpha:I->Ordinal) (beta:Ordinal),
  ord_sup alpha <= beta -> forall i:I, alpha i <= beta.
Proof.
intros.
inversion H.
Require Import Eqdep.
apply inj_pair2 in H2.
destruct H2.
apply H3.
Qed.

Lemma ord_le_trans: forall alpha beta gamma:Ordinal,
  alpha <= beta -> beta <= gamma -> alpha <= gamma.
Proof.
induction alpha.
induction beta.
induction gamma.
intros.
apply ord_le_respects_succ.
apply IHalpha with beta.
apply ord_le_respects_succ_converse; trivial.
apply ord_le_respects_succ_converse; trivial.
intros.
apply ord_le_S_sup_converse in H1.
destruct H1 as [i].
apply ord_le_S_sup with i.
apply H; trivial.
intros.
pose proof (ord_sup_minimal_converse _ _ _ H1).
apply ord_le_S_sup_converse in H0.
destruct H0 as [i].
apply H with i; trivial.
intros.
pose proof (ord_sup_minimal_converse _ _ _ H0).
constructor.
intro.
apply H with beta; trivial.
Qed.

Lemma ord_le_sup: forall (I:Type) (alpha:I->Ordinal) (i:I),
  alpha i <= ord_sup alpha.
Proof.
assert (forall beta:Ordinal, beta <= beta /\
  forall (I:Type) (alpha:I->Ordinal) (i:I),
  beta <= alpha i -> beta <= ord_sup alpha).
induction beta.
destruct IHbeta.
split.
apply ord_le_respects_succ; trivial.
intros.
apply ord_le_S_sup with i.
trivial.
split.
apply ord_sup_minimal.
intro.
destruct (H i).
apply H1 with i; trivial.
intros J alpha j ?.
apply ord_sup_minimal.
intro.
destruct (H i).
apply H2 with j.
apply ord_le_trans with (ord_sup o).
apply H2 with i; trivial.
trivial.

intros.
destruct (H (alpha i)).
apply H1 with i; trivial.
Qed.

Lemma ord_le_refl: forall alpha:Ordinal, alpha <= alpha.
Proof.
induction alpha.
apply ord_le_respects_succ; trivial.
apply ord_sup_minimal.
apply ord_le_sup.
Qed.

Lemma ord_le_S: forall alpha:Ordinal, alpha <= ordS alpha.
Proof.
induction alpha.
apply ord_le_respects_succ; trivial.
apply ord_sup_minimal.
intro.
apply ord_le_trans with (ordS (o i)).
apply H.
apply ord_le_respects_succ.
apply ord_le_sup.
Qed.

Lemma ord_lt_le: forall alpha beta:Ordinal,
  alpha < beta -> alpha <= beta.
Proof.
intros.
apply ord_le_trans with (ordS alpha); trivial.
apply ord_le_S.
Qed.

Lemma ord_lt_le_trans: forall alpha beta gamma:Ordinal,
  alpha < beta -> beta <= gamma -> alpha < gamma.
Proof.
intros.
apply ord_le_trans with beta; trivial.
Qed.

Lemma ord_le_lt_trans: forall alpha beta gamma:Ordinal,
  alpha <= beta -> beta < gamma -> alpha < gamma.
Proof.
intros.
apply ord_le_trans with (ordS beta); trivial.
apply ord_le_respects_succ; trivial.
Qed.

Lemma ord_lt_trans: forall alpha beta gamma:Ordinal,
  alpha < beta -> beta < gamma -> alpha < gamma.
Proof.
intros.
apply ord_lt_le_trans with beta; trivial;
 apply ord_lt_le; trivial.
Qed.

Lemma ord_lt_respects_succ: forall alpha beta:Ordinal,
  alpha < beta -> ordS alpha < ordS beta.
Proof.
intros.
apply ord_le_respects_succ; trivial.
Qed.

Lemma ord_total_order: forall alpha beta:Ordinal,
  alpha < beta \/ alpha == beta \/ alpha > beta.
Proof.
induction alpha.
induction beta.
destruct (IHalpha beta) as [|[|]].
left; apply ord_lt_respects_succ; trivial.
right; left.
split.
apply ord_le_respects_succ; apply H.
apply ord_le_respects_succ; apply H.
right; right.
apply ord_lt_respects_succ; trivial.

destruct (classic (exists i:I, ordS alpha < o i)).
destruct H0 as [i].
left.
apply ord_lt_le_trans with (o i); trivial.
apply ord_le_sup.
destruct (classic (exists i:I, ordS alpha == o i)).
destruct H1 as [i].
right; left.
split.
apply ord_le_trans with (o i).
apply H1.
apply ord_le_sup.
apply ord_sup_minimal.
intro.
destruct (H i0) as [|[|]].
contradiction H0; exists i0; trivial.
apply H2.
apply ord_lt_le; trivial.
assert (forall i:I, ordS alpha > o i).
intros.
destruct (H i) as [|[|]].
contradiction H0; exists i; trivial.
contradiction H1; exists i; trivial.
trivial.
right; right.
apply ord_le_lt_trans with alpha.
apply ord_sup_minimal.
intro.
apply ord_le_respects_succ_converse.
apply H2.
apply ord_le_refl.

induction beta.
case (classic (exists i:I, o i > ordS beta)); intro.
destruct H0 as [i].
right; right.
apply ord_lt_le_trans with (o i); trivial.
apply ord_le_sup.
case (classic (exists i:I, o i == ordS beta)); intro.
right; left.
destruct H1 as [i].
split.
apply ord_sup_minimal.
intro j.
destruct (H j (ordS beta)) as [|[|]].
apply ord_lt_le; trivial.
apply H2.
contradiction H0; exists j; trivial.
apply ord_le_trans with (o i).
apply H1.
apply ord_le_sup.
left.
apply ord_le_respects_succ.
apply ord_sup_minimal.
intro.
destruct (H i (ordS beta)) as [|[|]].
apply ord_le_respects_succ_converse; trivial.
contradiction H1; exists i; trivial.
contradiction H0; exists i; trivial.

case (classic (exists j:I0, ord_sup o < o0 j)); intro.
left.
destruct H1 as [j].
apply ord_lt_le_trans with (o0 j); trivial.
apply ord_le_sup.
case (classic (exists i:I, o i > ord_sup o0)); intro.
destruct H2 as [i].
right; right.
apply ord_lt_le_trans with (o i); trivial.
apply ord_le_sup.

right; left.
split.
apply ord_sup_minimal; intro.
destruct (H i (ord_sup o0)) as [|[|]].
apply ord_lt_le; trivial.
apply H3.
contradiction H2; exists i; trivial.
apply ord_sup_minimal; intro j.
destruct (H0 j) as [|[|]].
contradiction H1; exists j; trivial.
apply H3.
apply ord_lt_le; trivial.
Qed.

Lemma ordinals_well_founded: well_founded ord_lt.
Proof.
red; intro alpha.
induction alpha.
constructor.
intros beta ?.
apply ord_le_respects_succ_converse in H.
constructor; intros gamma ?.
destruct IHalpha.
apply H1.
apply ord_lt_le_trans with beta; trivial.

constructor; intros alpha ?.
apply ord_le_S_sup_converse in H0.
destruct H0 as [j].

destruct (H j).
apply H1; trivial.
Qed.

Lemma ord_lt_irrefl: forall alpha:Ordinal, ~(alpha < alpha).
Proof.
intro; red; intro.
assert (forall beta:Ordinal, beta <> alpha).
intro.
pose proof (ordinals_well_founded beta).
induction H0.
red; intro.
symmetry in H2; destruct H2.
contradiction (H1 alpha H); trivial.
contradiction (H0 alpha); trivial.
Qed.

Inductive successor_ordinal : Ordinal->Prop :=
  | intro_succ_ord: forall alpha:Ordinal,
    successor_ordinal (ordS alpha)
  | succ_ord_wd: forall alpha beta:Ordinal,
    successor_ordinal alpha -> alpha == beta ->
    successor_ordinal beta.
Inductive limit_ordinal : Ordinal->Prop :=
  | intro_limit_ord: forall {I:Type} (alpha:I->Ordinal),
    (forall i:I, exists j:I, alpha i < alpha j) ->
    limit_ordinal (ord_sup alpha)
  | limit_ord_wd: forall alpha beta:Ordinal,
    limit_ordinal alpha -> alpha == beta ->
    limit_ordinal beta.

Lemma ord_successor_or_limit: forall alpha:Ordinal,
  successor_ordinal alpha \/ limit_ordinal alpha.
Proof.
induction alpha.
left; constructor.
destruct (classic (forall i:I, exists j:I, o i < o j)).
right; constructor; trivial.
destruct (not_all_ex_not _ _ H0) as [i].
assert (forall j:I, o j <= o i).
intro.
destruct (ord_total_order (o i) (o j)) as [|[|]].
contradiction H1; exists j; trivial.
apply H2.
apply ord_lt_le; trivial.

assert (ord_sup o == o i).
split.
apply ord_sup_minimal; trivial.
apply ord_le_sup.
case (H i); intro.
left; apply succ_ord_wd with (o i); trivial.
split; apply H3.
right.
apply limit_ord_wd with (o i); trivial.
split; apply H3.
Qed.

Lemma successor_ordinal_not_limit: forall alpha:Ordinal,
  successor_ordinal alpha -> ~ limit_ordinal alpha.
Proof.
intros; red; intro.
induction H.
inversion_clear H0.
induction H as [I beta|].
assert (ord_sup beta <= alpha).
apply ord_sup_minimal.
intro.
apply ord_le_respects_succ_converse.
destruct (H i) as [j].
apply ord_le_trans with (beta j); trivial.
apply ord_le_trans with (ord_sup beta).
apply ord_le_sup.
apply H1.

contradiction (ord_lt_irrefl alpha).
apply ord_le_trans with (ord_sup beta); trivial.
apply H1.

apply IHlimit_ordinal.
split; apply ord_le_trans with beta;
  (apply H0 || apply H1).

contradiction IHsuccessor_ordinal.
apply limit_ord_wd with beta; trivial.
split; apply H1.
Qed.
