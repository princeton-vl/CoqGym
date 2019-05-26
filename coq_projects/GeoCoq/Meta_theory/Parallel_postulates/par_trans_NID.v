Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section par_trans_NID.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma par_dec_NID : decidability_of_parallelism <-> decidability_of_not_intersection.
Proof.
split; intros Hdec A B C D; destruct (cop_dec A B C D) as [|HNCop].
- destruct (Hdec A B C D) as [[HParS|Heq]|HNPar].
  * left; unfold Par_strict in HParS; spliter; assumption.
  * right; intro Habs; apply Habs; exists B; spliter; Col.
  * right; intro Habs.
    destruct (eq_dec_points A B).
      apply Habs; exists C; subst; split; Col.
    destruct (eq_dec_points C D).
      apply Habs; exists A; subst; split; Col.
    apply HNPar; left; unfold Par_strict; repeat split; assumption.

- left; intros [I []]; apply HNCop; exists I; left; split; Col.

- destruct (eq_dec_points A B).
    right; subst; intro; assert_diffs; auto.
  destruct (eq_dec_points C D).
    right; subst; intro; assert_diffs; auto.
  destruct (col_dec A C D).

  {
    destruct (col_dec B C D).
      left; right; repeat split; assumption.
    right; intros [[_ [_ [_ Habs]]]|].
      apply Habs; exists A; split; Col.
    spliter; auto.
  }

  destruct (Hdec A B C D) as [HPar|HNPar].
    left; left; repeat split; assumption.
  right.
  intros [HParS|Heq].
    apply HNPar; unfold Par_strict in HParS; spliter; assumption.
  spliter; auto.

- right; intro HPar; apply HNCop, par__coplanar, HPar.
Qed.

Lemma par_trans__par_dec :
  postulate_of_transitivity_of_parallelism ->
  decidability_of_parallelism.
Proof.
intros HTP A B C D.
elim (eq_dec_points A B); intro HAB;
[treat_equalities; right; intro; assert_diffs; intuition|].
elim (eq_dec_points C D); intro HCD;
[treat_equalities; right; intro; assert_diffs; intuition|].
destruct (parallel_existence1 A B C HAB) as [D' HPar].
elim (col_dec C D D'); intro HCol;
[left; apply par_col_par with D'; Par; Col|
 right; intro; apply HCol; apply par_id_3; apply HTP with A B; Par].
Qed.

Lemma col_int : forall A B C,
  Col A B C <-> ~ (~ Bet A B C /\ ~ Bet B C A /\ ~ Bet C A B).
Proof.
intros A B C; unfold Col.
induction (bet_dec A B C); induction (bet_dec B C A); induction (bet_dec C A B);
intuition.
Qed.

Definition playfair_ter := forall A1 A2 B1 B2 C1 C2 P,
  A1 <> A2 -> B1 <> B2 -> C1 <> C2 ->
  Col P B1 B2 -> Col P C1 C2 ->
  ~ (Col A1 B1 B2 /\ Col A2 B1 B2) ->
  ~ (Col A1 C1 C2 /\ Col A2 C1 C2) ->
  ~ (Col C1 B1 B2 /\ Col C2 B1 B2) ->
  (exists I, ~ (~ (Col A1 A2 I /\ Col B1 B2 I) /\
                ~ (Col A1 B1 I /\ Col A2 B2 I) /\
                ~ (Col A1 B2 I /\ Col A2 B1 I))) ->
  (exists I, ~ (~ (Col A1 A2 I /\ Col C1 C2 I) /\
               ~ (Col A1 C1 I /\ Col A2 C2 I) /\
               ~ (Col A1 C2 I /\ Col A2 C1 I))) ->
  ~ (~ (exists I, Col I A1 A2 /\ Col I B1 B2) /\
     ~ (exists I, Col I A1 A2 /\ Col I C1 C2)).

Definition playfair_quater_qf A1 A2 B1 B2 C1 C2 P :=
  A1 <> A2 /\ B1 <> B2 /\ C1 <> C2 /\
  Col P B1 B2 /\ Col P C1 C2 /\
  ~ (Col A1 B1 B2 /\ Col A2 B1 B2) /\
  ~ (Col A1 C1 C2 /\ Col A2 C1 C2) /\
  ~ (Col C1 B1 B2 /\ Col C2 B1 B2) /\
  (exists I, ~ (~ (Col A1 A2 I /\ Col B1 B2 I) /\
                ~ (Col A1 B1 I /\ Col A2 B2 I) /\
                ~ (Col A1 B2 I /\ Col A2 B1 I))) /\
  (exists I, ~ (~ (Col A1 A2 I /\ Col C1 C2 I) /\
                ~ (Col A1 C1 I /\ Col A2 C2 I) /\
                ~ (Col A1 C2 I /\ Col A2 C1 I))) /\
  ~ (exists I, Col I A1 A2 /\ Col I B1 B2) /\
  ~ (exists I, Col I A1 A2 /\ Col I C1 C2).

Definition playfair_quater := ~ exists A1 A2 B1 B2 C1 C2 P,
  playfair_quater_qf A1 A2 B1 B2 C1 C2 P.

Lemma playfair__playfair_ter :
  playfair_s_postulate -> playfair_ter.
Proof.
intros HP A1 A2 B1 B2 C1 C2 P HA HB HC HP1 HP2 HNC1 HNC2 HNC3 HIAB HIAC.
intros [HAB HAC]. apply HNC3.
apply (HP A1 A2 B1 B2 C1 C2 P); Col; left;
repeat (split; Col).

  {
  destruct HIAB as [IAB HIAB]; exists IAB.
  clear HA HB HC HP1 HP2 HNC1 HNC2 HNC3 HIAC HAB HAC P C1 C2.
  induction (col_dec A1 A2 IAB); induction (col_dec B1 B2 IAB);
  try solve [left; Col];
  induction (col_dec A1 B1 IAB); induction (col_dec A2 B2 IAB);
  try solve [right; left; Col];
  induction (col_dec A1 B2 IAB); induction (col_dec A2 B1 IAB);
  try solve [right; right; Col];
  exfalso; apply HIAB; intuition.
  }

  {
  destruct HIAC as [IAC HIAC]; exists IAC.
  clear HA HB HC HP1 HP2 HNC1 HNC2 HNC3 HIAB HAB HAC P B1 B2.
  induction (col_dec A1 A2 IAC); induction (col_dec C1 C2 IAC);
  try solve [left; Col];
  induction (col_dec A1 C1 IAC); induction (col_dec A2 C2 IAC);
  try solve [right; left; Col];
  induction (col_dec A1 C2 IAC); induction (col_dec A2 C1 IAC);
  try solve [right; right; Col];
  exfalso; apply HIAC; intuition.
  }
Qed.

Lemma playfair__playfair_quater :
  playfair_s_postulate -> playfair_quater.
Proof.
intro HP; intro HPQ; destruct HPQ as [A1 [A2 [B1 [B2 [C1 [C2 [P HPQ]]]]]]].
assert (H:= HP A1 A2 B1 B2 C1 C2 P); clear HP.
destruct HPQ as [HD1 [HD2 [HD3 [HC1 [HC2 [HNC1 [HNC2 [HNC3 HPQ]]]]]]]].
destruct HPQ as [HIAB [HIAC [HNI1 HNI2]]].
apply HNC3; apply H; clear H; Col; left;
repeat (split; try assumption); auto.


  {
  destruct HIAB as [IAB HIAB]; exists IAB.
  clear HD1 HD2 HD3 HC1 HC2 HNC1 HNC2 HNC3 HIAC HNI1 HNI2 P C1 C2.
  induction (col_dec A1 A2 IAB); induction (col_dec B1 B2 IAB);
  try solve [left; Col];
  induction (col_dec A1 B1 IAB); induction (col_dec A2 B2 IAB);
  try solve [right; left; Col];
  induction (col_dec A1 B2 IAB); induction (col_dec A2 B1 IAB);
  try solve [right; right; Col];
  exfalso; apply HIAB; intuition.
  }

  {
  destruct HIAC as [IAC HIAC]; exists IAC.
  clear HD1 HD2 HD3 HC1 HC2 HNC1 HNC2 HNC3 HIAB HNI1 HNI2 P B1 B2.
  induction (col_dec A1 A2 IAC); induction (col_dec C1 C2 IAC);
  try solve [left; Col];
  induction (col_dec A1 C1 IAC); induction (col_dec A2 C2 IAC);
  try solve [right; left; Col];
  induction (col_dec A1 C2 IAC); induction (col_dec A2 C1 IAC);
  try solve [right; right; Col];
  exfalso; apply HIAC; intuition.
  }
Qed.

Lemma playfair_ter__playfair :
  playfair_ter -> playfair_s_postulate.
Proof.
intros HP A1 A2 B1 B2 C1 C2 P HPar1 HP1 HPar2 HP2.
elim (col_dec A1 B1 B2); intro HNC1.

  {
  assert (HA : A1 <> A2) by (assert_diffs; auto).
  assert (HB : B1 <> B2) by (assert_diffs; auto).
  assert (HC : C1 <> C2) by (assert_diffs; auto).
  apply (not_strict_par _ _ _ _ A1) in HPar1; Col.
  destruct HPar1 as [HC1 HC2]; clear HNC1.
  apply (not_strict_par _ _ _ _ P) in HPar2; spliter; try split; ColR.
  }

  {
  elim (col_dec A1 C1 C2); intro HNC2.

    {
    assert (HA : A1 <> A2) by (assert_diffs; auto).
    assert (HB : B1 <> B2) by (assert_diffs; auto).
    assert (HC : C1 <> C2) by (assert_diffs; auto).
    apply (not_strict_par _ _ _ _ A1) in HPar2; Col.
    destruct HPar2 as [HC1 HC2]; clear HNC2.
    apply (not_strict_par _ _ _ _ P) in HPar1; spliter; try split; ColR.
    }

    {
    assert (H : ~ ~ (Col C1 B1 B2 /\ Col C2 B1 B2) ->
                Col C1 B1 B2 /\ Col C2 B1 B2);
    [induction (col_dec C1 B1 B2); induction (col_dec C2 B1 B2); intuition|
     apply H; clear H; intro HNC3; apply (HP A1 A2 B1 B2 C1 C2 P);
     try solve [assert_diffs; Col]; try (intros [HC1 HC2]; intuition)].

      {
      apply par_symmetry in HPar1.
      apply (par_not_col_strict _ _ _ _ A1) in HPar1; Col.
      destruct HPar1 as [_ [_ [[IAB HIAB] _]]].
      exists IAB; intros [HIAB1 [HIAB2 HIAB3]].
      elim HIAB; clear HIAB; intro HIAB; [apply HIAB1|];
      try solve [spliter; split; Col].
      elim HIAB; clear HIAB; intro HIAB; [apply HIAB2|apply HIAB3];
      spliter; split; Col.
      }

      {
      apply par_symmetry in HPar2.
      apply (par_not_col_strict _ _ _ _ A1) in HPar2; Col.
      destruct HPar2 as [_ [_ [[IAC HIAC] _]]].
      exists IAC; intros [HIAC1 [HIAC2 HIAC3]].
      elim HIAC; clear HIAC; intro HIAC; [apply HIAC1|];
      try solve [spliter; split; Col].
      elim HIAC; clear HIAC; intro HIAC; [apply HIAC2|apply HIAC3];
      spliter; split; Col.
      }

      {
      apply par_symmetry in HPar1; apply par_symmetry in HPar2.
      apply (par_not_col_strict _ _ _ _ A1) in HPar1; Col.
      apply (par_not_col_strict _ _ _ _ A1) in HPar2; Col.
      destruct HPar1 as [_ [_ [_ HI1]]]; destruct HPar2 as [_ [_ [_ HI2]]].
      split; intros [I [HC1 HC2]]; [apply HI1| apply HI2]; exists I; Col.
      }
    }
  }
Qed.

Lemma not_ex_forall_not_7 :
  forall (T : Type) (P : T -> T -> T -> T -> T -> T -> T -> Prop),
  ~(exists x1 : T, exists x2 : T, exists x3 : T,
    exists x4 : T, exists x5 : T, exists x6 : T,
    exists x7 :T, P x1 x2 x3 x4 x5 x6 x7) <->
  forall x1 : T, forall x2 : T, forall x3 : T,
  forall x4 : T, forall x5 : T, forall x6 : T,
  forall x7 : T, ~ P x1 x2 x3 x4 x5 x6 x7.
Proof.
intros; split; intro H1; intros; intro H2;
[apply H1; exists x1, x2, x3, x4, x5, x6, x7; auto|].
destruct H2 as [x1 [x2 [x3 [x4 [x5 [x6 [x7 H2]]]]]]].
apply (H1 x1 x2 x3 x4 x5 x6 x7); auto.
Qed.

Lemma playfair_quater__playfair :
  playfair_quater -> playfair_s_postulate.
Proof.
intros HP A1 A2 B1 B2 C1 C2 P HPar1 HP1 HPar2 HP2.
assert (H : playfair_quater <->
              forall A1 A2 B1 B2 C1 C2 P,
                ~ playfair_quater_qf A1 A2 B1 B2 C1 C2 P)
  by (apply not_ex_forall_not_7). rewrite H in HP; clear H.
assert (H : Col C1 B1 B2 /\ Col C2 B1 B2 <-> ~ ~ (Col C1 B1 B2 /\ Col C2 B1 B2))
  by (induction (col_dec C1 B1 B2); induction (col_dec C2 B1 B2); tauto).
apply H; clear H; intro HNC; apply (HP A1 A2 B1 B2 C1 C2 P).
repeat try (split; [assert_diffs; assumption|]).
assert (HNC1 : ~ Col A1 B1 B2).
  {
  intro.
  assert (HA : A1 <> A2) by (assert_diffs; auto).
  assert (HB : B1 <> B2) by (assert_diffs; auto).
  assert (HC : C1 <> C2) by (assert_diffs; auto).
  apply (not_strict_par _ _ _ _ A1) in HPar1; Col; spliter.
  apply (not_strict_par _ _ _ _ P) in HPar2; spliter; try ColR.
  apply HNC; split; ColR.
  }
assert (HNC2 : ~ Col A2 B1 B2).
  {
  intro.
  assert (HA : A1 <> A2) by (assert_diffs; auto).
  assert (HB : B1 <> B2) by (assert_diffs; auto).
  assert (HC : C1 <> C2) by (assert_diffs; auto).
  apply (not_strict_par _ _ _ _ A2) in HPar1; Col; spliter.
  apply (not_strict_par _ _ _ _ P) in HPar2; spliter; try ColR.
  apply HNC; split; ColR.
  }
assert (HNC3 : ~ Col A1 C1 C2).
  {
  intro.
  assert (HA : A1 <> A2) by (assert_diffs; auto).
  assert (HB : B1 <> B2) by (assert_diffs; auto).
  assert (HC : C1 <> C2) by (assert_diffs; auto).
  apply (not_strict_par _ _ _ _ A1) in HPar2; Col; spliter.
  apply (not_strict_par _ _ _ _ P) in HPar1; spliter; try ColR.
  apply HNC; split; ColR.
  }
assert (HNC4 : ~ Col A2 C1 C2).
  {
  intro.
  assert (HA : A1 <> A2) by (assert_diffs; auto).
  assert (HB : B1 <> B2) by (assert_diffs; auto).
  assert (HC : C1 <> C2) by (assert_diffs; auto).
  apply (not_strict_par _ _ _ _ A2) in HPar2; Col; spliter.
  apply (not_strict_par _ _ _ _ P) in HPar1; spliter; try ColR.
  apply HNC; split; ColR.
  }
apply par_symmetry in HPar1; apply (par_not_col_strict _ _ _ _ A1) in HPar1;
Col; apply par_strict_symmetry in HPar1; destruct HPar1 as [_ [_ [HCop1 HPar1]]].
apply par_symmetry in HPar2; apply (par_not_col_strict _ _ _ _ A1) in HPar2;
Col; apply par_strict_symmetry in HPar2; destruct HPar2 as [_ [_ [HCop2 HPar2]]].
repeat (split; try tauto).

  {
  destruct HCop1 as [IAB HIAB].
  exists IAB; intros [HIAB1 [HIAB2 HIAB3]].
  elim HIAB; clear HIAB; intro HIAB; [apply HIAB1|];
  try solve [spliter; split; Col].
  elim HIAB; clear HIAB; intro HIAB; [apply HIAB2|apply HIAB3];
  spliter; split; Col.
  }

  {
  destruct HCop2 as [IAC HIAC].
  exists IAC; intros [HIAC1 [HIAC2 HIAC3]].
  elim HIAC; clear HIAC; intro HIAC; [apply HIAC1|];
  try solve [spliter; split; Col].
  elim HIAC; clear HIAC; intro HIAC; [apply HIAC2|apply HIAC3];
  spliter; split; Col.
  }
Qed.

End par_trans_NID.