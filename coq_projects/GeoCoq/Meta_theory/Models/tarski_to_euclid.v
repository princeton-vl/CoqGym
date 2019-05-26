Require Import GeoCoq.Tarski_dev.Ch12_parallel.
Require Import GeoCoq.Axioms.euclidean_axioms.
Require Export GeoCoq.Axioms.continuity_axioms.
Require Export GeoCoq.Meta_theory.Continuity.elementary_continuity_props.
Require Export GeoCoq.Meta_theory.Parallel_postulates.parallel_postulates.

Section Tarski_neutral_to_Euclid_neutral.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.


Definition Tcircle : Type := Tpoint*Tpoint*Tpoint %type.

Definition OnCirc P (C:Tcircle) := 
  match C with 
  (X,A,B) => tarski_axioms.Cong X P A B
  end.

Definition CI (J:Tcircle) A C D := J=(A,C,D) /\ C<>D.

Definition InCirc P (J:Tcircle) :=
   match J with
  (C,A,B) => 
   exists X Y, Definitions.BetS X C Y /\ tarski_axioms.Cong C Y A B /\
               tarski_axioms.Cong C X A B /\ Definitions.BetS X P Y
  end.

Definition OutCirc P (J:Tcircle) :=
   match J with
  (C,A,B) => 
      exists X, Definitions.BetS C X P /\ tarski_axioms.Cong C X A B
 end.

Lemma on : 
 forall A B C D J, CI J A C D /\ OnCirc B J ->
                   tarski_axioms.Cong A B C D.
Proof.
intros.
unfold CI,OnCirc in *.
destruct J.
destruct p.
spliter.
congruence.
Qed.

Lemma inside : forall A B C J P,
  CI J C A B /\ InCirc P J <-> 
  exists X Y, CI J C A B /\ 
   Definitions.BetS X C Y /\ 
   tarski_axioms.Cong C Y A B /\ 
   tarski_axioms.Cong C X A B /\ 
   Definitions.BetS X P Y.
Proof.
intros.
unfold InCirc, CI.
destruct J;destruct p.
split.
intros;spliter.
decompose [ex and] H0;clear H0.
exists x. exists x0.
inversion H; subst; auto.
intros.
decompose [ex and] H;clear H.
inversion H1; subst;split; auto.
exists x; exists x0;auto.
Qed.


Lemma outside : forall A B C J P,
  CI J C A B /\ OutCirc P J <->
  exists X, CI J C A B /\ Definitions.BetS C X P /\
   tarski_axioms.Cong C X A B.
Proof.
intros.
unfold OutCirc, CI.
destruct J;destruct p.
split.
intros;spliter.
decompose [ex and] H0;clear H0.
exists x.
inversion H; subst; auto.
intros.
decompose [ex and] H;clear H.
inversion H0; subst;split; auto.
exists x;auto.
Qed.



End Tarski_neutral_to_Euclid_neutral.

Section circle_continuity.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma bet_cases : forall B C D1 D2,
 C<>B ->
 Definitions.BetS D1 B D2 ->
 Definitions.BetS D1 C D2 ->
 Definitions.BetS D1 B C \/ Definitions.BetS C B D2.
Proof.
intros.
assert (T:Bet D1 C B \/ Bet D1 B C).
  apply (l5_3 D1 C B D2);unfold Definitions.BetS in *;spliter;finish.
 destruct T.
 right.
 unfold Definitions.BetS in *;spliter.
 assert (Bet C B D2)
  by (eBetween).
 unfold Definitions.BetS.
 repeat split;auto.
 left.
 unfold Definitions.BetS.
 unfold Definitions.BetS in *;spliter;repeat split;auto.
Qed.

Lemma circle_line :
 circle_circle ->
 forall A B C K P Q,
    CI K C P Q -> InCirc B K ->  A <> B ->
    exists X Y, Definitions.Col A B X /\ Definitions.Col A B Y /\
  OnCirc X K /\ OnCirc Y K /\ Definitions.BetS X B Y.
Proof.
intros.
apply circle_circle__circle_circle_bis in H.
apply circle_circle_bis__one_point_line_circle in H.
apply one_point_line_circle__two_points_line_circle in H.
unfold CI in *.
destruct K.
destruct p.
spliter.
injection H0.
intros;subst.
unfold InCirc in *.
unfold two_points_line_circle in H.

destruct H1 as [D1 [D2 [HBetS [HCongA [HCongB HBetSB]]]]].
destruct (eq_dec_points B C).
subst.
assert (HColD: Definitions.Col A C C)
   by (unfold Definitions.Col;Between).
assert (HBet: Bet C C D2) by Between.
destruct (H C D2 A C C HColD H2 HBet) as [Z1 [Z2 HZ]].
spliter.
exists Z1. exists Z2.
repeat split;try assumption.
unfold OnCircle, OnCirc in *;eCong.
unfold OnCircle, OnCirc in *;eCong.
assert (C<>D2)
 by (unfold Definitions.BetS in *;spliter;auto).
assert (Z1<>Z2) by auto.
unfold OnCircle in *.
intro;treat_equalities;intuition.
unfold OnCircle in *.
intro;treat_equalities.
unfold Definitions.BetS in *;intuition.
assert (TwoCases:Definitions.BetS D1 B C \/ Definitions.BetS C B D2)
 by (apply bet_cases;auto).
destruct TwoCases.
- assert (HColD: Definitions.Col A B B)
   by (unfold Definitions.Col;Between).
assert (HBet:Bet C B D1)
 by (unfold Definitions.BetS in *;spliter;finish).
destruct (H C D1 A B B HColD H2 HBet)
 as [Z1 [Z2 HZ]].
exists Z1.
exists Z2.
spliter.
assert (B<>D1)
 by (unfold Definitions.BetS in *;spliter;auto).
assert (Z1<>Z2) by auto.
assert (Z1<>B).
{
 intro. subst.
 unfold OnCircle in *.
 assert (B=D1) by (apply between_cong with C;finish).
 subst. intuition.
}
assert_diffs.
assert (B<>Z2).
{
 intro. subst.
 assert (Bet C Z2 D1) 
  by (unfold BetS in *;spliter;finish).
 unfold OnCircle in *.
 assert (Z2=D1)
  by (apply between_cong with C;finish).
 intuition.
}
assert (Definitions.BetS Z1 B Z2)
 by (unfold Definitions.BetS;auto).
unfold OnCirc;simpl.
unfold OnCircle in *.
repeat split; eCong.
- assert (HColD: Definitions.Col A B B)
   by (unfold Definitions.Col;Between).
assert (HBet:Bet C B D2)
 by (unfold Definitions.BetS in *;spliter;finish).
destruct (H C D2 A B B HColD H2 HBet)
 as [Z1 [Z2 HZ]].
exists Z1.
exists Z2.
spliter.
assert (B<>D2)
 by (unfold Definitions.BetS in *;spliter;auto).
assert (Z1<>Z2) by auto.
assert (Z1<>B).
{
 intro. subst.
 unfold OnCircle in *.
 assert (B=D2) by (apply between_cong with C;finish).
 subst. intuition.
}
assert_diffs.
assert (B<>Z2).
{
 intro. subst.
 assert (Bet C Z2 D2) 
  by (unfold BetS in *;spliter;finish).
 unfold OnCircle in *.
 assert (Z2=D2)
  by (apply between_cong with C;finish).
 intuition.
}
assert (Definitions.BetS Z1 B Z2)
 by (unfold Definitions.BetS;auto).
unfold OnCirc;simpl.
unfold OnCircle in *.
repeat split; eCong.
Qed.

Lemma circle_circle' :
 circle_circle ->
 forall C D F G J K P Q R S,
    CI J C R S -> InCirc P J ->
    OutCirc Q J -> CI K D F G ->
    OnCirc P K -> OnCirc Q K ->
    exists X, OnCirc X J /\ OnCirc X K.
Proof.
intros.
unfold circle_circle in H.
destruct J.
destruct p.
destruct K.
destruct p.
unfold CI in *.
spliter.
injection H0;intros;subst.
injection H3;intros;subst.
clear H0 H3.
unfold OnCirc in *.
unfold InCirc in *.
destruct H1 as [D1 [D2 HD]].
spliter.
unfold OutCirc in *.
destruct H2 as [X HX].
spliter.
assert (OnCircle P D Q)
 by (unfold OnCircle;eCong).
assert (OnCircle Q D Q)
 by (unfold OnCircle;eCong).
assert (InCircle P C D1).
{
 unfold InCircle.
 destruct (eq_dec_points C P).
 subst. apply le_trivial.
 assert (TwoCases:Definitions.BetS D1 P C \/ Definitions.BetS C P D2)
  by (apply bet_cases;auto).
 destruct TwoCases.
 exists P.
 split; unfold Definitions.BetS in *;spliter; finish.
 apply l5_6 with C P C D2.
 exists P.
 split; unfold Definitions.BetS in *;spliter; finish.
 finish.
 eCong.
}
assert (OutCircle Q C D1).
{
 unfold OutCircle.
 exists X.
 split; unfold Definitions.BetS in *;spliter; eCong.
}
assert (Hex: exists Z : Tpoint, OnCircle Z C D1 /\ OnCircle Z D Q) by eauto.
destruct Hex as [Z HZ].
exists Z.
unfold OnCircle in *;spliter;split;eCong.
Qed.

End circle_continuity.

Section Neutral.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Global Instance Euclid_neutral_follows_from_Tarski_neutral : euclidean_neutral.
Proof.
eapply (Build_euclidean_neutral Tpoint Tcircle tarski_axioms.Cong Tarski_dev.Definitions.BetS (* InCirc OnCirc OutCirc*) tarski_axioms.PA tarski_axioms.PB tarski_axioms.PC CI).
- intros;apply cong_transitivity with P Q;finish.
- intro;finish.
- intro;finish.
- intros;apply (l2_11 A B C a b c); unfold Definitions.BetS in *;intuition.
- intros.
  destruct (eq_dec_points A B);intuition.
- intros.
  decompose [ex and] H0.
  unfold CI in *.
  spliter.
  congruence.
- assert (T:=lower_dim).
  split.
  intro H;rewrite H in *;apply T;Between.
  split.
  intro H;rewrite H in *;apply T;Between.
  split.
  intro H;rewrite H in *;apply T;Between.
  split.
  unfold Definitions.BetS in *;intuition.
  unfold Definitions.BetS in *;intuition.
- intros; unfold Definitions.BetS;
intro;spliter;treat_equalities;intuition.
- intros;unfold Definitions.BetS in *;
intros;spliter;finish.
- intros;unfold Definitions.BetS in *;
intros;spliter;try assumption;eBetween.
- intros;unfold Definitions.BetS in *;
intros;spliter .
assert (Bet A B C \/ Bet A C B) by (apply l5_3 with D;auto).
assert (~ (Bet A C B /\ A <> C /\ B <> C)) by intuition.
assert (T3:=eq_dec_points A B).
assert (T4:=eq_dec_points A C).
assert (T5:=eq_dec_points B C).
tauto.
- intros;intro;treat_equalities;finish.
- intros.
assert (tarski_axioms.Cong C D c d)
 by (apply (five_segment A a B b C c D d);
unfold Definitions.BetS in *;spliter;auto).
finish.
- intros;unfold Definitions.BetS in *;spliter.
  destruct (inner_pasch A B C P Q H H0) as [X [HXa HXb]]. 
  exists X.
  assert_diffs.
  assert (~ Bet A C B) by tauto.
  assert (B<>C) by auto.
  assert (~ Bet A B C) by tauto.
  assert (C<>A) by auto.
  assert (~ Bet C A B) by tauto.
  assert (~ Bet B C A) by Between.
  repeat split;Between.

 all:intro;treat_equalities;assert_cols;
 assert (HCol:Definitions.Col A B C) by ColR;
 unfold Definitions.Col in HCol;
 tauto.
- intros;unfold Definitions.BetS in *;spliter.
  assert (~ Bet B Q A) by tauto.
  assert (A<>Q) by auto.
  assert (~ Bet B A Q) by tauto.
  assert (B<>A) by auto.
  assert (Q<>B) by auto.
  assert (~ Bet Q B A) by tauto.
 assert (~ Bet A Q B) by finish.
  assert (Bet Q C B) by finish.
  destruct (outer_pasch Q A C B P H18 H) as [X [HXa HXb]].
  exists X.
   assert_diffs.
  repeat split;Between.
  intro;treat_equalities;assert_cols;
 assert (HCol:Definitions.Col B A Q) by ColR;
 unfold Definitions.Col in HCol;tauto.
  intro;treat_equalities;assert_cols;
 assert (HCol:Definitions.Col B A X) by ColR;
 unfold Definitions.Col in HCol;tauto.
  intro;treat_equalities;assert_cols;
  assert (HCol:Definitions.Col A Q B) by ColR;
  unfold Definitions.Col in HCol;tauto.
  intro;treat_equalities;assert_cols;
  assert (HCol:Definitions.Col A Q B) by ColR;
  unfold Definitions.Col in HCol;tauto.
- intros. destruct (segment_construction A B A B) as [X [HXa HXb]].
  exists X; unfold Definitions.BetS;assert_diffs;auto.
- intros.
  unfold CI;exists (A,A,B);auto.
Defined.

End Neutral.


Section RulerAndCompass.

Context `{TRC:Tarski_ruler_and_compass}.

Lemma BetS_BetS : forall A B C,
 Definitions.BetS A B C <-> BetS A B C.
Proof.
intros.
unfold BetS;simpl.
intuition.
Qed.

Lemma Col_Col : forall A B C,
 Definitions.Col A B C <-> Col A B C.
Proof.
intros.
unfold Definitions.Col, Col, BetS.
simpl.
unfold Definitions.BetS,eq.
split.
intros.
destruct (eq_dec_points A B).
left;auto.
destruct (eq_dec_points A C).
right;left;auto.
destruct (eq_dec_points B C).
right;right;left;auto.
decompose [or] H.
right;right;right;right;left;auto.
right;right;right;right;right;finish.
right;right;right;left;finish.
intros.
decompose [or] H;subst;spliter;finish.
Qed.

Lemma nCol_not_Col : forall A B C,
 nCol A B C -> ~ Col A B C.
Proof.
unfold nCol.
unfold Col.
intuition.
Qed.

Lemma InCirc_not_OnCirc: forall J A,
 InCirc J A -> ~ OnCirc J A.
Proof.
unfold InCirc, OnCirc in *.
intros A J.
destruct J as [[X C] D].
intros.
destruct H as [U [V HUV]];spliter.
intro.
unfold Definitions.BetS in *;spliter.
assert (tarski_axioms.Cong X U X V) by eCong.
assert (Midpoint X U V) by (split;finish).
assert (Midpoint X A V).
apply (cong_col_mid A X V).
assumption.
ColR.
eCong.
treat_equalities;intuition.
Qed.

Lemma InCirc_InCirc : forall A K, euclidean_axioms.InCirc A K -> InCirc A K.
Proof.
intros.
unfold euclidean_axioms.InCirc in *.
destruct K as [[C U] V].
unfold euclidean_axioms.InCirc in *.
destruct H as [X [Y [C0 [V [W [HW1 HW2]]]]]].
destruct HW2.
- unfold eq in *;subst.
unfold euclidean_axioms.CI in *;simpl in *.
unfold CI in *.
spliter.
inversion H;subst.
destruct (eq_dec_points C0 V).
subst.
destruct (symmetric_point_construction W V) as [X0 HX].
exists X0.
exists W.
assert_bets.
assert_diffs.
split;finish.
unfold Definitions.BetS;finish.
split;finish.
split;finish.
unfold Definitions.BetS;finish.
destruct (segment_construction_3 C0 V V W H1 H0) as [X0 [HX0 HX1]].
destruct (symmetric_point_construction X0 C0) as [Y0 HY0].
exists X0.
exists Y0.
assert_bets.
assert_diffs.
unfold Definitions.BetS;split;finish.
split.
eCong.
split.
eCong.
split;finish.
- spliter.
unfold euclidean_axioms.CI in *;simpl in *;unfold CI in *;spliter.
inversion H2;subst.
assert (C0 <> A).
 {
  intro;treat_equalities.
  unfold Definitions.BetS in *;intuition.
 }

destruct (segment_construction_3 C0 A V W H4 H3) as [X0 [HX0 HX1]].
destruct (eq_dec_points A X0).
 {
  treat_equalities.
  assert_diffs.
  assert (HCong: tarski_axioms.Cong C0 Y C0 X) by eCong.
  unfold Definitions.BetS in *;spliter.
  assert (eq:= between_cong C0 X Y H HCong).
  subst;intuition.
 }

destruct (symmetric_point_construction X0 C0) as [Y0 HY0].
destruct (eq_dec_points A Y0).
 {
  treat_equalities.
  unfold Definitions.BetS in *;spliter.
  assert_diffs.
  unfold Midpoint in *;spliter.
  assert (HCong: tarski_axioms.Cong C0 X0 C0 X) by eCong.
  assert (HCong2: tarski_axioms.Cong C0 Y C0 X) by eCong.
  assert (eq:= between_cong C0 X Y H HCong2).
  subst;intuition.  
 }
destruct HX0 as [HA [ HB [HC | HC]]].
exists X0.
exists Y0.
assert_diffs.
split;unfold Definitions.BetS;finish.
split.
eCong.
split.
eCong.
assert_bets;finish.
split;finish.
eBetween.

assert (Lt C0 Y C0 X)
 by (unfold Definitions.BetS in *;spliter;apply (bet__lt1213);auto).
assert (Le C0 X0 C0 A) 
 by (apply (bet__le1213);auto).
assert (HCong: tarski_axioms.Cong C0 X0 C0 X) by eCong.
assert (Lt C0 X C0 A)
 by (apply (cong2_lt__lt C0 X0 C0 A);finish).
assert (Lt C0 Y C0 A)
 by (apply (le3456_lt__lt) with C0 X;auto using lt__le).
assert (Hc : tarski_axioms.Cong C0 Y C0 A) by finish.
apply cong__nlt in Hc.
intuition.
Qed.

Lemma OnCirc_OnCirc : forall A P Q R, Q<>R -> OnCirc A (P,Q,R) -> euclidean_axioms.OnCirc A (P,Q,R).
Proof.
intros.
unfold OnCirc in *.
unfold euclidean_axioms.OnCirc.
exists Q.
exists R.
exists P.
unfold euclidean_axioms.CI;simpl;unfold CI.
finish.
Qed.

Lemma eOnCirc_OnCirc : forall A K, euclidean_axioms.OnCirc A K -> OnCirc A K.
Proof.
intros.
unfold OnCirc.
destruct K.
destruct p.
unfold euclidean_axioms.OnCirc in *.
destruct H as [X [Y [U HXY]]].
spliter.
unfold euclidean_axioms.CI in *;simpl in *;unfold CI in *.
spliter.
inversion H;subst;finish.
Qed.

Lemma eOutCirc_OutCirc : forall A K, euclidean_axioms.OutCirc A K -> OutCirc A K.
Proof.
intros.
destruct K.
destruct p.
unfold euclidean_axioms.OutCirc in *.
destruct H as [X [Y [U [V HV]]]].
spliter.
unfold euclidean_axioms.CI in *;simpl in *;unfold CI in *.
spliter.
inversion H;subst.
exists X;finish.
Qed.


Lemma InCircCenter: forall U V W, V<>W -> InCirc U (U, V, W).
Proof.
intros.

unfold InCirc.
destruct (eq_dec_points U V).
subst.
exists W.
destruct (symmetric_point_construction W V) as [Y HY].
exists Y.
assert_diffs.
unfold Definitions.BetS.
split;finish.
destruct (segment_construction_3 U V V W H0 H) as [X HX].
destruct (symmetric_point_construction X U) as [Y HY].
spliter.
assert_diffs.
assert_bets.
exists X. exists Y.
split.
unfold Definitions.BetS;finish.
split.
eCong.
split.
eCong.
unfold Definitions.BetS;finish.
Qed.

Global Instance Euclid_neutral_ruler_compass_follows_from_Tarski_ruler_and_compass :
  euclidean_neutral_ruler_compass Euclid_neutral_follows_from_Tarski_neutral.
Proof.
assert (cc : circle_circle).
cut (circle_circle_axiom).
apply equivalent_variants_of_circle_circle; simpl; tauto.
unfold circle_circle_axiom.
exact circle_circle_continuity.
split.
- intros.
  apply InCirc_InCirc in H0.
  destruct (circle_line cc A B C K P Q H H0 H1) as [X [Y HXY]].
  spliter.
  destruct (bet_dec A B Y).
  exists X.
  exists Y.
  split.
  apply (Col_Col A B X); auto.
  split.
  unfold BetS;simpl.
  unfold Definitions.BetS.
  split.
  assumption.
  split.
  assumption.
  unfold Definitions.BetS in *;spliter;finish.

  
  split.
  destruct K as [p q].
  destruct p.
  apply OnCirc_OnCirc.
  { 
   unfold euclidean_axioms.CI in *;simpl in *;unfold CI in *.
   spliter.
   inversion H;subst;auto.
  }
  assumption.
  split.
  destruct K as [p q].
  destruct p.
  apply OnCirc_OnCirc.
  {
  unfold euclidean_axioms.CI in *;simpl in *;unfold CI in *.
   spliter.
   inversion H;subst;auto.
  }
  assumption.
  
  unfold BetS;simpl;auto.

 exists Y.
 exists X.
 split.
 apply (Col_Col A B Y); auto.
 split.
 unfold Definitions.BetS in *;spliter;assert_diffs.
 unfold Definitions.Col in H2.
 destruct H2.
 unfold BetS;simpl;unfold Definitions.BetS.
 split;finish.
 destruct H2.
 exfalso;apply H7.
 eBetween.
 unfold  BetS;simpl;unfold Definitions.BetS.
 split;finish.
  exfalso;apply H7;eBetween.
 split.
  destruct K as [p q].
  destruct p.
  apply OnCirc_OnCirc.
  { 
   unfold euclidean_axioms.CI in *;simpl in *;unfold CI in *.
   spliter.
   inversion H;subst;auto.
  }
  assumption.
  split.
    destruct K as [p q].
  destruct p.
  apply OnCirc_OnCirc.
  { 
   unfold euclidean_axioms.CI in *;simpl in *;unfold CI in *.
   spliter.
   inversion H;subst;auto.
  }
  assumption.
  unfold BetS;simpl;unfold Definitions.BetS in *;spliter;finish.

- simpl.
  intros.
  apply InCirc_InCirc in H0.
  apply eOnCirc_OnCirc in H3.
  apply eOnCirc_OnCirc in H4.
  apply eOutCirc_OutCirc in H1.
  destruct (circle_circle' cc C D F G J K P Q R S H) as [X HX];auto.
  spliter.
  exists X.
  split.
  destruct J.
  destruct p.
  unfold CI in *.
  spliter.
  inversion H;subst.
  apply OnCirc_OnCirc;auto.
  destruct K.
  destruct p.
  unfold CI in *.
  spliter.
  inversion H2;subst.
  apply OnCirc_OnCirc;auto.
Defined.

End RulerAndCompass.

Section Euclidean.

Context `{TRC:Tarski_ruler_and_compass}.
Context `{TE:@Tarski_euclidean Tn TnEQD}.

Lemma Euclid5 :
   forall a p q r s t,
    BetS r t s -> BetS p t q -> BetS r a q ->
    Cong p t q t -> Cong t r t s -> nCol p q s ->
    exists X, BetS p a X /\ BetS s q X.
Proof.
intros.
assert (T:tarski_s_parallel_postulate -> 
        euclid_5).
{
 assert (T:=equivalent_postulates_without_decidability_of_intersection_of_lines_bis).
 unfold all_equiv.all_equiv in *.
 apply T;simpl;auto 10.
}
assert (T2:euclid_5).
apply T.
unfold tarski_s_parallel_postulate.
apply euclid.
unfold euclid_5 in *.
assert (T3:exists I : Tpoint, Definitions.BetS s q I /\ Definitions.BetS p a I).
apply (T2 p q r s t a);
auto using BetS_BetS.
unfold BetS in *;simpl in *;
unfold Definitions.BetS in *;spliter;finish.
intro HnCol.
apply Col_Col in HnCol.
apply nCol_not_Col in H4;intuition.
finish.
destruct T3 as [X HX].
exists X;spliter;auto.
Qed.

Global Instance Euclid_follows_from_Tarski_euclidean :
 euclidean_euclidean Euclid_neutral_ruler_compass_follows_from_Tarski_ruler_and_compass.
Proof.
intros.
split.
apply Euclid5.
Qed.

End Euclidean.