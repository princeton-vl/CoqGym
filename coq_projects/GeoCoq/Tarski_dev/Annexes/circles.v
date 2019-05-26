Require Export GeoCoq.Tarski_dev.Ch12_parallel.

Section Circle.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma inc112 : forall A B,
 InCircle A A B.
Proof.
  unfold InCircle.
  Le.
Qed.

Lemma onc212 : forall A B,
 OnCircle B A B.
Proof.
  unfold OnCircle.
  Cong.
Qed.

Lemma onc_sym : forall A B P, OnCircle P A B -> OnCircle B A P.
Proof.
  unfold OnCircle.
  Cong.
Qed.

Lemma ninc__outcs : forall X O P, ~ InCircle X O P -> OutCircleS X O P.
Proof.
intros.
unfold OutCircleS.
unfold InCircle in *.
apply nle__lt in H; auto.
Qed.

Lemma inc__outc : forall A B P, InCircle P A B <-> OutCircle B A P.
Proof.
  split; trivial.
Qed.

Lemma incs__outcs : forall A B P, InCircleS P A B <-> OutCircleS B A P.
Proof.
  split; trivial.
Qed.

Lemma onc__inc : forall A B P, OnCircle P A B -> InCircle P A B.
Proof.
unfold OnCircle, InCircle.
Le.
Qed.

Lemma onc__outc : forall A B P, OnCircle P A B -> OutCircle P A B.
Proof.
unfold OnCircle, OutCircle.
Le.
Qed.

Lemma inc_outc__onc : forall A B P, InCircle P A B -> OutCircle P A B -> OnCircle P A B.
Proof.
  intros A B P HIn HOut.
  apply le_anti_symmetry; trivial.
Qed.

Lemma incs__inc : forall A B P, InCircleS P A B -> InCircle P A B.
Proof.
unfold InCircleS, InCircle.
Le.
Qed.

Lemma outcs__outc : forall A B P, OutCircleS P A B -> OutCircle P A B.
Proof.
unfold OutCircleS, OutCircle.
Le.
Qed.

Lemma incs__noutc : forall A B P, InCircleS P A B <-> ~ OutCircle P A B.
Proof.
intros.
split; intro; [apply lt__nle|apply nle__lt]; assumption.
Qed.

Lemma outcs__ninc : forall A B P, OutCircleS P A B <-> ~ InCircle P A B.
Proof.
intros.
split; intro; [apply lt__nle|apply nle__lt]; assumption.
Qed.

Lemma inc__noutcs : forall A B P, InCircle P A B <-> ~ OutCircleS P A B.
Proof.
intros.
split; intro; [apply le__nlt|apply nlt__le]; assumption.
Qed.

Lemma outc__nincs : forall A B P, OutCircle P A B <-> ~ InCircleS P A B.
Proof.
intros.
split; intro; [apply le__nlt|apply nlt__le]; assumption.
Qed.

Lemma inc_eq : forall A P, InCircle P A A -> A = P.
Proof.
intros A B HIn.
apply le_zero with A; assumption.
Qed.

Lemma outc_eq : forall A B, OutCircle A A B -> A = B.
Proof.
intros A B HOut.
apply le_zero with A; assumption.
Qed.

Lemma onc2__cong : forall O P A B, OnCircle A O P -> OnCircle B O P -> Cong O A O B.
Proof.
unfold OnCircle.
intros O P A B H1 H2.
apply cong_transitivity with O P; Cong.
Qed.

End Circle.


Hint Resolve inc112 onc212 onc_sym inc__outc onc__inc onc__outc
             inc_outc__onc incs__inc outcs__outc : circle.

Ltac Circle := auto with circle.

Ltac treat_equalities :=
try treat_equalities_aux;
repeat
  match goal with
   | H:(Cong ?X3 ?X3 ?X1 ?X2) |- _ =>
      apply cong_symmetry in H; apply cong_identity in H;
      smart_subst X2;clean_reap_hyps
   | H:(Cong ?X1 ?X2 ?X3 ?X3) |- _ =>
      apply cong_identity in H;smart_subst X2;clean_reap_hyps
   | H:(Bet ?X1 ?X2 ?X1) |- _ =>
      apply  between_identity in H;smart_subst X2;clean_reap_hyps
   | H:(Midpoint ?X ?Y ?Y) |- _ => apply l7_3 in H; smart_subst Y;clean_reap_hyps
   | H : Bet ?A ?B ?C, H2 : Bet ?B ?A ?C |- _ =>
     let T := fresh in not_exist_hyp (A=B); assert (T : A=B) by (apply (between_equality A B C); finish);
                       smart_subst A;clean_reap_hyps
   | H : Bet ?A ?B ?C, H2 : Bet ?A ?C ?B |- _ =>
     let T := fresh in not_exist_hyp (B=C); assert (T : B=C) by (apply (between_equality_2 A B C); finish);
                       smart_subst B;clean_reap_hyps
   | H : Bet ?A ?B ?C, H2 : Bet ?C ?A ?B |- _ =>
     let T := fresh in not_exist_hyp (A=B); assert (T : A=B) by (apply (between_equality A B C); finish);
                       smart_subst A;clean_reap_hyps
   | H : Bet ?A ?B ?C, H2 : Bet ?B ?C ?A |- _ =>
     let T := fresh in not_exist_hyp (B=C); assert (T : B=C) by (apply (between_equality_2 A B C); finish);
                       smart_subst A;clean_reap_hyps
   | H:(Le ?X1 ?X2 ?X3 ?X3) |- _ =>
      apply le_zero in H;smart_subst X2;clean_reap_hyps
   | H : Midpoint ?P ?A ?P1, H2 : Midpoint ?P ?A ?P2 |- _ =>
     let T := fresh in not_exist_hyp (P1=P2);
                      assert (T := symmetric_point_uniqueness A P P1 P2 H H2);
                      smart_subst P1;clean_reap_hyps
   | H : Midpoint ?A ?P ?X, H2 : Midpoint ?A ?Q ?X |- _ =>
     let T := fresh in not_exist_hyp (P=Q); assert (T := l7_9 P Q A X H H2);
                       smart_subst P;clean_reap_hyps
   | H : Midpoint ?A ?P ?X, H2 : Midpoint ?A ?X ?Q |- _ =>
     let T := fresh in not_exist_hyp (P=Q); assert (T := l7_9_bis P Q A X H H2);
                       smart_subst P;clean_reap_hyps
   | H : Midpoint ?M ?A ?A |- _ =>
     let T := fresh in not_exist_hyp (M=A); assert (T : l7_3 M A H);
                       smart_subst M;clean_reap_hyps
   | H : Midpoint ?A ?P ?P', H2 : Midpoint ?B ?P ?P' |- _ =>
     let T := fresh in not_exist_hyp (A=B); assert (T := l7_17 P P' A B H H2);
                       smart_subst A;clean_reap_hyps
   | H : Midpoint ?A ?P ?P', H2 : Midpoint ?B ?P' ?P |- _ =>
     let T := fresh in not_exist_hyp (A=B); assert (T := l7_17_bis P P' A B H H2);
                       smart_subst A;clean_reap_hyps
   | H : Midpoint ?A ?B ?A |- _ =>
     let T := fresh in not_exist_hyp (A=B); assert (T := is_midpoint_id_2 A B H);
                       smart_subst A;clean_reap_hyps
   | H : Midpoint ?A ?A ?B |- _ =>
     let T := fresh in not_exist_hyp (A=B); assert (T := is_midpoint_id A B H);
                       smart_subst A;clean_reap_hyps
   | H : OnCircle ?A ?A ?B |- _ =>
      apply cong_reverse_identity in H;smart_subst B;clean_reap_hyps
   | H : OnCircle ?B ?A ?A |- _ =>
      apply cong_identity in H;smart_subst B;clean_reap_hyps
   | H : InCircle ?B ?A ?A |- _ =>
      apply le_zero in H;smart_subst B;clean_reap_hyps
   | H : OutCircle ?A ?A ?B |- _ =>
      apply le_zero in H;smart_subst B;clean_reap_hyps
end.

Section Circle_2.


Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

(** If a point is strictly inside a segment of a disk, it is strictly inside the circle. *)

Lemma bet_inc2__incs : forall O P U V X,
 X <> U -> X <> V -> Bet U X V ->
 InCircle U O P -> InCircle V O P ->
 InCircleS X O P.
Proof.
intros O P U V X HUX HVX HBet HUIn HVIn.
destruct (le_cases O U O V).
- apply le3456_lt__lt with O V; trivial.
  apply lt_comm, (bet_le__lt U); Le.
- apply le3456_lt__lt with O U; trivial.
  apply lt_comm, (bet_le__lt V); Between; Le.
Qed.

Lemma bet_incs2__incs : forall O P U V X,
 Bet U X V -> InCircleS U O P -> InCircleS V O P ->
 InCircleS X O P.
Proof.
intros O P U V X HBet HUIn HVIn.
destruct (eq_dec_points X U).
  subst; assumption.
destruct (eq_dec_points X V).
  subst; assumption.
apply bet_inc2__incs with U V; Circle.
Qed.

(** If A and B are two points inside the circle, then all points on the segment AB are also
    in the circle, i.e. a circle is a convex figure.
*)

Lemma bet_inc2__inc : forall A B U V P, InCircle U A B -> InCircle V A B -> Bet U P V ->
  InCircle P A B.
Proof.
  intros A B U V P HU HV HBet.
  destruct (eq_dec_points P U).
    subst P; assumption.
  destruct (eq_dec_points P V).
    subst P; assumption.
  apply incs__inc, bet_inc2__incs with U V; assumption.
Qed.

(** Given two points U and V on a circle, the points of the line UV which are inside the circle are
    between U and V. *) 

Lemma col_inc_onc2__bet : forall A B U V P, U <> V -> OnCircle U A B -> OnCircle V A B ->
  Col U V P -> InCircle P A B -> Bet U P V.
Proof.
  intros A B U V P HUV HU HV HCol HIn.
  assert (Cong A U A V) by (apply cong_transitivity with A B; Cong).
  destruct HCol as [HBet|[HBet|HBet]]; Between.
  - destruct (eq_dec_points P V); try (subst; Between).
    exfalso.
    assert (HLt : Lt V A U A).
      apply (bet_le__lt P); Between.
      apply (l5_6 A P A B); Cong.
    destruct HLt as [HLe HNCong].
    apply HNCong; Cong.
  - destruct (eq_dec_points P U); try (subst; Between).
    exfalso.
    assert (HLt : Lt U A V A).
      apply (bet_le__lt P); trivial.
      apply (l5_6 A P A B); Cong.
    destruct HLt as [HLe HNCong].
    apply HNCong; Cong.
Qed.

(** Given two points U and V on a circle, all points of line UV which are outside the segment UV are
    outside the circle. *)

Lemma onc2_out__outcs : forall A B U V P, U <> V -> OnCircle U A B -> OnCircle V A B -> Out P U V ->
  OutCircleS P A B.
Proof.
  intros A B U V P HUV HUOn HVOn HOut.
  apply outcs__ninc.
  intro HIn.
  apply (not_bet_and_out U P V).
  split; trivial.
  apply (col_inc_onc2__bet A B); Col.
Qed.

(** Given two points U and V inside a circle, all points of line UV which are outside the circle are
    outside the segment UV. *)

Lemma col_inc2_outcs__out : forall A B U V P, InCircle U A B -> InCircle V A B ->
  Col U V P -> OutCircleS P A B -> Out P U V.
Proof.
  intros A B U V P HUIn HVIn HCol HOut.
  apply not_bet_out; Col.
  intro HBet.
  apply outcs__ninc in HOut.
  apply HOut, bet_inc2__inc with U V; trivial.
Qed.

(** If the center of a circle belongs to a chord, then it is the midpoint of the chord. *)

Lemma col_onc2__mid : forall A B U V, U <> V -> OnCircle U A B -> OnCircle V A B ->
  Col U V A -> Midpoint A U V.
Proof.
  intros A B U V HUV HU HV HCol.
  split.
    apply (col_inc_onc2__bet A B); Circle.
    apply cong_transitivity with A B; Cong.
Qed.

(** Given a point U on a circle and a point P inside the circle, there is a point V such as
    UV is a chord of the circle going through P. *)

Lemma chord_completion : forall A B U P, OnCircle U A B -> InCircle P A B ->
  exists V, OnCircle V A B /\ Bet U P V.
Proof.
  intros A B U P HOn HIn.
  destruct (eq_dec_points U A).
    unfold OnCircle, InCircle in *|-.
    treat_equalities; exists U; split; Circle; Between.
  assert (HA' : exists A', U <> A' /\ Col U P A' /\ Per A A' U).
  { destruct (col_dec U P A) as [HCol|HNCol].
      exists A; split; Col; Perp.
    destruct (l8_18_existence U P A) as [A' [HCol HPerp]]; trivial.
    assert (U <> A').
    { intro; treat_equalities.
      assert_diffs.
      destruct (l11_46 P U A) as [_ HLt]; auto.
        left; Perp.
      apply lt__nle in HLt.
      apply HLt.
      apply (l5_6 A P A B); Cong.
    }
    exists A'; repeat split; trivial.
    apply l8_2, perp_per_1.
    apply perp_left_comm, perp_col with P; trivial.
  }
  destruct HA' as [A' [HUA' [HCol HPer]]].
  destruct (symmetric_point_construction U A') as [V HV].
  assert_diffs.
  assert (HCong := per_double_cong A A' U V HPer HV).
  assert (HVOn : OnCircle V A B).
    unfold OnCircle in *.
    apply cong_transitivity with A U; Cong.
  exists V; split; trivial.
  apply (col_inc_onc2__bet A B); trivial.
  ColR.
Qed.

(** Given a circle, there is a point strictly outside the circle. *)

Lemma outcs_exists : forall O P, exists Q, OutCircleS Q O P.
Proof.
intros.
induction(eq_dec_points O P).
subst P.
assert(HH:=another_point O).
ex_and HH Q.
exists Q.
unfold OutCircleS.
apply lt1123;auto.

assert(HH:=segment_construction O P O P).
ex_and HH Q.
exists Q.
split.
exists P.
split; Cong.
intro.
assert (P=Q) by eauto using between_cong.
treat_equalities;intuition.
Qed.

(** Given a circle of center O and a ray OX, there is a point on the ray
    which is also strictly outside the circle. *)

Lemma outcs_exists1 : forall O P X, X <> O -> exists Q, Out O X Q /\ OutCircleS Q O P.
Proof.
intros O P X HOX.
destruct (segment_construction O X O P) as [Q [HQ1 HQ2]].
exists Q; split.
  apply bet_out; auto.
split.
- apply le_comm.
  exists X.
  split; Between; Cong.
- intro.
  apply HOX.
  apply between_cong with Q; Between.
  apply cong_transitivity with O P; Cong.
Qed.

(** Given a circle there is a point which is strictly inside. *)

Lemma incs_exists : forall O P, O <> P -> exists Q, InCircleS Q O P.
Proof.
intros.
exists O.
apply lt1123;auto.
Qed.

(** Given a circle of center O and a ray OX, there is a point on the ray
    which is also strictly inside the circle. *)

Lemma incs_exists1 : forall O P X, X <> O -> P <> O -> exists Q, Out O X Q /\ InCircleS Q O P.
Proof.
intros O P X HOX HOP.
destruct (midpoint_existence O P) as [M HM].
destruct (segment_construction_3 O X O M) as [Q [HQ1 HQ2]]; auto.
  intro; treat_equalities; auto.
exists Q; split; auto.
apply (cong2_lt__lt O M O P); Cong.
apply mid__lt; auto.
Qed.

(** Given a circle of center O and a ray OX, there is a point on the ray which is also on the circle. *)

Lemma onc_exists : forall O P X,  X <> O -> O <> P -> exists Q, OnCircle Q O P /\ Out O X Q.
Proof.
intros.
assert(HH:=segment_construction_2 X O O P H).
ex_and HH Q.
exists Q.
split.
unfold OnCircle.
Cong.
unfold Out.
repeat split; auto.
intro.
subst Q.
treat_equalities; tauto.
Qed.

(** Given a circle of center O and a line OX, O is between two points of the line
    which are also on the circle. *)

Lemma diam_points : forall O P X, exists Q1 Q2,
  Bet Q1 O Q2 /\ Col Q1 Q2 X /\ OnCircle Q1 O P /\ OnCircle Q2 O P.
Proof.
intros O P X.
destruct (eq_dec_points X O).
  subst X.
  destruct (segment_construction P O O P) as [P' [HP'1 HP'2]].
  exists P, P'; repeat split; Col; Circle.
destruct (eq_dec_points O P).
  subst P.
  exists O, O; repeat split; finish; Circle.
assert(HH:= onc_exists O P X H H0).
ex_and HH Q1.
assert(HH:= segment_construction Q1 O O Q1).
ex_and HH Q2.
exists Q1, Q2.
repeat split; Col.
ColR.
apply cong_transitivity with O Q1; Cong.
Qed.

(** The symmetric of a point on a circle relative to the center is also on the circle. *)

Lemma symmetric_oncircle : forall X Y O P, 
 Midpoint O X Y -> OnCircle X O P -> OnCircle Y O P.
Proof.
intros.
apply cong_transitivity with O X; Cong.
Qed.


(** The middle of a chord together with the center of the circle and one end of the chord
    form a right angle *)

Lemma mid_onc2__per : forall O P U V X,
 OnCircle U O P -> OnCircle V O P -> Midpoint X U V -> Per O X U.
Proof.
intros.
unfold Per.
exists V.
unfold OnCircle in *.
split; trivial.
apply cong_transitivity with O P; Cong.
Qed.

(** Euclid Book III Prop 3 (two lemmas).
 If a straight line passing through the center of a circle 
 bisects a straight line not passing through the center,
 then it also cuts it at right angles; and if it cuts it at right angles, then it also bisects it.
*)

(** The line from the center of a circle to the midpoint of a chord is perpendicular to the chord. *)

Lemma mid_onc2__perp : forall O P A B X,
 O <> X -> A <> B -> OnCircle A O P -> OnCircle B O P -> Midpoint X A B -> Perp O X A B.
Proof.
intros.
assert(Per O X A).
apply (mid_onc2__per O P A B X); auto.
unfold Midpoint in *.
spliter.

apply per_perp_in in H4; auto.
apply perp_in_perp in H4.
apply perp_sym.

apply (perp_col _ X); Perp.
Col.
intro.
subst X.
treat_equalities; tauto.
Qed.

(** If a line passing through the center of a circle is perpendicular to a chord,
    then they intersect at the middle of the chord *)

Lemma col_onc2_perp__mid : forall O P A B X,
 O<>X -> A<>B -> Col A B X -> OnCircle A O P -> OnCircle B O P -> Perp O X A B -> Midpoint X A B.
Proof.
  intros O P A B X HOX HAB HCol HAOn HBOn HPerp.
  destruct (midpoint_existence A B) as [M HM].
  cut (X = M).
    intro; subst; trivial.
  assert (HNCol : ~ Col A B O) by (destruct (perp_not_col2 A B O X); Perp; Col).
  apply (l8_18_uniqueness A B O); Col; Perp.
  apply perp_sym, mid_onc2__perp with P; auto.
  intro; subst; apply HNCol; Col.
Qed.

(** If two circles intersect at a point which is not on the line joining the center,
    then they intersect on any half-plane delimited by that line. *)

Lemma circle_circle_os : forall A B C D I P,
  OnCircle I A B -> OnCircle I C D -> ~ Col A C I -> ~ Col A C P ->
  exists Z, OnCircle Z A B /\ OnCircle Z C D /\ OS A C P Z.
Proof.
  intros A B C D I P HI1 HI2 HNCol1 HNCol2.
  destruct (l8_18_existence A C I) as [X []]; trivial.
  destruct (l10_15 A C X P) as [Z0 []]; trivial.
  assert_diffs.
  destruct (l6_11_existence X X I Z0) as [Z []]; auto.
  exists Z.
  assert (Perp A C X Z).
    assert_diffs; apply perp_sym, perp_col with Z0; Perp; Col.
  assert (OS A C P Z).
    apply one_side_transitivity with Z0; trivial.
    apply out_one_side_1 with X; [apply one_side_not_col124 with P| |apply l6_6]; trivial.
  clear dependent Z0.
  repeat split; auto.
  - apply cong_transitivity with A I; trivial.
    destruct (eq_dec_points A X).
      subst; assumption.
    apply l10_12 with X X; Cong; [apply perp_per_2|apply perp_per_1];
      apply perp_left_comm, perp_col with C; auto.
  - apply cong_transitivity with C I; trivial.
    destruct (eq_dec_points C X).
      subst; assumption.
    apply l10_12 with X X; Cong; [apply perp_per_2|apply perp_per_1];
      apply perp_left_comm, perp_col with A; Perp; Col.
Qed.

(** If two circles intersect, then they intersect on any plane containing the centers *)

Lemma circle_circle_cop : forall A B C D I P, OnCircle I A B -> OnCircle I C D ->
  exists Z, OnCircle Z A B /\ OnCircle Z C D /\ Coplanar A C P Z.
Proof.
  intros A B C D I P HI1 HI2.
  destruct (col_dec A C P).
    exists I; repeat split; trivial.
    exists P; left; split; Col.
  destruct (col_dec A C I).
    exists I; repeat split; trivial.
    exists I; left; split; Col.
  destruct (circle_circle_os A B C D I P) as [Z [HZ1 [HZ2 HOS]]]; trivial.
  exists Z; repeat split; Cop.
Qed.

(** A circle does not cut a line at more than two points. *)

Lemma line_circle_two_points : forall O P U V W,
 U <> V -> Col U V W -> OnCircle U O P -> OnCircle V O P -> OnCircle W O P -> 
 W = U \/ W = V.
Proof.
intros O P U V W HUV HCol HUOn HVOn HWOn.
destruct (eq_dec_points W U); auto.
right.
apply between_equality with U; apply col_inc_onc2__bet with O P; Col; Circle.
Qed.

(** The midpoint of a chord is strictly inside the circle. *)

Lemma onc2_mid__incs : forall O P U V M, 
 U <> V -> OnCircle U O P -> OnCircle V O P -> Midpoint M U V ->
 InCircleS M O P.
Proof.
intros O P U V M HUV HUOn HVOn HM.
assert_diffs.
apply bet_inc2__incs with U V; Between; Circle.
Qed.

(** A point is either strictly inside, on or strictly outside a circle. *)

Lemma circle_cases : forall O P X,
  OnCircle X O P \/ InCircleS X O P \/ OutCircleS X O P.
Proof.
intros O P X.
destruct (cong_dec O X O P); auto.
right.
destruct (le_cases O P O X); [right|left]; split; Cong.
Qed.

(** If a point is inside a circle, then it lies on a radius. *)

Lemma inc__radius : forall O P X, InCircle X O P ->
  exists Y, OnCircle Y O P /\ Bet O X Y.
Proof.
  intros O P X HIn.
  destruct (eq_dec_points O P).
    unfold InCircle in HIn; treat_equalities.
    exists O; split; Circle; Between.
  destruct (eq_dec_points O X).
    subst; exists P; split; Circle; Between.
  destruct (segment_construction_3 O X O P) as [Y [HY1 HY2]]; auto.
  exists Y; split; auto.
  apply l6_13_1; trivial.
  apply (l5_6 O X O P); Cong.
Qed.

Lemma onc_not_center : forall O P A, O <> P -> OnCircle A O P -> A <> O.
Proof.
intros.
intro.
unfold OnCircle in *.
treat_equalities; tauto.
Qed.

Lemma onc2_per__mid : forall O P U V M, U <> V -> M <> U ->
 OnCircle U O P -> OnCircle V O P -> Col M U V -> Per O M U -> Midpoint M U V .
Proof.
intros.
assert(HH:=midpoint_existence U V).
ex_and HH M'.
assert(HH:=(mid_onc2__per O P U V M' H1 H2 H5)).
assert(M = M' \/ ~ Col M' U V).
apply(col_per2_cases O M U V M'); Col.
assert_diffs;auto.
induction H6.
subst M'.
assumption.
apply False_ind.
apply H6.
ColR.
Qed.

(** Euclid Book III Prop 14
Equal straight lines in a circle are equally distant from the center, 
and those which are equally distant from the center equal one another.
*)

Lemma cong_chord_cong_center : forall O P A B C D M N,
 OnCircle A O P ->
 OnCircle B O P ->
 OnCircle C O P ->
 OnCircle D O P ->
 Midpoint M A B ->
 Midpoint N C D ->
 Cong A B C D ->
 Cong O N O M.
Proof.
intros.
assert(Cong M B N D).
apply cong_commutativity.
eapply (cong_cong_half_1 _ _ A _ _ C); Midpoint.
Cong.
unfold Midpoint in *.
unfold OnCircle in *.
spliter.
apply cong_commutativity.
apply cong_symmetry.
apply(l4_2 A M B O C N D O).
unfold IFSC.
repeat split; Cong.
apply (cong_transitivity _ _ O P); Cong.
apply (cong_transitivity _ _ O P); Cong.
Qed.

(** variant *)
Lemma cong_chord_cong_center1 : forall O P A B C D M N,
 A <> B -> C <> D -> M <> A -> N <> C ->
 OnCircle A O P ->
 OnCircle B O P ->
 OnCircle C O P ->
 OnCircle D O P ->
 Col M A B ->
 Col N C D ->
 Per O M A ->
 Per O N C ->
 Cong A B C D ->
 Cong O N O M.
Proof.
intros.
assert(Midpoint M A B).
apply(onc2_per__mid O P A B M H H1 H3 H4 H7 H9).
assert(Midpoint N C D).
apply(onc2_per__mid O P C D N H0 H2 H5 H6 H8 H10).
apply (cong_chord_cong_center O P A B C D M N); auto.
Qed.

(** Prop 7   **)

Lemma onc_sym__onc : forall O P A B X Y, 
Bet O A B -> OnCircle A O P -> OnCircle B O P -> OnCircle X O P -> ReflectL X Y A B -> OnCircle Y O P.
Proof.
intros.
unfold OnCircle in *.
assert(Cong X O Y O).
  {
    apply(is_image_spec_col_cong A B X Y O H3);Col.
  }
apply cong_transitivity with O X; Cong.
Qed.


Lemma mid_onc__diam : forall O P A B, OnCircle A O P -> Midpoint O A B -> Diam A B O P.
Proof.
  intros O P A B HA HB.
  repeat split; Between.
  apply (symmetric_oncircle A); trivial.
Qed.

Lemma chord_le_diam : forall O P A B U V,
 Diam A B O P -> OnCircle U O P -> OnCircle V O P -> Le U V A B.
Proof.
intros.
unfold OnCircle in *.
unfold Diam in *.
spliter.
apply(triangle_inequality_2 U O V A O B); trivial;
apply cong_transitivity with O P; Cong.
Qed.

Lemma chord_lt_diam : forall O P A B U V, 
 ~ Col O U V -> Diam A B O P -> OnCircle U O P -> OnCircle V O P ->
 Lt U V A B.
Proof.
intros.
assert(HH:= chord_le_diam O P A B U V H0 H1 H2).
unfold Lt.
split; auto.
intro.
apply H.
unfold Diam in *.
assert(HP:=midpoint_existence U V).
ex_and HP O'.
unfold Midpoint in *.
spliter.
unfold OnCircle in *.
assert(Cong O A O B) by (apply cong_transitivity with O P; Cong).
assert(Cong A O U O').
apply(cong_cong_half_1 A O B U O' V); unfold Midpoint; try split; Cong.
assert(Cong B O V O').
apply(cong_cong_half_2 A O B U O' V); unfold Midpoint; try split; Cong.
apply(l4_13 O A B).
Col.
unfold Cong_3.
repeat split; Cong; apply cong_transitivity with O P; Cong.
Qed.


Lemma inc2_le_diam: forall O P A B U V, Diam A B O P -> InCircle U O P -> InCircle V O P -> Le U V A B.
Proof.
intros.
unfold InCircle in *.
unfold Diam in *.
spliter.
unfold OnCircle in *.
assert(HH:= segment_construction U O O V).
ex_and HH W.
assert(Le U V U W).
{
  apply (triangle_inequality U O); Between; Cong.
}

assert(Le U W A B).
{
  apply(bet2_le2__le O O A B U W); Between.

  apply (l5_6 O U O P O U O A);Cong.
  apply (l5_6 O V O P O W O B);Cong.
}
apply(le_transitivity U V U W A B); auto.
Qed.


Lemma onc_col_diam__eq : forall O P A B X, Diam A B O P -> OnCircle X O P -> Col A B X -> X = A \/ X = B.
Proof.
intros.
unfold Diam in *.
spliter.
unfold OnCircle in *.
induction(eq_dec_points O P).
treat_equalities.
left; auto.

induction(eq_dec_points X B).
right; auto.
left.
assert_diffs.
assert(Cong O A O X) by (apply cong_transitivity with O P; Cong).
assert(Col A O X) by ColR.
assert(HH:= l7_20 O A X H11 H10).
induction HH.
auto.
assert(Midpoint O A B).
unfold Midpoint; split; trivial.
apply cong_transitivity with O P; Cong.
apply False_ind.
apply H5.
apply (symmetric_point_uniqueness A O ); auto.
Qed.

Lemma onc2_out__eq : forall O P A B, OnCircle A O P -> OnCircle B O P -> Out O A B -> A = B.
Proof.
  intros O P A B HAOn HBOn HOut.
  destruct (symmetric_point_construction A O) as [A' HA'].
  destruct (onc_col_diam__eq O P A A' B); auto.
    apply mid_onc__diam; assumption.
    ColR.
  exfalso.
  subst A'.
  apply (not_bet_and_out A O B); Between.
Qed.

Lemma bet_onc_le_a : forall O P A B T X, Diam A B O P -> Bet B O T -> OnCircle X O P -> Le T A T X.
Proof.
intros.
unfold Diam in*.
spliter.
unfold OnCircle in *.
assert(Cong O X O A) by (apply cong_transitivity with O P; Cong).
induction(eq_dec_points P O).
treat_equalities.
apply le_reflexivity.
induction(eq_dec_points T O).
subst T.
apply cong__le;Cong.
assert_diffs.
apply(triangle_reverse_inequality O T X A); Cong.
assert_diffs.
repeat split; auto.
apply (l5_2 B); Between.
Qed.


Lemma bet_onc_lt_a : forall O P A B T X,
 Diam A B O P -> O <> P -> O <> T -> X <> A -> Bet B O T  -> OnCircle X O P ->
 Lt T A T X.
Proof.
intros.
assert(HH:= bet_onc_le_a O P A B T X H H3 H4).
assert(Lt T A T X \/ Cong T A T X).
{
  induction(cong_dec T A T X).
  right; auto.
  left.
  unfold Lt.
  split; auto.
}
induction H5; auto.
unfold Diam in*.
spliter.
unfold OnCircle in *.
assert_diffs.
assert(Bet O A T \/ Bet O T A).
apply(l5_2 B O A T); Between.
assert (Cong O A O X) by (apply cong_transitivity with O P; Cong).
induction H13.
assert(Bet O X T).
{
  apply(l4_6 O A T O X T); auto.
  unfold Cong_3.
  repeat split; Cong.
}
apply False_ind.
apply H2.
apply(between_cong_2 O T); Cong.
assert(Bet O T X).
{
  apply(l4_6 O T A O T X); auto.
  unfold Cong_3.
  repeat split; Cong.
}
apply False_ind.
apply H2.
apply(between_cong_3 O T); Cong.
Qed.



Lemma bet_onc_le_b : forall O P A B T X,
 Diam A B O P -> Bet A O T -> OnCircle X O P ->
 Le T X T A.
Proof.
intros.
unfold Diam in *.
spliter.
unfold OnCircle in *.
apply(triangle_inequality T O X A).
Between.
apply cong_transitivity with O P; Cong.
Qed.


Lemma bet_onc_lt_b : forall O P A B T X,
 Diam A B O P -> T <> O -> X <> A -> Bet A O T -> OnCircle X O P ->
 Lt T X T A.
Proof.
intros.
assert(HH:= bet_onc_le_b O P A B T X H H2 H3 ).
assert(Lt T X  T A \/ Cong T A T X).
{
  induction(cong_dec T A T X).
  right; auto.
  left.
  unfold Lt.
  split; Cong.
}
unfold Diam in *.
spliter.
unfold OnCircle in *.
induction H4; auto.
apply False_ind.
assert(Bet T O A) by eBetween.
assert(Bet T O X).
{
  apply(l4_6 T O A T O X); auto.
  repeat split.
    apply cong_reflexivity.
    assumption.
    apply cong_transitivity with O P; Cong.
}
apply H1.
apply(between_cong_3 T O); trivial.
apply cong_transitivity with O P; Cong.
Qed.



Lemma incs2_lt_diam : forall O P A B U V, Diam A B O P -> InCircleS U O P -> InCircleS V O P -> Lt U V A B.
Proof.
intros.
unfold Diam in H.
spliter.
unfold OnCircle in *.
unfold InCircleS in *.

induction(eq_dec_points O P).
treat_equalities.
unfold Lt in H0.
spliter.
apply le_zero in H.
treat_equalities.
apply False_ind.
apply H0; Cong.

assert(Lt A O A B /\ Lt B O A B).
{
  assert (Midpoint O A B).
    split; [assumption|apply cong_transitivity with O P; Cong].
  split.
  apply(mid__lt );  assert_diffs;auto.
  assert (Lt B O B A) by (apply mid__lt;assert_diffs;finish).
  auto using lt_right_comm.
}
spliter.

induction(eq_dec_points O U).
treat_equalities.
spliter.
assert(Lt O V O A).
{
  apply(cong2_lt__lt O V O P); Cong.
}
apply (lt_transitivity O V O A A B); auto.
apply lt_left_comm; auto.

assert(HH:=segment_construction U O O V).
ex_and HH V'.

assert(Le U V U V').
{
  apply(triangle_inequality U O V V' H8); Cong.
}
assert(Lt U V' A B).
{
  apply(bet2_lt2__lt O O A B U V' H8 H).
  apply(cong2_lt__lt O U O P O U O A); Cong.
  apply(cong2_lt__lt O V O P O V' O B); Cong.
}

apply(le1234_lt__lt U V U V' A B); auto.
Qed.

Lemma incs_onc_diam__lt : forall O P A B U V, Diam A B O P -> InCircleS U O P -> OnCircle V O P -> Lt U V A B.
Proof.
intros.
unfold Diam in *.
spliter.
unfold OnCircle in *.
unfold InCircleS in *.

assert(HH:=segment_construction V O O U).
ex_and HH U'.
assert(Lt V U' A B).
{
  apply(bet2_lt_le__lt O O A B V U' H4 H).
  apply cong_transitivity with O P; Cong.
  apply(cong2_lt__lt O U O P); Cong.
}
assert(Le V U V U').
{
  apply(triangle_inequality V O U U' H4); Cong.
}
apply lt_left_comm.
apply(le1234_lt__lt V U V U'); auto.
Qed.

Lemma diam_cong_incs__outcs : forall O P A B U V, Diam A B O P -> Cong A B U V -> InCircleS U O P -> OutCircleS V O P.
Proof.
intros.
induction(eq_dec_points O P).
treat_equalities.
unfold InCircleS in H1.

unfold Lt in H1.
spliter.
apply le_zero in H1.
treat_equalities.
apply False_ind.
apply H2; Cong.

assert(HH:= circle_cases O P V).
induction HH.
assert(Lt U V A B) by  apply(incs_onc_diam__lt O P A B U V H H1 H3).
unfold Lt in H4.
spliter.
apply False_ind.
apply H5; Cong.

induction H3.
assert(HH:=incs2_lt_diam O P A B U V H H1 H3).
unfold Lt in HH.
spliter.
apply False_ind.
apply H5; Cong.
assumption.
Qed.

Lemma diam_uniqueness : forall O P A B X, Diam A B O P -> Cong A X A B -> OnCircle X O P -> X = B.
Proof.
intros.
unfold Diam in *.
spliter.
unfold OnCircle in *.
induction(eq_dec_points O P).
treat_equalities; auto.
assert(Bet A O X).
{
  apply(l4_6 A O B A O X); auto.
  repeat split; Cong.
  apply cong_transitivity with O P; Cong.
}
assert_diffs.
apply(between_cong_3 A O); auto.
apply cong_transitivity with O P; Cong.
Qed.

Lemma onc3__ncol : forall O P A B C,
 A <> B -> A <> C -> B <> C ->
 OnCircle A O P -> OnCircle B O P -> OnCircle C O P ->
 ~ Col A B C.
Proof.
intros.
unfold OnCircle in *.
intro.
induction H5.
assert(InCircleS B O P).
{
  apply(bet_inc2__incs O P A C B); Circle.
}
unfold InCircleS in *.
unfold Lt in *.
tauto.
induction H5.
assert(InCircleS C O P).
{
  apply(bet_inc2__incs O P B A C); Circle.
}
unfold InCircleS in *.
unfold Lt in *.
tauto.
assert(InCircleS A O P).
{
  apply(bet_inc2__incs O P C B A); Circle.
}
unfold InCircleS in *.
unfold Lt in *.
tauto.
Qed.

Lemma diam_exists : forall O P T, exists A, exists B, Diam A B O P /\ Col A B T.
Proof.
intros.
destruct (diam_points O P T) as [A [B [HBet [HCol [HA HB]]]]].
exists A, B.
repeat split; auto.
Qed.

Lemma chord_intersection : forall O P A B X Y,
  OnCircle A O P -> OnCircle B O P -> OnCircle X O P -> OnCircle Y O P -> TS A B X Y ->
  TS X Y A B.
Proof.
intros.
unfold TS in H3.
spliter.
ex_and H5 T.
repeat split.
apply (onc3__ncol O P); Circle; try(intro; treat_equalities; Col).
apply (onc3__ncol O P); Circle; try(intro; treat_equalities; Col).
exists T.
split.
Col.
assert_diffs.
apply (col_inc_onc2__bet O P); Col.
apply(bet_inc2__incs O P X Y T); Circle; intro; treat_equalities; Col.
Qed.

Lemma ray_cut_chord : forall O P A B X Y,
  Diam A B O P -> OnCircle X O P -> OnCircle Y O P -> TS A B X Y -> OS X Y O A ->
  TS X Y O B.
Proof.
intros.
unfold Diam in *.
spliter.
apply(l9_8_2 X Y A O B); [|Side].
apply (chord_intersection O P); assumption.
Qed.

Lemma center_col__diam : forall O P A B,
 A <> B -> Col O A B -> OnCircle A O P -> OnCircle B O P ->
 Diam A B O P.
Proof.
Proof.
intros.
unfold Diam.
split; Circle.
assert(Cong O A O B) by (apply cong_transitivity with O P; Cong).
assert(A = B \/ Midpoint O A B) by (apply(l7_20 O A B); Col).
induction H4.
contradiction.
Between.
Qed.

Lemma diam__midpoint: forall O P A B, Diam A B O P -> Midpoint O A B.
Proof.
intros.
unfold Diam in *.
spliter.
unfold Midpoint.
unfold OnCircle in *.
split.
  assumption.
apply cong_transitivity with O P; Cong.
Qed.

Lemma diam_sym : forall O P A B, Diam A B O P -> Diam B A O P.
Proof.
intros.
unfold Diam in *.
spliter.
repeat split; Between.
Qed.

Lemma diam_end_uniqueness : forall O P A B C, Diam A B O P -> Diam A C O P -> B = C.
Proof.
intros.
apply diam__midpoint in H.
apply diam__midpoint in H0.
apply (symmetric_point_uniqueness A O); Midpoint.
Qed.


Lemma center_onc2_mid__ncol : forall O P A B M ,
 O <> P -> ~ Col O A B ->
 OnCircle A O P -> OnCircle B O P ->
 Midpoint M A B  -> ~ Col A O M.
Proof.
intros.
intro.
assert_diffs.
unfold Midpoint in H3.
spliter.
apply H0.
ColR.
Qed.

Lemma bet_chord__diam_or_ncol : forall O P A B T,
  A <> B -> T <> A -> T <> B -> OnCircle A O P -> OnCircle B O P -> Bet A T B ->
  Diam A B O P \/ ~Col O A T /\ ~Col O B T.
Proof.
intros.
induction(col_dec O A B).
left.
apply(center_col__diam); Col.
right.
split.
intro.
apply H5; ColR.
intro.
apply H5; ColR.
Qed.

Lemma mid_chord__diam_or_ncol : forall O P A B T,
 A <> B -> OnCircle A O P -> OnCircle B O P ->
 Midpoint T A B ->
 Diam A B O P \/ ~Col O A T /\ ~Col O B T.
Proof.
intros.
unfold Midpoint in H2.
spliter.
apply(bet_chord__diam_or_ncol);auto.
intro.
treat_equalities; tauto.
intro.
treat_equalities; tauto.
Qed.

Lemma cop_mid_onc2_perp__col : forall O P A B X Y, A <> B -> OnCircle A O P -> OnCircle B O P ->
  Midpoint X A B -> Perp X Y A B -> Coplanar O A B Y -> Col X Y O.
Proof.
  intros O P A B X Y HAB HAOn HBOn HX HPerp HCop.
  destruct (eq_dec_points O X).
    subst; Col.
  apply cop_perp2__col with A B; Cop.
  apply perp_left_comm, mid_onc2__perp with P; auto.
Qed.

Lemma cong2_cop2_onc3__eq : forall O P X A B C, A <> B -> A <> C -> B <> C ->
  OnCircle A O P -> OnCircle B O P -> OnCircle C O P -> Coplanar A B C O ->
  Cong X A X B -> Cong X A X C -> Coplanar A B C X ->
  X = O.
Proof.
  intros O P X A B C HAB HAC HBC HAOn HBOn HCOn HCop HCong1 HCong2 HCop1.
  destruct (midpoint_existence A B) as [M1 HM1].
  destruct (midpoint_existence A C) as [M2 HM2].
  assert (HNCol : ~ Col C A B) by (apply (onc3__ncol O P); auto).
  destruct (l10_15 A B M1 C) as [P1 [HPerp1 HOS1]]; Col.
  destruct (l10_15 A C M2 B) as [P2 [HPerp2 HOS2]]; Col.
  assert (HColX1 : Col M1 P1 X).
    apply (cop_mid_onc2_perp__col X A A B); Circle; Perp.
    apply coplanar_perm_12, coplanar_trans_1 with C; Cop.
  assert (HColO1 : Col M1 P1 O).
    apply (cop_mid_onc2_perp__col O P A B); Perp.
    apply coplanar_perm_12, coplanar_trans_1 with C; Cop.
  apply not_col_permutation_3 in HNCol.
  assert (HColX2 : Col M2 P2 X).
    apply (cop_mid_onc2_perp__col X A A C); Circle; Perp.
    apply coplanar_perm_12, coplanar_trans_1 with B; Cop.
  assert (HColO2 : Col M2 P2 O).
    apply (cop_mid_onc2_perp__col O P A C); Perp.
    apply coplanar_perm_12, coplanar_trans_1 with B; Cop.
  assert_diffs.
  destruct (col_dec M1 P1 M2); [apply (l6_21 M2 P2 M1 P1)|apply (l6_21 M1 P1 M2 P2)]; Col.
  intro.
  apply HBC.
  destruct (eq_dec_points M1 M2).
    apply (symmetric_point_uniqueness A M1); subst; trivial.
  apply l10_2_uniqueness_spec with M1 P1 A.
    split; Perp; exists M1; Col.
  split.
    exists M2; auto.
  left.
  apply perp_sym, perp_col2_bis with P2 M2; ColR.
Qed.

Lemma tree_points_onc_cop : forall O P, O <> P -> exists A B C,
  A <> B /\ A <> C /\ B <> C /\ OnCircle A O P /\ OnCircle B O P /\ OnCircle C O P /\ Coplanar A B C O.
Proof.
  intros O P HOP.
  destruct (not_col_exists O P) as [X HNCol]; auto.
  destruct (diam_points O P X) as [B [C [HBet [HCol []]]]].
  exists P, B, C.
  repeat split; Circle.
    intro; subst; apply HNCol; ColR.
    intro; subst; apply HNCol; ColR.
    intro; treat_equalities; auto.
    exists B; left; split; Col.
Qed.

Lemma tree_points_onc_cop2 : forall O P Q, O <> P -> exists A B C,
  A <> B /\ A <> C /\ B <> C /\ OnCircle A O P /\ OnCircle B O P /\ OnCircle C O P /\
  Coplanar A B C O /\ Coplanar A B C Q.
Proof.
  intros O P Q HOP.
  destruct (eq_dec_points O Q).
    subst Q.
    destruct (tree_points_onc_cop O P HOP) as [A [B [C]]]; spliter.
    exists A, B, C; repeat split; auto.
  destruct (not_col_exists O Q) as [X HNCol]; auto.
  destruct (diam_points O P X) as [B [C [HBet [HCol []]]]].
  destruct (l6_11_existence O O P Q) as [A []]; auto.
  exists A, B, C.
  assert (~ Col O A B) by (intro; unfold OnCircle in *; assert_diffs; apply HNCol; ColR).
  assert_diffs.
  repeat split; Circle.
    intro; subst; apply HNCol; ColR.
    exists B; left; split; Col.
    exists O; right; right; split; Col.
Qed.

Lemma tree_points_onc : forall O P, O <> P -> exists A B C,
  A <> B /\ A <> C /\ B <> C /\ OnCircle A O P /\ OnCircle B O P /\ OnCircle C O P.
Proof.
  intros O P HOP.
  destruct (tree_points_onc_cop O P HOP) as [A [B [C]]]; spliter.
  exists A, B, C; repeat split; assumption.
Qed.

Lemma bet_cop_onc2__ex_onc_os_out : forall O P A B C I,
  A <> I -> B <> I -> ~ Col A B C -> ~ Col A B O ->
  OnCircle A O P -> OnCircle B O P -> Bet A I B -> Coplanar A B C O ->
  exists C1, Out C1 O I /\ OnCircle C1 O P /\ OS A B C C1.
Proof.
  intros O P A B C I HAI HBI HNCol HNCol1 HA HB HBet HCop.
  destruct (diam_points O P I) as [C1 [C2 [HBet1 [HCol [HC1 HC2]]]]].
  assert (HTS : TS A B C1 C2).
  { apply (chord_intersection O P); trivial.
    unfold OnCircle in *; assert_diffs.
    repeat split; [intro; apply HNCol1; ColR..|exists I; split; Col].
  }
  assert (HBet2 : Bet C1 I C2).
  { assert_diffs; apply (col_inc_onc2__bet O P); auto.
    apply bet_inc2__inc with A B; Circle.
  }
  assert (HNCol2 : ~ Col C1 A B) by (destruct HTS; assumption).
  destruct (cop__one_or_two_sides A B C C1); Col.
    apply coplanar_trans_1 with O; Col; [Cop|exists I; right; right; assert_diffs; split; ColR].
  - exists C2.
    split; [|split; trivial; exists C1; Side].
    apply bet2__out with C1; Between.
      intro; treat_equalities; auto.
      destruct HTS as [_ [HNCol3 _]]; spliter; intro; subst; apply HNCol3; Col.
  - exists C1.
    split; [|split; trivial].
    apply bet2__out with C2; trivial.
      intro; treat_equalities; auto.
      intro; subst; apply HNCol2; Col.
Qed.

(** Two circles are equal if and only if they have the same center and the same radius *)

Lemma EqC_chara: forall A B C D, EqC A B C D <-> A = C /\ Cong A B C D.
Proof.
  intros A B C D.
  split.
  - intro Heq.
    unfold EqC in Heq.
    assert (C = A).
    { destruct (eq_dec_points A B) as [|Hd].
      - subst B.
        unfold OnCircle in Heq.
        assert (Cong A D A A) by (rewrite Heq; Cong).
        treat_equalities.
        destruct (segment_construction A C A C) as [A' []].
        assert (Cong A A' A A) by (rewrite Heq; Cong).
        treat_equalities; auto.
      - destruct (tree_points_onc_cop2 A B C Hd) as [B0 [B1 [B2]]].
        spliter; unfold OnCircle in *.
        assert (Cong C B0 C D) by (rewrite <- Heq; Cong).
        apply cong2_cop2_onc3__eq with B B0 B1 B2; auto;
          apply cong_transitivity with C D; trivial;
          unfold OnCircle in *; apply cong_symmetry; rewrite <- Heq; assumption.
    }
    subst C.
    split; trivial.
    unfold OnCircle in Heq.
    rewrite <- (Heq B); Cong.
  - intros [].
    subst C.
    intro X.
    split; intro; [apply cong_transitivity with A B|apply cong_transitivity with A D]; Cong.
Qed.

(** Two circles are distinct if and only if there is a point
    belonging to the first and not to the second *)

Lemma nEqC_chara : forall A B C D, A <> B ->
  ~ EqC A B C D <->
  (exists X, OnCircle X A B /\ ~ OnCircle X C D).
Proof.
  intros A B C D HAB.
  split.
  { intro Hneq.
    destruct (eq_dec_points C A) as [|HCA].
    { destruct (cong_dec A B C D) as [|HNCong].
        exfalso; apply Hneq, EqC_chara; split; auto.
        subst C; exists B; split; Circle.
    }
    destruct (tree_points_onc_cop2 A B C HAB) as [B0 [B1 [B2]]]; spliter.
    destruct (cong_dec C B0 C D); [destruct (cong_dec C B1 C D);[destruct (cong_dec C B2 C D)|]|].
    - exfalso.
      apply HCA.
      apply cong2_cop2_onc3__eq with B B0 B1 B2; auto; apply cong_transitivity with C D; Cong.
    - exists B2; auto.
    - exists B1; auto.
    - exists B0; auto.
  }
  intros [X [HX Habs]] Heq.
  apply Habs, Heq, HX.
Qed.

Lemma EqC_sym : forall A B C D, EqC A B C D -> EqC C D A B.
Proof.
  intros A B C D Heq X.
  split; intro; [rewrite (Heq X)|rewrite <- (Heq X)]; assumption.
Qed.

End Circle_2.

Section Circle_2D.

Context `{T2D:Tarski_2D}.

(** The center of a circle belongs to the perpendicular bisector of each chord *)

Lemma mid_onc2_perp__col : forall O P A B X Y,
 A <> B -> OnCircle A O P -> OnCircle B O P -> Midpoint X A B -> Perp X Y A B -> Col X Y O.
Proof.
  intros O P A B X Y HAB HAOn HBOn HX HPerp.
  assert (HCop := all_coplanar O A B Y).
  apply cop_mid_onc2_perp__col with P A B; assumption.
Qed.

(** Euclid Book III Prop 4.
 If in a circle two straight lines which do not pass through the center cut one another,
 then they do not bisect one another.
 *)

Lemma mid2_onc4__eq : forall O P A B C D X, B <> C-> A <> B -> 
 OnCircle A O P ->
 OnCircle B O P ->
 OnCircle C O P ->
 OnCircle D O P ->
 Midpoint X A C ->
 Midpoint X B D ->
 X=O.
Proof.
intros O P A B C D X Hbc.
intros.
assert(HH:=mid_onc2__per O P A C X H0 H2 H4).
assert(HP:=mid_onc2__per O P B D X H1 H3 H5).

induction(eq_dec_points X O).
auto.
assert(Col A B X).
apply(per2__col A B O X); Perp.
unfold Midpoint in *.
spliter.
assert(Col B X D).
apply bet_col; auto.
assert(Col A X C).
ColR.

induction(eq_dec_points A X).
subst X.
treat_equalities.
assert(OutCircleS D O P).
apply(onc2_out__outcs O P A B D); auto.
assert_diffs.
unfold Out.
split.
auto.
split.
auto.
left; Between.

unfold OutCircleS in *.
unfold Lt in *.
spliter.
unfold OnCircle in H3.
apply False_ind.
absurd (Cong O P O D);Cong.

assert(Col A B C). 
ColR.

assert(C = A \/ C = B).
apply(line_circle_two_points O P A B C); Col.
destruct H14.
treat_equalities.
intuition.
treat_equalities.
assert(A = D) by
(apply (symmetric_point_uniqueness C X); split; Between; Cong).
treat_equalities.
tauto.
Qed.

(** Euclid Book III Prop 9.
 If a point is taken within a circle,
 and more than two equal straight lines fall from the point on the circle,
 then the point taken is the center of the circle.
*)

Lemma cong2_onc3__eq : forall O P X A B C, A <> B -> A <> C -> B <> C ->
  OnCircle A O P -> OnCircle B O P -> OnCircle C O P ->
  Cong X A X B -> Cong X A X C ->
  X = O.
Proof.
  intros O P X A B C HAB HAC HBC HAOn HBOn HCOn HCong1 HCong2.
  assert (HCop := all_coplanar A B C O).
  assert (HCop1 := all_coplanar A B C X).
  apply cong2_cop2_onc3__eq with P A B C; assumption.
Qed.

Lemma onc2_mid_cong_col : forall O P U V M X,
 U <> V ->OnCircle U O P -> OnCircle V O P -> Midpoint M U V -> Cong U X V X -> Col O X M.
Proof.
intros.
assert(HH:=mid_onc2__per O P U V M H0 H1 H2).
assert(Per X M U).
unfold Per.
exists V.
unfold OnCircle in *.
split; Cong.
apply(per2__col _ _ U); auto.
assert_diffs.
auto.
Qed.


Lemma cong_onc3_cases : forall O P A X Y,
 Cong A X A Y ->
 OnCircle A O P -> OnCircle X O P -> OnCircle Y O P ->
 X = Y \/ ReflectL X Y O A.
Proof.
intros.
unfold OnCircle in *.
induction(eq_dec_points X Y).
left; auto.
right.
assert(HH:= midpoint_existence X Y).
ex_and HH M.
assert(Per O M X).
{
  apply(mid_onc2__per O P X Y M); Circle.
}
assert(Per A M X).
{
  unfold Per.
  exists Y.
  split; auto.
}
assert(Col A O M).
{
  apply (per2__col _ _ X); auto.
  intro.
  treat_equalities; tauto.
}

unfold ReflectL.
split.
exists M.
split; Midpoint.
Col.
left.

unfold Midpoint in *.
spliter.

induction(eq_dec_points M O).
subst M.
apply per_perp_in in H6.
apply perp_in_comm in H6.
apply perp_in_perp in H6.
apply perp_sym in H6.
apply (perp_col X O O A Y) in H6; Col.
Perp.
intro.
treat_equalities; tauto.
intro.
treat_equalities; tauto.

apply(perp_col O M Y X A);Col.
intro.
treat_equalities; tauto.
apply per_perp_in in H5.
apply perp_in_comm in H5.
apply perp_in_perp in H5.
apply perp_sym in H5.
apply(perp_col X M M O Y) in H5; auto.
Perp.
Col.
auto.
intro.
treat_equalities; tauto.
Qed.


Lemma bet_cong_onc3_cases : forall O P A X Y T,
 T <> O -> Bet A O T -> Cong T X T Y ->
 OnCircle A O P  -> OnCircle X O P  -> OnCircle Y O P ->
 X = Y \/ ReflectL X Y O A.
Proof.
intros.
unfold OnCircle in *.
induction(eq_dec_points O P).
treat_equalities.
left; auto.

induction(eq_dec_points T X).
treat_equalities.
left; auto.

assert(CongA T O X T O Y /\ CongA O T X O T Y /\ CongA T X O T Y O).
{
  apply(l11_51 O T X O T Y); Cong.
    intro.
    treat_equalities; tauto.
  apply cong_transitivity with O P; Cong.
}
spliter.
assert(Out T O A).
{
  unfold Out.
  repeat split; auto.
  intro.
  treat_equalities; tauto.
  Between.
}
assert(Cong A X A Y).
{ apply(cong2_conga_cong A T X A T Y); Cong.
  apply (out_conga O T X O T Y); auto.
  apply out_trivial; auto.
  apply out_trivial.
  intro.
  treat_equalities; tauto.
}
apply (cong_onc3_cases O P); auto.
Qed.

Lemma prop_7_8 : forall O P A B T X Y , Diam A B O P -> Bet A O T 
                               -> OnCircle X O P -> OnCircle Y O P
                               -> LeA A O X A O Y -> Le T Y T X.
Proof.
intros.
assert(HD:=H).
unfold Diam in H.
spliter.
unfold OnCircle in *.
induction(eq_dec_points O P).
subst P.
treat_equalities; auto.
apply le_reflexivity.

induction(eq_dec_points O T).
treat_equalities.
apply cong__le, cong_transitivity with O P; Cong.

induction(cong_dec A X A Y).
assert(X = Y \/ ReflectL X Y O A).
{
  apply(cong_onc3_cases O P A X Y); Circle.
}
induction H9.
treat_equalities.
apply le_reflexivity.
apply cong__le.
apply cong_symmetry.
apply cong_commutativity.
apply(is_image_spec_col_cong O A X Y T); auto.
unfold Diam in *.
spliter.
ColR.

assert(Le T X T A).
{
  apply(bet_onc_le_b O P A B T X HD H0).
  Circle.
}
assert_diffs.

assert(LeA Y O T X O T).
{
  apply lea_comm.
  apply(l11_36 A O X A O Y T T); auto.
}

assert(Lt T Y T X).
{
  assert(Cong O X O Y) by (apply cong_transitivity with O P; Cong).
  apply(t18_18 O T X O T Y); Cong.
  unfold LtA.
  split; auto.
  intro.
  assert(Cong Y T X T).
  {
    apply(cong2_conga_cong Y O T X O T); Cong.
  }
  assert(CongA A O X A O Y).
  apply(l11_13 T O X T O Y A A); Between.
  CongA.
  apply H8.
  apply(cong2_conga_cong A O X A O Y); Cong.
}
apply lt__le.
assumption.
Qed.




Lemma Prop_7_8_uniqueness : forall O P A X Y Z T, T <> O -> X <> Y ->
  Bet A O T -> Cong T X T Y -> Cong T X T Z ->
  OnCircle A O P -> OnCircle X O P -> OnCircle Y O P -> OnCircle Z O P ->
  Z = X \/ Z = Y.
Proof.
intros.
induction(eq_dec_points O P).
unfold OnCircle in *.
treat_equalities.
auto.
assert(X = Y \/ ReflectL X Y O A).
{
  apply(bet_cong_onc3_cases O P A X Y T); auto.
}
assert(X = Z \/ ReflectL X Z O A).
{
  apply(bet_cong_onc3_cases O P A X Z T); auto.
}
assert(Y = Z \/ ReflectL Y Z O A).
{
  apply(bet_cong_onc3_cases O P A Y Z T); auto.
  apply cong_transitivity with T X; Cong.
}
induction H9.
contradiction.
induction H10.
auto.
induction H11.
auto.
assert(HH:=l10_2_uniqueness_spec O A Z X Y H10 H11).
contradiction.
Qed.

Lemma chords_midpoints_col_par : forall O P A M B C N D, 
 O <> P ->
 OnCircle A O P -> OnCircle B O P ->
 OnCircle C O P -> OnCircle D O P ->
 Midpoint M A B -> Midpoint N C D ->
 Col O M N -> ~ Col O A B -> ~ Col O C D -> Par A B C D.
Proof.
intros.
assert(Perp O M A B).
{
  apply(mid_onc2__perp O  P A B M); Circle.
  intro.
  treat_equalities.
  apply H7.
  Col.
  intro.
  treat_equalities.
  apply H7; Col.
}
assert(Perp O N C D).
{
  apply(mid_onc2__perp O  P C D N); Circle.
  intro.
  treat_equalities.
  apply H8.
  Col.
  intro.
  treat_equalities.
  apply H8; Col.
}
assert(Perp O M C D).
{
  apply (perp_col O N C D M); Col.
  intro.
  treat_equalities.
  apply H7; Col.
}
apply (l12_9_2D A B C D O M); Perp.
Qed.

Lemma onc3_mid2__ncol : forall O P A B C A' B',
 O <> P -> 
 OnCircle A O P -> OnCircle B O P -> OnCircle C O P ->
 Midpoint A' A C -> Midpoint B' B C -> ~ Col A B C ->
 ~ Col O A' B' \/ A' = O \/ B' = O.
Proof.
intros.
induction(col_dec O A C).
assert(A = C \/ Midpoint O A C).
{
  unfold OnCircle in *.
  apply l7_20; eCong.
  Col.
}
induction H7.
treat_equalities.
apply False_ind.
apply H5; Col.
right; left.
apply (l7_17 A C); auto.

induction(col_dec O B C).
assert(B = C \/ Midpoint O B C).
{
  unfold OnCircle in *.
  apply l7_20; eCong.
  Col.
}
induction H8.
treat_equalities.
apply False_ind.
apply H5; Col.
right; right.
apply (l7_17 B C); auto.
left.
intro.
assert(HH:=chords_midpoints_col_par O P A A' C B B' C H H0 H2 H1 H2 H3 H4 H8 H6 H7).
induction HH.
apply H9.
exists C.
split; Col.
spliter; contradiction.
Qed.

(** Euclid Book III Prop 9.
 If a point is taken within a circle,
 and more than two equal straight lines fall from the point on the circle, 
 then the point taken is the center of the circle.*)

Lemma onc4_cong2__eq: 
 forall A B C D O P X,
 A<>B -> C<>D ->
 ~ Par A B C D ->
 OnCircle A O P ->
 OnCircle B O P ->
 OnCircle C O P ->
 OnCircle D O P ->
 Cong A X B X ->
 Cong C X D X ->
 O=X.
Proof.
intros.

assert(HP:O <> P).
{
intro.
unfold OnCircle in *.
treat_equalities. intuition.
}

assert(HH:= midpoint_existence A B).
ex_and HH M.
assert(HH:= midpoint_existence C D).
ex_and HH N.

assert(Col O X M)
 by (apply(onc2_mid_cong_col O P A B M X); auto).
assert(Col O X N)
 by (apply(onc2_mid_cong_col O P C D N X); auto).

induction(eq_dec_points O X).
- auto.
- assert(Col O M N); eCol.


assert(HH1:=cong_perp_or_mid A B M X H H8 H6).
assert(HH2:=cong_perp_or_mid C D N X H0 H9 H7).

induction HH1.
subst X.
induction HH2.
subst N.

induction(col_dec O A B).
assert(A = B \/ Midpoint O A B).
unfold OnCircle in *.
apply l7_20; Col.
apply cong_transitivity with O P; Cong.
induction H15.
contradiction.
assert(M = O).
apply (l7_17 A B); auto.
subst M; tauto.

induction(col_dec O C D).
assert(C = D \/ Midpoint O C D).
unfold OnCircle in *.
apply l7_20; Col.
apply cong_transitivity with O P; Cong.
induction H16.
contradiction.
apply (l7_17 C D); auto.
assert(HM1:=mid_onc2__perp O P A B M H12 H H2 H3 H8).
assert(HM2:=mid_onc2__perp O P C D M H12 H0 H4 H5 H9).
apply False_ind.
apply H1.
apply (l12_9_2D _ _ _ _ O M); Perp.

spliter.
apply perp_in_perp in H15.
induction(col_dec O A B).
assert(A = B \/ Midpoint O A B).
unfold OnCircle in *.
apply l7_20; Col.
apply cong_transitivity with O P; Cong.
induction H17.
contradiction.
assert(M = O).
apply (l7_17 A B); auto.
subst M; tauto.
assert(HM1:=mid_onc2__perp O P A B M H12 H H2 H3 H8).
apply(perp_col M N C D O ) in H15; Col.
apply False_ind.
apply H1.
apply (l12_9_2D _ _ _ _ O M); Perp.
induction HH2.
subst X.
spliter.

induction(col_dec O C D).
assert(C = D \/ Midpoint O C D).
unfold OnCircle in *.
apply l7_20; Col.
apply cong_transitivity with O P; Cong.
induction H17.
contradiction.
apply (l7_17 C D); auto.

assert(HM1:=mid_onc2__perp O P C D N H12 H0 H4 H5 H9).
apply perp_in_perp in H15.
apply False_ind.
apply H1.
apply(perp_col N M A B O) in H15; Col.

apply (l12_9_2D _ _ _ _ O N); Perp.
spliter.
apply perp_in_perp in H17.
apply perp_in_perp in H16.

apply(perp_col X M A B O) in H17; Col.
apply(perp_col X N C D O) in H16; Col.
apply False_ind.
apply H1.
apply (l12_9_2D _ _ _ _ O X); Perp.
Qed.


End Circle_2D.