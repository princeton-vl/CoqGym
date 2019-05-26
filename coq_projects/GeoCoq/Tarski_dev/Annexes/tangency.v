Require Export GeoCoq.Tarski_dev.Annexes.circles.
Require Export GeoCoq.Axioms.continuity_axioms.

Section Tangency.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

(** Euclid Book III, Prop 11 and Prop 12
 We do not need to distinguish between internal or external tangency. *)

(** If two circles are tangent, the common point is on the line joining the centers. *)

Lemma TangentCC_Col : forall A B C D X,
 TangentCC A B C D ->
 OnCircle X A B ->
 OnCircle X C D ->
 Col X A C.
Proof.
intros.

unfold TangentCC in *.

induction(eq_dec_points A C).
subst C.
Col.

assert(HS:=ex_sym1 A C X H2).
ex_and HS Y.
ex_and H4 M.

assert(Cong X A Y A).
apply(is_image_col_cong A C X Y A H2 H6); Col.
assert(Cong X C Y C).
apply(is_image_col_cong A C X Y C H2 H6); Col.

destruct H.
unfold unique in H.

assert(x =X).
apply H.
split; auto.
subst x.
assert(OnCircle Y A B).
unfold OnCircle in *.
apply cong_transitivity with A X; Cong.
assert(OnCircle Y C D).
unfold OnCircle in *.
apply cong_transitivity with C X; Cong.
assert(X = Y).
apply H.
split; auto.
subst Y.

unfold Reflect in H6.
induction H6.
spliter.
unfold ReflectL in *.
spliter.
ex_and H11 Z.

assert(Z = X).
apply l7_3; auto.
subst Z.
Col.
spliter.
contradiction.
Qed.

Lemma tangent_neq : forall A B O P,
 O<>P -> Tangent A B O P -> A<>B.
Proof.
intros.
intro.
subst B.
unfold Tangent in *.
unfold unique in *.
ex_and H0 T.
assert(HH:=symmetric_point_construction T O).
ex_and HH T'.
assert(OnCircle T' O P).
apply (symmetric_oncircle T T' O P); auto.
assert(T = T').
apply H1.
split; Col.
subst T'.
apply H.
apply l7_3 in H3.
subst T.
unfold OnCircle in H2.
treat_equalities; tauto.
Qed.

(** A line going through the center is not tangent to the circle. *)

Lemma diam_not_tangent : forall O P A B, 
  P <> O -> Col O A B -> ~ Tangent A B O P.
Proof.
intros O P A B HOP HCol HTan.
destruct HTan as [Q [[HQCol HQOn] HQUnique]].
destruct(eq_dec_points A B).
  subst B.
  destruct (segment_construction Q O O P) as [Q' [HQ'1 HQ'2]].
  assert (HQQ' : Q <> Q') by (intro; treat_equalities; auto).
  apply HQQ', HQUnique; split; Col.
destruct (diff_col_ex3 A B O) as [C [HOC [HAC [HBC HColC]]]]; Col.
destruct (diam_points O P C) as [Q1 [Q2 [HBet [HQ1Q2C [HQ1On HQ2On]]]]].
assert (HQ1Q2 : Q1 <> Q2).
  intro; treat_equalities; auto.
assert(Q = Q1) by (apply HQUnique; split; ColR).
assert(Q = Q2) by (apply HQUnique; split; ColR).
treat_equalities; auto.
Qed.

(** Every point on the tangent different from the point of tangency is strictly outside the circle. *)

Lemma tangent_out : forall A B O P T X,
  X <> T -> Col A B X -> TangentAt A B O P T -> OutCircleS X O P.
Proof.
intros.
unfold TangentAt in *.
spliter.

induction(eq_dec_points O P).
subst P.
unfold OutCircleS.
unfold Lt.

split.
apply le_trivial.
intro.
unfold OnCircle in *.
assert(T = O).
apply cong_identity with O; Cong.
assert(X = O).
apply cong_identity with O; Cong.
subst O.
contradiction.

assert(InCircle X O P -> X = T).
intro.

assert(HH:= chord_completion O P T X H3 H5).
ex_and HH T'.
assert(A <> B).
apply (tangent_neq A B O P); auto.
unfold Tangent in *.
unfold unique in *.
ex_and H1 TT.
assert(TT= T).
apply H9.
split; auto.
subst TT.
assert(T = T').
apply H9.
split; auto.
apply bet_col in H7.

assert(Col A X T); ColR.
subst T'.
apply between_identity in H7.
subst X.
tauto.

assert(~InCircle X O P).
intro.
apply H5 in H6.
contradiction.
apply ninc__outcs.
assumption.
Qed.

(** If line AB is tangent to a circle of center O at a point T, then OT is perpendicular to AB.
This is Euclid Book III, Prop 18 *)

Lemma tangentat_perp : 
forall A B O P T, O <> P -> TangentAt A B O P T -> Perp A B O T.
Proof.
intros.
assert(TA:=H0).
unfold TangentAt in H0.
spliter.
assert(A <> B).
apply (tangent_neq A B O P); auto.
assert(~Col A B O).
intro.
assert(~Tangent A B O P).
apply(diam_not_tangent); Col.
contradiction.

assert(HH:= l8_18_existence A B O H4).
ex_and HH R.

induction(eq_dec_points T R).
subst R.
auto.

assert(HH:= (symmetric_point_construction T R)).
ex_and HH T'.

induction(eq_dec_points A R).
subst A.
assert(Perp T R R O).
apply perp_comm.
apply (perp_col R B O R T); Col.
assert(Perp_at R T R R O).
apply perp_in_comm.
apply perp_perp_in.
Perp.
assert(Per O R T).
apply l8_2.
apply perp_in_per; auto.
unfold Per in *.
ex_and H11 T''.
assert(T' = T'').
apply (symmetric_point_uniqueness T R T' T''); auto.
subst T''.

assert(T <> T').
intro.
subst T'.
apply H7.
apply sym_equal.
apply l7_3; auto.

assert(OnCircle T' O P).
unfold OnCircle in *.
apply cong_transitivity with O T; Cong.

assert(OutCircleS T' O P).
apply (tangent_out R B O P T T'); ColR.
unfold OutCircleS in *.
unfold Lt in *.
spliter.
unfold OnCircle in H14.
apply False_ind.
apply H16.
Cong.


assert(Perp T R R O).
apply perp_comm.
apply (perp_col R A O R T); Col.
apply perp_left_comm.
eapply (perp_col A B O R R); auto.
unfold Midpoint in *.
spliter.
apply bet_col in H8.
eCol.
assert(Perp_at R T R R O).
apply perp_in_comm.
apply perp_perp_in.
Perp.


assert(Per O R T).
apply l8_2.
apply perp_in_per; auto.
unfold Per in *.
ex_and H12 T''.
assert(T' = T'').
apply (symmetric_point_uniqueness T R T' T''); auto.
subst T''.

assert(T <> T').
intro.
subst T'.
apply H7.
apply sym_equal.
apply l7_3; auto.

assert(OnCircle T' O P).
unfold OnCircle in *.
apply cong_transitivity with O T; Cong.

assert(OutCircleS T' O P).
unfold Midpoint in *.
spliter.
apply bet_col in H12.
apply (tangent_out A B O P T T'); auto.
ColR.
unfold OutCircleS in *.
unfold Lt in *.
spliter.
unfold OnCircle in H14.
apply False_ind.
apply H17.
Cong.
Qed.

(** AB is tangent to the circle (O,P) iff they intersect at a point X
such that AB is perpendicular to OX. *)

Lemma tangency_chara : forall A B O P, P <> O ->
 (exists X, OnCircle X O P /\ Perp_at X A B O X) <-> Tangent A B O P.
Proof.
intros.

split.
intro.
ex_and H0 T.
unfold Tangent.
unfold unique.
exists T.
split.
split; auto.
apply perp_in_col in H1.
tauto.
intros.
spliter.
assert(Col A B T).
apply perp_in_col in H1.
tauto.

induction(eq_dec_points T x').
auto.
apply False_ind.

assert(Perp T x' O T).
apply (perp_col2 A B); auto.
apply perp_in_perp in H1.
auto.

assert(Perp_at T T x' O T).
apply perp_perp_in; auto.

assert(Per x' T O).
apply perp_in_comm in H7.
apply perp_in_per; auto.

assert(~Col x' T O).
apply perp_not_col in H6.
ColR.

assert(Lt T x' x' O /\ Lt T O x' O).
assert_diffs.
apply(l11_46 x' T O); auto.
unfold OnCircle in *.
unfold Lt in H10.
spliter.
apply H12.
apply cong_transitivity with O P; Cong.

intros.
assert(HT:=H0).
unfold Tangent in H0.
unfold unique in H0.
ex_and H0 T.

assert(TangentAt A B O P T).
unfold TangentAt.
repeat split; auto.
exists T.
split; auto.
assert(HH:=tangentat_perp A B O P T).
assert(Perp A B O T).
apply HH; auto.

apply(l8_14_2_1b_bis A B O T T H4); Col.
Qed.


Lemma tangency_chara2 : forall A B O P Q,
 OnCircle Q O P -> Col Q A B -> 
 ((forall X, Col A B X -> X = Q \/ OutCircleS X O P) <-> Tangent A B O P).
Proof.
intros.
split.
intros.
unfold Tangent.
unfold unique.
exists Q.
repeat split; Col.
intros.
spliter.
assert(HH:=(H1 x' H2)).
induction HH.
auto.
unfold OnCircle in *.
unfold OutCircleS in *.
unfold Lt in *.
spliter.
apply False_ind.
apply H5; Cong.

intros.
assert(TangentAt A B O P Q).
unfold TangentAt.
repeat split; Col.

induction(eq_dec_points X Q).
left; auto;

unfold Tangent in H1.
right.

apply(tangent_out A B O P Q X); auto.
Qed.


Lemma tangency_chara3 : forall A B O P Q, A <> B ->
 OnCircle Q O P -> Col Q A B -> 
 ((forall X, Col A B X -> OutCircle X O P) <-> Tangent A B O P).
Proof.

intros.
split.
intros.

assert(HT:= (tangency_chara2 A B O P Q H0 H1)); auto.
apply HT.
intros.
induction(eq_dec_points X Q).
left; auto.
right.
assert(OutCircle X O P).
apply H2; Col.

unfold OutCircleS.
unfold OutCircle in H5.
unfold Lt.
split; auto.
intro.

assert(HH:=midpoint_existence X Q).
ex_and HH M.
assert(InCircleS M O P).
apply(bet_inc2__incs O P Q X M); Circle.
intro.
subst M.

apply l7_2 in H7.
apply is_midpoint_id in H7.
subst X; tauto.
intro.
subst M.
apply is_midpoint_id in H7.
contradiction.
unfold Midpoint in H7.
spliter.
Between.

assert(Col A B M).
unfold Midpoint in *.
spliter.
ColR.
assert(HH:=(H2 M H9)).
unfold InCircleS in *.
unfold OutCircle in *.

apply le__nlt in HH.
contradiction.

intros.
assert(TangentAt A B O P Q).
unfold TangentAt.
repeat split; Col.

induction(eq_dec_points X Q).
subst X.
unfold TangentAt in *.
spliter.
apply onc__outc; auto.

assert(OutCircleS X O P).
apply(tangent_out A B O P Q X); auto.
unfold OutCircleS in *.
unfold OutCircle.
unfold Lt in H6.
tauto.
Qed.

(** Euclid Book III Prop 5 
 If two circles cut one another, then they do not have the same center. *)

Lemma intercc__neq :  forall A B C D,
 InterCC A B C D -> A<>C.
Proof.
intros.
unfold InterCC in *.
ex_and H P.
ex_and H0 Q.
unfold InterCCAt in *.
spliter.
unfold OnCircle in *.
intro.
subst C.
apply H.
unfold EqC.
unfold OnCircle in *.
assert(Cong A B A D) by (apply cong_transitivity with A P; Cong).
intro.
split.
intro.
apply cong_transitivity with A B; Cong.
intro.
apply cong_transitivity with A D; Cong.
Qed.

(** Euclid Book III Prop 6 
If two circles touch one another, then they do not have the same center.
*)

Lemma tangentcc__neq: forall A B C D,
 A<>B ->
 TangentCC A B C D ->
 A<>C.
Proof.
intros.
unfold TangentCC in *.
unfold unique in *.
ex_and H0 T.
intro.
subst C.
unfold OnCircle in *.
assert(Cong A B A D) by (apply cong_transitivity with A T; Cong).
assert(T = B).
apply(H1 B); Cong.
subst T.
assert(HH:=symmetric_point_construction B A).
ex_and HH B'.
unfold Midpoint in *.
spliter.
assert(B = B').
  apply(H1 B'); split; Cong.
  apply cong_transitivity with A B; Cong.
subst B'.
treat_equalities; tauto.
Qed.

Lemma interccat__neq : forall A B C D P Q, InterCCAt A B C D P Q -> A <> C.
Proof.
intros.
apply intercc__neq  with B D.
unfold InterCC.
exists P; exists Q;auto.
Qed.

(** Prop 17 construction of the tangent to a circle at a given point *)

Lemma tangent_construction : forall O P X, segment_circle -> OutCircle X O P 
                                                  -> exists Y, Tangent X Y O P.
Proof.
intros.
induction(eq_dec_points O P).
subst P.
exists O.
unfold Tangent.
unfold unique.
unfold OnCircle in *.
exists O.
repeat split; Col; Cong.
intros.
spliter.
treat_equalities; auto.

assert(O <> X).
{
  intro.
  rewrite H2 in *;clear H2.
  treat_equalities.
  intuition.
}

assert(HH:=circle_cases O P X).
induction HH.

assert(HH:= perp_exists X O X H2).
ex_and HH Y.
unfold OnCircle in *.
exists Y.
apply tangency_chara; auto.
exists X.
apply perp_perp_in in H4.
split; Circle.

induction H3.
unfold OutCircle in *.
unfold InCircleS in *.
apply lt__nle in H3; contradiction.


assert(exists Q : Tpoint, OnCircle Q O P /\ Out O X Q).
{
  apply(onc_exists); auto.
}

ex_and H4 U.

assert(Bet O U X).
{
  unfold Out in H5.
  spliter.
  induction H7.
  unfold OutCircleS in *.
  unfold OnCircle in *.
  assert(Le O X O U).
  {
    unfold Le.
    exists X.
    split; Cong.
  }
  assert(Lt O U O X).
  {
    apply(cong2_lt__lt O P O X); Cong.
  }
  apply le__nlt in H8.
  contradiction.
  assumption.
}

assert(exists X : Tpoint, Perp U X O U).
{
  apply(perp_exists U O U).
  intro.
  unfold OnCircle in H4.
  treat_equalities; tauto.
}
ex_and H7 R.
assert(HP:=symmetric_point_construction X O).
ex_and HP W.
unfold Midpoint in *.
spliter.
assert(exists X0 : Tpoint, (Bet U R X0 \/ Bet U X0 R) /\ Cong U X0 W X).
{
  apply(segment_construction_2 R U W X).
  apply perp_distinct in H8.
  spliter.
  auto.
}

ex_and H10 T.

assert(InCircleS U O X).
{
  unfold InCircleS.
  unfold OutCircleS in H3.
  unfold OnCircle in H4.
  apply(cong2_lt__lt O P O X); Cong.
}

assert(OutCircleS T O X).
{
  apply(diam_cong_incs__outcs O X X W U T); auto.
  unfold Diam.
  unfold OnCircle.
  repeat split; Cong.
  Cong.
}
unfold segment_circle in H.
assert(exists Z : Tpoint, Bet U Z T /\ OnCircle Z O X).
{
  apply(H O X U T).
  apply incs__inc; auto.
  apply outcs__outc; auto.
}

ex_and H14 Y.
assert(exists Q : Tpoint, OnCircle Q O P /\ Out O Y Q).
{
  apply(onc_exists O P Y); auto.
  intro.
  unfold OnCircle in H15.
  treat_equalities; tauto.
}
ex_and H16 V.

exists V.

assert(Bet O V Y).
{
  unfold Out in H17.
  spliter.
  induction H19.
  unfold OutCircleS in H3.
  assert(Lt O V O Y).
  {
    apply (cong2_lt__lt O P O X); Cong.
  }
  unfold OnCircle in *.
  assert(Le O Y O V).
  {
    unfold Le.
    exists Y.
    split; Cong.
  }
  apply le__nlt in H21.
  contradiction.
  assumption.
}

assert(Cong O X O Y) by Cong.
assert(Cong O U O V) by (apply cong_transitivity with O P; Cong).


assert(CongA X O V Y O U).
{
  unfold OnCircle in *.
  apply(out_conga U O Y Y O U X V Y U).
  apply conga_left_comm.
  apply conga_refl; intro;treat_equalities; tauto.
  unfold Out.
  repeat split; try(intro;treat_equalities; tauto).
  left; auto.
  unfold Out.
  repeat split; try(intro;treat_equalities; tauto).
  right; auto.
  apply out_trivial;  intro;treat_equalities; tauto.
  apply out_trivial;  intro;treat_equalities; tauto.
}

assert(Cong V X U Y).
{

  apply(cong2_conga_cong V O X U O Y); Cong.
  CongA.
}

assert(CongA O U Y O V X).
{
  unfold OnCircle in *.
  apply(cong3_conga O U Y O V X).
  intro;treat_equalities; tauto.
  intro;treat_equalities.
  unfold OutCircleS in *.
  unfold Lt in *.
  spliter.
  (assert (Cong O P O V) by finish;intuition) ||
  (assert (Cong O P O Y) by finish;intuition ).
  unfold Cong_3.
  split.
  finish.
  split;finish.
}

assert(Per O V X).
{
  apply(l11_17 O U Y O V X).
  apply(perp_col _ _ _ _ Y) in H8.

  apply perp_perp_in in H8.
  apply perp_in_comm in H8.
  apply perp_in_per.
  apply perp_in_sym.
  apply perp_in_comm.
  assumption.
  intro.
  treat_equalities.
  unfold CongA in H23.
  tauto.
  induction H10;
  ColR.
  assumption.
}

apply tangency_chara; auto.
exists V.
split; auto.
apply per_perp_in in H24; Cong.
apply perp_in_left_comm.
apply perp_in_sym.
assumption.
unfold OnCircle in *.
intro.
treat_equalities; tauto.
intro.
treat_equalities.
unfold CongA in H23.
tauto.
Qed.

Lemma interccat__ncol : forall A B C D P Q,
 InterCCAt A B C D P Q -> ~ Col A C P.
Proof.
intros.
intro.
assert (HH := H).
unfold InterCCAt in HH.
spliter.
apply H2.
apply (l4_18 A C).
apply interccat__neq in H.
auto.
assumption.
apply cong_transitivity with A B; Cong.
apply cong_transitivity with C D; Cong.
Qed.

(** Euclid Book III Prop 10
 A circle does not cut a circle at more than two points.
 *)
Lemma cop_onc2__oreq : forall A B C D P Q,
 InterCCAt A B C D P Q -> Coplanar A C P Q ->
 forall Z, OnCircle Z A B -> OnCircle Z C D -> Coplanar A C P Z -> Z=P \/ Z=Q.
Proof.
intros.
assert(HIC := H).
unfold InterCCAt in H.
spliter.
induction (eq_dec_points Z Q).
  right; auto.
left.
assert(HH:=midpoint_existence Q P).
ex_and HH M.
assert(Per A M Q).
apply(mid_onc2__per A B Q P M); auto.
assert(Per C M Q).
apply(mid_onc2__per C D Q P M); auto.

assert(HH:=midpoint_existence Z Q).
ex_and HH N.

assert(Per A N Q).
apply(mid_onc2__per A Z Q Z).
apply cong_transitivity with A B; Cong.
Circle.
Midpoint.


assert(Per C N Q).
apply(mid_onc2__per C Z Q Z).
apply cong_transitivity with C D; Cong.
Circle.
Midpoint.

assert(Col A C M).
apply cop_per2__col with Q; auto.
induction(col_dec P Q A).
exists M.
left.
split; ColR.
apply coplanar_perm_12, col_cop__cop with P; Col; Cop.
assert_diffs;auto.

assert(A <> C).
apply(interccat__neq A B C D P Q); auto.

assert(Col A C N).
apply cop_per2__col with Q; auto.
apply coplanar_perm_12, col_cop__cop with Z; Col.
apply coplanar_trans_1 with P; Cop.
apply interccat__ncol in HIC.
Col.
assert_diffs;auto.

assert(Perp A C Q P).
induction(eq_dec_points A M).
subst M.
apply per_perp_in in H12; auto.
apply perp_in_comm in H12.

apply perp_in_perp in H12.
apply perp_sym.
apply (perp_col Q A A C P); Perp.
ColR.
assert_diffs;auto.

apply per_perp_in in H11; auto.
apply perp_in_comm in H11.
apply perp_in_perp in H11.
apply perp_comm in H11.
apply (perp_col A M M Q C) in H11; Col.
apply perp_sym in H11.
apply perp_comm in H11.
apply (perp_col Q M C A P) in H11; Col.
Perp.
assert_diffs;auto.

assert(Col Q N Z).
ColR.

assert(Perp A C Q Z).
induction(eq_dec_points A N).
subst N.
apply per_perp_in in H15; auto.
apply perp_in_comm in H15.
apply perp_in_perp in H15.
apply perp_sym.
apply (perp_col Q A A C Z); Perp.
assert_diffs;auto.

apply per_perp_in in H14; auto.
apply perp_in_comm in H14.
apply perp_in_perp in H14.
apply perp_comm in H14.
apply (perp_col A N N Q C) in H14; Col.
apply perp_sym in H14.
apply perp_comm in H14.
apply (perp_col Q N C A Z) in H14; Col.
Perp.
assert_diffs;auto.

apply perp_sym in H21.
apply perp_sym in H19.
assert (HH : Par Q P Q Z).
apply (l12_9 _ _ _ _ A C); auto.
Cop.
apply coplanar_trans_1 with P; Cop.
apply interccat__ncol in HIC.
Col.
induction HH.
unfold Par_strict in H22.
spliter.
apply False_ind.
apply H25.
exists Q.
split; ColR.
spliter.
assert(Z = P \/ Z = Q).
apply(line_circle_two_points A B P Q Z H4); auto.
induction H26; tauto.
Qed.

End Tangency.

Section Tangency_2D.

Context `{T2D:Tarski_2D}.

Lemma onc2__oreq : forall A B C D P Q,
 InterCCAt A B C D P Q ->
 forall Z, OnCircle Z A B -> OnCircle Z C D  -> Z=P \/ Z=Q.
Proof.
intros.
assert(HCop := all_coplanar A C P Q).
assert(HCop1 := all_coplanar A C P Z).
apply(cop_onc2__oreq A B C D); assumption.
Qed.

End Tangency_2D.