

Section Props_Confluence.

  Variable R R' : red_rule.

  Hypothesis same_rel : forall e : env, same_relation term (R e) (R' e).
  Hypothesis R_confl : confluent R.


  Lemma confluent_is_ext : confluent R'.
Proof.
unfold confluent, commut, transp in |- *.
intros.
elim same_rel with e.
unfold inclusion in |- *; intros.
elim R_confl with e x y z; auto with pts; intros.
exists x0; auto with pts.
Qed.


  Lemma strip_confl :
   forall e : env, commut term (R_rt R e) (transp term (R e)).
Proof.
unfold commut, transp in |- *.
simple induction 1; intros.
elim R_confl with e y0 x0 z; intros; auto with pts.
exists x1; auto with pts.

exists z; auto with pts.

elim H1 with z0; intros; auto with pts.
elim H3 with x1; intros; auto with pts.
exists x2; auto with pts.
red in |- *.
apply rt_trans with x1; auto with pts.
Qed.

  Lemma strongly_confluent : confluent (R_rt R).
Proof.
unfold confluent, commut, transp in |- *.
simple induction 1; intros.
elim strip_confl with e z x0 y0; intros; auto with pts.
exists x1; auto with pts.

exists z; auto with pts.

elim H1 with z0; intros; auto with pts.
elim H3 with x1; intros; auto with pts.
exists x2; auto with pts.
red in |- *.
apply rt_trans with x1; auto with pts.
Qed.

End Props_Confluence.


Section Props_Church_Rosser.

  Variable R : red_rule.
  Hypothesis Rconfl : confluent (R_rt R).

  Lemma confl_church_rosser : church_rosser R.
Proof.
red in |- *.
simple induction 1; intros.
split with y; auto with pts.

split with x; auto with pts.

inversion_clear H1.
split with x0; trivial.

inversion_clear H1.
inversion_clear H3.
elim Rconfl with (1 := H5) (2 := H1); intros.
split with x2.
red in |- *; apply rt_trans with x0; auto.

red in |- *; apply rt_trans with x1; auto.
Qed.

End Props_Church_Rosser.


Section Tait_Martin_Lof.

  Variable R R' : red_rule.

  Hypothesis R'_confl : confluent R'.
  Hypothesis incl_R_R' : forall e : env, inclusion term (R e) (R' e).
  Hypothesis incl_R'_R_rt : forall e : env, inclusion term (R' e) (R_rt R e).


  Lemma closures_are_equal :
   forall e : env, same_relation term (R_rt R' e) (R_rt R e).
Proof.
unfold same_relation, inclusion, R_rt in |- *.
split.
simple induction 1; intros; auto with pts.
apply (incl_R'_R_rt e x0 y0); auto with pts.

apply rt_trans with y0; auto with pts.

simple induction 1; intros; auto with pts.
apply rt_step.
apply (incl_R_R' e x0 y0); auto with pts.

apply rt_trans with y0; auto with pts.
Qed.


  Lemma confl_closure : confluent (R_rt R).
Proof.
apply confluent_is_ext with (R_rt R').
exact closures_are_equal.

apply strongly_confluent.
trivial with pts.
Qed.


  Lemma TML_Church_rosser : church_rosser R.
Proof.
apply confl_church_rosser.
exact confl_closure.
Qed.

End Tait_Martin_Lof.