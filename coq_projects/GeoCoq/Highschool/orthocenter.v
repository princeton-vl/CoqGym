Require Export GeoCoq.Highschool.circumcenter.

Section Orthocenter.

Context `{TE:Tarski_euclidean}.

(**
Orthocenter

#
<applet name="ggbApplet" code="geogebra.GeoGebraApplet" archive="geogebra.jar"
	codebase="http://jars.geogebra.org/webstart/4.2/unsigned/"
	width="1669" height="873">
	<param name="ggbBase64" value="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" />
	<param name="java_arguments" value="-Xmx1024m -Djnlp.packEnabled=true" />
	<param name="cache_archive" value="geogebra.jar, geogebra_main.jar, geogebra_gui.jar, geogebra_cas.jar, geogebra_algos.jar, geogebra_export.jar, geogebra_javascript.jar, jlatexmath.jar, jlm_greek.jar, jlm_cyrillic.jar, geogebra_properties.jar" />
	<param name="cache_version" value="4.2.47.0, 4.2.47.0, 4.2.47.0, 4.2.47.0, 4.2.47.0, 4.2.47.0, 4.2.47.0, 4.2.47.0, 4.2.47.0, 4.2.47.0, 4.2.47.0" />
	<param name="showResetIcon" value="false" />
	<param name="enableRightClick" value="true" />
	<param name="errorDialogsActive" value="true" />
	<param name="enableLabelDrags" value="false" />
	<param name="showMenuBar" value="true" />
	<param name="showToolBar" value="false" />
	<param name="showToolBarHelp" value="false" />
	<param name="showAlgebraInput" value="false" />
	<param name="useBrowserForJS" value="true" />
	<param name="allowRescaling" value="true" />
C'est une appliquette Java créée avec GeoGebra ( www.geogebra.org) - Il semble que Java ne soit pas installé sur votre ordinateur, merci d'aller sur www.java.com
</applet>
#

**)

(*
Definition is_orthocenter H A B C :=
 ~ Col A B C /\
 exists A1, exists B1, Perp A A1 B C /\ Perp B B1 A C /\ Col H A A1 /\ Col H B B1.
*)

Definition is_orthocenter H A B C :=
 ~ Col A B C /\ Perp A H B C /\ Perp B H A C /\ Perp C H A B.

Lemma construct_intersection : forall A B C X1 X2 X3,
 ~ Col A B C ->
 Par A C B X1 -> Par A B C X2 ->  Par B C A X3 ->
 exists E, Col E A X3 /\ Col E B X1.
Proof with finish.
intros A B C X1 X2 X3 HNC HPar1 HPar2 HPar3.
apply cop_npar__inter_exists.
  apply coplanar_perm_2, coplanar_trans_1 with C; Col; Cop.
intro HNPar; apply HNC.
assert (HFalsePar : Par B C A C)
  by (apply (par_trans B C B X1 A C); finish; apply (par_trans B C A X3 B); finish).
apply par_id_2...
Qed.

Lemma not_col_par_col2_diff : forall A B C D E F,
  ~ Col A B C -> Par A B C D -> Col C D E -> Col A E F -> A <> E.
Proof.
intros A B C D E F HNC HPar HC1 HC2.
intro; subst.
apply HNC; apply not_strict_par1 with D E; finish.
Qed.

Lemma construct_triangle : forall A B C,
  ~ Col A B C -> exists D, exists E, exists F,
  Col B D F /\ Col A E F /\ Col C D E /\
  Par A B C D /\ Par A C B D /\ Par B C A E /\
  Par A B C E /\ Par A C B F /\ Par B C A F /\
  D <> E /\ D <> F /\ E <> F.
Proof.
intros A B C HNC.
assert_diffs; rename H2 into HAB; rename H1 into HBC; rename H4 into HAC.

elim (parallel_existence1 A B C HAB);intros X1 HX1.
elim (parallel_existence1 A C B HAC);intros X2 HX2.
elim (parallel_existence1 B C A HBC);intros X3 HX3.

assert (T : exists D, Col D B X2 /\ Col D C X1) by (apply construct_intersection with A X3; finish); DecompExAnd T D.
assert (T : exists E, Col E A X3 /\ Col E C X1) by (apply construct_intersection with B X2; finish); DecompExAnd T E.
assert (T : exists F, Col F A X3 /\ Col F B X2) by (apply construct_intersection with C X1; finish); DecompExAnd T F.

assert (A <> E) by (apply not_col_par_col2_diff with B C X1 X3; finish).
assert (A <> F) by (apply not_col_par_col2_diff with C B X2 X3; finish).
assert (B <> D) by (apply not_col_par_col2_diff with A C X1 X2; finish).
assert (B <> F) by (apply not_col_par_col2_diff with C A X3 X2; finish).
assert (C <> D) by (apply not_col_par_col2_diff with A B X2 X1; finish).
assert (C <> E) by (apply not_col_par_col2_diff with B A X3 X1; finish).

assert (Par A B C D) by (apply par_col_par with X1; finish).
assert (Par A C B D) by (apply par_col_par with X2; finish).
assert (Par B C A E) by (apply par_col_par with X3; finish).
assert (Par A B C E) by (apply par_col_par with X1; finish).
assert (Par A C B F) by (apply par_col_par with X2; finish).
assert (Par B C A F) by (apply par_col_par with X3; finish).

assert (~ (D = E /\ D = F)).

  intro; spliter; treat_equalities.
  assert_paras_perm.
  assert_nparas_perm.
  permutation_intro_in_hyps.
  contradiction.

exists D; exists E; exists F.
assert_diffs.
(*
deduce_cols.
repeat split; try cols; finish; clear_cols; untag_hyps.
*)
repeat split; finish; try ColR.

intro; subst.
assert (E <> F) by (intro; subst; intuition).
apply HNC; apply col_permutation_1; apply not_strict_par1 with E A; sfinish.

intro; subst.
assert (E <> F) by (intro; subst; intuition).
apply HNC; apply col_permutation_2; apply not_strict_par1 with E C; sfinish.

intro; subst.
assert (D <> F) by (intro; subst; intuition).
apply HNC; apply not_strict_par1 with D B; sfinish.
Qed.

Lemma diff_not_col_col_par4_mid: forall A B C D E,
  D <> E -> ~ Col A B C -> Col C D E -> Par A B C D ->
  Par A B C E -> Par A E B C -> Par A C B D -> Midpoint C D E.
Proof.
intros A B C D E HD HNC HC HPar1 HPar2 HPar3 HPar4.
assert (HPara1 : Parallelogram_strict A B C E) by (apply parallel_2_plg; finish).
assert (HPara2 : Parallelogram_strict C A B D) by (apply parallel_2_plg; finish).
assert_congs_perm.
apply cong_col_mid; Col; eCong.
Qed.

Lemma altitude_is_perp_bisect : forall A B C O A1 E F,
  A <> O -> E <> F -> Perp A A1 B C -> Col O A1 A -> Col A E F -> Par B C A E -> Midpoint A E F ->
  Perp_bisect A O E F.
Proof with finish.
intros.
apply perp_mid_perp_bisect...
apply perp_sym.
apply cop_par_perp__perp with B C...
apply par_col_par with A...
apply perp_col1 with A1...
Qed.

Lemma altitude_intersect:
 forall A  A1 B B1 C C1 O: Tpoint,
 ~ Col A B C ->
 Perp A A1 B C  -> Perp B B1 A C -> Perp C C1 A B ->
 Col O A A1 -> Col O B B1 ->
 Col O C C1.
Proof with finish.
intros A A1 B B1 C C1 O HNC HPerp1 HPerp2 HPerp3 HC1 HC2.
assert (HT := HNC).
apply construct_triangle in HT.
destruct HT as [D [E [F HT]]].
spliter.

assert (Midpoint A E F) by (apply diff_not_col_col_par4_mid with B C; finish).
assert (Midpoint B D F) by (apply diff_not_col_col_par4_mid with A C; finish).
assert (Midpoint C D E) by (apply diff_not_col_col_par4_mid with A B; finish).

assert_diffs.
elim (eq_dec_points A O); intro.

  treat_equalities; apply col_permutation_4; apply cop_perp2__col with A B...
  apply perp_right_comm; apply perp_col1 with B1...

elim (eq_dec_points B O); intro.

  treat_equalities; apply col_permutation_4; apply cop_perp2__col with A B...
  apply perp_col1 with A1...

elim (eq_dec_points C O); intro.

  subst; Col.

assert (Perp_bisect A O E F) by (apply altitude_is_perp_bisect with B C A1; finish).
assert (Perp_bisect B O D F) by (apply altitude_is_perp_bisect with A C B1; finish).

assert (Perp O C D E).

  apply circumcenter_intersect with F A B; finish.
  apply perp_bisect_sym_1; assumption.
  apply perp_bisect_sym_1; assumption.

assert (Perp C1 C D E).

  apply perp_sym; apply cop_par_perp__perp with A B...
  apply par_symmetry; apply par_col_par_2 with C...

apply col_permutation_2; apply cop_perp2__col with D E; Perp.
apply coplanar_pseudo_trans with A B C.

  assumption.
  Cop.
  apply col_cop__cop with D; Col; Cop.
  Cop.
  apply coplanar_perm_2, col_cop__cop with B1; Col; Cop.

Qed.

Lemma is_orthocenter_cases :
  forall A B C G,
  is_orthocenter G A B C \/
  is_orthocenter G A C B \/
  is_orthocenter G B A C \/
  is_orthocenter G B C A \/
  is_orthocenter G C A B \/
  is_orthocenter G C B A ->
  is_orthocenter G A B C.
Proof.
intros.
decompose [or] H;clear H;
unfold is_orthocenter in *;spliter;
repeat (split; finish).
Qed.

Lemma is_orthocenter_perm : forall A B C G,
 is_orthocenter G A B C ->
 is_orthocenter G A B C /\ is_orthocenter G A C B /\
 is_orthocenter G B A C /\ is_orthocenter G B C A /\
 is_orthocenter G C A B /\ is_orthocenter G C B A.
Proof.
intros.
unfold is_orthocenter in *.
spliter.
repeat split;finish.
Qed.

Lemma is_orthocenter_perm_1 : forall A B C G,
 is_orthocenter G A B C -> is_orthocenter G A C B.
Proof.
intros.
apply is_orthocenter_perm in H;intuition.
Qed.

Lemma is_orthocenter_perm_2 : forall A B C G,
 is_orthocenter G A B C -> is_orthocenter G B A C.
Proof.
intros.
apply is_orthocenter_perm in H;intuition.
Qed.

Lemma is_orthocenter_perm_3 : forall A B C G,
 is_orthocenter G A B C -> is_orthocenter G B C A.
Proof.
intros.
apply is_orthocenter_perm in H;intuition.
Qed.

Lemma is_orthocenter_perm_4 : forall A B C G,
 is_orthocenter G A B C -> is_orthocenter G C A B.
Proof.
intros.
apply is_orthocenter_perm in H;intuition.
Qed.

Lemma is_orthocenter_perm_5 : forall A B C G,
 is_orthocenter G A B C -> is_orthocenter G C B A.
Proof.
intros.
apply is_orthocenter_perm in H;intuition.
Qed.

Lemma orthocenter_per :
 forall A B C H,
 Per A B C ->
 is_orthocenter H A B C ->
 H=B.
Proof.
intros.
unfold is_orthocenter in *;spliter.
assert_diffs.
assert (Perp A B B C) by (apply per_perp;finish).
assert (Par A H A B)
 by (apply l12_9 with B C;Cop).
assert (Col A B H)
 by (perm_apply (par_id A B H)).

assert (Par C H B C)
 by (apply l12_9 with A B;finish).
assert (Col B C H)
 by (perm_apply (par_id C B H)).
apply l6_21 with A B C B;finish.
Qed.

Lemma orthocenter_col :
 forall A B C H,
 Col H B C ->
 is_orthocenter H A B C ->
 H = B \/ H = C.
Proof.
intros.
unfold is_orthocenter in *.
spliter.
assert (Perp_at H B C A H).
apply l8_14_2_1b_bis;finish.
induction (eq_dec_points B H).
subst;auto.
assert (Perp A H B H)
 by (apply (perp_col1 A H B C H);finish).
assert (Par A H A C)
  by (apply l12_9 with B H;finish).
assert (Col H A C)
  by (perm_apply (par_id A C H)).
assert (H=C).
assert_diffs.
apply l6_21 with B C A C;finish.
subst.
auto.
Qed.

End Orthocenter.

Hint Resolve
     is_orthocenter_perm_1
     is_orthocenter_perm_2
     is_orthocenter_perm_3
     is_orthocenter_perm_4
     is_orthocenter_perm_5 : Orthocenter.