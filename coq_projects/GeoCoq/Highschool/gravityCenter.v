Require Export GeoCoq.Tarski_dev.Annexes.midpoint_theorems.
Require Export GeoCoq.Highschool.varignon.

Section GravityCenter.

Context `{TE:Tarski_euclidean}.

(**
Center of gravity

#
<applet name="ggbApplet" code="geogebra.GeoGebraApplet" archive="geogebra.jar"
	codebase="http://jars.geogebra.org/webstart/4.2/unsigned/"
	width="917" height="865">
	<param name="ggbBase64" value="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" />
	<param name="java_arguments" value="-Xmx1024m -Djnlp.packEnabled=true" />
	<param name="cache_archive" value="geogebra.jar, geogebra_main.jar, geogebra_gui.jar, geogebra_cas.jar, geogebra_algos.jar, geogebra_export.jar, geogebra_javascript.jar, jlatexmath.jar, jlm_greek.jar, jlm_cyrillic.jar, geogebra_properties.jar" />
	<param name="cache_version" value="4.2.47.0, 4.2.47.0, 4.2.47.0, 4.2.47.0, 4.2.47.0, 4.2.47.0, 4.2.47.0, 4.2.47.0, 4.2.47.0, 4.2.47.0, 4.2.47.0" />
	<param name="showResetIcon" value="false" />
	<param name="enableRightClick" value="false" />
	<param name="errorDialogsActive" value="true" />
	<param name="enableLabelDrags" value="false" />
	<param name="showMenuBar" value="false" />
	<param name="showToolBar" value="false" />
	<param name="showToolBarHelp" value="false" />
	<param name="showAlgebraInput" value="false" />
	<param name="useBrowserForJS" value="true" />
	<param name="allowRescaling" value="true" />
C'est une appliquette Java créée avec GeoGebra ( www.geogebra.org) - Il semble que Java ne soit pas installé sur votre ordinateur, merci d'aller sur www.java.com
</applet>
#

**)

Lemma intersection_two_medians_exist :
forall A B C I J,
 ~Col A B C ->
 Midpoint I B C -> Midpoint J A C ->
 exists G, Col G A I /\ Col G B J.
Proof with finish.
intros.
assert_bets.
elim (inner_pasch A B C J I)...
intro G;intros.
exists G.
spliter;assert_cols;split...
Qed.

Lemma intersection_two_medians_exist_unique :
forall A B C I J,
 ~Col A B C ->
 Midpoint I B C -> Midpoint J A C ->
 exists! G, Col G A I /\ Col G B J.
Proof with finish.
intros.
elim (intersection_two_medians_exist A B C I J H H0 H1); intros G HG; spliter.
exists G.
unfold unique.
assert_all.
repeat split...
intros G' HG'; spliter.
apply l6_21 with A I B J...
intro; search_contradiction.
show_distinct' B J...
Qed.

Definition is_gravity_center G A B C :=
 ~ Col A B C /\
 exists I, exists J, Midpoint I B C /\ Midpoint J A C /\ Col G A I /\ Col G B J.

Lemma is_gravity_center_coplanar : forall A B C G,
  is_gravity_center G A B C -> Coplanar G A B C.
Proof.
intros.
destruct H as [HNCol [I [J]]]; spliter.
exists I; left; split; Col.
Qed.

Lemma is_gravity_center_exist_unique : forall A B C,
  ~ Col A B C ->
  exists! G, is_gravity_center G A B C.
Proof with finish.
intros.
assert_diffs.
Name I the midpoint of B and C.
Name J the midpoint of A and C.
elim (intersection_two_medians_exist A B C I J H H1 H4); intros G HG; spliter.
exists G; unfold unique; unfold is_gravity_center; repeat split...
exists I;  exists J; do 3 (split; finish).
intros G' HG'; spliter; decompose [ex and] H8;clear H8.
assert_all.
apply l6_21 with A x B x0...
intro;search_contradiction.
show_distinct' B x0...
Qed.

Ltac intersection_medians G A B C I J H1 H2 H3 :=
 let T := fresh in assert(T:= intersection_two_medians_exist A B C I J H1 H2 H3);
 ex_and T G.

Tactic Notation "Name" ident(G) "the" "intersection" "of" "the" "medians" "(" ident(A) ident(I) ")" "which" "is" "a" "median" "since" ident(H2) "and" "(" ident(B) ident(J) ")" "which" "is" "a" "median" "since" ident(H3) "of" "the" "non-flat" "triangle" ident(A) ident(B) ident(C) ident(H1) :=
 intersection_medians G A B C I J H1 H2 H3.

Lemma three_medians_intersect:
 forall A B C I J K,
 ~Col A B C ->
 Midpoint I B C ->
 Midpoint J A C ->
 Midpoint K A B ->
 exists G, Col G A I /\ Col G B J /\Col G C K.
Proof with assert_all.
intros.
assert_diffs.
Name G the intersection of the medians (A I)
     which is a median since H0 and (B J)
     which is a median since H1
     of the non-flat triangle A B C H.
exists G; repeat split; try assumption.
Name D the symmetric of C wrt G.
assert_all.
show_distinct' A D.
permutation_intro_in_hyps.
assert (Par A D J G) by (apply (triangle_mid_par A D C G J H13 H14 H1)).
show_distinct' B G.
assert (Par G B A D)
     by (perm_apply (par_col_par A D G J B)).
show_distinct' B D.
assert (Par B D I G) by (apply (triangle_mid_par B D C G I H104 H14 H0)).
show_distinct' A G.
assert (Par G A D B)
     by (perm_apply (par_col_par B D G I A))...
show_distinct' D G.
assert (~ Col G A D)
     by (intro; search_contradiction).
assert (Parallelogram G A D B)
     by (apply (par_2_plg G A D B); finish).
Name Z the intersection of the diagonals (G D)
     and (A B) of the parallelogram H17...
ColR.
Qed.

Lemma is_gravity_center_col : forall A B C G I,
  is_gravity_center G A B C ->
  Midpoint I A B ->
  Col G I C.
Proof.
intros.
unfold is_gravity_center in *.
spliter.
destruct H1 as [J [K [Ha [Hb [Hc Hd]]]]].
elim (three_medians_intersect A B C J K I H);try assumption.
intro G';intros.
spliter.
assert (T:=is_gravity_center_exist_unique A B C H).
elim T.
intros G''.
intros.
unfold unique in *.
spliter.
assert (G''=G).
apply H5.
unfold is_gravity_center.
split;auto.
exists J. exists K;auto.
assert (G''=G').
apply H5.
unfold is_gravity_center.
split;auto.
exists J. exists K;auto.
subst.
subst.
Col.
Qed.

Lemma is_gravity_center_diff_1 :
 forall A B C G,
 is_gravity_center G A B C ->
 G<>A.
Proof.
intros.
intro.
unfold is_gravity_center in *.
spliter.
decompose [ex and] H1.
assert_cols.
apply H.
treat_equalities.
assert_diffs.
ColR.
Qed.

Lemma is_gravity_center_diff_2 :
 forall A B C G,
 is_gravity_center G A B C ->
 G<>B.
Proof.
intros.
intro.
unfold is_gravity_center in *.
spliter.
decompose [ex and] H1.
assert_cols.
apply H.
treat_equalities.
assert_diffs.
ColR.
Qed.

Lemma is_gravity_center_diff_3 :
 forall A B C G,
 is_gravity_center G A B C ->
 G<>C.
Proof.
intros.
intro.
unfold is_gravity_center in *.
spliter.
decompose [ex and] H1.
assert_cols.
apply H.
treat_equalities.
assert_diffs.
ColR.
Qed.
(* TODO put in assert_diffs ? *)

(** We don't have ratio so we express that AG=2/3 AA' using midpoints. *)

Lemma is_gravity_center_third :
 forall A B C G G' A',
 is_gravity_center G A B C ->
 Midpoint G' A G ->
 Midpoint A' B C ->
 Midpoint G A' G'.
Proof.
intros.
Name C' the midpoint of A and B.
assert (Col G C' C) by (apply is_gravity_center_col with A B; Col).
unfold is_gravity_center in *.
spliter.
destruct H4 as [A'' [B' HIJ]].
spliter.
treat_equalities.
assert_diffs.
Name G'' the midpoint of C and G.
assert (HPar : Parallelogram  C' A' G'' G').
apply (varignon' A B C G C' A' G'' G'); finish.
apply parallelogram_to_plg in HPar.
destruct HPar as [HDiff [I [HCol1 HCol2]]].
assert (G = I); try (treat_equalities; unfold Midpoint in *; spliter; eCong).
show_distinct G A; assert_diffs; try (apply H; assert_cols; ColR).
assert_diffs; assert_cols.
assert (~ Col A C G) by (intro; apply H; ColR).
elim HDiff; clear HDiff; intro; show_distinct A' G'; show_distinct C' G''; Col;
assert_diffs; assert_cols; try (apply H; ColR);
apply l6_21 with A G C G; assert_diffs; Col; ColR.
Qed.

Lemma is_gravity_center_third_reci :
 forall A B C G A' A'',
 Midpoint A' B C ->
 Midpoint A'' A G ->
 Midpoint G A' A'' ->
 ~ Col A B C ->
 is_gravity_center G A B C.
Proof.
intros A B C G A' A'' HMid1 HMid2 HMid3 HNC.
split; Col.
Name B' the midpoint of A and C.
Name C' the midpoint of A and B.
exists A'; exists B'; split; Col; try split; Col; split;
try (assert (A <> G) by (intro; treat_equalities; assert_cols; Col);
     assert_diffs; assert_cols; ColR).
Name B'' the midpoint of B and G.
assert (HB' := symmetric_point_construction B'' G).
destruct HB' as [B''' HB'].
assert (HPar1 : Par B A A' B').
  {
  apply triangle_mid_par with C; assert_diffs; try split;
  unfold Midpoint in *; spliter; Between; Cong.
  }
assert (HCong1 : Cong A C' A' B').
  {
  assert (H := triangle_mid_par_cong A B C A' B' C');
  destruct H as [Hc1 [Hc2 [Hc3 [H Hc4]]]]; assert_diffs; Cong.
  }
assert (HPar2 : Par A B A'' B'').
  {
  apply triangle_mid_par with G; assert_diffs; try split;
  unfold Midpoint in *; spliter; Between; Cong.
  }
assert (HCong2 : Cong A C' A'' B'').
  {
  assert (H := triangle_mid_par_cong A B G B'' A'' C');
  destruct H as [Hc1 [Hc2 [Hc3 [H Hc4]]]]; assert_diffs; Cong;
  intro; treat_equalities; assert_cols; Col.
  assert_diffs; apply HNC; ColR.
  }
assert (HPar3 : Par A'' B'' A' B''').
  {
  apply plg_par_1; try (intro; treat_equalities; Col; assert_diffs; assert_cols; apply HNC; ColR).
  apply mid_plg_1 with G; try (intro; treat_equalities; assert_cols; Col);
  unfold Midpoint in *; spliter; split; Between; Cong.
  }
assert (Cong3 : Cong A'' B'' A' B''').
  {
  apply plg_cong_1.
  apply mid_plg_1 with G; try (intro; treat_equalities; assert_cols; Col);
  unfold Midpoint in *; spliter; split; Between; Cong.
  }
assert (HCol : Col A' B' B''').
  {
  assert (H := parallel_uniqueness A B A' B' A' B''' A'); destruct H as [HCol1 HCol2]; Col; Par.
  apply par_trans with A'' B''; Par.
  }
assert (HElim := l7_20 A' B' B'''); elim HElim; clear HElim; try intro HElim; Col; eCong.

  {
  treat_equalities; assert_diffs; assert_cols.
  assert (G <> B'') by (intro; treat_equalities; Col); ColR.
  }

  {
  assert (HFalse : OS A' B'' A'' B''').
    {
    apply one_side_transitivity with G.

      {
      apply one_side_symmetry.
      assert (HH1 : A' <> B'') by (intro; treat_equalities; Col).
      assert (HH2 : Col A' B'' A') by Col.
      assert (HH3 : Col G A''  A') by (assert_cols; Col).
      assert (HH := l9_19 A' B'' G A'' A' HH2 HH3); rewrite HH.
      assert_diffs; assert_cols; show_distinct G A'; treat_equalities; Col.
      show_distinct G A''; treat_equalities; Col.
      show_distinct G B''; treat_equalities; Col.
      assert_diffs; assert_cols; assert (HABG : ~ Col A B G) by (intro; apply HNC; ColR).
      split; try (intro; apply HABG; ColR).
      split; Col.
      split; try (intro; treat_equalities; Col).
      unfold Midpoint in *; spliter; Between.
      }

      {
      assert (HH1 : A' <> B'') by (intro; treat_equalities; Col).
      assert (HH2 : Col A' B'' B'') by Col.
      assert (HH3 : Col G B'''  B'') by (assert_cols; Col).
      assert (HH := l9_19 A' B'' G B''' B'' HH2 HH3); rewrite HH.
      assert_diffs; assert_cols; show_distinct G A'; treat_equalities; Col.
      show_distinct G A''; treat_equalities; Col.
      show_distinct G B''; treat_equalities; Col.
      assert_diffs; assert_cols; assert (HABG : ~ Col A B G) by (intro; apply HNC; ColR).
      split; try (intro; apply HABG; ColR).
      split; Col.
      split; try (intro; treat_equalities; Col).
      unfold Midpoint in *; spliter; Between.
      }
    }
  apply l9_9_bis in HFalse; exfalso; apply HFalse; clear HFalse.
  apply l9_8_2 with B'.

    {
    assert (A' <> B'') by (intro; treat_equalities; Col).
    assert_diffs; assert_cols; show_distinct G A'; treat_equalities; Col.
    show_distinct G A''; treat_equalities; Col.
    show_distinct G B''; treat_equalities; Col.
    assert_diffs; assert_cols; assert (HABG : ~ Col A B G) by (intro; apply HNC; ColR).
    split; try (intro; apply HABG; ColR).
    split; try (intro; apply HABG; ColR).
    exists A'; unfold Midpoint in *; spliter; split; Col; Between.
    }

    {
    apply one_side_transitivity with A.

      {
      apply one_side_symmetry; apply l9_17 with C;
      try (unfold Midpoint in *; spliter; assumption).
      apply one_side_transitivity with G.

        {
        apply one_side_symmetry.
        assert_diffs; assert_cols; show_distinct G A'; treat_equalities; Col.
        show_distinct G A''; treat_equalities; Col.
        show_distinct G B''; treat_equalities; Col.
        assert (HH1 : A' <> B'') by (intro; treat_equalities; Col).
        assert (HH2 : Col A' B'' A') by Col.
        assert (HH3 : Col G A  A') by ColR.
        assert (HH := l9_19 A' B'' G A A' HH2 HH3); rewrite HH.
        assert_diffs; assert_cols; assert (HABG : ~ Col A B G) by (intro; apply HNC; ColR).
        split; try (intro; apply HABG; ColR).
        split; Col.
        split; try (intro; treat_equalities; Col).
        unfold Midpoint in *; spliter; eBetween.
        }

        {
        exists B; split.

          {
          assert (A' <> B'') by (intro; treat_equalities; Col).
          assert_diffs; assert_cols; show_distinct G A'; treat_equalities; Col.
          show_distinct G A''; treat_equalities; Col.
          show_distinct G B''; treat_equalities; Col.
          assert_diffs; assert_cols; assert (HABG : ~ Col A B G) by (intro; apply HNC; ColR).
          split; try (intro; apply HABG; ColR).
          split; try (intro; apply HABG; ColR).
          exists B''; unfold Midpoint in *; spliter; split; Col; Between.
          }

          {
          assert (A' <> B'') by (intro; treat_equalities; Col).
          assert_diffs; assert_cols; show_distinct G A'; treat_equalities; Col.
          show_distinct G A''; treat_equalities; Col.
          show_distinct G B''; treat_equalities; Col.
          assert_diffs; assert_cols; assert (HABG : ~ Col A B G) by (intro; apply HNC; ColR).
          split; try (intro; apply HABG; ColR).
          split; try (intro; apply HABG; ColR).
          exists A'; unfold Midpoint in *; spliter; split; Col; Between.
          }
        }
      }

      {
      assert_diffs; assert_cols; show_distinct G A'; treat_equalities; Col.
      show_distinct G A''; treat_equalities; Col.
      show_distinct G B''; treat_equalities; Col.
      assert (HH1 : A' <> B'') by (intro; treat_equalities; Col).
      assert (HH2 : Col A' B'' A') by Col.
      assert (HH3 : Col A A''  A') by ColR.
      assert (HH := l9_19 A' B'' A A'' A' HH2 HH3); rewrite HH.
      assert_diffs; assert_cols; assert (HABG : ~ Col A B G) by (intro; apply HNC; ColR).
      show_distinct A A'; Col.
      split; try (intro; apply HABG; ColR).
      split; Col.
      split; try (intro; treat_equalities; Col).
      unfold Midpoint in *; spliter; eBetween.
      }
    }
  }
Qed.

Lemma is_gravity_center_perm : forall A B C G,
 is_gravity_center G A B C ->
 is_gravity_center G A B C /\ is_gravity_center G A C B /\
 is_gravity_center G B A C /\ is_gravity_center G B C A /\
 is_gravity_center G C A B /\ is_gravity_center G C B A.
Proof.
intros.
Name I the midpoint of A and B.
assert (Col G I C)
 by (apply is_gravity_center_col with A B;finish).
unfold is_gravity_center in *.
spliter.
destruct H2 as [J [K [Ha [Hb [Hc Hd]]]]].
 repeat split;Col.
exists J; exists K;repeat (split;finish).
exists J; exists I;repeat (split;finish).
exists K; exists J;repeat (split;finish).
exists K; exists I;repeat (split;finish).
exists I; exists J;repeat (split;finish).
exists I; exists K;repeat (split;finish).
Qed.

Lemma is_gravity_center_perm_1 : forall A B C G,
 is_gravity_center G A B C -> is_gravity_center G A C B.
Proof.
intros.
apply is_gravity_center_perm in H;intuition.
Qed.

Lemma is_gravity_center_perm_2 : forall A B C G,
 is_gravity_center G A B C -> is_gravity_center G B A C.
Proof.
intros.
apply is_gravity_center_perm in H;intuition.
Qed.

Lemma is_gravity_center_perm_3 : forall A B C G,
 is_gravity_center G A B C -> is_gravity_center G B C A.
Proof.
intros.
apply is_gravity_center_perm in H;intuition.
Qed.

Lemma is_gravity_center_perm_4 : forall A B C G,
 is_gravity_center G A B C -> is_gravity_center G C A B.
Proof.
intros.
apply is_gravity_center_perm in H;intuition.
Qed.

Lemma is_gravity_center_perm_5 : forall A B C G,
 is_gravity_center G A B C -> is_gravity_center G C B A.
Proof.
intros.
apply is_gravity_center_perm in H;intuition.
Qed.

Lemma is_gravity_center_cases : forall A B C G,
  is_gravity_center G A B C \/
  is_gravity_center G A C B \/
  is_gravity_center G B A C \/
  is_gravity_center G B C A \/
  is_gravity_center G C A B \/
  is_gravity_center G C B A ->
  is_gravity_center G A B C.
Proof.
intros.
decompose [or] H;clear H.
apply is_gravity_center_perm in H0;intuition.
apply is_gravity_center_perm in H1;intuition.
apply is_gravity_center_perm in H0;intuition.
apply is_gravity_center_perm in H1;intuition.
apply is_gravity_center_perm in H0;intuition.
apply is_gravity_center_perm in H0;intuition.
Qed.

End GravityCenter.
(* If we prove it with "Context `{Tn:Tarski_neutral_dimensionless}." we do not get the warning
"the hint: eapply @is_gravity_center_perm_1 will only be used by eauto".
There must be a bug with the handling of bases of hints. *)
Hint Resolve is_gravity_center_coplanar : cop.

Hint Resolve
     is_gravity_center_perm_1
     is_gravity_center_perm_2
     is_gravity_center_perm_3
     is_gravity_center_perm_4
     is_gravity_center_perm_5 : gravitycenter.

Ltac permutation_intro_in_goal :=
 match goal with
 | |- Par ?A ?B ?C ?D => apply Par_cases
 | |- Par_strict ?A ?B ?C ?D => apply Par_strict_cases
 | |- Perp ?A ?B ?C ?D => apply Perp_cases
 | |- Perp_at ?X ?A ?B ?C ?D => apply Perp_in_cases
 | |- Per ?A ?B ?C => apply Per_cases
 | |- Midpoint ?A ?B ?C => apply Mid_cases
 | |- ~ Col ?A ?B ?C => apply NCol_cases
 | |- Col ?A ?B ?C => apply Col_cases
 | |- Bet ?A ?B ?C => apply Bet_cases
 | |- Cong ?A ?B ?C ?D => apply Cong_cases
 | |- is_gravity_center ?G ?A ?B ?C => apply is_gravity_center_cases
 end.

Ltac Gravitycenter := auto with gravitycenter.

(*
Ltac finish := repeat match goal with
 | |- Bet ?A ?B ?C => Between
 | |- Col ?A ?B ?C => Col
 | |- ~ Col ?A ?B ?C => Col
 | |- Par ?A ?B ?C ?D => Par
 | |- Par_strict ?A ?B ?C ?D => Par
 | |- Perp ?A ?B ?C ?D => Perp
 | |- Perp_at ?A ?B ?C ?D ?E => Perp
 | |- Per ?A ?B ?C => Perp
 | |- Cong ?A ?B ?C ?D => Cong
 | |- is_gravity_center ?G ?A ?B ?C => Gravitycenter
 | |- Midpoint ?A ?B ?C => Midpoint
 | |- ?A<>?B => apply swap_diff;assumption
 | |- _ => try assumption
end.
*)

Ltac sfinish := repeat match goal with
 | |- Bet ?A ?B ?C => Between; eBetween
 | |- Col ?A ?B ?C => Col;ColR
 | |- ~ Col ?A ?B ?C => Col
 | |- ~ Col ?A ?B ?C => intro;search_contradiction
 | |- Par ?A ?B ?C ?D => Par
 | |- Par_strict ?A ?B ?C ?D => Par
 | |- Perp ?A ?B ?C ?D => Perp
 | |- Perp_at ?A ?B ?C ?D ?E => Perp
 | |- Per ?A ?B ?C => Perp
 | |- Cong ?A ?B ?C ?D => Cong;eCong
 | |- is_gravity_center ?G ?A ?B ?C => Gravitycenter
 | |- Midpoint ?A ?B ?C => Midpoint
 | |- ?A<>?B => apply swap_diff;assumption
 | |- ?A<>?B => intro;treat_equalities; solve [search_contradiction]
 | |- ?G1 /\ ?G2 => split
 | |- _ => try assumption
end.

Ltac perm_apply t :=
 permutation_intro_in_goal;
 try_or ltac:(apply t;solve [finish]).
