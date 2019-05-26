Require Export GeoCoq.Tarski_dev.Annexes.midpoint_theorems.
Require Export GeoCoq.Highschool.circumcenter.
Require Export GeoCoq.Highschool.orthocenter.
Require Export GeoCoq.Highschool.midpoint_thales.
Require Export GeoCoq.Highschool.concyclic.
Require Export GeoCoq.Highschool.gravityCenter.

Section Euler_line.

Context `{TE:Tarski_euclidean}.

(**
<applet name="ggbApplet" code="geogebra.GeoGebraApplet" archive="geogebra.jar"
        codebase="http://www.geogebra.org/webstart/4.0/unsigned/"
        width="796" height="466">
        <param name="ggbBase64" value="UEsDBBQACAAIALt4u0QAAAAAAAAAAAAAAAAWAAAAZ2VvZ2VicmFfamF2YXNjcmlwdC5qc0srzUsuyczPU0hPT/LP88zLLNHQVKiuBQBQSwcI1je9uRkAAAAXAAAAUEsDBBQACAAIALt4u0QAAAAAAAAAAAAAAAAMAAAAZ2VvZ2VicmEueG1s3VvbcptIGr7OPEWXLvYqQn0GsnKmnGRm4qpkPLXObm3tTQpBWyJGoAFkS6l5qX2Rfab9uxsQCEuxHNtRksRpoH/68H3/qbvx+OfVPEHXKi/iLD0ZEAcPkErDLIrT6clgWV4OvcHPL38aT1U2VZM8QJdZPg/KkwHXknF0MsBeNPGFr4ZcRRL+CydDf3JJhhPJsO9j5bJADBBaFfGLNPs9mKtiEYTqIpypefAuC4PSdDwry8WL0ejm5sapu3KyfDqaTifOqogGCIaZFieD6uIFNNd56YYZcYoxGf37/Tvb/DBOizJIQzVAegrL+OVPz8Y3cRplN+gmjsrZycDDMI2ZiqczmJPUNyMttABAFios42tVwKutWzPncr4YGLEg1fXP7BVKmukMUBRfx5HKAR+HCuYCBFkeq7SsBEjV0ahuYnwdqxvblr4y3fABKrMsmQS6GfTXX4hiitFzXRBbUCiktFXYPsPMFtQW3BbCynD7Orei3MpwK8PZAF3HRTxJ1MngMkgKgC1OL3OgrLkvynWizHiqB5spk+cwpyL+DMJM42hxhucYP9c/AO5zXgPcmiRp9VrmywM7rbsUHrt7l/RrumR1lxTf0iUVO2Yp94Brx3CXaRLRQha6Mv/MT69HRg/o0d5/XYeSP8kUx6PaUsaVcaBipmUrJks1L7S5MB8JX2s9QQJMQ7qg5AIRHwqXIjAGRATiAm6Jh6QuXcRcqOCIIQ9pOcKQsQ3hwX/cNY1JJKAx/dQFk0QEOuJIMESMSXEEhoSMWYKJUgYSQiABL+nuCdVNMIm4hDvmIQ5j1BbpEhBk8CLcQ/cUMYKYfpm4iEokdXuEa0uXnh46NEmRxEgS3SAYNRi0NWaQ9xDTs5EVXHG6WJYdiMJ5VF+W2aLhAqTBHW08nXVPHUf4bJwEE5VAbLjQTCJ0HSTaIkxHl1laoppEap9N82Axi8PiQpUlvFWgT8F18C4o1epXkC7qvo1smKXFH3lWvs6S5TwtEAqzBDdjzhLSuqbNqOGGtSp4u0K0KmTr2r213wxq0LJQ0H+WF7V4EEVnWmLjGgDJ8zRZv8pVcLXI4u40xiMTZsZqGSZxFAfpv0BZdS8aF1RHHeOt6qjDuVcPJMuji3UBGoxW/1F5Bj6GE4eL1l93gNa2imHpEG/zF8y9CANte1x034HYs95ZZXpW1w1BwUpt5jrNtWG3bs6KV1myeWSm/zpYlMvc5Aswq1xP6jSdJsqoiDFsCMbh1SRbXVjdYLatD+sF3GE7gsnUwI7ANVABA55W5cSWRkYPrZHCRgYbCVwrWxw19cSnRsKUE1saKdBeO7RqqqSeJsF1N3FhM5tBZTa1s9K6r2P7Mo3Ld/VNGYdXm6nqF35fzieq0aBum+Sh2hyPtlRsfKXyVCWVRgOZy2xZWANtKXukwngOt7aigiTQdP0TBmCfRmqaq3rgicnFLGCmFreVtffYNPVrns3P0usPoAtbAxiP6lGOizCPF1rn0ASiwJXaaFUUFwEEkaj9njZBmHqogwXAU2powDiX5SzLTboFPgVKbXmJmkOehUqjXkZDG5hPTdam8UTZ5BO4tSby2foNYVB9q6oZpQySxSzQmV016SRYq7wDg2nvfRZtgwPYmxmAjS8stwulrFrY8cLFApoz1tTxUYB2gVYwAAf0ea3zbx/i7WebstucVU9Vm1jHK9unWzyB8liUvoDXq+8fryFzhGcQw452BY+M2OvvHzHu6GR1rXFiD6NiYTafB2mEUpMK/pEl62mWDjbJSYC1aaKAaI1DAdUwWoyWZV2/gLeIlQmtTAAFhP6J7a3q4xZ6bG81AbadbiAoIUW5gmVYYZYGZRWXzMXbOIqUSU9H+4ltQdlmlghmuBWkilQbaskh1O7Wv0JN9V0zkPALGnj4QA/UwbYmwXq1/UcYvRoKx/WsYvmOi/2WDNuO0XenRv2Z2lcKGzjj+SKJw7hsNCnROn+WlhBGlYkj/eh4pdRCpyXn6Yc8SAu912FlWlH3jjQEx0PDEDu8ywPmhgjXca2BDz1HUs439eSH4WFyRDwwR3ZpqOyBOL609uCCBG3x8D3ZQ9fLv48jGxlvdfN9//7mS268HWXf3CvK6g2KqS0mtvh6ThmswQyJcPEYwfIdML8F4SsL4ZsehNF+CLUSNQhFfQS7K5IddtFddj2EUUBCazNa6bjWCoZEpyDS25hBb+n2MGZwsPZW0J/2oP/lEO395Wi0FyKD9A341PHZ06jvL7s8gDpAfdWxqC9xhF+txzxRaS+4AgKZ8xOrbOPJt/COLN6qh/dvh+jsb0ejs5Az+syVmPnVH2bwF8SRTFZxlAItRPAHVOTzvJxlsI4IkltUugpqQQ/iywNU+vJYVHpo08L1rsTR5u0E02/poPfyUbnpSY+P6QF8TI+FD5sdrnfkj5oN7DDqtdh4pOz9cN9zaYmY9oh4e4jveXs0vkdyhzPie7wB2uyTQNrOPMlb1mCcECyqPLdlPw/pj7TWv4o15Fm+BXrfDc0OUPvZsaj9HdwQdVzS3j14rOXSvWjoe5/4ABriY6Hhi95HONglLRKePBTscj4z63ziHg/nhzif86NxPq4jhU9JQ4J1Ppw7wsMbN1OtQh/V+byP87yn71USdN6D+/RvwSIr/n4I6PUr94H+wfbSW64IckspMfGES13OKOey3rjxIBxwxrkAXijB3iOsoV7HeZhspzjn9Xb5NtpX+3EOszQOGwSv7rc59kBO5l4uIp6q9Nr42wKhFa4+WVtj2z/6XD9ZERM4dB2pHn0mLWrmQZnHK3Ray5/WUqdUE6tDi8CccNcnVAq9X33Kqj5OuWmaSun74PuYpB5zjYQwOiEEh+SYui6HVMGvT/e3nZv+rCK+BDL2kr/3sKQ2E3Mc0lcFfdRBq1T4I6kOTcwFzCS4m1X2D0/o0x+emLJnzvwQbTtgw/gj+bot49tHe/+c03Hdto8hdTT2Oi7JBmPuEN/3hCRSr4yJFI+0DfEtDlSOjJchuAjRcf5us5tPmO8RTl0qpCuEqM9YsE+wzyXFwncfa4PoWzBzp2j9xOzsOHtsjh6H3/XZYzdImM+ttkNEExs2p+r9fev//Xd/ADCf8zQUgrR+H0a1rHCHYOdi15eMShcinS+9L7n6fUkbwf2c4q6n5F+x7AjysJWj1V9SJEl28w91maiVgfeuXNwesF9bHt7WodqE4FZi3IvbrPrUoY7bszpuTz7qkM4bq/tIDg/h7OlCOO4Y91N8/nDfMLF7pA8XIojcGyIIOC1CPb3BxJmPBfueXNJ+WmZHRAtzSDejaj5L8WhnlWdJkXopwDdx+8cJ3NqXHAspO7KpHZbyo+dSR2Qtw21zqZi53VqEwzyPNx6M+nuYYUfGzJ0+AXjbXXpvx+6zQ7a5zo5mbxE71O/tsBvzI6zz+DE+EriobOAgoD/tB3rbrj59052uDdDC8SlYiPR8zPQv4NF6Ne8TiplLuOCehESa1QccGDJr7rrg6KRHiHsXR0eOxJ5G7Y/2za/GVL/Z+fL/UEsHCHiX1BNKCgAAdjoAAFBLAQIUABQACAAIALt4u0TWN725GQAAABcAAAAWAAAAAAAAAAAAAAAAAAAAAABnZW9nZWJyYV9qYXZhc2NyaXB0LmpzUEsBAhQAFAAIAAgAu3i7RHiX1BNKCgAAdjoAAAwAAAAAAAAAAAAAAAAAXQAAAGdlb2dlYnJhLnhtbFBLBQYAAAAAAgACAH4AAADhCgAAAAA=" />
        <param name="image" value="http://www.geogebra.org/webstart/loading.gif" />
        <param name="boxborder" value="false" />
        <param name="centerimage" value="true" />
        <param name="java_arguments" value="-Xmx512m -Djnlp.packEnabled=true" />
        <param name="cache_archive" value="geogebra.jar, geogebra_main.jar, geogebra_gui.jar, geogebra_cas.jar, geogebra_algos.jar, geogebra_export.jar, geogebra_javascript.jar, jlatexmath.jar, jlm_greek.jar, jlm_cyrillic.jar, geogebra_properties.jar" />
        <param name="cache_version" value="4.0.19.0, 4.0.19.0, 4.0.19.0, 4.0.19.0, 4.0.19.0, 4.0.19.0, 4.0.19.0, 4.0.19.0, 4.0.19.0, 4.0.19.0, 4.0.19.0" />
        <param name="showResetIcon" value="false" />
        <param name="showAnimationButton" value="true" />
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
*)

Lemma concyclic_not_col_or_eq_aux :
  forall A B C D, Concyclic A B C D -> A = B \/ A = C \/ B = C \/ ~ Col A B C.
Proof.
intros A B C D HC.
elim (eq_dec_points A B); intro HAB; Col.
elim (eq_dec_points A C); intro HAC; Col.
elim (eq_dec_points B C); intro HBC; Col5.
right; right; right; intro HCol.
destruct HC as [HCop [O [HCong1 [HCong2 HCong3]]]].
assert (H := midpoint_existence A B); destruct H as [M1 HMid1].
assert (HOM1 : O <> M1).
  {
  intro; treat_equalities.
  assert (H := l7_20 O A C); elim H; clear H; try intro H; Cong;
  try (apply HBC; apply symmetric_point_uniqueness with A O; Col);
  assert_cols; ColR.
  }
assert (H := midpoint_existence A C); destruct H as [M2 HMid2].
assert (HOM2 : O <> M2).
  {
  intro; treat_equalities.
  assert (H := l7_20 O A B); elim H; clear H; try intro H; Cong;
  try (apply HBC; apply symmetric_point_uniqueness with A O; Col);
  assert_cols; ColR.
  }
assert (HM1M2 : M1 <> M2) by (intro; treat_equalities; Col).
assert (HPerp1 : Perp_bisect O M1 A B)
  by (apply cong_cop_perp_bisect; spliter; Cong; Cop).
assert (HPerp2 : Perp_bisect O M2 A C)
  by (apply cong_cop_perp_bisect; spliter; Cong; Cop).
assert (HOM1M2 : ~ Col O M1 M2).
  {
  intro HOM1M2; assert (H := l7_20 O A B); elim H; clear H; try intro H; Cong;
  try (apply HOM1; apply l7_17 with A B; Col); assert_diffs; assert_cols; ColR.
  }
assert (HPar_strict : Par_strict O M1 O M2).
  {
  apply par_not_col_strict with M2; Col.
  apply l12_9 with A B; [Cop| |Cop..| |].
    apply coplanar_perm_16, col_cop__cop with C; Col; Cop.
    apply perp_bisect_perp; Col.
  apply perp_col0 with A C; Col; perm_apply perp_bisect_perp.

  }
assert (H := not_par_strict_id O M1 M2); Col.
Qed.

Lemma concyclic_not_col_or_eq :
  forall A B C A', Concyclic A B C A' ->
  A'=C \/ A'=B \/ A=B \/ A=C \/ A=A' \/ (~ Col A B A' /\ ~ Col A C A').
Proof.
intros A B C A' H.
assert (H' := H); apply concyclic_perm_1 in H; apply concyclic_perm_3 in H'.
apply concyclic_not_col_or_eq_aux in H; apply concyclic_not_col_or_eq_aux in H'.
elim (eq_dec_points A' C); intro; try tauto.
elim (eq_dec_points A' B); intro; try tauto.
elim (eq_dec_points A B); intro; try tauto.
elim (eq_dec_points A C); intro; try tauto.
elim (eq_dec_points A A'); intro; try tauto.
do 3 (elim H; clear H; intro H; try tauto); Col.
do 3 (elim H'; clear H'; intro H'; try tauto); Col.
Qed.

Lemma Euler_line_special_case :
  forall A B C G H O,
  Per A B C ->
  is_gravity_center G A B C ->
  is_orthocenter H A B C ->
  is_circumcenter O A B C ->
  Col G H O.
Proof.
intros.
assert (H=B).
  apply orthocenter_per with A C;finish.
subst.
assert (Midpoint O A C).
 apply circumcenter_per with B;finish.
 unfold is_orthocenter in *;spliter;assert_diffs;finish.
 unfold is_orthocenter in *;spliter;assert_diffs;finish.
assert (is_gravity_center G A C B).
 apply is_gravity_center_perm in H1;intuition.
perm_apply (is_gravity_center_col A C B G O).
Qed.

Lemma gravity_center_change_triangle:
 forall A B C G I B' C',
 is_gravity_center G A B C ->
 Midpoint I B C ->
 Midpoint I B' C' ->
 ~ Col A B' C' ->
 is_gravity_center G A B' C'.
Proof.
intros.
Name G' the midpoint of A and G.
assert (Midpoint G I G')
  by (apply (is_gravity_center_third A B C G G' I);finish).
apply (is_gravity_center_third_reci A B' C' G I G');finish.
Qed.

(* Could be removed. See gravityCenter.v. *)
Hint Resolve
     is_gravity_center_perm_1
     is_gravity_center_perm_2
     is_gravity_center_perm_3
     is_gravity_center_perm_4
     is_gravity_center_perm_5 : gravitycenter.

Hint Resolve
     is_orthocenter_perm_1
     is_orthocenter_perm_2
     is_orthocenter_perm_3
     is_orthocenter_perm_4
     is_orthocenter_perm_5 : Orthocenter.

Hint Resolve
     is_circumcenter_perm_1
     is_circumcenter_perm_2
     is_circumcenter_perm_3
     is_circumcenter_perm_4
     is_circumcenter_perm_5 : Circumcenter.


Lemma Euler_line :
 forall A B C G H O,
  ~ Col A B C ->
  is_gravity_center G A B C ->
  is_orthocenter H A B C ->
  is_circumcenter O A B C ->
  Col G H O.
Proof.
intros.
elim (cong_dec A B A C); intro.

Name A' the midpoint of B and C.
Name B' the midpoint of A and C.
Name C' the midpoint of A and B.

assert (Perp_bisect A A' B C)
  by (apply cong_cop_perp_bisect; assert_diffs; Cong; Cop; intro; treat_equalities; apply H0; Col).

assert (Col G A' A)
  by (apply is_gravity_center_perm in H1; apply is_gravity_center_col with B C; spliter; Col).

unfold is_orthocenter in *; spliter.

elim (eq_dec_points O G); intro; treat_equalities; Col;
elim (eq_dec_points O H); intro; treat_equalities; Col.

elim (eq_dec_points O A'); intro; treat_equalities.

assert (Col A H O) by (apply cop_perp2__col with B C; Col; Cop; apply perp_bisect_perp; Col).
apply col_permutation_1; apply cop_perp2__col with B C.

apply coplanar_trans_1 with A; Cop.
apply perp_sym; apply perp_col0 with A O; try apply perp_bisect_perp; Col.
apply perp_sym; apply perp_col0 with A H; Col.

assert (Col A A' H) by (apply cop_perp2__col with B C; Cop; apply perp_bisect_perp; auto).
assert (Perp_bisect O A' B C) by (apply circumcenter_perp with A; assert_diffs; Col).
assert (Col A' A O)
  by (apply cop_perp2__col with B C; Cop; apply perp_left_comm; apply perp_bisect_perp; auto).
show_distinct A A'; assert_cols; Col; ColR.

Name A' the symmetric of A wrt O.

assert_diffs.

assert (Concyclic A B C A').
 unfold Concyclic.
 split.
 destruct (eq_dec_points A O).
  treat_equalities; Cop.
 apply coplanar_perm_12, col_cop__cop with O; Col; Cop.
 exists O.
 apply circumcenter_cong in H3.
 spliter.
 assert_congs_perm.
 spliter;repeat (split;finish).

assert (T:=concyclic_not_col_or_eq A B C A' H5).
decompose [or] T;clear T;try contradiction.
 - subst.
   assert (Per A B C).
    apply midpoint_thales with O;finish.
    unfold is_circumcenter in *;spliter;finish.
   apply (Euler_line_special_case A B C G H O);finish.
 - subst.
   assert (Per A C B).
    apply midpoint_thales with O;finish.
    unfold is_circumcenter in *;spliter.
    apply cong_transitivity with O B;finish.

   apply (Euler_line_special_case A C B G H O);finish.
(* For 8.5  bug *)
   try (apply is_gravity_center_perm_1; assumption). 
   auto with Orthocenter.
   auto with Circumcenter.

 - unfold is_circumcenter in *;spliter.
   treat_equalities.
   intuition.
 - spliter.

assert_diffs.

assert (Per A B A').
 apply midpoint_thales with O;finish.
 unfold is_circumcenter in *;spliter;finish.

assert (Perp C H A B)
 by (unfold is_orthocenter in *;spliter;finish).

assert (Perp A' B B A)
 by (apply per_perp;finish).

assert (Par C H A' B).
 unfold Concyclic in *; spliter.
 apply l12_9 with A B; [Cop|Cop| |Cop|Perp..].
 apply coplanar_trans_1 with C; Col; Cop.

assert (Perp B H A C)
 by (unfold is_orthocenter in *;spliter;finish).

assert (Per A C A').
 {
 apply midpoint_thales with O;finish.
 unfold is_circumcenter in *;spliter;finish.
 apply cong_transitivity with B O;finish.
 }

assert (Perp A' C C A) by (apply per_perp;finish).

assert (Par B H C A').
 unfold Concyclic in *; spliter.
 apply l12_9 with A C; [Cop..| |Perp|Perp].
 apply coplanar_trans_1 with B; Col; Cop.

induction (col_dec B H C).
 * assert (H=B \/ H=C) by (apply (orthocenter_col A B C H);finish).
   induction H26.
   + subst H.
     assert (Midpoint O A C) by (apply (circumcenter_per) with B;finish).
     assert (Col G O B).
        apply (is_gravity_center_col A C B G O).
        apply is_gravity_center_perm in H1;intuition idtac.
        assumption.
     Col.
   (*  perm_apply (is_gravity_center_col A C B G O). bug in 8.5 *) 
   + subst H;assert_diffs; intuition.
 * assert (Parallelogram B H C A')
     by (apply par_2_plg;finish).

   assert (T:exists I : Tpoint, Midpoint I B C /\ Midpoint I H A')
     by (apply plg_mid;finish).

   destruct T as [I [HI1 HI2]].

   elim (per_dec B A C); intro.

   apply Euler_line_special_case with B A C;
   try apply is_gravity_center_cases; auto;
   try apply is_orthocenter_cases; auto;
   try apply is_circumcenter_cases; auto.

   assert (is_gravity_center G A H A').
     {
     apply gravity_center_change_triangle with B C I;finish.
     show_distinct A' H; treat_equalities.
     apply plg_par in H26; spliter; assert_diffs; Col.
     apply H25; apply par_id_5; Par.
     intro.
     Name A'' the midpoint of B and C.
     show_distinct A'' O; treat_equalities.
     apply H27; apply perp_per_1; assert_diffs; Perp.
     assert (Perp_bisect O A'' B C) by (apply circumcenter_perp with A; Col).
     elim (eq_dec_points A A''); intro; treat_equalities.
     eauto using perp_bisect_cong_2 with cong.
     assert (Perp_bisect A'' A B C).
     apply perp_mid_perp_bisect; Col.
     apply perp_sym; apply perp_col0 with O A''; Col;
     try (apply perp_bisect_perp; assumption); assert_cols; try ColR.
     eauto using perp_bisect_cong_2 with cong.
     }

   assert (is_gravity_center G A A' H)
     by (apply is_gravity_center_cases;auto).

   perm_apply (is_gravity_center_col A A' H G O).
Qed.

End Euler_line.
