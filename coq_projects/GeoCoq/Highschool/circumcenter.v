Require Export GeoCoq.Highschool.midpoint_thales.
Require Export GeoCoq.Highschool.exercises.

Section Circumcenter.

Context `{TE:Tarski_euclidean}.

Definition is_circumcenter G A B C := Cong A G B G /\ Cong B G C G /\ Coplanar G A B C.

Lemma circumcenter_cong : forall G A B C,
 is_circumcenter G A B C ->
 Cong A G B G /\ Cong B G C G /\ Cong C G A G.
Proof.
intros.
unfold is_circumcenter in *.
intuition eCong.
Qed.

Lemma is_circumcenter_perm : forall A B C G,
 is_circumcenter G A B C ->
 is_circumcenter G A B C /\ is_circumcenter G A C B /\
 is_circumcenter G B A C /\ is_circumcenter G B C A /\
 is_circumcenter G C A B /\ is_circumcenter G C B A.
Proof.
unfold is_circumcenter.
intros.
spliter.
repeat split;eauto using cong_transitivity with cong;Cop.
Qed.

Lemma is_circumcenter_cases :
  forall A B C G,
  is_circumcenter G A B C \/
  is_circumcenter G A C B \/
  is_circumcenter G B A C \/
  is_circumcenter G B C A \/
  is_circumcenter G C A B \/
  is_circumcenter G C B A ->
  is_circumcenter G A B C.
Proof.
intros.
decompose [or] H;clear H; first [apply is_circumcenter_perm in H0|apply is_circumcenter_perm in H1];
spliter; assumption.
Qed.

Lemma is_circumcenter_perm_1 : forall A B C G,
 is_circumcenter G A B C -> is_circumcenter G A C B.
Proof.
intros.
apply is_circumcenter_perm in H;intuition.
Qed.

Lemma is_circumcenter_perm_2 : forall A B C G,
 is_circumcenter G A B C -> is_circumcenter G B A C.
Proof.
intros.
apply is_circumcenter_perm in H;intuition.
Qed.

Lemma is_circumcenter_perm_3 : forall A B C G,
 is_circumcenter G A B C -> is_circumcenter G B C A.
Proof.
intros.
apply is_circumcenter_perm in H;intuition.
Qed.

Lemma is_circumcenter_perm_4 : forall A B C G,
 is_circumcenter G A B C -> is_circumcenter G C A B.
Proof.
intros.
apply is_circumcenter_perm in H;intuition.
Qed.

Lemma is_circumcenter_perm_5 : forall A B C G,
 is_circumcenter G A B C -> is_circumcenter G C B A.
Proof.
intros.
apply is_circumcenter_perm in H;intuition.
Qed.

Lemma is_circumcenter_cop : forall A B C G,
 is_circumcenter G A B C -> Coplanar G A B C.
Proof.
unfold is_circumcenter.
intros; spliter; assumption.
Qed.

End Circumcenter.


(* TODO investigate bug Hint Resolve/Section *)
Hint Resolve
     is_circumcenter_perm_1
     is_circumcenter_perm_2
     is_circumcenter_perm_3
     is_circumcenter_perm_4
     is_circumcenter_perm_5 : Circumcenter.

Hint Resolve is_circumcenter_cop : cop.

Section Circumcenter2 .

Context `{TE:Tarski_euclidean}.

(**
#
<script type="text/javascript" language="javascript" src="
http://www.geogebra.org/web/4.2/web/web.nocache.js"></script><article class="geogebraweb" data-param-width="800" data-param-height="600" 
data-param-showResetIcon="false" data-param-enableLabelDrags="false" data-param-showMenuBar="false" data-param-showToolBar="false" data-param-showAlgebraInput="false" enableLabelDrags="true" data-param-ggbbase64="UEsDBBQACAAIAPNdNkIAAAAAAAAAAAAAAAAWAAAAZ2VvZ2VicmFfamF2YXNjcmlwdC5qc0srzUsuyczPU0hPT/LP88zLLNHQVKiuBQBQSwcI1je9uRkAAAAXAAAAUEsDBBQACAAIAPNdNkIAAAAAAAAAAAAAAAAMAAAAZ2VvZ2VicmEueG1s1Vrbcts4En3OfAWKD/tk0biDzMqZsl012Ux5LrXObm3tG0VCEmKK5JKULaXy8dsASIm2bMWyk9ijxIYANtDoc7obDSbjn1eLHF3rujFlcRKQEAdIF2mZmWJ2Eizb6SgKfn7303imy5me1AmalvUiaU8CHtJgOw96IVF2sslOAplolbKJHKlIRyMuSTyK40k8SnXMKNOJEngSILRqzNui/D1Z6KZKUn2ZzvUiuSjTpHVrztu2ent8fHNzE/baw7KeHc9mk3DVZAGCnRfNSdB9eQvL3Zp0w5w4xZgc/+e3C7/8yBRNmxSpDpC1amne/fRmfGOKrLxBNyZr5ydBhMGMuTazOZgpbefYClVga6XT1lzrBqYOus7mdlEFTiwp7PM3/hvKN+YEKDPXJtP1SYBDSRgRKoq5YjLilASorI0u2k6WdDqP+9XG10bf+GXtN6eR41gBBaYxk1yfBNMkb8AqU0xrQBQ2VC+h27TrXE+Suu9v90OO4A8ImM/argVmehhOAsGPGJVHCuMjITrzh3oD1JZl7hbFSMToyxdEMcXoyDbENxQaKf0j7Mcw8w31DfeN8DLcT+delHsZ7mU422Nm199rZ28lG1pJwDz7AwwfcbxrZjQwk1gbviBiN+8ahuy2idu+bXjXlb6rXEOwb0j3MLK/HFzyeQaxJxlEBkr9mg/r7AYGSnuVhHH5eJ30OTo3ZnJ5j0oqHjDzIHD3GCqGIQGhYP+6nx2VjD6LzydolPw5kf8EhQr/CIXj4z7PjbvYQ83cyna+0+pFY5MOi13eQQQJCEypIE0IRGJolA1QiohAXECXREjaViFmY5IjhiJk5QhDLruICH5xF68SCVjLDiofuIhxJBgiLidxBJkIubwGOY4ykBACCZhktROrlknEJXRYhDhs0GY0ZdMGg3nQB+UUMYKYnUsUohJJipTNioTbZCkju3dYlCKJkbRTIS1CSvTpEGZEiFlrwMOrsjEbcOc6r3qMHIymqJbtLejSRdZ/bctqQ6GTzsr06uwO1Dpp2sGScBJtzzt/Mt06Dt+M82SicygaLq0XIHSd5DaA3frTsmhR7wHUj83qpJqbtLnUbQuzGvQpuU4uklavfgHppt+gU+1O6bFeprnJTFL8G1zELmEXRP2h7dNSf2rHWHk1aVnW2eW6AcdBq//quoSUZKuUdfc9dr0mTaxbC+weDXtuEX292WWy0pu9oVltI2PQ+dCclfl2qCpN0Z4nVbusXTUF+ay2+zstZrl2ODn2oC5Jrybl6rLLr36tj+sKet0OJrPzMi9rBLFFhQCBrp341snYrW2ksJPBTgL3iJts85zE1Em4duJbJwUU+q11ppLeTIJ7NaZxGcHi5hymT6HWAWyZsyxMe9F3WpNebU21E35fLibgO51z3V6TfKs1x8d33GV8petC594nCiBzWS4b76UbT3szXjb6z6SdnxbZP/UMouvPxCa4Fpb2otstZzo1C5joxzvwEkvsv2CrfjTTs1r3JuaugPXQuqd46KE7w26pX+py8aG4/ghec2er4+PennGT1qay3okmkHGv9Nb/MtMkkK+z4TwwvgErUps7AMjWgnhu6nS5SKH81HWAkmU7L2tXr0I4gm0U/ZoUkJdrSIDgnTYUc70AadQ6H3VuvuHq1FXBlhRUTj5BgtgcB/75FkJ4fK+/Os9O8mqe2Eq5wyNP1rCBIUJuvT+m00a3aHUSjGIIXWjU4OlvZXYXVSDNmQ4ZofLuU2ntPc9bA18qUOYCduAZjqbGKhL24rO2Vx4Gh/Bnf2fyNwQLhI3iW9nPj94hGPzTY/gVNM9eCk3qjWTfG00adppISL8/nOcvBCd3JsI17zujGfdojlgovg2cablYJEWGClfpXeqZHQ+2RUaCbcyjhFhn9dAt2/5B4lfr1tghp+lW6+FPvkLPwOaH+MGPZmeHgC2MLMTxrY/0oNIwjhyoAC+JZHT3yGyhormCCzscRKLnDPsv/zBZpl211mOUWx4/2JzbaJeOd4+jK60rWwf8UXysk6Kxr15un0OHEnXmiTrfIWpyGFGTV0IUD1XkqHGvniwxBEIgJnAd7T/sL0fSuSfpdIek9DCS0ldC0kiFkWdpxENM8fAjHGsiCjmlrzmcbImU64fSHkrofUGV7ecLSjGTbtjIXpSte0Gn+0GHu5YurmGnJZTHaIW7t8dr7PWjz/3ICkAa+bsV6YY+k8HJBMdebVbotJc/7aVOqS0/QyXimMVCKRVTphSMs07FKYeVJRx1ShEWYcppRGyyPhVeo6SEMRIxrigVWMlu4/8rvK2Nv0TYe6yZmnS/C1wARGemcfbecYR0h3q9n3oL94ZZ/Uri9L7gXG/C1yZXKsKI0YGQeob33CHBLKrcpKZ9MgnJDgnTA0iYvhISfImxvr8G6Q44hfm+XPmjgZ/sAD87APjZKwF+5EqIdV9TANRchIKpQTzIHw365ji7g7j2B890B/j3+4G/fRl6/6TLEFS9FnnbTHxz+OXSl9M0fmRIMBEywSTvblEhZfDpwyLy1xyQiTlIfO+rzvuHrjrzw4qz+dPcnmL+bRw/02lZ++tmf7e8GxAkJEpFUkZECqoU3xZxjA7PW0+AgsRFKAUSlMJUSP70YHmhuvv9Q3W3OYxa8/qp5SG9RW337oyE7FYlxXwipBGcRSyOBOMRj6gUf1lud2v0T4dx++nVc8tCiYdVL+mSpoROJEmshCIRll01QRlU18QGN8QuFBxy33X5pal96DiceXJ365DTvyVV2fz9kEOxn/JSRyPx7+/o3tfYg5qd4DBWFMLSR3AEREPy3bz/6HIzCUHiWx6OX6lMdi9EZ4dTcfayVPAuJz6yfoQTL6REEdyV75BLMYnJpnpXnokopKKv3r8rE1PPxO6t6PxwJs5fOihIxwV9HBcyCu0rg8hTKEgooogS0XPh34tHIY8x296vnkfK8fAf1tw/Wnf/Ze3d/wFQSwcIn/9OBqgIAABiJwAAUEsBAhQAFAAIAAgA8102QtY3vbkZAAAAFwAAABYAAAAAAAAAAAAAAAAAAAAAAGdlb2dlYnJhX2phdmFzY3JpcHQuanNQSwECFAAUAAgACADzXTZCn/9OBqgIAABiJwAADAAAAAAAAAAAAAAAAABdAAAAZ2VvZ2VicmEueG1sUEsFBgAAAAACAAIAfgAAAD8JAAAAAA=="></article>
#
**)

Lemma circumcenter_perp : forall A B C A' G,
  A<>B -> B<>C -> A<>C -> G <> A' ->
  is_circumcenter G A B C ->
  Midpoint A' B C ->
  Perp_bisect G A' B C.
Proof.
intros.
apply cong_cop_perp_bisect; try assumption;
unfold Midpoint, is_circumcenter in *;
intuition eCong; Cop.
Qed.


Lemma exists_circumcenter : forall A B C,
  ~ Col A B C -> exists G, is_circumcenter G A B C.
Proof.
intros.
assert (triangle_circumscription_principle).
apply (inter_dec_plus_par_perp_perp_imply_triangle_circumscription).
unfold decidability_of_intersection; apply inter_dec.
unfold perpendicular_transversal_postulate.
intros; apply cop_par_perp__perp with A0 B0; auto.
unfold triangle_circumscription_principle in *.
destruct (H0 A B C H) as [G HG].
exists G.
unfold is_circumcenter.
spliter.
repeat split;eCong; Cop.
Qed.

Lemma circumcenter_perp_all : forall A B C A' B' C' G,
  A<>B -> B<>C -> A<>C -> G <> A' -> G <> B' -> G <> C' ->
  is_circumcenter G A B C ->
  Midpoint A' B C ->
  Midpoint B' A C ->
  Midpoint C' A B ->
  Perp_bisect G A' B C /\ Perp_bisect G B' A C /\ Perp_bisect G C' A B.
Proof.
intros.
split; try apply cong_cop_perp_bisect; try (split; try apply cong_cop_perp_bisect);
try assumption;
unfold is_circumcenter in *;
intuition eCong; Cop.
Qed.

Lemma circumcenter_intersect : forall A B C A' B' C' G,
  A<>B -> B<>C -> A<>C -> G <> A' -> G <> B' -> G <> C' ->
  Midpoint A' B C ->
  Midpoint B' A C ->
  Midpoint C' A B ->
  Perp_bisect G A' B C ->
  Perp_bisect G B' A C ->
  Perp G C' A B.
Proof.
intros.
assert (Cong B G C G).
 apply (perp_bisect_cong2 G A' B C ).
 assumption.
assert (Cong A G B G).
 assert (Cong A G C G).
  apply (perp_bisect_cong2 G B' A C).
  assumption.
 eCong.
apply perp_col1 with C'; Col.
apply perp_right_comm.
apply per_perp; auto.
 apply midpoint_distinct_1 with B; Midpoint.
exists B.
split; Cong.
Qed.

Lemma is_circumcenter_uniqueness :
   forall A B C O O',
  A<>B -> B<>C -> A<>C ->
  is_circumcenter O A B C ->
  is_circumcenter O' A B C ->
  O = O'.
Proof.
intros A B C O O' HAB HBC HAC HIC1 HIC2.
elim (col_dec A B C); intro HABC.

  {
  Name C' the midpoint of A and B.
  assert (HPer1 : Perp_bisect O C' A B).
    {
    apply cong_cop_perp_bisect; unfold is_circumcenter in *; spliter; Cong; Cop.
    intro; treat_equalities; assert (HFalse := l7_20 O B C); elim HFalse; clear HFalse;
    try intro HFalse; Cong; assert_cols; ColR.
    }
  Name A' the midpoint of B and C.
  assert (HPer2 : Perp_bisect O A' B C).
    {
    apply cong_cop_perp_bisect; unfold is_circumcenter in *; spliter; Cong; Cop.
    intro; treat_equalities; assert (HFalse := l7_20 O A B); elim HFalse; clear HFalse;
    try intro HFalse; Cong; assert_cols; ColR.

    }
  assert (HPar : Par_strict O A' O C').
    {
    apply par_not_col_strict with C'; Col.

      {
      apply l12_9 with A B; [Cop..| |Cop| |apply perp_bisect_perp; assumption].
        apply col__coplanar; ColR.
      apply perp_col0 with B C; Col; apply perp_sym; apply perp_bisect_perp; Col.
      }

      {
      show_distinct A' C'; try (apply HAC; apply symmetric_point_uniqueness with B A';
      unfold Midpoint in *; spliter; split; Cong; Between).
      intro; assert (HFalse := l7_20 O A B); elim HFalse; clear HFalse; try intro HFalse;
      unfold is_circumcenter in *; spliter; Cong; assert_diffs; assert_cols; try ColR.
      assert (HOC' : O <> C').
        {
        apply perp_bisect_equiv_def in HPer1.
        apply perp_bisect_equiv_def in HPer2.
        unfold Perp_bisect in *; unfold Perp_at in *;
        destruct HPer1 as [I [HOC' Hc1]]; assert_diffs; Col.
        }
      apply HOC'; apply l7_17 with A B; Col.
      }
    }
  assert (HFalse := not_par_strict_id O A' C'); exfalso; apply HFalse; Col.
  }

  {
  Name C' the midpoint of A and B.
  elim (eq_dec_points O C'); intro HOC'; elim (eq_dec_points O' C'); intro HO'C';
  treat_equalities; Col.

    {
    assert (HPer : Per A C B).
      {
      apply midpoint_thales with O; unfold is_circumcenter in *;
      spliter; Col; try split; eCong.
      }
    Name B' the midpoint of A and C.
    assert (HO'B' : O' <> B').
      {
      intro; treat_equalities.
      assert (HPer2 : Per A B C).
        {
        apply midpoint_thales with O'; unfold is_circumcenter in *;
        spliter; Col; try split; eCong.
        }
      assert (HPar : Par_strict A B A C).
        {
        apply par_not_col_strict with C; Col.
        apply l12_9 with B C; [Cop..| |apply perp_right_comm]; apply per_perp; Perp.
        }
      assert (HFalse := not_par_strict_id A B C); exfalso; apply HFalse; Col.
      }
    Name A' the midpoint of B and C.
    assert (HO'A' : O' <> A').
      {
      intro; treat_equalities.
      assert (HPer2 : Per B A C).
        {
        apply midpoint_thales with O'; unfold is_circumcenter in *;
        spliter; Col; try split; eCong.
        }
      assert (HPar : Par_strict B A B C).
        {
        apply par_not_col_strict with C; Col.
        apply l12_9 with A C; [Cop..| |apply perp_right_comm]; apply per_perp; Perp.
        }
      assert (HFalse := not_par_strict_id B A C); exfalso; apply HFalse; Col.
      }
    assert (H : Perp_bisect O' A' B C /\ Perp_bisect O' B' A C /\ Perp_bisect O' O A B).
      {
      apply circumcenter_perp_all; Col.
      }
    destruct H as [HPer3 [HPer4 Hc]]; clear Hc.
    assert (HPer1 : Perp_bisect O A' B C).
      {
      apply cong_cop_perp_bisect; unfold is_circumcenter in *; spliter; Cong; Cop.
      show_distinct O B; Col.
      intro; treat_equalities; apply HABC; assert_cols; ColR.
      }
    assert (HPer2 : Perp_bisect O B' A C).
      {
      apply cong_cop_perp_bisect; unfold is_circumcenter in *; spliter; eCong; Cop.
      show_distinct O A; Col.
      intro; treat_equalities; apply HABC; assert_cols; ColR.
      }
    apply l6_21 with O A' B' O'; Col.

      {
      assert (HRect : Rectangle C B' O A').
        {
        apply Per_mid_rectangle with B A; Perp; unfold Midpoint in *; spliter;
        split; Between; Cong.
        }
      destruct HRect as [HPara Hc]; clear Hc.
      apply plg_to_parallelogram in HPara.
      apply plg_permut in HPara.
      intro HOA'B'; apply plg_col_plgf in HPara; Col.
      destruct HPara as [Hc1 [HCol2 Hc2]]; clear Hc1; clear Hc2.
      assert_diffs; assert_cols; apply HABC; ColR.
      }

      {
      apply col_permutation_2; apply cop_perp2__col with B C;
        [|apply perp_bisect_perp;apply perp_bisect_sym_1; auto..].
      apply coplanar_trans_1 with A; Col; Cop.
      }

      {
      apply col_permutation_5; apply cop_perp2__col with A C;
        [|apply perp_bisect_perp;apply perp_bisect_sym_1; auto..].
      apply coplanar_trans_1 with B; Col; Cop.
      }
    }

    {
    assert (HPer : Per A C B).
      {
      apply midpoint_thales with O'; unfold is_circumcenter in *;
      spliter; Col; try split; eCong.
      }
    Name B' the midpoint of A and C.
    assert (HOB' : O <> B').
      {
      intro; treat_equalities.
      assert (HPer2 : Per A B C).
        {
        apply midpoint_thales with O; unfold is_circumcenter in *;
        spliter; Col; try split; eCong.
        }
      assert (HPar : Par_strict A B A C).
        {
        apply par_not_col_strict with C; Col.
        apply l12_9 with B C; [Cop..| |apply perp_right_comm]; apply per_perp; Perp.
        }
      assert (HFalse := not_par_strict_id A B C); exfalso; apply HFalse; Col.
      }
    Name A' the midpoint of B and C.
    assert (HOA' : O <> A').
      {
      intro; treat_equalities.
      assert (HPer2 : Per B A C).
        {
        apply midpoint_thales with O; unfold is_circumcenter in *;
        spliter; Col; try split; eCong.
        }
      assert (HPar : Par_strict B A B C).
        {
        apply par_not_col_strict with C; Col.
        apply l12_9 with A C; [Cop..| |apply perp_right_comm]; apply per_perp; Perp.
        }
      assert (HFalse := not_par_strict_id B A C); exfalso; apply HFalse; Col.
      }
    assert (H : Perp_bisect O A' B C /\ Perp_bisect O B' A C /\ Perp_bisect O O' A B).
      {
      apply circumcenter_perp_all; Col.
      }
    destruct H as [HPer3 [HPer4 Hc]]; clear Hc.
    assert (HPer1 : Perp_bisect O' A' B C).
      {
      apply cong_cop_perp_bisect; unfold is_circumcenter in *; spliter; Cong; Cop.
      show_distinct O' B; Col.
      intro; treat_equalities; apply HABC; assert_cols; ColR.
      }
    assert (HPer2 : Perp_bisect O' B' A C).
      {
      apply cong_cop_perp_bisect; unfold is_circumcenter in *; spliter; eCong; Cop.
      show_distinct O' A; Col.
      intro; treat_equalities; apply HABC; assert_cols; ColR.
      }
    apply l6_21 with O' A' B' O; Col.

      {
      assert (HRect : Rectangle C B' O' A').
        {
        apply Per_mid_rectangle with B A; Perp; split; Between; Cong.
        }
      destruct HRect as [HPara Hc]; clear Hc.
      apply plg_to_parallelogram in HPara.
      apply plg_permut in HPara.
      intro HO'A'B'; apply plg_col_plgf in HPara; Col.
      destruct HPara as [Hc1 [HCol2 Hc2]]; clear Hc1; clear Hc2.
      assert_diffs; assert_cols; apply HABC; ColR.
      }

      {
      apply col_permutation_2; apply cop_perp2__col with B C;
        [|apply perp_bisect_perp, perp_bisect_sym_1; auto..].
      apply coplanar_trans_1 with A; Cop.
      }

      {
      apply col_permutation_5; apply cop_perp2__col with A C;
        [|apply perp_bisect_perp, perp_bisect_sym_1; auto..].
      apply coplanar_trans_1 with B; Col; Cop.
      }
    }

    {
    Name B' the midpoint of A and C.
    elim (eq_dec_points O B'); intro HOB'; elim (eq_dec_points O' B'); intro HO'B';
    treat_equalities; Col.

      {
      assert (HPer : Per A B C).
        {
        apply midpoint_thales with O; unfold is_circumcenter in *;
        spliter; Col; try split; eCong.
        }
      Name A' the midpoint of B and C.
      assert (HO'A' : O' <> A').
        {
        intro; treat_equalities.
        assert (HPer2 : Per B A C).
          {
          apply midpoint_thales with O'; unfold is_circumcenter in *;
          spliter; Col; try split; eCong.
          }
        assert (HPar : Par_strict A C B C).
          {
          apply par_not_col_strict with B; Col.
          apply l12_9 with A B; [Cop..|apply perp_left_comm|apply perp_comm]; apply per_perp; Perp.
          }
        assert (HFalse := not_par_strict_id C A B); exfalso; apply HFalse; Par.
        }
      assert (H : Perp_bisect O' A' B C /\ Perp_bisect O' O A C /\ Perp_bisect O' C' A B).
        {
        apply circumcenter_perp_all; Col.
        }
      destruct H as [HPer3 [Hc HPer4]]; clear Hc.
      assert (HPer1 : Perp_bisect O A' B C).
        {
        apply cong_cop_perp_bisect; unfold is_circumcenter in *; spliter; Cong; Cop.
        show_distinct O C; Col.
        intro; treat_equalities; apply HABC; assert_cols; ColR.
        }
      assert (HPer2 : Perp_bisect O C' A B).
        {
        apply cong_cop_perp_bisect; unfold is_circumcenter in *; spliter; eCong; Cop.
        }
      apply l6_21 with O A' C' O'; Col.

        {
        assert (HRect : Rectangle B A' O C').
          {
          apply Per_mid_rectangle with A C; Perp; split; Between; Cong.
          }
        destruct HRect as [HPara Hc]; clear Hc.
        apply plg_to_parallelogram in HPara.
        apply plg_permut in HPara.
        intro HOA'C'; apply plg_col_plgf in HPara; Col.
        destruct HPara as [Hc1 [HCol2 Hc2]]; clear Hc1; clear Hc2.
        assert_diffs; assert_cols; apply HABC; ColR.
        }

        {
        apply col_permutation_2; apply cop_perp2__col with B C;
          [|apply perp_bisect_perp, perp_bisect_sym_1; auto..].
        apply coplanar_trans_1 with A; Cop.
        }

        {
        apply col_permutation_5; apply cop_perp2__col with A B;
          [|apply perp_bisect_perp, perp_bisect_sym_1; auto..].
        apply coplanar_trans_1 with C; Col; Cop.
        }
      }

      {
      assert (HPer : Per A B C).
        {
        apply midpoint_thales with O'; unfold is_circumcenter in *;
        spliter; Col; try split; eCong.
        }
      Name A' the midpoint of B and C.
      assert (HOA' : O <> A').
        {
        intro; treat_equalities.
        assert (HPer2 : Per B A C).
          {
          apply midpoint_thales with O; unfold is_circumcenter in *;
          spliter; Col; try split; eCong.
          }
        assert (HPar : Par_strict A C B C).
          {
          apply par_not_col_strict with B; Col.
          apply l12_9 with A B; [Cop..|apply perp_left_comm|apply perp_comm]; apply per_perp; Perp.
          }
        assert (HFalse := not_par_strict_id C A B); exfalso; apply HFalse; Par.
        }
      assert (H : Perp_bisect O A' B C /\ Perp_bisect O O' A C /\ Perp_bisect O C' A B).
        {
        apply circumcenter_perp_all; Col.
        }
      destruct H as [HPer3 [Hc HPer4]]; clear Hc.
      assert (HPer1 : Perp_bisect O' A' B C).
        {
        apply cong_cop_perp_bisect; unfold is_circumcenter in *; spliter; Cong; Cop.
        show_distinct O' C; Col.
        intro; treat_equalities; apply HABC; assert_cols; ColR.
        }
      assert (HPer2 : Perp_bisect O' C' A B).
        {
        apply cong_cop_perp_bisect; unfold is_circumcenter in *; spliter; eCong; Cop.
        }
      apply l6_21 with O' A' C' O; Col.

        {
        assert (HRect : Rectangle B A' O' C').
          {
          apply Per_mid_rectangle with A C; Perp; split; Between; Cong.
          }
        destruct HRect as [HPara Hc]; clear Hc.
        apply plg_to_parallelogram in HPara.
        apply plg_permut in HPara.
        intro HO'A'C'; apply plg_col_plgf in HPara; Col.
        destruct HPara as [Hc1 [HCol2 Hc2]]; clear Hc1; clear Hc2.
        assert_diffs; assert_cols; apply HABC; ColR.
        }

        {
        apply col_permutation_2; apply cop_perp2__col with B C;
          [|apply perp_bisect_perp, perp_bisect_sym_1; auto..].
        apply coplanar_trans_1 with A; Cop.
        }

        {
        apply col_permutation_5; apply cop_perp2__col with A B;
          [|apply perp_bisect_perp, perp_bisect_sym_1; auto..].
        apply coplanar_trans_1 with C; Col; Cop.
        }
      }

      {
      Name A' the midpoint of B and C.
      elim (eq_dec_points O A'); intro HOA'; elim (eq_dec_points O' A'); intro HO'A';
      treat_equalities; Col.

        {
        assert (HPer : Per C A B).
          {
          apply midpoint_thales with O; unfold is_circumcenter in *;
          spliter; Col; try split; eCong; Between.
          }
        assert (H : Perp_bisect O' O B C /\ Perp_bisect O' B' A C /\ Perp_bisect O' C' A B).
          {
          apply circumcenter_perp_all; Col.
          }
        destruct H as [Hc [HPer3 HPer4]]; clear Hc.
        assert (HPer1 : Perp_bisect O B' A C).
          {
          apply cong_cop_perp_bisect; unfold is_circumcenter in *; spliter; eCong; Cop.
          }
        assert (HPer2 : Perp_bisect O C' A B).
          {
          apply cong_cop_perp_bisect; unfold is_circumcenter in *; spliter; eCong; Cop.
          }
        apply l6_21 with O B' C' O'; Col.

          {
          assert (HRect : Rectangle A B' O C').
            {
            apply Per_mid_rectangle with B C; Perp; split; Between; Cong.
            }
          destruct HRect as [HPara Hc]; clear Hc.
          apply plg_to_parallelogram in HPara.
          apply plg_permut in HPara.
          intro HOB'C'; apply plg_col_plgf in HPara; Col.
          destruct HPara as [Hc1 [HCol2 Hc2]]; clear Hc1; clear Hc2.
          assert_diffs; assert_cols; apply HABC; ColR.
          }

          {
          apply col_permutation_2; apply cop_perp2__col with A C;
            [|apply perp_bisect_perp, perp_bisect_sym_1; auto..].
          apply coplanar_trans_1 with B; Col; Cop.
          }

          {
          apply col_permutation_5; apply cop_perp2__col with A B;
            [|apply perp_bisect_perp, perp_bisect_sym_1; auto..].
          apply coplanar_trans_1 with C; Col; Cop.
          }
        }

        {
        assert (HPer : Per C A B).
          {
          apply midpoint_thales with O'; unfold is_circumcenter in *;
          spliter; Col; try split; eCong; Between.
          }
        assert (H : Perp_bisect O O' B C /\ Perp_bisect O B' A C /\ Perp_bisect O C' A B).
          {
          apply circumcenter_perp_all; Col.
          }
        destruct H as [Hc [HPer3 HPer4]]; clear Hc.
        assert (HPer1 : Perp_bisect O' B' A C).
          {
          apply cong_cop_perp_bisect; unfold is_circumcenter in *; spliter; eCong; Cop.
          }
        assert (HPer2 : Perp_bisect O' C' A B).
          {
          apply cong_cop_perp_bisect; unfold is_circumcenter in *; spliter; eCong; Cop.
          }
        apply l6_21 with O' B' C' O; Col.

          {
          assert (HRect : Rectangle A B' O' C').
            {
            apply Per_mid_rectangle with B C; Perp; split; Between; Cong.
            }
          destruct HRect as [HPara Hc]; clear Hc.
          apply plg_to_parallelogram in HPara.
          apply plg_permut in HPara.
          intro HO'B'C'; apply plg_col_plgf in HPara; Col.
          destruct HPara as [Hc1 [HCol2 Hc2]]; clear Hc1; clear Hc2.
          assert_diffs; assert_cols; apply HABC; ColR.
          }

          {
          apply col_permutation_2; apply cop_perp2__col with A C;
            [|apply perp_bisect_perp, perp_bisect_sym_1; auto..].
          apply coplanar_trans_1 with B; Col; Cop.
          }

          {
          apply col_permutation_5; apply cop_perp2__col with A B;
            [|apply perp_bisect_perp, perp_bisect_sym_1; auto..].
          apply coplanar_trans_1 with C; Col; Cop.
          }
        }

        {
        assert (H : Perp_bisect O A' B C /\ Perp_bisect O B' A C /\ Perp_bisect O C' A B).
          {
          apply circumcenter_perp_all; Col.
          }
        destruct H as [HPer1 [HPer2 Hc]]; clear Hc.
        assert (H : Perp_bisect O' A' B C /\ Perp_bisect O' B' A C /\ Perp_bisect O' C' A B).
          {
          apply circumcenter_perp_all; Col.
          }
        destruct H as [HPer3 [HPer4 Hc]]; clear Hc.
        apply l6_21 with O A' B' O; Col.

          {
          intro HOA'B'; assert (HPar : Par_strict A C C B).
            {
            apply par_not_col_strict with B; Col.
            apply l12_9 with O A'; [| |Cop..| |].
              apply coplanar_perm_4, col_cop__cop with B; Col; Cop.
              apply coplanar_perm_4, col_cop__cop with C; Col; Cop.
              apply perp_col0 with O B'; Col; apply perp_bisect_perp; assumption.
            apply perp_sym; apply perp_right_comm; apply perp_bisect_perp; Col.
            }
          assert (HFalse := not_par_strict_id C A B); apply HFalse; Par.
          }

          {
          apply col_permutation_2; apply cop_perp2__col with B C;
            [|apply perp_bisect_perp, perp_bisect_sym_1; auto..].
          apply coplanar_trans_1 with A; Cop.
          }

          {
          apply col_permutation_5; apply cop_perp2__col with A C;
            [|apply perp_bisect_perp, perp_bisect_sym_1; auto..].
          apply coplanar_trans_1 with B; Col; Cop.
          }
        }
      }
    }
  }
Qed.


End Circumcenter2.

Section Circumcenter3.

Context `{TE:Tarski_euclidean}.

Lemma midpoint_thales_reci_circum :
  forall A B C O: Tpoint,
   Per A C B ->
   Midpoint O A B ->
   is_circumcenter O A B C.
Proof.
intros.
assert (T:= midpoint_thales_reci A B C O H H0).
spliter.
split;finish.
Qed.

Lemma circumcenter_per :
 forall A B C O,
 A<>B -> B<>C ->
 Per A B C ->
 is_circumcenter O A B C ->
 Midpoint O A C.
Proof.
intros.

Name O' the midpoint of A and C.
assert (T:= midpoint_thales_reci_circum A C B O' H1 H4).
assert (O=O').
apply is_circumcenter_uniqueness with A B C;finish.
intro.
treat_equalities.
apply l8_8 in H1.
intuition.
auto using is_circumcenter_perm_1.
subst;auto.
Qed.

End Circumcenter3.