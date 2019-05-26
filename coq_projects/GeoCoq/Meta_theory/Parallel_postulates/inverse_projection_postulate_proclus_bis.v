Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch13_1.

Section inverse_projection_postulate_proclus_bis.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma inverse_projection_postulate__proclus_bis :
  inverse_projection_postulate -> alternative_proclus_postulate.
Proof.
  intros ip A B C D P Q HPerp2 HNC1 HCop1 HInter HNC2 HCop2.
  elim(col_dec C D P).
    intro; exists P; split; Col.
  intro HNCol1.
  assert(Par_strict C D A B).
  { apply (par_not_col_strict _ _ _ _ P); auto.
    apply par_symmetry.
    destruct HPerp2 as [X [Y [HCol1 [HPerp1 HPerp2]]]].
    assert (HI1 := HPerp1); assert (HI2 := HPerp2).
    destruct HI1 as [I1 H1]; destruct HI2 as [I2 H2].
    apply perp_in_col in H1; apply perp_in_col in H2.
    destruct H1 as [HCol2 HCol3]; destruct H2 as [HCol4 HCol5].
    assert (P = I1); [|treat_equalities; rename I2 into R].
      {
      elim (perp_not_col2 _ _ _ _ (perp_sym _ _ _ _ HPerp1)); intro;
      [apply l6_21 with A B X Y|apply l6_21 with A B Y X]; assert_diffs; Col.
      }
    elim (eq_dec_points P R); intro HNE; treat_equalities; [exfalso; Col|].
    apply (l12_9 _ _ _ _ X Y); Perp; apply coplanar_perm_16;
    apply col2_cop__cop with P R; try solve [assert_diffs; ColR];
    apply coplanar_perm_2;
    [apply col_cop__cop with D|apply col_cop__cop with C|
     apply col_cop__cop with D|apply col_cop__cop with C];
    Col; try solve [assert_diffs; auto]; apply coplanar_perm_16;
    [apply col_cop__cop with B|apply col_cop__cop with B|
     apply col_cop__cop with A|apply col_cop__cop with A];
    assert_diffs; Col; Cop.
  }
  destruct HPerp2 as [P1 [P2 [HP [HPerpAP HPerpCP]]]].
  assert(HC0 := HPerpCP); auto.
  destruct HC0 as [C0 [_ [_ [HC0P [HC0C _]]]]].
  assert(HP' := HPerpAP); auto.
  destruct HP' as [P' HPerpP].
  assert(P'=P) by (apply (l8_14_2_1b _ P1 P2 A B); Col).
  subst P'.
  destruct HPerpP as [_ [_ [HPP _]]].
  assert(P<>C0) by (intro; subst C0; Col).
  apply (perp_col0 _ _ _ _ P C0) in HPerpAP; Col.
  apply (perp_col0 _ _ _ _ P C0) in HPerpCP; Col.
  clear dependent P1.
  clear dependent P2.

  assert(P<>Q) by (intro; subst; auto).
  elim(col_dec P Q C0).
    intro; exists C0; Col.
  intro HNCol2.
  assert(HNCol3 : ~ Col C0 A B) by (apply (par_not_col C D); auto).
  assert(HQ0 := cop_not_par_same_side A B Q P P C0).
  destruct HQ0 as [Q0 []]; Col.
  assert (Coplanar C D P C0) by Cop.
  assert (Coplanar C D P A)
    by (apply col2_cop__cop with A B; assert_diffs; Col; Cop).
  assert (Coplanar C D P B)
    by (apply col2_cop__cop with A B; assert_diffs; Col; Cop).
  CopR.
  assert(HNCol4 : ~ Col A B Q0) by (apply (one_side_not_col123 _ _ _ C0); Side).
  assert(P<>Q0) by (intro; subst; auto).
  assert(HNCol5 : ~ Col P C0 Q0) by (intro; apply HNCol2; ColR).
  assert_diffs.
  assert(HC1 : exists C1, Col C D C1 /\ C1 <> C0).
  { elim(eq_dec_points C C0).
      intro; subst C0; exists D; split; Col.
      intro; exists C; split; Col.
  }
  destruct HC1 as [C1 []].
  assert (Coplanar C D P C0) by Cop.
  assert (Coplanar C D P A)
    by (apply col2_cop__cop with A B; assert_diffs; Col; Cop).
  assert (Coplanar C D P B)
    by (apply col2_cop__cop with A B; assert_diffs; Col; Cop).
  assert (Coplanar A B P C0) by Cop.
  assert(HA0 : exists A0, Col A B A0 /\ OS P C0 Q0 A0).
  { elim(col_dec P C0 A).
    - intro.
      assert(~ Col P C0 B) by (intro; apply HNCol3; ColR).
      assert (HA0 := cop_not_par_same_side P C0 B A P Q0).
      destruct HA0 as [A0 []]; Col.
      assert (Coplanar B P Q Q0) by Cop.
      assert (Coplanar B P Q C0) by CopR.
      assert (~ Col B P Q); [intro; apply HNC2; ColR|CopR].
      exists A0.
      split; Col.
    - intro.
      apply (cop_not_par_same_side _ _ _ _ P); Col.
      assert (Coplanar A P Q Q0) by Cop.
      assert (Coplanar A P Q C0) by CopR.
      assert (~ Col A P Q); [intro; apply HNC2; ColR|CopR].
  }
  destruct HA0 as [A0 []].
  assert(HNCol6 : ~ Col P C0 A0) by (apply (one_side_not_col123 _ _ _ Q0); Side).
  assert_diffs.

  assert(HY := ip C0 P Q0 C0 C1).
  destruct HY as [Y []]; auto.

    {
    exists C0, P, A0; split.
    assert(HPer := l8_16_1 A B C0 A0 P); destruct HPer; Col; Perp.
    split.

      {
      exists Q0; split; CongA.
      apply os2__inangle; Side.
      apply (col2_os__os A B); auto.
      }

      {
      intro.
      assert(Habs := conga_cop__or_out_ts C0 P Q0 A0).
      destruct Habs as [Habs|Habs]; auto.
      elim(col_dec P C0 A).

        {
        intro.
        assert(~ Col P C0 B) by (intro; apply HNCol3; ColR).
        assert (Coplanar B P Q Q0) by Cop.
        assert (Coplanar B P Q C0) by CopR.
        assert (Coplanar B P C0 Q0)
          by (assert (~ Col B P Q); [intro; apply HNC2; ColR|CopR]).
        apply coplanar_perm_2; apply col2_cop__cop with P B;
        assert_diffs; Cop; Col; ColR.
        }

        {
        intro.
        assert (Coplanar A P Q Q0) by Cop.
        assert (Coplanar A P Q C0) by CopR.
        assert (Coplanar A P C0 Q0)
          by (assert (~ Col A P Q); [intro; apply HNC2; ColR|CopR]).
        apply coplanar_perm_2; apply col2_cop__cop with P A;
        assert_diffs; Cop; Col; ColR.
        }

      apply HNCol4; ColR.
      apply l9_9 in Habs; apply Habs; Side.
      }
    }

    {
    apply out_trivial; auto.
    }

    {
    assert(HPer := l8_16_1 C D P C1 C0); destruct HPer; Col; Perp.
    }

    {
    assert (Coplanar C0 C1 P A0).
      {
      apply col2_cop__cop with A B; Col.
      apply coplanar_perm_16. apply col2_cop__cop with C D; Col.
      }
    assert (Coplanar P C0 Q0 A0) by Cop.
    CopR.
    }

    {
    exists Y; split; assert_diffs; ColR.
    }
Qed.

End inverse_projection_postulate_proclus_bis.