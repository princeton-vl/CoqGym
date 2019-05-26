Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch13_1.

Section alternate_interior_angles_playfair_bis.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma alternate_interior__playfair_aux : alternate_interior_angles_postulate ->
   forall A1 A2 B1 B2 C1 C2 P,
   Perp2 A1 A2 B1 B2 P -> ~ Col A1 A2 P -> Col P B1 B2 -> Coplanar A1 A2 B1 B2 ->
   Par A1 A2 C1 C2 -> Col P C1 C2 ->
   Col C1 B1 B2. (** "half" of playfair_bis *)
Proof.
  intros aip A1 A2 B1 B2 C1 C2 P HPerp2 HNC1 HPB HCop HParAC HPC.
  elim(eq_dec_points P C1).
    intro; subst C1; auto.
  intro.
  assert(HParAB : Par A1 A2 B1 B2).
    {
    assert (Par_strict A1 A2 B1 B2); [|Par].
    apply (par_not_col_strict _ _ _ _ P); Col.
    apply par_symmetry.
    destruct HPerp2 as [X [Y [HCol1 [HPerp1 HPerp2]]]].
    assert (HI1 := HPerp1); assert (HI2 := HPerp2).
    destruct HI1 as [I1 H1]; destruct HI2 as [I2 H2].
    apply perp_in_col in H1; apply perp_in_col in H2.
    destruct H1 as [HCol2 HCol3]; destruct H2 as [HCol4 HCol5].
    assert (P = I2); [|treat_equalities; rename I1 into R].
      {
      elim (perp_not_col2 _ _ _ _ (perp_sym _ _ _ _ HPerp2)); intro;
      [apply l6_21 with B1 B2 X Y|apply l6_21 with B1 B2 Y X]; assert_diffs; Col.
      }
    elim (eq_dec_points P R); intro HNE; treat_equalities; [exfalso; Col|].
    apply (l12_9 _ _ _ _ X Y); Perp; apply coplanar_perm_16;
    apply col2_cop__cop with P R; try solve [assert_diffs; ColR];
    apply coplanar_perm_2;
    [apply col_cop__cop with A2|apply col_cop__cop with A1|
     apply col_cop__cop with A2|apply col_cop__cop with A1];
    Col; try solve [assert_diffs; auto]; apply coplanar_perm_16;
    [apply col_cop__cop with B2|apply col_cop__cop with B2|
     apply col_cop__cop with B1|apply col_cop__cop with B1];
    assert_diffs; Col; Cop.
    }
  elim(col_dec P A1 A2).
    { intro.
      assert_diffs.
      apply (not_strict_par _ _ _ _ P) in HParAB; Col.
      apply (not_strict_par _ _ _ _ P) in HParAC; Col.
      spliter.
      ColR.
    }
    intro HStrict.
    apply (par_not_col_strict _ _ _ _ P) in HParAB; Col.
    apply (par_not_col_strict _ _ _ _ P) in HParAC; Col.
    destruct HPerp2 as [P1 [P2 [HP [HPerpAP HPerpBP]]]].
    assert(HQ := HPerpAP); auto.
    destruct HQ as [Q [_ [_ [HQP[HQL _]]]]].
    assert(HP' := HPerpBP); auto.
    destruct HP' as [P' HPerpP].
    assert(P'=P) by (apply (l8_14_2_1b _ P1 P2 B1 B2); Col).
    subst P'.
    destruct HPerpP as [_ [_ [HPP _]]].
    assert(P<>Q) by (intro; subst Q; auto).
    apply (perp_col0 _ _ _ _ P Q) in HPerpAP; Col.
    apply (perp_col0 _ _ _ _ P Q) in HPerpBP; Col.
    clear dependent P1.
    clear dependent P2.

    assert(~ Col Q C1 P)
      by (apply (par_not_col A1 A2); auto;
          apply (par_strict_col_par_strict _ _ _ C2); Col).
    assert_diffs.
    assert(HB3 : exists B3, Col B1 B2 B3 /\ B3 <> P).
    { elim(eq_dec_points B1 P).
      intro; subst B1; exists B2; Col.
      intro; exists B1; Col.
    }
    destruct HB3 as [B3 []].
    assert(Col P C1 B3); [|ColR].
    assert_diffs.
    apply (cop_perp2__col _ _ _ P Q); auto; [| |apply (perp_col2 B1 B2); Col].
    assert (Coplanar A1 A2 P B3) by (apply col2_cop__cop with B1 B2; Col; Cop).
    assert (Coplanar A1 A2 C1 C2) by (apply pars__coplanar; auto).
    assert (Coplanar A1 A2 P C1) by (apply col2_cop__cop with C1 C2; Col; Cop).
    assert (Coplanar A1 A2 P Q) by (apply coplanar_perm_1, col__coplanar; Col).
    CopR.
    apply perp_left_comm.
    apply per_perp; auto.

    assert(HA3 : exists A3, Col A1 A2 A3 /\ TS P Q C1 A3).
    { elim(col_dec P Q A1);
      [|intro; apply (cop_not_par_other_side _ _ _ _ Q); Col].

      {
      intro.
      assert(HA3 := cop_not_par_other_side P Q A2 A1 Q C1).
      destruct HA3 as [A3 []]; Col; [intro; apply HStrict; ColR| |].
      assert (Coplanar A1 A2 C1 C2) by (apply pars__coplanar; auto).
      assert (Coplanar A1 A2 P C1) by (apply col2_cop__cop with C1 C2; Col; Cop).
      assert (Coplanar A1 A2 P Q) by (apply coplanar_perm_1, col__coplanar; Col).
      CopR.
      exists A3; split; Col.
      }

      {
      assert (Coplanar A1 A2 C1 C2) by (apply pars__coplanar; auto).
      assert (Coplanar A1 A2 P C1) by (apply col2_cop__cop with C1 C2; Col; Cop).
      assert (Coplanar A1 A2 P Q) by (apply coplanar_perm_1, col__coplanar; Col).
      CopR.
      }

    }
    destruct HA3 as [A3 [HA3 Hts]].
    assert(~ Col A3 P Q) by (destruct Hts as [_ []]; auto).
    assert_diffs.
    apply (l11_17 A3 Q P).
    apply perp_per_1; auto; apply (perp_col2 A1 A2); Col.
    apply conga_sym.
    apply aip; auto.
    apply (par_col4__par C1 C2 A1 A2); Col.
    apply par_strict_par; Par.
Qed.

Lemma alternate_interior__playfair_bis : alternate_interior_angles_postulate -> alternative_playfair_s_postulate.
Proof.
intros aia.
intros A1 A2 B1 B2 C1 C2 P HPerp2 HPB HCop HParAC HPC.
split.
apply (alternate_interior__playfair_aux aia A1 A2 _ _ _ C2 P); auto.
apply (alternate_interior__playfair_aux aia A1 A2 _ _ _ C1 P); Col; Par.
Qed.

End alternate_interior_angles_playfair_bis.