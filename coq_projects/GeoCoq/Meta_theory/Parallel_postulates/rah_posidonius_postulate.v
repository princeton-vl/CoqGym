Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section rah_posidonius.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma rah__posidonius_aux : postulate_of_right_saccheri_quadrilaterals ->
  forall A1 A2 A3 B1 B2 B3,
  Per A2 A1 B1 -> Per A1 A2 B2 -> Cong A1 B1 A2 B2 -> OS A1 A2 B1 B2 ->
  Col A1 A2 A3 -> Col B1 B2 B3 -> Perp A1 A2 A3 B3 ->
  Cong A3 B3 A1 B1.
Proof.
  intros rah A1 A2 A3 B1 B2 B3 HPer1 HPer2 HCong HOS HA HB HPerp.
  assert (HSac : Saccheri A1 B1 B2 A2) by repeat (split; finish).
  assert(Hdiff := sac_distincts A1 B1 B2 A2 HSac).
  spliter.
  assert_diffs.
  elim(eq_dec_points A1 A3).
  { intro.
    subst A3.
    assert(B1 = B3); [|subst; Cong].
    apply (l6_21 B1 B2 A1 B1); Col.
      apply not_col_permutation_1; apply (sac__ncol123 _ _ _ A2); assumption.
      unfold Saccheri in HSac; spliter; apply (cop_perp2__col _ _ _ A1 A2); Perp.
      apply col_cop__cop with B2; Cop.
  }
  intro.
  destruct(segment_construction_3 A3 B3 A1 B1) as [B'3 []]; auto.
  assert_diffs.
  assert(B3 = B'3); [|subst; assumption].
  assert(Par_strict B1 B2 A1 A3).
  { apply (par_strict_col_par_strict _ _ _ A2); auto.
    apply par_strict_symmetry.
    apply sac__par_strict1423; assumption.
  }
  apply (l6_21 B1 B2 A3 B3); Col.
    apply (par_strict_not_col_4 _ _ A1); auto.
  apply col_permutation_2.
  assert (Coplanar A1 B2 B'3 B1).
  { apply coplanar_perm_15, coplanar_trans_1 with A3.
      apply not_col_permutation_2, par_strict_not_col_4 with A1; assumption.
      apply coplanar_perm_18, pars__coplanar; assumption.
    exists B3; right; right; split; Col.
  }
  apply cop_per2__col with A1; auto; apply l8_2.
    apply (rah _ _ _ A2); auto.
  apply (rah _ _ _ A3).
  unfold Saccheri in *.
  spliter.
  assert(B1 <> B3).
  { intro.
    subst B3.
    assert(A1 = A3); auto.
    apply (l8_18_uniqueness A1 A2 B1); Col; Perp.
    apply not_col_permutation_1; apply per_not_col; auto.
  }
  assert(Per A1 A3 B'3).
  { apply perp_per_1; auto.
    apply perp_comm; apply (perp_col _ A2); Col.
    apply (perp_col1 _ _ _ B3); Col.
  }
  repeat split; Cong.
    apply (per_col _ _ A2); auto.
  apply (one_side_transitivity _ _ _ B3).
    apply l12_6; auto; apply (par_strict_col_par_strict _ _ _ B2); Col; Par.
    apply invert_one_side; apply out_one_side; auto; right; apply not_col_permutation_4; apply per_not_col; auto.
Qed.

Lemma rah__posidonius :
  postulate_of_right_saccheri_quadrilaterals -> posidonius_postulate.
Proof.
intro HP.
destruct ex_saccheri as [A1 [B1 [B2 [A2 [HPer1 [HPer2 [HCong HOS]]]]]]].
exists A1; exists A2; exists B1; exists B2.
assert (HNE : A1 <> A2) by (destruct HOS as [X [[H ?] ?]]; intro; subst A2; Col).
split; [destruct HOS; unfold TS in *; spliter; Col|].
split; [intro; treat_equalities; apply l8_7 in HPer1; intuition|split; [Cop|]].
intros A3 A4 B3 B4 HC1 HC2 HPerp1 HC3 HC4 HPerp2.
assert (HCong1 := rah__posidonius_aux HP A1 A2 A3 B1 B2 B3).
assert (HCong2 := rah__posidonius_aux HP A1 A2 A4 B1 B2 B4).
apply cong_inner_transitivity with A1 B1; apply cong_symmetry;
[apply HCong1|apply HCong2]; Cong; apply l8_2; auto.
Qed.

End rah_posidonius.