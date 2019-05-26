Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section proclus_bis_proclus.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma proclus_bis__proclus : alternative_proclus_postulate -> proclus_postulate.
Proof.
  intros proclus_bis A B C D P Q HPar HInter HNCol HCop.
  elim(col_dec C D P).
    intro; exists P; Col.
  intro HNCol1.
  apply par_symmetry in HPar.
  apply (par_not_col_strict _ _ _ _ P) in HPar; auto.
  assert(HC0 := l8_18_existence C D P).
  destruct HC0 as [C0 []]; auto.
  assert(HNCol2 : ~ Col C0 A B) by (apply (par_not_col C D); Col).
  assert_diffs.
  assert(HA0 : exists A0, Col A B A0 /\ ~ Col C0 P A0).
  { elim(col_dec C0 P A).
    - intro.
      assert(~ Col C0 P B) by (intro; apply HNCol2; ColR).
      exists B.
      split; Col.

    - intro.
      exists A.
      split; Col.
  }
  destruct HA0 as [A0 []].
  assert(HA' := l10_15 C0 P P A0).
  destruct HA' as [A' []]; Col.
  assert_diffs.
  elim(col_dec A0 P A').
  - intro.
    apply (proclus_bis A0 P); Col; [| |intro; apply HNCol; ColR].

      {
      exists C0.
      exists P.
      split; Col.
      split; [|Perp].
      apply perp_right_comm.
      apply (perp_col1 _ _ _ A'); Perp; Col.
      }

      {
      apply pars__coplanar in HPar.
      assert (Coplanar C D P A0) by (apply col2_cop__cop with A B; Col; Cop).
      CopR.
      }

  - intro.
    exfalso.
    assert(HY := proclus_bis A' P C D P A0).
    assert (Coplanar C D P A0).
      {
      apply pars__coplanar in HPar.
      assert (Coplanar C D P A0) by (apply col2_cop__cop with A B; Col; Cop).
      CopR.
      }
    destruct HY as [Y []]; Col.

      {
      exists C0; exists P; repeat split; Col; Perp.
      }

      {
      assert (Coplanar P A0 A' C0) by Cop.
      elim (eq_dec_points C0 C); intro; treat_equalities;
      elim (eq_dec_points C0 D); intro; treat_equalities; auto; try CopR.
      assert (Coplanar P A0 C C0) by (apply col2_cop__cop with C D; Col; Cop).
      assert (Coplanar P A0 D C0); [|CopR].
      apply col2_cop__cop with C D; Col; Cop.
      }

      {
      assert(Habs : ~ Col Y A B) by (apply (par_not_col C D); Col).
      apply Habs; ColR.
      }
Qed.

End proclus_bis_proclus.