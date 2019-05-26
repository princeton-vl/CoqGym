Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section playfair_bis_playfair.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma playfair_bis__playfair : alternative_playfair_s_postulate -> playfair_s_postulate.
Proof.
intros playfair_bis.
intros A1 A2 B1 B2 C1 C2 P HParAB HPB HParAC HPC.
elim (col_dec A1 A2 P); [intro HCol; treat_equalities|intro HNC1].

  {
  elim HParAB; [intros [_ [_ [_ HF]]]; exfalso; apply HF; exists P; Col|].
  intros [_ [_ [HCol1 HCol2]]].
  elim HParAC; [intros [_ [_ [_ HF]]]; exfalso; apply HF; exists P; Col|].
  intros [_ [_ [HCol3 HCol4]]].
  assert_diffs; split; ColR.
  }

  {
  assert_diffs.
  assert(HX := perp_exists P A1 A2).
  destruct HX as [X HPerp1]; auto.
  assert_diffs.
  assert (HCop1 : Coplanar P X A1 A2) by Cop.
  elim (perp_not_col2 _ _ _ _ HPerp1); intro HNC2.

    {
    assert(HD := ex_perp_cop P X P A1).
    destruct HD as [D [HPerp2 HCop2]]; auto.
    assert_diffs.
    assert(Perp2 A1 A2 P D P).
      {
      exists X.
      exists P.
      split; Col.
      split; Perp.
      }
    assert(Col B1 P D /\ Col B2 P D)
      by (apply (playfair_bis A1 A2 _ _ _ _ P); Col; CopR).
    assert(Col C1 P D /\ Col C2 P D)
      by (apply (playfair_bis A1 A2 _ _ _ _ P); Col; CopR).
    spliter.
    split; apply(col3 P D); Col.
    }

    {
    assert(HD := ex_perp_cop P X P A2).
    destruct HD as [D [HPerp2 HCop2]]; auto.
    assert_diffs.
    assert(Perp2 A1 A2 P D P).
      {
      exists X.
      exists P.
      split; Col.
      split; Perp.
      }
    assert(Col B1 P D /\ Col B2 P D)
      by (apply (playfair_bis A1 A2 _ _ _ _ P); Col; CopR).
    assert(Col C1 P D /\ Col C2 P D)
      by (apply (playfair_bis A1 A2 _ _ _ _ P); Col; CopR).
    spliter.
    split; apply(col3 P D); Col.
    }
  }
Qed.

End playfair_bis_playfair.