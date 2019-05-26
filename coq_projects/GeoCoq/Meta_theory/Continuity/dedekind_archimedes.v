Require Import GeoCoq.Axioms.continuity_axioms.
Require Import GeoCoq.Tarski_dev.Ch07_midpoint.

Section Dedekind_archimedes.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma archimedes_aux : (forall A B C, Out A B C -> Reach A B A C) -> archimedes_axiom.
Proof.
  intros Haux A B C D HAB.
  destruct (eq_dec_points C D).
    subst; exists B.
    split; Le.
    apply grad_init.
  destruct (segment_construction_3 A B C D) as [E [HOut HCong]]; auto.
  destruct (Haux A B E HOut) as [B' [HGrad HLe]]; trivial.
  exists B'.
  split; trivial.
  apply le_transitivity with A E; Le.
Qed.

Lemma dedekind__archimedes : (forall A B C D, ~ ~ Reach A B C D -> Reach A B C D) ->
  dedekind_s_axiom -> archimedes_axiom.
Proof.
  intros Hstab dedekind.
  apply archimedes_aux.
  intros A B C HOut.
  apply Hstab.
  intro HNReach.
  assert (HX : exists X, forall P Q, (Out A B P /\ ~ ~ Reach A B A P) ->
                                       (Out A B Q /\ ~ Reach A B A Q) -> Bet P X Q).
  { apply dedekind.
    exists A.
    intros X Y [HXOut HX] [HYOut HY].
    assert (HOut' : Out A X Y) by (apply l6_7 with B; [apply l6_6|]; trivial).
    destruct (HOut') as [_ [_ [|Habs]]]; trivial.
    exfalso.
    apply HX; clear HX.
    intro HX.
    apply HY.
    destruct HX as [B' [HGrad HLe]].
    exists B'; split; trivial.
    apply le_transitivity with A X; Le.
  }
  destruct HX as [X HX].
  assert_diffs.
  assert (HGrad := grad_init A B).
  assert (HBet : Bet B X C).
  { apply HX; split; trivial.
      apply out_trivial; auto.
    intro HAbs; apply HAbs.
    exists B; split; Le.
  }
  assert (Out A B X) by (apply out_bet_out_1 with C; auto).
  destruct HOut as [_ [_ [HBet2|HBet2]]]; [|exfalso; apply HNReach; exists B; split; Le].
  absurd (~ Reach A B A X).

  - intro HAbs.
    destruct (eq_dec_points X B).
      subst; apply HAbs; exists B; split; Le.
    destruct (le_cases X A A B) as [HLe|HLe].
      apply HAbs; exists B; split; Le.
    assert (Bet A B X) by (apply l6_13_1; Le).
    destruct HLe as [X0 [HBet1 HCong]].
    absurd (~ Reach A B A X0).
    { intro HNReach0.
      assert (HXOut : Out X X0 B).
        apply l6_7 with A; [|apply l6_6]; apply bet_out; Between.
        intro; treat_equalities; auto.
      destruct (le_cases X B X X0) as [HLe|HLe].
      - apply HNReach0; exists B; split; trivial.
        exists X0; split; Cong.
        apply between_inner_transitivity with X; Between.
        apply between_symmetry, l6_13_1; trivial.
        apply l6_6; trivial.
      - absurd (X = X0).
          assert_diffs; auto.
        apply between_equality with B.
          apply l6_13_1; trivial.
        apply between_symmetry, HX; split; trivial.
          apply out_trivial; auto.
          intro HN; apply HN; exists B; split; Le.
        apply l6_7 with X; trivial.
        apply l6_6, bet_out; Between.
        intro; subst X0; apply HNReach0.
        exists B; split; Le.
    }
    intro HReach.
    destruct HReach as [B' [HGrad' HLe]].
    destruct (segment_construction A B' A B) as [B1' [HBet' HCong']].
    apply HAbs; exists B1'; split.
      apply grad_stab with B'; Cong.
    apply bet2_le2__le1346 with X0 B'; Le; Between.
    apply cong__le, cong_transitivity with A B; Cong.

  - intro HReach.
    destruct (segment_construction_3 X C A B) as [X1 [HOut' HCong]]; auto.
      intro; subst; contradiction.
    assert (HBet1 : Bet A X X1).
      apply between_symmetry, bet_out__bet with C; eBetween.
    apply (not_bet_and_out X1 X C).
    split; [|apply l6_6; trivial].
    apply HX; split; trivial; [| |apply bet_out; auto].
    { apply l6_7 with X; trivial.
      assert_diffs; apply bet_out; auto.
    }
    destruct HReach as [B' [HGrad' HLe]].
    destruct (segment_construction A B' A B) as [B1' [HBet' HCong']].
    intro HAbs; apply HAbs.
    exists B1'; split.
      apply grad_stab with B'; Cong.
    apply bet2_le2__le1346 with X B'; Le.
    apply cong__le, cong_transitivity with A B; Cong.
Qed.

End Dedekind_archimedes.