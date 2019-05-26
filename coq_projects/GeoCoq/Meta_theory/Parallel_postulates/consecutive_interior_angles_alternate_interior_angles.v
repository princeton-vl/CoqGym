Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.suma.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section consecutive_interior_angles_alternate_interior_angles.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma consecutive_interior__alternate_interior :
   consecutive_interior_angles_postulate -> alternate_interior_angles_postulate.
Proof.
  intros cia A B C D Hts HPar.
  destruct (segment_construction D C C D) as [D' []].
  apply suppa2__conga123 with A C D'.
  - apply cia; [|assert_diffs; apply par_left_comm, par_col_par with D; Col].
    exists D; split; trivial.
    destruct Hts as [_ [HNCol _]].
    repeat split.
      intro; apply HNCol; ColR.
      Col.
    exists C; split; [Col|Between].
  - assert_diffs; split; auto.
    exists D'; split; CongA.
Qed.

End consecutive_interior_angles_alternate_interior_angles.