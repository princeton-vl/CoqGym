Require Import GeoCoq.Tarski_dev.Annexes.quadrilaterals.

Section Tagged_predicates.

Context `{Tn:Tarski_neutral_dimensionless}.

Definition Diff_tagged (A B: Tpoint) := A <> B.

Lemma Diff_Diff_tagged : forall A B , A <> B -> Diff_tagged A B.
Proof.
trivial.
Qed.

Lemma Diff_tagged_Diff : forall A B , Diff_tagged A B -> A <> B.
Proof.
trivial.
Qed.

Lemma Diff_perm :
  forall (A B: Tpoint),
  A <> B ->
  A <> B /\ B <> A.
Proof.
intros.
repeat split; intuition.
Qed.

Definition Cong_tagged A B C D := Cong A B C D.

Lemma Cong_Cong_tagged : forall A B C D, Cong A B C D -> Cong_tagged A B C D.
Proof.
trivial.
Qed.

Lemma Cong_tagged_Cong : forall A B C D, Cong_tagged A B C D -> Cong A B C D.
Proof.
trivial.
Qed.

Definition Bet_tagged A B C := Bet A B C.

Lemma Bet_Bet_tagged : forall A B C, Bet A B C -> Bet_tagged A B C.
Proof.
trivial.
Qed.

Lemma Bet_tagged_Bet : forall A B C, Bet_tagged A B C -> Bet A B C.
Proof.
trivial.
Qed.

Definition Col_tagged A B C := Col A B C.

Lemma Col_Col_tagged : forall A B C, Col A B C -> Col_tagged A B C.
Proof.
trivial.
Qed.

Lemma Col_tagged_Col : forall A B C, Col_tagged A B C -> Col A B C.
Proof.
trivial.
Qed.

Definition NCol_tagged A B C := ~ Col A B C.

Lemma NCol_NCol_tagged : forall A B C, ~ Col A B C -> NCol_tagged A B C.
Proof.
trivial.
Qed.

Lemma NCol_tagged_NCol : forall A B C, NCol_tagged A B C -> ~ Col A B C.
Proof.
trivial.
Qed.

Definition Mid_tagged A B C := Midpoint A B C.

Lemma Mid_Mid_tagged : forall A B C, Midpoint A B C -> Mid_tagged A B C.
Proof.
trivial.
Qed.

Lemma Mid_tagged_Mid : forall A B C, Mid_tagged A B C -> Midpoint A B C.
Proof.
trivial.
Qed.

Definition Per_tagged A B C := Per A B C.

Lemma Per_Per_tagged : forall A B C, Per A B C -> Per_tagged A B C.
Proof.
trivial.
Qed.

Lemma Per_tagged_Per : forall A B C, Per_tagged A B C -> Per A B C.
Proof.
trivial.
Qed.

Definition Perp_in_tagged X A B C D := Perp_at X A B C D.

Lemma Perp_in_Perp_in_tagged : forall X A B C D, Perp_at X A B C D -> Perp_in_tagged X A B C D.
Proof.
trivial.
Qed.

Lemma Perp_in_tagged_Perp_in : forall X A B C D, Perp_in_tagged X A B C D -> Perp_at X A B C D.
Proof.
trivial.
Qed.

Definition Perp_tagged A B C D := Perp A B C D.

Lemma Perp_Perp_tagged : forall A B C D, Perp A B C D -> Perp_tagged A B C D.
Proof.
trivial.
Qed.

Lemma Perp_tagged_Perp : forall A B C D, Perp_tagged A B C D -> Perp A B C D.
Proof.
trivial.
Qed.

Definition Par_strict_tagged A B C D := Par_strict A B C D.

Lemma Par_strict_Par_strict_tagged : forall A B C D, Par_strict A B C D -> Par_strict_tagged A B C D.
Proof.
trivial.
Qed.

Lemma Par_strict_tagged_Par_strict : forall A B C D, Par_strict_tagged A B C D -> Par_strict A B C D.
Proof.
trivial.
Qed.

Definition Par_tagged A B C D := Par A B C D.

Lemma Par_Par_tagged : forall A B C D, Par A B C D -> Par_tagged A B C D.
Proof.
trivial.
Qed.

Lemma Par_tagged_Par : forall A B C D, Par_tagged A B C D -> Par A B C D.
Proof.
trivial.
Qed.

Definition Plg_tagged A B C D := Parallelogram A B C D.

Lemma Plg_Plg_tagged : forall A B C D, Parallelogram A B C D -> Plg_tagged A B C D.
Proof.
trivial.
Qed.

Lemma Plg_tagged_Plg : forall A B C D, Plg_tagged A B C D -> Parallelogram A B C D.
Proof.
trivial.
Qed.

End Tagged_predicates.
