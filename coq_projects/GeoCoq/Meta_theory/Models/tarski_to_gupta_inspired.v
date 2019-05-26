Require Import GeoCoq.Axioms.tarski_axioms.
Require Import GeoCoq.Axioms.gupta_inspired_variant_axioms.
Require Import GeoCoq.Tarski_dev.Ch05_bet_le.

Section Tarski_neutral_dimensionless_to_Gupta_inspired_variant_of_Tarski_neutral_dimensionless.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma cong_inner_transitivity' : forall A B C D E F, Cong A B E F -> Cong C D E F -> Cong A B C D.
Proof.
  intros A B C D E F H1 H2; apply (cong_inner_transitivity E F); apply cong_symmetry; assumption.
Qed.

Lemma inner_pasch' : forall A B C P Q,
  Bet A P C -> Bet B Q C -> A <> P -> P <> C -> B <> Q -> Q <> C ->
  ~ (Bet A B C \/ Bet B C A \/ Bet C A B) ->
  exists x : Tpoint, Bet P x B /\ Bet Q x A.
Proof.
  intros A B C P Q; intros; apply inner_pasch with C; assumption.
Qed.

Instance T_to_TG : Gupta_inspired_variant_of_Tarski_neutral_dimensionless_with_decidable_point_equality.
Proof.
exact (Build_Gupta_inspired_variant_of_Tarski_neutral_dimensionless_with_decidable_point_equality
  Tpoint Bet Cong eq_dec_points
  cong_pseudo_reflexivity cong_inner_transitivity' cong_identity
  segment_construction five_segment between_symmetry between_inner_transitivity inner_pasch'
  PA PB PC lower_dim).
Defined.

End Tarski_neutral_dimensionless_to_Gupta_inspired_variant_of_Tarski_neutral_dimensionless.

Section Tarski_2D_to_Gupta_inspired_variant_of_Tarski_2D.

Context `{T2D:Tarski_2D}.

Instance T2D_to_TG2D : Gupta_inspired_variant_of_Tarski_2D T_to_TG.
Proof.
  split; intros A B C P Q HPQ HAB HAC HBC; apply upper_dim, HPQ.
Defined.

End Tarski_2D_to_Gupta_inspired_variant_of_Tarski_2D.

Section Tarski_euclidean_to_Gupta_inspired_variant_of_Tarski_euclidean.

Context `{TE:Tarski_euclidean}.

Instance T_euclidean_to_TG_euclidean : Gupta_inspired_variant_of_Tarski_euclidean T_to_TG.
Proof.
  split; intros A B C D T H1 H2 HBD HDC HNCol.
  assert (A <> D) by (intro; subst; apply HNCol; right; right; apply between_symmetry, H2).
  apply euclid with D; assumption.
Defined.

End Tarski_euclidean_to_Gupta_inspired_variant_of_Tarski_euclidean.