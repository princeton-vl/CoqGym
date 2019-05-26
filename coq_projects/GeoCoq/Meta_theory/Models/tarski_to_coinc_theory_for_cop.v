Require Import GeoCoq.Tarski_dev.Ch09_plane.
Require Import GeoCoq.Tactics.Coinc.tactics_axioms.

(* In this file we prove that Cop in Tarski neutral dimensionless is a Coinc_theory *)

Section Tarski_is_a_Coinc_theory_for_cop.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Definition not_col : arity Tpoint 3 := fun A B C : Tpoint => ~ Col A B C.

Lemma not_col_perm_1 : forall A X, app_1_n not_col A X -> app_n_1 not_col X A.
Proof.
unfold not_col.
simpl.
Col.
Qed.

Lemma not_col_perm_2 : forall A B (X : cartesianPower Tpoint 1),
  app_2_n not_col A B X -> app_2_n not_col B A X.
Proof.
unfold not_col.
unfold app_2_n.
simpl.
Col.
Qed.

Definition cop : arity Tpoint 4 := Coplanar.

Lemma cop_perm_1 : forall A (X : cartesianPower Tpoint 3), app_1_n cop A X -> app_n_1 cop X A.
Proof.
unfold cop.
simpl.
Cop.
Qed.

Lemma cop_perm_2 : forall A B (X : cartesianPower Tpoint 2), app_2_n cop A B X -> app_2_n cop B A X.
Proof.
unfold cop.
unfold app_2_n.
simpl.
Cop.
Qed.

Lemma cop_bd : forall A (X : cartesianPower Tpoint 2), app_2_n cop A A X.
Proof.
unfold cop.
unfold app_2_n.
simpl.
Cop.
Qed.

Lemma cop_3 : forall (COP : cartesianPower Tpoint 4) (NOT_COL : cartesianPower Tpoint 3),
  pred_conj cop COP NOT_COL -> app not_col NOT_COL -> app cop COP.
Proof.
unfold pred_conj.
unfold cop.
unfold not_col.
simpl in *.
intros COP NOT_COL HCop HNot_Col.
destruct HCop as [HCop1 [HCop2 [HCop3 HCop4]]].
apply coplanar_pseudo_trans with (fst NOT_COL) (fst (snd NOT_COL)) (snd (snd NOT_COL)); Cop.
Qed.

Global Instance Tarski_is_a_Arity_for_cop : Arity.
Proof. exact (Build_Arity Tpoint 1). Defined.

Global Instance Tarski_is_a_Coinc_predicates_for_cop :
  (Coinc_predicates Tarski_is_a_Arity_for_cop).
Proof.
exact (Build_Coinc_predicates Tarski_is_a_Arity_for_cop not_col cop).
Defined.

Global Instance Tarski_is_a_Coinc_theory_for_cop :   (Coinc_theory Tarski_is_a_Arity_for_cop Tarski_is_a_Coinc_predicates_for_cop).
Proof.
exact (Build_Coinc_theory Tarski_is_a_Arity_for_cop
                          Tarski_is_a_Coinc_predicates_for_cop
                          not_col_perm_1 not_col_perm_2 cop_perm_1 cop_perm_2
                          cop_bd cop_3).
Defined.

End Tarski_is_a_Coinc_theory_for_cop.