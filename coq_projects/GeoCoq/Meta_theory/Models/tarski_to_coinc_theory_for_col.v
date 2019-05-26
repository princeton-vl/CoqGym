Require Export GeoCoq.Tarski_dev.Ch06_out_lines.
Require Import GeoCoq.Tactics.Coinc.tactics_axioms.

(* In this file we prove that Col in Tarski neutral dimensionless is a Coinc_theory *)

Section Tarski_is_a_Coinc_theory_for_col.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Definition diff : arity Tpoint 2 := fun A B : Tpoint => A <> B.

Lemma diff_perm_1 : forall A B, app_1_n diff A B -> app_n_1 diff B A.
Proof.
unfold diff.
simpl.
auto.
Qed.

Lemma diff_perm_2 : forall A B (X : cartesianPower Tpoint 0), app_2_n diff A B X -> app_2_n diff B A X.
Proof.
unfold diff.
unfold app_2_n.
simpl.
auto.
Qed.

Definition col : arity Tpoint 3 := Col.

Lemma col_perm_1 : forall A (X : cartesianPower Tpoint 2), app_1_n col A X -> app_n_1 col X A.
Proof.
unfold col.
simpl.
Col.
Qed.

Lemma col_perm_2 : forall A B (X : cartesianPower Tpoint 1), app_2_n col A B X -> app_2_n col B A X.
Proof.
unfold col.
unfold app_2_n.
simpl.
Col.
Qed.

Lemma col_bd : forall A (X : cartesianPower Tpoint 1), app_2_n col A A X.
Proof.
unfold col.
unfold app_2_n.
simpl.
Col.
Qed.

Lemma col_3 : forall (COL : cartesianPower Tpoint 3) (DIFF : cartesianPower Tpoint 2),
  pred_conj col COL DIFF -> app diff DIFF -> app col COL.
Proof.
unfold pred_conj.
unfold col.
unfold diff.
simpl in *.
intros COL DIFF HCol HDiff.
destruct HCol as [HCol1 [HCol2 HCol3]].
apply col3 with (fst DIFF) (snd DIFF); Col.
Qed.

Global Instance Tarski_is_a_Arity_for_col : Arity.
Proof. exact (Build_Arity Tpoint 0). Defined.

Global Instance Tarski_is_a_Coinc_predicates_for_col :
  (Coinc_predicates Tarski_is_a_Arity_for_col).
Proof.
exact (Build_Coinc_predicates Tarski_is_a_Arity_for_col diff Col).
Defined.

Global Instance Tarski_is_a_Coinc_theory_for_col :
  (Coinc_theory Tarski_is_a_Arity_for_col Tarski_is_a_Coinc_predicates_for_col).
Proof.
exact (Build_Coinc_theory Tarski_is_a_Arity_for_col
                          Tarski_is_a_Coinc_predicates_for_col
                          diff_perm_1 diff_perm_2 col_perm_1 col_perm_2
                          col_bd col_3).
Defined.

End Tarski_is_a_Coinc_theory_for_col.