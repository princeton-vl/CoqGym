Require Export GeoCoq.Tarski_dev.Ch06_out_lines.
Require Import GeoCoq.Tactics.Coinc.tactics_axioms.

(** In this file we prove that Tarski neutral dimensionless is a Col_theory. *)

Section Tarski_is_a_Col_theory.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Global Instance Tarski_is_a_Col_theory : (Col_theory Tpoint Col).
Proof.
exact (Build_Col_theory Tpoint Col col_trivial_1 col_permutation_1 col_permutation_5 col3).
Defined.

End Tarski_is_a_Col_theory.
