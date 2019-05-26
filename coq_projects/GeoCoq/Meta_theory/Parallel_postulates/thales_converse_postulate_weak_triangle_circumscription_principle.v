Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.perp_bisect.

Section thales_converse_postulate_weak_triangle_circumscription_principle.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma thales_converse_postulate__weak_triangle_circumscription_principle :
  thales_converse_postulate -> weak_triangle_circumscription_principle.
Proof.
intros HP A B C A1 A2 B1 B2 HNC HPer HPerpB1 HPerpB2 HCop1 HCop2 HCop3 HCop4.
destruct (midpoint_existence A B) as [M HM]; exists M;
assert (H := HP A B C M HNC HM HPer); split;
[apply cong_cop2_perp_bisect_col with B C|
 apply cong_cop2_perp_bisect_col with A C]; Cong;
[| |destruct HM as [_ HM]; apply cong_transitivity with M A; Cong| |];
apply coplanar_perm_3, col2_cop__cop with A B; assert_diffs; Col; Cop.
Qed.

End thales_converse_postulate_weak_triangle_circumscription_principle.