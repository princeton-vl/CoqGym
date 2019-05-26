
Require Export Relation_Definitions.
Require Export Relation_Operators.
Require Export Operators_Properties.

Require Export Inclusion.
Require Export Transitive_Closure.
Require Export Union.
Require Export Inverse_Image.
Require Export Lexicographic_Product.


Hint Resolve rt_step rt_refl rst_step rst_refl t_step: core.
Hint Unfold transp union reflexive transitive: core.
Hint Immediate rst_sym: core.


  Lemma clos_refl_trans_ind_right :
   forall (A : Set) (R : relation A) (M : A) (P : A -> Prop),
   P M ->
   (forall P0 N : A, R N P0 -> clos_refl_trans A R P0 M -> P P0 -> P N) ->
   forall a : A, clos_refl_trans A R a M -> P a.
intros.
generalize H H0.
elim H1; intros; auto.
apply H4 with y; auto.

apply H3; intros.
apply H5; intros; auto.
apply H7 with P0; auto.

apply H7 with P0; auto.
apply rt_trans with y; auto.
Qed.

  Hint Resolve left_sym right_sym sp_swap sp_noswap: core.