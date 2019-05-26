

Section Sound_Rules.

  Load "PTS_spec".

Section Beta_Reduction_Sound.


  Hypothesis inv_prod : product_inversion le_type.

  Let le_type_prod_l := inv_prod_l le_type inv_prod.
  Let le_type_prod_r := inv_prod_r le_type inv_prod.


  Theorem beta_sound : rule_sound the_PTS beta.
Proof.
red in |- *.
simple induction 1; intros.
Inversion_typ H0.
Inversion_typ H2.
apply typ_conv_wf with (subst N U).
apply substitution with T; trivial.
Inversion_typ H5.
apply type_conv with V s1; trivial.
apply le_type_prod_l with (1 := H6).

apply type_correctness with (App (Abs T M) N); trivial.

apply le_type_trans with (2 := H3).
apply le_type_subst0 with V.
apply le_type_prod_r with (1 := H6).
Qed.

End Beta_Reduction_Sound.


Section Delta_Reduction_Sound.


  Theorem delta_sound : rule_sound the_PTS delta.
red in |- *.
simple destruct 1; intros.
Inversion_typ H1.
apply typ_conv_wf with (lift (S n) (typ_of_decl x0)); simpl in |- *;
 auto with pts.
replace x0 with (Def d T); simpl in |- *.
apply definition_lift; auto with pts.
apply typ_wf with (Ref n) T0; auto with pts.

apply fun_item with e0 n; auto with pts.

apply type_correctness with (Ref n); auto with pts.
Qed.

End Delta_Reduction_Sound.

End Sound_Rules.