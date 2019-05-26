
Section Soundness.

  Load "PTS_spec".

  Notation typ2 := (typ the_PTS) (only parsing).
  Notation wf_type2 := (wf_type the_PTS) (only parsing).


Section SoundnessDef.

  Variable R : red_rule.

  Definition rule_sound :=
    forall (e : env) (x y : term),
    R e x y -> forall T : term, typ the_PTS e x T -> typ the_PTS e y T.

End SoundnessDef.


Section Sound_context.


  Variable the_rule : Basic_rule.

  Let R := Rule the_rule.
  Let Rlifts : R_lift R := R_lifts the_rule.

  Hint Resolve Rlifts: pts.


  Hypothesis
    incl_R_le_type :
      forall (e : env) (x y : term), ctxt R e x y -> le_type e y x.



  Theorem red_incl_le_type :
   forall (e : env) (x y : term), red R e x y -> le_type e y x.
simple induction 1; intros; auto with pts.
apply le_type_trans with y0; auto with pts.
Qed.


  Theorem red_in_env :
   forall (e : env) (u v t T : term),
   typ the_PTS (Ax u :: e) t T ->
   forall s : sort,
   typ the_PTS e v (Srt s) -> red R e u v -> typ the_PTS (Ax v :: e) t T.
intros.
apply subtype_in_env with (1 := H).
constructor.
constructor.
red in |- *.
auto with pts.
apply red_incl_le_type.
trivial with pts.

apply wf_var with s; trivial with pts.
Qed.


  Theorem ctxt_sound : rule_sound R -> rule_sound (ctxt R).
red in |- *.
simple induction 2; auto with pts; intros.
Inversion_typ H3.
apply typ_conv_wf with (Prod M U); auto with pts.
apply type_conv with (Prod M' U) s; auto with pts.
Inversion_typ H5.
apply type_abs with s3; auto with pts.
apply type_prod with s1 s2; auto with pts.
apply red_in_env with M s1; auto with pts.

apply red_in_env with M s1; auto with pts.

apply incl_R_le_type.
auto with pts.

apply type_correctness with (Abs M N); auto with pts.

Inversion_typ H3.
apply typ_conv_wf with (Prod N U); auto with pts.
apply type_abs with s; auto with pts.

apply type_correctness with (Abs N M); auto with pts.

Inversion_typ H3.
apply typ_conv_wf with (subst M2 Ur); auto with pts.
apply type_app with V; auto with pts.

apply type_correctness with (App M1 M2); auto with pts.

Inversion_typ H3.
apply typ_conv_wf with (subst M2 Ur); auto with pts.
cut (wf_type the_PTS e0 (Prod V Ur)); intros.
inversion_clear H7.
Inversion_typ H8.
apply type_conv with (subst N2 Ur) s2; auto with pts.
apply type_app with V; auto with pts.

apply red_incl_le_type.
unfold subst in |- *.
apply red_subst_l with e0; auto with pts.

replace (Srt s2) with (subst M2 (Srt s2)); auto with pts.
apply substitution with V; auto with pts.

apply type_correctness with M1; auto with pts.

apply type_correctness with (App M1 M2); auto with pts.

Inversion_typ H3.
apply typ_conv_wf with (Srt s3); auto with pts.
apply type_prod with s1 s2; auto with pts.
apply red_in_env with M1 s1; auto with pts.

apply type_correctness with (Prod M1 M2); auto with pts.

Inversion_typ H3.
apply typ_conv_wf with (Srt s3); auto with pts.
apply type_prod with s1 s2; auto with pts.

apply type_correctness with (Prod M1 M2); auto with pts.
Qed.


End Sound_context.


  Theorem incl_sound :
   forall P Q : red_rule,
   (forall (e : env) (x y : term), P e x y -> Q e x y) ->
   rule_sound Q -> rule_sound P.
unfold rule_sound in |- *.
intros.
apply H0 with x; auto with pts.
Qed.

  Theorem union_sound :
   forall P Q : red_rule,
   rule_sound P -> rule_sound Q -> rule_sound (reunion P Q).
red in |- *.
simple induction 3; intros.
apply H with x; auto with pts.

apply H0 with x; auto with pts.
Qed.


  Theorem clos_trans_sound :
   forall P : red_rule,
   rule_sound P -> rule_sound (fun e : env => clos_trans term (P e)).
red in |- *.
simple induction 2; intros; auto with pts.
apply H with x0; auto with pts.
Qed.


  Theorem clos_refl_trans_sound :
   forall P : red_rule, rule_sound P -> rule_sound (R_rt P).
red in |- *.
simple induction 2; intros; auto with pts.
apply H with x0; auto with pts.
Qed.


End Soundness.