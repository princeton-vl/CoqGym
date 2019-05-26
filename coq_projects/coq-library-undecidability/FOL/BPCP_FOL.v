(** * FOL Reductions *)

Require Export FOL.PCP Deduction.

(** ** Validity *)

Section validity.

  Notation u := 0. Notation v := 1.
  Context {b : logic}.
  Variable R : BSRS.

  Definition prep (x : string bool) (t : term) : term := fold_right t_f t x.
  Definition iprep domain eta {I : interp domain eta} (x : list bool) (y : domain) := fold_right i_f y x.
  Definition enc s := (prep s t_e).

  Definition F1 := map (fun '(x,y) => Pr (enc x) (enc y)) R.
  Definition F2 := map (fun '(x, y) => ∀ u; ∀ v; Pr u v --> Pr (prep x u) (prep y v)) R.
  Definition F3 := (∀ u; Pr u u --> Q).

  Definition F : form b := F1 ==> F2 ==> F3 --> Q.

  Lemma enc_vars x :
    vars_t (enc x) = [].
  Proof.
    induction x; trivial.
  Qed.

  Lemma prep_subst y t1 x t :
    subst_t y t1 (prep x t) = prep x (subst_t y t1 t).
  Proof.
    induction x; cbn; f_equal; eauto.
  Qed.

  Lemma prep_vars x t :
    vars_t (prep x t) = vars_t t.
  Proof.
    induction x; cbn; eauto.
  Qed.

  Lemma iprep_eval domain eta (I : interp domain eta) rho x s :
    eval rho (prep x s) = iprep x (eval rho s).
  Proof.
    induction x; cbn; now do 2 f_equal.
  Qed.

  Lemma iprep_app domain eta (I : interp domain eta) x y d :
    iprep (x ++ y) d = iprep x (iprep y d).
  Proof.
    unfold iprep. now rewrite fold_right_app.
  Qed.
  
  Global Instance IB : interp (string bool) (fun _ => []) :=
    {|
      i_f b s := b :: s ;
      i_e := nil;
      i_P u v := derivable R u v ;
      i_Q := BPCP' R
    |}.

  Lemma IB_prep rho s t :
    eval rho (prep s t) = s ++ eval rho t.
  Proof.
    induction s; cbn; trivial.
    rewrite <- IHs. reflexivity.
  Qed.

  Lemma IB_enc rho s :
    eval rho (enc s) = s.
  Proof.
    unfold enc. rewrite IB_prep.
    cbn. apply app_nil_r.
  Qed.

  Lemma IB_drv rho t1 t2 :
    rho ⊨ (Pr t1 t2) <-> derivable R (eval rho t1) (eval rho t2).
  Proof.
    cbn. reflexivity.
  Qed.

  Lemma IB_F1 rho :
    rho ⊫ F1.
  Proof.
    unfold F1. 
    intros ? ([x y] & <- & ?) % in_map_iff.
    cbn. econstructor. now rewrite !IB_enc.
  Qed.

  Lemma IB_F2 rho :
    rho ⊫ F2.
  Proof.
    unfold F2. intros ? ([x y] & <- & ?) % in_map_iff u v ?. cbn.
    rewrite !IB_prep. cbn in *. eauto using derivable.
  Qed.

  Lemma IB_F3 rho :
    rho ⊨ F3.
  Proof.
    cbn. apply cBPCP.
  Qed.

  Lemma IB_F rho :
    rho ⊨ F -> BPCP' R.
  Proof.
    intros H. unfold F in H. rewrite !impl_sat in H. eapply H.
    - eapply IB_F1.
    - eapply IB_F2.
    - apply IB_F3.
  Qed.

  Lemma drv_val domain eta (I : interp domain eta) rho u v :
    derivable R u v -> rho ⊨ (F1 ==> F2 ==> Pr (enc u) (enc v)).
  Proof.
    rewrite !impl_sat. intros. induction H.
    - eapply H0. eapply in_map_iff. exists (x/y). eauto.
    - eapply (H1 (∀ 0; ∀ 1; Pr 0 1 --> Pr (prep x 0) (prep y 1))) in IHderivable.
      + cbn. unfold enc in *. rewrite !iprep_eval in *. cbn in IHderivable.
        rewrite <- !iprep_app in IHderivable. eapply IHderivable.
      + eapply in_map_iff. exists (x/y). eauto.
  Qed.

  Theorem BPCP_valid :
    BPCP R <-> valid F.
  Proof.
    rewrite BPCP_BPCP'. split.
    - intros [u H] D eta I rho.
      eapply (@drv_val _ _ I) in H. unfold F. cbn in *.
      rewrite !impl_sat in *. cbn in *.
      intros. eapply (H2 (eval rho (enc u))). eauto.
    - intros H. apply IB_F with (rho := fun _ => nil), H.
  Qed.

  (** ** Provability *)

  Hint Resolve enc_vars.

  Definition ctx_S :=
    F3 :: rev F2 ++ rev F1.

  Lemma drv_prv s u v :
    derivable R u v -> (@prv s b ctx_S (Pr (enc u) (enc v))).
  Proof.
    induction 1.
    - econstructor. right. eapply in_app_iff. right.
      rewrite <- in_rev. eapply in_map_iff. exists (x/y). eauto.
    - assert (@prv s b ctx_S (∀ 0; ∀ 1; Pr 0 1 --> Pr (prep x 0) (prep y 1))).
      + econstructor. right. eapply in_app_iff. left.
        rewrite <- in_rev. eapply in_map_iff. exists (x/y). eauto.
      + eapply AllE with (t := enc u) in H1; eauto.
        cbn in H1. rewrite !prep_subst in H1. cbn in H1.
        eapply AllE with (t := enc v) in H1; eauto. cbn in H1.
        unfold enc in H1. rewrite !prep_subst in H1. cbn in H1.
        unfold enc, prep in *. rewrite !fold_right_app.
        eapply (ImpE H1). eassumption.
  Qed.

  Lemma impl_prv s A B phi :
    @prv s b (rev B ++ A) phi -> @ prv s b A (B ==> phi).
  Proof.
    revert A; induction B; intros A; cbn; simpl_list; intros.
    - firstorder.
    - eapply ImpI. now eapply IHB.
  Qed.

  Lemma BPCP_prv' s :
    BPCP' R -> @prv s b nil F.
  Proof.
    intros [u H].
    apply drv_prv with (s:=s) in H. unfold F.
    repeat eapply impl_prv. simpl_list. eapply ImpI.
    assert (@prv s b ctx_S (∀ 0; Pr 0 0 --> Q)).
    econstructor. now unfold ctx_S. eapply AllE with  (t := enc u) in H0.
    cbn in H0. now eapply (ImpE H0). apply prep_vars.
  Qed.

End validity.

Theorem BPCP_prv R :
  BPCP R <-> nil ⊢M (F R).
Proof.
  rewrite BPCP_BPCP'. split.
  - apply BPCP_prv'.
  - intros H % soundness. eapply BPCP_BPCP'. now apply (BPCP_valid R).
Qed.

(** ** Satisfiability *)

Lemma valid_satis phi :
  valid phi -> ~ satis (¬ phi).
Proof.
  intros H1 (D & eta & I & rho & H2).
  apply H2, (H1 D eta I rho).
Qed.

Theorem BPCP_satis R :
  ~ BPCP R <-> satis (¬ F R).
Proof.
  rewrite BPCP_BPCP'. split.
  - intros H. exists _, (fun _ => nil), (IB R), (fun _ => nil).
    intros H'. cbn. apply H, (IB_F H').
  - rewrite <- BPCP_BPCP'. intros H1 H2 % (BPCP_valid R (b:=full)).
    apply (valid_satis H2), H1.
Qed.



(** ** Corollaries *)

Lemma form_discrete {b : logic} :
  discrete (form b).
Proof.
  apply discrete_iff. constructor. apply eq_dec_form.
Qed.

Hint Resolve stack_enum form_discrete.

Definition UA :=
  ~ enumerable (compl BPCP).

Corollary valid_red :
  BPCP ⪯ @valid frag.
Proof.
  exists (fun R => F R). intros R. apply (BPCP_valid R).
Qed.

Corollary valid_undec :
  UA -> ~ decidable (@valid frag).
Proof.
  intros H. now apply (not_decidable valid_red).
Qed.

Corollary valid_unenum :
  UA -> ~ enumerable (compl (@valid frag)).
Proof.
  intros H. now apply (not_coenumerable valid_red).
Qed.

Corollary prv_red :
  BPCP ⪯ @prv intu frag nil.
Proof.
  exists (fun R => F R). intros R. apply (BPCP_prv R).
Qed.

Corollary prv_undec :
  UA -> ~ decidable (@prv intu frag nil).
Proof.
  intros H. now apply (not_decidable prv_red).
Qed.

Corollary prv_unenum :
  UA -> ~ enumerable (compl (@prv intu frag nil)).
Proof.
  intros H. apply (not_coenumerable prv_red); trivial.
Qed.

Corollary satis_red :
  compl BPCP ⪯ @satis full.
Proof.
  exists (fun R => ¬ F R). intros R. apply (BPCP_satis R).
Qed.

Corollary satis_undec :
  UA -> ~ decidable (@satis full).
Proof.
  intros H1 H2 % (dec_red satis_red).
  now apply H1, dec_count_enum.
Qed.

Corollary satis_enum :
  UA -> ~ enumerable (@satis full).
Proof.
  intros H1 H2 % (enumerable_red satis_red); auto.
Qed.


  





(** ** Non-Standard Model *)

Module NonStan. Section Nonstan.

  Variable R : BSRS.

  Instance IB : interp (option (string bool)) (fun _ => Some nil) :=
    {|
      i_f b x := match x with Some u => Some (b :: u) | None => None end ;
      i_e := Some nil;
      i_P x y := match x, y with Some u, Some v => derivable R u v | _, _ => True end ;
      i_Q := False
    |}.

  Lemma IB_eval_Some rho t u v :
    eval rho t = Some v -> eval rho (prep u t) = Some (u ++ v).
  Proof.
    intros H. induction u; cbn; trivial.
    unfold prep in IHu. now rewrite IHu.
  Qed.

  Lemma IB_eval_None rho t u :
    eval rho t = None -> eval rho (prep u t) = None.
  Proof.
    intros H. induction u; cbn; trivial.
    unfold prep in IHu. now rewrite IHu.
  Qed.

  Lemma IB_enc rho u :
    eval rho (enc u) = Some u.
  Proof.
    unfold enc. rewrite <- (app_nil_r u) at 2.
    now apply IB_eval_Some.
  Qed.

  Lemma IB_deriv rho u v :
    rho ⊨ (Pr (enc u) (enc v)) <-> derivable R u v.
  Proof.
    cbn. rewrite !IB_enc. reflexivity.
  Qed.

  Lemma IB_deriv' rho t1 t2 u v :
    eval rho t1 = Some u -> eval rho t2 = Some v ->
    rho ⊨ (Pr t1 t2) <-> derivable R u v.
  Proof.
    intros H1 H2. cbn. rewrite H1, H2. reflexivity.
  Qed.

  Lemma IB_F1 rho :
    rho ⊫ F1 R.
  Proof.
    unfold F1. 
    intros ? ([x y] & <- & ?) % in_map_iff.
    cbn. rewrite !IB_enc. now constructor.
  Qed.

  Lemma IB_F2 rho :
    rho ⊫ F2 R.
  Proof.
    unfold F2. intros ? ([x y] & <- & ?) % in_map_iff [u|] [v|] ?; cbn in *.
    - erewrite !IB_eval_Some; cbn; auto. now constructor 2.
    - erewrite IB_eval_Some, IB_eval_None; cbn; auto.
    - erewrite IB_eval_None; cbn; auto.
    - erewrite !IB_eval_None; cbn; auto.
  Qed.

  Lemma IB_F rho :
    rho ⊨ F R.
  Proof.
    unfold F. rewrite !impl_sat. intros _ _ H.
    apply (H None). cbn. auto.
  Qed.

  Lemma IB_nonstandard rho :
    rho ⊨ ¬ ∀ 0; ¬ Pr 0 0.
  Proof.
    intros H. apply (H None). cbn. auto.
  Qed.

End Nonstan. End NonStan.
