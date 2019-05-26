(** * Classical Natural Deduction *)

Require Export BPCP_FOL.

(** ** Double Negation Translation *)

Implicit Type b : logic.

Definition cprv := @prv class full.

Instance iUnit P : interp unit (fun _ => tt) :=
  {| i_f _ _ := tt ; i_e := tt ; i_P _ _ := True ; i_Q := P  |}.

Hint Constructors prv.

Fixpoint cast {b} (phi : form b) : form full :=
  match phi with
  | Pr s t => Pr s t
  | Q => Q
  | Fal => Fal
  | Impl phi psi => Impl (cast phi) (cast psi)
  | All x phi => All x (cast phi)
  end.

Lemma subst_cast {b} x t phi :
  cast (subst x t phi) = subst x t (cast phi).
Proof.
  induction phi; cbn in *; dec; congruence.
Qed.

Lemma consts_casts {b} phi :
  consts (cast phi) = consts phi.
Proof.
  induction phi; cbn in *; congruence.
Qed.
  
Lemma MND_CND A (phi : form frag) :
  A ⊢M phi -> map cast A ⊢C cast phi.
Proof.
  unfold prv_min. revert A phi. remember frag as b. intros.
  induction H; cbn in *; subst; try congruence.
  - eapply Ctx, in_map_iff; eauto.
  - eapply ImpI; eauto.
  - eapply ImpE; eauto.
  - eapply AllI with (y0 := y).
    + rewrite consts_casts. intros [] % in_app_iff; eapply H; eauto.
      eapply in_app_iff. right. unfold consts_l in *.
      eapply in_flat_map in H1 as (? & (? & <- & ?) % in_map_iff & ?).
      rewrite consts_casts in H2. eapply in_flat_map. eauto.
    + rewrite subst_cast in IHprv. eauto.
  - rewrite subst_cast. eapply AllE; eauto.
Qed.
                                                    
Lemma cnd_XM:
  (forall (phi : form full), cprv [] phi -> valid phi) ->
  forall P, ~~ P -> P.
Proof.
  intros H P. specialize (H ( (¬¬Q) --> Q)).
  refine (H _ unit _ (iUnit P) (fun _ => tt)).
  eapply ImpI. eapply DN. eauto.
Qed.

Definition dnQ {b} (phi : form b) : form b := (phi --> Q) --> Q.

Fixpoint trans {b} (phi : form b) : form b :=
  match phi with
  | Impl phi1 phi2 => Impl (trans phi1) (trans phi2)
  | All x phi => All x (trans phi)
  | Pr s t => dnQ (Pr s t)
  | Q =>  Q  
  | Fal => Q
  end.

Lemma consts_trans b phi :
  consts (trans phi) = consts phi.
Proof.
  induction phi; cbn; try congruence; destruct b; cbn; try now rewrite !app_nil_r.
Qed.

Lemma trans_subst b x t (phi : form b) :
  trans (subst x t phi) = subst x t (trans phi).
Proof.
  induction phi; cbn; try congruence; decs.
Qed.

Lemma appCtx b psi1 psi2 A :
  psi1 --> psi2 el A -> A ⊢I psi1 -> A ⊢I psi2.
Proof.
  intros. eapply (ImpE (phi1 := psi1) (phi2 := psi2)); eauto using Ctx.
Qed.

Lemma app1 b psi1 psi2 A :
  (psi1 --> psi2 :: A) ⊢I psi1 -> (psi1 --> psi2 :: A) ⊢I psi2.
Proof.
  intros. eapply appCtx; eauto.
Qed.

Lemma app2 b psi1 psi2 A phi :
  (phi :: psi1 --> psi2 :: A) ⊢I psi1 -> (phi :: psi1 --> psi2 :: A) ⊢I psi2.
Proof.
  intros. eapply appCtx; eauto.
Qed.

Lemma app3 b psi1 psi2 A phi phi2 :
  (phi :: phi2 :: psi1 --> psi2 :: A) ⊢I psi1 -> (phi :: phi2 :: psi1 --> psi2 :: A) ⊢I psi2.
Proof.
  intros. eapply appCtx; eauto.
Qed.

Lemma trans_trans b (phi : form b) A :
  A ⊢I ((dnQ (trans phi)) --> trans phi).
Proof.
  revert A. induction phi using form_ind_subst; cbn; intros.
  - eapply ImpI. eapply ImpI. eapply app2. eapply ImpI.
    eapply app1. eapply Ctx. eauto.
  - cbn. eapply ImpI. eapply app1 . eapply ImpI. eapply Ctx. eauto.
  - eapply ImpI. eapply app1. eapply ImpI. eapply Ctx. eauto.
  - eapply ImpI. eapply ImpI. eapply ImpE. eapply IHphi2.
    eapply ImpI. eapply app3. eapply ImpI. eapply app2. eapply app1. eapply Ctx. eauto.
  - eapply ImpI. destruct (make_fresh (n :: consts phi ++ consts_l A)) as [y Hy].
    eapply AllI with (y0 := y).
    + cbn. rewrite consts_trans. rewrite !app_nil_r.
      intros [ | ] % in_app_iff; eauto.
    + rewrite <- trans_subst.
      assert ((dnQ (∀ n; trans phi) :: A) ⊢I ((dnQ (trans (subst n (P y) phi))) --> trans (subst n (P y) phi))) by eapply H.
      eapply (ImpE H0). eapply ImpI. eapply app2. eapply ImpI.
      eapply app2. rewrite trans_subst. eapply AllE.
      * reflexivity.
      * eapply Ctx. eauto.
Qed.
        
Lemma Double' b A (phi : form b) :
  A ⊢C phi -> map trans A ⊢I trans phi.
Proof.
  remember class as s; induction 1; cbn in *; subst; try congruence.
  - eapply Ctx. now eapply in_map.
  - eapply ImpI. eauto.
  - eapply ImpE; eauto.
  - eapply AllI with (y0 := y).
    + rewrite consts_trans. unfold consts_l. rewrite flat_map_concat_map.
      rewrite map_map. erewrite map_ext with (g := consts).
      now rewrite <- flat_map_concat_map.
      eapply consts_trans.
    + rewrite <- trans_subst. eauto.
  - rewrite trans_subst. eapply AllE; eauto.
  - specialize (IHprv eq_refl). eapply ImpE. eapply trans_trans. eauto.    
Qed.

Lemma Double b (phi : form b) :
  [] ⊢C phi -> [] ⊢I (trans phi).
Proof.
  eapply Double'. 
Qed.


(** ** Reduction **)
    
Section BPCP_CND.

  Variable R : BSRS.
  Context {b : logic}.

  Lemma BPCP_to_CND :
    BPCP R -> [] ⊢C (F R).
  Proof.
    intros H. rewrite BPCP_BPCP' in *. now apply BPCP_prv'.
  Qed.

  Lemma impl_trans A phi :
    trans (A ==> phi) = (map trans A) ==> trans phi.
  Proof.
    induction A; cbn; congruence.
  Qed.
    
  Lemma CND_BPCP :
    [] ⊢C (F R) -> BPCP R.
  Proof.
    intros H % Double % soundness.
    specialize (H _ _ (IB R) (fun _ => nil)).
    unfold F, F1, F2 in H. rewrite !impl_trans, !map_map, !impl_sat in H. cbn in H.
    eapply BPCP_BPCP'.  eapply H.
    - intros ? [(x,y) [<- ?] ] % in_map_iff ?. cbn in *. eapply H1.
      left. now rewrite !IB_enc.
    - intros ? [(x,y) [<- ?] ] % in_map_iff ? ? ? ?. cbn in *. eapply H1. intros.
      eapply H2. rewrite !IB_prep. cbn. econstructor 2; trivial.
    - intros. eapply H0. intros []; eauto.
  Qed.

  Lemma BPCP_CND :
    BPCP R <-> [] ⊢C (F R).
  Proof. 
    split. eapply BPCP_to_CND. intros ? % CND_BPCP.  eauto.
  Qed.

End BPCP_CND.



(** ** Corollaries **)

Corollary cprv_red :
  BPCP ⪯ cprv nil.
Proof.
  exists (fun R => F R). intros R. apply (BPCP_CND R).
Qed.

Corollary cprv_undec :
  UA -> ~ decidable (cprv nil).
Proof.
  intros H. now apply (not_decidable cprv_red).
Qed.

Corollary cprv_unenum :
  UA -> ~ enumerable (compl (@cprv nil)).
Proof.
  intros H. apply (not_coenumerable cprv_red); trivial.
Qed.
