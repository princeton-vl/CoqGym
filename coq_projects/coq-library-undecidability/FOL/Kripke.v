(** * Kripke Semantics *)

Require Export FOL.Deduction.

(** ** Kripke Models *)

Section Kripke.

  Context {domain : Type}.
  Variable eta : nat -> domain.

  Structure embedding (I J : interp domain eta) :=
    {
      Hf : forall b d, @i_f _ _ I b d = @i_f _ _ J b d ;
      He : @i_e _ _ I = @i_e _ _ J ;

      HP : forall c d, @i_P _ _ I c d -> @i_P _ _ J c d ;
      HQ : @i_Q _ _ I -> @i_Q _ _ J 
    }.

  Lemma emb_refl (I : interp domain eta) :
    embedding I I.
  Proof.
    firstorder.
  Qed.
      
  Definition emb_trans (I J K : interp domain eta) :
    embedding I J -> embedding J K -> embedding I K.
  Proof.
    intros F F'. econstructor.
    - intros b d. rewrite (Hf F), (Hf F'). reflexivity. 
    - now rewrite (He F), (He F').
    - intros c d. intros. now eapply (HP F'), (HP F).
    - intros. now eapply (HQ F'), (HQ F).
  Qed.
      
  Class kmodel :=
    {
      nodes : Type ;

      reachable : nodes -> nodes -> Prop ;
      reach_refl u : reachable u u ;
      reach_tran u v w : reachable u v -> reachable v w -> reachable u w ;

      world : nodes -> interp domain eta ;

      world_f : forall u v, reachable u v -> embedding (world u) (world v)
    }.

  Variable M : kmodel.
  Implicit Type b : logic.

  Fixpoint ksat b u (rho : var -> domain) (phi : form b) : Prop :=
    match phi with
    | Pr t1 t2 => @i_P _ _ (world u) (@eval _ _ (world u) rho t1) (@eval _ _ (world u) rho t2)
    | Q => @i_Q _ _ (world u)
    | Fal => False
    | Impl phi psi => forall v, reachable u v -> ksat v rho phi -> ksat v rho psi
    | All n phi => forall v, reachable u v -> forall j : domain, ksat v (rho [[ n := j ]]) phi
    end.

  Global Arguments ksat {_} _ _ _.
  
  Notation "rho  '⊨(' u ')'  phi" := (ksat u rho phi) (at level 20).
  Notation "rho  '⊫(' u ')'  A" := (forall phi, phi el A -> rho ⊨(u) phi) (at level 20).

  Lemma eval_invar u v :
    reachable u v -> forall rho t, @eval _ _ (world u) rho t = @eval _ _ (world v)rho t.
  Proof.
    intros H rho t. induction t; cbn; try congruence.
    - now rewrite IHt, (Hf (world_f H)).
    - now rewrite (He (world_f H)).
  Qed.
  
  Lemma ksat_mon b (u : nodes) (rho : var -> domain) (phi : form b) :
    forall v (H : reachable u v), ksat u rho phi -> ksat v rho phi.
  Proof.
    revert rho. induction phi; intros rho v H; cbn.
    - intros. rewrite <- !(eval_invar H). now eapply (world_f H).
    - intros. now eapply (world_f H).
    - eauto.
    - intros H1 K H2 H3. apply H1; eauto. eapply reach_tran; eauto.
    - intros H1 K H2 k. apply (H1 K (reach_tran H H2) k).
  Qed.
  
  Lemma ksat_iff b u rho phi :
    ksat u rho phi <-> forall v (H : reachable u v), ksat v rho phi.
  Proof.
    split.
    - intros H1 v H2. eapply ksat_mon; eauto.
    - intros H. apply H. eapply reach_refl.
  Qed.

  Notation sem_imp v rho A phi :=
    ((forall psi, psi el A -> ksat v rho psi) -> ksat v rho phi).

  Lemma impl_ksat {b} u A rho (phi : form b) :
    ksat u rho (A ==> phi) <-> (forall v, reachable u v -> sem_imp v rho A phi).
  Proof.
    cbn. revert u rho. induction A; cbn; intros u rho.
    - intuition. 
      + eapply ksat_mon; eauto.
      + apply H. eapply reach_refl. tauto.
    - split; intros H v H1 H2.
      + specialize (H v H1). rewrite IHA in H.
        assert (H' : ksat v rho a) by (now apply H2; now left).
        apply (H H' v (reach_refl v)).
        intros psi H0. apply H2. now right.
      + apply IHA. intros w H3 H4.
        apply H. eapply reach_tran; eauto. intros psi [-> |H'].
        * eapply ksat_mon; eauto.
        * now apply H4.
  Qed.

  Lemma impl_ksat' {b} u A rho (phi : form b) :
    ksat u rho (A ==> phi) -> (forall v, reachable u v -> sem_imp v rho A phi).
  Proof.
    apply impl_ksat.
  Qed.

End Kripke.

Arguments ksat {_} _ _ {_} _ _ _, {_ _} _ {_} _ _ _.

(* Notation "rho '⊫(' u ')'  A" := ( forall phi, phi el A -> ksat u rho phi) (at level 20). *)
Notation "rho '⊩(' u , M , eta ')' phi" := (@ksat _ eta M _ u rho phi) (at level 20).

(** ** Connection to Tarski Semantics *)

Instance interp_kripke {domain eta} (I : interp domain eta) : kmodel  eta :=
  {| nodes := unit ; reachable u v := True |}.
Proof.
  all: try abstract tauto.
  intros. apply emb_refl.
Defined.

Lemma kripke_tarski domain eta (b : logic) (I : interp domain eta) rho phi :
  rho ⊨ phi <-> rho ⊩(tt, interp_kripke I, _) phi.
Proof.
  revert rho. induction phi; intros rho.
  - tauto.
  - tauto.
  - tauto.
  - split; intros H. cbn in *.
    + intros [] [] H'. apply IHphi2, H,  IHphi1, H'.
    + intros H'. apply IHphi2, (H tt Logic.I), IHphi1, H'.
  - split; intros H; cbn in *.
    + intros [] [] i. apply IHphi, H.
    + intros i. apply IHphi, (H tt Logic.I).
Qed.

Definition kvalid b (phi : form b) :=
  forall domain eta (M : @kmodel domain eta) u rho, rho ⊩(u,M,eta) phi.

Definition ksatis b (phi : form b) :=
  exists domain eta (M : @kmodel domain eta) u rho, ksat eta M u rho phi.

Lemma kvalid_valid b (phi : form b) :
  kvalid phi -> valid phi.
Proof.
  intros H domain I eta rho. eapply kripke_tarski, H.
Qed.

Lemma ksatis_satis b (phi : form b) :
  satis phi -> ksatis phi.
Proof.
  intros (domain & eta & I & rho & ?). eapply kripke_tarski in H.
  now exists domain, eta, (interp_kripke I), tt,  rho.
Qed.



(** ** Soundness **)

Hint Resolve reach_refl.

Definition kcast domain (eta eta' : nat -> domain) (M : kmodel eta) : kmodel eta'.
Proof.
  unshelve econstructor.
  - exact (@nodes _ _ M).
  - exact (@reachable _ _ M).
  - intros. eapply cast. eapply (@world _ _ M). exact X.
  - eauto.
  - destruct M; eauto.
  - destruct M. abstract (
    intros; cbn; destruct (world_f0 u v H), (world0 u), (world0 v); cbn; econstructor; eauto).
Defined.

Notation "! M" := (kcast _ M) (at level 10).

Lemma ksat_ext_p dom b (phi : form b) rho rho' eta eta' (M : @kmodel dom eta ) u :
  (forall v, rho v = rho' v) ->
  (forall p, p el consts phi -> eta p = eta' p) ->
  rho ⊩(u,M,eta) phi <->
  rho' ⊩(u, !M, eta') phi.
Proof.
  intros. revert u rho rho' H; induction phi; cbn in *; intros.
  - destruct (world u). erewrite eval_ext_p with (eta' := eta').
    erewrite eval_ext_p with (eta := eta).
    cbn. reflexivity. all: cbn in *; firstorder.
  - destruct (world u); firstorder.
  - firstorder.
  - split; intros.
    + eapply IHphi2. 3: eapply H1. all: eauto.
      eapply IHphi1; try eassumption; eauto.
    + eapply IHphi2. 3: eapply H1. all: eauto.
      eapply IHphi1; try eassumption; eauto.    
  - firstorder; eapply IHphi. 6:eapply H1. 3:eapply H1. all:firstorder. all:decs.
Qed.
  
Lemma ksat_ext dom b (phi : form b) rho rho' eta (M : @kmodel dom eta ) u :
  rho ⊩(u,M,eta) phi -> (forall v, rho v = rho' v) ->  rho' ⊩(u,M,eta) phi.
Proof.
  intros H1 H2. erewrite ksat_ext_p in *; eauto.
Qed.

Lemma subst_ksat dom b eta rho (M : @kmodel dom eta ) u (phi : form b) x t :
  vars_t t = [] ->
  rho ⊩(u,M,eta) (subst x t phi) <-> rho[[x:=eval (I:=world u) rho t]] ⊩(u,M,eta) phi.
Proof.
  intros Hy. revert u rho.
  induction phi; intros u rho; cbn in *; try rewrite fresh_app in *.
  - now rewrite !subst_eval.
  - reflexivity.
  - reflexivity.
  - split; intros H w H1 H2.
    + erewrite (eval_invar H1). apply IHphi2; eauto.
      apply H, IHphi1; eauto. erewrite <- (eval_invar H1). eassumption.
    + apply IHphi2; eauto. rewrite <- (eval_invar H1).
      apply H. eassumption. rewrite (eval_invar H1). apply IHphi1; eauto.
  - cbn. split.
    + intros H v H1 j. destruct Dec as [->|H'].
      * specialize (H v H1 j). apply (ksat_ext H). intros z. decs.
      * specialize (H v H1 j). apply IHphi in H; eauto.
        rewrite eval_empty with (rho':=rho) in H; trivial.
        apply (ksat_ext H). intros. decs. now rewrite (eval_invar H1).
    + intros H v H1 j. destruct Dec as [->|H'].
      * specialize (H v H1 j). apply (ksat_ext H). intros z. decs.
      * specialize (H v H1 j). apply IHphi; eauto.
        rewrite eval_empty with (rho':=rho); trivial.
        apply (ksat_ext H). intros. decs. now rewrite (eval_invar H1).
Qed.

Lemma substconst_ksat b dom eta rho (phi : form b) x a d (M : @kmodel dom eta) u :
  fresh a (consts phi) ->
  rho ⊩(u, kcast (eta [[a := d]]) M, _) (subst x (P a) phi) <-> 
  rho [[ x := d ]] ⊩(u,M,eta) phi.
Proof.
  intros H. rewrite subst_ksat; trivial.
  symmetry. eapply ksat_ext_p; intros n; repeat decs.
Qed.

(* Arguments ksat {_ _} _ {_} _ _ _. *)

Lemma ksoundness' {b} A (phi : form b) :
  A ⊢I phi -> kvalid (A ==> phi).
Proof.
  remember intu as s.
  induction 1; intros domain eta M u rho; eapply impl_ksat; intros; subst.
  - eauto.
  - intros ? ? ?. apply (impl_ksat' (IHprv eq_refl domain eta M u rho) ). eauto using reach_tran.
    intros ? [-> | ]; eauto. eapply ksat_mon. eauto using reach_tran. eauto.
  - pose proof (impl_ksat' (IHprv1 eq_refl domain eta M u rho)). specialize (H3 v H1).  cbn in H3.
    eapply H3; eauto. eapply (impl_ksat' (IHprv2 eq_refl domain eta M u rho)); eauto.
  - intros w H3 d. specialize (IHprv eq_refl domain _ (kcast (eta [[y := d]]) M) w rho). rewrite impl_ksat in IHprv.
    specialize (IHprv w (reach_refl _)).
    rewrite <- substconst_ksat. apply IHprv. 2: firstorder.
    intros. specialize (H2 _ H4). eapply ksat_iff in H2; eauto.
    rewrite <- ksat_ext_p; eauto. intros. decs. destruct H; firstorder. 
    eapply in_app_iff. right. eapply in_flat_map. eauto.
  - eapply subst_ksat. rewrite H; eauto. pose proof (impl_ksat' (IHprv eq_refl domain eta M u rho)). cbn in H3.
    specialize (H3 v H1 H2 v (reach_refl _)). eapply H3.
  - specialize (IHprv eq_refl domain eta M v rho).
    eapply impl_ksat in IHprv as []; eauto.
  - inv Heqs. 
Qed.

Theorem ksoundness {b} (phi : form b) :
  [] ⊢I phi -> valid phi.
Proof.
  apply soundness'.
Qed.
