(** * Weakening *)

Require Import Deduction.

Fixpoint ren_t (rho : nat -> nat) t :=
  match t with
  | V n => V n
  | P p => P (rho p)           
  | t_f b t => t_f b (ren_t rho t)
  | t_e => t_e
  end.

Fixpoint ren {b : logic} (rho : nat -> nat) phi :=
  match phi with
  | Pr s t => Pr (ren_t rho s) (ren_t rho t)
  | Q => Q
  | Fal => Fal
  | Impl phi1 phi2 => Impl (ren rho phi1) (ren rho phi2)
  | All x phi => All x (ren rho phi)
  end.

Lemma vars_t_ren rho t :
  vars_t (ren_t rho t) = vars_t t.
Proof.
  induction t; cbn; congruence.
Qed.

Definition singles (y z x : nat) := if Dec (x = y) then z else x.
Notation "x :-> y" := (singles x y) (at level 20).


Definition ren_ctx {b : logic} f := map (ren f).

Definition fun_comp {X Y Z} (f : Y -> Z) (g : X -> Y) x := f (g x).
Notation "f ∘ g" := (fun_comp f g) (at level 20).

Arguments fun_comp : simpl nomatch.

(**  Renamings and identity *)

Lemma ren_id_t t :
  ren_t (fun x => x) t = t.
Proof.
  induction t; cbn; try congruence.
Qed.

Lemma ren_id {b : logic} t :
  ren (fun x => x) t = t.
Proof.
  induction t; cbn; try congruence.
  now rewrite !ren_id_t.
Qed.

Lemma ren_ctx_id {b : logic} A :
  ren_ctx (fun x => x) A = A.
Proof.
  induction A; cbn; trivial. now rewrite IHA, ren_id.
Qed.

(** Renamings and composition *)

Lemma ren_comp_t rho1 rho2 t :
  ren_t rho1 (ren_t rho2 t) = ren_t (rho1 ∘ rho2) t.
Proof.
  induction t; cbn; now try congruence.
Qed.

Lemma ren_comp {b : logic} rho1 rho2 phi :
  ren rho1 (ren rho2 phi) = ren (rho1 ∘ rho2) phi.
Proof.
  induction phi; cbn; try congruence.
  now rewrite !ren_comp_t.
Qed.

Lemma ren_comp_ctx {b : logic}  rho1 rho2 A :
  ren_ctx rho1 (ren_ctx rho2 A) = ren_ctx (rho1 ∘ rho2) A.
Proof.
  induction A; cbn; try rewrite ren_comp; congruence.
Qed.

(** Renamings are extensional *)

Lemma ren_ext_t t rho1 rho2 :
  (forall p, p el consts_t t -> rho1 p = rho2 p) ->
  ren_t rho1 t = ren_t rho2 t.
Proof.
  intros; induction t; cbn in *; try congruence.
  - rewrite H; eauto.
  - rewrite IHt; eauto.
Qed.

Lemma ren_ext {b : logic} phi rho1 rho2 :
  (forall p, p el consts phi -> rho1 p = rho2 p) ->
  ren rho1 phi = ren rho2 phi.
Proof.
  intros; induction phi; cbn in *; try congruence.
  - f_equal; erewrite ren_ext_t; eauto.
  - rewrite IHphi1, IHphi2; eauto.
  - rewrite IHphi; eauto.
Qed.

Lemma ren_ext_ctx {b : logic} B rho1 rho2 :
  (forall p, p el consts_l B -> rho1 p = rho2 p) ->
  ren_ctx rho1 B = ren_ctx rho2 B.
Proof.
  intros. eapply map_ext_in; intros. eapply ren_ext.
  intros. eapply H. eapply in_flat_map. eauto.
Qed.

(** Renaming and substitution *)

Lemma ren_subst_t {b : logic} rho x t s :
  ren_t rho (subst_t x t s) = subst_t x (ren_t rho t) (ren_t rho s).
Proof.
  intros. induction s; cbn in *; try congruence.
  - dec; cbn.
    + reflexivity.
    + firstorder.
Qed.

Lemma ren_subst {b : logic} rho x t phi : vars_t t = [] ->
  ren rho (subst x t phi) = subst x (ren_t rho t) (ren rho phi).
Proof.
  intros H. induction phi; cbn; intros; try congruence.
  - erewrite <- !ren_subst_t. reflexivity. all:eauto.
  - f_equal. decs.
Qed.

Lemma ren_swap_ctx {b : logic} x y rho B : fresh x (consts_l B) ->
  ren_ctx (rho[[x := rho y]] ∘ (y :-> x)) B = ren_ctx rho B.
Proof.
  intros. eapply ren_ext_ctx. intros.
  unfold singles, update, fun_comp. decs. 
Qed.

(** Weakening *)

Theorem gen_weakening {s : nd} {b : logic} A phi : 
  A ⊢ phi -> forall rho B, A <<= B -> ren_ctx rho B ⊢ ren rho phi.
Proof.
  induction 1; cbn in *; intros.
  - eapply Ctx. eapply in_map_iff. eauto.
  - eapply ImpI. eapply (IHprv rho (phi1 :: B)); eauto. 
  - eapply ImpE; eauto.
  - destruct (make_fresh (rho y :: y :: x :: consts phi ++ consts_l B ++ consts (ren rho phi) ++ consts_l (ren_ctx rho B))) as [z Hz].
    eapply AllI with (y0 := z). intros [] % in_app_iff; eapply Hz; eauto 10.
    rewrite <- ren_swap_ctx with (x0 := z) (y0 := y). 2: intros ?; eapply Hz; eauto 10.
    pose ( B0 := ren_ctx (y :-> z) B).
    pose (rho0 := rho[[z := rho y]][[y := z]]).
    assert (ren_ctx ((rho [[z := rho y]]) ∘ (y :-> z)) B = ren_ctx rho0 B0) as ->. {
     unfold rho0, B0.  rewrite ren_comp_ctx. eapply ren_ext_ctx. unfold update, singles, fun_comp. intros ?. decs. all:firstorder.
    }
    assert (subst x (P z) (ren rho phi) = ren rho0 (subst x (P y) phi)) as ->. {
      rewrite ren_subst. 2: now cbn. unfold rho0. cbn.
      unfold update at 1. dec; try tauto; subst.
      f_equal. eapply ren_ext; eauto. intros ? ?. decs. destruct H. firstorder. destruct Hz. firstorder.
    }
    eapply IHprv.
    intros ? ?. eapply in_map_iff. exists a. split; eauto.
    rewrite <- ren_id. eapply ren_ext. intros. unfold singles; decs.
    destruct H. eapply in_app_iff. right. eapply in_flat_map. eauto.
  - rewrite ren_subst. eapply AllE; eauto. 2:eauto. now rewrite vars_t_ren.
  - eapply Exp; eauto.
  - eapply DN; eauto.
Qed.

Corollary Weak {s : nd} {b : logic} A B phi :
  A ⊢ phi -> A <<= B -> B ⊢ phi.
Proof.
  intros H1 H2. specialize (gen_weakening H1 (fun n => n) H2).
  now rewrite ren_id, ren_ctx_id.
Qed.

(** Inclusion of intuitionistic in classical deduction *)

Lemma ND_CND A (phi : form frag) :
  A ⊢M phi -> A ⊢C phi.
Proof.
  induction 1; eauto.
  eapply DN. eapply ImpI. eapply Weak; eauto.
Qed.
