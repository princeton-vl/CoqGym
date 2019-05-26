Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Require Export FcEtt.tactics.
Require Export FcEtt.imports.
Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_ind.

Require Export FcEtt.ext_context_fv.

Require Import FcEtt.ext_wf.
Import ext_wf.

Require Import FcEtt.fc_wf.
Import fc_wf.

Require Import FcEtt.utils.
Require Import FcEtt.erase_syntax.
Require Export FcEtt.toplevel.
Require Import FcEtt.ett_value.

(** comment *) 
Lemma Beta_lc1 : forall a a' , Beta a a' -> lc_tm a.
  intros.  induction H; auto.
  eapply Value_lc in H. eauto.
Qed.

Lemma Beta_lc2 : forall a a' , Beta a a' -> lc_tm a'.
intros.  induction H; auto.
- inversion H. apply lc_body_tm_wrt_tm; auto.
- apply Value_lc in H. inversion H.
  apply lc_body_tm_wrt_tm; auto.
- inversion H. apply lc_body_tm_wrt_co; auto.
- apply Toplevel_lc in H. inversion H. auto.
Qed.

Lemma cf : forall A B (f : A -> B) (a b : A),  a = b -> f a = f b.
  intros. f_equal.
  auto.
Qed.
Lemma Beta_tm_subst : forall a a' b x, Beta a a' -> lc_tm b -> Beta (tm_subst_tm_tm b x a) (tm_subst_tm_tm b x a').
Proof.
  intros.
  destruct H.
  - simpl.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm; eauto 2.
    econstructor; eauto using tm_subst_tm_tm_lc_tm.
    apply tm_subst_tm_tm_lc_tm with (a2 := b) (x1:=x) in H; auto.
  - simpl.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm; eauto 2.
    econstructor; eauto using tm_subst_tm_tm_lc_tm.
    eapply Value_tm_subst_tm_tm in H; eauto.
  - simpl.
    rewrite tm_subst_tm_tm_open_tm_wrt_co; eauto 2.
    simpl.
    econstructor.
    apply tm_subst_tm_tm_lc_tm with (a2 := b) (x1:=x) in H; auto.
  - move: (toplevel_closed H) => h.
    simpl.
    rewrite tm_subst_tm_tm_fresh_eq. eauto.
    move: (first context_fv_mutual _ _ _ h) => Fr. simpl in Fr.
    fsetdec.
Qed.

Lemma Beta_co_subst : forall a a' b x, Beta a a' -> lc_co b -> Beta (co_subst_co_tm b x a) (co_subst_co_tm b x a').
Proof.
  intros.
  destruct H.
  - simpl.
    rewrite co_subst_co_tm_open_tm_wrt_tm; eauto 2.
    econstructor; eauto using co_subst_co_tm_lc_tm.
    apply co_subst_co_tm_lc_tm with (g1 := b) (c1:=x) in H; auto.
  - simpl.
    rewrite co_subst_co_tm_open_tm_wrt_tm; eauto 2.
    econstructor; eauto using co_subst_co_tm_lc_tm.
    eapply Value_co_subst_co_tm in H; eauto.
  - simpl.
    rewrite co_subst_co_tm_open_tm_wrt_co; eauto 2.
    simpl.
    econstructor.
    apply co_subst_co_tm_lc_tm with (g1 := b) (c1:=x) in H; auto.
  - move: (toplevel_closed H) => h.
    simpl.
    rewrite co_subst_co_tm_fresh_eq. eauto.
    move: (first context_fv_mutual _ _ _ h) => Fr. simpl in Fr.
    fsetdec.
Qed.
