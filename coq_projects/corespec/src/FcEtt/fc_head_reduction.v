Require Import FcEtt.sigs.
Require Import FcEtt.fc_wf.

Module fc_head_reduction (e_invert : ext_invert_sig)
       (wk: fc_weak_sig) (wf : fc_wf_sig) (sub : fc_subst_sig).

Import e_invert.
Import wk.
Import sub.

Require Export FcEtt.imports.
Require Import FcEtt.utils.
Require Export FcEtt.tactics.

Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ind.

Require Export FcEtt.ett_par.
Require Export FcEtt.erase_syntax.

Require Import FcEtt.ext_red_one.
Module red1 := ext_red_one e_invert.
Import red1.

Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".


Lemma weaken_head_reduction : forall G0 a a',
    head_reduction G0 a a' ->
    forall E F G, (G0 = F ++ G) -> AnnCtx (F ++ E ++ G) -> head_reduction (F ++ E ++ G) a a'.
Proof.
  intros G a a' H.
  induction H; pre; subst; eauto 4.


  all: try (pick fresh x and apply An_AbsTerm;
    [eapply AnnTyping_weakening; eauto|
    rewrite_env (([(x, Tm A)] ++ F) ++ E ++ G0); eauto;
    eapply H1; eauto;
    simpl_env; eauto using AnnTyping_weakening]).
  all: try solve [econstructor; eauto;
                  eapply AnnDefEq_weaken_available; eauto;
                  eapply (AnnDefEq_weakening H0 E F G0); eauto].
Qed.



Lemma subst_head_reduction : forall G a a',
    head_reduction G a a' -> forall G1 G2 A b x,
       G = G1 ++ [(x, Tm A)] ++ G2
      -> AnnTyping G2 b A
      -> head_reduction (map (tm_subst_tm_sort b x) G1 ++ G2)
                       (tm_subst_tm_tm b x a)
                       (tm_subst_tm_tm b x a').
Proof.
  intros G a a' R.
  induction R;
    intros G1 G2 A0 b0 x0 EQ Ty;
    simpl; subst; eauto using tm_subst_tm_tm_lc_tm, AnnTyping_lc1, AnnTyping_lc2,
           tm_subst_tm_co_lc_co.
  - have h0: lc_tm b0 by apply AnnTyping_lc1 in Ty.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm; auto.
    apply An_AppAbs; simpl; try apply tm_subst_tm_tm_lc_tm; auto.
    eapply Value_tm_subst_tm_tm in H0; simpl in H0; eauto.
  - have h0: lc_tm b0 by apply AnnTyping_lc1 in Ty.
    rewrite tm_subst_tm_tm_open_tm_wrt_co; auto.
    apply An_CAppCAbs; simpl.
    destruct phi.
    apply tm_subst_tm_constraint_lc_constraint; auto.
    have h1 := tm_subst_tm_tm_lc_tm _ _ x0 H0 h0; auto.
    apply tm_subst_tm_co_lc_co; auto.
  - eapply An_AbsTerm with (L := singleton x0 \u L); eauto.
    + have h0 := first ann_tm_substitution_mutual _ _ _ H; auto.
      simpl in h0.
      eapply h0; eauto.
    + simpl in H1.
      intros x H2.
      have h1 : lc_tm b0 by apply AnnTyping_lc1 in Ty.
      have h0 := H1 x ltac:(auto) ((x, Tm A) :: G1) G2 A0 b0 x0 ltac:(auto) Ty.
      repeat rewrite tm_subst_tm_tm_open_tm_wrt_tm_rec in h0; auto.
      simpl.
      simpl in h0.
      destruct eq_dec; auto.
      fsetdec.
  - eapply An_Axiom; eauto.
    erewrite tm_subst_fresh_2; eauto.
    eapply an_toplevel_closed; eauto.
  - have h1 : lc_tm b0 by apply AnnTyping_lc1 in Ty.
    apply An_Combine; auto.
    all: try apply tm_subst_tm_co_lc_co; auto.
    apply Value_tm_subst_tm_tm; auto.
  - have h1 : lc_tm b0 by apply AnnTyping_lc1 in Ty.
    eapply An_Push; eauto.
    eapply Value_tm_subst_tm_tm; eauto.
    eapply (fourth ann_tm_substitution_mutual) in H0; eauto 2.
    simpl in H0.
    eapply AnnDefEq_weaken_available; eauto.
  - have h1 : lc_tm b0 by apply AnnTyping_lc1 in Ty.
    eapply An_CPush; eauto.
    eapply Value_tm_subst_tm_tm; eauto.
    eapply (fourth ann_tm_substitution_mutual) in H0; eauto 2.
    simpl in H0.
    eapply AnnDefEq_weaken_available; eauto.
Qed.


(* A useful tactic *)
Ltac resolve_open a :=
    let s := fresh in
    match goal with
      [ x1 : ?b = open_tm_wrt_tm a (a_Var_f ?x) |- _ ] =>
      destruct a; inversion x1;
        [unfold open_tm_wrt_tm in x1;
         simpl in x1;
         match goal with [ n:nat |- _ ] =>
                         destruct (lt_eq_lt_dec n 0) as [s | [| s]];
                         try destruct s; inversion x1
         end | subst; unfold open_tm_wrt_tm in x1;
               unfold open_tm_wrt_tm; simpl in *; inversion x1; clear x1]
    end.


Lemma An_AbsTerm_exists : ∀ G x A (a a' : tm),
    x `notin` (fv_tm a \u fv_tm a' \u dom G) ->
    AnnTyping G A a_Star ->
    head_reduction ([(x, Tm A)] ++ G) (open_tm_wrt_tm a (a_Var_f x))
                                      (open_tm_wrt_tm a' (a_Var_f x))
    → head_reduction G (a_Abs Irrel A a) (a_Abs Irrel A a').
Proof.
  intros.
  pick fresh x0 and apply An_AbsTerm.
  auto.
  have AC: (AnnCtx ([(x,Tm A)] ++ G)) by  eauto with ctx_wff.
  intros.
  rewrite (tm_subst_tm_tm_intro x); auto.
  rewrite (tm_subst_tm_tm_intro x a'); auto.
  move: weaken_head_reduction => h.
  eapply h with (F:= [(x,Tm A)])(E := [(x0,Tm A)])(G:=G) in H1.
  eapply subst_head_reduction with
  (G := nil ++ [(x, Tm A)] ++ ([(x0,Tm A)] ++ G))(b := (a_Var_f x0)) (x:=x) in H1; eauto.
  simpl_env in H1. auto.
  econstructor; eauto with ctx_wff.
  auto.
  econstructor; eauto with ctx_wff.
  eapply AnnTyping_weakening with (F:=nil); eauto 4.
  simpl.
  econstructor;
  eauto with ctx_wff.
Qed.



End fc_head_reduction.
