Require Import FcEtt.sigs.


Require Import FcEtt.imports.
Require Import FcEtt.tactics.

Require Import FcEtt.ett_ott.
Require Import FcEtt.ett_inf.
Require Import FcEtt.ett_inf_cs.
Require Import FcEtt.ett_ind.


Require Import FcEtt.ett_par.
Require Import FcEtt.ext_invert.
Require Import FcEtt.ext_red.
Require Import FcEtt.ext_red_one.
Require Import FcEtt.erase_syntax.

Require Import FcEtt.fc_invert FcEtt.fc_unique.

Module fc_preservation (wf : fc_wf_sig) (weak : fc_weak_sig) (subst : fc_subst_sig)
        (e_subst : ext_subst_sig).

Import subst weak wf.

Module e_invert := ext_invert e_subst.
Import e_invert.

Module red := ext_red e_invert.
Import red.

Module red_one := ext_red_one e_invert.
Import red_one.

Module invert := fc_invert wf weak subst.
Module unique := fc_unique wf subst.
Import invert unique.


Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.


(* This version is just for "head reduction."
 *)

Lemma open_a_Conv : forall a b g,
    open_tm_wrt_tm (a_Conv a g) b =
    a_Conv (open_tm_wrt_tm a b) (open_co_wrt_tm g b).
intros.
unfold open_tm_wrt_tm. simpl. auto.
Qed.

Lemma open_a_Conv_co : forall a b g,
    open_tm_wrt_co (a_Conv a g) b =
    a_Conv (open_tm_wrt_co a b) (open_co_wrt_co g b).
intros.
unfold open_tm_wrt_co. simpl. auto.
Qed.

(* Helper tactic for below. Solves lc_tm goals using hypotheses from
   the annotated language. Perhaps it is useful elsewhere? *)
Ltac lc_erase_hyp :=
  match goal with
  | H : AnnTyping ?G ?a ?A0 |- lc_tm (erase_tm ?a) => eapply lc_erase; apply (AnnTyping_lc H)
  | H : AnnTyping ?G ?a ?A0 |- lc_tm ?a => apply (AnnTyping_lc1 H)
  | H : lc_tm ?a |- lc_tm (erase ?a) => eapply lc_erase; eauto
  | H : lc_tm (a_Abs ?r ?a ?b) |- lc_tm ?c => apply lc_erase in H; simpl in H; auto
  | H : lc_tm (a_CAbs ?a ?b) |- lc_tm ?c => apply lc_erase in H; simpl in H; auto
  end.


Lemma binds_toplevel: forall F a A,
  binds F (Ax a A) an_toplevel ->
  binds F (Ax (erase a) (erase A)) toplevel.
Proof.
  intros.
  unfold toplevel. unfold erase_sig.
  eapply binds_map with (f:= erase_csort) in H.
  auto.
Qed.


Ltac do_rho :=
  match goal with
    H : ∀ x : atom, x `notin` ?L → RhoCheck Irrel x (erase_tm (open_tm_wrt_tm ?b (a_Var_f x))) |-
                    ?x `notin` fv_tm_tm_tm (open_tm_wrt_tm (erase ?b) (a_Var_f ?x)) =>
    let h := fresh in
    let F := fresh in
    assert (F : x `notin` L); auto;
    move: (H x F) => h; inversion h; subst;
    replace (a_Var_f x) with (erase (a_Var_f x)); auto;
    rewrite open_tm_erase_tm; auto
  end.

(* A specialized version of eauto that only uses the most common
   lc lemmas to cut down the search space. *)
Ltac eauto_lc := simpl; eauto using AnnTyping_lc1, Value_lc,
                        AnnDefEq_lc3, AnnPropWff_lc.


(* We need to know that the term type checks.  But if it does, our annotated
   operational semantics corresponds with reduction_in_one. *)
Lemma head_reduction_in_one : forall G a b,
    head_reduction G a b -> forall A,  AnnTyping G a A ->
    reduction_in_one (erase a) (erase b) \/ erase a = erase b.
Proof.
  move: lc_erase => [lc_er_tm _] G a b H.
  induction H; intros AA TT ; inversion TT; try (simpl; eauto).
  - destruct rho.
    destruct (IHhead_reduction _ H6); subst; simpl.
    left. eauto. simpl in H8. rewrite H8. eauto.
    destruct (IHhead_reduction _ H6); subst; simpl.
    left. eauto. simpl in H8. rewrite H8. eauto.
  - subst. destruct rho; left; simpl_erase.
    ++ eapply E_AppAbs; eauto using lc_er_tm.
       eapply Value_lc in H0. lc_erase_hyp.
    ++ inversion H6; clear H6; subst.
       pose EB := erase w.
       pick fresh x.
       rewrite (tm_subst_tm_tm_intro x); auto using fv_tm_erase_tm.
       rewrite tm_subst_tm_tm_fresh_eq.
       rewrite -(tm_subst_tm_tm_fresh_eq (open_tm_wrt_tm (erase w) (a_Var_f x)) a_Bullet x).
       rewrite -tm_subst_tm_tm_intro; eauto.
       econstructor. auto.
       eapply Value_erase in H0. auto.
       do_rho.
       do_rho. 
  - subst.
    destruct (IHhead_reduction _ H4); simpl.
    eauto.
    simpl in H1. rewrite H1.
    eauto.
  - subst. left. autorewcs.
    erewrite <- open_co_erase_tm2.
    econstructor. apply lc_er_tm in H0. eauto.
  - subst.
    pick fresh x.
    edestruct (H1 x); eauto.
    left. apply E_AbsTerm_exists with (x:=x).
    eauto using fv_tm_erase_tm.
    rewrite <- open_tm_erase_tm in H2.
    rewrite <- open_tm_erase_tm in H2.
    simpl in H2. eauto.
    right. f_equal.
    move: (H9 x ltac:(auto)) => h0. inversion h0. subst.
    rewrite <- open_tm_erase_tm in H2.
    rewrite <- open_tm_erase_tm in H2.
    simpl in H2.
    apply open_tm_wrt_tm_inj in H2.
    auto.
    eauto using fv_tm_erase_tm.
    eauto using fv_tm_erase_tm.
  - left.
    assert (Ax a A = Ax a0 AA).
    { eapply binds_unique; eauto. apply uniq_an_toplevel. } inversion H6. subst.
    apply binds_toplevel in H.
    eauto.
  - subst. destruct rho.
    simpl. eauto.
    simpl. eauto.
Qed.


(* We need to know that the term type checks.  But if it does, our annotated
   operational semantics corresponds with parallel reduction. *)

Lemma head_reduction_erased : forall G a b, head_reduction G a b ->
    forall A, AnnTyping G a A ->  Par G (dom G) (erase a) (erase b).
Proof.
  intros G a b H.
  induction H; intros AA TT ; inversion TT; try (simpl; econstructor; eauto).
  + destruct rho; simpl. econstructor; eauto. econstructor.
    eapply lc_erase. eapply AnnTyping_lc with (A := A). eauto.
    econstructor; eauto.
  + destruct rho; simpl_erase.
    econstructor.
    econstructor. apply Value_lc in H0. lc_erase_hyp.
    econstructor. apply Value_lc in H0. lc_erase_hyp.
    match goal with
      H :  AnnTyping ?G (a_Abs Irrel ?A ?b) (a_Pi Irrel ?A0 ?B) |- _ => inversion H; clear H end. subst.
    pose EB := (erase w).
    pick fresh x.
    rewrite (tm_subst_tm_tm_intro x); auto using fv_tm_erase_tm.
    rewrite tm_subst_tm_tm_fresh_eq.
    rewrite -(tm_subst_tm_tm_fresh_eq (open_tm_wrt_tm (erase w) (a_Var_f x)) a_Bullet x).
    rewrite -tm_subst_tm_tm_intro; eauto.
    econstructor. econstructor. apply Value_lc in H0.
    match goal with H : lc_tm (a_Abs Irrel ?A0 ?b) |-
                    lc_tm (a_UAbs Irrel (erase ?b)) => eapply lc_erase in H; simpl in H; auto end.
    do_rho.
    do_rho.
  + subst. simpl.
    autorewcs. rewrite -(open_co_erase_tm2 _ _ g_Triv).
    econstructor. econstructor. lc_erase_hyp.
  + intros.
    assert (x `notin` L \u L0). eapply H10.
    replace (a_Var_f x) with (erase (a_Var_f x)); auto.
    rewrite open_tm_erase_tm.
    rewrite open_tm_erase_tm.
    eapply context_Par_irrelevance; eauto.
  + unfold toplevel. unfold erase_sig.
    apply binds_map with (f := erase_csort) in H.
    simpl in H.
    eauto.
  + simpl. eauto.
  + match goal with
      H : AnnTyping ?G (a_Conv ?v ?g1) ?A |- lc_tm (erase_tm ?v) =>
      inversion H end.
    lc_erase_hyp.
  + destruct rho; subst; simpl; eauto using lc_erase.
    econstructor. eapply AnnTyping_lc1 in TT. eapply lc_tm_erase in TT. eauto.
    econstructor. eapply AnnTyping_lc1 in TT. eapply lc_tm_erase in TT. eauto.
  + eapply AnnTyping_lc1 in TT. eapply lc_tm_erase in TT. eauto.
Qed.

Lemma preservation : forall G a A, AnnTyping G a A -> forall a', head_reduction G a a' -> AnnTyping G a' A.
Proof.
  intros G a A H. induction H.
  - intros. inversion H0.
  - intros. inversion H1.
  - intros. inversion H2; subst.
  - intros. inversion H3. subst.
    pick fresh x and apply An_Abs; eauto 3.
    have RC: RhoCheck Irrel x (erase_tm (open_tm_wrt_tm a (a_Var_f x))); eauto.
    inversion RC. subst.
    have HR: head_reduction ([(x, Tm A)] ++ G) (open_tm_wrt_tm a (a_Var_f x))
                            (open_tm_wrt_tm b' (a_Var_f x)); eauto.
    have Ta: AnnTyping ([(x, Tm A)] ++ G) (open_tm_wrt_tm b' (a_Var_f x))
                       (open_tm_wrt_tm B (a_Var_f x)); eauto.
    constructor.
    eapply Par_fv_preservation; eauto.
    eapply head_reduction_erased; eauto.
  - (* application case *)
    intros. inversion H1; subst.
    + eauto.
    + inversion H. subst.
      pick fresh x.
      rewrite (tm_subst_tm_tm_intro x); auto.
      rewrite (tm_subst_tm_tm_intro x B); auto.
      eapply AnnTyping_tm_subst; eauto.
    + (* Push case *)
      inversion H. subst. resolve_unique_subst.
      move: (AnnDefEq_regularity H7)  => [C1 [C2 [g' hyps]]]. split_hyp.
      invert_syntactic_equality.
      inversion H2. inversion H6. subst.
      eapply An_Conv; eauto.
      eapply An_PiSnd; eauto.
      eapply An_EraseEq; eauto.
      eapply AnnTyping_tm_subst_nondep; eauto.
  - intros. inversion H2; subst.
    + eauto.
    + inversion H. subst.
      econstructor; eauto 2.
      eapply An_Trans with (a1 := A); eauto 2 using AnnTyping_regularity.
      eapply An_Refl; eauto with ctx_wff.
  - intros. inversion H2.
  - intros. inversion H2.
  - intros. inversion H1; subst.
    + eauto.
    + inversion H; subst.
      pick fresh c.
      rewrite (co_subst_co_tm_intro c); auto.
      rewrite (co_subst_co_tm_intro c B); auto.
      eapply AnnTyping_co_subst; eauto.
    + (* CPush case *)
      inversion H. subst. resolve_unique_subst.
      move: (AnnDefEq_regularity H5)  => [C1 [C2 [g' hyps]]]. split_hyp.
      invert_syntactic_equality.
      inversion H2. inversion H7. subst. destruct phi1.
      eapply An_Conv; eauto.
      eapply AnnTyping_co_subst_nondep; eauto.
  - move=> a' hr.
    inversion hr.
  - move=> a' hr.
    inversion hr. subst.

    assert (Ax a A = Ax a' A0).
    { eapply binds_unique; eauto. apply uniq_an_toplevel. }
    inversion H2. subst. clear H2. clear H0.
    apply an_toplevel_closed in H4.
    eapply AnnTyping_weakening with (F:=nil)(G:=nil)(E:=G) in H4; eauto.
    simpl in H4.
    rewrite app_nil_r in H4.
    auto.
    rewrite app_nil_r. simpl. auto.
Qed. (* preservation *)




End fc_preservation.
