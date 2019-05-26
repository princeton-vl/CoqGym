Require Import FcEtt.sigs.


Require Import FcEtt.imports.
Require Import FcEtt.tactics.
Require Import FcEtt.fset_facts.


Require Import FcEtt.ett_ott.
Require Import FcEtt.ett_inf.
Require Import FcEtt.ett_inf_cs.
Require Import FcEtt.ett_ind.

Require Import FcEtt.erase_syntax.
Require Export Metalib.CoqEqDec.
Require Import Coq.Logic.Decidable.
Require Import Metalib.Metatheory.
Require Import FcEtt.fc_unique.

Require Import FcEtt.fc_wf.
Require Import FcEtt.toplevel.
Require Import FcEtt.fc_context_fv.

Module fc_invert (wf : fc_wf_sig) (weak : fc_weak_sig) (subst : fc_subst_sig).
Import weak subst.

Module unique := fc_unique wf subst.
Import unique.

Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

(* ------------------------------------------------------------- *)

Lemma AnnTyping_regularity :
  (forall G a A, AnnTyping G a A -> AnnTyping G A a_Star).
Proof.
  induction 1; eauto with ctx_wff.
  - eapply binds_to_AnnTyping; eauto.
  - inversion IHAnnTyping1. eapply AnnTyping_tm_subst_nondep; eauto.
  - inversion IHAnnTyping. eapply AnnTyping_co_subst_nondep; eauto.
  - eapply AnnTyping_weakening with (F:=nil)(G:=nil) in H1.
    simpl_env in H1.
    eauto.
    auto.
    simpl_env.
    auto.
  - eapply AnnTyping_weakening with (F:=nil)(G:=nil) in H1;
      simpl_env in H1; simpl_env; eauto.
Qed.

Lemma AnnPropWff_regularity :
  forall G A B A1, AnnPropWff G (Eq A B A1) -> exists B1 g,
      AnnTyping G A A1 /\ AnnTyping G B B1 /\ AnnDefEq G empty g A1 B1.
Proof.
  intros G A B A1 H.
  inversion H. subst.
  pose K := AnnTyping_regularity H4.
  pose L := AnnTyping_regularity H5.
  pose M := AnnTyping_regularity K.
  pose N := AnnTyping_regularity M.
  pose g := g_Refl2 A1 B0 (g_Refl a_Star).
  assert (DE : AnnDefEq G empty g A1 B0). eapply An_EraseEq; eauto.
  exists B0. eexists. eauto.
Qed.


(* -------------------------------------------------------------- *)

(*  Interlude: some lemmas about how erasure and typing interact. *)

(* -------------------------------------------------------------- *)


Lemma erase_pi : forall G AB0 rho A B S, erase AB0 = (a_Pi rho A B) -> AnnTyping G AB0 S ->
  exists A1 B0, erase AB0 = erase (a_Pi rho A1 B0) /\ erase A1 = A /\ erase B0 = B /\ AnnTyping G (a_Pi rho A1 B0) a_Star.
Proof.
  induction AB0; intros rho' A B S H; try solve [try destruct rho; simpl in H; inversion H].
  - simpl in H; inversion H.
    intros. exists AB0_1. exists AB0_2.
    repeat split. inversion H0. subst. auto.
  - simpl in H; inversion H.
    intros H0.  inversion H0. destruct (IHAB0 rho' A B A0 H) as [A2 [B2 [E1 [E2 [E3 AT]]]]]; auto.
    subst.
    exists A2. exists B2. simpl in *. subst. repeat split. auto.
    auto.
Qed.

Lemma erase_cpi : forall AB0 A B G S,
    erase AB0 = (a_CPi A B) -> AnnTyping G AB0 S ->
    exists A1 B0, erase AB0 = erase (a_CPi A1 B0) /\ erase_constraint A1 = A /\ erase B0 = B
             /\ AnnTyping G (a_CPi A1 B0) a_Star.
Proof.
  induction AB0; intros A B G S H; try destruct rho; simpl in H; inversion H.
  - intros J.
    inversion J. subst.
    destruct (IHAB0 A B G A0 H) as [A1 [B0 [E1 [E2 E3]]]]; auto.
    subst.
    exists A1. exists B0. simpl. subst. auto.
  - exists phi. exists AB0. inversion H0. subst.  auto.
Qed.

Lemma erase_app_Rel :
  forall AB0 A B C G, erase AB0 = (a_App A Rel B) -> AnnTyping G AB0 C ->
  exists A1 B0 g D, erase AB0 = erase (a_App A1 Rel B0) /\ erase A1 = A /\ erase B0 = B /\
          AnnTyping G (a_App A1 Rel B0) D /\ AnnDefEq G (dom G) g C D.
Proof.
  induction AB0;
    move=> A B C G H; try destruct rho;
            simpl in H;

    inversion H;
    eauto.
  - intros T.
    pose K := AnnTyping_regularity T.
    eexists. eexists. eexists. eexists.
    repeat split. eauto.  eauto.
  - intros T.
    inversion T. subst.
    destruct (IHAB0 _ _ _ _ H H3) as [A1 [B0 [g1 [D [E1 [E2 [E3 [T1 DE]]]]]]]].
    simpl in E1. inversion E1. subst.
    pose K := AnnTyping_regularity T. clearbody K.
    pose K2 := AnnTyping_regularity T1. clearbody K2.
    pose K3 := AnnTyping_regularity H3. clearbody K3.
    assert (AnnCtx G). eauto using AnnTyping_AnnCtx.
    exists A1, B0. eexists. exists D.
    repeat split. simpl. eauto. eauto.
    eapply An_Trans with (a1 := A0).
    eapply An_Sym; eauto. eauto. eauto. eauto.
    eapply An_Refl. eauto.
Qed.

Lemma erase_app_Irrel :
  forall AB0 A C G, erase AB0 = (a_App A Irrel a_Bullet) -> AnnTyping G AB0 C ->
  exists A1 B0 g D, erase AB0 = erase (a_App A1 Irrel B0) /\ erase A1 = A /\
          AnnTyping G (a_App A1 Irrel B0) D /\ AnnDefEq G (dom G) g C D.
Proof.
  induction AB0;
    move=> A C G H; try destruct rho;
            simpl in H;
    inversion H;
    eauto.
  - intros T.
    pose K := AnnTyping_regularity T.
    eexists. eexists. eexists. eexists.
    repeat split. eauto.  eauto.
  - intros T.
    inversion T. subst.
    destruct (IHAB0 _ _ _  H H3) as [A1 [B0 [g1 [D [E1 [E3 [T1 DE]]]]]]].
    simpl in E1. inversion E1. subst.
    pose K := AnnTyping_regularity T. clearbody K.
    pose K2 := AnnTyping_regularity T1. clearbody K2.
    pose K3 := AnnTyping_regularity H3. clearbody K3.
    assert (AnnCtx G). eauto using AnnTyping_AnnCtx.
    exists A1, B0. eexists. exists D.
    repeat split. simpl. eauto. eauto.
    eapply An_Trans with (a1 := A0).
    eapply An_Sym; eauto. eauto. eauto. eauto.
    eapply An_Refl. eauto.
Qed.


(*
Lemma erase_abs : forall AB0 rho B, erase AB0 = (a_UAbs rho B) ->
  exists A1 B0, erase AB0 = erase (a_Abs rho A1 B0) /\ erase B0 = B.
Proof.
  induction AB0;
    move=> rho' B H;
            try destruct rho;
    simpl in H;
    inversion H;
    eauto.
Qed.
*)
(*
Lemma erase_capp :
  forall AB0 A C G, erase AB0 = (a_CApp A g_Triv) -> AnnTyping G AB0 C ->
  exists A1 g0 g D, erase AB0 = erase (a_CApp A1 g0) /\ erase A1 = A /\
          AnnTyping G (a_CApp A1 g0) D /\ AnnDefEq G (dom G) g C D.
Proof.
  induction AB0;
    move=> A C G H;
    simpl in H;
    inversion H;
    eauto.
  - intros T.
    inversion T. subst.
    destruct (IHAB0 _  _ _ H H3) as [A1 [g0 [g1 [D [E1 [E3 [T1 DE]]]]]]].
    simpl in E1. inversion E1. subst.
    pose K := AnnTyping_regularity T. clearbody K.
    pose K2 := AnnTyping_regularity T1. clearbody K2.
    pose K3 := AnnTyping_regularity H3. clearbody K3.
    assert (AnnCtx G). eauto.
    exists A1, g0. eexists. eexists.
    repeat split. simpl. eauto. eauto. eapply An_Trans with (a1 := A0).
    eapply An_Sym; eauto. eauto. eauto. eauto.
    eapply An_Refl. eauto.
   -  intros T.
    pose K := AnnTyping_regularity T.
    eexists. eexists. eexists. eexists.
    repeat split. eauto.  eauto.
Qed.
*)

(* -------------------------------------------------------------- *)


Lemma erasure_compatible : forall G a A (H1 :AnnTyping G a A),
    forall b B (H2 : AnnTyping G b B)
      (E : erase a = erase b)
      (F : erase A = erase B),
    exists g1, AnnDefEq G (dom G) g1 a b.
Proof.
  intros.
  pose K1 := AnnTyping_regularity H1.
  pose K2 := AnnTyping_regularity H2.
  eexists.
  eapply An_EraseEq.
  eauto. eauto. eauto.
  eapply An_EraseEq; eauto using AnnTyping_AnnCtx.
Qed.


(* ------------------------------------------------------------- *)


(*
    Challenging lemma: coercible terms have coercible types.


     NOTE: this result for AnnDefEq is *not* AnnPropWff G (Eq A B).

 *)
Lemma AnnDefEqAnnIso_regularity :
  (forall G0 a A, AnnTyping G0 a A -> True ) /\
  (forall G0 phi,   AnnPropWff G0 phi -> True ) /\
  (forall G D g p1 p2, AnnIso G D g p1 p2 ->
                 AnnPropWff G p1 /\ AnnPropWff G p2) /\
  (forall G D g A B,   AnnDefEq G D g A B ->
           exists C1 C2 g', AnnTyping G A C1 /\ AnnTyping G B C2 /\ AnnDefEq G (dom G) g' C1 C2) /\
  (forall G0, AnnCtx G0 -> True).
Proof.
  apply ann_typing_wff_iso_defeq_mutual; eauto.
  { intros.
  destruct H as [C1 [C2 [g' [AT1 [AT2 DE]]]]].
  inversion AT1. inversion AT2. subst. split; auto. }
  all: intros.
  - destruct H. eauto.
  - pose K:= binds_to_AnnPropWff _ _ _ _ a0 b0.
    destruct (AnnPropWff_regularity K) as [B1 [g [TA [TB DE]]]].
    exists A, B1, g. split. auto. split. auto. eapply AnnDefEq_weaken_available. eauto.
  - exists A, A, (g_Refl A).
    pose N := AnnTyping_regularity a0.
    eauto.
  - pose N1 := AnnTyping_regularity a0.
    pose N2 := AnnTyping_regularity a1.
    exists A, B. eexists.
    repeat split.
    eauto. eauto. eauto.
  - exists A, B, (g_Sym g1).
    pose K1 := AnnTyping_regularity a0.
    pose K2 := AnnTyping_regularity a1.
    split. auto. split. auto.
    eapply An_Sym. eauto. eauto. eapply An_Refl. eapply An_Star.
    eauto using AnnTyping_AnnCtx.
    eapply AnnDefEq_weaken_available.
    eauto.
  - destruct H as [C1 [D1 [g1' [TbC1 [TaD1 EQ1]]]]]; auto.
    destruct H0 as [C2 [D2 [g2' [TbC2 [TaD2 EQ2]]]]]; auto.
    assert (D1 = C2). eapply AnnTyping_unique; eauto.
    subst.
    exists C1, D2. eexists.
    repeat split. auto. auto.
    eapply An_Trans. eauto. eauto.
    eapply AnnTyping_regularity. eauto.
    eapply AnnTyping_regularity. eauto.
    eapply An_Refl. eapply An_Star. eauto with ctx_wff.
  - exists B0, B1. eexists.
    pose N1 := AnnTyping_regularity a.
    pose N2 := AnnTyping_regularity a0.
    repeat split.
    eauto. eauto.
    eapply An_EraseEq; eauto with ctx_wff.
  - exists a_Star, a_Star. eexists.
    assert (HG : AnnCtx G); eauto with ctx_wff.
  - (* abs cong *)
    clear H1. clear H2. clear H3.

    assert (ANG : AnnCtx G). eauto with ctx_wff.
    pick fresh x1. assert (FR1 : x1 `notin` L). eauto.
    destruct (H0 x1 FR1) as [B1 [B2 [g' [Tb1 [Tb2 EqB1B2]]]]]. clear H0.
    assert (FRB1 : x1 `notin` fv_tm_tm_tm (close_tm_wrt_tm x1 B1)).
    autorewrite with lngen; eauto.
    assert (R1 : AnnTyping G (a_Abs rho A1 b1) (a_Pi rho A1 (close_tm_wrt_tm x1 B1))).
    { eapply (An_Abs_exists); eauto.
      rewrite open_tm_wrt_tm_close_tm_wrt_tm. eauto. }
    pick fresh x2. assert (FR2 : x2 `notin` L). eauto.
    pose N1 := (e x2 FR2). clearbody N1. clear e.
    assert (HSG : AnnDefEq G D (g_Sym g1) A2 A1). {
      assert (AnnDefEq G D (g_Refl a_Star) a_Star a_Star). eauto with ctx_wff.
      eapply An_Sym; eauto with ctx_wff.
      }
    remember (tm_subst_tm_tm (a_Conv (a_Var_f x2) (g_Sym g1)) x1 B2) as B3.
    assert (EQB : open_tm_wrt_tm (close_tm_wrt_tm x2 B3) (a_Var_f x2) =
                  open_tm_wrt_tm (close_tm_wrt_tm x1 B2) (a_Conv (a_Var_f x2) (g_Sym g1))).
    { rewrite HeqB3.
      rewrite (tm_subst_tm_tm_intro x1 (close_tm_wrt_tm x1 B2) (a_Conv (a_Var_f x2) (g_Sym g1))).
      rewrite (open_tm_wrt_tm_close_tm_wrt_tm B2 x1).
      rewrite (open_tm_wrt_tm_close_tm_wrt_tm).
      auto.
      autorewrite with lngen; auto.
    }
    assert (x2 `notin` fv_tm_tm_tm (close_tm_wrt_tm x2 B3)). {
      autorewrite with lngen; auto. }
    assert (R2 : AnnTyping G (a_Abs rho A2 b3) (a_Pi rho A2 (close_tm_wrt_tm x2 B3))).
    { eapply An_Abs_exists with (x := x2). eauto. eauto.
      rewrite N1.
      rewrite EQB.
      rewrite (tm_subst_tm_tm_intro x1); auto.
      rewrite (tm_subst_tm_tm_intro x1 (close_tm_wrt_tm x1 B2)).
      eapply (@AnnTyping_tm_subst ([(x2, Tm A2)] ++ G) x1 A1).
      rewrite open_tm_wrt_tm_close_tm_wrt_tm.
      eapply AnnTyping_weakening; eauto.
      eapply An_ConsTm; eauto with ctx_wff.
      eapply (AnnTyping_weakening a1 _ nil); simpl; eauto.
      eapply An_ConsTm; eauto with ctx_wff.
      eapply An_Conv. eauto.
      eapply AnnDefEq_weaken_available.
      eapply (AnnDefEq_weakening HSG _ nil); simpl; eauto.
      eapply An_ConsTm; eauto.
      eapply (AnnTyping_weakening a1 _ nil); simpl; eauto.
      eapply An_ConsTm; eauto.
      autorewrite with lngen. auto.
      move: (r0 x2 FR2) => r2'. auto.
    }
    exists (a_Pi rho A1 (close_tm_wrt_tm x1 B1)), (a_Pi rho A2 (close_tm_wrt_tm x2 B3)).
    exists (g_PiCong rho g1 (close_co_wrt_tm x1 g') ).
    repeat split. auto. auto.
    eapply An_PiCong_exists with (x1:=x1)(x2:=x2)(B2 := close_tm_wrt_tm x1 B2).
    autorewrite with lngen. auto.
    autorewrite with lngen. auto.
    eapply AnnDefEq_weaken_available. eauto.
    {
      rewrite (open_co_wrt_tm_close_co_wrt_tm g').
      rewrite (open_tm_wrt_tm_close_tm_wrt_tm).
      rewrite (open_tm_wrt_tm_close_tm_wrt_tm).
      eapply AnnDefEq_strengthen_available_tm; eauto.
      assert (x1 `notin` dom G). auto.
      simpl.  clear Fr0. clear Fr.
      fsetdec.
    }
    eauto.
    eapply AnnTyping_regularity. eauto.
    eapply AnnTyping_regularity. eauto.
    destruct (AnnDefEq_context_fv EqB1B2) as (_ & _ & _ & _ & h4 & _).
    simpl in h4.
    autorewrite with lngen.
    clear Fr0. assert (x1 `notin` dom G). auto. clear Fr.
    {
      eapply An_Pi_exists with (x:= x1); eauto 1.
      autorewrite with lngen.
      fsetdec.
      autorewrite with lngen.
      eapply AnnTyping_regularity; eauto.
    }
  - inversion a3.
    inversion a4.
    subst.
    destruct H as [P1 [P2 [g [AT1 [AT2 EP]]]]].
    destruct H0 as [Q1 [Q2 [g' [AU1 [AU2 EP']]]]].
    resolve_unique_subst.
    resolve_unique_subst.
    resolve_unique_subst.
    resolve_unique_subst.
    assert (HG : AnnCtx G); eauto with ctx_wff.
    eexists. eexists. eexists.
    split. eauto. split. eauto.
    eapply AnnDefEq_weaken_available; eauto.
  - destruct H as [C1 [C2 [g' [T1 [T2 E1]]]]].
    inversion T1. inversion T2. subst.
    exists a_Star. exists a_Star. exists (g_Refl a_Star).
    assert (HG : AnnCtx G); eauto with ctx_wff.
  - destruct H as [C1 [C2 [g [T1 [T2 E1]]]]].
    destruct H0 as [C1' [C2' [g' [T12 [T22 E2]]]]].
    inversion T1. inversion T2. subst.
    pick fresh x1. assert (FRL: x1 `notin` L). auto.
    pose N1 := H6 x1 FRL. clearbody N1. clear H6.
    pick fresh x2.
    assert (FRL0 : x2 `notin` L0). auto.
    pose N2 := H13 x2 FRL0. clearbody N2. clear H13.
    exists a_Star. exists a_Star. exists (g_Refl a_Star).
    repeat split.
    move: (AnnTyping_tm_subst N1 a3) => K1.
    simpl in K1.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm in K1; auto.
    rewrite tm_subst_tm_tm_var in K1.
    rewrite tm_subst_tm_tm_fresh_eq in K1; auto.
    apply (AnnTyping_lc a3). clear Fr.
    pose K2 := AnnTyping_tm_subst N2 a4. clearbody K2.
    simpl in K2.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm in K2; auto.
    rewrite tm_subst_tm_tm_var in K2.
    rewrite tm_subst_tm_tm_fresh_eq in K2; auto.
    apply (AnnTyping_lc a4). clear Fr0.
    assert (HG : AnnCtx G); eauto with ctx_wff.
  - exists a_Star. exists a_Star. eexists.
    assert (HG : AnnCtx G); eauto with ctx_wff.
  - (* cabs_cong *)
    exists (a_CPi phi1 B1), (a_CPi phi2 B2).
    exists g4.
    repeat split. auto. auto. auto.
  - clear H2. clear H3.
    destruct H as [C1 [D1 [g [T1 [T2 E1]]]]].
    destruct H0 as [C2 [D2 [g2' [T12 [T22 E2]]]]].
    destruct H1 as [C3 [D3 [g3' [T13 [T23 E3]]]]].
    inversion a5. inversion a6. subst.
    assert ((a_CPi (Eq a9 b A1) B0) = C1). eapply AnnTyping_unique; eauto.
    assert ((a_CPi (Eq a11 b0 A0) B1) = D1). eapply AnnTyping_unique; eauto.
    subst.
    eexists. eexists. eexists.
    eauto.
 -  destruct H as [C1 [D1 [g [T1 [T2 E1]]]]].
    destruct H0 as [C2 [D2 [g2' [T12 [T22 E2]]]]].
    destruct H1 as [C3 [D3 [g3' [T13 [T23 E3]]]]].
    inversion T1. inversion T2. subst.
    exists a_Star. exists a_Star. eexists.
    repeat split.
    eapply AnnTyping_co_subst_nondep; eauto.
    eapply AnnTyping_co_subst_nondep; eauto.
    eauto.
 - destruct H as [C1 [D1 [g [T1 [T2 E1]]]]].
   destruct H0 as [WF1 WF2].
   inversion WF1. inversion WF2.
   subst.
   assert (HG : AnnCtx G); eauto with ctx_wff.
   assert (U1 : AnnTyping G B a_Star). eapply AnnTyping_regularity; eauto.
   assert (U2 : AnnTyping G B1 a_Star). eapply AnnTyping_regularity; eauto.
   eexists. eexists. eexists.
   split. eauto. split.  eauto.
   eapply An_EraseEq; eauto.
 - split_hyp.
   inversion H. inversion H0. subst.
   assert (HG : AnnCtx G); eauto with ctx_wff.
   assert (U1 : AnnTyping G A a_Star). eapply AnnTyping_regularity; eauto.
   assert (U2 : AnnTyping G B a_Star). eapply AnnTyping_regularity; eauto.
   eexists. eexists. eexists.
   repeat split; eauto 1.
   eapply An_Refl; eauto 1.
   eapply An_Star. eauto.
 - assert (HG : AnnCtx G); eauto with ctx_wff.
   assert (U1 : AnnTyping G (a_Pi rho A B) a_Star).
   eapply AnnTyping_regularity; eauto.
   inversion U1.
   exists (a_Pi rho A B), (a_Pi rho A B). eexists.
   repeat split; eauto 1.
   pick fresh x and apply An_Abs; auto.
   + rewrite e; eauto. econstructor.
   eapply AnnTyping_weakening with (F:=nil); simpl; eauto.
   econstructor; eauto.
   econstructor; eauto.
   + rewrite e; eauto.
   destruct rho. econstructor; eauto. econstructor; eauto.
   simpl. autorewcs. apply union_notin_iff. split. 
   eapply fv_tm_erase_tm. auto. auto.
(*   rewrite e; eauto.
   econstructor. eapply lc_erase. eauto using AnnTyping_lc1. *)
   + eapply An_Refl. eauto.
 - assert (HG : AnnCtx G); eauto with ctx_wff.
   assert (U1 : AnnTyping G (a_CPi phi B) a_Star).
   eapply AnnTyping_regularity; eauto.
   inversion U1. subst.
   exists (a_CPi phi B), (a_CPi phi B). eexists.
   repeat split; eauto 1. 
   pick fresh x and apply An_CAbs; auto.
   inversion H3; subst.
   + rewrite e; eauto. econstructor. 
     eapply AnnTyping_weakening with (F:=nil); simpl; eauto.
     econstructor; eauto. econstructor; eauto. 
   + eapply An_Refl. eauto.
 (* Left/Right
 -  exists (a_Pi rho A B), (a_Pi rho A' B'), g2. repeat split; eauto 1.
 -  exists A, A'. eexists.  repeat split; eauto 1.
    eapply An_PiFst. eauto.
 - exists (a_CPi (Eq a1 a2 A0) B), (a_CPi (Eq a1' a2' A0') B'), g2. repeat split; eauto 1. *)
Qed.


Definition  AnnDefEq_regularity :
    (forall G D g A B,   AnnDefEq G D g A B ->
                    exists C1 C2 g', AnnTyping G A C1 /\ AnnTyping G B C2
                                /\ AnnDefEq G (dom G) g' C1 C2) :=
  fourth AnnDefEqAnnIso_regularity.


Definition AnnIso_regularity :
  forall G D g phi1 phi2, AnnIso G D g phi1 phi2 ->
                     AnnPropWff G phi1 /\ AnnPropWff G phi2 :=
  third AnnDefEqAnnIso_regularity.


(* --------------------------------------------------------- *)

(* Smart constructors for the annotated language *)

  Lemma An_Sym2
    : ∀ (G : context) (D : available_props) (g : co) (a b : tm),
      AnnDefEq G D g b a → AnnDefEq G D (g_Sym g) a b.
  Proof.
    intros.
    destruct (AnnDefEq_regularity H) as [A1 [A2 [g3 [T1 [T2 DE]]]]].
    eapply An_Sym ; eassumption.
  Qed.


Lemma An_Trans2
     : ∀ (G : context) (D : available_props) (g1 g2 : co)
       (a b a1 : tm),
       AnnDefEq G D g1 a a1
       → AnnDefEq G D g2 a1 b
       → AnnDefEq G D (g_Trans g1 g2) a b .
Proof.
  intros.
  destruct (AnnDefEq_regularity H) as [A1 [A2 [g3 [T1 [T2 DE]]]]].
    eapply An_Trans; eassumption.
Qed.


(* ---------------------------------------------- *)


Lemma erase_a_Const : forall G0 a0 A0 A1 T,
       erase a0 = a_Const T ->
       binds T (Cs A1) an_toplevel ->
       AnnTyping G0 a0 A0   ->
       exists g, AnnDefEq G0 (dom G0) g A0 A1.
   Proof.
     intros. dependent induction H1.
     all: try destruct rho; simpl in H; try done.
     + move: (IHAnnTyping1 H) => [? ?].
       eexists. eapply An_Trans2 with (a1 := A).
       eapply An_Sym2. eassumption.
       eassumption.
     + inversion H. subst.
       move: (binds_unique _ _ _ _ _ H0 H2 uniq_an_toplevel) => EQ. inversion EQ.
       subst.
       eexists. eapply An_Refl.
       move: (AnnTyping_weakening H3 G nil nil eq_refl) => h0.
       simpl_env in h0.
       eauto.
   Qed.


Lemma erase_capp :
  forall AB0 C G, AnnTyping G AB0 C -> forall A, erase AB0 = (a_CApp A g_Triv) ->
  exists a1 g0 g D, erase AB0 = erase (a_CApp a1 g0) /\ erase a1 = A /\
          AnnTyping G (a_CApp a1 g0) D /\ AnnDefEq G (dom G) g C D.
Proof.
  induction 1; intros a0 EQ; try destruct rho; inversion EQ; subst.
  - move: (IHAnnTyping1 _ H3) => [A1 [g0 [g1 [D hyp]]]]. split_hyp.
    subst.
    ann_invert_clear.
    exists A1.
    exists g0.
    eexists.
    eexists.
    repeat split.
    + simpl. simpl in *.  auto.
    + eapply An_CApp. eassumption. auto.
    + eapply An_Trans2 with (a1 := A). eapply An_Sym2; eauto.
      eauto.
  - exists a1. exists g. eexists. eexists.
    repeat split. eauto.
    eapply An_Refl.
    move: (AnnTyping_regularity H) => h0. inversion h0. subst.
    eapply AnnTyping_co_subst_nondep. eauto. eauto.
Qed.



Lemma An_AppCong2 : ∀ (G : context) (D : available_props) rho (g1 g2 : co)
       (a1 a2 b1 b2 A B : tm),
       AnnDefEq G D g1 a1 b1
       → AnnDefEq G D g2 a2 b2
         → AnnTyping G (a_App a1 rho a2) A
           → AnnTyping G (a_App b1 rho b2) B
           → AnnDefEq G D (g_AppCong g1 rho g2) (a_App a1 rho a2) (a_App b1 rho b2).
Proof.
  intros.
  assert (TMP: exists g3, AnnDefEq G (dom G) g3 A B).
  { destruct (AnnDefEq_regularity H) as (A1 & B1 & g4 & T1 & T2 & DE).
    destruct (AnnDefEq_regularity H0) as (A2 & B2 & g5 & T3 & T4 & DE2).
    inversion H1.
    inversion H2.
    resolve_unique_subst.
    resolve_unique_subst.
    resolve_unique_subst.
    resolve_unique_subst.
    eexists.
    eapply An_PiSnd; eauto 2. eapply AnnDefEq_weaken_available; eauto 1.
  } destruct TMP as [g3 EQ].
  eapply An_AppCong; eauto 1.
Qed.

(* ---------------------------------------------- *)

Lemma An_CAppCong2 :
      ∀ (G : context) (D : available_props) (g1 g2 g3 : co) (a1 b1 a2 b2 a3 b3 A B : tm),
       AnnDefEq G D g1 a1 b1
       → AnnDefEq G (dom G) g2 a2 b2
       → AnnDefEq G (dom G) g3 a3 b3
       → AnnTyping G (a_CApp a1 g2) A
       → AnnTyping G (a_CApp b1 g3) B
       → AnnDefEq G D (g_CAppCong g1 g2 g3) (a_CApp a1 g2) (a_CApp b1 g3).
Proof.
  intros.
  assert (TMP : exists g4, AnnDefEq G (dom G) g4 A B).
  {
    destruct (AnnDefEq_regularity H) as (A1 & B1 & g4 & T1 & T2 & DE).
    inversion H2.
    inversion H3.
    resolve_unique_subst.
    resolve_unique_subst.
    resolve_unique_subst.
    resolve_unique_subst.
    eexists.
    eapply An_CPiSnd; eauto 2.
  } destruct TMP as [g4 EQ].
  eapply An_CAppCong; eauto 1.
Qed.

Lemma An_Trans'
     : ∀ (G : context) (D : available_props) (g1 g2 : co)
       (a b a1 : tm),
       AnnDefEq G D g1 a a1
       → AnnDefEq G D g2 a1 b
       → exists g, AnnDefEq G D g a b .
Proof.
  intros.
  destruct (AnnDefEq_regularity H) as [A1 [A2 [g3 [T1 [T2 DE]]]]].
  eexists.
  eapply An_Trans; eassumption.
Qed.

Lemma An_Sym'
   : ∀ (G : context) (D : available_props) (g : co) (a b : tm),
       AnnDefEq G D g b a → exists g, AnnDefEq G D g a b.
Proof.
  intros.
  destruct (AnnDefEq_regularity H) as [A1 [A2 [g3 [T1 [T2 DE]]]]].
  eexists.
  eapply An_Sym ; eassumption.
Qed.

Lemma An_Refl_Star : forall G D a b A,
     erase a = erase b -> AnnTyping G b a_Star ->
     AnnTyping G a A -> erase A = a_Star ->
     exists g, AnnDefEq G D g a b.
  Proof.
    intros.
    eexists.
    eapply An_EraseEq. eauto. eauto. eauto.
    eapply An_EraseEq. eapply AnnTyping_regularity. eauto.
    eapply An_Star. eauto with ctx_wff.
    eauto. eapply An_Refl. eapply An_Star.
    eauto with ctx_wff.
  Qed.


Lemma An_IsoRefl2_derivable  : ∀ (G : context) (D : available_props) (phi1 phi2 : constraint),
       AnnPropWff G phi1
       → AnnPropWff G phi2
       → erase_constraint phi1 = erase_constraint phi2 →
       exists g,
       AnnIso G D g phi1 phi2.
Proof.
  intros G D phi1 phi2 H H0 H1.
  destruct phi1 as [a1 b1 A1].
  destruct phi2 as [a2 b2 B2].
  assert (AnnCtx G). eauto 2 with ctx_wff.
  inversion H. inversion H0. simpl in H1. inversion H1. clear H1. subst.
  eexists.
  eapply An_IsoConv; eauto 1.
  eapply An_EraseEq; eauto 1.
  eapply AnnTyping_regularity; eauto 1.
  eapply AnnTyping_regularity; eauto 1.
  eapply An_Refl; eauto.
Qed.


Lemma An_Pi_exists2
     : ∀ (x : atom) (G : list (atom * sort)) (rho : relflag) (A B : tm),
       x `notin` union (dom G) (fv_tm_tm_tm B)
       → AnnTyping ([(x, Tm A)] ++ G) (open_tm_wrt_tm B (a_Var_f x)) a_Star
       → AnnTyping G (a_Pi rho A B) a_Star.
Proof.
  intros.
  eapply An_Pi_exists; eauto.
  sort_inversion.
Qed.

Lemma An_Abs_exists2
  : ∀ (x : atom) (G : context) (rho : relflag) (A a B : tm),
    x `notin` union (dom G) (union (fv_tm_tm_tm a) (fv_tm_tm_tm B))
    → AnnTyping ([(x, Tm A)] ++ G) (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x))
    → RhoCheck rho x (erase_tm (open_tm_wrt_tm a (a_Var_f x)))
    → AnnTyping G (a_Abs rho A a) (a_Pi rho A B).
Proof.
  intros.
  eapply An_Abs_exists; eauto.
  sort_inversion.
Qed.

Lemma An_CPi_exists2
  : ∀ (c : atom) (G : context) (phi : constraint) (B : tm),
       c `notin` union (dom G) (fv_co_co_tm B)
       → AnnTyping ([(c, Co phi)] ++ G) (open_tm_wrt_co B (g_Var_f c)) a_Star
       → AnnTyping G (a_CPi phi B) a_Star.
Proof.
  intros.
  eapply An_CPi_exists; eauto.
  sort_inversion.
Qed.


Lemma An_CAbs_exists2
   : ∀ (c : atom) (G : context) (phi : constraint) (a B : tm),
       c `notin` union (dom G) (union (fv_co_co_tm a) (fv_co_co_tm B))
       → AnnTyping ([(c, Co phi)] ++ G) (open_tm_wrt_co a (g_Var_f c)) (open_tm_wrt_co B (g_Var_f c))
       → AnnTyping G (a_CAbs phi a) (a_CPi phi B).
Proof.
  intros.
  eapply An_CAbs_exists; eauto.
  sort_inversion.
Qed.

Lemma An_Fam2 :  ∀ (G : context) (F : tyfam) (A a : tm),
       AnnCtx G
       → binds F (Ax a A) an_toplevel
       → AnnTyping G (a_Fam F) A.
Proof.
  intros.
  eapply An_Fam.
  eauto. eauto.
  move: (an_toplevel_closed H0) => h0.
  move: (AnnTyping_regularity h0) => h1.
  eauto.
Qed.

Lemma An_AbsCong_exists2
      : ∀ (x1 x2 : atom) (G : context) (D : available_props) (rho : relflag) (g1 g2 : co)
        (A1 b1 A2 b3 b2 B : tm),
        x1 `notin` union (dom G) (union (fv_tm_tm_tm b1) (union (fv_tm_tm_tm b2) (fv_tm_tm_co g2)))
        → x2 `notin` union (dom G) (union (fv_tm_tm_tm b2) (union (fv_tm_tm_tm b3) (fv_tm_tm_co g1)))
          → AnnDefEq G D g1 A1 A2
            → AnnDefEq ([(x1, Tm A1)]++ G) D (open_co_wrt_tm g2 (a_Var_f x1))
                (open_tm_wrt_tm b1 (a_Var_f x1)) (open_tm_wrt_tm b2 (a_Var_f x1))
              → open_tm_wrt_tm b3 (a_Var_f x2) = open_tm_wrt_tm b2 (a_Conv (a_Var_f x2) (g_Sym g1))
                  → AnnTyping G A2 a_Star
                    → RhoCheck rho x1 (erase_tm (open_tm_wrt_tm b1 (a_Var_f x1)))
                      → RhoCheck rho x2 (erase_tm (open_tm_wrt_tm b3 (a_Var_f x2)))
                        → AnnTyping G (a_Abs rho A1 b2) B
                          → AnnDefEq G D (g_AbsCong rho g1 g2) (a_Abs rho A1 b1) (a_Abs rho A2 b3).
 Proof.
   intros. eapply An_AbsCong_exists; eauto.
   inversion H7. auto.
 Qed.

 Lemma An_CPiCong_exists2
      : ∀ (c : atom) (G : context) (D : available_props)
        (g1 g3 : co) (phi1 : constraint) (B1 : tm)
        (phi2 : constraint) (B3 B2 : tm),
        AnnIso G D g1 phi1 phi2
        → c
          `notin` (union (dom G)
                   (union D
                    (union (fv_co_co_tm B2)
                       (union (fv_co_co_tm B1)
                          (union (fv_co_co_co g3)
                              (union (fv_co_co_co g1)
                                     (fv_co_co_tm B3)))))))
          → AnnDefEq ([(c, Co phi1)] ++ G) D
                     (open_co_wrt_co g3 (g_Var_f c))
                     (open_tm_wrt_co B1 (g_Var_f c))
                     (open_tm_wrt_co B2 (g_Var_f c))
          → open_tm_wrt_co B3 (g_Var_f c) =
            open_tm_wrt_co B2 (g_Cast (g_Var_f c) (g_Sym g1))
          → AnnTyping G (a_CPi phi1 B1) a_Star
          → AnnTyping G (a_CPi phi1 B2) a_Star
          → AnnDefEq G D (g_CPiCong g1 g3) (a_CPi phi1 B1) (a_CPi phi2 B3).
 Proof.
   intros. eapply An_CPiCong_exists with (B1 := B1) (B2 := B2) (B3:= B3); eauto.
   eapply An_CPi_exists2 with (c:= c).
   fsetdec.
   rewrite H2.
   move: (AnnIso_regularity H) => [h0 h1].
   move: (AnnIso_AnnCtx H) => h2.
   destruct phi1 as [a1 b1 A1].
   destruct phi2 as [a2 b2 A2].
   inversion h1. subst.
   inversion H4. subst.
   eapply AnnTyping_co_subst_nondep with (D := dom ([(c, Co (Eq a2 b2 A2))] ++ G))(L := L \u {{c}} \u dom G).
   eapply An_Cast.
   eapply An_Assn.
   eauto.
   eauto.
   simpl. eauto.
   eapply An_IsoSym.
   eapply AnnIso_weakening with (F := nil); simpl; eauto using AnnIso_weaken_available.
   eapply (third ann_weaken_available_mutual).
   eapply AnnIso_weaken_available. eauto. eauto.
   econstructor; eauto.
   intros c1 Fr.
   move: (H12 c1 ltac:(auto)) => h3.
   eapply AnnTyping_weakening with (F:= (c1 ~ Co (Eq a1 b1 A1))); eauto.
   econstructor; eauto.
   eapply AnnPropWff_weakening with (F:=nil); eauto.
   simpl. econstructor; eauto.
 Qed.



(* Left/Right
  Lemma An_Left2 :
      ∀ (G : context) (D : available_props) (g1 g2 : co)
       (a a' : tm) (T : ett_ott.const) (rho : relflag)
       (A B A' B' b b' : tm),
       Path T a
       → Path T a'
       → AnnTyping G a (a_Pi rho A B)
       → AnnTyping G a' (a_Pi rho A' B')
       → AnnDefEq G D g1 (a_App a rho b) (a_App a' rho b')
       → AnnDefEq G (dom G) g2 (a_Pi rho A B) (a_Pi rho A' B')
       → AnnDefEq G D (g_Left g1 g2) a a'.
  Proof.
    intros.
    move: (AnnDefEq_regularity H3) => [s1 [s2 [g4 hyp]]]. split_hyp.
    ann_invert_clear.
    ann_invert_clear.
    resolve_unique_subst.
    resolve_unique_subst.
    invert_syntactic_equality.
    eapply An_Left with (b:=b)(b':=b'); try eassumption.
  Qed.


  Lemma An_Right2 : ∀ (G : context) (D : available_props) (g1 g2 : co) (b b' : tm) (T : ett_ott.const) (a a' : tm) (A A' B B' : tm),
      Path T a
      → Path T a'
      → AnnTyping G a (a_Pi Rel A B)
      → AnnTyping G a' (a_Pi Rel A' B')
      → AnnDefEq G D g1 (a_App a Rel b) (a_App a' Rel b')
      → AnnDefEq G (dom G) g2 (a_Pi Rel A B) (a_Pi Rel A' B')
      → AnnDefEq G D (g_Right g1 g2) b b'.
  Proof.
    intros.
    move: (AnnDefEq_regularity H3) => [T1 [T2 [g hyp]]]. split_hyp.
    ann_invert_clear.
    ann_invert_clear.
    resolve_unique_subst.
    resolve_unique_subst.
    invert_syntactic_equality.
    eapply An_Right with (a:=a)(a':=a'); try eassumption.
  Qed.

  Lemma An_CLeft2 : ∀ (G : context) (D : available_props) (g1 g2 : co) (a a' : tm)
                      (T : const) phi B phi' B'
                      (g g': co),
      Path T a
      → Path T a'
      → AnnTyping G a (a_CPi phi B)
      → AnnTyping G a' (a_CPi phi' B')
      → AnnDefEq G D g1 (a_CApp a g) (a_CApp a' g')
      → AnnDefEq G (dom G) g2 (a_CPi phi B) (a_CPi phi' B')
      → AnnDefEq G D (g_Left g1 g2) a a'.
  Proof.
    intros.
    move: (AnnDefEq_regularity H3) => [T1 [T2 [s hyp]]]. split_hyp.
    inversion H5. inversion H6. subst.
    destruct phi as [a1 a2 A]. destruct phi' as [a1' a2' A'].
    resolve_unique_subst.
    resolve_unique_subst.
    inversion H8.
    inversion H9.
    subst.
    eapply An_CLeft with (g := g)(g':=g')(a1 := a0)(a2:=b)(A0:=A1)(a1':=a3)(a2':=b0)(A0':=A0); try eassumption.
  Qed.
*)

End fc_invert.
