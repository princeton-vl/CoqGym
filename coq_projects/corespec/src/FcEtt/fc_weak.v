Require Import FcEtt.sigs.
Require Export FcEtt.imports.
Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ind.

Require Import FcEtt.tactics.
Require Import FcEtt.ett_par.

Require Import FcEtt.erase_syntax.

Require Export FcEtt.fc_wf.

(* can remove this parameter *)
Module fc_weak (wf : fc_wf_sig) <: fc_weak_sig.


Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

(* Weakening *)

(* ------------------------------------------------------------------- *)


Lemma ann_respects_atoms_eq_mutual :
  (forall G a A,       AnnTyping  G a A       -> True) /\
  (forall G phi,       AnnPropWff G phi       -> True) /\
  (forall G D g p1 p2, AnnIso     G D g p1 p2 -> forall D', D [=] D' -> AnnIso   G D' g p1 p2) /\
  (forall G D g A B,   AnnDefEq   G D g A B   -> forall D', D [=] D' -> AnnDefEq G D' g A B) /\
  (forall G,           AnnCtx     G           -> True).
Proof.
  eapply ann_typing_wff_iso_defeq_mutual.
  all: pre; subst; eauto 3.
  all: econstructor; eauto.
  fsetdec.
Qed.

Definition AnnIso_respects_atoms_eq   := third  ann_respects_atoms_eq_mutual.
Definition AnnDefEq_respects_atoms_eq := fourth ann_respects_atoms_eq_mutual.

Instance AnnIso_atoms_eq_mor : Morphisms.Proper
                                 (eq ==> AtomSetImpl.Equal ==> eq ==> eq ==> eq ==> iff)
                                 AnnIso.
Proof.
  simpl_relation; split=> ?;
  eauto using AnnIso_respects_atoms_eq, AtomSetProperties.equal_sym.
Qed.

Instance AnnDefEq_atoms_eq_mor : Morphisms.Proper
                                   (eq ==> AtomSetImpl.Equal ==> eq ==> eq ==> eq ==> iff)
                                   AnnDefEq.
Proof.
  simpl_relation; split=> ?;
  eauto using AnnDefEq_respects_atoms_eq, AtomSetProperties.equal_sym.
Qed.


Lemma ann_strengthen_noncovar:
  (forall G1  a A,   AnnTyping G1 a A -> True) /\
  (forall G1  phi,   AnnPropWff G1 phi -> True) /\
  (forall G1 D g p1 p2, AnnIso G1 D g p1 p2 -> forall x, not (exists phi, binds x (Co phi) G1) ->
                     AnnIso G1 (remove x D) g p1 p2) /\
  (forall G1 D g A B,   AnnDefEq G1 D g A B ->  forall x, not (exists phi, binds x (Co phi) G1) ->
                    AnnDefEq G1 (remove x D) g A B) /\
  (forall G1 ,       AnnCtx G1 -> True).
Proof.
  apply ann_typing_wff_iso_defeq_mutual; eauto 3; try done.
  - econstructor; eauto.
  - intros. destruct (x == c).
    + subst. assert False. apply H0. eexists. eauto. done.
    + eapply An_Assn; eauto.
  - econstructor; eauto.
  - intros.
    eapply (An_PiCong (L \u singleton x \u dom G)); eauto.
    intros. eapply H0; auto.
    unfold not in *. intros. destruct H6. apply H4.
    simpl in H6.
    destruct (binds_cons_1 _ x x0 _ (Tm A1) G H6). destruct H7. inversion H8.
    exists x1. auto.
  - intros.
    eapply (An_AbsCong (L \u singleton x)); eauto.
    intros. eapply H0; auto.
    unfold not in *. intros. destruct H6. apply H4.
    simpl in H6.
    destruct (binds_cons_1 _ x x0 _ (Tm A1) G H6). destruct H7. inversion H8.
    exists x1. auto.
  - eauto.
  - eauto.
  - intros.
    eapply (An_CPiCong (L \u singleton x)); eauto.
    intros.
    eapply H0; auto.
    unfold not in *. intros. destruct H6. apply H4.
    simpl in H6.
    destruct (binds_cons_1 _ x c _ (Co phi1) G H6). destruct H7.
    subst. fsetdec.
    exists x0. auto.
  - intros.
    eapply (An_CAbsCong (L \u singleton x)); eauto.
    move=> c Fr.
    eapply H0; first fsetdec.
    move=> [phi b].
    move: b => /binds_cons_iff [[? [?]] | /= b]; first (subst; fsetdec).
      by apply H5; exists phi.
  - eauto.
Qed. (* strengthen_nocovar *)

Lemma AnnDefEq_strengthen_available_tm :
  forall G D g A B, AnnDefEq G D g A B ->  forall x A', binds x (Tm A') G ->
                    forall D', D' [=] remove x D ->
                    AnnDefEq G D' g A B.
Proof.
  intros. eapply ann_respects_atoms_eq_mutual.
  eapply (fourth ann_strengthen_noncovar). eauto.
  unfold not.
  intros b. destruct b as [phi b].
  assert (Tm A' = Co phi). eapply binds_unique; eauto with ctx_wff.
  inversion H2.
  fsetdec.
Qed.

Lemma ann_weaken_available_mutual:
  (forall G1  a A,   AnnTyping G1 a A -> True) /\
  (forall G1  phi,   AnnPropWff G1 phi -> True) /\
  (forall G1 D g p1 p2, AnnIso G1 D g p1 p2 -> forall D', D [<=] D' -> AnnIso G1 D' g p1 p2) /\
  (forall G1 D g A B,   AnnDefEq G1 D g A B -> forall D', D [<=] D' -> AnnDefEq G1 D' g A B) /\
  (forall G1 ,       AnnCtx G1 -> True).
Proof.
  apply ann_typing_wff_iso_defeq_mutual; eauto 3; try done.
  all: econstructor; eauto.
Qed.

Lemma ann_remove_available_mutual:
  (forall G1  a A,   AnnTyping G1 a A -> True) /\
  (forall G1  phi,   AnnPropWff G1 phi -> True) /\
  (forall G1 D g p1 p2, AnnIso G1 D g p1 p2 ->
                   AnnIso G1 (AtomSetImpl.inter D (dom G1)) g p1 p2) /\
  (forall G1 D g A B,   AnnDefEq G1 D g A B ->
                   AnnDefEq G1 (AtomSetImpl.inter D (dom G1)) g A B) /\
  (forall G1 ,       AnnCtx G1 -> True).
Proof.
  apply ann_typing_wff_iso_defeq_mutual; eauto 3; try done.
  - intros L G D. intros.
    eapply (An_PiCong (L \u dom G \u D)); eauto.
    intros.
    eapply (fourth ann_respects_atoms_eq_mutual). eapply H0. eauto.
    simpl. fsetdec.
  - intros L G D. intros.
    eapply (An_AbsCong (L \u dom G \u D)); eauto.
    intros.
    eapply (fourth ann_respects_atoms_eq_mutual). eapply H0. eauto.
    simpl. fsetdec.
  - intros L G D. intros.
    eapply (An_CPiCong (L \u dom G \u D)); eauto.
    intros.
    eapply (fourth ann_respects_atoms_eq_mutual). eapply H0. eauto.
    simpl. fsetdec.
  - intros L G D. intros.
    eapply (An_CAbsCong (L \u dom G \u D)); eauto 1.
    intros.
    eapply (fourth ann_respects_atoms_eq_mutual). eapply H0. eauto.
    simpl. fsetdec.
    eauto.
Qed.

Lemma AnnDefEq_weaken_available :
  forall G D g A B, AnnDefEq G D g A B -> AnnDefEq G (dom G) g A B.
Proof.
  intros.
  remember (AtomSetImpl.inter D (dom G)) as D'.
  eapply (fourth ann_weaken_available_mutual).
  eapply (fourth ann_remove_available_mutual).
  eauto. subst. fsetdec.
Qed.

Lemma AnnIso_weaken_available :
  forall G D g A B, AnnIso G D g A B -> AnnIso G (dom G) g A B.
Proof.
  intros G D. intros.
  remember (AtomSetImpl.inter D (dom G)) as D'.
  eapply (third ann_weaken_available_mutual).
  eapply (third ann_remove_available_mutual).
  eauto. subst. fsetdec.
Qed.

Instance AnnIso_atoms_sub_mor : Morphisms.Proper
                                    (eq ==> AtomSetImpl.Subset ==> eq ==> eq ==> eq ==> impl)
                                    AnnIso.
Proof.
  simpl_relation; eapply (third ann_weaken_available_mutual); eassumption.
Qed.

Instance AnnDefEq_atoms_sub_mor : Morphisms.Proper
                                    (eq ==> AtomSetImpl.Subset ==> eq ==> eq ==> eq ==> impl)
                                    AnnDefEq.
Proof.
  simpl_relation; eapply (fourth ann_weaken_available_mutual); eassumption.
Qed.


(* FIXME: temporary hack *)
Ltac ann_weak_speedup :=
  first [eapply An_AppCong | eapply An_PiSnd].


(* ------------------------------------------------------------------- *)

Lemma ann_typing_weakening_mutual:
  (forall G0 a A,       AnnTyping  G0 a A       ->
     forall E F G, (G0 = F ++ G) -> AnnCtx (F ++ E ++ G) -> AnnTyping (F ++ E ++ G) a A) /\
  (forall G0 phi,       AnnPropWff G0 phi       ->
     forall E F G, (G0 = F ++ G) ->
        AnnCtx (F ++ E ++ G) -> AnnPropWff (F ++ E ++ G) phi) /\
  (forall G0 D g p1 p2, AnnIso     G0 D g p1 p2 ->
     forall E F G, (G0 = F ++ G) ->
        AnnCtx (F ++ E ++ G) -> AnnIso (F ++ E ++ G) D g p1 p2) /\
  (forall G0 D g A B,   AnnDefEq   G0 D g A B   ->
     forall E F G, (G0 = F ++ G) ->
        AnnCtx (F ++ E ++ G) -> AnnDefEq (F ++ E ++ G) D g A B) /\
  (forall G0,           AnnCtx     G0           ->
     forall E F G, (G0 = F ++ G) ->
        AnnCtx (F ++ E ++ G) -> AnnCtx (F ++ E ++ G)).
Proof.
  eapply ann_typing_wff_iso_defeq_mutual.
  all: pre; subst.
  all: eauto 3.
  all: try first [ ann_weak_speedup
                 | An_pick_fresh x;
                   try auto_rew_env;
                   try apply_first_hyp;
                   try simpl_env];
                   eauto 3.
  all: try solve [econstructor; eauto 2].
  all: try solve [eapply AnnDefEq_weaken_available; eauto 2].
  all: try solve [try rewrite <- dom_app; try rewrite <- dom_app;
                  eapply AnnDefEq_weaken_available;  eauto].
  all: try solve [econstructor; eauto 2;
                  eapply AnnDefEq_weaken_available; eauto 2].
  all: try solve [
    (* These are all AnnCtx goals. Need to show the new assumption
       is well-formed by using induction on a term that mentions it.
     *)
    econstructor; eauto 2;
      by move: (H1 E F G0 eq_refl ltac:(auto)); inversion 1].

  (* Left/Right
  eapply An_Right with (a:=a)(a':=a'); eauto 2;
    eapply AnnDefEq_weaken_available; eauto 2. *)
Qed.

Definition AnnTyping_weakening  := first  ann_typing_weakening_mutual.
Definition AnnPropWff_weakening := second ann_typing_weakening_mutual.
Definition AnnIso_weakening     := third  ann_typing_weakening_mutual.
Definition AnnDefEq_weakening   := fourth ann_typing_weakening_mutual.
Definition AnnCtx_weakening     := fifth  ann_typing_weakening_mutual.

End fc_weak.
