Require Import FcEtt.sigs.

Require Import FcEtt.tactics.
Require Import FcEtt.utils.
Require Export FcEtt.imports.
Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_par.
Require Export FcEtt.ett_ind.


Module ext_weak (wf: ext_wf_sig).

Include wf.

Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

(* TODO: this tactic is not so "automated" (e.g. has to link a_Pi to E_Pi),
but it is hard to make it more
         "searchy" without trying extensively all the lemmas. We could probably work something out, though *)
(*
Ltac E_pick_fresh x :=
  match goal with
    | [ |- Typing _ ?shape _ ] =>
      let v := match shape with
            | a_Pi _ _ _ => E_Pi
            | a_UAbs _ _ => E_Abs
            | a_CPi _ _  => E_CPi
            | a_CAbs _ _ => E_CAbs
            | a_UCAbs _  => E_CAbs
           end
      in pick fresh x and apply v
    | [ |- DefEq _ _ ?shape _ _ ] =>
      let v := match shape with
            | a_Pi _ _ _ => E_PiCong
            | a_UAbs _ _ => E_AbsCong
            | a_CPi _ _  => E_CPiCong
            | a_CAbs _ _ => E_CAbsCong
            | a_UCAbs _  => E_CAbsCong
               end
      in pick fresh x and apply v
    | [ |- Par _ _ ?shape _ ] =>
      let v := match shape with
            | a_Pi _ _ _ => Par_Pi
            | a_UAbs _ _ => Par_Abs
            | a_CPi _ _  => Par_CPi
            | a_CAbs _ _ => Par_CAbs
            | a_UCAbs _  => Par_CAbs
           end
      in pick fresh x and apply v
  end.
*)

(* ------------------------------------------------------------------- *)
(* Weakening Lemmas for the available set *)

(* Can replace set with an equivalent *)
Lemma respects_atoms_eq_mutual :
  (forall G a A,     Typing  G a A       -> True) /\
  (forall G phi,     PropWff G phi       -> True) /\
  (forall G D p1 p2, Iso G D p1 p2 -> forall D', D [=] D' -> Iso G D' p1 p2) /\
  (forall G D A B T,   DefEq G D A B T  -> forall D', D [=] D' -> DefEq G D' A B T) /\
  (forall G,           Ctx G           -> True).
Proof. 
  ext_induction CON; intros; subst; eauto 2.
  all: try solve [eapply CON; eauto 2; try fsetdec].

  (* these are hard to find. *)
  (*
  eapply E_LeftRel with (b:=b)(b':=b'); eauto 2.
  eapply E_LeftIrrel with (b:=b)(b':=b'); eauto 2.
  eapply E_Right with (a:=a)(a':=a'); eauto 2.
  *)
Qed.

Definition Iso_respects_atoms_eq   := third  respects_atoms_eq_mutual.
Definition DefEq_respects_atoms_eq := fourth respects_atoms_eq_mutual.
(*
Instance Iso_atoms_eq_mor : Morphisms.Proper
                                 (eq ==> AtomSetImpl.Equal ==> eq ==> eq ==> iff)
                                 Iso.
Proof.
  simpl_relation; split=> ?;
  eauto using Iso_respects_atoms_eq, AtomSetProperties.equal_sym.
Qed.

Instance DefEq_atoms_eq_mor : Morphisms.Proper
                                   (eq ==> AtomSetImpl.Equal ==> eq ==> eq ==> eq ==> iff)
                                   DefEq.
Proof.
  simpl_relation; split=> ?;
  eauto using DefEq_respects_atoms_eq, AtomSetProperties.equal_sym.
Qed.

*)
(* ----- *)

Ltac binds_cons :=
  let H5 := fresh in
  match goal with
    [
      H4 : (∃ phi : constraint, binds ?x (Co phi) ?G) → False
      |- ((exists phi, binds ?x (Co phi) ([(?y, ?s)] ++ ?G)) -> False) ] =>
    intro H5; destruct H5; apply H4; simpl in H5;
    destruct (binds_cons_1 _ x y _ s G H5); split_hyp; subst;
    try done; eauto
  end.


Lemma strengthen_available_noncovar:
  (forall G1  a A,    Typing G1 a A -> True) /\
  (forall G1  phi,    PropWff G1 phi -> True) /\
  (forall G1 D p1 p2, Iso G1 D p1 p2 -> forall x, not (exists phi, binds x (Co phi) G1) ->
                 Iso G1 (remove x D) p1 p2) /\
  (forall G1 D A B A1,DefEq G1 D A B A1 ->  forall x, not (exists phi, binds x (Co phi) G1) ->
                 DefEq G1 (remove x D) A B A1) /\
  (forall G1 ,        Ctx G1 -> True).
Proof.
  eapply typing_wff_iso_defeq_mutual; eauto 3; try done.
  all: intros; unfold not in *. Focus 5. destruct rho. Unfocus.
  all: try (E_pick_fresh y; eauto 3).
  all: try solve [destruct (x == c); [ subst; assert False; eauto | eauto]].
  all: try (eapply H0; auto; binds_cons).
  all: try (eapply H; auto; binds_cons).
  all: try (move: H5 => /binds_cons_iff [[? [?]] | /= H5]; subst;
                       assert (y <> y); [fsetdec|done|fsetdec|done]).
  all: eauto 4.
  - move: H2 => /binds_cons_iff [[? [?]] | /= H2]; subst;
                       assert (y <> y); [fsetdec|done|fsetdec|done].
Qed.  (* strengthen_available_nocovar *)

Lemma DefEq_strengthen_available_tmvar :
  forall G D g A B, DefEq G D g A B ->  forall x A', binds x (Tm A') G ->
                    forall D', D' [=] remove x D ->
                    DefEq G D' g A B.
Proof.
  intros. eapply respects_atoms_eq_mutual.
  eapply (fourth strengthen_available_noncovar). eauto.
  unfold not.
  intros b. destruct b as [phi b].
  assert (Tm A' = Co phi). eapply binds_unique; eauto.
  inversion H2.
  fsetdec.
Qed.

(* ----- *)

Lemma weaken_available_mutual:
  (forall G1  a A,   Typing G1 a A -> True) /\
  (forall G1  phi,   PropWff G1 phi -> True) /\
  (forall G1 D p1 p2, Iso G1 D p1 p2 -> forall D', D [<=] D' -> Iso G1 D' p1 p2) /\
  (forall G1 D A B T,   DefEq G1 D A B T -> forall D', D [<=] D' -> DefEq G1 D' A B T) /\
  (forall G1 ,       Ctx G1 -> True).
Proof.
  ext_induction CON.
  all: try done.
  all: intros; try solve [eapply CON; eauto 2].
  (*
  - eapply E_LeftRel   with (b := b) (b' := b'); eauto 2.
  - eapply E_LeftIrrel with (b:=b) (b' := b'); eauto 2.
  - eapply E_Right     with (a:=a)(a':=a'); eauto 2.
  *)
Qed.

Lemma remove_available_mutual:
  (forall G1  a A,   Typing G1 a A -> True) /\
  (forall G1  phi,   PropWff G1 phi -> True) /\
  (forall G1 D p1 p2, Iso G1 D p1 p2 ->
                   Iso G1 (AtomSetImpl.inter D (dom G1)) p1 p2) /\
  (forall G1 D A B T,   DefEq G1 D A B T ->
                   DefEq G1 (AtomSetImpl.inter D (dom G1)) A B T) /\
  (forall G1 ,       Ctx G1 -> True).
Proof.
  ext_induction CON.
  all: try done.
  all: eauto 2.
  all: intros; try solve [eapply CON; eauto 2].
  (* only binding constructors left *)
  all: eapply (CON (L \u dom G \u D)); auto;
    intros;
    eapply (fourth respects_atoms_eq_mutual);
    [match goal with [H0 : forall x, x `notin` ?L -> DefEq _ (AtomSetImpl.inter _ _) _ _ _ |- _ ] => eapply H0 end; auto|
    auto; simpl; fsetdec].
Qed.

(*
Instance Iso_atoms_sub_mor : Morphisms.Proper
                                    (eq ==> AtomSetImpl.Subset ==> eq ==> eq ==> impl)
                                    Iso.
Proof.
  simpl_relation; eapply (third weaken_available_mutual); eassumption.
Qed.

Instance DefEq_atoms_sub_mor : Morphisms.Proper
                                    (eq ==> AtomSetImpl.Subset ==> eq ==> eq ==> eq ==> impl)
                                    DefEq.
Proof.
  simpl_relation; eapply (fourth weaken_available_mutual); eassumption.
Qed.
*)

Lemma DefEq_weaken_available :
  forall G D A B T, DefEq G D A B T -> DefEq G (dom G) A B T.
Proof.
  intros.
  remember (AtomSetImpl.inter D (dom G)) as D'.
  eapply (fourth weaken_available_mutual).
  eapply (fourth remove_available_mutual).
  eauto. subst. fsetdec.
Qed.

Lemma Iso_weaken_available :
  forall G D A B, Iso G D A B -> Iso G (dom G) A B.
Proof.
  intros G D. intros.
  remember (AtomSetImpl.inter D (dom G)) as D'.
  eapply (third weaken_available_mutual).
  eapply (third remove_available_mutual).
  eauto. subst. fsetdec.
Qed.

Hint Resolve DefEq_weaken_available Iso_weaken_available.


Lemma typing_weakening_mutual:
  (forall G0 a A,     Typing G0 a A ->
     forall E F G, (G0 = F ++ G) -> Ctx (F ++ E ++ G) -> Typing (F ++ E ++ G) a A) /\
  (forall G0 phi,     PropWff G0 phi ->
     forall E F G, (G0 = F ++ G) -> Ctx (F ++ E ++ G) -> PropWff (F ++ E ++ G) phi) /\
  (forall G0 D p1 p2, Iso G0 D p1 p2 ->
     forall E F G, (G0 = F ++ G) -> Ctx (F ++ E ++ G) -> Iso (F ++ E ++ G) D p1 p2) /\
  (forall G0 D A B T, DefEq G0 D A B T ->
     forall E F G, (G0 = F ++ G) -> Ctx (F ++ E ++ G) -> DefEq (F ++ E ++ G) D A B T) /\
  (forall G0,         Ctx G0 ->
     forall E F G, (G0 = F ++ G) -> Ctx (F ++ E ++ G) -> Ctx (F ++ E ++ G)).
Proof.
  ext_induction CON.
  all: intros; subst; try done.

  (* TODO: move E_LeftRel etc. first using ensure_case *)

  all: try solve [eapply CON; eauto 2].
  all: try solve [eapply CON; eauto 2; eapply DefEq_weaken_available; eauto 2]. 
  Focus 6. destruct rho. Unfocus.
  all: try solve [E_pick_fresh y; try auto_rew_env; apply_first_hyp; try simpl_env; eauto 3].
  (*
  eapply E_LeftRel with (b:=b)(b':=b'); eauto 2;
    try eapply DefEq_weaken_available; eauto 2.
  eapply E_LeftIrrel with (b:=b)(b':=b'); eauto 2;
    try eapply DefEq_weaken_available; eauto 2.
  eapply E_Right with (a:=a)(a':=a'); eauto 2;
    try eapply DefEq_weaken_available; eauto 2.
  *)
Qed.


Definition Typing_weakening  := first  typing_weakening_mutual.
Definition PropWff_weakening := second typing_weakening_mutual.
Definition Iso_weakening     := third  typing_weakening_mutual.
Definition DefEq_weakening   := fourth typing_weakening_mutual.
Definition Ctx_weakening     := fifth  typing_weakening_mutual.


(*
Lemma Typing_weakening : ∀ (E F G : context) (a A : tm),  Typing (F ++ G) a A →  Ctx (F ++ E ++ G) ->
                                                          Typing (F ++ E ++ G) a A.
Proof. intros. apply (first typing_weakening_mutual) with (G0 := F ++ G)(F:=F)(E:=E)(G:=G); auto. Qed.


Lemma PropWff_weakening : forall (E F G : context) phi, PropWff (F ++ G) phi -> Ctx (F ++ E ++ G) → PropWff (F ++ E ++ G) phi.
Proof. intros. apply (second typing_weakening_mutual) with (G0 := F ++ G)(F:=F)(E:=E)(G:=G); auto. Qed.

Lemma Iso_weakening : ∀ (E F G : context) (D : available_props) (p1 p2 : constraint),
       Iso (F ++ G) D p1 p2 -> Ctx (F ++ E ++ G) → Iso (F ++ E ++ G) D p1 p2.
Proof. intros. apply (third typing_weakening_mutual) with (G0 := F ++ G)(F:=F)(E:=E)(G:=G); auto. Qed.

Lemma DefEq_weakening : ∀ (E F G : context) (D : available_props) (A B T : tm),
    DefEq (F ++ G) D A B T → Ctx (F ++ E ++ G) → DefEq (F ++ E ++ G) D A B T.
Proof. intros. apply (fourth typing_weakening_mutual) with (G0 := F ++ G)(F:=F)(E:=E)(G:=G); auto. Qed.

Lemma Ctx_weakening : ∀ (E F G: context),
       Ctx (F ++ G) → Ctx (F ++ E ++ G) → Ctx (F ++ E ++ G).
Proof. intros. apply (fifth typing_weakening_mutual) with (G0 := F ++ G)(F:=F)(E:=E)(G:=G); auto. Qed.


Lemma Iso_weakening_dom :
   ∀ (E F G : context) (D : available_props) (p1 p2 : constraint),
       Iso (F ++ G) (dom (F ++ G)) p1 p2 -> Ctx (F ++ E ++ G) → Iso (F ++ E ++ G) (dom(F ++ E ++ G)) p1 p2.
Proof.
  intros.
  eapply Iso_weaken_available.
  eapply Iso_weakening.
  eassumption.
  auto.
Qed.

Lemma DefEq_weakening_dom : ∀ (E F G : context) (D : available_props) (A B T : tm),
    DefEq (F ++ G) (dom (F ++ G)) A B T → Ctx (F ++ E ++ G) → DefEq (F ++ E ++ G) (dom (F ++ E ++ G)) A B T.
Proof.
  intros.
  eapply DefEq_weaken_available.
  eapply DefEq_weakening.
  eassumption.
  auto.
Qed.
*)


End ext_weak.
