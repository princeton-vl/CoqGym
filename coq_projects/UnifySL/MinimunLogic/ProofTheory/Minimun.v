Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.TheoryOfSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.TheoryOfSequentCalculus.

Local Open Scope logic_base.
Local Open Scope syntax.

Definition multi_imp {L: Language} {minL: MinimunLanguage L} (xs: list expr) (y: expr): expr :=
  fold_right impp y xs.

Class NormalAxiomatization (L: Language) {minL: MinimunLanguage L} (Gamma: ProofTheory L): Type := {
  derivable_provable: forall Phi y, derivable Phi y <->
                        exists xs, Forall (fun x => Phi x) xs /\ provable (multi_imp xs y)
}.

Class MinimunAxiomatization (L: Language) {minL: MinimunLanguage L} (Gamma: ProofTheory L) := {
  modus_ponens: forall x y, |-- (x --> y) -> |-- x -> |-- y;
  axiom1: forall x y, |-- (x --> (y --> x));
  axiom2: forall x y z, |-- ((x --> y --> z) --> (x --> y) --> (x --> z))
}.

Class MinimunSequentCalculus (L: Language) {minL: MinimunLanguage L} (Gamma: ProofTheory L) := {
  deduction_modus_ponens: forall Phi x y, Phi |-- x -> Phi |-- x --> y -> Phi |-- y;
  deduction_impp_intros: forall Phi x y, Phi;; x |-- y -> Phi |-- x --> y
}.

Section DerivableRulesFromAxiomatization.

Context {L: Language}
        {minL: MinimunLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}.

Lemma provable_impp_refl: forall (x: expr), |-- x --> x.
Proof.
  intros.
  pose proof axiom2 x (x --> x) x.
  pose proof axiom1 x (x --> x).
  pose proof axiom1 x x.
  pose proof modus_ponens _ _ H H0.
  pose proof modus_ponens _ _ H2 H1.
  auto.
Qed.

Lemma aux_minimun_rule00: forall (x y: expr), |-- x -> |-- y --> x.
Proof.
  intros.
  pose proof axiom1 x y.
  eapply modus_ponens; eauto.
Qed.

Lemma aux_minimun_theorem00: forall (x y z: expr), |--  (y --> z) --> (x --> y) --> (x --> z).
Proof.
  intros.
  pose proof axiom2 x y z.
  pose proof aux_minimun_rule00 _ (y --> z) H.
  pose proof axiom1 (y --> z) x.
  pose proof axiom2 (y --> z) (x --> y --> z) ((x --> y) --> (x --> z)).
  pose proof modus_ponens _ _ H2 H0.
  pose proof modus_ponens _ _ H3 H1.
  auto.
Qed.

Lemma aux_minimun_rule01: forall (x y z: expr), |-- x --> y -> |-- (z --> x) --> (z --> y).
Proof.
  intros.
  pose proof aux_minimun_theorem00 z x y.
  pose proof modus_ponens _ _ H0 H.
  auto.
Qed.

Lemma aux_minimun_rule02: forall (x y z: expr), |-- x --> y -> |-- y --> z -> |-- x --> z.
Proof.
  intros.
  pose proof aux_minimun_theorem00 x y z.
  pose proof modus_ponens _ _ H1 H0.
  pose proof modus_ponens _ _ H2 H.
  auto.
Qed.

Lemma aux_minimun_theorem01: forall (x y z: expr), |-- (x --> z) --> (x --> y --> z).
Proof.
  intros.
  apply aux_minimun_rule01.
  apply axiom1.
Qed.

Lemma aux_minimun_theorem02: forall (x y: expr), |-- x --> (x --> y) --> y.
Proof.
  intros.
  pose proof axiom2 (x --> y) x y.
  pose proof provable_impp_refl (x --> y).
  pose proof modus_ponens _ _ H H0.
  pose proof aux_minimun_rule01 _ _ x H1.
  pose proof axiom1 x (x --> y).
  pose proof modus_ponens _ _ H2 H3.
  auto.
Qed.

Lemma aux_minimun_theorem03: forall (x y z: expr), |--  y --> (x --> y --> z) --> (x --> z).
Proof.
  intros.
  pose proof aux_minimun_theorem00 x (y --> z) z.
  pose proof aux_minimun_theorem02 y z.
  eapply aux_minimun_rule02; eauto.
Qed.

Lemma aux_minimun_theorem04: forall (x y: expr), |-- (x --> x --> y) --> x --> y.
Proof.
  intros.
  pose proof axiom2 x (x --> y) y.
  pose proof aux_minimun_theorem02 x y.
  pose proof modus_ponens _ _ H H0.
  auto.
Qed.

Lemma provable_impp_arg_switch: forall (x y z: expr), |-- (x --> y --> z) --> (y --> x --> z).
Proof.
  intros.
  apply aux_minimun_rule02 with (y --> x --> y --> z).
  + apply axiom1.
  + pose proof axiom2 y (x --> y --> z) (x --> z).
    eapply modus_ponens; eauto. clear H.
    pose proof aux_minimun_theorem00 x (y --> z) z.
    eapply aux_minimun_rule02; eauto.
    apply aux_minimun_theorem02.
Qed.

Lemma provable_impp_trans: forall (x y z: expr), |-- (x --> y) --> (y --> z) --> (x --> z).
Proof.
  intros.
  pose proof provable_impp_arg_switch (y --> z) (x --> y) (x --> z).
  eapply modus_ponens; eauto. clear H.
  apply aux_minimun_theorem00.
Qed.

End DerivableRulesFromAxiomatization.

Section DerivableRules_multi_impp.

Context {L: Language}
        {minL: MinimunLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}.

Lemma provable_multi_imp_shrink: forall (xs: list expr) (x y: expr), |-- (x --> multi_imp xs (x --> y)) --> multi_imp xs (x --> y).
Proof.
  intros.
  induction xs.
  + simpl.
    apply aux_minimun_theorem04.
  + simpl.
    apply aux_minimun_rule01 with (z := a) in IHxs.
    eapply aux_minimun_rule02; [| eauto].
    apply provable_impp_arg_switch.
Qed.

Lemma provable_multi_imp_arg_switch1: forall (xs: list expr) (x y: expr), |-- (x --> multi_imp xs  y) --> multi_imp xs (x --> y).
Proof.
  intros.
  induction xs.
  + simpl.
    apply provable_impp_refl.
  + simpl.
    apply aux_minimun_rule02 with (a --> x --> multi_imp xs y).
    - apply provable_impp_arg_switch.
    - apply aux_minimun_rule01; auto.
Qed.

Lemma provable_multi_imp_arg_switch2: forall (xs: list expr) (x y: expr), |-- multi_imp xs (x --> y) --> (x --> multi_imp xs  y).
Proof.
  intros.
  induction xs.
  + simpl.
    apply provable_impp_refl.
  + simpl.
    apply aux_minimun_rule02 with (a --> x --> multi_imp xs y).
    - apply aux_minimun_rule01; auto.
    - apply provable_impp_arg_switch.
Qed.

Lemma provable_multi_imp_weaken: forall (xs: list expr) (x y: expr), |-- x --> y -> |-- multi_imp xs x --> multi_imp xs y.
Proof.
  intros.
  induction xs.
  + auto.
  + apply aux_minimun_rule01; auto.
Qed.

(* TODO: maybe this one is also not useful now. *)
Lemma provable_multi_imp_split:
  forall Phi1 Phi2 (xs: list expr) (y: expr),
    Forall (Union _ Phi1 Phi2) xs ->
    |-- multi_imp xs y ->
    exists xs1 xs2,
      Forall Phi1 xs1 /\
      Forall Phi2 xs2 /\
      |-- multi_imp xs1 (multi_imp xs2 y).
Proof.
  intros.
  revert y H0; induction H.
  + exists nil, nil.
    split; [| split]; [constructor .. | auto].
  + intros.
    specialize (IHForall (x --> y)).
    eapply modus_ponens in H1;
      [| simpl; apply provable_multi_imp_arg_switch1].
    specialize (IHForall H1); clear H1.
    destruct IHForall as [xs1 [xs2 [? [? ?]]]].
    destruct H.
    - exists (x :: xs1), xs2.
      split; [constructor | split]; auto.
      simpl; eapply modus_ponens; [apply provable_multi_imp_arg_switch2 |].
      eapply modus_ponens; [apply provable_multi_imp_weaken | exact H3].
      apply provable_multi_imp_arg_switch2.
    - exists xs1, (x :: xs2).
      split; [| split; [constructor | ]]; auto.
      eapply modus_ponens; [apply provable_multi_imp_weaken | exact H3].
      simpl; apply provable_multi_imp_arg_switch2.
Qed.

Lemma provable_add_multi_imp_left_head: forall xs1 xs2 y, |-- multi_imp xs2 y --> multi_imp (xs1 ++ xs2) y.
Proof.
  intros.
  induction xs1.
  + apply provable_impp_refl.
  + eapply aux_minimun_rule02; eauto.
    apply axiom1.
Qed.

Lemma provable_add_multi_imp_left_tail: forall xs1 xs2 y, |-- multi_imp xs1 y --> multi_imp (xs1 ++ xs2) y.
Proof.
  intros.
  induction xs1; simpl.
  + pose proof (provable_add_multi_imp_left_head xs2 nil y).
    rewrite app_nil_r in H; auto.
  + apply aux_minimun_rule01; auto.
Qed.

Lemma provable_multi_imp_modus_ponens: forall xs y z, |-- multi_imp xs y --> multi_imp xs (y --> z) --> multi_imp xs z.
Proof.
  intros.
  induction xs; simpl.
  + apply aux_minimun_theorem02.
  + eapply aux_minimun_rule02; [| apply provable_impp_arg_switch].
    eapply aux_minimun_rule02; [| apply aux_minimun_theorem04].
    apply aux_minimun_rule01.
    eapply aux_minimun_rule02; [eauto |].
    eapply aux_minimun_rule02; [| apply provable_impp_arg_switch].
    apply aux_minimun_theorem00.
Qed.

End DerivableRules_multi_impp.

Section Axiomatization2SequentCalculus.

Context {L: Language}
        {minL: MinimunLanguage L}
        {Gamma: ProofTheory L}
        {AX: NormalAxiomatization L Gamma}.

Lemma Axiomatization2SequentCalculus_SC: NormalSequentCalculus L Gamma.
Proof.
  constructor.
  intros.
  rewrite derivable_provable.
  split; intros.
  + exists nil; split; auto.
  + destruct H as [xs [? ?]].
    destruct xs; [auto |].
    inversion H; subst.
    inversion H3.
Qed.

Context {minAX: MinimunAxiomatization L Gamma}.

Lemma Axiomatization2SequentCalculus_fwSC: FiniteWitnessedSequentCalculus L Gamma.
Proof.
  constructor.
  hnf; intros.
  rewrite derivable_provable in H.
  destruct H as [xs [? ?]].
  exists xs.
  split; auto.
  rewrite derivable_provable.
  exists xs.
  split; auto.
  rewrite Forall_forall; auto.
Qed.

Lemma Axiomatization2SequentCalculus_minSC: MinimunSequentCalculus L Gamma.
Proof.
  constructor.
  + intros.
    rewrite derivable_provable in H, H0 |- *.
    destruct H as [xs1 [? ?]], H0 as [xs2 [? ?]].
    exists (xs1 ++ xs2); split.
    - rewrite Forall_app_iff; auto.
    - pose proof modus_ponens _ _ (provable_add_multi_imp_left_tail xs1 xs2 _) H1.
      pose proof modus_ponens _ _ (provable_add_multi_imp_left_head xs1 xs2 _) H2.
      pose proof provable_multi_imp_modus_ponens (xs1 ++ xs2) x y.
      pose proof modus_ponens _ _ H5 H3.
      pose proof modus_ponens _ _ H6 H4.
      auto.
  + intros.
    rewrite derivable_provable in H |- *.
    destruct H as [xs [? ?]].
    pose proof provable_multi_imp_split _ _ _ _ H H0 as [xs1 [xs2 [? [? ?]]]].
    exists xs1.
    split; auto.
    eapply modus_ponens; [| exact H3].
    apply provable_multi_imp_weaken.
    clear - H2 minAX.
    induction H2.
    - apply axiom1.
    - inversion H; subst x0; clear H.
      simpl.
      pose proof aux_minimun_theorem04 x y.
      pose proof aux_minimun_rule01 _ _ x IHForall.
      eapply aux_minimun_rule02; [exact H0 | exact H].
Qed.

Lemma Axiomatization2SequentCalculus_bSC: BasicSequentCalculus L Gamma.
Proof.
  assert (DW: DeductionWeaken L Gamma).
  {
    hnf; intros.
    rewrite derivable_provable in H0 |- *.
    destruct H0 as [xs [? ?]].
    exists xs; split; auto.
    revert H0; apply Forall_impl.
    auto.
  }
  constructor; auto.
  + intros.
    rewrite derivable_provable.
    exists (x :: nil); split.
    - constructor; auto.
    - simpl.
      apply provable_impp_refl.
  + apply DeductionWeaken_ContextualDerivableFiniteWitnessed_DeductionSubst1_2_DeductionSubst.
    - exact DW.
    - apply DeductionWeaken_DerivableFiniteWitnessed_2_ContextualDerivableFiniteWitnessed.
      * exact DW.
      * exact (@derivable_finite_witnessed _ _ Axiomatization2SequentCalculus_fwSC).
    - apply DeductionImpIntro_DeductionMP_2_DeductionSubst1.
      * exact (@deduction_impp_intros _ _ _ Axiomatization2SequentCalculus_minSC).
      * exact (@deduction_modus_ponens _ _ _ Axiomatization2SequentCalculus_minSC).
Qed.

End Axiomatization2SequentCalculus.

Section DerivableRulesFromSequentCalculus.

Context {L: Language}
        {Gamma: ProofTheory L}
        {bSC: BasicSequentCalculus L Gamma}.

Context {minL: MinimunLanguage L}
        {minSC: MinimunSequentCalculus L Gamma}.

Lemma deduction_impp_elim: forall Phi x y,
  Phi |-- impp x y ->
  Union _ Phi (Singleton _ x) |-- y.
Proof.
  intros.
  eapply deduction_modus_ponens; solve_assum.
Qed.

Theorem deduction_theorem:
  forall (Phi: context) (x y: expr),
    Union _ Phi (Singleton _ x) |-- y <->
    Phi |-- x --> y.
Proof.
  intros; split.
  + apply deduction_impp_intros; auto.
  + apply deduction_impp_elim; auto.
Qed.

Theorem deduction_theorem_multi_imp:
  forall (Phi: context) (xs: list expr) (y: expr),
    Union _ Phi (fun x => In x xs) |-- y <->
    Phi |-- multi_imp xs y.
Proof.
  intros.
  revert Phi; induction xs; intros.
  + simpl.
    split; apply deduction_weaken;
    unfold Included, Ensembles.In; intros.
    - rewrite Union_spec in H.
      tauto.
    - rewrite Union_spec.
      tauto.
  + simpl.
    rewrite <- deduction_theorem, <- IHxs.
    split; apply deduction_weaken;
    unfold Included, Ensembles.In; intros.
    - rewrite Union_spec in H.
      rewrite !Union_spec, Singleton_spec.
      tauto.
    - rewrite !Union_spec, Singleton_spec in H.
      rewrite !Union_spec.
      tauto.
Qed.

Lemma derivable_impp_refl: forall (Phi: context) (x: expr), Phi |-- x --> x.
Proof.
  intros.
  apply deduction_theorem.
  solve_assum.
Qed.

Lemma deduction_left_impp_intros: forall (Phi: context) (x y: expr),
  Phi |-- x ->
  Phi |-- y --> x.
Proof.
  intros.
  apply deduction_theorem.
  solve_assum.
Qed.

Lemma derivable_axiom1: forall (Phi: context) (x y: expr),
  Phi |-- x --> y --> x.
Proof.
  intros.
  rewrite <- !deduction_theorem.
  solve_assum.
Qed.

Lemma derivable_axiom2: forall (Phi: context) (x y z: expr),
  Phi |-- (x --> y --> z) --> (x --> y) --> (x --> z).
Proof.
  intros.
  rewrite <- !deduction_theorem.
  apply deduction_modus_ponens with y.
  + apply deduction_modus_ponens with x; solve_assum.
  + apply deduction_modus_ponens with x; solve_assum.
Qed.

Lemma derivable_modus_ponens: forall (Phi: context) (x y: expr),
  Phi |-- x --> (x --> y) --> y.
Proof.
  intros.
  rewrite <- !deduction_theorem.
  apply deduction_modus_ponens with x; solve_assum.
Qed.

Lemma deduction_impp_trans: forall (Phi: context) (x y z: expr),
  Phi |-- x --> y ->
  Phi |-- y --> z ->
  Phi |-- x --> z.
Proof.
  intros.
  rewrite <- deduction_theorem in H |- *.
  apply deduction_modus_ponens with y; solve_assum.
Qed.

Lemma deduction_impp_arg_switch: forall (Phi: context) (x y z: expr),
  Phi |-- x --> y --> z ->
  Phi |-- y --> x --> z.
Proof.
  intros.
  rewrite <- !deduction_theorem in *.
  eapply deduction_weaken; [| exact H].
  intros ? ?.
  destruct H0; [destruct H0 |].
  + left; left; auto.
  + right; auto.
  + left; right; auto.
Qed.

End DerivableRulesFromSequentCalculus.

Section SequentCalculus2Axiomatization.

Context {L: Language}
        {Gamma: ProofTheory L}
        {minL: MinimunLanguage L}
        {SC: NormalSequentCalculus L Gamma}
        {bSC: BasicSequentCalculus L Gamma}
        {minSC: MinimunSequentCalculus L Gamma}.

Theorem SequentCalculus2Axiomatization_minAX: MinimunAxiomatization L Gamma.
Proof.
  constructor.
  + intros x y.
    rewrite !provable_derivable.
    intros.
    eapply deduction_modus_ponens; eauto.
  + intros x y.
    rewrite provable_derivable.
    apply derivable_axiom1.
  + intros x y z.
    rewrite provable_derivable.
    apply derivable_axiom2.
Qed.

Theorem SequentCalculus2Axiomatization_AX {fwSC: FiniteWitnessedSequentCalculus L Gamma}: NormalAxiomatization L Gamma.
Proof.
  constructor; intros.
  split; intros.
  + apply derivable_finite_witnessed in H.
    destruct H as [xs [? ?]]; exists xs.
    split; auto.
    apply provable_derivable.
    apply deduction_theorem_multi_imp.
    eapply deduction_weaken; eauto.
    apply right_Included_Union.
  + destruct H as [xs [? ?]].
    apply provable_derivable in H0.
    apply deduction_theorem_multi_imp in H0.
    eapply deduction_weaken; eauto.
    unfold Included, Ensembles.In; intros.
    rewrite Union_spec in H1.
    destruct H1 as [[] |].
    revert x H1.
    rewrite Forall_forall in H; auto.
Qed.

End SequentCalculus2Axiomatization.

Definition Build_AxiomaticProofTheory {L: Language} {minL: MinimunLanguage L} (Provable: expr -> Prop): ProofTheory L :=
  Build_ProofTheory L Provable
   (fun Phi y => exists xs, Forall (fun x => Phi x) xs /\ Provable (multi_imp xs y)).

Definition Build_AxiomaticProofTheory_AX {L: Language} {minL: MinimunLanguage L} (Provable: expr -> Prop): NormalAxiomatization L (Build_AxiomaticProofTheory Provable) :=
  Build_NormalAxiomatization L minL (Build_AxiomaticProofTheory Provable) (fun _ _ => iff_refl _).

Definition Build_SequentCalculus {L: Language} (Derivable: context -> expr -> Prop): ProofTheory L :=
  Build_ProofTheory L (fun x => Derivable (Empty_set _) x) Derivable.

Definition Build_SequentCalculus_SC {L: Language} (Derivable: context -> expr -> Prop): NormalSequentCalculus L (Build_SequentCalculus Derivable) :=
  Build_NormalSequentCalculus L (Build_SequentCalculus Derivable) (fun _ => iff_refl _).

Inductive Typeclass_Rewrite (l: list (sig (fun X: Prop => X))): Prop :=
| Typeclass_Rewrite_I : Typeclass_Rewrite l.

Definition OpaqueProp (P: Prop): Prop := P.

Ltac revert_dep_rec T :=
  match goal with
  | H: context [T] |- _ =>
      first [ revert H | revert_dep_rec H]; revert_dep_rec T
  | _ => idtac
  end.

Ltac revert_dep Gamma :=
  match goal with
  | |- ?G => change (OpaqueProp G)
  end;
  revert_dep_rec Gamma.

Lemma ready_for_intros: forall G: Prop, OpaqueProp (Typeclass_Rewrite nil -> G) -> OpaqueProp G.
Proof.
  unfold OpaqueProp.
  intros.
  apply H.
  apply  Typeclass_Rewrite_I.
Qed.

Lemma intro_with_record: forall (l: list (sig (fun X: Prop => X))) (P: Prop) (G: P -> Prop),
  (forall _____: P, OpaqueProp (Typeclass_Rewrite ((exist (fun X: Prop => X) P _____) :: l) -> G _____)) ->
  OpaqueProp (Typeclass_Rewrite l -> forall _____: P, G _____).
Proof.
  unfold OpaqueProp.
  intros.
  apply H.
  apply  Typeclass_Rewrite_I.
Qed.

Ltac intros_dep :=
  match goal with
  | |- ?G => change (OpaqueProp G); simple apply ready_for_intros
  end;
  repeat
    match goal with
    | |-  OpaqueProp (Typeclass_Rewrite _ -> OpaqueProp _) => fail 1
    | _ => apply intro_with_record; intro
    end.

Ltac schedule :=
  match goal with
  | |- OpaqueProp (Typeclass_Rewrite ?L -> _) => constr: (L)
  end.

Ltac tactic_rev_rec L1 L2 :=
  match L1 with
  | nil => L2
  | cons ?H ?L => tactic_rev_rec L (cons H L2)
  end.

Ltac tactic_rev L :=
  match type of L with
  | list ?T => tactic_rev_rec L constr:(@nil T)
  end.

Lemma change_schedule: forall (l l': list (sig (fun X: Prop => X))) (G: Prop),
  OpaqueProp (Typeclass_Rewrite l -> G) ->
  OpaqueProp (Typeclass_Rewrite l' -> G).
Proof.
  unfold OpaqueProp.
  intros.
  apply H.
  apply  Typeclass_Rewrite_I.
Qed.

Lemma pop_schedule: forall (x: (sig (fun X: Prop => X))) (l: list (sig (fun X: Prop => X))) (G: Prop),
  OpaqueProp (Typeclass_Rewrite l -> G) ->
  OpaqueProp (Typeclass_Rewrite (x :: l) -> G).
Proof.
  unfold OpaqueProp.
  intros.
  apply H.
  apply  Typeclass_Rewrite_I.
Qed.

Lemma push_schedule: forall (x: (sig (fun X: Prop => X))) (l: list (sig (fun X: Prop => X))) (G: Prop),
  OpaqueProp (Typeclass_Rewrite (x :: l) -> G) ->
  OpaqueProp (Typeclass_Rewrite l -> G).
Proof.
  unfold OpaqueProp.
  intros.
  apply H.
  apply  Typeclass_Rewrite_I.
Qed.

Ltac AddSC_enrich :=
  progress autorewrite with AddSC; intros; unfold OpaqueProp at 1.

Ltac AddAX_enrich :=
  progress autorewrite with AddAX; intros; unfold OpaqueProp at 1.

Lemma finish_enrich: forall (G: Prop), G -> OpaqueProp (Typeclass_Rewrite nil -> OpaqueProp G).
Proof.
  unfold OpaqueProp.
  intros.
  apply H.
Qed.

Ltac enrich tac :=
  first
    [ tac
    | match goal with
      | |- OpaqueProp (Typeclass_Rewrite (?x :: _) -> _) =>
             apply (pop_schedule x);
             enrich tac;
             apply (push_schedule x)
      end
    ].

Ltac enrichs L tac :=
  apply (change_schedule L);
  repeat
    match goal with
    | |- OpaqueProp (Typeclass_Rewrite (?x :: _) -> _) =>
            enrich tac
    | |- OpaqueProp (Typeclass_Rewrite nil -> _) =>
            fail 1
    | |- OpaqueProp (Typeclass_Rewrite ?l -> _) =>
           fail 1000 "Cannot proceed these typeclasses: " l
    end;
  apply finish_enrich.

Ltac clear_rec L :=
  match L with
  | nil => idtac
  | exist _ _ ?H :: ?L' => clear H; clear_rec L'
  end.

Ltac AddSequentCalculus Gamma :=
  revert_dep Gamma;
  intros_dep;
  let L := schedule in
  let L' := tactic_rev L in
  enrichs L' AddSC_enrich;
  clear_rec L;
  change (@provable _ Gamma) with (@provable _ (Build_AxiomaticProofTheory provable));
  set (Gamma' := (Build_AxiomaticProofTheory provable)) in *;
  clearbody Gamma';
  clear Gamma;
  rename Gamma' into Gamma.

Ltac AddAxiomatization Gamma :=
  revert_dep Gamma;
  intros_dep;
  let L := schedule in
  let L' := tactic_rev L in
  enrichs L' AddAX_enrich;
  clear_rec L;
  change (@derivable _ Gamma) with (@derivable _ (Build_SequentCalculus derivable));
  set (Gamma' := (Build_SequentCalculus derivable)) in *;
  clearbody Gamma';
  clear Gamma;
  rename Gamma' into Gamma.

Ltac instantiate_must_succeed := instantiate (1 := _); try (instantiate (1 := _); fail 2 || fail 1).

Lemma MakeSequentCalculus_MinimunAxiomatization {L: Language} {minL: MinimunLanguage L} {Gamma: ProofTheory L} {minAX: MinimunAxiomatization L Gamma}:
  forall (G: Prop) (l: list (sig (fun X: Prop => X))),
  (forall
     (AX: NormalAxiomatization L (Build_AxiomaticProofTheory (@provable L Gamma)))
     (minAX: MinimunAxiomatization L (Build_AxiomaticProofTheory (@provable L Gamma)))
     (SC: NormalSequentCalculus L (Build_AxiomaticProofTheory (@provable L Gamma)))
     (bSC: BasicSequentCalculus L (Build_AxiomaticProofTheory (@provable L Gamma)))
     (fwSC: FiniteWitnessedSequentCalculus L (Build_AxiomaticProofTheory (@provable L Gamma)))
     (minSC: MinimunSequentCalculus L (Build_AxiomaticProofTheory (@provable L Gamma))),
     OpaqueProp (OpaqueProp (Typeclass_Rewrite l -> G))) <->
  OpaqueProp (Typeclass_Rewrite ((exist (fun X: Prop => X) (MinimunAxiomatization L Gamma) minAX) :: l) -> G).
Proof.
  unfold OpaqueProp.
  intros.
  split; intros.
  + clear H0.
    assert (NormalAxiomatization L (Build_AxiomaticProofTheory provable))
      by (apply Build_AxiomaticProofTheory_AX).
    assert (MinimunAxiomatization L (Build_AxiomaticProofTheory provable))
      by (destruct minAX; constructor; auto).
    assert (NormalSequentCalculus L (Build_AxiomaticProofTheory provable))
      by (apply Axiomatization2SequentCalculus_SC).
    assert (BasicSequentCalculus L (Build_AxiomaticProofTheory provable))
      by (apply Axiomatization2SequentCalculus_bSC).
    assert (MinimunSequentCalculus L (Build_AxiomaticProofTheory provable))
      by (apply Axiomatization2SequentCalculus_minSC).
    assert (FiniteWitnessedSequentCalculus L (Build_AxiomaticProofTheory provable))
      by (apply Axiomatization2SequentCalculus_fwSC).
    apply H; auto.
    apply Typeclass_Rewrite_I.
  + apply H; auto.
    apply Typeclass_Rewrite_I.
Qed.

Hint Rewrite <- @MakeSequentCalculus_MinimunAxiomatization: AddSC.

Lemma MakeAxiomatization_BasicSequentCalculus {L: Language} {Gamma: ProofTheory L} {bSC: BasicSequentCalculus L Gamma}:
  forall (G: Prop) (l: list (sig (fun X: Prop => X))),
  (forall
     (SC: NormalSequentCalculus L (Build_SequentCalculus (@derivable L Gamma)))
     (bSC: BasicSequentCalculus L (Build_SequentCalculus (@derivable L Gamma))),
     OpaqueProp (OpaqueProp (Typeclass_Rewrite l -> G))) <->
  OpaqueProp (Typeclass_Rewrite ((exist (fun X: Prop => X) (BasicSequentCalculus L Gamma) bSC) :: l) -> G).
Proof.
  unfold OpaqueProp.
  intros.
  split; intros.
  + clear H0.
    assert (NormalSequentCalculus L (Build_SequentCalculus (@derivable L Gamma)))
      by (apply Build_SequentCalculus_SC).
    assert (BasicSequentCalculus L (Build_SequentCalculus (@derivable L Gamma)))
      by (destruct bSC; constructor; auto).
    apply H; auto.
    apply Typeclass_Rewrite_I.
  + apply H; auto.
    apply Typeclass_Rewrite_I.
Qed.

Hint Rewrite <- @MakeAxiomatization_BasicSequentCalculus: AddAX.

Lemma MakeAxiomatization_MinimunSequentCalculus {L: Language} {minL: MinimunLanguage L} {Gamma: ProofTheory L} {minSC: MinimunSequentCalculus L Gamma} {bSC': BasicSequentCalculus L (Build_SequentCalculus (@derivable L Gamma))}:
  forall (G: Prop) (l: list (sig (fun X: Prop => X))),
  (forall
     (minSC: MinimunSequentCalculus L (Build_SequentCalculus (@derivable L Gamma)))
     (minAX: MinimunAxiomatization L (Build_SequentCalculus (@derivable L Gamma))),
     OpaqueProp (OpaqueProp (Typeclass_Rewrite l -> G))) <->
  OpaqueProp (Typeclass_Rewrite ((exist (fun X: Prop => X) (MinimunSequentCalculus L Gamma) minSC) :: l) -> G).
Proof.
  unfold OpaqueProp.
  intros.
  split; intros.
  + clear H0.
    assert (NormalSequentCalculus L (Build_SequentCalculus (@derivable L Gamma)))
      by (apply Build_SequentCalculus_SC).
    assert (MinimunSequentCalculus L (Build_SequentCalculus (@derivable L Gamma)))
      by (destruct minSC; constructor; auto).
    assert (MinimunAxiomatization L (Build_SequentCalculus (@derivable L Gamma)))
      by (apply SequentCalculus2Axiomatization_minAX).
    apply H; auto.
    apply Typeclass_Rewrite_I.
  + apply H; auto.
    apply Typeclass_Rewrite_I.
Qed.

Hint Rewrite <- @MakeAxiomatization_MinimunSequentCalculus using (typeclasses eauto): AddAX.

Lemma MakeAxiomatization_FiniteWitnessedSequentCalculus {L: Language} {minL: MinimunLanguage L} {Gamma: ProofTheory L} {fwSC: FiniteWitnessedSequentCalculus L Gamma} {bSC': BasicSequentCalculus L (Build_SequentCalculus (@derivable L Gamma))} {minSC': MinimunSequentCalculus L (Build_SequentCalculus (@derivable L Gamma))}:
  forall (G: Prop) (l: list (sig (fun X: Prop => X))),
  (forall
     (fwSC: FiniteWitnessedSequentCalculus L (Build_SequentCalculus (@derivable L Gamma)))
     (AX: NormalAxiomatization L (Build_SequentCalculus (@derivable L Gamma))),
     OpaqueProp (OpaqueProp (Typeclass_Rewrite l -> G))) <->
  OpaqueProp (Typeclass_Rewrite ((exist (fun X: Prop => X) (FiniteWitnessedSequentCalculus L Gamma) fwSC) :: l) -> G).
Proof.
  unfold OpaqueProp.
  intros.
  split; intros.
  + clear H0.
    assert (NormalSequentCalculus L (Build_SequentCalculus (@derivable L Gamma)))
      by (apply Build_SequentCalculus_SC).
    assert (FiniteWitnessedSequentCalculus L (Build_SequentCalculus (@derivable L Gamma)))
      by (destruct fwSC; constructor; auto).
    assert (NormalAxiomatization L (Build_SequentCalculus (@derivable L Gamma)))
      by (apply SequentCalculus2Axiomatization_AX).
    apply H; auto.
    apply Typeclass_Rewrite_I.
  + apply H; auto.
    apply Typeclass_Rewrite_I.
Qed.

Hint Rewrite <- @MakeAxiomatization_FiniteWitnessedSequentCalculus using (typeclasses eauto): AddAX.

Section Test_AddSC.

Context {L: Language}
        {minL: MinimunLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}.

Lemma provable_impp_refl': forall (x: expr), |-- x --> x.
Proof.
  AddSequentCalculus Gamma.
Abort.

End Test_AddSC.

Section Test_AddAX.

Context {L: Language}
        {minL: MinimunLanguage L}
        {Gamma: ProofTheory L}
        {bSC: BasicSequentCalculus L Gamma}
        {minSC: MinimunSequentCalculus L Gamma}
        {fwSC: FiniteWitnessedSequentCalculus L Gamma}.

Lemma derivable_axiom2': forall Phi (x y z: expr), Phi |-- (x --> y --> z) --> (x --> y) --> (x --> z).
Proof.
  AddAxiomatization Gamma.
Abort.

End Test_AddAX.
