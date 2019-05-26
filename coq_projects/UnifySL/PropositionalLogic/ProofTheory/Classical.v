Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Class ClassicalPropositionalLogic (L: Language) {minL: MinimunLanguage L} {pL: PropositionalLanguage L} (Gamma: ProofTheory L) {minAX: MinimunAxiomatization L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} := {
  excluded_middle: forall x, |-- x || ~~ x
}.

Class ClassicalPropositionalSequentCalculus (L: Language) {minL: MinimunLanguage L} {pL: PropositionalLanguage L} (Gamma: ProofTheory L) {bSC: BasicSequentCalculus L Gamma} {minSC: MinimunSequentCalculus L Gamma} {ipSC: IntuitionisticPropositionalSequentCalculus L Gamma} := {
  derivable_excluded_middle: forall Phi x, Phi |-- x || ~~ x
}.

Section Axiomatization2SequentCalculus.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {cpGamma: ClassicalPropositionalLogic L Gamma}
        {SC: NormalSequentCalculus L Gamma}
        {bSC: BasicSequentCalculus L Gamma}
        {minSC: MinimunSequentCalculus L Gamma}
        {ipSC: IntuitionisticPropositionalSequentCalculus L Gamma}.

Lemma Axiomatization2SequentCalculus_cpSC: ClassicalPropositionalSequentCalculus L Gamma.
Proof.
  intros.
  constructor.
  intros.
  apply deduction_weaken0.
  apply excluded_middle.
Qed.

End Axiomatization2SequentCalculus.

Section AddSequentCalculus.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {cpGamma: ClassicalPropositionalLogic L Gamma}
        {minAX': MinimunAxiomatization L (Build_AxiomaticProofTheory (@provable L Gamma))}
        {ipGamma': IntuitionisticPropositionalLogic L (Build_AxiomaticProofTheory (@provable L Gamma))}
        {SC: NormalSequentCalculus L (Build_AxiomaticProofTheory (@provable L Gamma))}
        {bSC: BasicSequentCalculus L (Build_AxiomaticProofTheory (@provable L Gamma))}
        {minSC: MinimunSequentCalculus L (Build_AxiomaticProofTheory (@provable L Gamma))}
        {ipSC: IntuitionisticPropositionalSequentCalculus L (Build_AxiomaticProofTheory (@provable L Gamma))}.

Lemma MakeSequentCalculus_ClassicalPropositionalLogic:
  Typeclass_Rewrite (exist (fun X: Prop => X) (IntuitionisticPropositionalLogic L (Build_AxiomaticProofTheory (@provable L Gamma))) ipGamma' :: exist (fun X: Prop => X) (IntuitionisticPropositionalSequentCalculus L (Build_AxiomaticProofTheory (@provable L Gamma))) ipSC :: exist (fun X: Prop => X) (BasicSequentCalculus L (Build_AxiomaticProofTheory (@provable L Gamma))) bSC :: exist (fun X: Prop => X) (MinimunSequentCalculus L (Build_AxiomaticProofTheory (@provable L Gamma))) minSC :: nil) ->
  forall (G: Prop) (l: list (sig (fun X: Prop => X))),
  (forall
     (cpSC: ClassicalPropositionalSequentCalculus L (Build_AxiomaticProofTheory (@provable L Gamma)))
     (cpGamma: ClassicalPropositionalLogic L (Build_AxiomaticProofTheory (@provable L Gamma))),
     OpaqueProp (Typeclass_Rewrite l -> G)) <->
  OpaqueProp (Typeclass_Rewrite ((exist (fun X: Prop => X) (ClassicalPropositionalLogic L Gamma) cpGamma) :: l) -> G).
Proof.
  unfold OpaqueProp.
  intros _.
  intros.
  split; intros.
  + clear H0.
    assert (ClassicalPropositionalLogic L (Build_AxiomaticProofTheory provable))
      by (destruct cpGamma; constructor; auto).
    apply H; auto.
    - apply Axiomatization2SequentCalculus_cpSC.
    - apply Typeclass_Rewrite_I.
  + apply H; auto.
    apply Typeclass_Rewrite_I.
Qed.

End AddSequentCalculus.

Hint Rewrite <- @MakeSequentCalculus_ClassicalPropositionalLogic using first [typeclasses eauto | instantiate (1 := _); instantiate (1 := _); instantiate (1 := _); instantiate_must_succeed; apply Typeclass_Rewrite_I]: AddSC.

Section SequentCalculus2Axiomatization.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: ProofTheory L}
        {SC: NormalSequentCalculus L Gamma}
        {bSC: BasicSequentCalculus L Gamma}
        {minSC: MinimunSequentCalculus L Gamma}
        {ipSC: IntuitionisticPropositionalSequentCalculus L Gamma}
        {cpSC: ClassicalPropositionalSequentCalculus L Gamma}
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}.

Lemma SequentCalculus2Axiomatization_cpGamma: ClassicalPropositionalLogic L Gamma.
Proof.
  intros.
  constructor.
  intros.
  rewrite provable_derivable.
  apply derivable_excluded_middle.
Qed.

End SequentCalculus2Axiomatization.

Section AddAxiomatization.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: ProofTheory L}
        {bSC: BasicSequentCalculus L Gamma}
        {minSC: MinimunSequentCalculus L Gamma}
        {ipSC: IntuitionisticPropositionalSequentCalculus L Gamma}
        {cpSC: ClassicalPropositionalSequentCalculus L Gamma}
        {minAX: MinimunAxiomatization L (Build_SequentCalculus (@derivable L Gamma))}
        {ipGamma: IntuitionisticPropositionalLogic L (Build_SequentCalculus (@derivable L Gamma))}
        {SC': NormalSequentCalculus L (Build_SequentCalculus (@derivable L Gamma))}
        {bSC': BasicSequentCalculus L (Build_SequentCalculus (@derivable L Gamma))}
        {minSC': MinimunSequentCalculus L (Build_SequentCalculus (@derivable L Gamma))}
        {ipSC': IntuitionisticPropositionalSequentCalculus L (Build_SequentCalculus (@derivable L Gamma))}.

Lemma MakeAxiomatization_ClassicalPropositionalSequentCalculus:
  Typeclass_Rewrite (exist (fun X: Prop => X) (IntuitionisticPropositionalLogic L (Build_SequentCalculus (@derivable L Gamma))) ipGamma :: exist (fun X: Prop => X) (IntuitionisticPropositionalSequentCalculus L (Build_SequentCalculus (@derivable L Gamma))) ipSC' :: exist (fun X: Prop => X) (BasicSequentCalculus L (Build_SequentCalculus (@derivable L Gamma))) bSC' :: exist (fun X: Prop => X) (MinimunSequentCalculus L (Build_SequentCalculus (@derivable L Gamma))) minSC' :: nil) ->
  forall (G: Prop) (l: list (sig (fun X: Prop => X))),
  (forall
     (cpSC: ClassicalPropositionalSequentCalculus L (Build_SequentCalculus (@derivable L Gamma)))
     (cpGamma: ClassicalPropositionalLogic L (Build_SequentCalculus (@derivable L Gamma))),
     OpaqueProp (Typeclass_Rewrite l -> G)) <->
  OpaqueProp (Typeclass_Rewrite ((exist (fun X: Prop => X) (ClassicalPropositionalSequentCalculus L Gamma) cpSC) :: l) -> G).
Proof.
  unfold OpaqueProp.
  intros _.
  intros.
  split; intros.
  + clear H0.
    assert (ClassicalPropositionalSequentCalculus L (Build_SequentCalculus (@derivable L Gamma)))
      by (destruct cpSC; constructor; auto).
    apply H; auto.
    - apply SequentCalculus2Axiomatization_cpGamma.
    - apply Typeclass_Rewrite_I.
  + apply H; auto.
    apply Typeclass_Rewrite_I.
Qed.

End AddAxiomatization.

Hint Rewrite <- @MakeAxiomatization_ClassicalPropositionalSequentCalculus using first [typeclasses eauto | instantiate (1 := _); instantiate (1 := _); instantiate (1 := _); instantiate_must_succeed; apply Typeclass_Rewrite_I]: AddAX.

Section DerivableRulesFromAxiomatization1.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {cpGamma: ClassicalPropositionalLogic L Gamma}.

Lemma double_negp_elim: forall (x: expr),
  |-- ~~ (~~ x) --> x.
Proof.
  AddSequentCalculus Gamma.
  intros.
  unfold negp.
  pose proof orp_elim x (x --> FF) (((x --> FF) --> FF) --> x).
  pose proof axiom1 x ((x --> FF) --> FF).
  pose proof modus_ponens _ _ H H0.
  clear H H0.

  pose proof derivable_contradiction_elim empty_context (x --> FF) x.
  rewrite <- provable_derivable in H.
  pose proof modus_ponens _ _ H1 H.
  clear H H1.

  pose proof excluded_middle x.
  pose proof modus_ponens _ _ H0 H.
  auto.
Qed.

Lemma double_negp: forall (x: expr),
  |-- ~~ (~~ x) <--> x.
Proof.
  AddSequentCalculus Gamma.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros;
  rewrite <- provable_derivable.
  + apply double_negp_elim.
  + apply double_negp_intros.
Qed.

Instance Classical2GodelDummett: GodelDummettPropositionalLogic L Gamma.
Proof.
  constructor.
  AddSequentCalculus Gamma.
  intros.
  rewrite provable_derivable.
  set (Phi := empty_context).
  clearbody Phi.
  pose proof excluded_middle x.
  apply deduction_weaken0 with (Phi0 := Phi) in H.
  eapply deduction_modus_ponens; [exact H |].
  apply deduction_orp_elim'.
  + rewrite <- deduction_theorem.
    apply deduction_orp_intros2.
    rewrite deduction_theorem.
    apply derivable_axiom1.
  + rewrite <- deduction_theorem.
    apply deduction_orp_intros1.
    rewrite deduction_theorem.
    apply deduction_impp_arg_switch.
    apply derivable_contradiction_elim.
Qed.

Lemma contrapositiveNN: forall (x y: expr),
  |-- (~~ y --> ~~ x) --> (x --> y).
Proof.
  AddSequentCalculus Gamma.
  intros.
  rewrite <- (double_negp_elim y) at 2.
  rewrite provable_derivable.
  rewrite <- deduction_theorem.
  apply deduction_contrapositivePN.
  solve_assum.
Qed.

Lemma contrapositiveNP: forall (x y: expr),
  |-- (~~ y --> x) --> (~~ x --> y).
Proof.
  AddSequentCalculus Gamma.
  intros.
  rewrite <- (contrapositiveNN (~~ x) y).
  rewrite <- (double_negp_intros x).
  apply provable_impp_refl.
Qed.

End DerivableRulesFromAxiomatization1.

Section DerivableRulesFromSequentCalculus.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: ProofTheory L}
        {bSC: BasicSequentCalculus L Gamma}
        {minSC: MinimunSequentCalculus L Gamma}
        {ipSC: IntuitionisticPropositionalSequentCalculus L Gamma}
        {cpSC: ClassicalPropositionalSequentCalculus L Gamma}.

Lemma deduction_contrapositiveNN: forall Phi (x y: expr),
  Phi |-- ~~ y --> ~~ x ->
  Phi |-- x --> y.
Proof.
  AddAxiomatization Gamma.
  intros.
  rewrite <- contrapositiveNN.
  auto.
Qed.

Lemma deduction_contrapositiveNP: forall Phi (x y: expr),
  Phi |-- ~~ y --> x ->
  Phi |-- ~~ x --> y.
Proof.
  AddAxiomatization Gamma.
  intros.
  rewrite <- contrapositiveNP.
  auto.
Qed.

End DerivableRulesFromSequentCalculus.

Section DerivableRulesFromAxiomatization2.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {cpGamma: ClassicalPropositionalLogic L Gamma}.

Lemma impp2orp: forall (x y: expr),
  |-- (x --> y) <--> (~~ x || y).
Proof.
  AddSequentCalculus Gamma.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + rewrite <- deduction_theorem.
    apply (deduction_modus_ponens _ (x || ~~ x)); [apply derivable_excluded_middle |].
    apply deduction_orp_elim'.
    - rewrite <- deduction_theorem.
      apply deduction_orp_intros2.
      rewrite -> deduction_theorem.
      apply derivable_assum1.
    - rewrite <- deduction_theorem.
      apply deduction_orp_intros1.
      apply derivable_assum1.
  + apply deduction_orp_elim'.
    - rewrite <- deduction_theorem.
      rewrite <- deduction_theorem.
      apply deduction_falsep_elim.
      rewrite -> deduction_theorem.
      apply derivable_assum1.
    - apply derivable_axiom1.
Qed.

End DerivableRulesFromAxiomatization2.

