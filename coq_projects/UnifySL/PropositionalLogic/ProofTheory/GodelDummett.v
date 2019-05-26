(* M. Dummett. A propositional calculus with denumerable matrix. J. Symbolic Logic, 24(2):97–106, 1959. *)
(* K. G¨odel. On the intuitionistic propositional calculus. In S. Feferman, J. W. D. Jr, S. C. Kleene, G. H. Moore, R. M. Solovay, and J. van Heijenoort, editors, Collected Works, volume 1. Oxford University Press, 1986. *)

Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Class GodelDummettPropositionalLogic (L: Language) {minL: MinimunLanguage L} {pL: PropositionalLanguage L} (Gamma: ProofTheory L) {minAX: MinimunAxiomatization L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} := {
  impp_choice: forall x y, |-- (x --> y) || (y --> x)
}.

Lemma MakeSequentCalculus_GodelDummettPropositionalLogic {L: Language} {minL: MinimunLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {minAX: MinimunAxiomatization L Gamma} (minAX': MinimunAxiomatization L (Build_AxiomaticProofTheory (@provable L Gamma))) (ipGamma: IntuitionisticPropositionalLogic L Gamma) {ipGamma': IntuitionisticPropositionalLogic L (Build_AxiomaticProofTheory (@provable L Gamma))} {gdpGamma: GodelDummettPropositionalLogic L Gamma}:
  Typeclass_Rewrite (exist (fun X: Prop => X) (IntuitionisticPropositionalLogic L (Build_AxiomaticProofTheory (@provable L Gamma))) ipGamma' :: nil) ->
  forall (G: Prop) (l: list (sig (fun X: Prop => X))),
  (forall
     (gdpGamma: GodelDummettPropositionalLogic L (Build_AxiomaticProofTheory (@provable L Gamma))),
     OpaqueProp (Typeclass_Rewrite l -> G)) <->
  OpaqueProp (Typeclass_Rewrite ((exist (fun X: Prop => X) (GodelDummettPropositionalLogic L Gamma) gdpGamma) :: l) -> G).
Proof.
  unfold OpaqueProp.
  intros _.
  intros.
  split; intros.
  + clear H0.
    apply H; auto.
    - destruct gdpGamma; constructor; auto.
    - apply Typeclass_Rewrite_I.
  + apply H; auto.
    apply Typeclass_Rewrite_I.
Qed.

Hint Rewrite <- @MakeSequentCalculus_GodelDummettPropositionalLogic using (instantiate (1 := _); apply Typeclass_Rewrite_I): AddSC.

Section GodelDummett.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {gdpGamma: GodelDummettPropositionalLogic L Gamma}.
(*
Lemma derivable_impp_choice: forall (Phi: context) (x y: expr),
  Phi |-- (x --> y) || (y --> x).
Proof.
  intros.
  pose proof impp_choice x.
  apply deduction_weaken0; auto.
Qed.
*)
Instance GodelDummett2DeMorgan: DeMorganPropositionalLogic L Gamma.
Proof.
  constructor.
  AddSequentCalculus Gamma.
  intros.
  rewrite provable_derivable.
  set (Phi := empty_context).
  clearbody Phi.

  pose proof impp_choice x (~~ x).
  apply deduction_weaken0 with (Phi0 := Phi) in H.

  assert (Phi |-- (x --> ~~ x) --> (x --> FF)).
  Focus 1. {
    rewrite <- deduction_theorem.
    rewrite <- deduction_theorem.
    eapply deduction_weaken with (Union _ (Union _ (Union _ Phi (Singleton _ (x --> ~~ x))) (Singleton _ x)) (Singleton _ x)).
    + intros y ?.
      destruct H0; [| right; auto].
      destruct H0; [| right; auto].
      left; auto.
    + rewrite deduction_theorem.
      rewrite deduction_theorem.
      apply derivable_assum1.
  } Unfocus.
  assert (Phi |-- (~~ x --> x) --> (~~ x --> FF)).
  Focus 1. {
    rewrite <- deduction_theorem.
    pose proof derivable_assum1 Phi (~~ x --> x).
    set (Psi := Union expr Phi (Singleton expr (~~ x --> x))) in H1 |- *; clearbody Psi.
    rewrite <- deduction_theorem in H1 |- *.
    pose proof derivable_assum1 Psi (~~ x).
    pose proof deduction_modus_ponens _ _ _ H1 H2.
    auto.
  } Unfocus.

  rewrite <- deduction_theorem in H0, H1.
  apply (deduction_orp_intros1 _ _ (~~ x --> FF)) in H0.
  apply (deduction_orp_intros2 _ (x --> FF)) in H1.
  rewrite deduction_theorem in H0, H1.
  pose proof deduction_orp_elim' _ _ _ _ H0 H1.
  pose proof deduction_modus_ponens _ _ _ H H2.
  auto.
Qed.

End GodelDummett.
