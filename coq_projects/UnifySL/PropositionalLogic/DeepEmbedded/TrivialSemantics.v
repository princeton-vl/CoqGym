Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.Semantics.Trivial.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Trivial.
Require Import Logic.PropositionalLogic.DeepEmbedded.PropositionalLanguage.

Section TrivialSemantics.

Context {Sigma: PropositionalVariables}.

Existing Instances L minL pL.

Definition model: Type := Var -> Prop.

Fixpoint denotation (x: expr Sigma): Ensemble model :=
  match x with
  | andp y z => Semantics.andp (denotation y) (denotation z)
  | orp y z => Semantics.orp (denotation y) (denotation z)
  | impp y z => Semantics.impp (denotation y) (denotation z)
  | falsep => Semantics.falsep
  | varp p => fun m => m p
  end.

Instance MD: Model :=
  Build_Model model.

Instance SM: Semantics L MD :=
  Build_Semantics L MD denotation.

Instance tminSM: TrivialMinimunSemantics L MD SM.
Proof.
  constructor.
  simpl; intros.
  apply Same_set_refl.
Qed.

Instance tpSM: TrivialPropositionalSemantics L MD SM.
Proof.
  constructor.
  + simpl; intros.
    apply Same_set_refl.
  + simpl; intros.
    apply Same_set_refl.
  + simpl; intros.
    apply Same_set_refl.
Qed.

End TrivialSemantics.
