Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Class SeparationLogic_Precise
        (L: Language)
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {sL: SeparationLanguage L}
        (Gamma: ProofTheory L)
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {sGamma: SeparationLogic L Gamma} := {
  precise: expr -> Prop;
  precise_sepcon: forall x y, precise x -> precise y -> precise (x * y)
}.

(*
This rule is not sound for garbage collect SL
precise_impp: forall x y, |-- x --> y -> precise y -> precise x

The following is not sound e.g. when x := a = 0 && emp, y := a = 1, z := a = 0
sepcon_cancel: forall x y z, |-- (x * z) --> (y * z) -> precise z -> |-- (x --> y)
*)

Class SeparationLogic_PureFact
        (L: Language)
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {sL: SeparationLanguage L}
        (Gamma: ProofTheory L)
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {sGamma: SeparationLogic L Gamma} := {
  pure_fact: expr -> Prop;
  pure_falsep: pure_fact FF;
  pure_andp: forall x y, pure_fact x -> pure_fact y -> pure_fact (x && y);
  pure_orp: forall x y, pure_fact x -> pure_fact y -> pure_fact (x || y);
  pure_impp: forall x y, pure_fact x -> pure_fact y -> pure_fact (x --> y);
  pure_specon: forall x y, pure_fact x -> pure_fact y -> pure_fact (x * y);
  pure_wand: forall x y, pure_fact x -> pure_fact y -> pure_fact (x -* y);
  andp_sepcon: forall x y z, pure_fact x -> |-- (x && (y * z)) <--> ((x && y) * z)
}.

