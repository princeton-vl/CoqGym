Require Import Logic.GeneralLogic.Base.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.BigStepSemantics.
Require Import Logic.HoareLogic.TraceSemantics.
Require Import Logic.HoareLogic.HoareTriple_BigStepSemantics.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelSingleNotation.
Import KripkeModelNotation_Intuitionistic.

Definition guarded_triple_partial_valid
           {L: Language}
           {P: ProgrammingLanguage}
           {MD: Model}
           {J: Join model}
           {R: Relation model}
           {Res: Resource}
           {Ac: Action}
           {Acr: Action_resource Ac Res}
           {TS: TraceSemantics P (resources * model) Ac}
           {SM: Semantics L MD}
           (Inv: (resource * (model -> Prop)) -> Prop)
           (Pre: expr)
           (c: cmd)
           (Post: expr):
  Prop :=
  @triple_partial_valid L _ MD (ThreadLocal_BSS TS Inv) SM Pre c Post.
