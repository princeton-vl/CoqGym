Require Import Logic.GeneralLogic.Base.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.
Require Import Logic.HoareLogic.BigStepSemantics.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelSingleNotation.
Import KripkeModelNotation_Intuitionistic.

Definition triple_partial_valid {L: Language} {P: ProgrammingLanguage} {MD: Model} {BSS: BigStepSemantics P (model)} {SM: Semantics L MD} (Pre: expr) (c: cmd) (Post: expr): Prop :=
  forall (s_pre: model) (ms_post: MetaState model),
  KRIPKE: s_pre |= Pre ->
  access s_pre c ms_post ->
  match ms_post with
  | Error => False
  | NonTerminating => True
  | Terminating s_post => KRIPKE: s_post |= Post
  end.

Definition triple_total_valid {L: Language} {P: ProgrammingLanguage} {MD: Model} {BSS: BigStepSemantics P (model)} {SM: Semantics L MD} (Pre: expr) (c: cmd) (Post: expr): Prop :=
  forall (s_pre: model) (ms_post: MetaState model),
  KRIPKE: s_pre |= Pre ->
  access s_pre c ms_post ->
  match ms_post with
  | Error => False
  | NonTerminating => False
  | Terminating s_post => KRIPKE: s_post |= Post
  end.
