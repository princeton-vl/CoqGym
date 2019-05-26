Require Import Logic.GeneralLogic.Base.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.BigStepSemantics.
Require Import Logic.HoareLogic.ConcurrentSemantics_Angelic.
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
           {guard: Type}
           {TLBSS: ThreadLocalBigStepSemantics P (model) guard}
           {SM: Semantics L MD}
           (Inv: guard)
           (Pre: expr)
           (c: cmd)
           (Post: expr):
  Prop :=
  exists h,
  @triple_partial_valid L _ MD (guarded_BSS Inv) SM Pre (existT _ c h) Post.

Definition guarded_triple_total_valid
           {L: Language}
           {P: ProgrammingLanguage}
           {MD: Model}
           {guard: Type}
           {TLBSS: ThreadLocalBigStepSemantics P (model) guard}
           {SM: Semantics L MD}
           (Inv: guard)
           (Pre: expr)
           (c: cmd)
           (Post: expr):
  Prop :=
  exists h,
  @triple_total_valid L _ MD (guarded_BSS Inv) SM Pre (existT _ c h) Post.
