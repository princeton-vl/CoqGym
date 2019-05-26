Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.
Require Import Logic.HoareLogic.BigStepSemantics.

Definition DecorateProgram (P: ProgrammingLanguage) (hint: cmd -> Type): ProgrammingLanguage :=
  Build_ProgrammingLanguage (sigT hint).

Class ThreadLocalBigStepSemantics (P: ProgrammingLanguage) (state: Type) (guard: Type): Type := {
  hint: guard -> cmd -> Type;
  guarded_BSS: forall g: guard, BigStepSemantics (DecorateProgram P (hint g)) state
}.

Definition tl_access
           {P: ProgrammingLanguage}
           {state: Type}
           {guard: Type}
           {TLBSS: ThreadLocalBigStepSemantics P state guard}:
  forall (g: guard), state -> sigT (hint g) -> MetaState state -> Prop :=
  fun g => @access _ _ (guarded_BSS g).

Definition lift_tl_access
           {P: ProgrammingLanguage}
           {state: Type}
           {guard: Type}
           {TLBSS: ThreadLocalBigStepSemantics P state guard}:
  forall g: guard, MetaState state -> sigT (hint g) -> MetaState state -> Prop :=
  fun g => @lift_access _ _ (guarded_BSS g).
