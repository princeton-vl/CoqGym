Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.

Class SimpleSmallStepSemantics (P: ProgrammingLanguage) (state: Type): Type := {
  simple_step: cmd * state -> cmd * state -> Prop
}.

Definition step {P: ProgrammingLanguage} {state: Type} {SSSS: SimpleSmallStepSemantics P state} (final_state: cmd * state -> Prop) (cs: cmd * state) (mcs: MetaState (cmd * state)) :=
  match mcs with
  | Terminating cs0 => simple_step cs cs0
  | NonTerminating => False
  | Error => ~ final_state cs /\ forall cs0, ~ simple_step cs cs0
  end.
