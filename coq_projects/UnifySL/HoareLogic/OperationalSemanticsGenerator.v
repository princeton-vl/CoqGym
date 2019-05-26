Require Import Coq.omega.Omega.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.NatChoice.
Require Import Logic.lib.Stream.SigStream.
Require Import Logic.lib.Stream.StreamFunctions.
Require Import Logic.lib.Stream.StreamSplit.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.
Require Import Logic.HoareLogic.Trace.
Require Import Logic.HoareLogic.SimpleSmallStepSemantics.
Require Import Logic.HoareLogic.SmallStepSemantics.
Require Import Logic.HoareLogic.BigStepSemantics.

Module SSS_SimpleSSS.

Instance SSS_SimpleSSS
         {P: ProgrammingLanguage}
         {state: Type}
         (SSSS: SimpleSmallStepSemantics P state)
         (final_state: cmd * state -> Prop):
  SmallStepSemantics P state :=
  Build_SmallStepSemantics _ _ (SimpleSmallStepSemantics.step final_state).

End SSS_SimpleSSS.

