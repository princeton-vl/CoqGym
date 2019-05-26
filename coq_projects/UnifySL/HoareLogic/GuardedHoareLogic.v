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
Require Import Logic.HoareLogic.HoareLogic.

(***************************************)
(* Type Classes                        *)
(***************************************)

Class GuardedHoareTriple
      (L: Language)
      (P: ProgrammingLanguage)
      (HLan: Language): Type :=
{
  Assertion := @expr L;
  guard: Type;
  triple: guard ->
          Assertion ->
          cmd ->
          Assertion ->
          @expr HLan
}.

Definition triple_valid
           {L: Language}
           {P: ProgrammingLanguage}
           {HLan: Language}
           {TI: Semantics HLan unit_MD}
           (t: @expr HLan): Prop :=
  @satisfies _ _ TI tt t.

(*
Notation "|==  x" := (triple_valid x) (at level 71, no associativity) : hoare_logic.
(* This notation has been used. *)
*)
Notation "{{ Inv }} {{ P }} c {{ Q }}" := (triple Inv P c Q) (at level 80, no associativity) : guarded_hoare_logic.


