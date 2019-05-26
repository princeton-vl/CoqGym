Require Import Logic.GeneralLogic.Base.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.
Require Import Logic.HoareLogic.BigStepSemantics.

(***************************************)
(* Type Classes                        *)
(***************************************)

Class HoareTriple (L: Language) (P: ProgrammingLanguage) (HLan: Language): Type := {
  Assertion := @expr L;
  triple: Assertion -> cmd -> Assertion -> @expr HLan
}.

Definition triple_valid {L: Language} {P: ProgrammingLanguage} {HLan: Language} {TI: Semantics HLan unit_MD} (t: @expr HLan): Prop := @satisfies _ _ TI tt t.

Notation "|==  x" := (triple_valid x) (at level 71, no associativity) : hoare_logic.
Notation "{{ P }} c {{ Q }}" := (triple P c Q) (at level 80, no associativity) : hoare_logic.

Local Open Scope hoare_logic.
(*
Class TripleInterpretation_Partial (L: Language) (P: ProgrammingLanguage) (HLan: Language) {HT: HoareTriple L P HLan} (MD: Model) (BSS: BigStepSemantics P model) (SM: Semantics L MD) (TI: Semantics HLan unit_MD) : Type := {
  partial_valid_spec: forall (P: Assertion) (c: cmd) (Q: Assertion),
    (|== {{ P }} c {{ Q }}) <->
    triple_partial_valid P c Q
}.

Class TripleInterpretation_Total (L: Language) (P: ProgrammingLanguage) (HLan: Language) {HT: HoareTriple L P HLan} (MD: Model) (BSS: BigStepSemantics P model) (SM: Semantics L MD) (TI: Semantics HLan unit_MD) : Type := {
  total_valid_spec: forall (P: Assertion) (c: cmd) (Q: Assertion),
    (|== {{ P }} c {{ Q }}) <->
    triple_total_valid P c Q
}.
*)