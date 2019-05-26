Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.omega.Omega.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Class PropositionalVariables: Type := {
  Var: Type
}.

Inductive expr {Sigma: PropositionalVariables}: Type :=
  | andp : expr -> expr -> expr
  | orp : expr -> expr -> expr
  | impp : expr -> expr -> expr
  | falsep : expr
  | sepcon : expr -> expr -> expr
  | wand : expr -> expr -> expr
  | varp : Var -> expr.

Arguments expr: clear implicits.

Instance L {Sigma: PropositionalVariables}: Language :=
  Build_Language (expr Sigma).

Instance minL {Sigma: PropositionalVariables}: MinimunLanguage L :=
  Build_MinimunLanguage L impp.

Instance pL {Sigma: PropositionalVariables}: PropositionalLanguage L :=
  Build_PropositionalLanguage L andp orp falsep.

Instance sL {Sigma: PropositionalVariables}: SeparationLanguage L :=
  Build_SeparationLanguage L sepcon wand.
