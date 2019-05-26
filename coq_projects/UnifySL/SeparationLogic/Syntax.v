Require Import Logic.GeneralLogic.Base.

Class SeparationLanguage (L: Language): Type := {
  sepcon : expr -> expr -> expr;
  wand : expr -> expr -> expr
}.

Class SeparationEmpLanguage (L: Language) {SL: SeparationLanguage L}: Type := {
  emp: expr
}.

Module SeparationLogicNotation.

Notation "x * y" := (sepcon x y) (at level 40, left associativity) : syntax.
Notation "x -* y" := (wand x y) (at level 55, right associativity) : syntax.

End SeparationLogicNotation.

