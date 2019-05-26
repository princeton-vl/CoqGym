Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.

Class ModalLanguage (L: Language): Type := {
  boxp : expr -> expr
}.

Definition diamondp {L: Language} {minL: MinimunLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L}: expr -> expr :=
  fun x => negp (boxp (negp x)).

Module ModalLanguageNotation.

Notation "□ x" := (boxp x) (at level 35) : syntax. (* Unicode 25a1 *)
Notation "◇ x" := (diamondp x) (at level 35) : syntax. (* Unicode 25c7 *)

End ModalLanguageNotation.

