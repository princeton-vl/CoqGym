Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.ModalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.

Class CoreTransitSeparationLanguage (L: Language) {SL: SeparationLanguage L}: Type := {
  core_tr: expr -> expr
}.

Definition ct_mL (L: Language) {SL: SeparationLanguage L} {CtsGamma: CoreTransitSeparationLanguage L} : ModalLanguage L := @Build_ModalLanguage L core_tr.

Module CoreTransitNotation.

Notation "□ x" := (core_tr x) (at level 35) : syntax. (* Unicode 25a1 *)

End CoreTransitNotation.

