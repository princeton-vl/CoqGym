Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.ModalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import ModalLanguageNotation.
Import SeparationLogicNotation.

Class PropositionalStable (L: Language) {minL: MinimunLanguage L} {pL: PropositionalLanguage L} (Gamma: ProofTheory L) (stable: expr -> Prop) := {
  impp_stable: forall x y, stable x -> stable y -> stable (x --> y);
  andp_stable: forall x y, stable x -> stable y -> stable (x && y);
  orp_stable: forall x y, stable x -> stable y -> stable (x || y);
  falsep_stable: stable FF;
  stable_proper_iffp :> Proper ((fun x y => |-- x <--> y) ==> iff) stable
}.

Class ModalStable (L: Language) {minL: MinimunLanguage L} {mL: ModalLanguage L} (Gamma: ProofTheory L) (stable: expr -> Prop) := {
  boxp_stable: forall x, stable x -> stable (boxp x)
}.

Class ModalAbsorbStable (L: Language) {minL: MinimunLanguage L} {mL: ModalLanguage L} (Gamma: ProofTheory L) (stable: expr -> Prop) := {
  boxp_absorb_stable: forall x, stable x -> |-- x --> boxp x
}.

Class SeparationStable (L: Language) {minL: MinimunLanguage L} {sL: SeparationLanguage L} (Gamma: ProofTheory L) (stable: expr -> Prop) := {
  sepcon_stable: forall x y, stable x -> stable y -> stable (x * y);
  wand_stable: forall x y, stable x -> stable y -> stable (x -* y)
}.

Class SeparationAbsorbStable (L: Language) {minL: MinimunLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} (Gamma: ProofTheory L) (stable: expr -> Prop) := {
  stable_andp_sepcon1: forall x y z, stable x -> |-- (x && y) * z <--> x && (y * z)
}.

Lemma iffp_stable {L: Language} {minL: MinimunLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {stable: expr -> Prop} {pstable: PropositionalStable L Gamma stable}:
  forall x y, stable x -> stable y -> stable (x <--> y).
Proof.
  intros.
  apply andp_stable; apply impp_stable; auto.
Qed.

Lemma truep_stable {L: Language} {minL: MinimunLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {stable: expr -> Prop} {pstable: PropositionalStable L Gamma stable}:
  stable TT.
Proof.
  apply impp_stable; apply falsep_stable.
Qed.

