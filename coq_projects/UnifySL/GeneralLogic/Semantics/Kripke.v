Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.

Local Open Scope logic_base.
Local Open Scope kripke_model.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

(* TODO: This should be reformulated. Add a typeclass called kiMD: KripkeIntuitionisticModel, so that on every model, a preorder relation is defined. *)
Class KripkeIntuitionisticSemantics (L: Language) (MD: Model) {kMD: KripkeModel MD} (M: Kmodel) {R: Relation (Kworlds M)} (SM: Semantics L MD) : Type := {
  denote_closed: forall x, upwards_closed_Kdenote (Kdenotation M x)
}.

Lemma sat_mono {L: Language} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: Relation (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM}: forall m n x, m <= n -> KRIPKE: M , m |= x -> KRIPKE: M , n |= x.
Proof.
  intros ? ? ? ?.
  unfold satisfies.
  apply (denote_closed x); auto.
Qed.

