Require Export Coq.Sets.Ensembles.
Require Export Coq.Lists.List.
Require Import Logic.lib.Coqlib.

Class Language: Type := {
  expr: Type
}.

Definition context {L: Language}: Type := expr -> Prop. (* better to be (Ensemble model) if Ensemble is polymorphic *)

Definition empty_context {L: Language}: context := Empty_set _.

Class ProofTheory (L: Language): Type := {
  provable: expr -> Prop;
  derivable: context -> expr -> Prop
}.

Class Model: Type := {
  model: Type
}.

Class Semantics (L: Language) (MD: Model): Type := {
  denotation: expr -> model -> Prop (* better to be (expr -> Ensemble model) if Ensemble is polymorphic *)
}.

Definition satisfies {L: Language} {MD: Model} {SM: Semantics L MD}: model -> expr -> Prop :=
  fun (m: model) (x: expr) => denotation x m.

Definition ModelClass (MD: Model) := model -> Prop.

Class KripkeModel (MD: Model): Type := {
  Kmodel: Type;
  Kworlds: Kmodel -> Type;
  build_model: forall M: Kmodel, Kworlds M -> model
}.

Definition Kdenotation {L: Language} {MD: Model} {kMD: KripkeModel MD} (M: Kmodel) {SM: Semantics L MD}: expr -> Ensemble (Kworlds M) := fun x m => denotation x (build_model M m).

Definition unit_MD: Model := Build_Model unit.

Definition unit_kMD (MD: Model): KripkeModel MD :=
  Build_KripkeModel MD unit (fun _ => model) (fun _ m => m).

Definition AllModel (MD: Model): ModelClass MD := fun _ => True.

Inductive KripkeModelClass (MD: Model) {kMD: KripkeModel MD} (H: Kmodel -> Prop): ModelClass MD :=
| Build_KripkeModelClass: forall (M: Kmodel) (m: Kworlds M), H M -> KripkeModelClass MD H (build_model M m).

Definition consistent {L: Language} {Gamma: ProofTheory L}: context -> Prop :=
  fun Phi =>
    exists x: expr, ~ derivable Phi x.

Definition satisfiable {L: Language} {MD: Model} {SM: Semantics L MD}: ModelClass MD -> context -> Prop :=
  fun MC Phi =>
    exists m: model, MC m /\ forall x: expr, Phi x -> satisfies m x.

Definition consequence {L: Language} {MD: Model} {MD: Model} {SM: Semantics L MD}: ModelClass MD -> context -> expr -> Prop :=
  fun MC Phi y =>
    forall m: model, MC m -> (forall x, Phi x -> satisfies m x) -> satisfies m y.

Definition valid {L: Language} {MD: Model} {SM: Semantics L MD}: ModelClass MD -> expr -> Prop :=
  fun MC x =>
    forall m: model, MC m -> satisfies m x.

Definition sound {L: Language} (Gamma: ProofTheory L) {MD: Model} (SM: Semantics L MD) (MC: ModelClass MD): Prop :=
  forall x: expr, provable x -> valid MC x.

Definition weakly_complete {L: Language} (Gamma: ProofTheory L) {MD: Model} (SM: Semantics L MD) (MC: ModelClass MD): Prop :=
  forall x: expr, valid MC x -> provable x.

Definition strongly_complete {L: Language} (Gamma: ProofTheory L) {MD: Model} (SM: Semantics L MD) (MC: ModelClass MD): Prop :=
  forall (Phi: context) (x: expr), consequence MC Phi x -> derivable Phi x.

Notation "m  |=  x" := (satisfies m x) (at level 70, no associativity) : logic_base.
Notation "|--  x" := (provable x) (at level 71, no associativity) : logic_base.
Notation "Phi  |--  x" := (derivable Phi x) (at level 70, no associativity) : logic_base.
Notation "Phi ;; x" := (Union _ Phi (Singleton _ x)) (at level 69, left associativity) : logic_base.

Module KripkeModelFamilyNotation.
Notation "'KRIPKE:'  M , m" := (build_model M m) (at level 59, no associativity) : kripke_model.
End KripkeModelFamilyNotation.

Module KripkeModelSingleNotation.
Notation "'KRIPKE:'  m" := (@build_model _ (unit_kMD _) tt m) (at level 59, no associativity) : kripke_model.
End KripkeModelSingleNotation.

Module KripkeModelClass.

Definition kripke_model_class_join {MD: Model} {kMD: KripkeModel MD} (X Y: Kmodel -> Prop): Kmodel -> Prop := fun M => X M /\ Y M.

Notation "x + y" := (kripke_model_class_join x y) : kripke_model_class.

End KripkeModelClass.

