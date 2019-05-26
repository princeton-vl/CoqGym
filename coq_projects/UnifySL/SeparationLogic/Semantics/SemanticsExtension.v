Require Import Coq.Sets.Ensembles.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.

Local Open Scope kripke_model.
Import KripkeModelNotation_Intuitionistic.

Definition cut {worlds: Type} {J: Join worlds} (m: worlds) (P: worlds -> Prop) (n: worlds) : Prop :=
  exists m', join m' n m /\ P m'.

Definition greatest_cut {worlds: Type} {R: Relation worlds} {J: Join worlds} (m: worlds) (P: worlds -> Prop) (n: worlds) : Prop :=
  cut m P n /\ (forall n', cut m P n' -> n' <= n).

Definition Kdenote_precise {worlds: Type} {R: Relation worlds} {J: Join worlds} (P: Ensemble worlds): Prop :=
  forall m n, cut m P n ->
    exists n, greatest_cut m P n.

Require Import Logic.GeneralLogic.Base.

Local Open Scope logic_base.
Import KripkeModelFamilyNotation.

Definition sem_precise
        {L: Language}
        {MD: Model}
        {kMD: KripkeModel MD}
        {M: Kmodel}
        {R: Relation (Kworlds M)}
        {J: Join (Kworlds M)}
        {SM: Semantics L MD}
        (x: expr): Prop :=
  Kdenote_precise (Kdenotation M x).
