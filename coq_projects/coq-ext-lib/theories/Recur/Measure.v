Require Import Coq.Classes.RelationClasses.
Require Coq.Arith.Wf_nat.

Set Implicit Arguments.
Set Strict Implicit.

Section parametric.
  Context {T U : Type}.
  Variable f : T -> U.
  Variable R : U -> U -> Prop.
  Hypothesis well_founded_R : well_founded R.

  Definition compose (a b : T) : Prop :=
    R (f a) (f b).

  Definition well_founded_compose : well_founded compose :=
    (fun t =>
       (@Fix _ R well_founded_R (fun x => forall y, f y = x -> Acc compose y)
             (fun x recur y pf =>
                @Acc_intro _ compose y (fun y' (pf' : R (f y') (f y)) =>
                                          recur _ match pf in _ = t return R (f y') t with
                                                    | eq_refl => pf'
                                                  end _ eq_refl))
             (f t) t eq_refl)).
End parametric.

(** A well-founded relation induced by a measure to nat **)
Section measure.
  Context {T : Type}.
  Variable m : T -> nat.

  Definition mlt : T -> T -> Prop :=
    compose m lt.

  Definition well_founded_mlt : well_founded mlt :=
    @well_founded_compose T nat m lt Wf_nat.lt_wf.
End measure.