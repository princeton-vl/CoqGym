Require Import ExtLib.Core.Type.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Proper.

Set Implicit Arguments.
Set Strict Implicit.

Global Instance RelDec_eq_unit : RelDec (@eq unit) :=
{ rel_dec := fun _ _ => true }.
Global Instance RelDec_Correct_eq_unit : RelDec_Correct RelDec_eq_unit.
  constructor. destruct x; destruct y; auto; simpl. intuition.
Qed.

Global Instance type_unit : type unit :=
{ equal := fun _ _ => True 
; proper := fun _ => True
}.

Global Instance typeOk_N : typeOk type_unit.
Proof.
  constructor; compute; auto.
Qed.

Global Instance proper_tt (x : unit) : proper x.
Proof.
  exact I.
Qed.