Require Import Coq.PArith.BinPos.
Require Import ExtLib.Core.RelDec.

Set Implicit Arguments.
Set Strict Implicit.

(* Decidable Instances *)
Global Instance RelDec_peq : RelDec (@eq positive) :=
{ rel_dec := Pos.eqb }.

Global Instance RelDec_plt : RelDec (Pos.lt) :=
{ rel_dec := Pos.ltb }.

Global Instance RelDec_ple : RelDec (Pos.le) :=
{ rel_dec := Pos.leb }.

Global Instance RelDec_pgt : RelDec (Pos.gt) :=
{ rel_dec := fun x y => negb (Pos.leb x y) }.

Global Instance RelDec_pge : RelDec (Pos.ge) :=
{ rel_dec := fun x y => negb (Pos.ltb x y) }.

Global Instance RelDec_Correct_peq : RelDec_Correct RelDec_peq.
Proof.
  constructor; simpl. intros.
  apply Pos.eqb_eq.
Qed.

Global Instance RelDec_Correct_plt : RelDec_Correct RelDec_plt.
Proof.
  constructor; simpl; intros.
  apply Pos.ltb_lt.
Qed.

Global Instance RelDec_Correct_ple : RelDec_Correct RelDec_ple.
Proof.
  constructor; simpl; intros.
  apply Pos.leb_le.
Qed.

Global Instance RelDec_Correct_pgt : RelDec_Correct RelDec_pgt.
Proof.
  constructor; simpl; intros.
  unfold rel_dec; simpl.
  rewrite <- Pos.ltb_antisym. rewrite Pos.ltb_lt.
  intuition; [ apply Pos.lt_gt | apply Pos.gt_lt ]; auto.
Qed.

Global Instance RelDec_Correct_pge : RelDec_Correct RelDec_pge.
Proof.
  constructor; simpl. intros.
  unfold rel_dec; simpl.
  rewrite <- Pos.leb_antisym. rewrite Pos.leb_le.
  intuition; [ apply Pos.le_ge | apply Pos.ge_le ]; auto.
Qed.

Export Coq.PArith.BinPos.
