Require Export Lci.
Require Export misc.
Require Export Arith.
Require Export groups.
Require Export rings.
Require Export ZArith.
Require Import Omega.

(* Addition on Z, (Z, +) is a group *)

Definition IdZ (x : Z) := True.

Theorem Z_group : is_group Z IdZ Zplus 0%Z Zopp.
Proof.
split.
red in |- *; trivial.
split.
red in |- *; auto with zarith.
split; red in |- *.
split; auto with zarith.
unfold IdZ in |- *; trivial.
split; auto with zarith.
Qed.

(* Multiplication on Z, (Z, +, *, 0, 1) is a unitary commutative ring *)

Theorem Z_ring : is_ring Z IdZ Zplus Zmult 0%Z Zopp.
Proof.
unfold is_ring in |- *.
split.
red in |- *; auto with zarith.
split. exact Z_group.
split. unfold intern in |- *. intros. exact I.
split; red in |- *; auto with zarith.
Qed.

Theorem Z_unitary_commutative_ring :
 is_unitary_commutative_ring Z IdZ Zplus Zmult 0%Z 1%Z Zopp.
Proof.
unfold is_unitary_commutative_ring in |- *.
split. exact Z_ring.
split.
red in |- *; auto with zarith.
split.
unfold IdZ in |- *; trivial.
split; auto with zarith.
Qed.

(* Z is an integral domain *)

Theorem integrityZ : integrity Z Zmult 0%Z.
Proof.
unfold integrity in |- *.
intros a b; elim a.
(* OZ *)
intros; left; reflexivity.
(* pos n *)
intros; right.
generalize H; clear H; simpl in |- *; case b; intros; inversion H; trivial.
(* neg n *)
intros; right.
generalize H; clear H; simpl in |- *; case b; intros; inversion H; trivial.
Qed.

Lemma inversibleZ :
 forall x : Z, inversible Z Zmult 1%Z x -> x = 1%Z \/ x = (-1)%Z.
Proof.
unfold inversible in |- *.
intros.
inversion_clear H.
inversion_clear H0.
clear H1.
generalize H; clear H.
(* [x>0] *)
elim (Z_lt_ge_dec 0 x); intros. 
left.
elim (Z_le_lt_eq_dec 1 x); auto with zarith; intros.
cut (1 > x0)%Z; intros.
absurd (0 < x0)%Z; intros; auto with zarith.
apply Zgt_lt.
apply Zmult_gt_0_reg_l with x; auto with zarith.
apply Zmult_gt_reg_r with x; auto with zarith.
rewrite Zmult_1_l; rewrite Zmult_comm; auto with zarith.
(*[x<0] *)
elim (Z_le_lt_eq_dec x 0); auto with zarith; intros.
clear b.
right.
elim (Z_le_lt_eq_dec 1 (- x)); auto with zarith; intros.
cut (1 > - x0)%Z; intros.
absurd (0 < - x0)%Z; intros; auto with zarith.
apply Zgt_lt.
apply Zmult_gt_0_reg_l with (- x)%Z; auto with zarith.
rewrite Zopp_mult_distr_l_reverse; rewrite <- Zopp_mult_distr_r;
 auto with zarith.
apply Zmult_gt_reg_r with (- x)%Z; auto with zarith.
rewrite Zmult_1_l; rewrite Zmult_comm.
rewrite Zopp_mult_distr_l_reverse; rewrite <- Zopp_mult_distr_r;
 auto with zarith.
(* [x=0] *)
rewrite b0 in H; simpl in H; inversion H.
Qed.
