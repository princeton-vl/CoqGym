(* 
   Copyright 2001, 2009 Luc Rutten

   This file is part of ModRed.

   ModRed is free software: you can redistribute it and/or modify
   it under the terms of the GNU Lesser General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   ModRed is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public License
   along with ModRed.  If not, see <http://www.gnu.org/licenses/>.
*)

(* Unsigned arithmetic where w denotes a processor's word size. *)

(* Defines plusw (addition), minusw (subtraction), multw (low-word multiplication),
   uhwm (high-word multiplication), multp2 (left shift, or multiplication by a power of two),
   ursh (right shift, or division by a power of two), and ltw (comparison and choice).
*)

(* Coq 8.2 *)

Require Import ZArith.

Require Import preparation.

Open Scope Z_scope.

(*
Lemma is_in_Zpls_64 : in_Zpls 64.

  unfold in_Zpls. omega. Qed.

Definition in_Zpls_64 := exist in_Zpls 64 is_in_Zpls_64.

Definition w_def : Zpls.

  exact in_Zpls_64. Qed.
*)
Variable w_def : Zpls.

Definition w := proj1_sig w_def.

(* Defining w like this is not as elegant as using a Variable in {w:Z | `2 < w`} but 
   it allows easier splitting of modules because w does not have to be used as a parameter.
   When w_def is replaced with a Transparent definition, it also enables
   performing "real" computations.
*)

Lemma lt_0_w : 0 < w.

  unfold w. case w_def. trivial. Qed.

Lemma le_0_w : 0 <= w.

  apply Zlt_le_weak. exact lt_0_w. Qed.

Lemma lt02w : 0 < 2 ^ w.

  apply lt_0_Zpow. exact le_0_w. Qed.

Lemma zero_is_in_Z_ : in_Z_ (2 ^ w) 0.

  unfold in_Z_. split. omega. exact lt02w. Qed.

Definition zero_in_Z_ := exist (in_Z_ (2 ^ w)) 0 zero_is_in_Z_.

Lemma Zpow_2_w_is_2Zpow_2_wm1 : 2 ^ w = 2 ^ (w - 1) + 2 ^ (w - 1).

  transitivity (2 ^ (1 + (w - 1))). rewrite Zplus_minus. trivial. rewrite Zpower_exp.
  ring. omega. cut (0 < w). omega. exact lt_0_w. Qed.

Lemma lt_2wm1_2w : 2 ^ (w - 1) < 2 ^ w.

  rewrite Zpow_2_w_is_2Zpow_2_wm1. cut (0 < 2 ^ (w - 1)). omega. apply lt_0_Zpow. cut (0 < w). omega.
  exact lt_0_w. Qed.

Lemma mod_in_Z__ : forall z : Z, in_Z_ (2 ^ w) (z mod 2 ^ w).

  intro z. unfold in_Z_. split. apply Zmod_le_0_z. exact lt02w. apply Zmod_lt_z_m.
  exact lt02w. Qed.

Lemma is_in_Z_R_ursh : forall (x : Z_ (2 ^ w)) (i : Z_ w), in_Z_ (2 ^ w) (x / 2 ^ i).

  intros x i. unfold in_Z_. split. apply Zle_0_div. apply le_0__Z. apply lt_0_Zpow. apply le_0__Z. 
  apply Zle_lt_trans with ((2 ^ w - 1) / 2 ^ i). apply Zdiv_le. apply lt_0_Zpow. apply le_0__Z. 
  cut (x < 2 ^ w). omega. apply lt_z__Z. apply Zle_lt_trans with ((2 ^ w - 1) / 2 ^ 0). 
  apply Zdiv_den_le. cut (0 < 2 ^ w). omega. exact lt02w. replace (2 ^ 0) with 1. omega. trivial. 
  apply Zle_pow_le. omega. apply le_0__Z. replace (2 ^ 0) with 1.
  replace (2 ^ w - 1) with ((2 ^ w - 1) * 1). rewrite Z_div_mult. omega. omega. ring. trivial. Qed.

Lemma is_in_Z_R_uhwm : forall x y : Z_ (2 ^ w), in_Z_ (2 ^ w) (x * y / 2 ^ w).

  intros x y. unfold in_Z_. split. apply Zle_0_div. apply Zmult_le_0_compat; apply le_0__Z. 
  exact lt02w. apply Zle_lt_trans with (x * 2 ^ w / 2 ^ w). apply Zdiv_le. exact lt02w.
  apply Zmult_le_compat_l. apply Zlt_le_weak. apply lt_z__Z. apply le_0__Z. rewrite Z_div_mult.
  apply lt_z__Z. apply Zlt_gt. exact lt02w. Qed.

(* <KEEP TOGETHER - plusminustimesuhwm *)
Definition plusw (x y : Z_ (2 ^ w)) :=
  exist (in_Z_ (2 ^ w)) ((x + y) mod 2 ^ w)
             (mod_in_Z__ (x + y)).

Definition minusw (x y : Z_ (2 ^ w)) :=
  exist (in_Z_ (2 ^ w)) ((x - y) mod 2 ^ w) (mod_in_Z__ (x - y)).

Definition multw (x y : Z_ (2 ^ w)) :=
  exist (in_Z_ (2 ^ w)) (x * y mod 2 ^ w) (mod_in_Z__ (x * y)).

Definition uhwm (x y : Z_ (2 ^ w)) :=
  exist (in_Z_ (2 ^ w)) (x * y / 2 ^ w) (is_in_Z_R_uhwm x y).
(* KEEP TOGETHER> - plusminustimesuhwm *)

(* <KEEP TOGETHER - shifts *)
Definition multp2 (x : Z_ (2 ^ w)) (i : Z_ w) := 
  exist (in_Z_ (2 ^ w)) (2 ^ i * x mod 2 ^ w) (mod_in_Z__ (2 ^ i * x)).

Definition ursh (x : Z_ (2 ^ w)) (i : Z_ w) := 
  exist (in_Z_ (2 ^ w)) (x / 2 ^ i) (is_in_Z_R_ursh x i).
(* KEEP TOGETHER> - shifts *)

(* <KEEP TOGETHER - ltw *)
Definition ltw (x y t e : Z_ (2 ^ w)) :=
  If (Zlt_bool x y) t e.
(* KEEP TOGETHER> - ltw *)

Lemma Z_from_plusw : forall (x y : Z_ (2 ^ w)), _Z (plusw x y) = (x + y) mod (2 ^ w).

  trivial. Qed.

Lemma Z_from_multw : forall x y : Z_ (2 ^ w), _Z (multw x y) = x * y mod 2 ^ w.

  trivial. Qed.

Lemma Z_from_minusw : forall x y : Z_ (2 ^ w), _Z (minusw x y) = Zmod (x - y) (2 ^ w).

  trivial. Qed.

Lemma Z_from_multp2 : forall (x : Z_ (2 ^ w)) (i : Z_ w),
  _Z (multp2 x i) = Zmod (2 ^ i * x) (2 ^ w).

  trivial. Qed.

Lemma uhwm_eq : forall x y : Z_ (2 ^ w), _Z (uhwm x y) = (x * y) / 2 ^ w.

  trivial. Qed.

Lemma ltw_true : forall x y t e : Z_ (2 ^ w), x < y -> ltw x y t e = t.


  unfold ltw. unfold Zlt_bool. unfold Zlt. intros x y t e H. rewrite H.
  trivial. Qed.

Lemma ltw_false : forall x y t e : Z_ (2 ^ w), y <= x -> ltw x y t e = e.

  intros x y t e H. unfold ltw. unfold Zlt_bool. cut (x >= y). unfold Zge.
  case (x ?= y). trivial. intro H0. absurd (Lt <> Lt). auto. assumption.
  trivial. omega. Qed.

Close Scope Z_scope.
