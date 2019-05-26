(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(**
   gcd.
   Greatest common divisor.
   
   @author Olga Caprotti and Martijn Oostdijk
   @version $Revision$
 *)

Require Import ZArith.
Require Import Wf_nat.

Require Import lemmas.
Require Import natZ.
Require Import divides.
Require Import modulo.

(** * Linear combinations. *)

Definition LinComb (c x y : Z) :=
  exists a : Z, (exists b : Z, c = (x * a + y * b)%Z).

Definition LinCombMod (c x y : Z) (n : nat) :=
  exists a : Z, (exists b : Z, Mod c (x * a + y * b) n).

Definition ZLinCombMod (c x y n : Z) :=
  exists a : Z, (exists b : Z, ZMod c (x * a + y * b) n).

Lemma lincombmodzlincombmod :
 forall (c x y : Z) (n : nat),
 LinCombMod c x y n -> ZLinCombMod c x y (Z_of_nat n).
Proof.
   unfold LinCombMod, ZLinCombMod in |- *.
   intros. elim H. intros z Hz. exists z.
   elim Hz. intros b Hb. exists b.
   apply modzmod. assumption.
Qed.

Lemma zlincombmodlincombmod :
 forall c x y n : Z, ZLinCombMod c x y n -> LinCombMod c x y (Zabs_nat n).
Proof.
   unfold ZLinCombMod, LinCombMod in |- *.
   intros. elim H. intros a Ha. exists a.
   elim Ha. intros b Hb. exists b.
   apply zmodmod. assumption.
Qed.

(** * Greatest common divisor. *)

Definition common_div (x y : Z) (d : nat) :=
  Divides d (Zabs_nat x) /\ Divides d (Zabs_nat y).

Definition gcd (x y : Z) (d : nat) :=
  common_div x y d /\ (forall e : nat, common_div x y e -> e <= d).

Lemma gcd_unq :
 forall (d1 d2 : nat) (x y : Z), gcd x y d1 -> gcd x y d2 -> d1 = d2.
Proof.
   unfold gcd in |- *.
   intros.
   elim H.
   elim H0.
   intros.
   apply le_antisym.
   apply H2.
   assumption.
   apply H4.
   assumption.
Qed.

Lemma gcd_sym : forall (d : nat) (x y : Z), gcd x y d -> gcd y x d.
Proof.
   unfold gcd in |- *. unfold common_div in |- *. intros.
   elim H. intros. elim H0. intros.
   split. split.
   assumption. assumption.
   intros.
   elim H4. intros. apply H1. split.
   assumption. assumption.
Qed.

Lemma gcd_opp_l : forall (d : nat) (x y : Z), gcd x y d -> gcd (- x) y d.
Proof.
   unfold gcd in |- *. unfold common_div in |- *. intros.
   elim H. intros. elim H0. intros.
   split.
   split.
   rewrite <- abs_opp.
   assumption.
   assumption.
   intros.
   elim H4. intros.
   apply H1. split.
   rewrite abs_opp.
   assumption.
   assumption.
Qed.

Lemma gcd_opp_r : forall (d : nat) (x y : Z), gcd x y d -> gcd x (- y) d.
Proof.
   unfold gcd in |- *. unfold common_div in |- *. intros.
   elim H. intros. elim H0. intros.
   split.
   split.
   assumption.
   rewrite <- abs_opp.
   assumption.
   intros.
   elim H4. intros.
   apply H1. split.
   assumption.
   rewrite abs_opp.
   assumption.
Qed.

Lemma gcd_0_l : forall d : nat, d > 0 -> gcd 0 (Z_of_nat d) d.
Proof.
   unfold gcd in |- *. unfold common_div in |- *.
   split. split.
   split with 0. simpl in |- *. rewrite <- mult_n_O. reflexivity.
   split with 1. simpl in |- *. rewrite <- mult_n_Sm.
   rewrite <- mult_n_O. simpl in |- *. rewrite abs_inj. reflexivity.
   intros.
   apply div_le.
   assumption.
   elim H0. intros.
   rewrite abs_inj in H2. assumption.
Qed.

Lemma gcd_0_r : forall d : nat, d > 0 -> gcd (Z_of_nat d) 0 d.
Proof.
   intros. apply gcd_sym. apply gcd_0_l. assumption.
Qed.

(** * Euclid's theorem. *)

Lemma euclid_gcd1 :
 forall (d : nat) (x y q r : Z), gcd x y d -> x = (q * y + r)%Z -> gcd r y d.
Proof.
   unfold gcd in |- *. unfold common_div in |- *. intros.
   elim H. intros.
   elim H1. intros.
   split.
   split.
   rewrite <- (abs_inj d). apply zdivdiv.
   apply zdiv_plus_r with (q * y)%Z.
   rewrite Zmult_comm. apply zdiv_mult_compat_l.
   apply divzdiv. rewrite abs_inj. assumption.
   rewrite <- H0. apply divzdiv. rewrite abs_inj. assumption.
   assumption.
   intros.
   elim H5. intros.
   apply H2.
   split.
   rewrite <- (abs_inj e). apply zdivdiv.
   rewrite H0.
   apply zdiv_plus_compat.
   rewrite Zmult_comm. apply zdiv_mult_compat_l.
   apply divzdiv. rewrite abs_inj.
   assumption.
   apply divzdiv. rewrite abs_inj.
   assumption.
   assumption.
Qed.

Theorem euclid_gcd :
 forall (d1 d2 : nat) (x y q r : Z),
 x = (q * y + r)%Z -> gcd x y d1 -> gcd r y d2 -> d1 = d2.
Proof.
   intros.
   apply (gcd_unq d1 d2 r y).
   apply euclid_gcd1 with x q.
   assumption.
   assumption.
   assumption.
Qed.

(** * Greatest common divisor can be written as linear combination. *)

Lemma gcd_lincomb_nat :
 forall x y d : nat,
 x > 0 ->
 gcd (Z_of_nat x) (Z_of_nat y) d ->
 LinComb (Z_of_nat d) (Z_of_nat x) (Z_of_nat y).
Proof.
   unfold LinComb in |- *. intro x.
   apply (lt_wf_ind x). intros X IH. intros.
   elim (div_rem X y). intro q. intros. elim H1.
   intro r. case r.

   (* case r = 0 *)
   intros.
   elim H2. intros. elim H4. intros.
   rewrite <- plus_n_O in H6.
   split with 1%Z. split with 0%Z.
   rewrite <- Zmult_0_r_reverse. rewrite <- Zplus_0_r_reverse.
   rewrite Zmult_comm. rewrite Zmult_1_l.
   apply Znat.inj_eq.
   apply (euclid_gcd d X (Z_of_nat y) (Z_of_nat X) (Z_of_nat q) 0).
   rewrite <- Zplus_0_r_reverse. rewrite <- Znat.inj_mult. apply Znat.inj_eq. assumption.
   apply gcd_sym. assumption. apply gcd_0_l. assumption.

   (* case r > 0 *)
   intro r1. intros.
   elim H2. intros. elim H4. intros.
   elim (IH (S r1) H5 X d).
   intro delta. intros. elim H7. intro gamma. intros.
   split with (gamma - Z_of_nat q * delta)%Z. split with delta.
   rewrite H6. rewrite H8.
   unfold Zminus in |- *. rewrite Zmult_plus_distr_r.
   rewrite Znat.inj_plus. rewrite Zmult_plus_distr_l.
   rewrite Znat.inj_mult. rewrite <- Zopp_mult_distr_l_reverse.
   rewrite (Zmult_assoc (Z_of_nat X)).
   rewrite (Zmult_comm (Z_of_nat X) (- Z_of_nat q)).
   rewrite Zopp_mult_distr_l_reverse. rewrite Zopp_mult_distr_l_reverse.
   rewrite (Zplus_assoc_reverse (Z_of_nat X * gamma)).
   rewrite <- Znat.inj_mult.
   rewrite (Zplus_assoc (- (Z_of_nat (q * X) * delta))). 
   rewrite Zplus_opp_l. simpl in |- *. apply Zplus_comm.
   apply gt_Sn_O.
   apply
    (euclid_gcd1 d (Z_of_nat y) (Z_of_nat X) (Z_of_nat q) (Z_of_nat (S r1))).
   apply gcd_sym. assumption.
   rewrite <- Znat.inj_mult. rewrite <- Znat.inj_plus. apply Znat.inj_eq. assumption.
   assumption.
Qed.

Lemma gcd_lincomb_pos :
 forall (x y : Z) (d : nat),
 (x > 0)%Z -> gcd x y d -> LinComb (Z_of_nat d) x y.
Proof.
   intros.
   elim (Zle_or_lt 0 y).

   (* case 0 <= y *)
   intro. rewrite <- (inj_abs_pos x). rewrite <- (inj_abs_pos y).
   apply gcd_lincomb_nat.
   change (Zabs_nat x > Zabs_nat 0) in |- *.
   apply gtzgt. apply Zlt_le_weak. apply Zgt_lt. assumption.
   unfold Zle in |- *. simpl in |- *. discriminate.
   assumption.
   rewrite inj_abs_pos. rewrite inj_abs_pos. assumption.
   apply Zle_ge. assumption.
   apply Zle_ge. apply Zlt_le_weak. apply Zgt_lt. assumption.
   apply Zle_ge. assumption.
   apply Zle_ge. apply Zlt_le_weak. apply Zgt_lt. assumption.

   (* case y < 0 *)
   intro. rewrite <- (inj_abs_pos x).
   replace y with (- - y)%Z. rewrite <- (inj_abs_neg y).
   elim (gcd_lincomb_nat (Zabs_nat x) (Zabs_nat y) d).
   intro alpha. intros. elim H2. intro beta. intros.
   split with alpha. split with (- beta)%Z.
   rewrite <- Zopp_mult_distr_r. rewrite (Zmult_comm (- Z_of_nat (Zabs_nat y))).
   rewrite <- Zopp_mult_distr_r. rewrite Zopp_involutive. rewrite (Zmult_comm beta).
   assumption.
   change (Zabs_nat x > Zabs_nat 0) in |- *. apply gtzgt.
   apply Zlt_le_weak. apply Zgt_lt. assumption.
   unfold Zle in |- *. simpl in |- *. discriminate.
   assumption.
   rewrite inj_abs_pos. rewrite inj_abs_neg. apply gcd_opp_r. assumption.
   assumption.
   apply Zle_ge. apply Zlt_le_weak. apply Zgt_lt. assumption.
   assumption.
   apply Zopp_involutive.
   apply Zle_ge. apply Zlt_le_weak. apply Zgt_lt. assumption.
Qed.

Theorem gcd_lincomb :
 forall (x y : Z) (d : nat),
 x <> 0%Z -> gcd x y d -> LinComb (Z_of_nat d) x y.
Proof.
   intros.
   elim (Zle_or_lt 0 x).
   intro.
   elim (Zle_lt_or_eq 0 x).

   (* case 0 < x *)
   intro.
   apply gcd_lincomb_pos.
   apply Zlt_gt.
   assumption.
   assumption.

   (* case 0 = x *)
   intro.
   elim H.
   rewrite H2.
   reflexivity.
   assumption.

   (* case 0 > x *)
   intro.
   elim (gcd_lincomb_pos (- x) y d). intro alpha. intros.
   elim H2. intro beta. intros.
   split with (- alpha)%Z. split with beta.
   rewrite H3.
   rewrite (Zmult_comm x). rewrite Zopp_mult_distr_l_reverse. rewrite Zopp_mult_distr_l_reverse.
   rewrite (Zmult_comm alpha). reflexivity.
   apply Zopp_lt_gt_0. assumption. apply gcd_opp_l. assumption.
Qed.
