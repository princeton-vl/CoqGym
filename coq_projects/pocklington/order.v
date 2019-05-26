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
   order.
   The order of elements in the multgroup modulo p.
 
   @author Olga Caprotti and Martijn Oostdijk
   @version $Revision$
*)

Require Import Arith.
Require Import ZArith.
Require Import Wf_nat.

Require Import lemmas.
Require Import natZ.
Require Import dec.
Require Import list.

Require Import exp.
Require Import divides.
Require Import prime.
Require Import modulo.
Require Import modprime.
Require Import fermat.

(** (Order b q p) means the order of b is q in multgroup(Z_p). *)

Definition Order (b : Z) (q p : nat) :=
  0 < q /\
  Mod (Exp b q) 1 p /\ (forall d : nat, 0 < d -> Mod (Exp b d) 1 p -> q <= d).

Lemma orderdec : forall (b : Z) (q p : nat), Order b q p \/ ~ Order b q p.
Proof.
   intros. unfold Order in |- *.
   apply anddec.
   apply ltdec.
   apply anddec.
   apply moddec.
   elim (exdec (fun d : nat => 0 < d /\ Mod (Exp b d) 1 p) q).
   right. intros.
   elim H. intro d. intros.
   elim H0. intros.
   elim H2. intros.
   intro. elim (le_not_lt q d).
   apply H5.
   assumption.
   assumption.
   assumption.
   left. intros.
   elim (le_or_lt q d).
   intro. assumption.
   intro.
   elim H.
   split with d.
   split.
   assumption.
   split.
   assumption.
   assumption.
   intro.
   apply anddec.
   apply ltdec.
   apply moddec.
Qed.

Lemma order_ex1 :
 forall (b : Z) (p : nat),
 Prime p ->
 (exists d : nat, 0 < d /\ Mod (Exp b d) 1 p) -> exists x : nat, Order b x p.
Proof.
   intros. elim H0.
   intro. apply (lt_wf_ind x).
   intros X IH.
   intros.
   elim (exdec (fun m : nat => 0 < m /\ Mod (Exp b m) 1 p) X).
   intro.
   elim H2. 
   intros.
   elim H3. intros.
   elim H5. intros.
   elim (IH x0). intros.
   split with x1.
   assumption.
   assumption.
   split. assumption. assumption.
   intros. split with X.
   elim H1. intros.
   split.
   assumption.
   split.
   assumption.
   intros.
   elim (le_or_lt X d).
   intro. assumption.
   intros.
   elim H2.
   split with d.
   split.
   assumption.
   split.
   assumption.
   assumption.
   intro. apply anddec. apply ltdec. apply moddec.
Qed.

Lemma order_ex :
 forall (b : Z) (p : nat),
 Prime p -> ~ Mod b 0 p -> exists x : nat, x < p /\ Order b x p.
Proof.
   intros.
   elim H.
   intros.
   elim (order_ex1 b p H).
   intros.
   split with x.
   split.
   apply le_lt_trans with (pred p).
   elim H3.
   intros.
   elim H5.
   intros.
   apply (H7 (pred p)).
   apply lt_pred.
   assumption.
   apply flt. assumption. assumption.
   apply lt_pred_n_n.
   apply lt_trans with 1. apply lt_O_Sn. assumption.
   assumption.
   split with (pred p).
   split.
   apply lt_pred.
   assumption.
   apply flt. assumption. assumption.
Qed.

Lemma order_div :
 forall (b : Z) (x p : nat),
 Order b x p -> forall y : nat, 0 < y -> Mod (Exp b y) 1 p -> Divides x y.
Proof.
   intros.
   elim H. intros.
   elim H3. intros.
   elim (divdec y x). intro. assumption. intro.
   elim (notdiv_rem x y H2 H6).
   intro q. intros. elim H7. intro r. intros.
   elim H8. intros. elim H10. intros.
   rewrite H12 in H1.
   elim (lt_not_le r x).
   assumption.
   apply H5.
   assumption.
   apply mod_trans with (Exp b (q * x) * Exp b r)%Z.
   apply mod_trans with (Exp (Exp b x) q * Exp b r)%Z.
   pattern (Exp b r) at 1 in |- *.
   replace (Exp b r) with (1 * Exp b r)%Z.
   apply mod_mult_compat.
   apply mod_sym.
   apply mod_exp1.
   assumption.
   apply mod_refl.
   apply Zmult_1_l.
   rewrite mult_comm.
   rewrite exp_mult.
   apply mod_refl.
   rewrite <- exp_plus.
   assumption.
Qed.

Lemma order_le_predp :
 forall (b : Z) (q p : nat), Prime p -> Order b q p -> q <= pred p.
Proof.
   intros.
   elim H. intros.
   elim H0. intros.
   elim H4. intros.
   apply H6.
   apply lt_pred. assumption.
   apply flt.
   assumption.
   intro.
   elim (mod_0not1 p).
   assumption.
   apply mod_trans with (Exp b q).
   apply mod_sym.
   apply moda0_exp_compat.
   unfold gt in |- *.
   unfold gt in H1.
   unfold lt in |- *.
   apply lt_le_weak.
   assumption.
   assumption.
   assumption.
   assumption.
Qed.
