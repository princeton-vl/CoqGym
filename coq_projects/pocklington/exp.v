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
   exp.
   Exponential function on Z.
   
   @author Olga Caprotti and Martijn Oostdijk 
   @version $Revision$
*)

Require Import ZArith.

Require Import lemmas.
Require Import natZ.

(** * Exponential function with exponent in nat. *)

Fixpoint Exp (a : Z) (n : nat) {struct n} : Z :=
  match n with
  | O => 1%Z
  | S m => (a * Exp a m)%Z
  end.

Lemma exp_0 : forall n : nat, Exp 0 (S n) = 0%Z.
Proof.
   simpl in |- *. intros. reflexivity.
Qed.

Lemma exp_1 : forall n : nat, Exp 1 n = 1%Z.
Proof.
   simple induction n.
   simpl in |- *. reflexivity.
   simpl in |- *. intros m IH. rewrite IH. reflexivity.
Qed.

Lemma exp_S : forall (a : Z) (n : nat), Exp a (S n) = (a * Exp a n)%Z.
Proof.
   simpl in |- *. reflexivity.
Qed.

Lemma exp_plus :
 forall (a : Z) (n m : nat), Exp a (n + m) = (Exp a n * Exp a m)%Z.
Proof.
   simple induction n.
   simpl in |- *. intros. elim (Exp a m). reflexivity. reflexivity. reflexivity.
   intros n1 IH. simpl in |- *. intros.
   rewrite (IH m).
   apply Zmult_assoc.
Qed.

Lemma exp_abn :
 forall (a b : Z) (n : nat), Exp (a * b) n = (Exp a n * Exp b n)%Z.
Proof.
   simple induction n.
   simpl in |- *. reflexivity.
   intros m IH. simpl in |- *.
   rewrite IH.
   rewrite (Zmult_assoc (a * Exp a m) b (Exp b m)).
   rewrite (Zmult_assoc_reverse a (Exp a m) b).
   rewrite (Zmult_comm (Exp a m) b).
   rewrite (Zmult_assoc a b (Exp a m)).
   apply Zmult_assoc.
Qed.

Lemma exp_mult : forall (a : Z) (n m : nat), Exp a (n * m) = Exp (Exp a n) m.
Proof.
   simple induction n.
   simpl in |- *. intro. rewrite exp_1. reflexivity.
   intros m IH. simpl in |- *. intros.
   rewrite exp_plus.
   rewrite exp_abn.
   rewrite IH.
   reflexivity.
Qed.

Lemma exp_not0 : forall a : Z, a <> 0%Z -> forall m : nat, Exp a m <> 0%Z.
Proof.
   intros a Ha. simple induction m.
   simpl in |- *. discriminate.
   intros n IH. simpl in |- *. intro.
   elim (Zmult_ab0a0b0 a (Exp a n)).
   assumption. assumption. assumption.
Qed.

(** Convenience lemma for changing exponent. *)

Lemma exp_eq : forall (n m : nat) (a : Z), n = m -> Exp a n = Exp a m.
Proof.
   intros. rewrite H. reflexivity.
Qed.

Lemma exp_pred_succ : forall (a : Z) (n : nat), Exp a (pred (S n)) = Exp a n.
Proof.
   intros. simpl in |- *. reflexivity.
Qed.

(** * Exponential function with exponent in Z. *)

Definition ZExp (a n : Z) : Z :=
  match n with
  | Z0 => 1%Z
  | Zpos p => Exp a (nat_of_P p)
  | Zneg p => Exp a (nat_of_P p)
  end.

Lemma zexp_pred_succ : forall a x : Z, ZExp a (x + 1 - 1) = ZExp a x.
Proof.
   unfold Zminus in |- *.
   intros.
   rewrite Zplus_assoc_reverse.
   rewrite Zplus_opp_r.
   rewrite <- Zplus_0_r_reverse.
   reflexivity.
Qed.

(** Convenience lemma for changing exponent. *)

Lemma zexp_eq : forall x y a : Z, x = y -> ZExp a x = ZExp a y.
Proof.
   intros.
   rewrite H.
   reflexivity.
Qed.

Lemma inj_zexp : forall (n : nat) (a : Z), ZExp a (Z_of_nat n) = Exp a n.
Proof.
   simple induction n.
   simpl in |- *. reflexivity.
   intros m IH. intros.
   simpl in |- *. rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
   simpl in |- *. reflexivity.
Qed.

Lemma expzexp : forall x a : Z, ZExp a x = Exp a (Zabs_nat x).
Proof.
   intros.
   induction  x as [| p| p].
   simpl in |- *. reflexivity.
   simpl in |- *. reflexivity.
   simpl in |- *. reflexivity.
Qed.

Lemma zexp_S1 :
 forall a n : Z, (0 <= n)%Z -> ZExp a (n + 1) = (a * ZExp a n)%Z.
Proof.
   intros.
   rewrite expzexp.
   rewrite expzexp.
   rewrite abs_plus_pos.
   rewrite plus_comm.
   change (Exp a (S (Zabs_nat n)) = (a * Exp a (Zabs_nat n))%Z) in |- *.
   apply exp_S.
   assumption.
   unfold Zle in |- *.
   simpl in |- *.
   discriminate.
Qed.

Lemma zexp_S :
 forall a n : Z, (0 <= n)%Z -> ZExp a (Zsucc n) = (a * ZExp a n)%Z.
Proof.
   intros.
   change (ZExp a (n + 1) = (a * ZExp a n)%Z) in |- *.
   apply zexp_S1.
   assumption.
Qed.

Lemma zexp_plus :
 forall a n m : Z,
 (0 <= n)%Z -> (0 <= m)%Z -> ZExp a (n + m) = (ZExp a n * ZExp a m)%Z.
Proof.
   intros.
   rewrite expzexp.
   rewrite expzexp.
   rewrite expzexp.
   rewrite abs_plus_pos.
   apply exp_plus. assumption. assumption.
Qed.

Lemma zexp_mult :
 forall a n m : Z,
 (0 <= n)%Z -> (0 <= m)%Z -> ZExp a (n * m) = ZExp (ZExp a n) m.
Proof.
   intros.
   rewrite expzexp.
   rewrite expzexp.
   rewrite expzexp.
   rewrite abs_mult.
   apply exp_mult.
Qed.