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
   modulo
   Modulo Arithmetic.
 
   @author Olga Caprotti and Martijn Oostdijk
   @version $Revision$
*)

Require Import ZArith.

Require Import lemmas.
Require Import natZ.
Require Import exp.
Require Import divides.

(** (Mod a b n) means (a = b (mod n)) *)

Definition Mod (a b : Z) (n : nat) :=
  exists q : Z, a = (b + Z_of_nat n * q)%Z.

Lemma modpq_modp : forall (a b : Z) (p q : nat), Mod a b (p * q) -> Mod a b p.
Proof.
   unfold Mod in |- *.
   intros.
   elim H.
   intros.
   split with (Z_of_nat q * x)%Z.
   rewrite (Znat.inj_mult p q) in H0.
   rewrite Zmult_assoc.
   assumption.
Qed.

Lemma mod_refl : forall (a : Z) (n : nat), Mod a a n.
Proof.
   unfold Mod in |- *. intros.
   split with 0%Z.
   rewrite <- Zmult_0_r_reverse.
   rewrite <- Zplus_0_r_reverse.
   reflexivity.
Qed.

Lemma mod_sym : forall (a b : Z) (n : nat), Mod a b n -> Mod b a n.
Proof.
   unfold Mod in |- *. intros.
   elim H.
   intros.
   split with (- x)%Z.
   simpl in |- *.
   rewrite H0.
   simpl in |- *.
   rewrite Zplus_assoc_reverse.
   rewrite <- Zmult_plus_distr_r.
   rewrite Zplus_opp_r.
   rewrite <- Zmult_0_r_reverse.
   apply Zplus_0_r_reverse.
Qed.

Lemma mod_trans :
 forall (a b c : Z) (n : nat), Mod a b n -> Mod b c n -> Mod a c n.
Proof.
   unfold Mod in |- *. intros.
   elim H. elim H0.
   intros. rewrite H2. rewrite H1.
   split with (x + x0)%Z.
   rewrite Zmult_plus_distr_r.
   rewrite (Zplus_assoc c (Z_of_nat n * x) (Z_of_nat n * x0)).
   reflexivity.
Qed.

Lemma eqmod : forall x y : Z, x = y -> forall n : nat, Mod x y n.
Proof.
   intros. rewrite H. apply mod_refl.
Qed.

Lemma mod_plus_compat :
 forall (a b c d : Z) (n : nat),
 Mod a b n -> Mod c d n -> Mod (a + c) (b + d) n.
Proof.
   unfold Mod in |- *. intros.
   elim H. elim H0.
   intros. split with (x + x0)%Z.
   rewrite H1.
   rewrite H2.
   rewrite (Zplus_assoc (b + Z_of_nat n * x0) d (Z_of_nat n * x)).
   rewrite (Zplus_assoc_reverse b (Z_of_nat n * x0) d).
   rewrite (Zplus_comm (Z_of_nat n * x0) d).
   rewrite (Zplus_comm x x0).
   rewrite (Zmult_plus_distr_r (Z_of_nat n) x0 x).
   rewrite Zplus_assoc.
   rewrite Zplus_assoc.
   reflexivity.
Qed.

Lemma mod_mult_compat :
 forall (a b c d : Z) (n : nat),
 Mod a b n -> Mod c d n -> Mod (a * c) (b * d) n.
Proof.
   unfold Mod in |- *. intros.
   elim H. elim H0.
   intros. rewrite H1. rewrite H2. split with (x0 * d + x * b + Z_of_nat n * x0 * x)%Z.
   rewrite (Zmult_plus_distr_r (b + Z_of_nat n * x0) d (Z_of_nat n * x)).
   rewrite Zmult_plus_distr_l.
   rewrite Zmult_plus_distr_l.
   rewrite (Zmult_assoc b (Z_of_nat n) x).
   rewrite (Zmult_comm b (Z_of_nat n)).
   rewrite (Zmult_assoc (Z_of_nat n * x0) (Z_of_nat n) x).
   rewrite (Zmult_assoc_reverse (Z_of_nat n) x0 (Z_of_nat n)).
   rewrite (Zmult_assoc_reverse (Z_of_nat n) (x0 * Z_of_nat n) x).
   rewrite (Zmult_assoc_reverse (Z_of_nat n) b x).
   rewrite <- (Zmult_plus_distr_r (Z_of_nat n) (b * x) (x0 * Z_of_nat n * x)).
   rewrite (Zplus_assoc_reverse (b * d)).
   rewrite (Zmult_assoc_reverse (Z_of_nat n) x0 d).
   rewrite <-
    (Zmult_plus_distr_r (Z_of_nat n) (x0 * d) (b * x + x0 * Z_of_nat n * x))
    .
   rewrite (Zmult_comm x0 (Z_of_nat n)).
   rewrite Zplus_assoc.
   rewrite (Zmult_comm b x).
   reflexivity.
Qed.

Lemma mod_sqr_compat :
 forall (a b : Z) (n : nat), Mod a b n -> Mod (a * a) (b * b) n.
Proof.
   intros. apply mod_mult_compat. assumption. assumption.
Qed.

Lemma mod_exp_compat :
 forall (a b : Z) (n : nat),
 Mod a b n -> forall m : nat, Mod (Exp a m) (Exp b m) n.
Proof.
   simple induction m.
   simpl in |- *. apply mod_refl.
   intros m1 IHm. simpl in |- *.
   apply mod_mult_compat.
   assumption. assumption.
Qed.

Lemma moda0_exp_compat :
 forall (a : Z) (n : nat),
 n > 0 -> Mod a 0 n -> forall m : nat, m > 0 -> Mod (Exp a m) 0 n.
Proof.
   intros a n.
   case n.
   intro.
   elim (lt_irrefl 0).
   assumption.
   intro.
   intro.
   intro.
   intro.
   case m.
   intro.
   elim (lt_irrefl 0).
   assumption.
   intro m0.
   intros.
   elim H0.
   intros.
   rewrite H2.
   split with (x * Exp (Z_of_nat (S n0) * x) m0)%Z.
   rewrite Zmult_assoc.
   simpl in |- *.
   reflexivity.
Qed.

Lemma mod_opp_compat :
 forall (a b : Z) (n : nat), Mod a b n -> Mod (- a) (- b) n.
Proof.
   intros. elim H. intros.
   split with (- x)%Z. rewrite H0.
   rewrite Zopp_eq_mult_neg_1.
   rewrite Zopp_eq_mult_neg_1.
   rewrite Zopp_eq_mult_neg_1.
   rewrite Zmult_assoc.
   rewrite <- Zmult_plus_distr_l.
   reflexivity.
Qed.

Lemma mod_minus_compat :
 forall (a b c d : Z) (n : nat),
 Mod a b n -> Mod c d n -> Mod (a - c) (b - d) n.
Proof.
   intros.
   unfold Zminus in |- *.
   apply mod_plus_compat.
   assumption.
   apply mod_opp_compat.
   assumption.
Qed.

Lemma mod_nx_0_n : forall (n : nat) (x : Z), Mod (Z_of_nat n * x) 0 n.
Proof.
   intros. unfold Mod in |- *.
   split with x.
   simpl in |- *. reflexivity.
Qed.

Lemma moddivmin :
 forall (a b : Z) (n : nat), Mod a b n <-> Divides n (Zabs_nat (a - b)).
Proof.
   unfold Mod, Divides in |- *. split.
   intros.
   elim H.
   intros.
   rewrite H0.
   unfold Zminus in |- *.
   rewrite Zplus_assoc_reverse.
   rewrite Zplus_comm.
   rewrite Zplus_assoc_reverse.
   rewrite (Zplus_comm (- b) b).
   rewrite Zplus_opp_r.
   rewrite <- Zplus_0_r_reverse.
   split with (Zabs_nat x).
   pattern n at 2 in |- *.
   rewrite <- (abs_inj n).
   apply abs_mult.
   intros. elim H. intros.
   elim (Zle_or_lt b a).
   split with (Z_of_nat x).
   rewrite <- Znat.inj_mult.
   rewrite <- H0.
   rewrite inj_abs_pos.
   unfold Zminus in |- *.
   rewrite Zplus_assoc.
   rewrite Zplus_comm.
   rewrite Zplus_assoc.
   rewrite Zplus_opp_l.
   simpl in |- *. reflexivity.
   apply Zle_ge.
   replace 0%Z with (b - b)%Z. unfold Zminus in |- *.
   apply Zplus_le_compat_r. assumption.
   unfold Zminus in |- *.
   apply Zplus_opp_r.
   split with (- Z_of_nat x)%Z.
   rewrite Zmult_comm.
   rewrite Zopp_mult_distr_l_reverse.
   rewrite <- Znat.inj_mult.
   rewrite mult_comm.
   rewrite <- H0.
   rewrite inj_abs_neg.
   rewrite Zopp_involutive.
   unfold Zminus in |- *.
   rewrite (Zplus_comm a).
   rewrite Zplus_assoc.
   rewrite Zplus_opp_r.
   simpl in |- *. reflexivity.
   replace 0%Z with (b - b)%Z. unfold Zminus in |- *.
   rewrite (Zplus_comm a). rewrite (Zplus_comm b). apply Zplus_lt_compat_l.
   assumption.
   unfold Zminus in |- *. apply Zplus_opp_r.
Qed.

Lemma moddec : forall (a b : Z) (n : nat), Mod a b n \/ ~ Mod a b n.
Proof.
   intros.
   elim (moddivmin a b n). intros.
   elim (divdec (Zabs_nat (a - b)) n).
   left. apply H0. assumption.
   right. intro. elim H1. apply H. assumption.
Qed.

Lemma mod_0not1 : forall n : nat, n > 1 -> ~ Mod 0 1 n.
Proof.
   intros.
   intro.
   absurd (Divides n 1).
   intro.
   elim (le_not_lt n 1).
   apply div_le1.
   assumption.
   assumption.
   elim (moddivmin 0 1 n).
   intros.
   apply H1.
   assumption.
Qed.

Lemma mod_exp1 :
 forall (a : Z) (n : nat), Mod a 1 n -> forall m : nat, Mod (Exp a m) 1 n.
Proof.
   intros a n H.
   simple induction m.
   simpl in |- *.
   apply mod_refl.
   intros m1 IH.
   simpl in |- *.
   replace 1%Z with (1 * 1)%Z.
   apply mod_mult_compat.
   assumption.
   apply IH.
   simpl in |- *.
   reflexivity.
Qed.

Lemma mod_repr_non_0 :
 forall (n : nat) (x : Z), (0 < x < Z_of_nat n)%Z -> ~ Mod x 0 n.
Proof.
   intros.
   intro.
   elim H.
   intros.
   elim (moddivmin x 0 n).
   rewrite <- Zminus_0_l_reverse.
   intros.
   elim (le_not_lt n (Zabs_nat x)).
   apply div_le.
   change (Zabs_nat 0 < Zabs_nat x) in |- *.
   apply ltzlt.
   unfold Zle in |- *.
   simpl in |- *.
   discriminate.
   apply Zlt_le_weak.
   assumption.
   assumption.
   apply H3.
   assumption.
   rewrite <- (abs_inj n).
   apply ltzlt.
   apply Zlt_le_weak.
   assumption.
   change (Z_of_nat 0 <= Z_of_nat n)%Z in |- *.
   apply Znat.inj_le.
   apply le_O_n.
   assumption.
Qed.

Lemma mod_repr_eq :
 forall (p : nat) (x y : Z),
 0 < p ->
 (0 < x < Z_of_nat p)%Z -> (0 < y < Z_of_nat p)%Z -> Mod x y p -> x = y.
Proof.
   intros. unfold Mod in H2.
   elim H2. intros q Hq.
   rewrite Hq in H0.
   elim H0. elim H1. intros.
   elim (Zle_or_lt 0 q).
   intro. elim (Zle_lt_or_eq 0 q).

   (* 0<q *)
   intro. elim (Zlt_not_le 0 y).
   assumption. apply Zplus_le_reg_l with (Z_of_nat p).
   rewrite (Zplus_comm (Z_of_nat p)).
   rewrite (Zplus_comm (Z_of_nat p)). simpl in |- *.
   apply Zlt_le_weak.
   apply Zle_lt_trans with (y + Z_of_nat p * q)%Z.
   apply Zplus_le_compat_l. pattern (Z_of_nat p) at 1 in |- *. 
   rewrite <- Zmult_1_l with (Z_of_nat p).
   rewrite (Zmult_comm 1). apply Zle_mult_l.
   change (Z_of_nat 0 < Z_of_nat p)%Z in |- *.
   apply Znat.inj_lt. assumption.
   change (Zsucc 0 <= q)%Z in |- *. apply Zlt_le_succ. assumption.
   assumption.

   (* 0=q *)
   intro. rewrite <- H8 in Hq. rewrite Zmult_comm in Hq.
   rewrite Zplus_comm in Hq. simpl in Hq. assumption.

   assumption.

   (* q<0 *)
   intro. elim (Zlt_not_le 0 (y + Z_of_nat p * q)).
   assumption. apply Zle_trans with (y + Z_of_nat p * -1)%Z.
   apply Zplus_le_compat_l. apply Zle_mult_l.
   change (Z_of_nat 0 < Z_of_nat p)%Z in |- *. apply Znat.inj_lt.
   assumption. apply Zlt_succ_le. simpl in |- *. assumption.
   apply Zplus_le_reg_l with (Z_of_nat p).
   rewrite (Zplus_comm (Z_of_nat p)).
   rewrite (Zplus_comm (Z_of_nat p)).
   rewrite (Zmult_comm (Z_of_nat p)).
   rewrite (Zopp_mult_distr_l_reverse 1). rewrite Zmult_1_l.
   rewrite Zplus_assoc_reverse. rewrite Zplus_opp_l.
   rewrite (Zplus_comm y 0). simpl in |- *. apply Zlt_le_weak.
   assumption.
Qed.

(** ZMod, same as Mod but only uses Z. *)

Definition ZMod (a b n : Z) := exists q : Z, a = (b + n * q)%Z.

Lemma zmodpq_modp : forall a b p q : Z, ZMod a b (p * q) -> ZMod a b p.
Proof.
   unfold ZMod in |- *.
   intros.
   elim H.
   intros.
   split with (q * x)%Z.
   rewrite Zmult_assoc.
   assumption.
Qed.

Lemma zmod_refl : forall a n : Z, ZMod a a n.
Proof.
   unfold ZMod in |- *. intros.
   split with 0%Z.
   rewrite <- Zmult_0_r_reverse.
   rewrite <- Zplus_0_r_reverse.
   reflexivity.
Qed.

Lemma zmod_sym : forall a b n : Z, ZMod a b n -> ZMod b a n.
Proof.
   unfold ZMod in |- *. intros.
   elim H.
   intros.
   split with (- x)%Z.
   simpl in |- *.
   rewrite H0.
   simpl in |- *.
   rewrite Zplus_assoc_reverse.
   rewrite <- Zmult_plus_distr_r.
   rewrite Zplus_opp_r.
   rewrite <- Zmult_0_r_reverse.
   apply Zplus_0_r_reverse.
Qed.

Lemma zmod_trans : forall a b c n : Z, ZMod a b n -> ZMod b c n -> ZMod a c n.
Proof.
   unfold ZMod in |- *. intros.
   elim H. elim H0.
   intros. rewrite H2. rewrite H1.
   split with (x + x0)%Z.
   rewrite Zmult_plus_distr_r.
   rewrite (Zplus_assoc c (n * x) (n * x0)).
   reflexivity.
Qed.

Lemma zeqmod : forall x y : Z, x = y -> forall n : Z, ZMod x y n.
Proof.
   intros. rewrite H. apply zmod_refl.
Qed.

Lemma zmod_plus_compat :
 forall a b c d n : Z, ZMod a b n -> ZMod c d n -> ZMod (a + c) (b + d) n.
Proof.
   unfold ZMod in |- *. intros.
   elim H. elim H0.
   intros. split with (x + x0)%Z.
   rewrite H1.
   rewrite H2.
   rewrite (Zplus_assoc (b + n * x0) d (n * x)).
   rewrite (Zplus_assoc_reverse b (n * x0) d).
   rewrite (Zplus_comm (n * x0) d).
   rewrite (Zplus_comm x x0).
   rewrite (Zmult_plus_distr_r n x0 x).
   rewrite Zplus_assoc.
   rewrite Zplus_assoc.
   reflexivity.
Qed.

Lemma zmod_mult_compat :
 forall a b c d n : Z, ZMod a b n -> ZMod c d n -> ZMod (a * c) (b * d) n.
Proof.
   unfold ZMod in |- *. intros.
   elim H. elim H0.
   intros. rewrite H1. rewrite H2. split with (x0 * d + x * b + n * x0 * x)%Z.
   rewrite (Zmult_plus_distr_r (b + n * x0) d (n * x)).
   rewrite Zmult_plus_distr_l.
   rewrite Zmult_plus_distr_l.
   rewrite (Zmult_assoc b n x).
   rewrite (Zmult_comm b n).
   rewrite (Zmult_assoc (n * x0) n x).
   rewrite (Zmult_assoc_reverse n x0 n).
   rewrite (Zmult_assoc_reverse n (x0 * n) x).
   rewrite (Zmult_assoc_reverse n b x).
   rewrite <- (Zmult_plus_distr_r n (b * x) (x0 * n * x)).
   rewrite (Zplus_assoc_reverse (b * d)).
   rewrite (Zmult_assoc_reverse n x0 d).
   rewrite <- (Zmult_plus_distr_r n (x0 * d) (b * x + x0 * n * x)).
   rewrite (Zmult_comm x0 n).
   rewrite Zplus_assoc.
   rewrite (Zmult_comm b x).
   reflexivity.
Qed.

Lemma zmod_sqr_compat :
 forall a b n : Z, ZMod a b n -> ZMod (a * a) (b * b) n.
Proof.
   intros. apply zmod_mult_compat. assumption. assumption.
Qed.

Lemma zmodmod : forall a b n : Z, ZMod a b n -> Mod a b (Zabs_nat n).
Proof.
   unfold ZMod, Mod in |- *.
   intros. elim H. intros.
   rewrite H0.
   elim (Zle_or_lt 0 n).
   intro. rewrite inj_abs_pos.
   split with x. reflexivity.
   apply Zle_ge. assumption.
   intro. rewrite inj_abs_neg.
   split with (- x)%Z. rewrite Zopp_mult_distr_l_reverse.
   rewrite Zopp_mult_distr_r. rewrite Zopp_involutive.
   reflexivity.
   assumption.
Qed.

Lemma modzmod :
 forall (a b : Z) (n : nat), Mod a b n -> ZMod a b (Z_of_nat n).
Proof.
   unfold Mod, ZMod in |- *. intros. elim H.
   intros. rewrite H0. split with x.
   reflexivity.
Qed.

Lemma absmodzmod : forall a b n : Z, Mod a b (Zabs_nat n) -> ZMod a b n.
Proof.
   intros.
   elim H. intros q Hq. 
   elim Zle_or_lt with 0%Z n.
   intro. split with q. rewrite inj_abs_pos in Hq.
   assumption. apply Zle_ge. assumption.
   intros. split with (- q)%Z. rewrite inj_abs_neg in Hq.
   rewrite Zmult_comm. rewrite Zopp_mult_distr_l_reverse.
   rewrite Zopp_mult_distr_l_reverse in Hq. rewrite Zmult_comm.
   assumption. assumption.
Qed.

Lemma zmod_exp_compat :
 forall a b n : Z, ZMod a b n -> forall m : Z, ZMod (ZExp a m) (ZExp b m) n.
Proof.
   intros.
   apply absmodzmod.
   rewrite expzexp.
   rewrite expzexp.
   apply mod_exp_compat.
   apply zmodmod.
   assumption.
Qed.

Lemma zmoda0_exp_compat :
 forall a n : Z,
 (n > 0)%Z -> ZMod a 0 n -> forall m : Z, (m > 0)%Z -> ZMod (ZExp a m) 0 n.
Proof.
   intros. rewrite <- (inj_abs_pos n).
   apply modzmod. rewrite expzexp.
   apply moda0_exp_compat.
   change (Zabs_nat n > Zabs_nat 0) in |- *. apply gtzgt.
   apply Zlt_le_weak. apply Zgt_lt. assumption.
   apply Zeq_le. reflexivity.
   assumption.
   apply zmodmod. assumption.
   change (Zabs_nat m > Zabs_nat 0) in |- *. apply gtzgt.
   apply Zlt_le_weak. apply Zgt_lt. assumption.
   apply Zeq_le. reflexivity.
   assumption.
   apply Zle_ge. apply Zlt_le_weak. apply Zgt_lt. assumption.
Qed.

Lemma zmod_opp_compat : forall a b n : Z, ZMod a b n -> ZMod (- a) (- b) n.
Proof.
   intros. elim H. intros.
   split with (- x)%Z. rewrite H0.
   rewrite Zopp_eq_mult_neg_1.
   rewrite Zopp_eq_mult_neg_1.
   rewrite Zopp_eq_mult_neg_1.
   rewrite Zmult_assoc.
   rewrite <- Zmult_plus_distr_l.
   reflexivity.
Qed.

Lemma zmod_minus_compat :
 forall a b c d n : Z, ZMod a b n -> ZMod c d n -> ZMod (a - c) (b - d) n.
Proof.
   intros.
   unfold Zminus in |- *.
   apply zmod_plus_compat.
   assumption.
   apply zmod_opp_compat.
   assumption.
Qed.

Lemma zmod_nx_0_n : forall n x : Z, ZMod (n * x) 0 n.
Proof.
   intros. unfold ZMod in |- *.
   split with x.
   simpl in |- *. reflexivity.
Qed.

Lemma zmoddivmin : forall a b n : Z, ZMod a b n <-> ZDivides n (a - b).
Proof.
   unfold ZMod, Divides in |- *. split.

   (* -> *)
   intros. elim H. intros.
   rewrite H0.
   unfold Zminus in |- *.
   rewrite Zplus_assoc_reverse.
   rewrite Zplus_comm.
   rewrite Zplus_assoc_reverse.
   rewrite (Zplus_comm (- b) b).
   rewrite Zplus_opp_r.
   rewrite <- Zplus_0_r_reverse.
   split with x.
   reflexivity.

   (* <- *)
   intros. elim H. intros.
   split with x.
   rewrite <- H0.
   unfold Zminus in |- *.
   rewrite Zplus_assoc.
   rewrite Zplus_comm.
   rewrite Zplus_assoc.
   rewrite Zplus_opp_l.
   simpl in |- *. reflexivity.
Qed.

Lemma zmoddec : forall a b n : Z, ZMod a b n \/ ~ ZMod a b n.
Proof.
   intros.
   elim (zmoddivmin a b n).
   intros.
   elim (zdivdec (a - b) n).
   left.
   apply H0.
   assumption.
   right.
   intro.
   elim H1.
   apply H.
   assumption.
Qed.

Lemma zmod_0not1 : forall n : Z, (n > 1)%Z -> ~ ZMod 0 1 n.
Proof.
   intros. intro.
   elim (mod_0not1 (Zabs_nat n)).
   change (Zabs_nat n > Zabs_nat 1) in |- *. apply gtzgt.
   apply Zlt_le_weak. apply Zlt_trans with 1%Z.
   unfold Zlt in |- *. simpl in |- *. reflexivity.
   apply Zgt_lt. assumption.
   unfold Zle in |- *. simpl in |- *. discriminate.
   assumption.
   apply zmodmod. assumption.
Qed.

Lemma zmod_repr_non_0 : forall n x : Z, (0 < x < n)%Z -> ~ ZMod x 0 n.
Proof.
   intros.
   intro.
   elim H.
   intros.
   elim (mod_repr_non_0 (Zabs_nat n) x).
   split.
   assumption. rewrite inj_abs_pos.
   assumption. apply Zle_ge. apply Zle_trans with x.
   apply Zlt_le_weak. assumption.
   apply Zlt_le_weak. assumption.
   apply zmodmod. assumption.
Qed.
