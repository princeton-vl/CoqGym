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
   pock.
   Pocklington's criterion.
 
   @author Olga Caprotti and Martijn Oostdijk
   @version $Revision$
*)

Require Import Arith.
Require Import ZArith.

Require Import lemmas.
Require Import natZ.
Require Import dec.
Require Import list.
Require Import exp.
Require Import divides.
Require Import prime.
Require Import modulo.
Require Import gcd.
Require Import modprime.
Require Import order.

(**
   For all numbers q in natlist qlist: 1 is a linear combination
   of a^(m*qlist/qi) and n modulo n.
*)

Definition allLinCombMod (a : Z) (n m : nat) (qlist : natlist) :=
  alllist nat
    (fun q : nat =>
     LinCombMod 1 (Exp a (m * multDrop q qlist) - 1) (Z_of_nat n) n) qlist.

Lemma allLinCombMod_ok :
 forall (a : Z) (n m : nat) (qlist : natlist),
 allLinCombMod a n m qlist <->
 (forall qi : nat,
  inlist nat qi qlist ->
  LinCombMod 1 (Exp a (m * multDrop qi qlist) - 1) (Z_of_nat n) n).
Proof.
   intros.
   elim
    (alllist_ok nat
       (fun q : nat =>
        LinCombMod 1 (Exp a (m * multDrop q qlist) - 1) (Z_of_nat n) n) qlist).
   split.
   intros. apply H. assumption. assumption.
   intros. apply H0. assumption.
Qed.

(**
   Pocklington's theorem (finally).
   Proves Pocklington for natural numbers.
 *)

Theorem pocklington :
 forall (n q m : nat) (a : Z) (qlist : natlist),
 n > 1 ->
 n = S (q * m) ->
 q = product qlist ->
 allPrime qlist ->
 Mod (Exp a (pred n)) 1 n ->
 allLinCombMod a n m qlist -> n <= q * q -> Prime n.
Proof.
   intros.
   apply primepropdiv. assumption. intro p. intros.
   elim H6. intros. elim H7. intro pdn. intros.
   unfold gt in |- *. apply le_lt_trans with (pred p * pred p).
   apply le_trans with (q * q). assumption.
   cut (q <= pred p). intros.
   apply le_le_mult. assumption. assumption.
   apply order_le_predp with (Exp a m). assumption.
   cut (Mod (Exp (Exp a m) q) 1 p). intros.
   elim (order_ex (Exp a m) p). intro r. intros.
   elim H12. intros. elim H14. intros. elim H16. intros.
   elim (le_lt_or_eq r q). intro.
   cut (Divides r q). intros.
   elim (techlemma3 qlist r q). intro qi. intros.
   elim H21. intros. elim H23. intro rdm. intros.
   elim (allLinCombMod_ok a n m qlist).
   intros AH1 AH2. elim (AH1 H4 qi H22).
   intro alpha. intros. elim H25. intro beta. intros.
   elim (mod_0not1 p). assumption.
   apply mod_trans with ((1 - 1) * alpha + Z_of_nat n * beta)%Z.
   rewrite H10. simpl in |- *.
   rewrite Znat.inj_mult.
   rewrite Zmult_assoc_reverse.
   apply mod_sym.
   apply mod_nx_0_n.
   apply
    mod_trans
     with ((Exp a (m * multDrop qi qlist) - 1) * alpha + Z_of_nat n * beta)%Z.
   apply mod_plus_compat. apply mod_mult_compat. apply mod_minus_compat.
   rewrite H24.
   rewrite mult_assoc.
   apply mod_sym.
   rewrite exp_mult. apply mod_exp1. rewrite exp_mult.
   assumption.
   apply mod_refl. apply mod_refl. apply mod_refl.
   apply mod_sym. apply modpq_modp with pdn. rewrite <- H10. assumption.
   assumption.
   assumption.
   assumption.
   assumption.
   assumption.
   apply (order_div (Exp a m) r p H14 q).
   apply lt_trans with r.
   assumption.
   assumption.
   assumption.
   intro. rewrite <- H19. assumption.
   apply H18.
   elim (le_lt_or_eq 0 q).
   intro. assumption.
   intro. rewrite <- H19 in H5. simpl in H5. elim (le_not_lt n 0). assumption.
   apply lt_trans with 1. apply lt_O_Sn. assumption. apply le_O_n.
   assumption.
   assumption.
   apply mod_not_exp_0.
   assumption.
   intro. elim (mod_0not1 p). assumption.
   apply mod_trans with (Exp a (pred n)).
   apply mod_sym.
   apply moda0_exp_compat.
   unfold gt in |- *. apply lt_trans with 1. apply lt_O_Sn.
   assumption.
   assumption.
   apply gt_pred. assumption.
   rewrite H0. simpl in |- *. rewrite mult_comm. rewrite exp_mult. assumption.
   rewrite H0 in H3. simpl in H3. rewrite <- H0 in H3.
   apply modpq_modp with pdn.
   rewrite <- H10. rewrite <- exp_mult. rewrite mult_comm. assumption.
   apply lt_multpred_pp. assumption.
Qed.


(**
   Below is an attempt to restate Pocklington's theorem
   using only numbers from Z. This will make concrete
   computations faster.
 *)

(** ZallLinCombMod is equivalent to AllLinCombMod but uses Z. *)

Definition ZallLinCombMod (a n m N : Z) (qlist : Zlist) :=
  alllist Z
    (fun q : Z => ZLinCombMod 1 (ZExp a (m * zmultDrop q qlist) - 1) n N)
    qlist.

Lemma ZallLinCombMod_ok :
 forall (a n m N : Z) (qlist : Zlist),
 ZallLinCombMod a n m N qlist ->
 forall qi : Z,
 inlist Z qi qlist -> ZLinCombMod 1 (ZExp a (m * zmultDrop qi qlist) - 1) n N.
Proof.
   intros.
   elim
    (alllist_ok Z
       (fun q : Z => ZLinCombMod 1 (ZExp a (m * zmultDrop q qlist) - 1) n N)
       qlist).
   intros. apply H1. assumption. assumption.
Qed.

Lemma alllincombzalllincomb :
 forall (a n m : Z) (qlist : Zlist),
 (0 <= n)%Z ->
 (0 <= m)%Z ->
 allPos qlist ->
 ZallLinCombMod a n m n qlist ->
 allLinCombMod a (Zabs_nat n) (Zabs_nat m) (map _ _ Zabs_nat qlist).
Proof.
   intros.
   unfold ZallLinCombMod in H.
   elim
    (alllist_ok Z
       (fun q : Z => ZLinCombMod 1 (ZExp a (m * zmultDrop q qlist) - 1) n n)
       qlist).
   intros.
   elim
    (alllist_ok nat
       (fun q0 : nat =>
        LinCombMod 1
          (Exp a (Zabs_nat m * multDrop q0 (map _ _ Zabs_nat qlist)) - 1)
          (Z_of_nat (Zabs_nat n)) (Zabs_nat n)) (map _ _ Zabs_nat qlist)).
   intros.
   apply H6. intros.
   rewrite <- inj_zexp.
   rewrite Znat.inj_mult.
   rewrite inj_abs_pos.
   rewrite inj_abs_pos.
   replace m with (Z_of_nat (Zabs_nat m)).
   rewrite <- Znat.inj_mult.
   apply zlincombmodlincombmod.
   rewrite Znat.inj_mult. rewrite inj_abs_pos.
   rewrite multdropzmultdrop.
   rewrite inj_abs_pos_list.
   apply H3.
   assumption.
   apply inlist_inj_abs_pos_list.
   assumption. assumption.
   assumption.
   apply Zle_ge. assumption.
   apply inj_abs_pos.
   apply Zle_ge. assumption.
   apply Zle_ge. assumption.
   apply Zle_ge. assumption.
Qed.

(** Zpocklington is equivalent to pocklington but only uses numbers in Z. *)

Theorem Zpocklington :
 forall (n q m a : Z) (qlist : Zlist),
 (n > 1)%Z ->
 (0 <= q)%Z ->
 (0 <= m)%Z ->
 n = (q * m + 1)%Z ->
 q = zproduct qlist ->
 allZPrime qlist ->
 ZMod (ZExp a (n - 1)) 1 n ->
 ZallLinCombMod a n m n qlist -> (n <= q * q)%Z -> ZPrime n.
Proof.
   intros. cut (0 <= n)%Z. intros.
   rewrite <- (inj_abs_pos n). apply primezprime.
   apply
    (pocklington (Zabs_nat n) (Zabs_nat q) (Zabs_nat m) a
       (map _ _ Zabs_nat qlist)).
   change (Zabs_nat n > Zabs_nat 1) in |- *. apply gtzgt. assumption.
   unfold Zle in |- *. simpl in |- *. discriminate.
   assumption.
   rewrite H2. rewrite abs_plus_pos. rewrite abs_mult. rewrite plus_comm.
   simpl in |- *. reflexivity.
   apply isnat_mult.
   assumption.
   assumption.
   unfold Zle in |- *. simpl in |- *. discriminate.
   rewrite H3.
   apply zproductproduct.
   apply allzprimeallprime. assumption.
   apply mod_trans with (ZExp a (n - 1)).
   rewrite <- inj_zexp.
   rewrite abs_pred_pos.
   rewrite inj_abs_pos.
   apply mod_refl.
   apply Zle_ge.
   unfold Zminus in |- *.
   simpl in |- *.
   change (0 <= 0 + n + -1)%Z in |- *.
   rewrite (Zplus_assoc_reverse 0).
   rewrite Zplus_comm.
   apply (Zlt_left 0 n).
   apply Zlt_trans with 1%Z.
   unfold Zlt in |- *.
   simpl in |- *.
   reflexivity.
   apply Zgt_lt.
   assumption.
   apply Zlt_trans with 1%Z.
   unfold Zlt in |- *.
   simpl in |- *.
   reflexivity.
   apply Zgt_lt.
   assumption.
   apply zmodmod.
   assumption.
   apply alllincombzalllincomb.
   assumption.
   assumption.
   apply allzprimeallpos.
   assumption.
   assumption.
   rewrite <- abs_mult.
   apply lezle.
   assumption.
   apply isnat_mult.
   assumption.
   assumption.
   assumption.
   apply Zle_ge. assumption.
   apply Zle_trans with 1%Z.
   unfold Zle in |- *. simpl in |- *. discriminate.
   apply Zlt_le_weak. apply Zgt_lt. assumption.
Qed.
