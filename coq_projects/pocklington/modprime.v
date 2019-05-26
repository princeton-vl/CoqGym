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
   modprime.
   Some nice lemmas about div, mult, mod, prime, and gcd. 
 
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
Require Import gcd.

Lemma prime_div_or_gcd1 :
 forall (p : nat) (a : Z),
 Prime p -> ZDivides (Z_of_nat p) a \/ gcd (Z_of_nat p) a 1.
Proof.
   intros. elim (zdivdec a (Z_of_nat p)).
   left. assumption.
   right. unfold gcd in |- *. unfold common_div in |- *.
   split. split.
   split with p. simpl in |- *. rewrite <- plus_n_O. apply abs_inj.
   split with (Zabs_nat a). simpl in |- *. apply plus_n_O.
   intros. elim H1. intros. rewrite abs_inj in H2.
   elim (primediv1p p e).
   intro. rewrite H4. apply le_n.
   intro. rewrite H4 in H3. elim H0. apply divzdiv.
   rewrite abs_inj. assumption. assumption. assumption.
Qed.

Lemma divmultgcd :
 forall a b c : Z,
 a <> 0%Z -> ZDivides a (b * c) -> gcd a b 1 -> ZDivides a c.
Proof.
   intros. elim (gcd_lincomb a b 1).
   intro alpha. intros. elim H2. intro beta. intros.
   elim H0. intro y. intros.
   split with (c * alpha + y * beta)%Z. rewrite Zmult_plus_distr_r.
   rewrite Zmult_assoc. rewrite Zmult_assoc.
   rewrite <- H4. rewrite (Zmult_comm a c). rewrite (Zmult_comm b c).
   rewrite Zmult_assoc_reverse. rewrite Zmult_assoc_reverse.
   rewrite <- Zmult_plus_distr_r. transitivity (c * 1)%Z.
   rewrite Zmult_comm. rewrite Zmult_1_l. reflexivity.
   apply (f_equal (A:=Z)). assumption. assumption. assumption.
Qed.

Lemma primedivmult :
 forall p n m : nat,
 Prime p -> Divides p (n * m) -> Divides p n \/ Divides p m.
Proof.
   intros. elim (prime_div_or_gcd1 p (Z_of_nat n)).
   left. rewrite <- (abs_inj p). rewrite <- (abs_inj n).
   apply zdivdiv. assumption.
   right. rewrite <- (abs_inj p). rewrite <- (abs_inj m).
   apply zdivdiv. apply divmultgcd with (Z_of_nat n).
   elim H. intros. apply Zgt_neq.
   change (Z_of_nat p > Z_of_nat 0)%Z in |- *. apply Znat.inj_gt.
   apply gt_trans with 1. assumption. unfold gt in |- *. unfold lt in |- *. apply le_n.
   rewrite <- Znat.inj_mult. apply divzdiv. rewrite abs_inj. rewrite abs_inj.
   assumption. assumption. assumption.
Qed.

Lemma mod_mult_inv_r :
 forall (a : Z) (p : nat),
 Prime p -> ~ Mod a 0 p -> exists ra : Z, Mod (a * ra) 1 p.
Proof.
   intros. elim (prime_div_or_gcd1 p a).

   (* case p divides a *)
   intro. elim H0. elim H1. intros. split with x. simpl in |- *. assumption.

   (* case gcd(p,a)=1 *)
   intro. elim (gcd_lincomb (Z_of_nat p) a 1).
   intro alpha. intros. elim H2. intro beta. intros.
   unfold Mod in |- *. split with beta. split with (- alpha)%Z.
   simpl in H3. rewrite H3.
   rewrite (Zplus_comm (Z_of_nat p * alpha)). rewrite Zplus_assoc_reverse.
   rewrite <- Zmult_plus_distr_r. rewrite Zplus_opp_r.
   rewrite <- Zmult_0_r_reverse. rewrite <- Zplus_0_r_reverse. reflexivity.
   apply Zgt_neq. change (Z_of_nat p > Z_of_nat 0)%Z in |- *.
   apply Znat.inj_gt. apply gt_trans with 1. elim H. intros. assumption.
   unfold gt in |- *. unfold lt in |- *. apply le_n.
   assumption. assumption.
Qed.

Lemma mod_mult_cancel_r :
 forall (a b c : Z) (p : nat),
 Prime p -> ~ Mod c 0 p -> Mod (a * c) (b * c) p -> Mod a b p.
Proof.
   intros. elim (mod_mult_inv_r c p). intro rc. intros.
   apply mod_trans with (a * c * rc)%Z. rewrite Zmult_assoc_reverse.
   pattern a at 1 in |- *. replace a with (a * 1)%Z. apply mod_mult_compat. apply mod_refl.
   apply mod_sym. assumption.
   rewrite Zmult_comm. apply Zmult_1_l.
   apply mod_trans with (b * c * rc)%Z.
   apply mod_mult_compat. assumption. apply mod_refl. rewrite Zmult_assoc_reverse.
   pattern b at 2 in |- *. replace b with (b * 1)%Z. apply mod_mult_compat. apply mod_refl.
   assumption.
   rewrite Zmult_comm. apply Zmult_1_l.
   assumption. assumption.
Qed.

Lemma mod_mult_0 :
 forall (p : nat) (a b : Z),
 Prime p -> Mod (a * b) 0 p -> Mod a 0 p \/ Mod b 0 p.
Proof.
   intros.
   elim (moddivmin (a * b) 0 p).
   intros.
   rewrite <- Zminus_0_l_reverse in H1.
   rewrite abs_mult in H1.
   elim (primedivmult p (Zabs_nat a) (Zabs_nat b)).
   left. elim (moddivmin a 0 p). intros.
   apply H5. rewrite <- Zminus_0_l_reverse. assumption.
   right. elim (moddivmin b 0 p). intros.
   apply H5. rewrite <- Zminus_0_l_reverse. assumption.
   assumption.
   apply H1.
   assumption.
Qed.

Lemma mod_not_exp_0 :
 forall p : nat,
 Prime p -> forall a : Z, ~ Mod a 0 p -> forall m : nat, ~ Mod (Exp a m) 0 p.
Proof.
   intros p Hp a Ha. simple induction m.
   simpl in |- *. intro. elim (mod_0not1 p).
   elim Hp. intros. assumption.
   apply mod_sym. assumption.
   simpl in |- *. intros. intro.
   elim (mod_mult_0 p a (Exp a n) Hp).
   assumption. assumption. assumption.
Qed.

(**
  This lemma simply states that: if a divides b where 0<a<b,
  then there is a prime factor qi of b such that a divides (b/qi).
  I.e. If you divide by a non-trivial divisor, then the other
  divisor contains a prime factor.
*)

Lemma techlemma3 :
 forall (qlist : natlist) (a b : nat),
 0 < a ->
 a < b ->
 Divides a b ->
 b = product qlist ->
 allPrime qlist ->
 exists qi : nat, inlist nat qi qlist /\ Divides a (multDrop qi qlist).
Proof.
   simple induction qlist.
   simpl in |- *. intros. rewrite H2 in H0.
   elim (lt_not_le a 1). assumption. unfold lt in H. assumption.
   intros qi restqs IH. intros.
   elim (divdec a qi).

   (* case (Divides qi a) *)

   intro.
   elim H1. intro x. intros.
   elim H4. intro y. intros.
   elim (IH y (product restqs)). intro qj. intros.
   elim H7. intros.
   split with qj.
   split.
   unfold inlist in |- *. simpl in |- *. right. assumption.
   rewrite H6.
   elim H9. intro z. intros.
   elim (eqdec qi qj).
   intro. rewrite H11. rewrite multdrop_cons_eq.
   rewrite <- (multdrop_mult restqs qj). split with z.
   rewrite mult_assoc_reverse. rewrite H10. reflexivity. assumption.

   intro. rewrite multdrop_cons_neq.
   split with z.
   rewrite mult_assoc_reverse.
   rewrite H10.
   reflexivity.
   intro. elim H11. rewrite H12. reflexivity.

   elim (le_or_lt y 0). intro.
   elim (le_lt_or_eq y 0). intro.
   elim (lt_n_O y). assumption.
   intro. rewrite H8 in H6. rewrite <- mult_n_O in H6. rewrite H6 in H.
   elim (lt_n_O 0). assumption.
   assumption.
   intro. assumption.

   apply simpl_lt_mult_l with qi.
   rewrite <- H6.
   simpl in H2.
   rewrite <- H2.
   assumption.

   simpl in H2.
   rewrite H5 in H2.
   rewrite H6 in H2.
   split with x.
   rewrite mult_assoc_reverse in H2.
   apply simpl_eq_mult_l with qi.
   unfold allPrime in H3.
   simpl in H3.
   elim H3.
   intros.
   elim H7.
   intros.
   apply lt_trans with 1.
   apply lt_O_Sn.
   assumption.
   symmetry  in |- *.
   assumption.
   reflexivity.
   unfold allPrime in H3.
   simpl in H3.
   elim H3.
   intros.
   assumption.

   (* case ~(Divides qi a) *)

   intros.
   split with qi.
   split.
   unfold inlist in |- *.
   simpl in |- *.
   left.
   elim (beq_nat_ok qi qi).
   intros.
   reflexivity.
   rewrite multdrop_cons_eq.
   elim H1.
   intros.
   simpl in H2.
   unfold Divides in |- *.
   unfold allPrime in H3.
   simpl in H3.
   elim H3.
   intros.
   elim (primedivmult qi a x H6).
   intro.
   elim H4.
   assumption.
   intros.
   elim H8. intro z. intros.
   split with z.
   rewrite H2 in H5.
   rewrite H9 in H5.
   rewrite (mult_assoc a qi) in H5.
   rewrite (mult_comm a) in H5.
   rewrite (mult_assoc_reverse qi a) in H5.
   apply simpl_eq_mult_l with qi.
   elim H6.
   intros.
   apply lt_trans with 1. apply lt_O_Sn.
   assumption.
   assumption.
   split with (product restqs). rewrite <- H5. assumption.
Qed.
