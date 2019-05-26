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
   divides.
   The division predicate.
 
   @author Olga Caprotti and Martijn Oostdijk
   @version $Revision$
*)

Require Import ZArith.
Require Import Wf_nat.

Require Import lemmas.
Require Import natZ.
Require Import dec.
Require Import exp.

(** * Division on nat *)

Definition Divides (n m : nat) : Prop := exists q : nat, m = n * q.

Lemma div_refl : forall a : nat, Divides a a.
Proof.
   intros. split with 1.
   rewrite <- mult_n_Sm.
   rewrite <- mult_n_O.
   simpl in |- *. reflexivity.
Qed.

Lemma div_trans :
 forall p q r : nat, Divides p q -> Divides q r -> Divides p r.
Proof.
   intros.
   elim H.
   elim H0.
   intros.
   unfold Divides in |- *.
   split with (x0 * x).
   rewrite H1.
   rewrite H2.
   rewrite mult_assoc.
   reflexivity.
Qed.

Lemma div_antisym : forall a b : nat, Divides a b -> Divides b a -> a = b.
Proof.
   intros. elim H. elim H0. intros x Ha y Hb.
   rewrite Hb in Ha.
   rewrite mult_assoc_reverse in Ha.
   elim (mult_ppq_p0q1 a (y * x)). intro.
   rewrite H1 in Hb.
   simpl in Hb. rewrite H1. rewrite Hb. reflexivity.
   intros. elim (mult_pq1_p1q1 y x H1).
   intros.
   rewrite H2 in Hb. rewrite <- mult_n_Sm in Hb. rewrite <- mult_n_O in Hb.
   simpl in Hb. symmetry  in |- *. assumption. assumption.
Qed.

Lemma div_le1 : forall n d : nat, Divides d (S n) -> d <= S n.
Proof.
   unfold Divides in |- *.
   intros.
   elim H.
   intro q.
   case q.
   rewrite <- (mult_n_O d).
   intros.
   discriminate H0.
   intro q1.
   intros.
   rewrite H0.
   apply le_n_nm.
Qed.

Lemma div_le : forall d n : nat, 0 < n -> Divides d n -> d <= n.
Proof.
   intros d n. case n.
   intro. elim (lt_irrefl 0). assumption.
   intros. apply div_le1. assumption.
Qed.

(** Divides with bounded ex quantifier. *)

Definition bDivides (d n : nat) :=
  n = 0 \/ (exists q : nat, q < S n /\ n = d * q).

Lemma divbdiv : forall n d : nat, Divides d n <-> bDivides d n.
Proof.
   unfold Divides in |- *.
   unfold bDivides in |- *.
   split.
   case n.
   left.
   reflexivity.
   right.
   elim H.
   intro q.
   case d.
   simpl in |- *.
   intros.
   discriminate H0.
   intro d1.
   intros.
   split with q.
   split.
   rewrite H0.
   unfold lt in |- *.
   apply le_n_S.
   apply le_n_mn.
   assumption.
   intros.
   elim H.
   intros.
   rewrite H0.
   split with 0.
   rewrite <- (mult_n_O d).
   reflexivity.
   elim H.
   intros.
   rewrite H0.
   split with 0.
   rewrite <- (mult_n_O d).
   reflexivity.
   intros.
   elim H0.
   intros.
   split with x.
   elim H2.
   intros.
   assumption.
Qed.

(** Divides is decidable. *)

Lemma bdivdec : forall n d : nat, bDivides d n \/ ~ bDivides d n.
Proof.
   intros. unfold bDivides in |- *.
   apply ordec.
   apply eqdec.
   apply (exdec (fun q : nat => n = d * q) (S n)).
   intros. apply eqdec.
Qed.

Lemma divdec : forall n d : nat, Divides d n \/ ~ Divides d n.
Proof.
   intros. elim (divbdiv n d).
   intros. elim (bdivdec n d).
   left. apply (H0 H1).
   right. intro. apply H1. apply (H H2).
Qed.

(** If d|n, then either d<sqrt(n) or the other divisor x<sqrt(n). *)

Theorem sqrdivbound :
 forall n d : nat,
 Divides d n ->
 exists x : nat, Divides x n /\ x * x <= n /\ (x = d \/ d * x = n).
Proof.
   intros.
   unfold Divides in H.
   elim H.
   intros.
   rewrite H0.
   elim (sqrbound d x).
   intros.
   split with d.
   split.
   split with x.
   reflexivity.
   split.
   assumption.
   left.
   reflexivity.
   intros.
   split with x.
   split.
   split with d.
   apply mult_comm.
   split.
   assumption.
   right.
   reflexivity.
Qed.


(**
   Division with remainder.
*)

Theorem div_rem :
 forall d n : nat,
 d > 0 -> exists q : nat, (exists r : nat, 0 <= r /\ r < d /\ n = q * d + r).
Proof.
   intros d n.
   apply (lt_wf_ind n). intros N IH. intros.
   elim (le_or_lt d N).

   (* case d<=N *)
   intro.
   elim (le_witness d N). intros x Hx.
   elim (IH x). intro q'. intros. elim H1. intro r'. intros.
   elim H2. intros. elim H4. intros.
   split with (S q'). split with r'.
   split. assumption.
   split. assumption.
   simpl in |- *. rewrite <- Hx. rewrite (plus_assoc_reverse d (q' * d)).
   rewrite <- H6. reflexivity.
   unfold lt in |- *. apply witness_le. split with (pred d). rewrite plus_Snm_nSm.
   rewrite <- (S_pred d 0). rewrite plus_comm. assumption. assumption.
   assumption.
   assumption.

   (* case N<d *)
   intro.
   split with 0. split with N.
   split. apply le_O_n.
   split. assumption.
   simpl in |- *. reflexivity.
Qed.

Lemma div_rem0 :
 forall n d q r : nat, n = q * d + r -> r < d -> Divides d n -> r = 0.
Proof.
   intros.
   elim H1.
   intros.
   rewrite H2 in H.
   rewrite (mult_comm q d) in H.
   apply (le_diff0 (d * q) (d * x)).
   apply le_mult_l.
   apply le_S_n.
   change (x < S q) in |- *.
   apply simpl_lt_mult_l with d.
   rewrite <- (mult_n_Sm d q).
   replace (d * x) with (d * q + r).
   apply plus_lt_compat_l.
   assumption.
   assumption.
Qed.

Theorem notdiv_rem :
 forall d n : nat,
 0 < d ->
 ~ Divides d n ->
 exists q : nat, (exists r : nat, 0 < r /\ r < d /\ n = q * d + r).
Proof.
   intros d n.
   elim (le_or_lt d n).
   intro.
   elim (le_lt_or_eq d n).
   apply (lt_wf_ind n).
   intros N IH. intros.
   elim (lt_witness d N). intros.
   elim H3. intros.
   elim (le_or_lt d x).
   intro.
   elim (le_lt_or_eq d x).
   intro.
   elim (divdec x d).
   intros.
   elim H8.
   intros.
   rewrite H9 in H4.
   rewrite plus_comm in H4.
   rewrite mult_n_Sm in H4.
   elim H2.
   split with (S x0).
   symmetry  in |- *.
   assumption.
   intros.
   elim (IH x).
   intro q'.
   intros.
   elim H9.
   intro r'.
   intros.
   elim H10.
   intros.
   elim H12.
   intros.
   split with (S q').
   split with r'.
   split.
   assumption.
   split.
   assumption.
   simpl in |- *.
   rewrite plus_assoc_reverse.
   rewrite <- H14.
   symmetry  in |- *.
   assumption.
   rewrite <- H4.
   pattern x at 1 in |- *.
   replace x with (0 + x).
   apply plus_lt_compat_r.
   assumption.
   simpl in |- *.
   reflexivity.
   assumption.
   assumption.
   assumption.
   intro.
   elim H2.
   split with 2.
   rewrite mult_comm.
   simpl in |- *.
   rewrite <- (plus_n_O d).
   rewrite <- H4.
   rewrite H7.
   reflexivity.
   assumption.
   intro.
   split with 1.
   split with x.
   split.
   assumption.
   split.
   assumption.
   simpl in |- *.
   rewrite <- (plus_n_O d).
   rewrite H4.
   reflexivity.
   assumption.
   intros.
   elim H2.
   split with 1.
   rewrite mult_comm.
   simpl in |- *.
   rewrite <- (plus_n_O d).
   symmetry  in |- *.
   assumption.
   assumption.
   case n.
   intros.
   elim H1.
   split with 0.
   apply mult_n_O.
   intro n1.
   intros.
   split with 0.
   split with (S n1).
   split.
   apply lt_O_Sn.
   split.
   assumption.
   simpl in |- *. reflexivity.
Qed.

(** Compatibility results. *)

Lemma div_plus_compat :
 forall a b c : nat, Divides a b -> Divides a c -> Divides a (b + c).
Proof.
   intros.
   elim H. intro x. intros.
   elim H0. intro y. intros.
   split with (x + y).
   rewrite H1. rewrite H2. symmetry  in |- *.
   rewrite (mult_comm a). rewrite (mult_comm a). rewrite (mult_comm a).
   apply mult_plus_distr_r.
Qed.

Lemma div_minus_compat :
 forall a b d : nat, Divides d a -> Divides d b -> Divides d (a - b).
Proof.
   intros. elim H. elim H0. intros.
   unfold Divides in |- *. rewrite H1. rewrite H2.
   rewrite (mult_comm d).
   rewrite (mult_comm d).
   rewrite <- mult_minus_distr_r.
   split with (x0 - x).
   apply mult_comm.
Qed.

Lemma div_mult_compat_l :
 forall a b c : nat, Divides a b -> Divides a (b * c).
Proof.
   intros.
   elim H.
   intro x.
   intros.
   unfold Divides in |- *.
   rewrite H0.
   split with (x * c).
   rewrite mult_assoc.
   reflexivity.
Qed.

Lemma div_absexp_compat :
 forall (b : Z) (d : nat),
 Divides d (Zabs_nat b) -> forall n : nat, Divides d (Zabs_nat (Exp b (S n))).
Proof.
   intros b d H. elim H. intros k Hk. simple induction n.
   split with k.
   rewrite <- Hk.
   simpl in |- *.
   rewrite abs_mult.
   rewrite mult_comm.
   simpl in |- *.
   rewrite <- plus_n_O.
   reflexivity.
   intros m IH.
   replace (Exp b (S (S m))) with (b * Exp b (S m))%Z.
   rewrite abs_mult.
   apply div_mult_compat_l.
   assumption.
   simpl in |- *. reflexivity.
Qed.

Lemma div_plus_r :
 forall a b d : nat, Divides d a -> Divides d (a + b) -> Divides d b.
Proof.
   intros. elim H. elim H0. intros.
   split with (x - x0).
   rewrite mult_comm.
   rewrite mult_minus_distr_r.
   rewrite mult_comm.
   rewrite <- H1.
   rewrite mult_comm.
   rewrite <- H2.
   rewrite minus_plus.
   reflexivity.
Qed.

(** * Division on Z. *)

Definition ZDivides (x y : Z) : Prop := exists q : Z, y = (x * q)%Z.

Lemma zdivdiv :
 forall a b : Z, ZDivides a b -> Divides (Zabs_nat a) (Zabs_nat b).
Proof.
   intros.
   elim H.
   intros d Hd.
   exists (Zabs_nat d).
   rewrite Hd.
   apply abs_mult.
Qed.

Lemma divzdiv :
 forall a b : Z, Divides (Zabs_nat a) (Zabs_nat b) -> ZDivides a b.
Proof.
   intros.
   elim H.
   intros d Hd.
   elim (Zle_or_lt 0 a).
   elim (Zle_or_lt 0 b).

   (* case 0<=b, a<=b *)
   intros.
   exists (Z_of_nat d).
   rewrite <- (inj_abs_pos b).
   rewrite <- (inj_abs_pos a).
   rewrite <- Znat.inj_mult.
   rewrite Hd. reflexivity.
   apply Zle_ge. assumption.
   apply Zle_ge. assumption.

   (* case b<0, 0<=a *)
   intros.
   exists (- Z_of_nat d)%Z.
   rewrite <- (Zopp_involutive b).
   rewrite <- (inj_abs_neg b).
   rewrite <- (inj_abs_pos a).
   rewrite Zmult_comm. rewrite Zopp_mult_distr_l_reverse. rewrite Zmult_comm.
   rewrite <- Znat.inj_mult.
   apply (f_equal (A:=Z)).
   rewrite Hd.
   reflexivity.
   apply Zle_ge. assumption.
   assumption.

   elim (Zle_or_lt 0 b).

   (* case 0<=b, a<0 *)
   intros.
   exists (- Z_of_nat d)%Z.
   rewrite <- (Zopp_involutive a).
   rewrite <- (inj_abs_neg a).
   rewrite <- (inj_abs_pos b).
   rewrite Zmult_opp_opp.
   rewrite <- Znat.inj_mult.
   rewrite Hd.
   reflexivity.
   apply Zle_ge. assumption.
   assumption.

   (* case b<0, a<0 *)
   intros.
   exists (Z_of_nat d).
   rewrite <- (Zopp_involutive b).
   rewrite <- (Zopp_involutive a).
   rewrite <- (inj_abs_neg b).
   rewrite <- (inj_abs_neg a).
   rewrite Zopp_mult_distr_l_reverse.
   rewrite <- Znat.inj_mult.
   apply (f_equal (A:=Z)).
   rewrite Hd.
   reflexivity.
   assumption.
   assumption.
Qed.

Lemma zdivdec : forall x d : Z, ZDivides d x \/ ~ ZDivides d x. 
Proof.
   intros.
   elim (divdec (Zabs_nat x) (Zabs_nat d)).
   left. apply divzdiv. assumption.
   right. intro. apply H. apply zdivdiv. assumption.
Qed.

Lemma zdiv_plus_r :
 forall a b d : Z, ZDivides d a -> ZDivides d (a + b) -> ZDivides d b.
Proof.
   intros.
   elim H.
   elim H0.
   intros.
   split with (x - x0)%Z.
   rewrite Zmult_comm.
   rewrite Zmult_minus_distr_r.
   rewrite Zmult_comm.
   rewrite <- H1.
   rewrite Zmult_comm.
   rewrite <- H2.
   rewrite Zminus_plus.
   reflexivity.
Qed.

Lemma zdiv_plus_compat :
 forall a b c : Z, ZDivides a b -> ZDivides a c -> ZDivides a (b + c).
Proof.
   intros.
   elim H. intro x. intros.
   elim H0. intro y. intros.
   split with (x + y)%Z.
   rewrite H1. rewrite H2. symmetry  in |- *.
   rewrite (Zmult_comm a). rewrite (Zmult_comm a). rewrite (Zmult_comm a).
   apply Zmult_plus_distr_l.
Qed.

Lemma zdiv_mult_compat_l :
 forall a b c : Z, ZDivides a b -> ZDivides a (b * c).
Proof.
   intros.
   elim H.
   intro x.
   intros.
   unfold ZDivides in |- *.
   rewrite H0.
   split with (x * c)%Z.
   rewrite Zmult_assoc.
   reflexivity.
Qed.

Theorem zdiv_rem :
 forall d n : Z,
 (d > 0)%Z ->
 exists q : Z, (exists r : Z, (0 <= r < d)%Z /\ n = (q * d + r)%Z).
Proof.
   intros d n. intro.
   elim (Zle_or_lt 0 n).

   (* case 0<=n *)
   intro. rewrite <- (inj_abs_pos d). rewrite <- (inj_abs_pos n).
   elim (div_rem (Zabs_nat d) (Zabs_nat n)).
   intro qn. intros. elim H1. intro rn. intros.
   elim H2. intros. elim H4. intros.
   split with (Z_of_nat qn). split with (Z_of_nat rn).
   split. split. change (Z_of_nat 0 <= Z_of_nat rn)%Z in |- *.
   apply Znat.inj_le. apply le_O_n.
   apply Znat.inj_lt. assumption.
   rewrite <- Znat.inj_mult. rewrite <- Znat.inj_plus. apply Znat.inj_eq.
   assumption. change (Zabs_nat d > Zabs_nat 0) in |- *. apply gtzgt.
   apply Zlt_le_weak. apply Zgt_lt. assumption. apply Zeq_le. reflexivity.
   assumption. apply Zle_ge. assumption. apply Zle_ge.
   apply Zlt_le_weak. apply Zgt_lt. assumption.

   (* case n<0 *)
   intro. rewrite <- (inj_abs_pos d).
   replace n with (- - n)%Z. rewrite <- (inj_abs_neg n).
   elim (div_rem (Zabs_nat d) (Zabs_nat n)).
   intro qn. intros. elim H1. intro rn. intros.
   elim H2. intros. elim H4. intros.
   elim (le_lt_or_eq 0 rn).

   (* case 0<rn *)
   intro. split with (- Z_of_nat (S qn))%Z. split with (d - Z_of_nat rn)%Z.
   split. split. rewrite <- (inj_abs_pos d). apply Zle_minus. apply Znat.inj_le.
   apply lt_le_weak. assumption.
   apply Zle_ge. apply Zlt_le_weak. apply Zgt_lt. assumption.
   rewrite inj_abs_pos. apply Zplus_lt_reg_l with (Z_of_nat rn).
   unfold Zminus in |- *. rewrite (Zplus_comm d).
   rewrite (Zplus_assoc (Z_of_nat rn)).
   rewrite Zplus_opp_r. simpl in |- *. change (0 + d < Z_of_nat rn + d)%Z in |- *.
   rewrite Zplus_comm. rewrite (Zplus_comm (Z_of_nat rn)). apply Zplus_lt_compat_l.
   change (Z_of_nat 0 < Z_of_nat rn)%Z in |- *. apply Znat.inj_lt. assumption.
   apply Zle_ge. apply Zlt_le_weak. apply Zgt_lt. assumption.
   rewrite Znat.inj_S. unfold Zsucc in |- *. rewrite Zopp_mult_distr_l_reverse.
   rewrite Zmult_plus_distr_l. rewrite <- Znat.inj_mult. rewrite Zmult_1_l.
   rewrite (inj_abs_pos d). rewrite Zopp_plus_distr.
   unfold Zminus in |- *. rewrite Zplus_assoc_reverse. rewrite (Zplus_assoc (- d)).
   rewrite Zplus_opp_l. simpl in |- *. rewrite <- Zopp_plus_distr. rewrite <- Znat.inj_plus.
   rewrite <- H6. reflexivity.
   apply Zle_ge. apply Zlt_le_weak. apply Zgt_lt. assumption.

   (* case 0=rn *)
   intro.
   split with (- Z_of_nat qn)%Z. split with 0%Z.
   split. split. unfold Zle in |- *. simpl in |- *. discriminate.
   apply Zle_lt_trans with (Z_of_nat rn).
   change (Z_of_nat 0 <= Z_of_nat rn)%Z in |- *. apply Znat.inj_le. apply le_O_n.
   apply Znat.inj_lt. assumption.
   rewrite <- Zplus_0_r_reverse. rewrite inj_abs_neg.
   rewrite Zopp_mult_distr_l_reverse. rewrite <- Znat.inj_mult.
   rewrite <- H7 in H6. rewrite <- plus_n_O in H6. rewrite <- H6.
   rewrite inj_abs_neg. reflexivity.
   assumption. assumption. assumption.
   change (Zabs_nat d > Zabs_nat 0) in |- *. apply gtzgt. apply Zlt_le_weak.
   apply Zgt_lt. assumption.
   unfold Zle in |- *. simpl in |- *. discriminate.
   assumption. assumption.
   apply Zopp_involutive.
   apply Zle_ge. apply Zlt_le_weak. apply Zgt_lt. assumption.
Qed.
