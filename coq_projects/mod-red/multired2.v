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

(*
   Fast reduction of nonnegative integers
   by moduli M such that 1 <= M <= 2 ^ (w - 1)
   where w denotes a processor's word size.
*)
(* Faster than the version proposed in multired.v on some processors. *)

(* Coq 8.2 *)

Require Import ZArith.

Require Import preparation.
Require Import unsigned.

Require Import modred.

Open Scope Z_scope.

(* <KEEP TOGETHER - loop_invariant_multired_x *)
Definition P' (M p : Z) (d r : Z_ (2 ^ w)) (h : Z) (l : Z_ (2 ^ w)) :=
  (_Z d = (h mod M * 2 ^ w + l) / 2 ^ p * 2 ^ p mod M \/
   _Z d = (h mod M * 2 ^ w + l) / 2 ^ p * 2 ^ p mod M + M \/
   _Z d = ((h mod M + M) * 2 ^ w + l) / 2 ^ p * 2 ^ p mod M \/
   _Z d = ((h mod M + M) * 2 ^ w + l) / 2 ^ p * 2 ^ p mod M + M
  ) /\
   _Z r = (d + l mod 2 ^ p mod M) mod 2 ^ w.
(* KEEP TOGETHER> *)

Section parm_sec.

Variable M_in_Z_ : Z_ (2 ^ w).

Variable ptM'cM'' : Z_ w * Z_ w * Z_ (2 ^ w) * Z_ (2 ^ w) * Z_ (2 ^ w).
Variable d_Sir_Si : Z_ (2 ^ w) * Z_ (2 ^ w).
Variable l_in_Z_ : Z_ (2 ^ w).
Variable x_i_in_Z_ : Z_ (2 ^ w).
Variable h : Z.

Let p_in_Z_w := fst (fst (fst (fst ptM'cM''))).
Let t_in_Z_w := snd (fst (fst (fst ptM'cM''))).
Let M'_in_Z_ := snd (fst (fst ptM'cM'')).
Let c_in_Z_ := snd (fst ptM'cM'').
Let M''_in_Z_ := snd ptM'cM''.

Let M := _Z M_in_Z_.
Let p := _Z p_in_Z_w.
Let t := _Z t_in_Z_w.
Let c := _Z c_in_Z_.
Let M'' := _Z M''_in_Z_.
Let M' := _Z M'_in_Z_.
Let l := _Z l_in_Z_.
Let x_i := _Z x_i_in_Z_.

Definition d_Si := fst d_Sir_Si.
Definition r_Si := snd d_Sir_Si.

Hypothesis d_Si_eq_r_Si_eq : P' M p d_Si r_Si h l_in_Z_.

Hypothesis le_1_M : 1 <= M.
Hypothesis le_M_max : M <= 2 ^ (w - 1).
Hypothesis p_M : p = Zlog_sup M.
Hypothesis t_M : t = w - p \/ M = 1.
Hypothesis c_M : c = 2 ^ p.
Hypothesis M''_M : M'' = (2 ^ t * M) mod 2 ^ w.
Hypothesis M'_M : M' = 2 ^ (p + w) / M mod 2 ^ w.

Lemma le_0_p : 0 <= p.

  unfold p. apply le_0__Z. Qed.

Lemma le02w : 0 <= 2 ^ w.

  apply Zlt_le_weak. exact lt02w. Qed.

Local Hint Resolve le_0_w lt02w le02w : a.

Local Hint Resolve le_0_p : a.

Lemma le_M_2pp : M <= 2 ^ p.

  rewrite p_M. generalize le_1_M. case M. intro. absurd (2 <= 0); omega. intros q H.
  elim (Zlog_sup_correct2 (Zpos q)). omega. omega. intros q H. absurd (2 <= Zneg q). apply Zlt_not_le.
  unfold Zlt. trivial. assumption. Qed.

Lemma le_1_p : 1 <= p \/ M = 1.

  rewrite p_M. elim (Zle_lt_or_eq 1 M). intro H. left. apply Zle_trans with (Zlog_sup 2). simpl. omega. 
  apply Zlog_sup_seq. omega. intro H. right. symmetry. trivial. assumption. Qed.

Lemma lt_0_p : 0 < p \/ M = 1. 

  elim le_1_p; intro H; omega. Qed.

Lemma le_0_pm1 : 0 <= p - 1 \/ M = 1.

  elim lt_0_p; intro H; omega. Qed.

Lemma lt_2pm1_M : 2 ^ (p - 1) < M \/ M = 1.

  elim (Zle_lt_or_eq 1 M). intro H. rewrite p_M. generalize le_1_M. case M. intro. absurd (2 <= 0); omega. 
  intros q H0. elim (Zlog_sup_correct2 (Zpos q)). omega. omega. intros q H0. absurd (1 <= Zneg q). 
  apply Zlt_not_le. unfold Zlt. trivial. assumption. omega. assumption. Qed.

Local Hint Resolve lt_2pm1_M : a.

Local Hint Resolve le_M_2pp le_1_p lt_0_p le_0_pm1 : a.

Lemma div_M_1_again : 2 ^ p / M = 1.

  elim (Zle_lt_or_eq 1 M). intro H. replace (2 ^ p) with (1 * M + (2 ^ p - M)). apply Zdiv_mult_plus. omega.
  cut (M <= 2 ^ p). omega. auto with a. cut (2 ^ p < M + M). omega. 
  apply Zlt_le_trans with (2 ^ (p - 1) + 1 + (2 ^ (p - 1) + 1)).
  replace (2 ^ (p - 1) + 1 + (2 ^ (p - 1) + 1)) with (2 ^ (p - 1) + 2 ^ (p - 1) + 2). rewrite Z_pow_plus.
  replace (p - 1 + 1) with p. omega. ring. elim le_0_pm1. omega. intro H0. absurd (1 < M). omega.
  assumption. ring. cut (2 ^ (p - 1) < M). omega. elim lt_2pm1_M. omega. intro H0. absurd (1 < M). omega.
  assumption. ring. intro H0. rewrite p_M. rewrite <- H0. trivial. assumption. Qed.

Lemma large_M'_eq : 2 ^ w + (2 ^ (p + w) / M) mod 2 ^ w = 2 ^ (p + w) / M.

  transitivity (2 ^ (p + w) / M / 2 ^ w * 2 ^ w + (2 ^ (p + w) / M) mod 2 ^ w).
  apply f_equal2 with (f := Zplus). replace (2 ^ (p + w) / M / 2 ^ w) with 1. ring.
  rewrite Zdivdivdiv. rewrite Zmult_comm. rewrite <- Zdivdivdiv. rewrite Zpower_exp; auto with a. 
  rewrite Z_div_mult. symmetry. unfold p. unfold p_in_Z_w. apply div_M_1_again. apply Zlt_gt. auto with
  a. apply Zle_ge. auto with a.  apply Zle_ge. auto with a. auto with
  a. omega. omega. auto with a. trivial. apply Zdivmod_split.  auto
  with a. Qed.

(* <KE EP TOGETHER - multired_equations *)
Let r'_i := ltw d_Si c_in_Z_ r_Si (minusw r_Si M_in_Z_).

Let s_i := ursh x_i_in_Z_ p_in_Z_w.

Let s'_i := multp2 s_i p_in_Z_w.

Let l'_i := minusw x_i_in_Z_ s'_i.

Let s''_i := ltw r'_i c_in_Z_ s_i (minusw s_i M''_in_Z_).

Let h_i := multp2 r'_i t_in_Z_w.

Let h'_i := plusw h_i s''_i.

Let q_i := uhwm h'_i M'_in_Z_.

Let q'_i := plusw q_i h'_i.

Let y_i := multw q'_i M_in_Z_.

Definition d_i := minusw s'_i y_i.

Definition rrr_i := minusw x_i_in_Z_ y_i.

Definition r_i := ltw l'_i M_in_Z_ rrr_i (minusw rrr_i M_in_Z_).
(* KE EP TOGETHER> *)

Let d0 := d_Si. (* notation *)
Let r0 := r_Si. (* notation *)

(* <KE EP TOGETHER - multired_final *)
Let r'0 := ltw d0 M_in_Z_ r0 (minusw r0 M_in_Z_). (* notation *)

Definition r''0 := ltw r'0 M_in_Z_ r'0 (minusw r'0 M_in_Z_). (* only needed after the loop *)
(* KE EP TOGETHER> *)

Definition r'0' := ltw d0 c_in_Z_ r0 (minusw r0 M_in_Z_). (* needed in loop *)

Definition r''0' := ltw r'0' M_in_Z_ r'0' (minusw r'0' M_in_Z_). (* needed in loop *)

Let h_i' := multp2 r''0' t_in_Z_w.
 
Let h'_i' := plusw h_i' s_i.

Definition g' := r''0. (* only needed after the loop *)

Let x := h * 2 ^ w + l.

Lemma lt_0_2ppw : 0 < 2 ^ (p + w).

  apply lt_0_Zpow. fold (0 + 0). apply Zplus_le_compat; auto with a. Qed.

Lemma lt_0_2pp : 0 < 2 ^ p.

  apply lt_0_Zpow. auto with a. Qed.

Local Hint Resolve lt_0_2pp : a.

Lemma le_0_wm1 : 0 <= w - 1.

  cut (0 < w). omega. exact lt_0_w. Qed.

Local Hint Resolve le_0_wm1 lt_0_w : a.

Lemma lt_p_w : p < w.

  rewrite p_M. apply Zle_lt_trans with (w - 1). rewrite <- Zlog_sup_pow. apply Zlog_sup_seq.
  assumption. auto with a. omega. Qed.

Lemma le_p_w : p <= w.

  apply Zlt_le_weak. exact lt_p_w. Qed.

Lemma le_0_wmp : 0 <= w - p.

  cut (p <= w). omega. exact le_p_w. Qed.

Local Hint Resolve lt_p_w le_p_w le_0_wmp : a.

Lemma lt_M_2pw : M < 2 ^ w.

  unfold M. apply lt_z__Z. Qed.

Lemma le_M_2pw : M <= 2 ^ w.

  apply Zlt_le_weak. exact lt_M_2pw. Qed.

Hint Resolve lt_M_2pw le_M_2pw : a.

Lemma d_Si_eq : 
  _Z d_Si = (h mod M * 2 ^ w + l) / 2 ^ p * 2 ^ p mod M \/
  _Z d_Si = (h mod M * 2 ^ w + l) / 2 ^ p * 2 ^ p mod M + M \/
  _Z d_Si = ((h mod M + M) * 2 ^ w + l) / 2 ^ p * 2 ^ p mod M \/
  _Z d_Si = ((h mod M + M) * 2 ^ w + l) / 2 ^ p * 2 ^ p mod M + M.

  unfold P' in d_Si_eq_r_Si_eq. tauto. Qed.

Lemma r_Si_eq_lit : 
   _Z r_Si = (d_Si + l mod 2 ^ p mod M) mod 2 ^ w.

  unfold P' in d_Si_eq_r_Si_eq. tauto. Qed.

Lemma r_Si_eq_a :
  _Z r_Si = (d_Si + (h mod M * 2 ^ w + l mod 2 ^ p mod M) mod 2 ^ p) mod 2 ^ w.

  replace (h mod M * 2 ^ w) with (0 + h mod M * 2 ^ (w - p + p)). rewrite Zpower_exp. rewrite Zmult_assoc.
  rewrite Zmod_plus_distr_l with (m := 2 ^ p). rewrite Z_mod_plus. rewrite modred with (x := 0). 
  replace (0 + l mod 2 ^ p mod M) with (l mod 2 ^ p mod M). rewrite modred with (m := 2 ^ p). exact r_Si_eq_lit. 
  apply Zmod_le_0_z. omega. apply Zlt_le_trans with M. apply Zmod_lt_z_m. omega. exact le_M_2pp. ring. omega. apply lt_0_Zpow.
  auto with a. apply Zlt_gt. apply Zlt_le_trans with M. omega. auto with a. apply lt_0_Zpow. auto with a. cut (p < w). omega.
  auto with a. apply Zle_ge. auto with a. replace (w - p + p) with w. ring. ring. Qed.

Lemma r_Si_eq_b : 
  _Z r_Si = (_Z d_Si + ((h mod M + M) * 2 ^ w + l mod 2 ^ p mod M) mod 2 ^ p) mod 2 ^ w.

  replace ((h mod M + M) * 2 ^ w) with (0 + (h mod M + M) * 2 ^ (w - p + p)). rewrite Zpower_exp. rewrite Zmult_assoc.
  rewrite Zmod_plus_distr_l with (m := 2 ^ p). rewrite Z_mod_plus. rewrite modred with (x := 0). 
  replace (0 + l mod 2 ^ p mod M) with (l mod 2 ^ p mod M). rewrite modred with (m := 2 ^ p). exact r_Si_eq_lit. 
  apply Zmod_le_0_z. omega. apply Zlt_le_trans with M. apply Zmod_lt_z_m. omega. exact le_M_2pp. ring. omega. apply lt_0_Zpow.
  auto with a. apply Zlt_gt. apply Zlt_le_trans with M. omega. auto with a. apply lt_0_Zpow. auto with a. cut (p < w). omega.
  auto with a. apply Zle_ge. auto with a. replace (w - p + p) with w. ring. ring. Qed.

Lemma p2wp : 2 ^ w = 2 ^ (w - p) * 2 ^ p.

  rewrite <- Zpower_exp. replace (w - p + p) with w. trivial. ring. cut (p < w). omega. auto with a. apply Zle_ge. auto with a.
  Qed.

Lemma mod2p : forall a b c', (a * 2 ^ w + b) mod 2 ^ p = (c' * 2 ^ w + b) mod 2 ^ p.

  intros a b c'. replace w with (w - p + p). rewrite Zpower_exp. do 2 rewrite Zmult_assoc. do 2 rewrite Zplus_comm with (m := b).
  rewrite Z_mod_plus. rewrite Z_mod_plus. trivial. apply Zlt_gt. apply lt_0_Zpow. auto with a. apply Zlt_gt. apply lt_0_Zpow.
  auto with a. cut (p < w). omega. auto with a. apply Zle_ge. auto with a. ring. Qed.

Lemma M1_r'_i_eq : M = 1 -> _Z r'_i = 0.

  intro H. unfold r'_i. elim (Zle_or_lt c d_Si); intro H0. rewrite ltw_false. simpl. rewrite r_Si_eq_lit. fold M.
  rewrite <- Zmod_minus_distr_l. rewrite H. cut (_Z d_Si = 1). intro H1. rewrite H1. rewrite mod_1_0. replace (1 + 0 - 1) with 0.
  apply modred. omega. auto with a. ring. rewrite c_M in H0. rewrite p_M in H0. rewrite H in H0. simpl in H0. cut (d_Si < 2).
  omega. elim d_Si_eq; intro H1. rewrite H1. apply Zlt_trans with M. apply Zmod_lt_z_m. omega. omega. elim H1; intro H2.
  rewrite H2. rewrite H. rewrite mod_1_0. omega. elim H2; intro H3. rewrite H3. rewrite H. rewrite mod_1_0. omega. rewrite H3.
  rewrite H. rewrite mod_1_0. omega. auto with a. assumption. cut (_Z d_Si = 0). intro H1. rewrite ltw_true. rewrite r_Si_eq_lit.
  rewrite H1. rewrite H. rewrite mod_1_0. simpl. apply modred. omega. exact lt02w. rewrite H1. fold c. rewrite c_M.
  auto with a. elim d_Si_eq; intro H1. rewrite H1. rewrite H. apply mod_1_0. rewrite c_M in H0. rewrite p_M in H0. 
  rewrite H in H0. simpl in H0. cut (0 <= d_Si). omega. apply le_0__Z. Qed.

Lemma M1_h_i_eq : M = 1 -> _Z h_i = 0.

  intro H. unfold h_i. simpl. rewrite M1_r'_i_eq. fold t. replace (2 ^ t * 0) with 0. apply modred. omega. auto with a. ring.
  assumption. Qed.

Lemma M1_h'_i_eq : M = 1 -> _Z h'_i = x_i.

  intro H. unfold h'_i. rewrite Z_from_plusw. rewrite M1_h_i_eq. unfold s''_i. rewrite ltw_true. unfold s_i. simpl. fold p.
  rewrite p_M. rewrite H. simpl. fold x_i. replace x_i with (x_i * 1). rewrite Z_div_mult. transitivity x_i. apply modred.
  unfold x_i. apply le_0__Z. unfold x_i. apply lt_z__Z. ring. omega. ring. rewrite M1_r'_i_eq. fold c. rewrite c_M. auto with a.
  assumption. assumption. Qed.

Lemma le_0_2pp : forall z : Z, 0 <= z mod 2 ^ p.

  intro z. apply Zmod_le_0_z. auto with a. Qed.

Lemma le_0_mod_M : forall z : Z, 0 <= z mod M.

  intro z. apply Zmod_le_0_z. omega. Qed.

Lemma lt_plus_M_2p_2w : forall a b : Z, a mod M + b mod 2 ^ p < 2 ^ w.

  intros a b. rewrite Zpow_2_w_is_2Zpow_2_wm1. apply Zplus_lt_compat. apply Zlt_le_trans with M. apply Zmod_lt_z_m. omega.
  assumption. apply Zlt_le_trans with (2 ^ p). apply Zmod_lt_z_m. auto with a. apply Zle_pow_le. auto with a. cut (p < w). omega.
  auto with a. Qed.

Lemma divmultmodM : forall a b : Z, (a * 2 ^ w + b) / 2 ^ p * 2 ^ p mod M = (a mod M * 2 ^ w + b) / 2 ^ p * 2 ^ p mod M.

  intros a b. replace w with (w - p + p). rewrite Zpower_exp. rewrite Zmult_assoc. rewrite Zdiv_times_plus.
  rewrite Zmod_mult_distr_l. rewrite Zmod_plus_distr_l. rewrite Zmod_mult_distr_l with (a := a). rewrite <- Zmod_plus_distr_l.
  rewrite <- Zmod_mult_distr_l. rewrite <- Zdiv_times_plus. rewrite <- Zmult_assoc. rewrite <- Zpower_exp. 
  replace (w - p + p) with w. trivial. ring. cut (p < w). omega. auto with a. apply Zle_ge. auto with a. auto with a. omega. omega.
  omega. omega. omega. auto with a. cut (p < w). omega. auto with a. apply Zle_ge. auto with a. ring. Qed.

Lemma r'0plus : forall a b : Z, (a * 2 ^ w + b) mod 2 ^ p = b mod 2 ^ p.

  intros a b. replace w with (w - p + p). rewrite Zpower_exp. rewrite Zmult_assoc. rewrite Zplus_comm. rewrite Z_mod_plus. trivial.
  apply Zlt_gt. apply lt_0_Zpow. auto with a. cut (p <= w). omega. auto with a. apply Zle_ge. auto with a. ring. Qed.

(* <KE EP TOGETHER - r'_i_eq *)
Lemma r'_i_eq : _Z r'_i = (h mod M * 2 ^ w + l) / 2 ^ p * 2 ^ p mod M + (h mod M * 2 ^ w + l mod 2 ^ p mod M) mod 2 ^ p \/
                _Z r'_i = (h mod M * 2 ^ w + l) / 2 ^ p * 2 ^ p mod M + M + (h mod M * 2 ^ w + l mod 2 ^ p mod M) mod 2 ^ p.
(* KE EP TOGETHER> *)

  unfold r'_i. elim d_Si_eq; intro H. left. rewrite ltw_true. rewrite r_Si_eq_a. rewrite H. apply modred. apply Zplus_le_0_compat.
  apply le_0_mod_M. apply le_0_2pp. apply lt_plus_M_2p_2w. rewrite H. apply Zlt_le_trans with M. apply Zmod_lt_z_m. omega.
  fold c. rewrite c_M. exact le_M_2pp. elim H; intro H0. elim (Zle_or_lt c d_Si); intro H1. rewrite ltw_false. simpl. left.
  rewrite r_Si_eq_a. rewrite H0. fold M. rewrite <- Zmod_minus_distr_l. 
  replace (((h mod M * 2 ^ w + l) / 2 ^ p * 2 ^ p) mod M + M + (h mod M * 2 ^ w + (l mod 2 ^ p) mod M) mod 2 ^ p - M)
     with (((h mod M * 2 ^ w + l) / 2 ^ p * 2 ^ p) mod M + (h mod M * 2 ^ w + (l mod 2 ^ p) mod M) mod 2 ^ p).
  apply modred. apply Zplus_le_0_compat. apply le_0_mod_M. apply le_0_2pp. apply lt_plus_M_2p_2w. ring. auto with a. assumption.
  rewrite ltw_true. right. rewrite r_Si_eq_a. rewrite <- H0. apply modred. apply Zplus_le_0_compat. apply le_0__Z. apply le_0_2pp.
  apply Zlt_le_trans with (c + 2 ^ p). apply Zplus_lt_compat. assumption. apply Zmod_lt_z_m. auto with a. 
  rewrite Zpow_2_w_is_2Zpow_2_wm1. apply Zplus_le_compat. rewrite c_M. apply Zle_pow_le. auto with a. cut (p < w). omega.
  auto with a. apply Zle_pow_le. auto with a. cut (p < w). omega. auto with a. assumption. elim H0; intro H1. left.
  rewrite ltw_true. rewrite r_Si_eq_b. rewrite H1.
  transitivity ((((((h mod M + M) * (2 ^ (w - p) * 2 ^ p) + l) / 2 ^ p * 2 ^ p) mod M + M +
    ((h mod M + M) * (2 ^ (w - p) * 2 ^ p) + l mod 2 ^ p mod M) mod 2 ^ p) mod 
      (2 ^ (w - p) * 2 ^ p) - M) mod (2 ^ (w - p) * 2 ^ p)). (* workaround *)
  rewrite <- p2wp. rewrite <- Zmod_minus_distr_l.
  replace ((((h mod M + M) * 2 ^ w + l) / 2 ^ p * 2 ^ p) mod M + M + ((h mod M + M) * 2 ^ w + (l mod 2 ^ p) mod M) mod 2 ^ p - M)
     with ((((h mod M + M) * 2 ^ w + l) / 2 ^ p * 2 ^ p) mod M + ((h mod M + M) * 2 ^ w + (l mod 2 ^ p) mod M) mod 2 ^ p).
  trivial. ring. exact lt02w. rewrite Zmult_assoc. rewrite mod_over_div. rewrite Zmod_mult_distr_l with (a := h mod M + M).
  replace (h mod M + M) with (h mod M + 1 * M). rewrite Z_mod_plus. rewrite <- Zmod_mult_distr_l. rewrite <- mod_over_div.
  rewrite <- Zmult_assoc. rewrite <- Zmult_assoc. rewrite <- Zpower_exp. replace (w - p + p) with w.
  rewrite mod2p with (c' := h mod M). rewrite <- Zmod_minus_distr_l.
  replace (((h mod M * 2 ^ w + l) / 2 ^ p * 2 ^ p) mod M + M + (h mod M * 2 ^ w + (l mod 2 ^ p) mod M) mod 2 ^ p - M)
     with (((h mod M * 2 ^ w + l) / 2 ^ p * 2 ^ p) mod M + (h mod M * 2 ^ w + (l mod 2 ^ p) mod M) mod 2 ^ p).
  apply modred. apply Zplus_le_0_compat. apply le_0_mod_M. apply le_0_2pp. apply lt_plus_M_2p_2w. ring. auto with a. ring.
  cut (p < w). omega. auto with a. apply Zle_ge. auto with a. auto with a. omega. omega. omega. ring. omega. auto with a.
  omega. rewrite H1. apply Zlt_le_trans with M. apply Zmod_lt_z_m. omega. fold c. rewrite c_M. exact le_M_2pp.
  elim (Zle_or_lt c d_Si); intro H2. rewrite ltw_false. simpl. left. rewrite r_Si_eq_b. rewrite H1. fold M.
  rewrite <- Zmod_minus_distr_l. 
  replace ((((h mod M + M) * 2 ^ w + l) / 2 ^ p * 2 ^ p) mod M + M + ((h mod M + M) * 2 ^ w + (l mod 2 ^ p) mod M) mod 2 ^ p - M)
     with ((((h mod M + M) * 2 ^ w + l) / 2 ^ p * 2 ^ p) mod M + ((h mod M + M) * 2 ^ w + (l mod 2 ^ p) mod M) mod 2 ^ p).
  rewrite modred. rewrite divmultmodM. rewrite Zmod_plus_m. rewrite <- divmultmodM. rewrite r'0plus. rewrite r'0plus. trivial.
  omega. apply Zplus_le_0_compat. apply le_0_mod_M. apply le_0_2pp. apply lt_plus_M_2p_2w. ring. auto with a. assumption.
  rewrite ltw_true. rewrite r_Si_eq_b. right. rewrite r'0plus. rewrite r'0plus. rewrite modred. rewrite H1. rewrite divmultmodM.
  rewrite Zmod_plus_m. rewrite <- divmultmodM. trivial. omega. apply Zplus_le_0_compat. apply le_0__Z. apply le_0_2pp.
  apply Zlt_le_trans with (c + 2 ^ p). apply Zplus_lt_compat. assumption. apply Zmod_lt_z_m. auto with a. 
  rewrite Zpow_2_w_is_2Zpow_2_wm1. apply Zplus_le_compat. rewrite c_M. apply Zle_pow_le. auto with a. cut (p < w). omega.
  auto with a. apply Zle_pow_le. auto with a. cut (p < w). omega. auto with a. assumption. Qed.

Lemma r'_i_eq'_i : _Z r'_i = x mod M \/ _Z r'_i = x mod M + M \/ _Z r'_i = x mod M + M + M.

  elim r'_i_eq; intro H; rewrite H. rewrite Zdiv_a_b_b_Zmod. replace w with (w - p + p). rewrite Zpower_exp.
  rewrite Zmult_assoc. rewrite Zmod_km_plus. rewrite Zmod_km_plus. rewrite modred with (x := l mod 2 ^ p mod M).
  rewrite <- Zmult_assoc. rewrite <- Zpower_exp. replace (w - p + p) with w.
  elim (mod_plus (h mod M * 2 ^ w + l - l mod 2 ^ p) (l mod 2 ^ p) M). intro H0; rewrite H0;
    replace (h mod M * 2 ^ w + l - l mod 2 ^ p + l mod 2 ^ p) with (h mod M * 2 ^ w + l). rewrite Zmod_plus_distr_l.
  rewrite <- Zmod_mult_distr_l. rewrite <- Zmod_plus_distr_l. tauto. omega. omega. omega. ring.
  intro H0; rewrite H0; replace (h mod M * 2 ^ w + l - l mod 2 ^ p + l mod 2 ^ p) with (h mod M * 2 ^ w + l).
  rewrite Zmod_plus_distr_l. rewrite <- Zmod_mult_distr_l. rewrite <- Zmod_plus_distr_l. tauto. omega. omega. omega. ring. omega.
  ring. cut (p < w). omega. auto with a. apply Zle_ge. auto with a. apply Zmod_le_0_z. omega. apply Zlt_le_trans with M.
  apply Zmod_lt_z_m. omega. exact le_M_2pp. apply lt_0_Zpow. auto with a. apply lt_0_Zpow. auto with a. cut (p < w). omega.
  auto with a. apply Zle_ge. auto with a. ring. apply lt_0_Zpow. auto with a. right.
  cut (((h mod M * 2 ^ w + l) / 2 ^ p * 2 ^ p) mod M + (h mod M * 2 ^ w + (l mod 2 ^ p) mod M) mod 2 ^ p = x mod M \/
       ((h mod M * 2 ^ w + l) / 2 ^ p * 2 ^ p) mod M + (h mod M * 2 ^ w + (l mod 2 ^ p) mod M) mod 2 ^ p = x mod M + M).
  omega.
  rewrite Zdiv_a_b_b_Zmod. replace w with (w - p + p). rewrite Zpower_exp.
  rewrite Zmult_assoc. rewrite Zmod_km_plus. rewrite Zmod_km_plus. rewrite modred with (x := l mod 2 ^ p mod M).
  rewrite <- Zmult_assoc. rewrite <- Zpower_exp. replace (w - p + p) with w.
  elim (mod_plus (h mod M * 2 ^ w + l - l mod 2 ^ p) (l mod 2 ^ p) M). 
  intro H0; rewrite H0; replace (h mod M * 2 ^ w + l - l mod 2 ^ p + l mod 2 ^ p) with (h mod M * 2 ^ w + l).
  rewrite Zmod_plus_distr_l. rewrite <- Zmod_mult_distr_l. rewrite <- Zmod_plus_distr_l. tauto. omega. omega. omega. ring.
  intro H0; rewrite H0; replace (h mod M * 2 ^ w + l - l mod 2 ^ p + l mod 2 ^ p) with (h mod M * 2 ^ w + l).
  rewrite Zmod_plus_distr_l. rewrite <- Zmod_mult_distr_l. rewrite <- Zmod_plus_distr_l. tauto. omega. omega. omega. ring. omega.
  ring. cut (p < w). omega. auto with a. apply Zle_ge. auto with a. apply Zmod_le_0_z. omega. apply Zlt_le_trans with M.
  apply Zmod_lt_z_m. omega. exact le_M_2pp. apply lt_0_Zpow. auto with a. apply lt_0_Zpow. auto with a. cut (p < w). omega.
  auto with a. apply Zle_ge. auto with a. ring. apply lt_0_Zpow. auto with a. Qed.

Lemma d_Si_small : d_Si < M + M.

  elim d_Si_eq; intro H. apply Zlt_trans with M. rewrite H. apply Zmod_lt_z_m. omega. omega. elim H; intro H0. rewrite H0.
  cut (((h mod M * 2 ^ w + l) / 2 ^ p * 2 ^ p) mod M < M). omega. apply Zmod_lt_z_m. omega. elim H0; intro H1.
  apply Zlt_trans with M. rewrite H1. apply Zmod_lt_z_m. omega. omega. rewrite H1. 
  cut ((((h mod M + M) * 2 ^ w + l) / 2 ^ p * 2 ^ p) mod M < M). omega. apply Zmod_lt_z_m. omega. Qed.

Lemma r'0_eq_1 :
  _Z r'0 = ((h mod M * 2 ^ w + l) / 2 ^ p * 2 ^ p mod M + l mod 2 ^ p mod M) mod 2 ^ w \/
  _Z r'0 = (((h mod M + M) * 2 ^ w + l) / 2 ^ p * 2 ^ p mod M + l mod 2 ^ p mod M) mod 2 ^ w.

  unfold r'0. elim d_Si_eq; intro H. left. rewrite ltw_true. unfold r0. rewrite r_Si_eq_lit. rewrite H. trivial. unfold d0.
  rewrite H. fold M. apply Zmod_lt_z_m. omega. elim H; intro H0. left. rewrite ltw_false. simpl. unfold r0. rewrite r_Si_eq_lit.
  rewrite <- Zmod_minus_distr_l. fold M. rewrite H0. apply f_equal2 with (f := Zmod). ring. trivial. auto with a. fold M.
  unfold d0. rewrite H0. cut (0 <= ((h mod M * 2 ^ w + l) / 2 ^ p * 2 ^ p) mod M). omega. apply Zmod_le_0_z. omega. elim H0;
  intro H1. right. rewrite ltw_true. unfold r0. rewrite r_Si_eq_lit. rewrite H1. trivial. unfold d0. rewrite H1. fold M.
  apply Zmod_lt_z_m. omega. right. rewrite ltw_false. simpl. unfold r0. rewrite r_Si_eq_lit. rewrite <- Zmod_minus_distr_l. fold M.
  rewrite H1. apply f_equal2 with (f := Zmod). ring. trivial. auto with a. fold M. unfold d0. rewrite H1. 
  cut (0 <= (((h mod M + M) * 2 ^ w + l) / 2 ^ p * 2 ^ p) mod M). omega. apply Zmod_le_0_z. omega. Qed.

Lemma r'0_eq_2 :
  _Z r'0 = (h mod M * 2 ^ w + l) / 2 ^ p * 2 ^ p mod M + l mod 2 ^ p mod M \/
  _Z r'0 = ((h mod M + M) * 2 ^ w + l) / 2 ^ p * 2 ^ p mod M + l mod 2 ^ p mod M.

  elim r'0_eq_1; intro H; rewrite H. left. apply modred. apply Zplus_le_0_compat. apply Zmod_le_0_z. omega. apply Zmod_le_0_z.
  omega. rewrite Zpow_2_w_is_2Zpow_2_wm1. apply Zplus_lt_compat. apply Zlt_le_trans with M. apply Zmod_lt_z_m. omega. assumption.
  apply Zlt_le_trans with M. apply Zmod_lt_z_m. omega. assumption. right. apply modred. apply Zplus_le_0_compat. apply Zmod_le_0_z.
  omega. apply Zmod_le_0_z. omega. rewrite Zpow_2_w_is_2Zpow_2_wm1. apply Zplus_lt_compat. apply Zlt_le_trans with M.
  apply Zmod_lt_z_m. omega. assumption. apply Zlt_le_trans with M. apply Zmod_lt_z_m. omega. assumption. Qed.

Lemma r'0_eq_5 : forall b : Z, ((b mod M + M) * 2 ^ w + l) mod M = (b * 2 ^ w + l) mod M.

  intro b. rewrite Zmod_plus_distr_l. rewrite Zmod_mult_distr_l. replace (b mod M + M) with (b mod M + 1 * M). rewrite Z_mod_plus.
  rewrite modred with (x := b mod M). rewrite <- Zmod_mult_distr_l. rewrite <- Zmod_plus_distr_l. trivial. omega. omega.
  apply Zmod_le_0_z. omega. apply Zmod_lt_z_m. omega. omega. ring. omega. omega. Qed.

Lemma r'0_eq_6 : forall b : Z, (b * 2 ^ w + l) mod 2 ^ p = l mod 2 ^ p.

  intro b. replace w with (w - p + p). rewrite Zpower_exp. rewrite Zmult_assoc. rewrite Zplus_comm. rewrite Z_mod_plus. trivial.
  apply Zlt_gt. apply lt_0_Zpow. auto with a. cut (p <= w). omega. auto with a. apply Zle_ge. auto with a. ring. Qed.

Lemma r'0_eq_7 : 
  _Z r'0 = (h mod M * 2 ^ w + l) / 2 ^ p * 2 ^ p mod M + (h mod M * 2 ^ w + l) mod 2 ^ p mod M \/
  _Z r'0 = ((h mod M + M) * 2 ^ w + l) / 2 ^ p * 2 ^ p mod M + ((h mod M + M) * 2 ^ w + l) mod 2 ^ p mod M.

  elim r'0_eq_2; intro H; rewrite H. left. apply f_equal2 with (f := Zplus). trivial. symmetry. apply f_equal2 with (f := Zmod).
  apply r'0_eq_6. trivial. right. apply f_equal2 with (f := Zplus). trivial. symmetry. apply f_equal2 with (f := Zmod).
  apply r'0_eq_6. trivial. Qed.

Lemma r'0_eq_8 : forall a b : Z, a = b / 2 ^ p * 2 ^ p mod M + b mod 2 ^ p mod M -> a = b mod M \/ a = b mod M + M.

  intros a b H. elim (mod_plus (b / 2 ^ p * 2 ^ p) (b mod 2 ^ p) M). intro H0. left. rewrite H. rewrite H0. rewrite Zdivmod_split.
  trivial. apply lt_0_Zpow. auto with a. intro H0. right. rewrite H. rewrite H0. rewrite Zdivmod_split. trivial. apply lt_0_Zpow.
  auto with a. omega. Qed.

Lemma r'0_eq_9 :
  (_Z r'0 = (h mod M * 2 ^ w + l) mod M \/ _Z r'0 = (h mod M * 2 ^ w + l) mod M + M) \/
  (_Z r'0 = ((h mod M + M) * 2 ^ w + l) mod M \/ _Z r'0 = ((h mod M + M) * 2 ^ w + l) mod M + M).

  elim r'0_eq_7; intro H; rewrite H. left. apply r'0_eq_8. trivial. right. apply r'0_eq_8. trivial. Qed.

Lemma r'0_eq : _Z r'0 = x mod M \/ _Z r'0 = x mod M + M.

  elim r'0_eq_9; intro H. elim H; intro H0; rewrite H0. left. rewrite Zmod_plus_distr_l. rewrite <- Zmod_mult_distr_l. 
  rewrite <- Zmod_plus_distr_l. trivial. omega. omega. omega. right. rewrite Zmod_plus_distr_l. rewrite <- Zmod_mult_distr_l.
  rewrite <- Zmod_plus_distr_l. trivial. omega. omega. omega. elim H; intro H0; rewrite H0. left. rewrite r'0_eq_5. trivial.
  rewrite r'0_eq_5. right. trivial. Qed.

(* <KE EP TOGETHER - r''0_eq *) (* TO DO *)
Lemma r''0_eq : _Z r''0 = x mod M.
(* KE EP TOGETHER> *)

  unfold r''0. unfold r''0. (* Proof General beta oddity *) elim r'0_eq; intro H. rewrite ltw_true. trivial. rewrite H. apply Zmod_lt_z_m. fold M. omega. rewrite ltw_false.
  simpl. rewrite H. fold M. replace (x mod M + M - M) with (x mod M). apply modred.
  apply Zmod_le_0_z. omega. apply Zlt_trans with M. apply Zmod_lt_z_m. omega. unfold M. apply lt_z__Z. ring. rewrite H. fold M.
  cut (0 <= x mod M). omega. apply Zmod_le_0_z. omega. Qed.

Lemma r'_small : r'_i < 2 ^ p + M.

  unfold r'_i. elim (Zle_or_lt c d_Si); intro H. rewrite ltw_false. simpl. rewrite r_Si_eq_lit. rewrite <- Zmod_minus_distr_l.
  fold M. rewrite modred. cut (d_Si < 2 ^ p + M). cut (l mod 2 ^ p mod M < M). omega. apply Zmod_lt_z_m. omega. 
  apply Zlt_le_trans with (M + M). exact d_Si_small. apply Zplus_le_compat. exact le_M_2pp. omega. 
  cut (0 <= d_Si - M). cut (0 <= (l mod 2 ^ p) mod M). omega. apply Zmod_le_0_z. omega. cut (M <= d_Si). omega. 
  apply Zle_trans with (2 ^ p). exact le_M_2pp. omega. cut ((l mod 2 ^ p) mod M < M). cut (d_Si < 2 ^ w). omega. apply lt_z__Z.
  apply Zmod_lt_z_m. omega. exact lt02w. assumption. rewrite ltw_true. rewrite r_Si_eq_lit. rewrite modred.
  apply Zplus_lt_compat. apply Zlt_le_trans with c. assumption. omega. apply Zmod_lt_z_m. omega. apply Zplus_le_0_compat.
  apply le_0__Z. apply Zmod_le_0_z. omega. rewrite Zpow_2_w_is_2Zpow_2_wm1. apply Zlt_le_trans with (c + M). apply Zplus_lt_compat.
  assumption. apply Zmod_lt_z_m. omega. apply Zplus_le_compat. rewrite c_M. apply Zle_pow_le. auto with a. cut (p < w). omega.
  auto with a. omega. assumption. Qed.

Let r'a := ltw r'_i c_in_Z_ r'_i (minusw r'_i M_in_Z_).

Lemma r'a_small : r'a < 2 ^ p.

  unfold r'a. elim (Zle_or_lt c r'_i); intro H. rewrite ltw_false. simpl. fold M. rewrite modred. cut (r'_i < 2 ^ p + M).
  omega. exact r'_small. cut (M <= r'_i). omega. apply Zle_trans with c. rewrite c_M. exact le_M_2pp. omega. 
  cut (r'_i < 2 ^ w). cut (0 < M). omega. omega. apply lt_z__Z. assumption. rewrite ltw_true. rewrite <- c_M. assumption. 
  assumption. Qed.

Lemma r'a_eq : _Z r'a = x mod M \/ _Z r'a = x mod M + M.

  unfold r'a. elim (Zle_or_lt c r'_i); intro H. rewrite ltw_false. elim r'_i_eq'_i; intro H0. rewrite H0 in H. 
  absurd (c <= x mod M). apply Zlt_not_le. apply Zlt_le_trans with M. apply Zmod_lt_z_m. omega. rewrite c_M. exact le_M_2pp.
  assumption. simpl. fold M. elim H0; intro H1. rewrite H1. replace (x mod M + M - M) with (x mod M). rewrite modred. tauto.
  apply Zmod_le_0_z. omega. apply Zlt_trans with M. apply Zmod_lt_z_m. omega. unfold M. apply lt_z__Z. ring. rewrite H1.
  replace (x mod M + M + M - M) with (x mod M + M). rewrite modred. tauto. apply Zplus_le_0_compat. apply Zmod_le_0_z. omega.
  omega. rewrite Zpow_2_w_is_2Zpow_2_wm1. apply Zplus_lt_le_compat. apply Zlt_le_trans with M. apply Zmod_lt_z_m. omega.
  assumption. assumption. ring. assumption. rewrite ltw_true. elim r'_i_eq'_i; intro H0. tauto. elim H0; intro H1.
  tauto. rewrite H1 in H. absurd (x mod M + M + M <= c). apply Zlt_not_le. cut (c < M + M). cut (0 <= x mod M). omega.
  apply Zmod_le_0_z. omega. elim (Zle_lt_or_eq 0 p). intro H2. apply Zlt_le_trans with (2 ^ (p - 1) + 1 + (2 ^ (p - 1) + 1)). 
  replace (2 ^ (p - 1) + 1 + (2 ^ (p - 1) + 1)) with (2 ^ 1 * 2 ^ (p - 1) + 2). rewrite <- Zpower_exp.
  replace (1 + (p - 1)) with p. omega. ring. omega. omega. ring. apply Zplus_le_compat. elim lt_2pm1_M; intro H3. omega. 
  rewrite H3 in p_M. simpl in p_M. rewrite p_M in H2. absurd (0 < 0); omega. elim lt_2pm1_M; intro H3. omega. 
  rewrite H3 in p_M. simpl in p_M. rewrite p_M in H2. absurd (0 < 0); omega. intro H2. rewrite c_M. rewrite <- H2. simpl. omega.
  unfold p. apply le_0__Z. omega. assumption. Qed.

Let x' := r'a * 2 ^ w + x_i.

Lemma x_i_eq : x_i = x' mod 2 ^ w.

  unfold x'. rewrite Zmod_km_plus. symmetry. unfold x_i. apply modred. apply le_0__Z. apply lt_z__Z. exact lt02w. Qed.

(* <KE EP TOGETHER - s_i_eq *)
Lemma s_i_eq : _Z s_i = x' mod 2 ^ w / 2 ^ p.
(* KE EP TOGETHER> *)

  simpl. fold l. fold p. fold x_i. rewrite x_i_eq. trivial. Qed.

(* <KE EP TOGETHER - s'_i_eq *)
Lemma s'_i_eq : _Z s'_i = x' mod 2 ^ w - x' mod 2 ^ p.
(* KE EP TOGETHER> *)

  unfold s'_i. rewrite Z_from_multp2. fold p. rewrite s_i_eq. rewrite Zmult_comm. rewrite modred.
  replace (x' mod 2 ^ p) with (x' mod 2 ^ w mod 2 ^ p). apply Zdiv_a_b_b_Zmod. auto with a.
  replace (2 ^ w) with (2 ^ (w - p) * 2 ^ p). apply Zmod_prod_Zmod. apply lt_0_Zpow. auto with a.
  auto with a. rewrite <- Zpower_exp. apply f_equal2 with (f := Zpower). trivial. ring. apply Zle_ge.
  auto with a. apply Zle_ge. auto with a. fold (0 * 0). apply Zmult_le_compat. apply Zle_0_div. 
  apply Zmod_le_0_z. auto with a. auto with a. apply Zlt_le_weak. auto with a. omega. omega. 
  apply Zle_lt_trans with (x' mod 2 ^ w). rewrite Zmult_comm. apply Z_mult_div_ge. apply Zlt_gt.
  auto with a. apply Zmod_lt_z_m. auto with a. Qed.

Lemma le_0_x' : 0 <= x'.

  unfold x'. fold (0 + 0). apply Zplus_le_compat; auto with a. apply Zmult_le_0_compat. apply le_0__Z.
  auto with a. unfold x_i. apply le_0__Z. Qed.

Local Hint Resolve le_0_x' : a.

Lemma lt_x'_x'max : x' < 2 ^ (p + w).

  unfold x'. apply Zle_lt_trans with ((2 ^ p - 1) * 2 ^ w + (2 ^ w - 1)). apply Zplus_le_compat. apply Zmult_le_compat.
  cut (r'a < 2 ^ p). omega. exact r'a_small. omega. apply le_0__Z. apply Zlt_le_weak. exact lt02w. cut (x_i < 2 ^ w). omega.
  unfold x_i. apply lt_z__Z. rewrite Zmult_minus_distr_r. rewrite <- Zpower_exp. omega. apply Zle_ge. auto with a. apply Zle_ge.
  auto with a. Qed.

Lemma le_x'_x'max : x' <= 2 ^ (p + w) - 1.

  cut (x' < 2 ^ (p + w)). omega. exact lt_x'_x'max. Qed.

Local Hint Resolve lt_x'_x'max le_x'_x'max : a.

Lemma h'_i_eq_mod : M = 1 \/ _Z h'_i = (x' / 2 ^ p) mod 2 ^ w.

  elim t_M; intro Ht. right. unfold h'_i. simpl. fold t. rewrite <- Zmod_plus_distr_l. unfold s''_i. unfold x'. unfold r'a.
  unfold s_i. elim (Zle_or_lt c r'_i); intro H. rewrite ltw_false. rewrite ltw_false. simpl. fold p. fold x_i. fold p.
  fold M''. fold M. transitivity ((((r'_i - M) mod 2 ^ w * 2 ^ (w - p + p) + x_i) / 2 ^ p) mod 2 ^ w). rewrite Zpower_exp.
  rewrite Zmult_assoc. rewrite Zdiv_times_plus. rewrite M''_M. rewrite <- Zmod_minus_distr_r. rewrite Zplus_comm.
  rewrite Zmod_plus_distr_l with (b := x_i / 2 ^ p). rewrite <- Zmod_mult_distr_l. rewrite <- Zmod_plus_distr_l.
  rewrite <- Zmod_plus_distr_l. rewrite Zmult_minus_distr_r. rewrite Ht. apply f_equal2 with (f := Zmod). ring. trivial.
  exact lt02w. exact lt02w. exact lt02w. exact lt02w. exact lt02w. apply lt_0_Zpow. auto with a. cut (p < w). omega. auto with a.
  apply Zle_ge. auto with a. replace (w - p + p) with w. trivial. ring. assumption. assumption. rewrite ltw_true. rewrite ltw_true.
  rewrite Zmult_comm. (* replace w with (w - p + p). *)  (* Does not work... *)
  transitivity (((r'_i * 2 ^ (w - p + p) + x_i) / 2 ^ p) mod 2 ^ w). (* ... *)
  rewrite Zpower_exp. rewrite Zmult_assoc. rewrite Zdiv_times_plus. rewrite Ht. simpl. fold x_i. fold p. trivial. apply lt_0_Zpow.
  auto with a. cut (p < w). omega. auto with a. apply Zle_ge. auto with a. replace (w - p + p) with w. trivial. ring. assumption.
  assumption. auto with a. tauto. Qed.

Lemma M1_r'a : M = 1 \/ _Z h'_i = x' / 2 ^ p.

  elim h'_i_eq_mod; intro H. tauto. right. rewrite H. apply modred. apply Zle_0_div. exact le_0_x'. apply lt_0_Zpow.
  auto with a. apply Zle_lt_trans with ((2 ^ (p + w) - 1) / 2 ^ p). apply Zdiv_le. apply lt_0_Zpow. auto with a. 
  exact le_x'_x'max. rewrite Zplus_comm. rewrite Zpower_exp. rewrite Zdiv_mult_minus. omega. apply lt_0_Zpow. auto with a. 
  omega. cut (0 < 2 ^ p). omega. apply lt_0_Zpow. auto with a. apply Zle_ge. auto with a. apply Zle_ge. auto with a. Qed.

(* <KE EP TOGETHER - q_i_eq_ch *)
Lemma q_i_eq_ch : 
  M = 1 \/ _Z q_i = x' / 2 ^ p * (2 ^ (p + w) / M mod 2 ^ w) / 2 ^ w.
(* KE EP TOGETHER> *)

  elim M1_r'a; intro H. tauto. right. unfold q_i. rewrite uhwm_eq. rewrite H. fold M'. rewrite M'_M. trivial. Qed.

(* <KE EP TOGETHER - q_i_eq *)
Lemma q_i_eq : 
  _Z q_i = x' / 2 ^ p * (2 ^ (p + w) / M mod 2 ^ w) / 2 ^ w.
(* KE EP TOGETHER> *)

  elim (Zle_lt_or_eq 1 M). intro H. elim q_i_eq_ch; intro H0. absurd (1 < M); omega. assumption. intro H. unfold q_i. 
  rewrite uhwm_eq. fold M'. rewrite M'_M. rewrite <- H. replace (2 ^ (p + w)) with (2 ^ (p + w) * 1). rewrite Z_div_mult.
  rewrite Zpower_exp. rewrite Zmult_comm with (m := 2 ^ w). rewrite Zmod_mult_distr_l. rewrite Z_mod_same. 
  replace (0 * 2 ^ p) with 0. rewrite modred. replace (_Z h'_i * 0) with 0. replace (x' / 2 ^ p * 0) with 0. trivial. ring. ring.
  omega. exact lt02w. ring. apply Zlt_gt. exact lt02w. exact lt02w. apply Zle_ge. auto with a. apply Zle_ge. auto with a. omega.
  ring. omega. Qed.

Lemma q'_i_eq_pre_ch : 
  M = 1 \/ _Z q'_i = (x' / 2 ^ p * (2 ^ (p + w) / M) / 2 ^ w) mod 2 ^ w.

  elim M1_r'a; intro H. tauto. right. unfold q'_i. rewrite Z_from_plusw. rewrite q_i_eq. rewrite H. 
  rewrite Zplus_comm. rewrite <- Zdiv_times_plus. rewrite <- Zmult_plus_distr_r. rewrite large_M'_eq. trivial. auto with a. Qed.

Lemma q'_i_eq_pre : _Z q'_i = (x' / 2 ^ p * (2 ^ (p + w) / M) / 2 ^ w) mod 2 ^ w.

  elim q'_i_eq_pre_ch; intro H. unfold q'_i. rewrite Z_from_plusw. rewrite q_i_eq. rewrite M1_h'_i_eq. rewrite p_M. rewrite H.
  simpl. do 2 rewrite div_1_id. rewrite Z_div_mult. rewrite Z_mod_same. replace (x' * 0) with 0. rewrite Zdiv_small_0. simpl.
  unfold x'. symmetry. apply Zmod_km_plus. auto with a. omega. auto with a. ring. apply Zlt_gt. auto with a. apply Zlt_gt.
  auto with a. assumption. assumption. Qed.

Lemma mod_ab_mod : forall z a b m : Z, 0 < m ->
  z = a \/ z = b -> z mod m = a mod m \/ z mod m = b mod m.

  intros z a b m H H0. elim H0; intro H1; rewrite H1; tauto. Qed.

(* <KE EP TOGETHER - q'_i_eq *)
Lemma q'_i_eq :
  _Z q'_i = (x' / 2 ^ p * 2 ^ p / M) mod 2 ^ w \/
  _Z q'_i = (x' / 2 ^ p * 2 ^ p / M - 1) mod 2 ^ w.
(* KE EP TOGETHER> *)

  rewrite q'_i_eq_pre. apply mod_ab_mod. auto with a.
  cut (x' / 2 ^ p * (2 ^ p * 2 ^ w / M) / 2 ^ w = x' / 2 ^ p * 2 ^ p / M - 1 \/
       x' / 2 ^ p * (2 ^ p * 2 ^ w / M) / 2 ^ w = x' / 2 ^ p * 2 ^ p / M).
  rewrite Zpower_exp. tauto. apply Zle_ge. auto with a. apply Zle_ge. auto with a.
  cut (x' / 2 ^ p * 2 ^ p / M - 1 <= x' / 2 ^ p * (2 ^ p * 2 ^ w / M) / 2 ^ w).
  cut (x' / 2 ^ p * (2 ^ p * 2 ^ w / M) / 2 ^ w <= x' / 2 ^ p * 2 ^ p / M). intros H H0.
  elim (Zle_lt_or_eq (x' / 2 ^ p * (2 ^ p * 2 ^ w / M) / 2 ^ w) (x' / 2 ^ p * 2 ^ p / M)). intro H1. left.
  omega. intro H1. right. omega. assumption. apply approx_0_one. omega. auto with a. auto with a.
  auto with a. apply approx_m1_one. auto with a. auto with a. omega. auto with a. 
  cut (x' < 2 ^ p * 2 ^ w). cut (0 < 2 ^ p). omega. auto with a. rewrite <- Zpower_exp. auto with a. 
  apply Zle_ge. auto with a. apply Zle_ge. auto with a. Qed.

(* <KE EP TOGETHER - y_i_eq *)
Lemma y_i_eq :
  _Z y_i = x' / 2 ^ p * 2 ^ p / M * M mod 2 ^ w \/
  _Z y_i = (x' / 2 ^ p * 2 ^ p / M * M - M) mod 2 ^ w.
(* KE EP TOGETHER> *)
  
  unfold y_i. rewrite Z_from_multw. fold M. elim q'_i_eq; intro H; rewrite H. left. 
  rewrite <- Zmod_mult_distr_l. trivial. auto with a. right. rewrite <- Zmod_mult_distr_l.
  apply f_equal2 with (f := Zmod). ring. trivial. auto with a. Qed.

(* <KE EP TOGETHER - d_i_eq *)
Lemma d_i_eq :
  _Z d_i = x' / 2 ^ p * 2 ^ p mod M \/
  _Z d_i = x' / 2 ^ p * 2 ^ p mod M + M.
(* KE EP TOGETHER> *)

  unfold d_i. rewrite Z_from_minusw. rewrite s'_i_eq. rewrite Zmod_minus_distr_l.
  rewrite <- Zmod_minus_distr_l with (b := x' mod 2 ^ p). rewrite <- Zmod_minus_distr_l.
  rewrite <- Zdiv_a_b_b_Zmod. elim y_i_eq; intro H. left. rewrite H. rewrite <- Zmod_minus_distr_r.
  rewrite Zminus_Zdiv_Zmult. apply modred. apply Zmod_le_0_z. omega. apply Zlt_le_trans with M.
  apply Zmod_lt_z_m. omega. auto with a. omega. auto with a. right. rewrite H. 
  rewrite <- Zmod_minus_distr_r. 
  replace (x' / 2 ^ p * 2 ^ p - (x' / 2 ^ p * 2 ^ p / M * M - M))
     with (x' / 2 ^ p * 2 ^ p - x' / 2 ^ p * 2 ^ p / M * M + M). rewrite Zminus_Zdiv_Zmult. apply modred.
  fold (0 + 0). apply Zplus_le_compat. apply Zmod_le_0_z. omega. omega. apply Zlt_le_trans with (M + M).
  apply Zplus_lt_le_compat. apply Zmod_lt_z_m. omega. omega. rewrite Zpow_2_w_is_2Zpow_2_wm1. omega. omega.
  ring. auto with a. auto with a. auto with a. auto with a. auto with a. Qed.

(* <KE EP TOGETHER - rrr_i_eq *)
Lemma rrr_i_eq : _Z rrr_i = (_Z d_i + x' mod 2 ^ p) mod 2 ^ w.
(* KE EP TOGETHER> *)

  unfold rrr_i. unfold d_i. rewrite Z_from_minusw. rewrite Z_from_minusw. fold l. rewrite s'_i_eq.
  rewrite Zmod_minus_distr_l with (a := x' mod 2 ^ w - x' mod 2 ^ p).
  rewrite <- Zmod_minus_distr_l with (a := x'). rewrite <- Zmod_minus_distr_l. rewrite <- Zmod_plus_distr_l. fold x_i.
  replace (x' - x' mod 2 ^ p - _Z y_i + x' mod 2 ^ p) with (x' - _Z y_i). rewrite x_i_eq. 
  rewrite <- Zmod_minus_distr_l. trivial. auto with a. ring. auto with a. auto with a. auto with a.
  auto with a. Qed.

Lemma l'_i_eq : _Z l'_i = x' mod 2 ^ p.

  unfold l'_i. rewrite Z_from_minusw. fold x_i. rewrite s'_i_eq. unfold x'. rewrite Zmod_km_plus. rewrite modred with (x := x_i).
  replace (x_i - (x_i - (r'a * 2 ^ w + x_i) mod 2 ^ p)) with ((r'a * 2 ^ w + x_i) mod 2 ^ p). apply modred.
  apply Zmod_le_0_z. apply lt_0_Zpow. auto with a. apply Zlt_le_trans with (2 ^ p). apply Zmod_lt_z_m. apply lt_0_Zpow. 
  auto with a. apply Zle_pow_le. auto with a. cut (p < w). omega. auto with a. ring. unfold x_i. apply le_0__Z. unfold x_i.
  apply lt_z__Z. auto with a. Qed.

Lemma le2ppMM : 2 ^ p < M + M. 

  elim (Zle_or_lt M 1); intro H. cut (M = 1). intro H0. rewrite p_M. rewrite H0. simpl. omega. omega.
  elim lt_2pm1_M; intro H0. replace p with (p - 1 + 1). rewrite Zpower_exp. replace (2 ^ 1) with 2. omega. trivial.
  cut (1 <= p). omega. elim le_1_p; intro H1. assumption. absurd (1 < M); omega. omega. ring. rewrite p_M. rewrite H0. simpl.
  omega. Qed.

Lemma r_i_eq : _Z r_i = (_Z d_i + x' mod 2 ^ p mod M) mod 2 ^ w.

  unfold r_i. elim (Zle_or_lt M (_Z l'_i)); intro H. rewrite ltw_false. rewrite Z_from_minusw. rewrite rrr_i_eq. fold M.
  rewrite <- l'_i_eq. rewrite <- Zmod_minus_distr_l. replace (_Z d_i + _Z l'_i - M) with (_Z d_i + (_Z l'_i - M)).
  replace (_Z l'_i - M) with (_Z l'_i mod M). trivial. rewrite l'_i_eq. rewrite l'_i_eq in H. rewrite <- Zmod_minus_m.
  apply modred. omega. cut (x' mod 2 ^ p < M + M). omega. apply Zlt_le_trans with (2 ^ p). apply Zmod_lt_z_m. apply lt_0_Zpow.
  auto with a. apply Zlt_le_weak. exact le2ppMM. omega. ring. auto with a. assumption. rewrite ltw_true. rewrite rrr_i_eq.
  rewrite l'_i_eq in H. rewrite modred with (m := M). trivial. apply Zmod_le_0_z. apply lt_0_Zpow. auto with a. assumption.
  assumption. Qed.

Definition d_ir_i := (d_i, r_i).

Lemma d_i_r_i_eq : P' M p d_i r_i x x_i_in_Z_.

  unfold P'. split. elim d_i_eq; unfold x'. elim r'a_eq; intro H; rewrite H. tauto. tauto. elim r'a_eq; intro H; rewrite H. tauto.
  tauto. fold x_i. replace (x_i mod 2 ^ p) with (x' mod 2 ^ p). exact r_i_eq. unfold x'. rewrite mod2p with (c' := 0).
  apply f_equal2 with (f := Zmod). ring. trivial. Qed.

End parm_sec.

Section repeat.

Variable M_in_Z_ : Z_ (2 ^ w).

Variable ptM'cM'' : Z_ w * Z_ w * Z_ (2 ^ w) * Z_ (2 ^ w) * Z_ (2 ^ w).
Variable x : Z. (* multi-word *)

Let p_in_Z_w := fst (fst (fst (fst ptM'cM''))).
Let t_in_Z_w := snd (fst (fst (fst ptM'cM''))).
Let M'_in_Z_ := snd (fst (fst ptM'cM'')).
Let c_in_Z_ := snd (fst ptM'cM'').
Let M''_in_Z_ := snd ptM'cM''.

Let M := _Z M_in_Z_.
Let p := _Z p_in_Z_w.
Let t := _Z t_in_Z_w.
Let c := _Z c_in_Z_.
Let M'' := _Z M''_in_Z_.
Let M' := _Z M'_in_Z_.

Hypothesis le_1_M : 1 <= M.
Hypothesis le_M_max : M <= 2 ^ (w - 1).
Hypothesis p_M : p = Zlog_sup M.
Hypothesis t_M : t = w - p \/ M = 1.
Hypothesis c_M : c = 2 ^ p.
Hypothesis M''_M : M'' = (2 ^ t * M) mod 2 ^ w.
Hypothesis M'_M : M' = 2 ^ (p + w) / M mod 2 ^ w.

Definition x_ (i : nat) := exist (in_Z_ (2 ^ w)) (x / 2 ^ (Z_of_nat i * w) mod 2 ^ w) (mod_in_Z__ (x / 2 ^ (Z_of_nat i * w))).

Definition f' (d_Sir_Si : Z_ (2 ^ w) * Z_ (2 ^ w)) (xi : Z_ (2 ^ w)) :=
  (d_i M_in_Z_ ptM'cM'' d_Sir_Si xi, r_i M_in_Z_ ptM'cM'' d_Sir_Si xi).

Fixpoint foldlz (f : Z_ (2 ^ w) * Z_ (2 ^ w) -> Z_ (2 ^ w) -> Z_ (2 ^ w) * Z_ (2 ^ w)) (d_Sir_Si : Z_ (2 ^ w) * Z_ (2 ^ w)) (a:nat) {struct a} : 
 Z_ (2 ^ w) * Z_ (2 ^ w) :=
  match a with
  | O   => d_Sir_Si
  | S i => foldlz f (f d_Sir_Si (x_ i)) i
  end.

Lemma P'f' : forall (d r : Z_ (2 ^ w)) (h : Z) (l x_i : Z_ (2 ^ w)),
  P' M p d r h l -> P' M p (fst (f' (d, r) x_i)) (snd (f' (d, r) x_i)) (h * 2 ^ w + l) x_i.

  intros d r  h l x_i H. unfold f'. unfold M. unfold p. unfold p_in_Z_w. simpl. 
  apply d_i_r_i_eq; fold p_in_Z_w; fold M; fold p. assumption. omega. assumption. 
  assumption. assumption. assumption. assumption. assumption. Qed.

Lemma P'f'x : forall (d r : Z_ (2 ^ w)) (n : nat),
  P' M p d r (x / 2 ^ ((Z_of_nat n + 2) * w)) (x_ (S n)) ->
  P' M p (fst (f' (d, r) (x_ n))) (snd (f' (d, r) (x_ n))) (x / 2 ^ ((Z_of_nat n + 1) * w)) (x_ n).

  intros d r n H. 
  rewrite Z_div_mod_eq with (a := x / 2 ^ ((Z_of_nat n + 1) * w)) (b := 2 ^ w). rewrite Zdivdivdiv. rewrite <- Zpower_exp. 
  replace ((Z_of_nat n + 1) * w + w) with ((Z_of_nat n + 2) * w). replace (Z_of_nat n + 1) with (Z_of_nat (S n)).
  replace ((x / 2 ^ (Z_of_nat (S n) * w)) mod 2 ^ w) with (_Z (x_ (S n))). rewrite Zmult_comm. 
  apply P'f'. trivial. trivial. trivial.
  trivial. rewrite inj_S. ring. ring. apply Zle_ge. apply Zmult_le_0_compat. omega. exact le_0_w.
  apply Zle_ge. exact le_0_w. apply lt_0_Zpow. apply Zmult_le_0_compat. omega. exact le_0_w. exact lt02w. apply Zlt_gt.
  exact lt02w. Qed.

Lemma P'foldlz : forall (n : nat) (d r : Z_ (2 ^ w)),
  P' M p d r (x / 2 ^ ((Z_of_nat n + 2) * w)) (x_ (S n)) ->
  P' M p (fst (foldlz f' (d, r) (S n))) (snd (foldlz f' (d, r) (S n))) (x / 2 ^ w) (x_ O).

  induction n. intros d r. intro H.
  replace (foldlz f' (d, r) 1) with (f' (d, r) (x_ 0)).
  (* replace w with ((Z_of_nat 0 + 1) * w). *) (* does not work *)
  cut (P' M p (fst (f' (d, r) (x_ 0))) (snd (f' (d, r) (x_ 0))) (x / 2 ^ ((Z_of_nat 0 + 1) * w)) (x_ 0)). (* workaroud *)
  replace ((Z_of_nat 0 + 1) * w) with w. (* works *) trivial. ring. apply P'f'x. assumption. trivial. intros d r. intro H.
  replace (foldlz f' (d, r) (S (S n))) with (foldlz f' (f' (d, r) (x_ (S n))) (S n)).
  replace (f' (d, r) (x_ (S n))) with (d_i M_in_Z_ ptM'cM'' (d, r) (x_ (S n)), r_i M_in_Z_ ptM'cM'' (d, r) (x_ (S n))). apply IHn.
  replace (Z_of_nat n + 2) with (Z_of_nat (S n) + 1).
  replace (d_i M_in_Z_ ptM'cM'' (d, r) (x_ (S n))) with (fst (f' (d, r) (x_ (S n)))). 
  replace (r_i M_in_Z_ ptM'cM'' (d, r) (x_ (S n))) with (snd (f' (d, r) (x_ (S n)))).
  apply P'f'x. assumption. trivial. trivial. rewrite inj_S. unfold Zsucc. ring. trivial. trivial. Qed.

Lemma P_S : forall (n : nat),
  0 <= x -> x < 2 ^ (Z_of_nat (S n) * w) ->
  P' M p (fst (foldlz f' (zero_in_Z_, zero_in_Z_) (S n)))
         (snd (foldlz f' (zero_in_Z_, zero_in_Z_) (S n))) (x / 2 ^ w) (x_ 0).

  intros n H H0. apply P'foldlz. rewrite Zdiv_small_0. simpl. unfold P'. split. left.
  replace (_Z (x_ (S n))) with 0. replace (0 mod M) with 0. replace (0 * 2 ^ w + 0) with 0. rewrite Zdiv_small_0.
  replace (0 * 2 ^ p) with 0. rewrite modred. trivial. omega. omega. ring. omega. apply lt_0_Zpow. unfold p. unfold p_in_Z_w.
  apply le_0_p. trivial. symmetry. apply modred. omega. omega. transitivity (x / 2 ^ (Z_of_nat (S n) * w) mod 2 ^ w).
  rewrite Zdiv_small_0. symmetry. apply modred. omega. exact lt02w. assumption. assumption. trivial.
  replace (_Z (x_ (S n))) with 0. replace (0 mod 2 ^ p) with 0. simpl. symmetry. apply modred. omega. exact lt02w. symmetry.
  apply modred. omega. apply lt_0_Zpow. unfold p. unfold p_in_Z_w. apply le_0_p.
  transitivity (x / 2 ^ (Z_of_nat (S n) * w) mod 2 ^ w). rewrite Zdiv_small_0. symmetry. apply modred. omega. exact lt02w. 
  assumption. assumption. trivial. assumption. apply Zlt_trans with (2 ^ (Z_of_nat (S n) * w)). assumption. apply Zlt_pow_lt.
  apply Zmult_le_0_compat. omega. exact le_0_w. apply Zmult_gt_0_lt_compat_r. apply Zlt_gt. exact lt_0_w. rewrite inj_S. omega.
  Qed.

Lemma P_O : 
  0 <= x -> x < 2 ^ (Z_of_nat O * w) ->
  P' M p (fst (foldlz f' (zero_in_Z_, zero_in_Z_) O))
         (snd (foldlz f' (zero_in_Z_, zero_in_Z_) O)) (x / 2 ^ w) (x_ 0).

  intros H H0. replace (Z_of_nat 0 * w) with 0 in H0. simpl in H0. cut (x = 0). intro H1. rewrite H1. 
  rewrite Zdiv_small_0. unfold P'. split. left. simpl. rewrite H1. rewrite Zdiv_small_0. replace (0 * 2 ^ p) with 0. symmetry.
  apply modred. omega. omega. ring. rewrite Zdiv_small_0. replace (0 mod 2 ^ w) with 0. omega. symmetry. apply modred. omega.
  exact lt02w. omega. omega. rewrite Zdiv_small_0. rewrite modred. apply lt_0_Zpow. unfold p. unfold p_in_Z_w. apply le_0_p.
  omega. exact lt02w. omega. omega. simpl. rewrite H1. rewrite Zdiv_small_0. rewrite modred. rewrite modred. symmetry.
  apply modred. omega. apply lt_0_Zpow. unfold p. unfold p_in_Z_w. apply le_0_p. apply Zmod_le_0_z. apply lt_0_Zpow. unfold p.
  unfold p_in_Z_w. apply le_0_p. rewrite modred with (x := 0). omega. omega. apply lt_0_Zpow. unfold p. unfold p_in_Z_w.
  apply le_0_p. apply Zmod_le_0_z. omega. apply Zlt_le_trans with M. apply Zmod_lt_z_m. omega. rewrite Zpow_2_w_is_2Zpow_2_wm1.
  omega. omega. omega. omega. exact lt02w. omega. ring. Qed.

Lemma P_all : forall (n : nat),
  0 <= x -> x < 2 ^ (Z_of_nat n * w) ->
  P' M p (fst (foldlz f' (zero_in_Z_, zero_in_Z_) n))
         (snd (foldlz f' (zero_in_Z_, zero_in_Z_) n)) (x / 2 ^ w) (x_ 0).

  intro n. case n. intros. apply P_O; assumption. intro n0. intros. apply P_S with (n := n0); assumption. Qed.

Lemma Q_lem : forall (n : nat),
  0 <= x -> x < 2 ^ (Z_of_nat n * w) ->
  _Z (r''0 M_in_Z_ (* ptM'cM'' *) (foldlz f' (zero_in_Z_, zero_in_Z_) n)) = x mod M.

  intros n H H0.
  cut (P' M p (fst (foldlz f' (zero_in_Z_, zero_in_Z_) n)) (snd (foldlz f' (zero_in_Z_, zero_in_Z_) n)) (x / 2 ^ w) (x_ 0)).
  intro H1. rewrite r''0_eq with (M_in_Z_ := M_in_Z_) (ptM'cM'' := ptM'cM'') (d_Sir_Si := foldlz f' (zero_in_Z_, zero_in_Z_) n)
    (l_in_Z_ := x_ 0) (h := x / 2 ^ w). simpl. replace (x / 1) with ((x * 1 + 0) / 1).
  rewrite Zdiv_mult_plus. rewrite Zmult_comm. rewrite <- Z_div_mod_eq. trivial. apply Zlt_gt. exact lt02w. omega. omega. omega.
  apply f_equal2 with (f := Zdiv); ring. trivial. trivial. fold M. omega. trivial. trivial. assumption.
  apply P_all; assumption. Qed.

End repeat.

Lemma cex : forall M : Mset, in_Z_ (2 ^ w) (2 ^ Zlog_sup M).

  intro M. unfold in_Z_. split. cut (0 < 2 ^ Zlog_sup M). omega. apply lt_0_Zpow. apply Zle_trans with (Zlog_sup 1).
  simpl. omega. apply Zlog_sup_seq. apply Mset_l. apply Zlt_pow_lt. apply Zlog_sup_correct1. case M. unfold in_Mset. simpl. 
  intros. omega. apply Zle_lt_trans with (Zlog_sup (2 ^ (w - 1))). apply Zlog_sup_seq. case M. unfold in_Mset. simpl. intros.
  omega. rewrite Zlog_sup_pow. omega. cut (0 < w). omega. exact lt_0_w. Qed.

Lemma M''ex : forall M : Mset, in_Z_ (2 ^ w) (2 ^ (w - Zlog_sup M - 1 / M) * M mod 2 ^ w).

  intro M. apply xlex. Qed.

Lemma M'mod : forall M : Mset,
   2 ^ (Zlog_sup M + w) / M - 2 ^ w =
  (2 ^ (Zlog_sup M + w) / M) mod 2 ^ w.

  intro M. rewrite <- Zmod_minus_m. symmetry. apply modred; elim (M'ex M); tauto. exact lt02w. Qed.

(* <KE EP TOGETHER - d_n_r_n_def *)
Definition d_n := zero_in_Z_.

Definition r_n := zero_in_Z_.
(* KE EP TOGETHER> *)

Definition MultiRed (M : Z_ (2 ^ w)) (ptM'cM'' : Z_ w * Z_ w * Z_ (2 ^ w) * Z_ (2 ^ w) * Z_ (2 ^ w))
                    (n : nat) (x : Z_ (2 ^ (Z_of_nat n * w))) :=
  g' M (foldlz x (f' M ptM'cM'') (d_n, r_n) n).

(* <KE EP TOGETHER - C'def *)
Definition C' (M : Mset) :=
      ( C M,
        exist (in_Z_ (2 ^ w)) (2 ^ Zlog_sup M)                             (cex M),
        exist (in_Z_ (2 ^ w)) (2 ^ (w - Zlog_sup M - 1 / M) * M mod 2 ^ w) (M''ex M)).
(* KE EP TOGETHER> *)

(* <KE EP TOGETHER - multired_equality *)
Theorem MultiRed_eq : forall (M : Mset) (n : nat) (x : Z_ (2 ^ (Z_of_nat n * w))),
  _Z (MultiRed M (C' M) n x) = x mod M.
(* KE EP TOGETHER> *)

  intros M n x. unfold MultiRed. unfold d_n. unfold r_n. unfold g'. rewrite Q_lem; unfold C'; simpl. trivial. apply Mset_l.
  apply Mset_r. trivial. elim (Zle_lt_or_eq 1 M). intro H. left. rewrite Zdiv_small_0. ring. omega. assumption.
  intro H. rewrite H. tauto. apply Mset_l. trivial. trivial. apply M'mod; assumption. apply le_0__Z. apply lt_z__Z. Qed.

Close Scope Z_scope.
