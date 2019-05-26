(* 
   Copyright (C) 2001, 2009 Luc Rutten

   This file is free software; you can redistribute it
   and/or modify it under the terms of the GNU General Public
   License as published by the Free Software Foundation; either
   version 2, or (at your option) any later version.

   This file is distributed in the hope that it will be
   useful, but WITHOUT ANY WARRANTY; without even the implied
   warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
   See the GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this file; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place - Suite 330,
   Boston, MA 02111-1307, USA.
*)

(*
   Fast reduction of nonnegative integers
   by moduli M such that 1 <= M <= 2 ^ (w - 1)
   where w denotes a processor's word size.
*)
(* Faster than the version proposed in multired2.v on some processors. *)

(* Coq 8.2 *)

Require Import ZArith.

Require Import preparation.
Require Import unsigned.

Require Import modred.

Open Scope Z_scope.

(* <KEEP TOGETHER - loop_invariant *)
Definition P (M p : Z) (d r : Z_ (2 ^ w)) (h : Z) (l : Z_ (2 ^ w)) :=
  (_Z d = (h mod M * 2 ^ w + l) / 2 ^ p * 2 ^ p mod M \/
   _Z d = (h mod M * 2 ^ w + l) / 2 ^ p * 2 ^ p mod M + M \/
   _Z d = ((h mod M + M) * 2 ^ w + l) / 2 ^ p * 2 ^ p mod M \/
   _Z d = ((h mod M + M) * 2 ^ w + l) / 2 ^ p * 2 ^ p mod M + M
  ) /\
   _Z r = (d + l mod 2 ^ p) mod 2 ^ w.
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

Hypothesis d_Si_eq_r_Si_eq : P M p d_Si r_Si h l_in_Z_.

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

  clear x_i_in_Z_ x_i.
  rewrite p_M. generalize le_1_M. case M. intro. absurd (2 <= 0); omega. intros q H.
  elim (Zlog_sup_correct2 (Zpos q)). omega. omega. intros q H. absurd (2 <= Zneg q). apply Zlt_not_le.
  unfold Zlt. trivial. assumption. Qed.

Lemma le_1_p : 1 <= p \/ M = 1.

  clear x_i_in_Z_ x_i.
  rewrite p_M. elim (Zle_lt_or_eq 1 M). intro H. left. apply Zle_trans with (Zlog_sup 2). simpl. omega. 
  apply Zlog_sup_seq. omega. intro H. right. symmetry. trivial. assumption. Qed.

Lemma lt_0_p : 0 < p \/ M = 1. 

  clear x_i_in_Z_ x_i.
  elim le_1_p; intro H; omega. Qed.

Lemma le_0_pm1 : 0 <= p - 1 \/ M = 1.

  clear x_i_in_Z_ x_i.
  elim lt_0_p; intro H; omega. Qed.

Local Hint Resolve le_M_2pp le_1_p lt_0_p le_0_pm1 : a.

Lemma lt_2pm1_M : 2 ^ (p - 1) < M \/ M = 1.

  clear x_i_in_Z_ x_i.
  elim (Zle_lt_or_eq 1 M). intro H. rewrite p_M. generalize le_1_M. case M. intro. absurd (2 <= 0); omega. 
  intros q H0. elim (Zlog_sup_correct2 (Zpos q)). omega. omega. intros q H0. absurd (1 <= Zneg q). 
  apply Zlt_not_le. unfold Zlt. trivial. assumption. omega. assumption. Qed.

Local Hint Resolve lt_2pm1_M : a.

Lemma div_M_1 : 2 ^ p / M = 1.

  clear x_i_in_Z_ x_i.
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
  rewrite Z_div_mult. symmetry. exact div_M_1. apply Zlt_gt. auto with a. apply Zle_ge. auto with a. 
  apply Zle_ge. auto with a. auto with a. omega. omega. auto with a. trivial. apply Zdivmod_split. 
  auto with a. Qed.

(* <KEEP TOGETHER - multired_equations *)
Let r'_i := ltw d_Si M_in_Z_ r_Si (minusw r_Si M_in_Z_).

Let s_i := ursh x_i_in_Z_ p_in_Z_w.

Let s'_i := multp2 s_i p_in_Z_w.

Let s''_i := ltw r'_i c_in_Z_ s_i (minusw s_i M''_in_Z_).

Let h_i := multp2 r'_i t_in_Z_w.

Let h'_i := plusw h_i s''_i.

Let q_i := uhwm h'_i M'_in_Z_.

Let q'_i := plusw q_i h'_i.

Let y_i := multw q'_i M_in_Z_.

Definition d_i := minusw s'_i y_i.

Definition r_i := minusw x_i_in_Z_ y_i.
(* KEEP TOGETHER> *)

Let d0 := d_Si. (* notation *)
Let r0 := r_Si. (* notation *)

(* <KEEP TOGETHER - multired_final *)
Let r'0 := ltw d0 M_in_Z_ r0 (minusw r0 M_in_Z_). (* notation *)

Let r''0 := ltw r'0 c_in_Z_ r'0 (minusw r'0 M_in_Z_). (* only needed after the loop *)

Definition r'''0 := ltw r''0 M_in_Z_ r''0 (minusw r''0 M_in_Z_). (* only needed after the loop *)
(* KEEP TOGETHER> *)

Let h_i' := multp2 r''0 t_in_Z_w.
 
Let h'_i' := plusw h_i' s_i.

Definition g' := r'''0. (* only needed after the loop *)

Let x := h * 2 ^ w + l.

Let x' := r''0 * 2 ^ w + x_i.

Lemma x_i_eq : x_i = x' mod 2 ^ w.

  unfold x'. rewrite Zmod_km_plus. symmetry. unfold x_i. apply modred. apply le_0__Z. apply lt_z__Z. exact lt02w. Qed.

Lemma lt_0_2ppw : 0 < 2 ^ (p + w).

  apply lt_0_Zpow. fold (0 + 0). apply Zplus_le_compat; auto with a. Qed.

Lemma lt_0_2pp : 0 < 2 ^ p.

  apply lt_0_Zpow. auto with a. Qed.

Local Hint Resolve lt_0_2pp : a.

Lemma le_0_wm1 : 0 <= w - 1.

  clear. cut (0 < w). omega. exact lt_0_w. Qed.

Local Hint Resolve le_0_wm1 lt_0_w : a.

Lemma lt_p_w : p < w.

  clear x_i_in_Z_ x_i s_i s'_i s''_i h'_i q_i q'_i y_i h'_i h'_i' x'.
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

  unfold P in d_Si_eq_r_Si_eq. tauto. Qed.

Lemma r_Si_eq_lit : 
   _Z r_Si = (d_Si + l mod 2 ^ p) mod 2 ^ w.

  unfold P in d_Si_eq_r_Si_eq. tauto. Qed.

Lemma r_Si_eq_a :
  _Z r_Si = ( d_Si + (h mod M * 2 ^ w + l) mod 2 ^ p) mod 2 ^ w.

  clear x_i_in_Z_ x_i s_i s'_i s''_i h'_i q_i q'_i y_i h'_i' x'.
  replace (h mod M * 2 ^ w) with (0 + h mod M * 2 ^ (w - p + p)). rewrite Zpower_exp. rewrite Zmult_assoc.
  rewrite Zmod_plus_distr_l with (m := 2 ^ p). rewrite Z_mod_plus. rewrite modred with (x := 0). 
  replace (0 + l) with l. exact r_Si_eq_lit. ring. omega. apply lt_0_Zpow. auto with a.
  apply Zlt_gt. apply Zlt_le_trans with M. omega. auto with a. apply lt_0_Zpow. auto with a. cut (p < w). omega. auto with a.
  apply Zle_ge. auto with a. replace (w - p + p) with w. ring. ring. Qed.

Lemma r_Si_eq_b : 
  _Z r_Si = ( d_Si + ((h mod M + M) * 2 ^ w + l) mod 2 ^ p) mod 2 ^ w.

  clear x_i_in_Z_ x_i s_i s'_i s''_i h'_i q_i q'_i y_i h'_i h'_i' x'.
  replace ((h mod M + M) * 2 ^ w) with (0 + (h mod M + M) * 2 ^ (w - p + p)). rewrite Zpower_exp. rewrite Zmult_assoc.
  rewrite Zmod_plus_distr_l with (m := 2 ^ p). rewrite Z_mod_plus. rewrite modred with (x := 0). 
  replace (0 + l) with l. exact r_Si_eq_lit. ring. omega. apply lt_0_Zpow. auto with a.
  apply Zlt_gt. apply Zlt_le_trans with M. omega. auto with a. apply lt_0_Zpow. auto with a. cut (p < w). omega. auto with a.
  apply Zle_ge. auto with a. replace (w - p + p) with w. ring. ring. Qed.

Lemma p2wp : 2 ^ w = 2 ^ (w - p) * 2 ^ p.

  clear x_i_in_Z_ x_i s_i s'_i s''_i h'_i q_i q'_i y_i h'_i h'_i' x'.
  rewrite <- Zpower_exp. replace (w - p + p) with w. trivial. ring. cut (p < w). omega. auto with a. apply Zle_ge. auto with a.
  Qed.

Lemma mod2p : forall a b c', (a * 2 ^ w + b) mod 2 ^ p = (c' * 2 ^ w + b) mod 2 ^ p.

  clear x_i_in_Z_ x_i s_i s'_i s''_i h'_i q_i q'_i y_i h'_i h'_i' x'.
  intros a b c'. replace w with (w - p + p). rewrite Zpower_exp. do 2 rewrite Zmult_assoc. do 2 rewrite Zplus_comm with (m := b).
  rewrite Z_mod_plus. rewrite Z_mod_plus. trivial. apply Zlt_gt. apply lt_0_Zpow. auto with a. apply Zlt_gt. apply lt_0_Zpow.
  auto with a. cut (p < w). omega. auto with a. apply Zle_ge. auto with a. ring. Qed.

(* <KE EP TOGETHER - r'_i_eq *)
Lemma r'_i_eq : _Z r'_i = (h mod M * 2 ^ w + l) / 2 ^ p * 2 ^ p mod M + (h mod M * 2 ^ w + l) mod 2 ^ p.
(* KE EP TOGETHER> *)

  clear x_i_in_Z_ x_i s_i s'_i s''_i h'_i q_i q'_i y_i h'_i h'_i' x'.
  unfold r'_i. elim d_Si_eq; intro H. rewrite ltw_true. rewrite r_Si_eq_a. rewrite H. apply modred. apply Zplus_le_0_compat.
  apply Zmod_le_0_z. omega. apply Zmod_le_0_z. apply lt_0_Zpow. auto with a. apply Zlt_le_trans with (M + 2 ^ p).
  apply Zplus_lt_le_compat. apply Zmod_lt_z_m. omega. apply Zlt_le_weak. apply Zmod_lt_z_m. apply lt_0_Zpow. auto with a.
  rewrite Zpow_2_w_is_2Zpow_2_wm1. apply Zplus_le_compat. assumption. apply Zle_pow_le. auto with a. cut (p < w). omega.
  auto with a. rewrite H. fold M. apply Zmod_lt_z_m. omega. elim H; intro H0. rewrite ltw_false. simpl. rewrite r_Si_eq_a. fold M.
  rewrite H0. rewrite <- Zmod_minus_distr_l.
  replace (((h mod M * 2 ^ w + l) / 2 ^ p * 2 ^ p) mod M + M + (h mod M * 2 ^ w + l) mod 2 ^ p - M)
     with (((h mod M * 2 ^ w + l) / 2 ^ p * 2 ^ p) mod M + (h mod M * 2 ^ w + l) mod 2 ^ p).
  apply modred. apply Zplus_le_0_compat. apply Zmod_le_0_z. omega. apply Zmod_le_0_z. apply lt_0_Zpow. auto with a. 
  apply Zlt_le_trans with (M + 2 ^ p). apply Zplus_lt_le_compat. apply Zmod_lt_z_m. omega. apply Zlt_le_weak. apply Zmod_lt_z_m. 
  apply lt_0_Zpow. auto with a. rewrite Zpow_2_w_is_2Zpow_2_wm1. apply Zplus_le_compat. assumption. apply Zle_pow_le. auto with a. 
  cut (p < w). omega. auto with a. ring. exact lt02w. rewrite H0. fold M.
  cut (0 <= ((h mod M * 2 ^ w + l) / 2 ^ p * 2 ^ p) mod M). omega. apply Zmod_le_0_z. omega. elim H0; intro H1.
  rewrite ltw_true. rewrite r_Si_eq_b. rewrite H1. rewrite p2wp. rewrite Zmult_assoc. rewrite mod_over_div.
  rewrite Zmod_mult_distr_l with (a := h mod M + M). replace (h mod M + M) with (h mod M + 1 * M). rewrite Z_mod_plus.
  rewrite <- Zmod_mult_distr_l. rewrite <- mod_over_div. rewrite <- Zmult_assoc. rewrite <- Zmult_assoc. rewrite <- Zpower_exp.
  replace (w - p + p) with w. rewrite mod2p with (c' := h mod M). apply modred. apply Zplus_le_0_compat.
  apply Zmod_le_0_z. omega. apply Zmod_le_0_z. apply lt_0_Zpow. auto with a. apply Zlt_le_trans with (M + 2 ^ p).
  apply Zplus_lt_le_compat. apply Zmod_lt_z_m. omega. apply Zlt_le_weak. apply Zmod_lt_z_m. apply lt_0_Zpow. auto with a.
  rewrite Zpow_2_w_is_2Zpow_2_wm1. apply Zplus_le_compat. assumption. apply Zle_pow_le. auto with a. cut (p < w). omega.
  auto with a. ring. cut (p < w). omega. auto with a. apply Zle_ge. auto with a. apply lt_0_Zpow. auto with a. omega. omega.
  omega. ring. omega. apply lt_0_Zpow. auto with a. omega. rewrite H1. fold M. apply Zmod_lt_z_m. omega.
  rewrite ltw_false. simpl. rewrite r_Si_eq_b. rewrite H1.
  (* rewrite p2wp. *) (* does not work: Cannot solve a second-order unification problem *)
  (* replace ((h mod M + M) * 2 ^ w) with ((h mod M + M) * (2 ^ (w - p) * 2 ^ p)). *) (* again, does not work *)
  transitivity ((((((h mod M + M) * (2 ^ (w - p) * 2 ^ p) + l) / 2 ^ p * 2 ^ p) mod M + M +
    ((h mod M + M) * (2 ^ (w - p) * 2 ^ p) + l) mod 2 ^ p) mod 
      (2 ^ (w - p) * 2 ^ p) - M) mod (2 ^ (w - p) * 2 ^ p)). (* workaround *)
  rewrite <- p2wp. trivial. (* this works *)
  rewrite Zmult_assoc. rewrite mod_over_div.
  rewrite Zmod_mult_distr_l with (a := h mod M + M). replace (h mod M + M) with (h mod M + 1 * M). rewrite Z_mod_plus.
  rewrite <- Zmod_mult_distr_l. rewrite <- mod_over_div. rewrite <- Zmult_assoc. rewrite <- Zmult_assoc. rewrite <- Zpower_exp.
  replace (w - p + p) with w. rewrite mod2p with (c' := h mod M). rewrite <- Zmod_minus_distr_l. fold M.
  replace (((h mod M * 2 ^ w + l) / 2 ^ p * 2 ^ p) mod M + M + (h mod M * 2 ^ w + l) mod 2 ^ p - M)
     with (((h mod M * 2 ^ w + l) / 2 ^ p * 2 ^ p) mod M + (h mod M * 2 ^ w + l) mod 2 ^ p). apply modred. 
  apply Zplus_le_0_compat. apply Zmod_le_0_z. omega. apply Zmod_le_0_z. apply lt_0_Zpow. auto with a.
  apply Zlt_le_trans with (M + 2 ^ p). apply Zplus_lt_le_compat. apply Zmod_lt_z_m. omega. apply Zlt_le_weak. apply Zmod_lt_z_m. 
  apply lt_0_Zpow. auto with a. rewrite Zpow_2_w_is_2Zpow_2_wm1. apply Zplus_le_compat. assumption. apply Zle_pow_le. auto with a.
  cut (p < w). omega. auto with a. ring. auto with a. ring. cut (p < w). omega. auto with a. apply Zle_ge. auto with a. 
  apply lt_0_Zpow. auto with a. omega. omega. omega. ring. omega. apply lt_0_Zpow. auto with a. omega. rewrite H1. fold M. 
  cut (0 <= (((h mod M + M) * 2 ^ w + l) / 2 ^ p * 2 ^ p) mod M). omega. apply Zmod_le_0_z. omega. Qed.

Let x'' := h mod M * 2 ^ w + l.

Lemma sum_r'_i : forall a b : Z, (a mod M + b mod M) / M = 0 \/ (a mod M + b mod M) / M = 1.

  clear x_i_in_Z_ x_i s_i s'_i s''_i h'_i q_i q'_i y_i h'_i h'_i' x'.
  intros a b. cut (0 <= (a mod M + b mod M) / M). cut ((a mod M + b mod M) / M <= 1). omega. 
  apply Zle_trans with ((M - 1 + M) / M). apply Zdiv_le. omega. apply Zplus_le_compat. cut (a mod M < M). omega.
  apply Zmod_lt_z_m. omega. cut (b mod M < M). omega. apply Zmod_lt_z_m. omega. replace (M - 1 + M) with (2 * M - 1).
  rewrite Zdiv_mult_minus. omega. omega. omega. omega. ring. apply Zle_0_div. fold (0 + 0). apply Zplus_le_compat. 
  apply Zmod_le_0_z. omega. apply Zmod_le_0_z. omega. omega. Qed.

Lemma div_r'_i : forall a : Z, a mod 2 ^ p / M = 0 \/ a mod 2 ^ p / M = 1.

  clear x_i_in_Z_ x_i s_i s'_i s''_i h'_i q_i q'_i y_i h'_i h'_i' x'.
  intro a. cut (0 <= a mod 2 ^ p / M). cut (a mod 2 ^ p / M <= 1). omega. apply Zle_trans with (2 ^ p / M). apply Zdiv_le. omega. 
  cut (a mod 2 ^ p < 2 ^ p). omega. apply Zmod_lt_z_m. apply lt_0_Zpow. auto with a. rewrite div_M_1. omega. apply Zle_0_div.
  apply Zmod_le_0_z. apply lt_0_Zpow. auto with a. omega. Qed.

Lemma r'_i_eq'_i : _Z r'_i = x mod M \/ _Z r'_i = x mod M + M \/ _Z r'_i = x mod M + M + M.

  clear x_i_in_Z_ x_i s_i s'_i s''_i h'_i q_i q'_i y_i h'_i h'_i' x'.
  rewrite r'_i_eq. fold x''. rewrite Z_div_mod_eq with (a := x'' mod 2 ^ p) (b := M).
  rewrite Zplus_comm with (m := (x'' mod 2 ^ p) mod M). rewrite Zplus_assoc.
  rewrite Z_div_mod_eq with (a := (x'' / 2 ^ p * 2 ^ p) mod M + (x'' mod 2 ^ p) mod M) (b := M). rewrite <- Zmod_plus_distr_l.
  rewrite Zplus_comm with (n := x'' / 2 ^ p * 2 ^ p). rewrite <- Zmod_plus_distr_l. rewrite Zplus_comm with (n := x'' mod 2 ^ p).
  rewrite Zmult_comm with (m := 2 ^ p). rewrite <- Z_div_mod_eq. replace (x'' mod M) with (x mod M). 
  elim (sum_r'_i (2 ^ p * (x'' / 2 ^ p)) (x'' mod 2 ^ p)); intro H; elim (div_r'_i x''); intro H0; rewrite H; rewrite H0. left. ring.
  right. left. ring. right. left. ring. right. right. ring. unfold x''. rewrite Zmod_plus_distr_l. rewrite <- Zmod_mult_distr_l.
  rewrite <- Zmod_plus_distr_l. trivial. omega. omega. omega. apply Zlt_gt. apply lt_0_Zpow. auto with a. omega. omega. omega.
  omega. Qed.

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

Lemma r''0_small : r''0 < 2 ^ p.

  unfold r''0.
  unfold r'0. unfold d0. unfold r0. fold r'_i. (* too long *)
  elim (Zle_or_lt c r'_i); intro H. rewrite ltw_false. rewrite Z_from_minusw. fold M. rewrite modred. rewrite r'_i_eq.
  cut (((h mod M * 2 ^ w + l) / 2 ^ p * 2 ^ p) mod M < M). cut ((h mod M * 2 ^ w + l) mod 2 ^ p < 2 ^ p). omega.
  apply Zmod_lt_z_m. apply lt_0_Zpow. auto with a. apply Zmod_lt_z_m. omega. cut (M <= r'_i). omega.
  apply Zle_trans with c. rewrite c_M. exact le_M_2pp. assumption. cut (0 <= M). cut (r'_i < 2 ^ w). omega. apply lt_z__Z.
  omega. assumption. rewrite ltw_true. rewrite <- c_M. assumption. assumption. Qed.

(* <KE EP TOGETHER - r''0_eq *)
Lemma r''0_eq : _Z r''0 = x mod M \/ _Z r''0 = x mod M + M.
(* KE EP TOGETHER> *)

  clear x_i_in_Z_ x_i s_i s'_i s''_i h'_i q_i q'_i y_i h'_i h'_i' x'.
  unfold r''0.
  unfold r'0. unfold d0. unfold r0. fold r'_i. (* too long *) elim (Zle_or_lt c r'_i); intro H. rewrite ltw_false. simpl. fold M.
  rewrite modred. elim r'_i_eq'_i; intro H0. absurd (c <= r'_i). apply Zlt_not_le. rewrite H0. apply Zlt_le_trans with M.
  apply Zmod_lt_z_m. omega. rewrite c_M. exact le_M_2pp. assumption. elim H0; intro H1. left. omega. right. omega.
  cut (M <= 2 ^ p). omega. exact le_M_2pp. cut (r'_i < 2 ^ w). cut (0 < M). omega. omega. apply lt_z__Z. assumption.
  rewrite ltw_true. elim r'_i_eq'_i. intro H0. tauto. intro H0. elim H0; intro H1. tauto. absurd (r'_i < c). apply Zle_not_lt.
  rewrite H1. apply Zle_trans with (M + M). rewrite c_M. elim (Zle_lt_or_eq 1 M). intro H2. elim lt_2pm1_M; intro H3.
  replace p with (p - 1 + 1). rewrite Zpower_exp. simpl. unfold Zpower_pos. simpl. omega. cut (1 <= p). omega.
  replace 1 with (Zlog_sup 2). rewrite p_M. apply Zlog_sup_seq. omega. trivial. omega. ring. rewrite p_M. rewrite H3. omega.
  intro H2. rewrite p_M. rewrite <- H2. simpl. omega. omega. cut (0 <= x mod M). omega. apply Zmod_le_0_z. omega. assumption.
  assumption. Qed.

(* <KE EP TOGETHER - r'''0_eq *)
Lemma r'''0_eq : _Z r'''0 = x mod M.
(* KE EP TOGETHER> *)

  clear x_i_in_Z_ x_i s_i s'_i s''_i h'_i q_i q'_i y_i h'_i h'_i' x'.
  unfold r'''0. elim r''0_eq; intro H. rewrite ltw_true. trivial. rewrite H. apply Zmod_lt_z_m. fold M. omega. rewrite ltw_false.
  simpl. rewrite H. fold M. replace (x mod M + M - M) with (x mod M). apply modred.
  apply Zmod_le_0_z. omega. apply Zlt_trans with M. apply Zmod_lt_z_m. omega. unfold M. apply lt_z__Z. ring. rewrite H. fold M.
  cut (0 <= x mod M). omega. apply Zmod_le_0_z. omega. Qed.
  
Lemma lt_x'_x'max : x' < 2 ^ (p + w).

  unfold x'. apply Zle_lt_trans with ((2 ^ p - 1) * 2 ^ w + (2 ^ w - 1)). apply Zplus_le_compat. 
  apply Zmult_le_compat. auto with a. auto with a. cut (r''0 < 2 ^ p). omega. apply r''0_small. omega. auto with a.
  apply le_0__Z. auto with a. cut (x_i < 2 ^ w). omega. unfold x_i. apply lt_z__Z. rewrite Zmult_minus_distr_r. 
  rewrite <- Zpower_exp. omega. auto with a. apply Zle_ge. auto with a. apply Zle_ge. auto with a. Qed.

Lemma le_x'_x'max : x' <= 2 ^ (p + w) - 1.

  cut (x' < 2 ^ (p + w)). omega. exact lt_x'_x'max. Qed.

Local Hint Resolve lt_x'_x'max le_x'_x'max : a.

Lemma Meq_ir''0 : M = 1 -> _Z r''0 = 0.

  intro H. cut (r''0 < 2 ^ p). rewrite p_M. rewrite H. simpl. cut (0 <= r''0). omega. apply le_0__Z. exact r''0_small. Qed.

(* <KE EP TOGETHER - h_i'_eq *)
Lemma h_i'_eq : _Z h_i' = x' / 2 ^ w * 2 ^ (w - p).
(* KE EP TOGETHER> *)

  unfold x'. rewrite Zdiv_times_plus. rewrite Zdiv_small_0. simpl. fold t. replace (r''0 + 0) with (_Z r''0). elim t_M; intro H.
  rewrite H. rewrite Zmult_comm. apply modred. fold (0 * 0). apply Zmult_le_compat. apply le_0__Z. apply Zlt_le_weak. 
  apply lt_0_Zpow. auto with a. omega.
  omega. apply Zlt_le_trans with (2 ^ p * 2 ^ (w - p)). apply Zmult_lt_compat_r. auto with a. 
  apply lt_0_Zpow. auto with a. apply r''0_small. rewrite <- Zpower_exp. replace (p + (w - p)) with w. omega. 
  ring. apply Zle_ge. auto with a. apply Zle_ge. auto with a. rewrite Meq_ir''0. rewrite Zmult_comm. simpl. apply modred. omega.
  auto with a. assumption. ring. unfold x_i. apply le_0__Z. unfold x_i. apply lt_z__Z. auto with a. Qed.

(* <KE EP TOGETHER - h'_i'_eq *)
Lemma h'_i'_eq : _Z h'_i' = x' / 2 ^ p.
(* KE EP TOGETHER> *)

  unfold h'_i'. rewrite Z_from_plusw. rewrite h_i'_eq. simpl. fold x_i p. rewrite x_i_eq. rewrite <- Zdiv_times_plus.
  rewrite <- Zmult_assoc. rewrite <- Zpower_exp. replace (w - p + p) with w. rewrite Zdivmod_split.
  apply modred. apply Zle_0_div. auto with a. auto with a. apply Zlt_le_trans with (2 ^ (p + w) / 2 ^ p).
  apply Zle_lt_trans with ((2 ^ (p + w) - 1) / 2 ^ p). apply Zdiv_le. auto with a. cut (x' < 2 ^ (p + w)).
  omega. auto with a. rewrite Zpower_exp. rewrite Zmult_comm. rewrite Zdiv_mult_minus. rewrite Z_div_mult.
  omega. apply Zlt_gt. auto with a. auto with a. omega. cut (0 < 2 ^ p). omega. auto with a. apply Zle_ge.
  auto with a. apply Zle_ge. auto with a. rewrite Zpower_exp. rewrite Zmult_comm. rewrite Z_div_mult. 
  omega. apply Zlt_gt. auto with a. apply Zle_ge. auto with a. apply Zle_ge. auto with a. auto with a. 
  ring. apply Zle_ge. auto with a. apply Zle_ge. auto with a. auto with a. Qed.

Lemma h'_i'h'_i_eq : _Z h'_i' = _Z h'_i.

  unfold h'_i'. unfold h'_i. simpl. unfold r''0. 
  unfold r'0. unfold d0. unfold r0. fold r'_i. (* too long *)
  unfold s''_i. fold t. fold p. elim (Zle_or_lt c r'_i); intro H. rewrite ltw_false. rewrite ltw_false. simpl. fold M''.
  rewrite M''_M. fold M. fold x_i. rewrite Zmult_comm. rewrite <- Zmod_mult_distr_l. rewrite <- Zmod_plus_distr_l.
  rewrite <- Zmod_minus_distr_r. rewrite <- Zmod_plus_distr_l. rewrite Zplus_comm with (n := 2 ^ t * r'_i).
  rewrite <- Zmod_plus_distr_l. fold p. apply f_equal2 with (f := Zmod). ring. trivial. exact lt02w. exact lt02w. exact lt02w.
  exact lt02w. exact lt02w. assumption. assumption. rewrite ltw_true. rewrite ltw_true. trivial. assumption. assumption. Qed.

(* <KE EP TOGETHER - q_i_eq *)
Lemma q_i_eq : 
  _Z q_i = x' / 2 ^ p * (2 ^ (p + w) / M mod 2 ^ w) / 2 ^ w.
(* KE EP TOGETHER> *)

  unfold q_i. rewrite uhwm_eq. rewrite <- h'_i'h'_i_eq. rewrite h'_i'_eq. fold M'. rewrite M'_M. trivial. Qed.

Lemma q'_i_eq_pre : 
  _Z q'_i = (x' / 2 ^ p * (2 ^ (p + w) / M) / 2 ^ w) mod 2 ^ w.

  unfold q'_i. rewrite Z_from_plusw. rewrite q_i_eq. rewrite <- h'_i'h'_i_eq. rewrite h'_i'_eq. rewrite Zplus_comm. 
  rewrite <- Zdiv_times_plus. rewrite <- Zmult_plus_distr_r. rewrite large_M'_eq. trivial. auto with a. Qed.

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

(* <KE EP TOGETHER - r_i_eq *)
Lemma r_i_eq : _Z r_i = (_Z d_i + x' mod 2 ^ p) mod 2 ^ w.
(* KE EP TOGETHER> *)

  unfold r_i. unfold d_i. rewrite Z_from_minusw. rewrite Z_from_minusw. fold l. rewrite s'_i_eq.
  rewrite Zmod_minus_distr_l with (a := x' mod 2 ^ w - x' mod 2 ^ p).
  rewrite <- Zmod_minus_distr_l with (a := x'). rewrite <- Zmod_minus_distr_l. rewrite <- Zmod_plus_distr_l. fold x_i.
  replace (x' - x' mod 2 ^ p - _Z y_i + x' mod 2 ^ p) with (x' - _Z y_i). rewrite x_i_eq. 
  rewrite <- Zmod_minus_distr_l. trivial. auto with a. ring. auto with a. auto with a. auto with a.
  auto with a. Qed.

Definition d_ir_i := (d_i, r_i).

Lemma d_i_r_i_eq : P M p d_i r_i x x_i_in_Z_.

  unfold P. split. elim d_i_eq; unfold x'. elim r''0_eq; intro H; rewrite H. tauto. tauto. elim r''0_eq; intro H; rewrite H. tauto.
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
  P M p d r h l -> P M p (fst (f' (d, r) x_i)) (snd (f' (d, r) x_i)) (h * 2 ^ w + l) x_i.

  intros d r  h l x_i H. unfold f'. unfold M. unfold p. unfold p_in_Z_w. simpl. apply d_i_r_i_eq; fold p_in_Z_w; fold M; fold p.
  assumption. omega. assumption. assumption. assumption. assumption. assumption. assumption. Qed.

Lemma P'f'x : forall (d r : Z_ (2 ^ w)) (n : nat),
  P M p d r (x / 2 ^ ((Z_of_nat n + 2) * w)) (x_ (S n)) ->
  P M p (fst (f' (d, r) (x_ n))) (snd (f' (d, r) (x_ n))) (x / 2 ^ ((Z_of_nat n + 1) * w)) (x_ n).

  intros d r n H. 
  rewrite Z_div_mod_eq with (a := x / 2 ^ ((Z_of_nat n + 1) * w)) (b := 2 ^ w). rewrite Zdivdivdiv. rewrite <- Zpower_exp. 
  replace ((Z_of_nat n + 1) * w + w) with ((Z_of_nat n + 2) * w). replace (Z_of_nat n + 1) with (Z_of_nat (S n)).
  replace ((x / 2 ^ (Z_of_nat (S n) * w)) mod 2 ^ w) with (_Z (x_ (S n))). rewrite Zmult_comm. 
  apply P'f'. trivial. trivial. trivial.
  trivial. rewrite inj_S. ring. ring. apply Zle_ge. apply Zmult_le_0_compat. omega. exact le_0_w.
  apply Zle_ge. exact le_0_w. apply lt_0_Zpow. apply Zmult_le_0_compat. omega. exact le_0_w. exact lt02w. apply Zlt_gt.
  exact lt02w. Qed.

Lemma P'foldlz : forall (n : nat) (d r : Z_ (2 ^ w)),
  P M p d r (x / 2 ^ ((Z_of_nat n + 2) * w)) (x_ (S n)) ->
  P M p (fst (foldlz f' (d, r) (S n))) (snd (foldlz f' (d, r) (S n))) (x / 2 ^ w) (x_ O).

  induction n. intros d r. intro H.
  replace (foldlz f' (d, r) 1) with (f' (d, r) (x_ 0)).
  (* replace w with ((Z_of_nat 0 + 1) * w). *) (* does not work *)
  cut (P M p (fst (f' (d, r) (x_ 0))) (snd (f' (d, r) (x_ 0))) (x / 2 ^ ((Z_of_nat 0 + 1) * w)) (x_ 0)). (* workaroud *)
  replace ((Z_of_nat 0 + 1) * w) with w. (* works *) trivial. ring. apply P'f'x. assumption. trivial. intros d r. intro H.
  replace (foldlz f' (d, r) (S (S n))) with (foldlz f' (f' (d, r) (x_ (S n))) (S n)).
  replace (f' (d, r) (x_ (S n))) with (d_i M_in_Z_ ptM'cM'' (d, r) (x_ (S n)), r_i M_in_Z_ ptM'cM'' (d, r) (x_ (S n))). apply IHn.
  replace (Z_of_nat n + 2) with (Z_of_nat (S n) + 1).
  replace (d_i M_in_Z_ ptM'cM'' (d, r) (x_ (S n))) with (fst (f' (d, r) (x_ (S n)))). 
  replace (r_i M_in_Z_ ptM'cM'' (d, r) (x_ (S n))) with (snd (f' (d, r) (x_ (S n)))).
  apply P'f'x. assumption. trivial. trivial. rewrite inj_S. unfold Zsucc. ring. trivial. trivial. Qed.

Lemma P_S : forall (n : nat),
  0 <= x -> x < 2 ^ (Z_of_nat (S n) * w) ->
  P M p (fst (foldlz f' (zero_in_Z_, zero_in_Z_) (S n)))
        (snd (foldlz f' (zero_in_Z_, zero_in_Z_) (S n))) (x / 2 ^ w) (x_ 0).

  intros n H H0. apply P'foldlz. rewrite Zdiv_small_0. simpl. unfold P. split. left.
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
  P M p (fst (foldlz f' (zero_in_Z_, zero_in_Z_) O))
        (snd (foldlz f' (zero_in_Z_, zero_in_Z_) O)) (x / 2 ^ w) (x_ 0).

  intros H H0. replace (Z_of_nat 0 * w) with 0 in H0. simpl in H0. cut (x = 0). intro H1. rewrite H1. 
  rewrite Zdiv_small_0. unfold P. split. left. simpl. rewrite H1. rewrite Zdiv_small_0. replace (0 * 2 ^ p) with 0. symmetry.
  apply modred. omega. omega. ring. rewrite Zdiv_small_0. replace (0 mod 2 ^ w) with 0. omega. symmetry. apply modred. omega.
  exact lt02w. omega. omega. rewrite Zdiv_small_0. rewrite modred. apply lt_0_Zpow. unfold p. unfold p_in_Z_w. apply le_0_p.
  omega. exact lt02w. omega. omega. simpl. rewrite H1. rewrite Zdiv_small_0. rewrite modred. rewrite modred. symmetry.
  apply modred. omega. exact lt02w. rewrite modred. omega. omega. exact lt02w. rewrite modred. apply lt_0_Zpow. unfold p. 
  unfold p_in_Z_w. apply le_0_p. omega. exact lt02w. rewrite modred. rewrite modred. omega. omega. 
  exact lt02w. rewrite modred. omega. omega. exact lt02w. rewrite modred. apply lt_0_Zpow. unfold p. unfold p_in_Z_w.
  apply le_0_p. omega. exact lt02w. rewrite modred. rewrite modred. exact lt02w. omega. exact lt02w. rewrite modred.
  omega. omega. exact lt02w. rewrite modred. apply lt_0_Zpow. unfold p. unfold p_in_Z_w. apply le_0_p. omega. exact lt02w. 
  omega. omega. omega. exact lt02w. omega. ring. Qed.

Lemma P_all : forall (n : nat),
  0 <= x -> x < 2 ^ (Z_of_nat n * w) ->
  P M p (fst (foldlz f' (zero_in_Z_, zero_in_Z_) n))
        (snd (foldlz f' (zero_in_Z_, zero_in_Z_) n)) (x / 2 ^ w) (x_ 0).

  intro n. case n. intros. apply P_O; assumption. intro n0. intros. apply P_S with (n := n0); assumption. Qed.

Lemma Q_lem : forall (n : nat),
  0 <= x -> x < 2 ^ (Z_of_nat n * w) ->
  _Z (r'''0 M_in_Z_ ptM'cM'' (foldlz f' (zero_in_Z_, zero_in_Z_) n)) = x mod M.

  intros n H H0.
  cut (P M p (fst (foldlz f' (zero_in_Z_, zero_in_Z_) n)) (snd (foldlz f' (zero_in_Z_, zero_in_Z_) n)) (x / 2 ^ w) (x_ 0)).
  intro H1. rewrite r'''0_eq with (d_Sir_Si := foldlz f' (zero_in_Z_, zero_in_Z_) n) (l_in_Z_ := x_ 0) (h := x / 2 ^ w). simpl.
  replace (x / 1) with ((x * 1 + 0) / 1).
  rewrite Zdiv_mult_plus. rewrite Zmult_comm. rewrite <- Z_div_mod_eq. trivial. apply Zlt_gt. exact lt02w. omega. omega. omega.
  apply f_equal2 with (f := Zdiv); ring. trivial. fold M. omega. trivial. trivial. assumption. assumption.
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

(* <KEEP TOGETHER - d_n_r_n_def *)
Definition d_n := zero_in_Z_.

Definition r_n := zero_in_Z_.
(* KEEP TOGETHER> *)

Definition MultiRed (M_in_Z_ : Z_ (2 ^ w)) (ptM'cM'' : Z_ w * Z_ w * Z_ (2 ^ w) * Z_ (2 ^ w) * Z_ (2 ^ w))
                    (n : nat) (x : Z_ (2 ^ (Z_of_nat n * w))) :=
  g' M_in_Z_ ptM'cM'' (foldlz x (f' M_in_Z_ ptM'cM'') (d_n, r_n) n).

(* <KEEP TOGETHER - C'def *)
Definition C' (M : Mset) :=
      ( C M,
        exist (in_Z_ (2 ^ w)) (2 ^ Zlog_sup M)                             (cex M),
        exist (in_Z_ (2 ^ w)) (2 ^ (w - Zlog_sup M - 1 / M) * M mod 2 ^ w) (M''ex M)).
(* KEEP TOGETHER> *)

(* <KEEP TOGETHER - multired_equality *)
Theorem MultiRed_eq : forall (M : Mset) (n : nat) (x : Z_ (2 ^ (Z_of_nat n * w))),
  _Z (MultiRed M (C' M) n x) = x mod M.
(* KEEP TOGETHER> *)

  intros M n x. unfold MultiRed. unfold d_n. unfold r_n. unfold g'. apply Q_lem; unfold C'; simpl.
  apply Mset_l. apply Mset_r. trivial. elim (Zle_lt_or_eq 1 M). intro H. left. 
  rewrite Zdiv_small_0. ring. omega. assumption. intro H. rewrite H. tauto. apply Mset_l. trivial. trivial.
  apply M'mod; assumption. apply le_0__Z. apply lt_z__Z. Qed.

Close Scope Z_scope.
