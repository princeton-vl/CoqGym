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
   Fast reduction of integers in Z_(2 ^ (log_sup M + w)))
   by moduli M such that 1 <= M <= 2 ^ (w - 1)
   where w denotes a processor's word size.
*)

(* Coq 8.2 *)

Require Import ZArith.

Require Import preparation.
Require Import unsigned.

Open Scope Z_scope.

Section parm_sec.

Variable M_in_Z_ : Z_ (2 ^ w).
Variable ptM' : Z_ w * Z_ w * Z_ (2 ^ w).
Variables v_in_Z_ u_in_Z_ : Z_ (2 ^ w).

Let p_in_Z_w := fst (fst ptM').
Let t_in_Z_w := snd (fst ptM').
Let M'_in_Z_ := snd ptM'.

Let M := _Z M_in_Z_.
Let p := _Z p_in_Z_w.
Let t := _Z t_in_Z_w.
Let M' := _Z M'_in_Z_.
Let v := _Z v_in_Z_.
Let u := _Z u_in_Z_.

Hypothesis le_1_M : 1 <= M.
Hypothesis le_M_max : M <= 2 ^ (w - 1).
Hypothesis p_M : p = Zlog_sup M.
Hypothesis t_M : t = w - p \/ M = 1.
Hypothesis M'_M : M' = 2 ^ (p + w) / M mod 2 ^ w.
Hypothesis v_M : v < 2 ^ p.

Let x := v * 2 ^ w + u.

Lemma le_0_p : 0 <= p.

  unfold p. apply le_0__Z. Qed.

Lemma le_0_l : 0 <= u.
  
  unfold u. apply le_0__Z. Qed.

Lemma lt_l_2w : u < 2 ^ w.

  unfold u. apply lt_z__Z. Qed.

Lemma le_0_v : 0 <= v.

  unfold v. apply le_0__Z. Qed.

Lemma lt_v_2w : v < 2 ^ w.

  unfold v. apply lt_z__Z. Qed.

Lemma le02w : 0 <= 2 ^ w.

  apply Zlt_le_weak. exact lt02w. Qed.

Local Hint Resolve le_0_w lt02w le02w : a.
Local Hint Resolve le_0_p le_0_l lt_l_2w le_0_v lt_v_2w : a.

Lemma le_0_x : 0 <= x.

  unfold x. fold (0 + 0). apply Zplus_le_compat; auto with a. apply Zmult_le_0_compat; auto with a. Qed.

Local Hint Resolve le_0_x : a.

(* <KEEP TOGETHER - modred_equations *)
Let s := ursh u_in_Z_ p_in_Z_w.

Let s' := multp2 s p_in_Z_w.

Let h := multp2 v_in_Z_ t_in_Z_w.

Let h' := plusw h s.

Let q := uhwm h' M'_in_Z_.

Let q' := plusw q h'.

Let y := multw q' M_in_Z_.

Let d := minusw s' y.

Let r := minusw u_in_Z_ y.

Let r' := ltw d M_in_Z_ r (minusw r M_in_Z_).

Let r'' := ltw r' M_in_Z_ r' (minusw r' M_in_Z_).

Let r''' := ltw r'' M_in_Z_ r'' (minusw r'' M_in_Z_).
(* KEEP TOGETHER> *)

Definition ModRed := _Z r'''. (* keeps _Z out of ModRed_eq *)

Lemma l_eq : u = x mod 2 ^ w.

  unfold x. rewrite Zmod_km_plus. symmetry. apply modred. auto with a. auto with a. auto with a. Qed.

Lemma v_eq : v = x / 2 ^ w.

  unfold x. rewrite Zdiv_times_plus. rewrite Zdiv_small_0. ring. auto with a. auto with a. auto with a. Qed.

(* <KEEP TOGETHER - s_eq *)
Lemma s_eq : _Z s = x mod 2 ^ w / 2 ^ p.
(* KEEP TOGETHER> *)

  simpl. fold u. fold p. rewrite l_eq. trivial. Qed.

Lemma lt_0_2ppw : 0 < 2 ^ (p + w).

  apply lt_0_Zpow. fold (0 + 0). apply Zplus_le_compat; auto with a. Qed.

Lemma lt_0_2pp : 0 < 2 ^ p.

  apply lt_0_Zpow. auto with a. Qed.

Local Hint Resolve lt_0_2pp : a.

Lemma lt_x_xmax : x < 2 ^ (p + w).

  unfold x. apply Zle_lt_trans with ((2 ^ p - 1) * 2 ^ w + (2 ^ w - 1)). apply Zplus_le_compat. 
  apply Zmult_le_compat. auto with a. auto with a. cut (v < 2 ^ p). omega. auto with a. omega. auto with a.
  auto with a. cut (u < 2 ^ w). omega. auto with a. rewrite Zmult_minus_distr_r. rewrite <- Zpower_exp.
  omega. auto with a. apply Zle_ge. auto with a. apply Zle_ge. auto with a. Qed.

Lemma le_x_xmax : x <= 2 ^ (p + w) - 1.

  cut (x < 2 ^ (p + w)). omega. exact lt_x_xmax. Qed.

Local Hint Resolve lt_x_xmax le_x_xmax : a.

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

(* <KEEP TOGETHER - s'_eq *)
Lemma s'_eq : _Z s' = x mod 2 ^ w - x mod 2 ^ p.
(* KEEP TOGETHER> *)

  unfold s'. rewrite Z_from_multp2. fold p. rewrite s_eq. rewrite Zmult_comm. rewrite modred.
  replace (x mod 2 ^ p) with (x mod 2 ^ w mod 2 ^ p). apply Zdiv_a_b_b_Zmod. auto with a.
  replace (2 ^ w) with (2 ^ (w - p) * 2 ^ p). apply Zmod_prod_Zmod. apply lt_0_Zpow. auto with a.
  auto with a. rewrite <- Zpower_exp. apply f_equal2 with (f := Zpower). trivial. ring. apply Zle_ge.
  auto with a. apply Zle_ge. auto with a. fold (0 * 0). apply Zmult_le_compat. apply Zle_0_div. 
  apply Zmod_le_0_z. auto with a. auto with a. apply Zlt_le_weak. auto with a. omega. omega. 
  apply Zle_lt_trans with (x mod 2 ^ w). rewrite Zmult_comm. apply Z_mult_div_ge. apply Zlt_gt.
  auto with a. apply Zmod_lt_z_m. auto with a. Qed.

(* <KEEP TOGETHER - h_eq *)
Lemma h_eq : _Z h = x / 2 ^ w * 2 ^ (w - p).
(* KEEP TOGETHER> *)

  simpl. fold t v. elim t_M; intro H. rewrite H. rewrite <- v_eq. rewrite Zmult_comm. apply modred. 
  fold (0 * 0). apply Zmult_le_compat. auto with a. apply Zlt_le_weak. apply lt_0_Zpow. auto with a. omega.
  omega. apply Zlt_le_trans with (2 ^ p * 2 ^ (w - p)). apply Zmult_lt_compat_r. auto with a. 
  apply lt_0_Zpow. auto with a. assumption. rewrite <- Zpower_exp. replace (p + (w - p)) with w. omega. 
  ring. apply Zle_ge. auto with a. apply Zle_ge. auto with a. rewrite H in p_M. simpl in p_M.
  rewrite p_M in v_M. replace (2 ^ 0) with 1 in v_M. cut (v = 0). intro H0. unfold x. rewrite H0.
  replace (2 ^ t * 0) with 0. simpl. rewrite Zdiv_small_0. simpl. apply modred. omega. auto with a.
  auto with a. auto with a. ring. cut (0 <= v). omega. unfold v. apply le_0__Z. ring. Qed.

(* <KEEP TOGETHER - h'_eq *)
Lemma h'_eq : _Z h' = x / 2 ^ p.
(* KEEP TOGETHER> *)

  unfold h'. rewrite Z_from_plusw. rewrite h_eq. simpl. fold u p. rewrite l_eq. rewrite <- Zdiv_times_plus.
  rewrite <- Zmult_assoc. rewrite <- Zpower_exp. replace (w - p + p) with w. rewrite Zdivmod_split.
  apply modred. apply Zle_0_div. auto with a. auto with a. apply Zlt_le_trans with (2 ^ (p + w) / 2 ^ p).
  apply Zle_lt_trans with ((2 ^ (p + w) - 1) / 2 ^ p). apply Zdiv_le. auto with a. cut (x < 2 ^ (p + w)).
  omega. auto with a. rewrite Zpower_exp. rewrite Zmult_comm. rewrite Zdiv_mult_minus. rewrite Z_div_mult.
  omega. apply Zlt_gt. auto with a. auto with a. omega. cut (0 < 2 ^ p). omega. auto with a. apply Zle_ge.
  auto with a. apply Zle_ge. auto with a. rewrite Zpower_exp. rewrite Zmult_comm. rewrite Z_div_mult. 
  omega. apply Zlt_gt. auto with a. apply Zle_ge. auto with a. apply Zle_ge. auto with a. auto with a. 
  ring. apply Zle_ge. auto with a. apply Zle_ge. auto with a. auto with a. Qed.

(* <KEEP TOGETHER - q_eq *)
Lemma q_eq : 
  _Z q = x / 2 ^ p * (2 ^ (p + w) / M mod 2 ^ w) / 2 ^ w.
(* KEEP TOGETHER> *)

  unfold q. rewrite uhwm_eq. rewrite h'_eq. fold M'. rewrite M'_M. trivial. Qed.

Lemma le_M_2pp : M <= 2 ^ p.

  rewrite p_M. generalize le_1_M. case M. intro. absurd (2 <= 0); omega. intros q0 H.
  elim (Zlog_sup_correct2 (Zpos q0)). omega. omega. intros q0 H. absurd (2 <= Zneg q0). apply Zlt_not_le.
  unfold Zlt. trivial. assumption. Qed.

Lemma le_1_p : 1 <= p \/ M = 1.

  rewrite p_M. elim (Zle_lt_or_eq 1 M). intro H. left. apply Zle_trans with (Zlog_sup 2). simpl. omega. 
  apply Zlog_sup_seq. omega. intro H. right. symmetry. trivial. assumption. Qed.

Lemma lt_0_p : 0 < p \/ M = 1. 

  elim le_1_p; intro H; omega. Qed.

Lemma le_0_pm1 : 0 <= p - 1 \/ M = 1.

  elim lt_0_p; intro H; omega. Qed.

Local Hint Resolve le_M_2pp le_1_p lt_0_p le_0_pm1 : a.

Lemma lt_2pm1_M : 2 ^ (p - 1) < M \/ M = 1.

  elim (Zle_lt_or_eq 1 M). intro H. rewrite p_M. generalize le_1_M. case M. intro. absurd (2 <= 0); omega. 
  intros q0 H0. elim (Zlog_sup_correct2 (Zpos q0)). omega. omega. intros q0 H0. absurd (1 <= Zneg q0). 
  apply Zlt_not_le. unfold Zlt. trivial. assumption. omega. assumption. Qed.

Local Hint Resolve lt_2pm1_M : a.

Lemma div_M_1 : 2 ^ p / M = 1.

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

Lemma q'_eq_pre : 
  _Z q' = (x / 2 ^ p * (2 ^ (p + w) / M) / 2 ^ w) mod 2 ^ w.

  unfold q'. rewrite Z_from_plusw. rewrite q_eq. rewrite h'_eq. rewrite Zplus_comm. 
  rewrite <- Zdiv_times_plus. rewrite <- Zmult_plus_distr_r. rewrite large_M'_eq. trivial. auto with a. Qed.

Lemma mod_ab_mod : forall z a b m : Z, 0 < m ->
  z = a \/ z = b -> z mod m = a mod m \/ z mod m = b mod m.

  intros z a b m H H0. elim H0; intro H1; rewrite H1; tauto. Qed.

(* <KEEP TOGETHER - q'_eq *)
Lemma q'_eq :
  _Z q' = (x / 2 ^ p * 2 ^ p / M) mod 2 ^ w \/
  _Z q' = (x / 2 ^ p * 2 ^ p / M - 1) mod 2 ^ w.
(* KEEP TOGETHER> *)

  rewrite q'_eq_pre. apply mod_ab_mod. auto with a.
  cut (x / 2 ^ p * (2 ^ p * 2 ^ w / M) / 2 ^ w = x / 2 ^ p * 2 ^ p / M - 1 \/
       x / 2 ^ p * (2 ^ p * 2 ^ w / M) / 2 ^ w = x / 2 ^ p * 2 ^ p / M).
  rewrite Zpower_exp. tauto. apply Zle_ge. auto with a. apply Zle_ge. auto with a.
  cut (x / 2 ^ p * 2 ^ p / M - 1 <= x / 2 ^ p * (2 ^ p * 2 ^ w / M) / 2 ^ w).
  cut (x / 2 ^ p * (2 ^ p * 2 ^ w / M) / 2 ^ w <= x / 2 ^ p * 2 ^ p / M). intros H H0.
  elim (Zle_lt_or_eq (x / 2 ^ p * (2 ^ p * 2 ^ w / M) / 2 ^ w) (x / 2 ^ p * 2 ^ p / M)). intro H1. left.
  omega. intro H1. right. omega. assumption. apply approx_0_one. omega. auto with a. auto with a.
  auto with a. apply approx_m1_one. auto with a. auto with a. omega. auto with a. 
  cut (x < 2 ^ p * 2 ^ w). cut (0 < 2 ^ p). omega. auto with a. rewrite <- Zpower_exp. auto with a. 
  apply Zle_ge. auto with a. apply Zle_ge. auto with a. Qed.

(* <KEEP TOGETHER - y_eq *)
Lemma y_eq :
  _Z y = x / 2 ^ p * 2 ^ p / M * M mod 2 ^ w \/
  _Z y = (x / 2 ^ p * 2 ^ p / M * M - M) mod 2 ^ w.
(* KEEP TOGETHER> *)
  
  unfold y. rewrite Z_from_multw. fold M. elim q'_eq; intro H; rewrite H. left. 
  rewrite <- Zmod_mult_distr_l. trivial. auto with a. right. rewrite <- Zmod_mult_distr_l.
  apply f_equal2 with (f := Zmod). ring. trivial. auto with a. Qed.

Lemma lt_M_2pw : M < 2 ^ w.

  unfold M. apply lt_z__Z. Qed.

Lemma le_M_2pw : M <= 2 ^ w.

  apply Zlt_le_weak. exact lt_M_2pw. Qed.

Hint Resolve lt_M_2pw le_M_2pw : a.

(* <KEEP TOGETHER - d_eq *)
Lemma d_eq :
  _Z d = x / 2 ^ p * 2 ^ p mod M \/
  _Z d = x / 2 ^ p * 2 ^ p mod M + M.
(* KEEP TOGETHER> *)

  unfold d. rewrite Z_from_minusw. rewrite s'_eq. rewrite Zmod_minus_distr_l.
  rewrite <- Zmod_minus_distr_l with (b := x mod 2 ^ p). rewrite <- Zmod_minus_distr_l.
  rewrite <- Zdiv_a_b_b_Zmod. elim y_eq; intro H. left. rewrite H. rewrite <- Zmod_minus_distr_r.
  rewrite Zminus_Zdiv_Zmult. apply modred. apply Zmod_le_0_z. omega. apply Zlt_le_trans with M.
  apply Zmod_lt_z_m. omega. auto with a. omega. auto with a. right. rewrite H. 
  rewrite <- Zmod_minus_distr_r. 
  replace (x / 2 ^ p * 2 ^ p - (x / 2 ^ p * 2 ^ p / M * M - M))
     with (x / 2 ^ p * 2 ^ p - x / 2 ^ p * 2 ^ p / M * M + M). rewrite Zminus_Zdiv_Zmult. apply modred.
  fold (0 + 0). apply Zplus_le_compat. apply Zmod_le_0_z. omega. omega. apply Zlt_le_trans with (M + M).
  apply Zplus_lt_le_compat. apply Zmod_lt_z_m. omega. omega. rewrite Zpow_2_w_is_2Zpow_2_wm1. omega. omega.
  ring. auto with a. auto with a. auto with a. auto with a. auto with a. Qed.

(* <KEEP TOGETHER - r_eq *)
Lemma r_eq : _Z r = (_Z d + x mod 2 ^ p) mod 2 ^ w.
(* KEEP TOGETHER> *)

  unfold r. unfold d. rewrite Z_from_minusw. rewrite Z_from_minusw. fold u. rewrite s'_eq.
  rewrite Zmod_minus_distr_l with (a := x mod 2 ^ w - x mod 2 ^ p).
  rewrite <- Zmod_minus_distr_l with (a := x). rewrite <- Zmod_minus_distr_l. rewrite <- Zmod_plus_distr_l.
  replace (x - x mod 2 ^ p - _Z y + x mod 2 ^ p) with (x - _Z y). rewrite l_eq. (* explicit coercion needed here *)
  rewrite <- Zmod_minus_distr_l. trivial. auto with a. ring. auto with a. auto with a. auto with a.
  auto with a. Qed.

(* <KEEP TOGETHER - r'_eq *)
Lemma r'_eq : _Z r' = x / 2 ^ p * 2 ^ p mod M + x mod 2 ^ p.
(* KEEP TOGETHER> *)

  unfold r'. elim d_eq; intro H. rewrite ltw_true. rewrite r_eq. rewrite H. apply modred. fold (0 + 0).
  apply Zplus_le_compat. apply Zmod_le_0_z. omega. apply Zmod_le_0_z. auto with a.
  rewrite Zpow_2_w_is_2Zpow_2_wm1. apply Zplus_lt_le_compat. apply Zlt_le_trans with M. apply Zmod_lt_z_m. omega.
  assumption. apply Zlt_le_weak. apply Zlt_le_trans with (2 ^ p). apply Zmod_lt_z_m. auto with a. apply Zle_pow_le.
  auto with a. cut (p < w). omega. auto with a. fold M. rewrite H. apply Zmod_lt_z_m. omega. 
  rewrite ltw_false. rewrite Z_from_minusw. rewrite r_eq. rewrite H. fold M. rewrite <- Zmod_minus_distr_l.
  replace ((x / 2 ^ p * 2 ^ p) mod M + M + x mod 2 ^ p - M)
     with ((x / 2 ^ p * 2 ^ p) mod M + x mod 2 ^ p). apply modred. fold (0 + 0). apply Zplus_le_compat.
  apply Zmod_le_0_z. omega. apply Zmod_le_0_z. auto with a. rewrite Zpow_2_w_is_2Zpow_2_wm1. 
  apply Zplus_lt_le_compat. apply Zlt_le_trans with M. apply Zmod_lt_z_m. omega. assumption. 
  apply Zlt_le_weak. apply Zlt_le_trans with (2 ^ p). apply Zmod_lt_z_m. auto with a. apply Zle_pow_le. auto with a. 
  cut (p < w). omega. auto with a. ring. auto with a. fold M. rewrite H. cut (0 <= x / 2 ^ p * 2 ^ p mod M).
  omega. apply Zmod_le_0_z. omega. Qed.

Lemma r'_small : _Z r' < M + 2 ^ p.

  rewrite r'_eq. apply Zplus_lt_compat. apply Zmod_lt_z_m. omega. apply Zmod_lt_z_m. auto with a. Qed.

Lemma r'_x : _Z r' = x mod M \/ _Z r' = x mod M + M \/ _Z r' = x mod M + M + M.

  rewrite r'_eq. rewrite <- Zdivmod_split with (x := x mod 2 ^ p) (m := M). rewrite Zdiv_a_b_b_Zmod.
  rewrite Zplus_comm with (m := x mod 2 ^ p mod M). rewrite Zplus_assoc. elim (mod_plus (x - x mod 2 ^ p) (x mod 2 ^ p) M).
  intro H. rewrite H. replace (x - x mod 2 ^ p + x mod 2 ^ p) with x. elim (div_r'_i x M). intro H0. rewrite <- p_M in H0.
  rewrite H0. left. ring. intro H0. rewrite <- p_M in H0. rewrite H0. right. left. ring. omega. ring. intro H. rewrite H.
  replace (x - x mod 2 ^ p + x mod 2 ^ p) with x. elim (div_r'_i x M). intro H0. rewrite <- p_M in H0. rewrite H0. right. left.
  ring. intro H0. rewrite <- p_M in H0. rewrite H0. right. right. ring. omega. ring. omega. auto with a. omega. Qed.

Lemma r''_small : _Z r'' < 2 ^ p.

  unfold r''. elim (Zle_or_lt M r'); intro H. rewrite ltw_false. simpl. fold M. rewrite modred. cut (r' < M + 2 ^ p).
  omega. exact r'_small. omega. apply Zle_lt_trans with (_Z r'). omega. apply lt_z__Z. fold M. assumption. rewrite ltw_true.
  apply Zlt_le_trans with M. assumption. exact le_M_2pp. fold M. assumption. Qed.

(* <KEEP TOGETHER - r''_eq *)
Lemma r''_eq : _Z r'' = x mod M \/ _Z r'' = x mod M + M.
(* KEEP TOGETHER> *)

  unfold r''. elim (Zle_or_lt M r'); intro H. rewrite ltw_false. simpl. fold M. rewrite modred. elim r'_x. intro H0.
  rewrite H0 in H. absurd (M <= x mod M). apply Zlt_not_le. apply Zmod_lt_z_m. omega. assumption. intro H0; elim H0; intro H1.
  rewrite H1. left. ring. rewrite H1. right. ring. omega. apply Zle_lt_trans with (_Z r'). omega. apply lt_z__Z. fold M.
  assumption. rewrite ltw_true. elim r'_x. tauto. intro H0; elim H0; intro H1. tauto. absurd (x mod M + M + M < M).
  apply Zle_not_lt. cut (0 <= x mod M). omega. apply Zmod_le_0_z. omega. rewrite <- H1. assumption. fold M. assumption. Qed.

(* <KEEP TOGETHER - r'''_eq *)
Lemma r'''_eq : _Z r''' = x mod M.
(* KEEP TOGETHER> *)

  unfold r'''. elim r''_eq; intro H. rewrite ltw_true. assumption. rewrite H. fold M. apply Zmod_lt_z_m. 
  omega. rewrite ltw_false. rewrite Z_from_minusw. fold M. rewrite H.
  replace (x mod M + M - M) with (x mod M). apply modred. apply Zmod_le_0_z. omega. apply Zlt_trans with M.
  apply Zmod_lt_z_m. omega. auto with a. ring. fold M. rewrite H. cut (0 <= x mod M). omega.
  apply Zmod_le_0_z. omega. Qed.

End parm_sec.

Definition in_Mset (M : Z) := 1 <= M <= 2 ^ (w - 1).

Definition Mset := sig in_Mset.

Coercion Z_from_Mset (M : Mset) := proj1_sig (P := in_Mset) M.

Lemma Mset_l : forall M : Mset, 1 <= M.

  intro M. unfold Z_from_Mset. case M. unfold in_Mset. simpl. tauto. Qed.

Lemma Mset_r : forall M : Mset, M <= 2 ^ (w - 1).

  intro M. unfold Z_from_Mset. case M. unfold in_Mset. simpl. tauto. Qed.

Lemma logsuplew : forall (M : Mset), Zlog_sup M <= w.

  intro M. replace w with (Zlog_sup (2 ^ w)). apply Zlog_sup_seq. apply Zlt_le_weak. case M. unfold in_Mset.
  simpl. intros. cut (2 ^ (w - 1) < 2 ^ w). omega. exact lt_2wm1_2w. apply Zlog_sup_pow. exact le_0_w. Qed.

Lemma xhex : forall (M : Mset) (x : Z_ (2 ^ (Zlog_sup M + w))),
  in_Z_ (2 ^ w) (x / 2 ^ w).

  intros M x. unfold in_Z_. split. apply Zle_0_div. apply le_0__Z. exact lt02w. 
  apply Zle_lt_trans with ((2 ^ (Zlog_sup M + w) - 1) / 2 ^ w). apply Zdiv_le. exact lt02w.
  cut (x < 2 ^ (Zlog_sup M + w)). omega. apply lt_z__Z. rewrite Zpower_exp. 
  rewrite Zdiv_mult_minus. cut (2 ^ Zlog_sup M <= 2 ^ w). omega. apply Zle_pow_le. 
  apply Zlog_sup_correct1. apply Zlt_le_trans with 1. omega. apply Mset_l. apply logsuplew.
  exact lt02w. omega. cut (0 < 2 ^ w). omega. exact lt02w. apply Zle_ge. apply Zlog_sup_correct1. 
  apply Zlt_le_trans with 1. omega. apply Mset_l. apply Zle_ge. exact le_0_w. Qed.

Lemma xlex : forall x : Z, in_Z_ (2 ^ w) (x mod 2 ^ w).

  intro. unfold in_Z_. split. apply Zmod_le_0_z. exact lt02w. apply Zmod_lt_z_m. exact lt02w. Qed.

Lemma M'ex : forall M : Mset, in_Z_ (2 ^ w) (2 ^ (Zlog_sup M + w) / M - 2 ^ w).

  intro M. unfold in_Z_. elim (Zle_lt_or_eq 1 M). intro H0. cut (1 <= Zlog_sup M). intro H1.
  split. cut (2 ^ w <= 2 ^ (Zlog_sup M + w) / M). omega. rewrite Zpower_exp. 
  apply Zle_trans with (M * 2 ^ w / M). rewrite Zmult_comm. rewrite Z_div_mult. omega. omega. 
  apply Zdiv_le. omega. apply Zmult_le_compat_r. elim (Zlog_sup_correct2 M). omega. omega. 
  apply Zlt_le_weak. exact lt02w. omega. apply Zle_ge. exact le_0_w. 
  cut (2 ^ (Zlog_sup M + w) / M < 2 ^ w + 2 ^ w). omega. rewrite Zpower_exp.
  apply Zle_lt_trans with (((2 * M - 1) * 2 ^ w) / M). apply Zdiv_le. omega. apply Zmult_le_compat_r.
  replace (Zlog_sup M) with (Zlog_sup M - 1 + 1). rewrite Zpower_exp. 
  apply Zle_trans with ((M - 1) * 2). apply Zmult_le_compat. elim (Zlog_sup_correct2 M). omega.
  omega. simpl. unfold Zpower_pos. simpl. omega. apply Zle_trans with (2 ^ (1 - 1)). simpl. omega.
  apply Zle_pow_le. omega. omega. simpl. unfold Zpower_pos. simpl. omega. omega. omega. omega. ring.
  apply Zlt_le_weak. exact lt02w. replace ((2 * M - 1) * 2 ^ w) with ((2 ^ w + 2 ^ w) * M + - 2 ^ w).
  rewrite Zdiv_times_plus. cut (- 2 ^ w / M < 0). omega. apply Zle_lt_trans with (-1 / M).
  apply Zdiv_le. omega. cut (0 < 2 ^ w). omega. exact lt02w. replace (-1) with (0 * M - 1).
  rewrite Zdiv_mult_minus. omega. omega. omega. omega. ring. omega. ring. omega. apply Zle_ge. exact le_0_w.
  replace 1 with (Zlog_sup 2). apply Zlog_sup_seq. omega. trivial. intro H0. rewrite <- H0. simpl.
  replace (2 ^ w) with (2 ^ w * 1). rewrite Z_div_mult. split. omega. cut (0 < 2 ^ w). omega. exact lt02w.
  omega. ring. apply Mset_l. Qed.

Lemma p1ex_2le : forall M : Mset, in_Z_ w (Zlog_sup M).

  intro M. unfold in_Z_. split. apply Zle_trans with (Zlog_sup 1). simpl. omega. 
  apply Zlog_sup_seq. apply Mset_l. apply Zle_lt_trans with (w - 1).
  rewrite <- Zlog_sup_pow with (i := w - 1). apply Zlog_sup_seq. apply Mset_r. cut (0 < w). omega.
  exact lt_0_w. omega. Qed.

Lemma pex : forall M : Mset, in_Z_ w (Zlog_sup M).

  intros. apply p1ex_2le; omega. Qed.

Lemma tex : forall M : Mset, in_Z_ w (w - Zlog_sup M - 1 / M).

  intro M. unfold in_Z_. elim (Zle_lt_or_eq 1 M). intro H0. replace (1 / M) with 0. split.
  cut (Zlog_sup M <= w). omega. rewrite <- Zlog_sup_pow with (i := w). apply Zlog_sup_seq.
  apply Zle_trans with (2 ^ (w - 1)). apply Mset_r. apply Zlt_le_weak. apply lt_2wm1_2w.
  exact le_0_w. cut (1 <= Zlog_sup M). omega. 
  replace 1 with  (Zlog_sup 2). apply Zlog_sup_seq. omega. trivial. replace 1 with (0 * M + 1).
  symmetry. apply Zdiv_mult_plus. omega. omega. omega. ring. intro H0. rewrite <- H0. simpl. 
  replace (1 / 1) with 1. cut (0 < w). omega. exact lt_0_w. trivial. apply Mset_l. Qed.

Lemma in_Z__if_in_Mset : forall M : Mset, in_Z_ (2 ^ w) M.

  intro M. unfold in_Z_. case M. unfold in_Mset. simpl. intros. cut (2 ^ (w - 1) < 2 ^ w). omega.
  exact lt_2wm1_2w. Qed.

Definition Z__from_Mset (M : Mset) := exist (in_Z_ (2 ^ w)) M (in_Z__if_in_Mset M).

Coercion Z__from_Mset : Mset >-> sig.

(* <KEEP TOGETHER - Cdef *)
Definition C (M : Mset) :=
      ( exist (in_Z_ w)       (Zlog_sup M)                       (pex M),
        exist (in_Z_ w)       (w - Zlog_sup M - 1 / M)           (tex M),
        exist (in_Z_ (2 ^ w)) (2 ^ (Zlog_sup M + w) / M - 2 ^ w) (M'ex M)).
(* KEEP TOGETHER> *)

(* <KEEP TOGETHER - modred_equality *)
Theorem ModRed_eq : forall (M : Mset)
                           (x : Z_ (2 ^ (Zlog_sup M + w))),
  ModRed M
         (C M)
         (exist (in_Z_ (2 ^ w)) (x / 2 ^ w)   (xhex M x))
         (exist (in_Z_ (2 ^ w)) (x mod 2 ^ w) (xlex x))     =
  x mod M.
(* KEEP TOGETHER> *)

  intros M x. unfold ModRed. rewrite r'''_eq; simpl. rewrite Zdivmod_split. trivial.
  exact lt02w. apply Mset_l. apply Mset_r. trivial. elim (Zle_lt_or_eq 1 M). intro H. left.
  replace 1 with (0 * M + 1). rewrite Zdiv_mult_plus. ring. omega. omega. omega. ring. intro H. right.
  auto. apply Mset_l. rewrite <- modred with (x := 2 ^ (Zlog_sup M + w) / M - 2 ^ w) (m := 2 ^ w).
  rewrite Zmod_minus_distr_r. rewrite Z_mod_same. apply f_equal2 with (f := Zmod). ring. trivial.
  apply Zlt_gt. exact lt02w. exact lt02w. elim (M'ex M). omega. elim (M'ex M). omega. 
  apply Zle_lt_trans with ((2 ^ (Zlog_sup M + w) - 1) / 2 ^ w). apply Zdiv_le. exact lt02w.
  cut (x < 2 ^ (Zlog_sup M + w)). omega. apply lt_z__Z. rewrite Zpower_exp. rewrite Zdiv_mult_minus.
  omega. exact lt02w. omega. cut (0 < 2 ^ w). omega. exact lt02w. apply Zle_ge. apply Zlog_sup_correct1.
  apply Zlt_le_trans with 1. omega. apply Mset_l. apply Zle_ge. exact le_0_w. Qed.

Lemma xheex : forall (M : Mset) (h : Z_ (2 ^ Zlog_sup M)),
  in_Z_ (2 ^ w) h.

  intros M h. unfold in_Z_. split. apply le_0__Z. apply Zlt_le_trans with (2 ^ (Zlog_sup M)).
  apply lt_z__Z. apply Zle_pow_le. apply Zlog_sup_correct1. apply Zlt_le_trans with 1. omega. apply Mset_l.
  apply Zle_trans with (Zlog_sup (2 ^ w)).
  apply Zlog_sup_seq. apply Zlt_le_weak. apply Zle_lt_trans with (2 ^ (w - 1)). apply Mset_r.
  exact lt_2wm1_2w. rewrite Zlog_sup_pow. omega. exact le_0_w. Qed.

Lemma xleex : forall (u : Z_ (2 ^ w)),
  in_Z_ (2 ^ w) u.

  intro. unfold in_Z_. split. apply le_0__Z. apply lt_z__Z. Qed.

(* <KEEP TOGETHER - modred_equality2 *)
Theorem ModRed_eq2 : forall (M : Mset) (v : Z_ (2 ^ Zlog_sup M)) (u : Z_ (2 ^ w)),
  ModRed M
        (C M)
        (exist (in_Z_ (2 ^ w)) v (xheex M v))
        (exist (in_Z_ (2 ^ w)) u (xleex u))     =
  (2 ^ w * v + u) mod M.
(* KEEP TOGETHER> *)

  intros M v u. unfold ModRed. rewrite r'''_eq; simpl. rewrite Zmult_comm. trivial. apply Mset_l. apply Mset_r. trivial.
  elim (Zle_lt_or_eq 1 M). intro H. left. replace 1 with (0 * M + 1). 
  rewrite Zdiv_mult_plus. ring. omega. omega. omega. ring. intro H. right. auto. apply Mset_l.
  rewrite <- modred with (x := 2 ^ (Zlog_sup M + w) / M - 2 ^ w) (m := 2 ^ w).
  rewrite Zmod_minus_distr_r. rewrite Z_mod_same. apply f_equal2 with (f := Zmod). ring. trivial.
  apply Zlt_gt. exact lt02w. exact lt02w. elim (M'ex M). omega. elim (M'ex M). omega. apply lt_z__Z. Qed.

Close Scope Z_scope.
