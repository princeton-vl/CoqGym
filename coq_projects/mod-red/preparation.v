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

(* Preparations for fast modular reduction lemmas. *)

(* Coq 8.2 *)
Require Import ZArith.

Open Scope Z_scope.

Definition in_Z_ (m x : Z) := 0 <= x < m.

Definition Z_ (m : Z) := sig (in_Z_ m).

Coercion Z_from_Z_ (m : Z) (x : Z_ m) := proj1_sig (P := in_Z_ m) x.

Notation _Z := (Z_from_Z_ _).

Definition in_Zpls (x : Z) := 0 < x.

Definition Zpls := sig in_Zpls.

Coercion Zpls_ (x : Zpls) := proj1_sig (P := in_Zpls) x.

Lemma le_0__Z : forall (n : Z) (i : Z_ n), 0 <= i.

  intros n i. case i. unfold in_Z_. simpl. tauto. Qed.

Lemma lt_z__Z : forall (n : Z) (i : Z_ n), i < n.

  intros n i. case i. unfold in_Z_. simpl. tauto. Qed.

Lemma Zmod_le_0_z : forall x m : Z, 0 < m -> 0 <= x mod m.

  intros x m H. elim (Z_mod_lt x m); omega. Qed.

Lemma Zmod_lt_z_m : forall x m : Z, 0 < m -> x mod m < m.

  intros x m H. elim (Z_mod_lt x m); omega. Qed.

Lemma Zdiv_small_0 : forall x m : Z, 0 <= x -> x < m -> x / m = 0.

  intros x m H H0. cut (m * (x / m) + x mod m < m). intro H1. cut (m * (x / m) < m).
  intro H2. elim (Zle_or_lt 0 (x / m)); intro H3. elim (Zle_lt_or_eq 0 (x / m)). intro H4.
  cut (m * 1 <= m * (x / m)). intro H5. absurd (m * (x / m) < m). omega. assumption.
  apply Zmult_le_compat_l. omega. omega. omega. assumption. absurd (x / m < 0). apply Zle_not_lt. 
  apply Zge_le. apply Z_div_ge0; omega. assumption. cut (0 <= x mod m). omega. elim (Z_mod_lt x m). omega. 
  omega. rewrite <- Z_div_mod_eq. assumption. omega. Qed.

Lemma Zle_0_div : forall a m : Z, 0 <= a -> 0 < m -> 0 <= a / m.

  intros a m H H0. apply Zge_le. apply Z_div_ge0. omega. omega. Qed.

Lemma Zdiv_le : forall a b m : Z, 0 < m -> a <= b -> a / m <= b / m.

  intros. apply Zge_le. apply Z_div_ge. omega. omega. Qed.

Lemma Zmod_plus_m : forall x m : Z, 0 < m -> (x + m) mod m = x mod m.

  intros x m H. replace (x + m) with (x + 1 * m). apply Z_mod_plus. omega. ring. Qed.

Lemma Zmod_minus_m : forall x m : Z, 0 < m -> (x - m) mod m = x mod m.

  intros x m H. replace (x - m) with (x + -1 * m). apply Z_mod_plus. omega. ring. Qed.

Lemma Zmod_km_plus : forall x k m : Z, 0 < m -> (k * m + x) mod m = x mod m.

  intros. rewrite Zplus_comm. apply Z_mod_plus. omega. Qed.

Lemma Zmod_minus_km : forall x k m : Z, 0 < m -> (x - k * m) mod m = x mod m.

  intros. unfold Zminus. rewrite <- Zopp_mult_distr_l_reverse. apply Z_mod_plus. omega. Qed.

Lemma Zdivmod_split : forall x m : Z, 0 < m -> x / m * m + x mod m = x.

  intros. rewrite Zmult_comm. rewrite <- Z_div_mod_eq. trivial. omega. Qed.

Lemma Zmod_plus_distr_l : forall a b m : Z, 0 < m -> (a + b) mod m = (a mod m + b) mod m.

  intros a b m H. replace (a + b) with (a / m * m + a mod m + b). rewrite Zplus_comm.
  rewrite Zplus_comm with (m := a mod m). rewrite Zplus_assoc. rewrite Z_mod_plus. 
  rewrite Zplus_comm. trivial. omega. rewrite Zdivmod_split. trivial. assumption. Qed.

Lemma Zmod_mult_distr_l : forall a b m : Z, 0 < m -> (a * b) mod m = (a mod m * b) mod m.

  intros a b m H. replace (a * b) with ((a / m * m + a mod m) * b).
  rewrite Zmult_plus_distr_l. rewrite Zmod_plus_distr_l.
  replace (a / m * m * b) with (0 + a / m * b * m). rewrite Z_mod_plus. trivial. omega.
  ring. assumption. rewrite Zdivmod_split. trivial. assumption. Qed.

Lemma Zmod_minus_distr_l : forall a b m : Z, 0 < m -> (a - b) mod m = (a mod m - b) mod m.

  unfold Zminus. intros. apply Zmod_plus_distr_l. assumption. Qed.

Lemma Zmod_minus_distr_r : forall a b m : Z, 0 < m -> (a - b) mod m = (a - b mod m) mod m.

  intros a b m H. unfold Zminus. replace (- b) with (b * -1). do 2 rewrite Zplus_comm with (n := a).
  rewrite Zmod_plus_distr_l. rewrite Zmod_mult_distr_l. rewrite <- Zmod_plus_distr_l.
  apply f_equal2 with (f := Zmod). ring. trivial. assumption. assumption. assumption. ring. Qed.

Lemma modred : forall x m : Z, 0 <= x -> x < m -> x mod m = x.

  intros x m H H0. rewrite <- Zdivmod_split with (x := x) (m := m). 
  replace ((x / m * m + x mod m) mod m) with (x mod m).
  rewrite Zdiv_small_0; auto. rewrite Zdivmod_split. trivial. omega. omega. Qed.

Lemma Zdiv_a_b_b_Zmod : forall a b : Z, 0 < b -> a / b * b = a - a mod b.
  
  intros a b H. cut (a / b * b + a mod b = a). omega. apply Zdivmod_split. assumption. Qed.

Lemma Zminus_Zdiv_Zmult : forall a b : Z, 0 < b -> a - a / b * b = a mod b.

  intros. rewrite Zdiv_a_b_b_Zmod. ring. assumption. Qed.

Lemma Zmod_prod_Zmod : forall x y z : Z, 0 < y -> 0 < z -> x mod (y * z) mod z = x mod z.

  intros x y z H H0. rewrite <- Zminus_Zdiv_Zmult with (a := x). rewrite Zmult_assoc.
  apply Zmod_minus_km. assumption. fold (0 * 0). apply Zmult_lt_0_compat; omega. Qed.

Lemma Zdiv_mult_plus : forall a b m : Z, 0 < m -> 0 <= b -> b < m -> (a * m + b) / m = a.

  intros. rewrite Zplus_comm. rewrite Z_div_plus. rewrite Zdiv_small_0. ring.
  assumption. assumption. omega. Qed.

Lemma Zdiv_mult_minus : forall a b m : Z, 0 < m -> 0 < b -> b <= m -> (a * m - b) / m = a - 1.

  intros. replace (a * m - b) with ((a - 1) * m + (m - b)). apply Zdiv_mult_plus. auto. omega.
  omega. ring. Qed.

Lemma Zdiv_times_plus : forall x y m : Z, 0 < m -> (x * m + y) / m = (x + y / m).

  intros. rewrite Zplus_comm. rewrite Z_div_plus. ring. omega. Qed.

Lemma div_1_id : forall a : Z, a / 1 = a.

  intro a. replace a with (a * 1). rewrite Z_div_mult. ring. omega. ring. Qed.

Lemma mod_1_0 : forall z : Z, z mod 1 = 0.

  intro z. cut (0 <= z mod 1). cut (z mod 1 < 1). omega. apply Zmod_lt_z_m. omega. apply Zmod_le_0_z. omega. Qed.

Set Implicit Arguments.
Unset Strict Implicit.

Definition If (T : Set) (b : bool) (t e : T) :=
   (* If T b t e  =  if b then t else e *)
  match b with
  | true => t
  | false => e
  end.

Set Strict Implicit.
Unset Implicit Arguments.

Lemma Z_to_inject_nat : forall x : Z, 0 <= x -> Z_of_nat (Zabs_nat x) = x.

  simple destruct x. simpl. omega. intros. simpl. symmetry. 
  apply Zpos_eq_Z_of_nat_o_nat_of_P. intros p H. absurd (0 <= Zneg p). unfold Zle. tauto. 
  assumption. Qed.

Lemma Zlt_0_power_nat : forall i : nat, 0 < Zpower_nat 2 i.

  simple induction i. replace (Zpower_nat 2 0) with 1. omega. trivial. intros n H.
  rewrite <- two_power_nat_correct. rewrite two_power_nat_S. rewrite two_power_nat_correct.
  omega. Qed.

Lemma Zpower_nat_Zpower : forall i : nat, Zpower_nat 2 i = 2 ^ Z_of_nat i.

  induction i. simpl. trivial. rewrite <- two_power_nat_correct. rewrite two_power_nat_S.
  rewrite two_power_nat_correct. rewrite IHi. replace (Z_of_nat (S i)) with (1 + Z_of_nat i).
  rewrite Zpower_exp. replace (2 ^ 1) with 2. trivial. trivial. omega. omega. rewrite inj_S.
  omega. Qed.

Lemma Zpower_Zpower_nat : forall i : Z, 0 <= i -> 2 ^ i = Zpower_nat 2 (Zabs_nat i).

  intros i H. rewrite Zpower_nat_Zpower. rewrite Z_to_inject_nat. trivial. assumption. Qed.

Lemma lt_0_Zpow : forall x : Z, 0 <= x -> 0 < 2 ^ x.

  intros x H. rewrite Zpower_Zpower_nat. apply Zlt_0_power_nat. assumption. Qed.

Lemma Zlt_pow_lt :
  forall i j : Z, 0 <= i -> i < j -> 2 ^ i < 2 ^ j.

  intros i j Hi Hij. replace j with (i + (j - i)). rewrite Zpower_exp. 
  apply Zle_lt_trans with (2 ^ i * 2 ^ 0). simpl. omega. apply Zmult_lt_compat_l. apply lt_0_Zpow.
  assumption. replace (j - i) with (j - i - 1 + 1).  rewrite Zpower_exp. replace (2 ^ 1) with 2.
  replace (2 ^ 0) with 1. cut (0 < 2 ^ (j - i - 1)). omega. apply lt_0_Zpow. omega. trivial. trivial. 
  omega. omega.  ring. omega. omega. ring. Qed.

Lemma Zle_pow_le :
  forall i j : Z, 0 <= i -> i <= j -> 2 ^ i <= 2 ^ j.

  intros i j Hi Hij. elim (Zle_lt_or_eq i j). intro. apply Zlt_le_weak. apply Zlt_pow_lt.
  assumption. assumption. intro H. rewrite H. omega. assumption. Qed.

Lemma lt_pow_lt :
  forall i j : Z, 0 <= i -> 0 <= j -> 2 ^ i < 2 ^ j -> i < j.

  intros i j Hi Hj Hij. elim (Zle_lt_or_eq i j). trivial. intro H. rewrite H in Hij.
  absurd (2 ^ j < 2 ^ j). omega. assumption. elim (Zle_or_lt i j). trivial. intro H. cut (2 ^ j < 2 ^ i).
  intro H0. absurd (2 ^ j < 2 ^ i); omega. apply Zlt_pow_lt; omega. Qed.

Definition Zlog_sup (M : Z) :=
  match M with
  | Zpos p => log_sup p
  | _ => 0
  end.

Lemma Zlog_sup_pow : forall i : Z, 0 <= i -> Zlog_sup (2 ^ i) = i.

  intros i H. replace (2 ^ i) with (Zpos (shift_nat (Zabs_nat i) 1)). simpl. rewrite log_sup_shift_nat.
  apply Z_to_inject_nat. assumption. rewrite shift_nat_correct. rewrite Zpower_nat_Zpower. 
  rewrite Z_to_inject_nat. ring. assumption. Qed.

Lemma two_p_pow : forall z : Z, 0 <= z -> two_p z = 2 ^ z.

  intros z H. unfold two_p. case z. trivial. intro p. rewrite two_power_pos_correct. trivial. trivial. Qed.

Lemma Zlog_sup_correct1 : forall z : Z, 0 < z -> 0 <= Zlog_sup z. 

  intro z. case z. intro H. absurd (0 < 0); omega. simpl. intros p H. apply log_sup_correct1.
  intros p H. absurd (0 < Zneg p). simplify_eq. assumption. Qed.

Lemma Zlog_sup_correct2 : forall z : Z, 0 < z -> 2 ^ (Zlog_sup z - 1) < z <= 2 ^ Zlog_sup z.

  intros z H. elim (Zle_or_lt z 1). intro Hz. cut (z = 1). intro H0. rewrite H0. simpl. omega. omega.
  case z. intro. absurd (1 < 0); omega. simpl. intros p H0. rewrite <- two_p_pow. rewrite <- two_p_pow. 
  replace (log_sup p - 1) with (Zpred (log_sup p)). apply log_sup_correct2. unfold Zpred. ring. apply log_sup_correct1.
  generalize H0. case p. simpl. intros q H1. cut (0 <= log_inf q). omega. apply log_inf_correct1. simpl.
  intros q H1. cut (0 <= log_sup q). omega. apply log_sup_correct1. intro. absurd (1 < 1); omega.
  intros p H0. absurd (1 < Zneg p). simplify_eq. assumption. Qed.

Lemma Zlog_sup_unique : forall z : Z, 0 < z -> forall i j : Z, 0 <= i -> 0 <= j ->
  2 ^ (i - 1) < z -> z <= 2 ^ i -> 2 ^ (j - 1) < z -> z <= 2 ^ j -> i = j.

  intros z Hz i j Hi Hj H0 H1 H2 H3. elim (Zle_lt_or_eq i j). intro H4. cut (2 ^ i <= 2 ^ (j - 1)).
  intro H5. absurd (2 ^ (j - 1) < z). omega. assumption. apply Zle_pow_le. assumption. omega. trivial.
  elim (Zle_or_lt i j); intro H4. assumption. cut (2 ^ j <= 2 ^ (i - 1)). intro H5.
  absurd (2 ^ (i - 1) < z). omega. assumption. apply Zle_pow_le. assumption. omega. Qed.

Lemma Zlog_sup_from_interval : forall z : Z, 0 < z -> forall i : Z, 0 <= i -> 2 ^ (i - 1) < z ->
  z <= 2 ^ i -> Zlog_sup z = i.

  intros z Hz i Hi Hl Hh. apply Zlog_sup_unique with (z := z). assumption. apply Zlog_sup_correct1.
  assumption. assumption. elim (Zlog_sup_correct2 z). tauto. assumption. elim (Zlog_sup_correct2 z).
  tauto. assumption. assumption. assumption. Qed.

Lemma Zlog_sup_seq : forall p q : Z, p <= q -> Zlog_sup p <= Zlog_sup q.

  intros p q H. elim (Zle_or_lt p 0). intro Hp. replace (Zlog_sup p) with 0. elim (Zle_or_lt q 0).
  intro Hq. replace (Zlog_sup q) with 0. omega. generalize Hq. elim q. trivial. intros r Hr.
  absurd (Zpos r <= 0). apply Zlt_not_le. unfold Zlt. trivial. assumption. intros r Hr. trivial.
  apply Zlog_sup_correct1. generalize Hp. elim p. trivial. intros r Hr. absurd (Zpos r <= 0).
  apply Zlt_not_le. unfold Zlt. trivial. assumption. intros r Hr. trivial. intro H0.
  elim (Zle_or_lt (Zlog_sup p) (Zlog_sup q)); intro H1. assumption. cut (Zlog_sup q <= Zlog_sup p - 1). 
  intro H2. cut (2 ^ Zlog_sup q <= 2 ^ (Zlog_sup p - 1)). intro H3. absurd (p <= q). apply Zlt_not_le. 
  apply Zle_lt_trans with (2 ^ Zlog_sup q). elim (Zlog_sup_correct2 q). omega. omega. 
  elim (Zlog_sup_correct2 p). omega. assumption. assumption. apply Zle_pow_le. apply Zlog_sup_correct1.
  omega. assumption. omega. Qed.
  
Lemma Z_pow_plus : forall x : Z, 0 <= x -> 2 ^ x + 2 ^ x = 2 ^ (x + 1).

  intros. rewrite Zplus_diag_eq_mult_2. rewrite Zpower_exp. trivial. omega. omega. Qed.

Lemma Zdivdivdiv : forall x y z : Z, 0 < y -> 0 < z -> x / y / z = x / (y * z).

  intros x y z H H0. 
  replace (x / y / z) with
   ((x / (y * z) * z * y + x mod (y * z)) / y / z).
  rewrite Zdiv_times_plus. rewrite Zdiv_times_plus. rewrite Zplus_comm. rewrite Zdiv_small_0. ring.
  apply Zle_0_div. apply Zmod_le_0_z. apply Zmult_lt_0_compat; assumption. assumption.
  apply Zle_lt_trans with ((y * z - 1) / y). apply Zdiv_le. assumption. cut (x mod (y * z) < y * z).
  omega. apply Zmod_lt_z_m. apply Zmult_lt_0_compat; omega. rewrite Zmult_comm. rewrite Zdiv_mult_minus;
  omega. assumption. assumption. rewrite Zmult_comm with (n := y). rewrite <- Zmult_assoc.
  rewrite Zdivmod_split. trivial. apply Zmult_lt_0_compat; assumption. Qed.

Lemma Zdiv_simpl : forall x y z : Z, 0 < y -> 0 < z -> (x * z) / (y * z) = x / y.

  intros x y z H H0. rewrite Zmult_comm with (n := y). rewrite <- Zdivdivdiv.
  rewrite Z_div_mult. trivial. omega. assumption. assumption. Qed.

Lemma Zdiv_den_le : forall x y z : Z, 0 <= x -> 0 < z -> z <= y -> x / y <= x / z.
  
  intros x y z H H0 H1. rewrite <- Zdiv_simpl with (y := y) (z := z).
  rewrite <- Zdiv_simpl with (y := z) (z := y). rewrite Zmult_comm with (n := y).
  apply Zdiv_le. apply Zmult_lt_0_compat; omega. apply Zmult_le_compat_l; omega. assumption. omega. omega. 
  assumption. Qed.

Lemma approx_cz : forall c y z : Z, 0 < c -> 0 < y -> 0 <= z -> z <= c ->
  z / y - c / y * z / c <= 1.

  intros c y z Hc Hy Hz Hzc. rewrite <- Z_div_mult with (a := z / y - c / y * z / c) (b := c * y).
  rewrite Zmult_minus_distr_r. rewrite Zmult_comm with (n := c). rewrite Zmult_assoc.
  rewrite Zdiv_a_b_b_Zmod. rewrite Zmult_comm with (n := y). rewrite Zmult_assoc. rewrite Zdiv_a_b_b_Zmod.
  do 2 rewrite Zmult_minus_distr_r. rewrite <- Zmult_assoc. rewrite Zmult_comm with (m := y).
  rewrite Zmult_assoc. rewrite Zdiv_a_b_b_Zmod. rewrite Zmult_minus_distr_r.
  replace (z * c - z mod y * c - (c * z - c mod y * z - (c / y * z) mod c * y))
     with (c mod y * z + (c / y * z) mod c * y - z mod y * c).
  apply Zle_trans with ((c mod y * z + c * y) / (c * y)). apply Zdiv_le. apply Zmult_lt_0_compat;
  assumption. apply Zle_trans with (c mod y * z + (c / y * z) mod c * y). cut (0 <= z mod y * c). omega.
  apply Zmult_le_0_compat. apply Zmod_le_0_z. assumption. omega. apply Zplus_le_compat. omega.
  apply Zmult_le_compat_r. apply Zlt_le_weak. apply Zmod_lt_z_m. assumption. omega.
  replace (c mod y * z + c * y) with (1 * (c * y) + c mod y * z).
  rewrite Zdiv_times_plus. cut (c mod y * z / (c * y) <= 0). omega.
  apply Zle_trans with ((y - 1) * z / (c * y)). apply Zdiv_le. apply Zmult_lt_0_compat; assumption. 
  apply Zmult_le_compat_r. cut (c mod y < y). omega. apply Zmod_lt_z_m. 
  assumption. omega. rewrite Zdiv_small_0. omega. apply Zmult_le_0_compat; omega. 
  rewrite Zmult_comm with (n := c). elim (Zle_lt_or_eq 0 z). intro H. apply Zlt_le_trans with (y * z). 
  apply Zmult_lt_compat_r. assumption. omega. apply Zmult_le_compat_l; omega. intro H. rewrite <- H. 
  replace ((y - 1) * 0) with 0. apply Zmult_lt_0_compat; assumption. ring. assumption. 
  apply Zmult_lt_0_compat; assumption. ring. ring. assumption. assumption. assumption. 
  apply Zmult_gt_0_compat; omega. Qed.

Lemma approx_le1 : forall a b y x : Z, 0 < a -> 0 < b -> 0 < y -> 0 <= x -> x < a * b + a ->
  x / a * a / y - x / a * (a * b / y) / b <= 1.

  intros a b y x Ha Hb Hy Hx Hxab. rewrite Zmult_comm with (m := a * b / y).
  rewrite <- Zdiv_simpl with (y := b) (z := a). rewrite <- Zmult_assoc. rewrite Zmult_comm with (n := b).
  apply approx_cz. apply Zmult_lt_0_compat; assumption. assumption. apply Zmult_le_0_compat.
  apply Zle_0_div; assumption. omega. rewrite Zmult_comm with (m := b). apply Zmult_le_compat_r.
  apply Zle_trans with ((b * a + (a - 1)) / a). apply Zdiv_le. assumption. rewrite Zmult_comm. omega.
  rewrite Zdiv_mult_plus; omega. omega. assumption. assumption. Qed.

Lemma approx_m1_one : forall a b y x : Z, 0 < a -> 0 < b -> 0 < y -> 0 <= x -> x < a * b + a ->
  x / a * a / y - 1 <= x / a * (a * b / y) / b.

  intros a b y x Ha Hb Hy Hx Hxab. cut (x / a * a / y - x / a * (a * b / y) / b <= 1). omega.
  apply approx_le1; assumption. Qed.

Lemma approx_cz0 : forall c y z : Z, 0 < c -> 0 < y -> 0 <= z ->
  c / y * z / c <= z / y.

  intros c y z Hc Hy Hz. rewrite <- Zdiv_simpl with (z := y). replace (c / y * z * y) with (c / y * y * z).
  apply Zle_trans with (c * z / (c * y)). apply Zdiv_le. apply Zmult_lt_0_compat; assumption.
  apply Zmult_le_compat_r. rewrite Zmult_comm. apply Z_mult_div_ge. omega. assumption. 
  do 2 rewrite Zmult_comm with (n := c). rewrite Zdiv_simpl. omega. assumption. assumption. ring.
  assumption. assumption. Qed.

Lemma approx_ab_le : forall a b y x : Z, 0 < a -> 0 < b -> 0 < y -> 0 <= x ->
  x / a * (a * b / y) / b <= x / a * a / y.

  intros a b y x Ha Hb Hy Hx. rewrite Zmult_comm. rewrite <- Zdiv_simpl with (z := a). 
  rewrite <- Zmult_assoc. rewrite Zmult_comm with (n := b). apply approx_cz0. apply Zmult_lt_0_compat; assumption.
  assumption. apply Zmult_le_0_compat. apply Zle_0_div; assumption. omega. assumption. assumption. Qed.

Lemma approx_m1_two : forall y a b x : Z, 0 < y -> 0 < a -> a <= y -> 0 < b -> 0 <= x ->
  x / y - 1 <= x / a * a / y.

  intros y a b x lt_0_y lt_0_a le_a_y lt_0_b le_0_x. replace (x / y) with ((a * (x / a) + x mod a) / y).
  unfold Zminus. rewrite <- Z_div_plus. apply Zdiv_le. assumption. rewrite Zmult_comm.
  cut (x mod a <= 1 * y). omega. apply Zle_trans with a. apply Zlt_le_weak. apply Zmod_lt_z_m. assumption.
  omega. omega. rewrite <- Z_div_mod_eq. trivial. omega. Qed.

Lemma approx_m2 : forall y a b x : Z, 0 < y -> 0 < a -> a <= y -> 0 < b -> 0 <= x ->
  x < a * b + a -> x / y - 2 <= x / a * (a * b / y) / b.

  intros y a b x lt_0_y lt_0_a lt_a_y lt_0_b le_0_x lt_x_ab.
  apply Zle_trans with (x / a * a / y - 1). cut (x / y - 1 <= x / a * a / y). omega.
  apply approx_m1_two with (b := b); assumption. apply approx_m1_one; omega. Qed.

Lemma approx_0_one : forall y a b x : Z, 0 < y -> 0 < a -> 0 < b -> 0 <= x ->
  x / a * (a * b / y) / b <= x / a * a / y.

  intros y a b x lt_0_y lt_0_a lt_0_b le_0_x. rewrite <- Zdiv_simpl with (z := y). rewrite <- Zmult_assoc.
  apply Zle_trans with (x / a * (a * b) / (b * y)). apply Zdiv_le. apply Zmult_lt_0_compat; omega.
  apply Zmult_le_compat_l. rewrite Zmult_comm. apply Z_mult_div_ge. omega. apply Zle_0_div;
  omega. rewrite Zmult_comm with (m := y). rewrite Zmult_assoc. rewrite Zdiv_simpl. omega. assumption. 
  assumption. assumption. assumption. Qed.

Lemma approx_0_two : forall y a b x : Z, 0 < y -> 0 < a -> 0 < b -> 0 <= x ->
  x / a * a / y <= x / y.

  intros y a b x lt_0_y lt_0_a lt_0_b le_0_x.
  apply Zdiv_le. assumption. rewrite Zmult_comm. apply Z_mult_div_ge. omega. Qed.

Lemma approx_0 : forall y a b x : Z, 0 < y -> 0 < a -> 0 < b -> 0 <= x ->
  x / a * (a * b / y) / b <= x / y.

  intros y a b x lt_0_y lt_0_a lt_0_b le_0_x. apply Zle_trans with (x / a * a / y). apply approx_0_one;
  assumption. apply approx_0_two with (b := b); assumption. Qed.

Lemma mod_over_div : forall a b c m : Z, 0 < b -> 0 < m -> (a * b + c) / b * b mod m = (a mod m * b + c) / b * b mod m.

  intros a b c m Hb Hm. rewrite Zplus_comm. rewrite Z_div_plus. rewrite Zplus_comm with (m := c). rewrite Z_div_plus.
  rewrite Zmod_mult_distr_l. rewrite Zplus_comm. rewrite Zmod_plus_distr_l. rewrite Zplus_comm. rewrite <- Zmod_mult_distr_l.
  trivial. assumption. assumption. assumption. omega. omega. Qed.

Lemma sum_r'_i : forall a b m : Z, 0 < m -> (a mod m + b mod m) / m = 0 \/ (a mod m + b mod m) / m = 1.

  intros a b m H. cut (0 <= (a mod m + b mod m) / m). cut ((a mod m + b mod m) / m <= 1). omega. 
  apply Zle_trans with ((m - 1 + m) / m). apply Zdiv_le. omega. apply Zplus_le_compat. cut (a mod m < m). omega.
  apply Zmod_lt_z_m. omega. cut (b mod m < m). omega. apply Zmod_lt_z_m. omega. replace (m - 1 + m) with (2 * m - 1).
  rewrite Zdiv_mult_minus. omega. omega. omega. omega. ring. apply Zle_0_div. fold (0 + 0). apply Zplus_le_compat. 
  apply Zmod_le_0_z. omega. apply Zmod_le_0_z. omega. omega. Qed.

Lemma mod_plus : forall a b m : Z, 0 < m -> a mod m + b mod m = (a + b) mod m \/ a mod m + b mod m = (a + b) mod m + m.

  intros a b m H. rewrite Z_div_mod_eq with (a := a mod m + b mod m) (b := m). elim sum_r'_i with (a := a) (b := b) (m := m).
  intro H0. rewrite H0. left. rewrite <- Zmod_plus_distr_l. rewrite Zplus_comm with (n := a). rewrite <- Zmod_plus_distr_l.
  rewrite Zplus_comm with (m := a). ring. omega. omega. intro H0. rewrite H0. right. rewrite <- Zmod_plus_distr_l. 
  rewrite Zplus_comm with (n := a). rewrite <- Zmod_plus_distr_l. rewrite Zplus_comm with (m := a). ring. omega. omega. omega.
  omega. Qed.

Lemma div_m_1 : forall m : Z, 0 < m -> 2 ^ Zlog_sup m / m = 1.

  intros m H. elim (Zle_lt_or_eq 1 m). intro H0. replace (2 ^ Zlog_sup m) with (1 * m + (2 ^ Zlog_sup m - m)).
  apply Zdiv_mult_plus. omega. cut (m <= 2 ^ Zlog_sup m). omega. elim (Zlog_sup_correct2 m). tauto. assumption.
  cut (2 ^ Zlog_sup m < m + m). omega. 
  apply Zlt_le_trans with (2 ^ (Zlog_sup m - 1) + 1 + (2 ^ (Zlog_sup m - 1) + 1)).
  replace (2 ^ (Zlog_sup m - 1) + 1 + (2 ^ (Zlog_sup m - 1) + 1))
     with (2 ^ (Zlog_sup m - 1) + 2 ^ (Zlog_sup m - 1) + 2). rewrite Z_pow_plus.
  replace (Zlog_sup m - 1 + 1) with (Zlog_sup m). omega. ring. cut (1 <= Zlog_sup m). omega. replace 1 with (Zlog_sup 2).
  apply Zlog_sup_seq. omega. trivial. ring. apply Zplus_le_compat. cut (2 ^ (Zlog_sup m - 1) < m). omega.
  elim (Zlog_sup_correct2 m). tauto. assumption. cut (2 ^ (Zlog_sup m - 1) < m). omega. elim (Zlog_sup_correct2 m). tauto.
  assumption. ring. intro H0. rewrite <- H0. simpl. unfold Zdiv. trivial. omega. Qed.

Lemma div_r'_i : forall a m : Z, 0 < m -> a mod 2 ^ Zlog_sup m / m = 0 \/ a mod 2 ^ Zlog_sup m / m = 1.

  intros a m H. cut (0 <= a mod 2 ^ Zlog_sup m / m). cut (a mod 2 ^ Zlog_sup m / m <= 1). omega.
  apply Zle_trans with (2 ^ Zlog_sup m / m). apply Zdiv_le. assumption. cut (a mod 2 ^ Zlog_sup m < 2 ^ Zlog_sup m). omega.
  apply Zmod_lt_z_m. apply lt_0_Zpow. apply Zlog_sup_correct1. assumption. rewrite div_m_1. omega. assumption. apply Zle_0_div.
  apply Zmod_le_0_z. apply lt_0_Zpow. apply Zlog_sup_correct1. assumption. assumption. Qed.

(* <KEEP TOGETHER - approx_0_m2 *)
Theorem approx_0_m2 : forall (y b : Zpls) (a : Z_ y) (x : Z_ (a * b + a)),
  x / y - 2 <= x / a * (a * b / y) / b <= x / y.

  intros y b a x. split. apply approx_m2. case y; trivial. elim (Zle_lt_or_eq 0 a). trivial. intro H.
  rewrite <- H in x. simpl in x. elim x. unfold in_Z_. intros z H0. elim H0; intros H1 H2. absurd (z < 0);
  omega. apply le_0__Z. apply Zlt_le_weak. apply lt_z__Z. case b; trivial. apply le_0__Z. apply lt_z__Z.
  apply approx_0. elim y; trivial. elim (Zle_lt_or_eq 0 a). trivial. intro H. rewrite <- H in x. 
  simpl in x. elim x. unfold in_Z_. intros z H0. elim H0; intros H1 H2. absurd (z < 0);
  omega. apply le_0__Z. elim b; trivial. apply le_0__Z. Qed.
(* KEEP TOGETHER> - approx_0_m2 *)

(* <KEEP TOGETHER - div_approx1 *)
Theorem div_approx1 : forall (y : Zpls) (a : Zpls) (b : Zpls)
  (x : Z_ (a * b + a)),
    x / a * a / y - 1 <= x / a * (a * b / y) / b <= 
    x / a * a / y.

  intros y a b x. cut (0 < y). cut (0 < a). cut (0 < b).
  cut (0 <= x). cut (x < (a * b + a)). intros Hxlt H0lex Hb Ha Hy. split.
  apply approx_m1_one; assumption. apply approx_ab_le; assumption. apply lt_z__Z. apply le_0__Z.
  elim b. trivial. elim a. trivial. elim y. trivial. Qed.
(* KEEP TOGETHER> - div_approx1 *)

Close Scope Z_scope.
