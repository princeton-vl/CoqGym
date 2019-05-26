(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*                   Solange Coupet-Grimal & Line Jakubiec                  *)
(*                                                                          *)
(*                                                                          *)
(*              Laboratoire d'Informatique de Marseille                     *)
(*               CMI-Technopole de Chateau-Gombert                          *)
(*                   39, Rue F. Joliot Curie                                *)
(*                   13453 MARSEILLE Cedex 13                               *)
(*           e-mail:{Solange.Coupet,Line.Jakubiec}@lim.univ-mrs.fr          *)
(*                                                                          *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              May 30th 1996                               *)
(*                                                                          *)
(****************************************************************************)
(*                               Lib_Mult.v                                 *)
(****************************************************************************)

Require Export Lib_Plus.

Lemma plus_mult : forall n : nat, n + n = 2 * n.
intros n; simpl in |- *; elim plus_n_O; auto with arith.
Qed.
Hint Resolve plus_mult.


Lemma lt_mult_lt_O : forall n m : nat, 0 < n * m -> 0 < m -> 0 < n.
simple induction n; auto with arith.
Qed.


Lemma le_mult_cst : forall x y a : nat, x <= y -> a * x <= a * y.
auto with arith.
Qed.



Lemma le_mult_csts : forall a b c d : nat, a <= b -> c <= d -> a * c <= b * d.
intros.
apply le_trans with (a * d).
apply le_mult_cst; assumption.
elim mult_comm; elim mult_comm with d b.
apply le_mult_cst; assumption.
Qed.
Hint Resolve le_mult_csts.



Lemma lt_mult_n_Sn : forall n m : nat, 0 < m -> n * m < S n * m.
simple induction n; simple induction m; auto with arith.
intros; simpl in |- *.
elim plus_n_O; auto with arith.
intro.
elim mult_n_O; elim mult_n_O; auto with arith.
intros; simpl in |- *; apply lt_n_S; auto with arith.
Qed.
Hint Resolve lt_mult_n_Sn.



Lemma lt_mult_cst : forall x y a : nat, x < y -> 0 < a -> a * x < a * y.
intros.
elim H.
elim mult_comm; elim mult_comm with (S x) a.
apply lt_mult_n_Sn; assumption.
intros.
apply lt_trans with (a * m).
assumption.
elim mult_comm; elim mult_comm with (S m) a.
apply lt_mult_n_Sn; assumption. 
Qed.
Hint Resolve lt_mult_cst.



Lemma lt_mult_csts : forall a b c d : nat, a < b -> c < d -> a * c < b * d.
intros.
apply le_lt_trans with (a * d).
apply le_mult_cst.
apply lt_le_weak; assumption.
elim mult_comm; elim mult_comm with d b.
apply lt_mult_cst.
assumption.
apply lt_O with c; auto with arith.
Qed.
Hint Resolve lt_mult_csts.



Lemma pred_mult : forall n m : nat, 0 < n -> n * m = pred n * m + m.
intros.
elim H; simpl in |- *; auto with arith.
Qed.
Hint Resolve pred_mult.



Lemma le_lt_plus_mult :
 forall n m p n' p' : nat, n <= n' -> p < p' -> n * m + p < n' * m + p'.
intros; apply le_lt_plus; auto with arith.
Qed.



Lemma le_mult_l : forall n m : nat, 0 < m -> n <= m * n.
intros.
rewrite (S_pred m 0); trivial with arith.
simpl in |- *; auto with arith.
Qed.
Hint Resolve le_mult_l.



Lemma le_mult_r : forall n m : nat, 0 < m -> n <= n * m.
intros n m; elim (mult_comm m n); auto with arith.
Qed.
Hint Resolve le_mult_r.



Lemma lt_mult : forall n m : nat, 1 < m -> 0 < n -> n < n * m.
intros.
pattern n at 1 in |- *.
elim mult_1_r.
apply lt_mult_cst; auto with arith.
Qed.
Hint Resolve lt_mult.



Lemma lt_SO_mult : forall n m : nat, 1 < n -> 0 < m -> 1 < n * m.
intros.
apply lt_le_trans with (1 * n).
auto with arith.
simpl in |- *.
elim plus_n_O.
apply le_mult_r; auto with arith.
Qed.



Lemma plus_m_mult_n_m : forall n m : nat, m + n * m = S n * m.
simple induction n; simple induction m; simpl in |- *; auto with arith.
Qed.



Lemma y_eq_multxy : forall x y : nat, x = 1 \/ y = 0 -> y = x * y.
intros x y H; elim H; clear H; intros H; rewrite H; simpl in |- *;
 auto with arith.
Qed.



Lemma mult_plus_distr_left : forall n m p : nat, p * (n + m) = p * n + p * m.
intros; elim mult_comm.
elim (mult_comm n p).
elim (mult_comm m p).
auto with arith.
Qed.
Hint Resolve mult_plus_distr_left.



Lemma mult_minus_distr_left : forall n m p : nat, p * (n - m) = p * n - p * m.
intros.
rewrite (mult_comm p (n - m)); rewrite (mult_comm p n);
 rewrite (mult_comm p m); auto with arith.
Qed.
Hint Resolve mult_minus_distr_left.



Lemma mult_eq_zero : forall a b : nat, a * b = 0 -> a = 0 \/ b = 0.
intros a b; elim a.
auto with arith.
intros n H_rec H.
right.
elim (plus_eq_zero (n * b) b); auto with arith.
simpl in H; elim plus_comm.
auto with arith.
Qed. 
Hint Resolve mult_eq_zero.



Lemma lt_mult_S_S : forall n m : nat, 0 < S n * S m.
simple induction n; simpl in |- *; auto with arith.
Qed.
Hint Resolve lt_mult_S_S.



Lemma mult_S_O : forall n m : nat, 0 = S n * m -> 0 = m.
intros n m H.
elim (mult_eq_zero (S n) m); auto with arith.
intro; absurd (S n = 0); auto with arith.
Qed.



Lemma mult_reg_l : forall a b p : nat, p * a = p * b -> p = 0 \/ a = b.
intros a b p; generalize b; generalize a; clear a b.
simple induction a.
replace (p * 0) with 0.
intros.
cut (p = 0 \/ b = 0).
intro.
elim H0; auto with arith.
cut (p * b = 0).
elim (mult_eq_zero p b); auto with arith.
auto with arith.
apply mult_n_O.
intros n H_rec.
simple induction b.
replace (p * 0) with 0.
intro.
apply (mult_eq_zero p (S n) H).
apply mult_n_O.
intros m H.
replace (p * S n) with (p * n + p).
replace (p * S m) with (p * m + p).
2: apply mult_n_Sm.
2: apply mult_n_Sm.
clear a; clear b.
intro.
elim (H_rec m); auto with arith.
apply (fun a b : nat => plus_reg_l a b p).
elim (plus_comm (p * n) p).
elim (plus_comm (p * m) p); trivial with arith.
Qed.
Hint Resolve mult_reg_l.




Lemma mult_reg_l_bis : forall a b p : nat, 0 < p -> p * a = p * b -> a = b.
intros a b p H H1.
elim (mult_reg_l a b p); auto with arith.
intro; absurd (p = 0); auto with arith.
Qed.
Hint Immediate mult_reg_l_bis.



Lemma mult_eq_zero_bis : forall a b : nat, 0 < a -> a * b = 0 -> b = 0.
intros a b pos H.
elim (mult_eq_zero a b H); auto with arith.
intro h.
absurd (a = 0); auto with arith.
Qed. 
Hint Immediate mult_eq_zero_bis.



Lemma lt_nm_mult : forall n m : nat, 0 < n -> 0 < m -> 0 < n * m.
intros n m H1 H2.
elim H1; elim H2; simpl in |- *; auto with arith.
Qed.
Hint Resolve lt_nm_mult.
 


Lemma same_quotient_order :
 forall b q q' r r' : nat, r < b -> q < q' -> q * b + r < q' * b + r'.
intros.
apply lt_le_trans with (q * b + b).
apply plus_lt_compat_l.
try trivial with arith.
pattern b at 2 in |- *.
replace b with (1 * b).
elim mult_plus_distr_r.
apply le_trans with (q' * b).
elim (mult_comm b (q + 1)); elim (mult_comm b q').
apply le_mult_cst.
replace (q + 1) with (S q).
auto with arith.
elim plus_comm; simpl in |- *; auto with arith.
auto with arith.
simpl in |- *; auto with arith. 
Qed.
Hint Resolve same_quotient_order.

(************************************************************************)
