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
(*           e-mail:{Solange. Coupet,Line. Jakubiec}@lim.univ-mrs.fr          *)
(*                                                                          *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              May 30th 1996                               *)
(*                                                                          *)
(****************************************************************************)
(*                            Lib_Div_Even_Odd.v                            *)
(****************************************************************************)
Require Export Lib_Mult.

(****************************** even/odd *********************************)

Inductive even (n : nat) : Prop :=
    even_intro : forall q : nat, n = 2 * q -> even n.

Inductive odd (n : nat) : Prop :=
    odd_intro : forall q : nat, n = 2 * q + 1 -> odd n.


(************************* quotients and divisors ***********************)

Lemma no_zero_div :
 forall n m : nat, 0 < n -> forall q : nat, n = m * q -> 0 < q.
simple induction q.
intro.
absurd (0 = n).
apply lt_O_neq; auto with arith.
rewrite (mult_n_O m); auto with arith.
auto with arith.
Qed.



Lemma lt_quotient2_n :
 forall n : nat, 0 < n -> forall q : nat, n = 2 * q -> q < n.
intros.
rewrite (plus_n_O q).
rewrite H0.
elim plus_mult.
apply plus_lt_compat_l.
apply (no_zero_div n 2 H q H0).
Qed. 
Hint Resolve lt_quotient2_n.



Lemma less_div : forall n a b : nat, 0 < n -> n = a * b -> b <= n.
intros.
rewrite H0.
elim (mult_O_le b a); auto with arith.
intro.
absurd (n = 0).
unfold not in |- *; intro.
elim (lt_irrefl n).
pattern n at 1 in |- *.
rewrite H2; auto with arith.
rewrite H0.
rewrite H1; auto with arith.
Qed.


(************************************************************************)

Lemma even_or_odd : forall n : nat, {even n} + {odd n}.
simple induction n.
left; apply (even_intro 0 0); auto with arith.
intros y hrec.
elim hrec.
intro eveny.
right; elim eveny.
intros q hy; apply (odd_intro (S y) q).
elim hy.
elim plus_n_Sm.
auto with arith.
intro oddy; left.
elim oddy.
intros q hy; apply (even_intro (S y) (S q)).
rewrite hy.
rewrite plus_n_Sm.
elim (mult_comm (S q) 2).
elim (mult_comm q 2).
elim plus_comm.
auto with arith.
Qed.



Lemma even_odd : forall a : nat, even a -> ~ odd a.
unfold not in |- *; intros.
elim H0; elim H.
intros k1 evena k2 odda.
apply (le_Sn_n 1).
apply (less_div 1 (k1 - k2) 2); auto with arith.
rewrite mult_comm.
replace (2 * (k1 - k2)) with (2 * k1 - 2 * k2).
elim evena.
rewrite odda.
auto with arith.
elim mult_comm.
replace (2 * k1) with (k1 * 2).
2: apply mult_comm.
replace (2 * k2) with (k2 * 2).
2: apply mult_comm.
(* Rewrite (mult_minus_distr k1 k2 (S(S O))). *)
elim (mult_comm 2 k1); elim (mult_comm 2 k2).
apply sym_equal; auto with arith.
Qed.



Lemma odd_even : forall a : nat, odd a -> ~ even a.
unfold not in |- *; intros.
apply (even_odd a H0).
auto with arith.
Qed.


(********************** S,pred,plus,odd and even ************************)

Lemma plus_even_even : forall a b : nat, even a -> even b -> even (a + b).
intros.
elim H0; elim H.
intros.
rewrite H2; rewrite H1.
elim (mult_plus_distr_left q q0 2).
apply (even_intro (2 * (q + q0)) (q + q0)).
auto with arith.
Qed.



Lemma S_odd_even : forall a : nat, odd a -> even (S a).
intros.
elim H; intros.
rewrite H0.
rewrite (plus_n_Sm (2 * q) 1).
apply (plus_even_even (2 * q) 2).
apply (even_intro (2 * q) q); auto with arith.
apply (even_intro 2 1).
auto with arith.
Qed.



Lemma pred_odd_even : forall a : nat, odd a -> even (pred a).
intros.
elim H; intros.
rewrite H0.
elim (plus_n_Sm (2 * q) 0).
elim (pred_Sn (2 * q + 0)).
elim (plus_n_O (2 * q)).
apply (even_intro (2 * q) q); auto with arith.
Qed.



Lemma plus_even_odd : forall a b : nat, even a -> odd b -> odd (a + b).
intros.
elim H0; elim H; intros.
rewrite H2; rewrite H1.
rewrite (plus_assoc (2 * q) (2 * q0) 1).
elim (mult_plus_distr_left q q0 2).
apply (odd_intro (2 * (q + q0) + 1) (q + q0)).
auto with arith.
Qed.
Hint Resolve plus_even_odd.



Lemma plus_odd_even : forall a b : nat, odd a -> even b -> odd (a + b).
intros.
rewrite plus_comm.
auto with arith.
Qed.



Lemma S_even_odd : forall a : nat, even a -> odd (S a).
intros.
elim H; intros.
rewrite H0.
apply (odd_intro (S (2 * q)) q).
elim (plus_n_Sm (2 * q) 0).
auto with arith.
Qed.



Lemma plus_odd_odd : forall a b : nat, odd a -> odd b -> even (a + b).
intros.
elim H0; elim H; intros.
rewrite H2; rewrite H1; intros.
rewrite (plus_comm (2 * q0) 1).
rewrite (plus_assoc (2 * q + 1) 1 (2 * q0)).
rewrite (plus_assoc_reverse (2 * q) 1 1).
apply (plus_even_even (2 * q + (1 + 1)) (2 * q0)).
apply (plus_even_even (2 * q) (1 + 1)).
apply (even_intro (2 * q) q); auto with arith.
apply (even_intro (1 + 1) 1); auto with arith.
apply (even_intro (2 * q0) q0); auto with arith.
Qed.


(************************** mult, even and odd ***************************)

Lemma mult_even : forall a b : nat, even a -> even (a * b).
intros.
elim H.
intros.
apply (even_intro (a * b) (q * b)).
rewrite H0.
auto with arith.
Qed.



Lemma mult_odd_odd : forall a b : nat, odd a -> odd b -> odd (a * b).
intros.
elim H0; intros.
elim H; intros.
clear H0; clear H.
rewrite H2; rewrite H1.
rewrite (mult_plus_distr_r (2 * q0) 1 (2 * q + 1)).
apply (plus_even_odd (2 * q0 * (2 * q + 1)) (1 * (2 * q + 1))).
apply (mult_even (2 * q0) (2 * q + 1)).
apply (even_intro (2 * q0) q0); auto with arith.
apply (odd_intro (1 * (2 * q + 1)) q); auto with arith.
Qed.


(************************** div, even and odd ****************************)

Definition div (d a : nat) := exists k : nat, a = d * k.


(*************************************************************************)

Lemma div_odd_even : forall n d : nat, div d (2 * n) -> odd d -> div d n.
intros.
elim H.
intros.
cut (even x).
intro.
elim H2.
intros q evenx.
unfold div in |- *.
exists q.
apply (mult_reg_l_bis n (d * q) 2).
auto with arith.
rewrite H1.
rewrite evenx.
elim (mult_assoc_reverse 2 d q).
rewrite (mult_comm 2 d).
auto with arith.
elim (even_or_odd x).
auto with arith.
intros.
absurd (even (d * x)).
apply odd_even.
apply mult_odd_odd; auto with arith.
cut (d * x = 2 * n); auto with arith.
intro.
apply (even_intro (d * x) n).
auto with arith.
Qed.



Lemma div_odd_odd : forall n : nat, odd n -> forall d : nat, div d n -> odd d.
intros n oddn d divdn.
elim divdn.
intros.
 elim (even_or_odd d); auto with arith.
intros evend.
absurd (even n).
apply odd_even; auto with arith.
rewrite H.
apply mult_even; auto with arith.
Qed.



Lemma div_plus : forall n m d : nat, div d n -> div d m -> div d (n + m).
intros n m d divdn divdm.
elim divdm; intros; elim divdn; intros.
rewrite H0; rewrite H.
elim mult_plus_distr_left.
unfold div in |- *.
exists (x0 + x); auto with arith.
Qed.
Hint Resolve div_plus.



Lemma div_minus : forall n m d : nat, div d n -> div d m -> div d (n - m).
intros n m d divdn divdm.
elim divdm; intros; elim divdn; intros.
rewrite H0; rewrite H. elim (mult_minus_distr_left x0 x d).
unfold div in |- *.
exists (x0 - x); auto with arith.
Qed.
Hint Resolve div_minus.


(************* Informative definitions of Even and Or ********************)

Inductive Even (n : nat) : Set :=
    Even_intro : forall q : nat, n = 2 * q -> Even n.

Inductive Odd (n : nat) : Set :=
    Odd_intro : forall q : nat, n = 2 * q + 1 -> Odd n.


(************************************************************************)

Lemma Even_or_Odd : forall n : nat, Even n + Odd n.
simple induction n.
left; apply (Even_intro 0 0); auto with arith.
intros y hrec.
elim hrec.
intro eveny.
right; elim eveny.
intros q hy; apply (Odd_intro (S y) q).
elim hy.
elim plus_n_Sm.
auto with arith.
intro oddy; left.
elim oddy.
intros q hy; apply (Even_intro (S y) (S q)).
rewrite hy.
rewrite plus_n_Sm.
elim (mult_comm (S q) 2).
elim (mult_comm q 2).
elim plus_comm.
auto with arith.
Qed.



Lemma Odd_odd : forall n : nat, Odd n -> odd n.
intros.
elim H.
intros.
apply (odd_intro n q e).
Qed.
Hint Resolve Odd_odd.


(************************************************************************)
