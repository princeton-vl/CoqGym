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


(****************************************************************************)
(*                                                                          *)
(*  Proof of the three gap theorem.                                         *)
(*                                                                          *)
(*  Micaela Mayero (INRIA-Rocquencourt)                                     *)
(*  September 1998                                                          *)
(*                                                                          *)
(****************************************************************************)
(****************************************************************************)
(*                               Nat_compl.v                                *)
(****************************************************************************)

(*********************************************************)
(*             Complements for the natural numbers       *)
(*                                                       *)
(*********************************************************)

Global Set Asymmetric Patterns.

Require Export Arith.
Require Export Compare_dec.
Require Import Omega.
Require Import Classical.

(*********************************************************)

Definition decidable (P : Prop) := P \/ ~ P.

(**********************************************************) 
(*       Technical lemmas                                 *)
(**********************************************************)

(**********)
Lemma not_symt_et :
 forall P Q R S : Prop, ~ (P /\ Q /\ R /\ S) -> ~ ((P /\ Q) /\ R /\ S).
tauto.
Qed.

(**********)
Lemma tech_not_exist_pt :
 forall P Q R S : nat -> Prop,
 ((exists k : nat, P k /\ Q k /\ R k /\ S k) -> False) ->
 forall k : nat, P k -> Q k -> ~ R k \/ ~ S k.
intros;
 generalize (not_ex_all_not nat (fun n : nat => P n /\ Q n /\ R n /\ S n) H);
 intro; generalize (not_symt_et (P k) (Q k) (R k) (S k) (H2 k)); 
 intro; generalize (not_and_or (P k /\ Q k) (R k /\ S k) H3); 
 intro; generalize (or_to_imply (P k /\ Q k) (~ (R k /\ S k)) H4); 
 intro; cut (P k /\ Q k); auto with core arith.
 intro; generalize (H5 H6); intro; apply (not_and_or (R k) (S k) H7).
Qed.

(**********)
Lemma contraposee_ou :
 forall P Q R : Prop, (P \/ Q -> R) -> ~ R -> ~ P /\ ~ Q.
tauto.
Qed.

(**********)
Lemma princip_min :
 forall P : nat -> Prop,
 (forall n : nat, decidable (P n)) ->
 forall n : nat,
 P n -> exists m : nat, P m /\ (forall i : nat, P i -> i >= m).
intros;
 cut
  ((exists m : nat, P m /\ (forall i : nat, P i -> i >= m)) \/
   (forall p : nat, n >= p -> ~ P p)).
intro; elim H1; auto with core arith.
intro; generalize (H2 n (le_n n)); intros; absurd (P n); auto with core arith.
elim n.
elim (H 0); intros.
left; exists 0; auto with core arith.
right; unfold ge in |- *; intros; cut (p = 0).
intro; rewrite H3; auto with core arith.
auto with core arith.
intros; elim H1; auto with core arith.
intro; elim (H (S n0)); intro.
left; exists (S n0); split; auto with core arith.
cut (forall p : nat, S n0 <= p \/ p < S n0).
intros; elim (H4 i); auto with core arith.
unfold lt in |- *; intro; generalize (le_S_n i n0 H6); intro; unfold ge in H2;
 elim (H2 i H7); auto with core arith.
intro; apply le_or_lt.
right; intros; cut (p < S n0 \/ p = S n0).
intro; elim H5; intro.
generalize (lt_n_Sm_le p n0 H6).
intro; unfold ge in H2; generalize (H2 p H7); auto with core arith.
rewrite H6; auto with core arith.
apply (le_lt_or_eq p (S n0) H4).
Qed.

(**********)
Lemma inser_trans :
 forall n m p q : nat,
 n <= m /\ m < p -> {n <= m /\ m < q} + {q <= m /\ m < p}.
intros; cut ({q <= m} + {m < q}).
intro; elim H; intros.
elim H0; intro.
right; auto with core arith.
left; auto with core arith.
apply (le_lt_dec q m).
Qed.

(**********)
Lemma inser_trans_lt :
 forall n m p q : nat, n < m /\ m < p -> {n < m /\ m < q} + {q <= m /\ m < p}.
intros; cut ({q <= m} + {m < q}).
intro; elim H; intros.
elim H0; intro.
right; auto with core arith.
left; auto with core arith.
apply (le_lt_dec q m).
Qed.

(**********)
Lemma inser2_trans :
 forall n m p q t : nat,
 n <= m /\ m < t -> {n <= m /\ m < q} + {q <= m /\ m < p} + {p <= m /\ m < t}. 
intros; cut ({n <= m /\ m < p} + {p <= m /\ m < t}).
intro; elim H0; intro y.
left; apply (inser_trans n m p q y).
right; auto with core arith.
apply (inser_trans n m t p H).
Qed.

(**********)
Lemma inser2_trans_lt :
 forall n m p q t : nat,
 n < m /\ m < t -> {n < m /\ m < q} + {q <= m /\ m < p} + {p <= m /\ m < t}. 
intros; cut ({n < m /\ m < p} + {p <= m /\ m < t}).
intro; elim H0; intro y.
left; apply (inser_trans_lt n m p q y).
right; auto with core arith.
apply (inser_trans_lt n m t p H).
Qed.

(**********)
Lemma eq_le : forall n m : nat, n = m -> n <= m.
intros; omega.
Qed.

(**********)
Lemma en_plus : forall a : nat, a + 0 = a.
intro; omega.
Qed.

(**********)
Lemma lt_plus_minus : forall n m p : nat, m < n -> n < m + p -> n - m < p.
intros; omega.
Qed.

(**********)
Lemma le_plus_min : forall n m p : nat, n <= m + p -> n - m <= p.
intros; omega.
Qed.

(**********)
Lemma lt_n_minus_plus : forall n m p : nat, n < m - p -> n + p < m.
intros; omega.
Qed.

(**********)
Lemma lt_plus : forall n m : nat, 0 < m -> n < n + m.
intros; omega.
Qed.

(**********)
Lemma lt_minus1 : forall n m : nat, n < m -> n - m = 0.
intros; omega.
Qed.

(**********)
Lemma lt_minus2 : forall n m : nat, n < m -> 0 < m - n.
intros; omega.
Qed.

(**********)
Lemma lt_minus_not : forall n m : nat, n < m -> m - n <> 0.
intros; omega.
Qed.

(**********)
Lemma lt_O_plus : forall n m : nat, 0 < n -> 0 < n + m.
intros; omega.
Qed.

(**********)
Lemma lt_O_plus_eq : forall n m : nat, 0 < n -> n + m <> 0.
intros; omega.
Qed.

(**********)
Lemma lt_minus_p : forall n m p : nat, n < m -> n - p < m.
intros; omega.
Qed.

(**********)
Lemma contra_lt_minus_p : forall n m p : nat, n < m - p -> n < m.
intros; omega.
Qed.

(**********)
Lemma lt_not_eq : forall n m : nat, n < m -> n <> m.
intros; omega.
Qed.

(**********)
Lemma le_minus_plus : forall n m p : nat, n - m <= p -> n <= p + m.
intros; omega.
Qed.

(**********)
Lemma lt_minus_plus : forall n m p : nat, n - m < p -> n < p + m.
intros; omega.
Qed.

(**********)
Lemma not_gt_le : forall n m : nat, ~ n > m -> n <= m.
intros; omega.
Qed.

(**********)
Lemma tech_lt : forall n m p q : nat, n < m -> m - 1 + p < q -> n + p < q.
intros; omega.
Qed.

(**********)
Lemma lt_reg_minus : forall n m p : nat, n < m -> p <= n -> n - p < m - p.
intros; omega.
Qed.

(**********)
Lemma simpl_minus_plus :
 forall a b c : nat, b <= a -> a <= c -> a - b + (c - a) = c - b.
intros; omega.
Qed. 

(**********)
Lemma lt_0_le : forall a : nat, 0 < a -> 1 <= a.
intros; omega.
Qed. 

(**********)
Lemma arith_2_0 : forall n : nat, n >= 2 -> 0 < n.
intros; omega.
Qed.

(**********)
Lemma ge_trans : forall n m p : nat, n >= p -> p >= m -> n >= m.
intros; omega.
Qed.

(**********)
Lemma tech_inter31b :
 forall l n x m : nat, l < n -> n <= x -> x < m -> x - n + l < m.
intros; omega.
Qed.




