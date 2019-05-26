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
(*                               prop_elem.v                                *)
(****************************************************************************)

(*********************************************************)
(*          Elementary properties first last             *)
(*                                                       *)
(*********************************************************)

Require Import Max.
Require Export tools.

Unset Standard Proposition Elimination Names.

(*********************************************************)

(**********)
Lemma first_N : forall N : nat, N >= 2 -> first N < N.
intros; unfold first in |- *; case (N_classic N); intro.
absurd (N >= 2).
elim s; intro y; rewrite y; unfold ge in |- *; auto with arith real.
exact H.
case (exist_first N g); intros; elim a; intros; elim H1; intros;
 auto with arith real.
Qed.

(**********)
Lemma last_N : forall N : nat, N >= 2 -> last N < N.
intros; unfold last in |- *; case (N_classic N); intro.
absurd (N >= 2).
elim s; intro y; rewrite y; unfold ge in |- *; auto with arith real.
exact H.
case (exist_last N g); intros; elim a; intros; elim H1; intros;
 auto with arith real.
Qed.

(**********)
Lemma inter1 : forall N : nat, N >= 2 -> max (first N) (last N) < N.
intros; apply max_case2. 
apply (first_N N H).
apply (last_N N H).
Qed.

(**********)
Lemma first_N01 : forall N : nat, first N <= N.
intros; unfold first in |- *; case (N_classic N); intro; auto with arith real.
case (exist_first N g); intros; elim a; intros; elim H0; intros;
 auto with arith real.
Qed.

(**********)
Lemma last_N01 : forall N : nat, last N <= N.
intros; unfold last in |- *; case (N_classic N); intro; auto with arith real.
case (exist_last N g); intros; elim a; intros; elim H0; intros;
 auto with arith real.
Qed.

(**********)
Lemma first_0 : forall N : nat, N >= 2 -> 0 < first N.
intros; unfold first in |- *; case (N_classic N); intro.
absurd (N >= 2).
elim s; intro y; rewrite y; unfold ge in |- *; auto with arith real.
exact H.
case (exist_first N g); intros; elim a; intros; auto with arith real.
Qed.

(**********)
Lemma last_0 : forall N : nat, N >= 2 -> 0 < last N.
intros; unfold last in |- *; case (N_classic N); intro.
absurd (N >= 2).
elim s; intro y; rewrite y; unfold ge in |- *; auto with arith real.
exact H.
case (exist_last N g); intros; elim a; intros; auto with arith real.
Qed.

(**********)
Lemma first_n :
 forall N n : nat,
 N >= 2 ->
 0 < n ->
 n < N ->
 (0 < alpha)%R /\ (alpha < 1)%R ->
 (frac_part_n_alpha (first N) <= frac_part_n_alpha n)%R.
intros; unfold first in |- *; case (N_classic N); intro.
absurd (N >= 2).
elim s; intro y; rewrite y; unfold ge in |- *; auto with arith real.
exact H.
case (exist_first N g); unfold ordre_total in |- *; intros; elim a; intros.
elim H4; intros.
generalize (H6 n); intros.
elim H7.
intro; apply Rlt_le; auto with arith real.
unfold Rle in |- *; auto with arith real.
split; auto with arith real.
auto with arith real.
Qed.

(**********)
Lemma last_n :
 forall N n : nat,
 N >= 2 ->
 0 < n ->
 n < N ->
 (0 < alpha)%R /\ (alpha < 1)%R ->
 (frac_part_n_alpha n <= frac_part_n_alpha (last N))%R.
intros; unfold last in |- *; case (N_classic N); intro.
absurd (N >= 2).
elim s; intro y; rewrite y; unfold ge in |- *; auto with arith real.
exact H.
case (exist_last N g); unfold ordre_total in |- *; intros; elim a; intros.
elim H4; intros.
generalize (H6 n); intros.
elim H7.
intro; apply Rlt_le; auto with arith real.
unfold Rle in |- *; auto with arith real.
split; auto with arith real.
auto with arith real.
Qed.

(**********)
Lemma tech_first_last :
 forall N k : nat,
 N >= 2 ->
 0 < k -> k < N -> ordre_total (first N) k /\ ordre_total k (last N).
intros; split; unfold ordre_total in |- *; intro.
apply (first_n N k H H0 H1 H2).
apply (last_n N k H H0 H1 H2).
Qed.

(**********)
Lemma le_first_last :
 forall N : nat, N >= 2 -> ordre_total (first N) (last N).
intros; unfold ordre_total in |- *; intro.
apply (first_n N (last N) H (last_0 N H) (last_N N H) H0).
Qed.

