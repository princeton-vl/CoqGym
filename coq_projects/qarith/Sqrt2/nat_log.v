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


Require Import ZArith.
Require Import Zlogarithm.

Fixpoint nat_log_inf (p : positive) : nat :=
  match p with
  | xH => 0 (* 1 *)
  | xO q => S (nat_log_inf q) (* 2n *)
  | xI q => S (nat_log_inf q) (* 2n+1 *)
  end.

Fixpoint nat_log_sup (p : positive) : nat :=
  match p with
  | xH => 0 (* 1 *)
  | xO n => S (nat_log_sup n) (* 2n *)
  | xI n => S (S (nat_log_inf n)) (* 2n+1 *)
  end.

Lemma log_inf_log_inf :
 forall p : positive, Z_of_nat (nat_log_inf p) = log_inf p.
simple induction p; auto.
intros; simpl (nat_log_inf (xI p0)) in |- *; simpl (log_inf (xI p0)) in |- *.
rewrite <- H; apply Znat.inj_S.
intros; simpl (nat_log_inf (xO p0)) in |- *; simpl (log_inf (xO p0)) in |- *.
rewrite <- H; apply Znat.inj_S.
Qed.

Lemma log_sup_log_sup :
 forall p : positive, Z_of_nat (nat_log_sup p) = log_sup p.
simple induction p; auto.
intros; simpl (nat_log_sup (xI p0)) in |- *; simpl (log_sup (xI p0)) in |- *.
rewrite <- log_inf_log_inf; do 2 rewrite Znat.inj_S; auto.
intros; simpl (nat_log_sup (xO p0)) in |- *; simpl (log_sup (xO p0)) in |- *.
rewrite <- H; apply Znat.inj_S.
Qed.
