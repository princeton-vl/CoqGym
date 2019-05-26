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
(*                               three_gap.v                                *)
(****************************************************************************)

(*********************************************************)
(*                 THE THREE GAP THER0EM                 *)
(*                                                       *)
(*********************************************************)

Require Export preuve2.
(*********************************************************)

Section gap.
Variable N n : nat.
Hypothesis alpha_irr : forall n p : Z, (alpha * IZR p)%R <> IZR n.
Hypothesis prop_alpha : (0 < alpha)%R /\ (alpha < 1)%R.
Hypothesis prop_N : forall N : nat, N >= 2.
Hypothesis Hn : 0 < n /\ n < N.

(*********)
Definition succes := after N n.

(*********)
Definition num1 := n + first N.
Definition num2 := n + first N - last N.
Definition num3 := n - last N.

(*********************************************************)
(*                 Theorem                               *)
(*********************************************************)

(**********)
Theorem three_gap : succes = num1 \/ succes = num2 \/ succes = num3.

generalize (inser2_trans_lt 0 n (last N) (N - first N) N Hn).
intro; elim H; intros.
elim a; intros y0; elim y0; intros.
left; apply (three_gap1 alpha_irr prop_alpha prop_N N n H0 H1).
right; left; apply (three_gap2 alpha_irr prop_alpha prop_N N n H0 H1).
elim b; intros.
right; right; apply (three_gap3 alpha_irr prop_alpha prop_N N n H0 H1).
Qed.

End gap.