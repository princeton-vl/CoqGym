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


Require Import Arith.
Require Import Omega.

Section Ackermann.

Variable Ack : nat -> nat -> nat.

Axiom Ack0 : forall m : nat, Ack 0 m = S m.
Axiom Ack1 : forall n : nat, Ack (S n) 0 = Ack n 1.
Axiom Ack2 : forall n m : nat, Ack (S n) (S m) = Ack n (Ack (S n) m).

Hint Rewrite Ack0 Ack1 Ack2 : base0.

Lemma ResAck0 : Ack 3 2 = 29.
Proof.
  autorewrite with base0 using try reflexivity.
Qed.

End Ackermann.

Section McCarthy.

Variable g : nat -> nat -> nat.

Axiom g0 : forall m : nat, g 0 m = m.
Axiom g1 : forall n m : nat, n > 0 -> m > 100 -> g n m = g (pred n) (m - 10).
Axiom g2 : forall n m : nat, n > 0 -> m <= 100 -> g n m = g (S n) (m + 11).

Hint Rewrite g0 g1 g2 using omega : base1.

Lemma Resg0 : g 1 110 = 100.
Proof.
  autorewrite with base1 using reflexivity || simpl in |- *.
Qed.

Lemma Resg1 : g 1 95 = 91.
Proof.
  autorewrite with base1 using reflexivity || simpl in |- *.
Qed.

End McCarthy.
