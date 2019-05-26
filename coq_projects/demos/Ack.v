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


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              Nov 25th 1994                               *)
(*                                                                          *)
(****************************************************************************)
(*                                  Ack.v                                   *)
(****************************************************************************)


Inductive Ack : nat -> nat -> nat -> Prop :=
  | AckO : forall n : nat, Ack 0 n (S n)
  | AcknO : forall n p : nat, Ack n 1 p -> Ack (S n) 0 p
  | AckSS :
      forall n m p q : nat, Ack (S n) m q -> Ack n q p -> Ack (S n) (S m) p.

Hint Resolve AckO AcknO.

Goal forall n m : nat, {p : nat | Ack n m p}.
simple induction n.
intro m; exists (S m); auto.
simple induction m.
elim (H 1); intros.
exists x; auto.
intros m' H'; elim H'; intros.
elim (H x); intros.
exists x0.
apply AckSS with x; auto.
Save Ackermann.

(* Functional definition of Ackermann :
 (ack 0 n) = (S n)
 (ack (S n) 0) = (ack n (S 0))
 (ack (S n) (S m)) = (ack n (ack (S n) m)) *)
 
Definition ack (n : nat) :=
  (fix F (n0 : nat) : nat -> nat :=
     match n0 with
     | O => S
     | S n1 =>
         fun m : nat =>
         (fix F0 (n2 : nat) : nat :=
            match n2 with
            | O => F n1 1
            | S n3 => F n1 (F0 n3)
            end) m
     end) n. 
(* 0 *) 
(* (S n) *)  
(* 0 *) 
(* S m *) 

Goal forall n m p : nat, Ack n m p -> p = ack n m :>nat.
simple induction 1; simpl in |- *; trivial.
intros n1 m1 p1 q1 ASn Eq An Ep; elim Eq; elim Ep; trivial.
Save ack_Ack.

Goal forall n m : nat, Ack n m (ack n m).
simple induction n.
simpl in |- *; auto.
intros n' H; simple induction m.
simpl in |- *; auto.
intros m' H'; apply AckSS with (ack (S n') m'); auto.
apply (H (ack (S n') m')).
Save Ack_ack.
