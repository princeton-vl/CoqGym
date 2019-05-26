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
(*                                  Demo.v                                  *)
(****************************************************************************)

(* A short demo of coq *)

Fixpoint Plus (n : nat) : nat -> nat :=
  fun m : nat => match n with
                 | O => m
                 | S p => S (Plus p m)
                 end.

(**********************************************)
(***      A few elementary properties       ***)
(**********************************************)

Goal forall n : nat, n = Plus n 0.
simple induction n; simpl in |- *; auto with core.
Save Plus_n_O.
Hint Resolve Plus_n_O.

Goal forall m n : nat, S (Plus m n) = Plus m (S n).
simple induction m; simpl in |- *; auto with core.
Save Plus_S.
Hint Resolve Plus_S.

Goal forall n m : nat, Plus n m = Plus m n.
simple induction m; simpl in |- *; auto with core.
simple induction 1; auto with core.
Save Plus_com.
Hint Immediate Plus_com.

Goal forall n m p : nat, Plus n m = Plus n p -> m = p :>nat.
simple induction n; simpl in |- *; auto with core.
Save Plus_simpl.

Goal forall n m p : nat, Plus n (Plus m p) = Plus (Plus n m) p.
simple induction n; simpl in |- *; auto with core.
Save Plus_assoc.
Hint Resolve Plus_assoc.

Goal forall n m p : nat, Plus (Plus n m) p = Plus n (Plus m p).
auto with core.
Save assoc_Plus.


(************************************)
(***         Trees                ***)
(************************************)

Inductive tree : Set :=
  | tip : tree
  | node : tree -> tree -> tree.  

Fixpoint size (t : tree) : nat :=
  match t return nat with
  | tip => 1
  | node u v => Plus (size u) (size v)
  end.

Goal
forall t u v : tree, size (node t (node u v)) = size (node (node t u) v).
simpl in |- *; auto with core.
Save size_assoc.