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
(*                               Ensf_union.v                               *)
(****************************************************************************)
(*              Formal Language Theory                                      *)
(*                                                                          *)
(*              Judicael Courant - Jean-Christophe Filliatre                *)
(*                                                                          *)
(*              Developped in V5.8  June-July 1993                          *)
(*              Ported     to V5.10 October 1994                            *)
(****************************************************************************)


Require Import Ensf_types.
Require Import Ensf_dans.

(*									*)
(*  UNION :								*)
(*    On definit ici l'union de 2 ensembles. On remarquera qu'un 	*)
(*    peut apparaitre plusieurs fois dans un ensemble, et que c'est     *)
(*    pour cela que l'on utilise 					*)
(*      union E (add x F) -> add x (union E F)				*)
(*    directement.							*)
(*									*)

Fixpoint union (A : Ensf) : Ensf -> Ensf :=
  fun B : Ensf =>
  match A return Ensf with
  | empty =>
      (* empty *)  B
      (* add   *) 
  | add x e => add x (union e B)
  end.

Lemma union_a_empty : forall a : Ensf, a = union a empty :>Ensf.
simple induction a.
apply refl_equal.
intros a0 b H.
simpl in |- *; auto.
Qed.
Hint Resolve union_a_empty.


Lemma dans_union :
 forall (x : Elt) (a b : Ensf), dans x (union a b) -> dans x a \/ dans x b.
intros x.
simple induction a.
auto.

intros a0 b H b0.
simpl in |- *.
intro H0.
cut (a0 = x :>Elt \/ dans x (union b b0)).
2: apply dans_add; auto.
intro H1; elim H1.
intro; left.
rewrite H2; auto.
intro.
cut (dans x b \/ dans x b0); auto.
intro H3; elim H3; auto.
Qed.
Hint Resolve dans_union.


Lemma union_g : forall (x : Elt) (a b : Ensf), dans x a -> dans x (union a b).
intro x.
simple induction a.
intros.
apply (dans_empty_imp_P x); auto.
intros a0 b H b0.
simpl in |- *.
intro.
cut (a0 = x :>Elt \/ dans x b).
2: apply dans_add; auto.
intro H1; elim H1; clear H1.
intro H1.
rewrite H1; auto.
auto.
Qed.
Hint Resolve union_g.

Lemma union_d : forall (x : Elt) (a b : Ensf), dans x b -> dans x (union a b).
intro x.
simple induction a; simpl in |- *; auto.
Qed.
Hint Resolve union_d.


Lemma dans_union_inv :
 forall (x : Elt) (a b : Ensf), dans x a \/ dans x b -> dans x (union a b).
intros x a b H; elim H; auto.
Qed.