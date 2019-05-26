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
(*                              Ensf_inclus.v                               *)
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
Require Import Ensf_union.
Require Import Ensf_produit.

(*									*)
(*  INCLUSION  								*)
(*    On definit le predicat (inclus E F) par (dans x E)->(dans x F).	*)
(*    On montre ensuite facilement les resultats suivants :		*)
(*    -- inclus empty A							*)
(*    -- inclus A A							*)
(*    -- (inclus a b)->(inclus c d)					*)
(*		->(inclus (prodcart a c) (prodcart b d)			*)
(*									*)

Definition inclus (A B : Ensf) : Prop := forall x : Elt, dans x A -> dans x B.

Hint Unfold inclus.

Lemma empty_inclus : forall x : Ensf, inclus empty x.
unfold inclus in |- *; intros.
absurd (dans x0 empty); auto.
Qed.
Hint Resolve empty_inclus.

Lemma refl_inclus : forall x : Ensf, inclus x x.
auto.
Qed.
Hint Resolve refl_inclus.

Lemma inclus_trans :
 forall a b c : Ensf, inclus a b -> inclus b c -> inclus a c.
auto.
Qed.

Lemma cart_inclus :
 forall a b c d : Ensf,
 inclus a b -> inclus c d -> inclus (prodcart a c) (prodcart b d).
unfold inclus in |- *.
intros.
cut
 (exists x1 : Elt,
    (exists x2 : Elt, dans x1 a /\ dans x2 c /\ x = couple x1 x2)).
2: apply coupl3; auto.
intro H2; elim H2; clear H2.
intros x1 H2; elim H2; clear H2.
intros x2 H2; elim H2; clear H2.
intros H2 H3; elim H3; clear H3.
intros H3 H4.
rewrite H4.
auto.
Qed.
Hint Resolve cart_inclus.

Lemma inclus_add :
 forall (a b : Ensf) (y : Elt), inclus a b -> inclus a (add y b).
auto.
Qed.
Hint Resolve inclus_add.

Lemma singl_inclus_add :
 forall (e : Elt) (a : Ensf), inclus (singleton e) (add e a).
unfold inclus in |- *.
intros e a x H.
cut (x = e); auto.
intro H0.
rewrite H0; auto.
Qed.
Hint Resolve singl_inclus_add.

Lemma inclus_singl :
 forall (e : Elt) (a : Ensf), inclus (singleton e) a -> dans e a.
auto.
Qed.


Lemma add_inclus :
 forall (x : Elt) (a b : Ensf), dans x b -> inclus a b -> inclus (add x a) b.
unfold inclus in |- *.
intros.
cut (x = x0 \/ dans x0 a).
2: apply dans_add; auto.
intro H2; elim H2; clear H2.
intro H2; rewrite <- H2; auto.
auto.
Qed.
Hint Resolve add_inclus.

Lemma dans_trans :
 forall (x : Elt) (a b : Ensf), dans x a -> inclus a b -> dans x b.
auto.
Qed.

Lemma union_inclus :
 forall a b c : Ensf, inclus a c -> inclus b c -> inclus (union a b) c.
unfold inclus in |- *.
intros.
cut (dans x a \/ dans x b); auto.
intro H2; elim H2; auto.
Qed.
Hint Resolve union_inclus.

Lemma inclus_g : forall a b : Ensf, inclus a (union a b).
auto.
Qed.

Lemma inclus_d : forall a b : Ensf, inclus b (union a b).
auto.
Qed.

Lemma inclus_g2 : forall A B C : Ensf, inclus A B -> inclus A (union B C).
auto.
Qed.
Hint Resolve inclus_g2.

Lemma inclus_d2 : forall A B C : Ensf, inclus A C -> inclus A (union B C).
auto.
Qed.
Hint Resolve inclus_d2.
