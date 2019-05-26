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
(*                                Ensf_map.v                                *)
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
Require Import Ensf_inclus.

(*									*)
(*  MAP "a la CAML"							*)
(*    On definit une fonction map qui applique une fonction a tous les  *)
(*    elements d'un ensemble et renvoie l'ensemble des resultats	*)
(*    Ceci permet, entre autres, de definir facilement l'union		*)
(*    disjointe (Voir ci-dessous)					*)
(*									*)
Fixpoint map (f : Elt -> Elt) (e : Ensf) {struct e} : Ensf :=
  match e with
  | empty => empty
  | add y e => add (f y) (map f e)
  end.

(*									*)
(*  On montre ici le resultat general suivant :				*)
(*    (dans  x (map f A)) -> il existe y dans A tel que x=f y		*)
(*									*)

Lemma dans_map :
 forall (f : Elt -> Elt) (a : Ensf) (x : Elt),
 dans x (map f a) -> exists y : Elt, dans y a /\ x = f y.
intros f.
simple induction a.
simpl in |- *.
intros x H.
absurd (dans x empty); auto.

intros a0 b H x.
simpl in |- *.
intro.
cut (f a0 = x :>Elt \/ dans x (map f b)).
2: apply dans_add; auto.
intro H1; elim H1; clear H1.
intro; exists a0; auto.
intro.
cut (exists y : Elt, dans y b /\ x = f y).
intro H2; elim H2; clear H2.
2: auto.
intros x0 H2; elim H2; clear H2.
intros.
exists x0.
split; auto.
Qed.
Hint Resolve dans_map.

Lemma dans_map_inv :
 forall (f : Elt -> Elt) (x : Elt) (a : Ensf),
 dans x a -> dans (f x) (map f a).
intros f x.
simple induction a.
intro.
apply (dans_empty_imp_P x); auto.

intros a0 b H.
simpl in |- *.
intro H1.
cut (a0 = x :>Elt \/ dans x b).
2: apply dans_add; auto.
intro H2; elim H2; clear H2.
intro.
rewrite H0; auto.
auto.
Qed.
Hint Resolve dans_map_inv.

Lemma map_union :
 forall (f : Elt -> Elt) (a b : Ensf),
 union (map f a) (map f b) = map f (union a b) :>Ensf.
intro f.
simple induction a; simpl in |- *; auto.
Qed.
Hint Resolve map_union.

Lemma dans_map_trans :
 forall (x : Elt) (f : Elt -> Elt) (a b : Ensf),
 dans x (map f a) -> inclus a b -> dans x (map f b).
intros.
cut (exists y : Elt, dans y a /\ x = f y :>Elt).
2: apply dans_map; auto. 
intro Ht; elim Ht; clear Ht.
intros y Ht; elim Ht; clear Ht.
intros.
cut (dans y b).
2: apply dans_trans with a; auto.
intro.
rewrite H2.
apply dans_map_inv; auto.
Qed.

Lemma map_egal :
 forall (f g : Elt -> Elt) (E : Ensf),
 (forall x : Elt, dans x E -> f x = g x :>Elt) -> map f E = map g E :>Ensf.
intros f g.
simple induction E; simpl in |- *; auto.
Qed.

Lemma map_inclus :
 forall (a b : Ensf) (f : Elt -> Elt),
 inclus a b -> inclus (map f a) (map f b).
unfold inclus in |- *.
intros.
cut (exists y : Elt, dans y a /\ x = f y :>Elt).
2: apply dans_map; auto.
intro Ht; elim Ht; clear Ht; intros y Ht; elim Ht; clear Ht; intros.
cut (dans y b); auto.
intro.
replace x with (f y); auto.
Qed.