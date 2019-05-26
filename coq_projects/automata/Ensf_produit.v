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
(*                              Ensf_produit.v                              *)
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
Require Import Ensf_couple.

(*									*)
(*  PRODUIT CARTESIEN 							*)
(*    On definit ici le produit cartesien de 2 ensembles. Pour cela     *)
(*    on commence par definir (singleprod x E) qui est l'ensemble	*)
(*    des couples (x,y) pour y dans E, puis (prodcart E F) qui est	*)
(*    l'union des (singleprod x F) pour x dans E.			*)
(*									*)

(*
Fixpoint singleprod [x:Elt; A:Ensf] : Ensf :=
  (<Ensf>Case A of
        (* empty *) empty
        (* add   *) [y:Elt][e:Ensf] (add (couple x y) (singleprod x e)) 
  end ).
*)
Fixpoint singleprod (x : Elt) (A : Ensf) {struct A} : Ensf :=
  match A with
  | empty => empty
  | add y e => add (couple x y) (singleprod x e)
  end.

(*
Fixpoint prodcart [A:Ensf] : Ensf -> Ensf :=
  [B:Ensf]
  (<Ensf>Case A of
	(* empty *) empty
        (* add   *) [x:Elt][e:Ensf] (union (singleprod x B) (prodcart e B))
  end ).
*)
Fixpoint prodcart (A : Ensf) : Ensf -> Ensf :=
  fun B : Ensf =>
  match A with
  | empty => empty
  | add x e => union (singleprod x B) (prodcart e B)
  end.

(*  On montre en premier que si (x,y) est dans (singleprod x0 b) alors	*)
(*  on a x=x0 et y dans b						*)

Lemma dans_singleprod :
 forall (x y x0 : Elt) (b : Ensf),
 dans (couple x y) (singleprod x0 b) -> x = x0 :>Elt /\ dans y b.
intros x y x0.
simple induction b.
simpl in |- *.
intro.
apply (dans_empty_imp_P (couple x y)); auto.

intros a b0 H.
simpl in |- *.
intro.
cut (couple x0 a = couple x y :>Elt \/ dans (couple x y) (singleprod x0 b0)).
2: apply dans_add; auto.
intro H1; elim H1; clear H1.
intro H1.
injection H1; intros.
split; auto.
rewrite H2; auto.

intro.
cut (x = x0 :>Elt /\ dans y b0); auto.
intro H2; elim H2; clear H2.
intros.
split; auto.
Qed.

(*  On peut ensuite en deduire que si (x,y) est dans AxB alors 		*)
(*  x est dans A et y est dans B.					*)
 
Lemma coupl2 :
 forall (x y : Elt) (a b : Ensf),
 dans (couple x y) (prodcart a b) -> dans x a /\ dans y b.
intros x y.
simple induction a.
intro b.
simpl in |- *.
intro.
apply (dans_empty_imp_P (couple x y)); auto.

intros a0 b H b0.
simpl in |- *.
intro.
cut
 (dans (couple x y) (singleprod a0 b0) \/ dans (couple x y) (prodcart b b0)).
2: apply dans_union; auto.
intro H1; elim H1; clear H1.
intro H1.
cut (x = a0 :>Elt /\ dans y b0).
2: apply dans_singleprod; auto.
intro H2; elim H2; clear H2.
intros.
rewrite H2.
split; auto.
intro.
cut (dans x b /\ dans y b0); auto.
intro H2; elim H2; clear H2.
intros.
split; auto.
Qed.

(*  Plus facile : l'inverse...						*)

Lemma dans_single :
 forall (x y : Elt) (a : Ensf),
 dans y a -> dans (couple x y) (singleprod x a).
intros x y.
simple induction a.
intro.
apply (dans_empty_imp_P y); auto.
intros a0 b H H1.
cut (a0 = y :>Elt \/ dans y b).
2: apply dans_add; auto.
intro H2; elim H2; clear H2.
intro.
simpl in |- *.
rewrite H0; auto.
simpl in |- *; auto.
Qed.

Lemma coupl2_inv :
 forall (x y : Elt) (a b : Ensf),
 dans x a -> dans y b -> dans (couple x y) (prodcart a b).
intros x y.
simple induction a.
intros b H.
apply (dans_empty_imp_P x); auto.

intros a0 b H b0 H0.
cut (a0 = x :>Elt \/ dans x b).
2: apply dans_add; auto.
simpl in |- *.
intro H1; elim H1; clear H1.
intros H1 H2.
apply dans_union_inv.
left.
rewrite H1.
apply dans_single; auto.
intros H1 H2.
apply dans_union_inv.
right.
auto.
Qed.
Hint Resolve coupl2_inv.

(*  De meme on commence ici par monter que si x est dans		*)
(*  (singleprod x0 b) alors x est de la forme (x0,y) avec y dans b	*)

Lemma dans_singleprod2 :
 forall (x x0 : Elt) (b : Ensf),
 dans x (singleprod x0 b) -> exists y : Elt, x = couple x0 y /\ dans y b.
intros x x0.
simple induction b.
intro.
apply (dans_empty_imp_P x); auto.
intros a b0 H.
simpl in |- *.
intro.
cut (couple x0 a = x :>Elt \/ dans x (singleprod x0 b0)).
2: apply dans_add; auto.
intro H1; elim H1; clear H1.
intro.
exists a; auto.
intro.
cut (exists y : Elt, x = couple x0 y /\ dans y b0); auto.
intro H2; elim H2; clear H2.
intros.
exists x1.
elim H2; clear H2.
intros.
split; auto.
Qed.

(*  On peut ensuite en deduire que si x est dans AxB alors x est de la	*)
(*  forme (x1,x2) avec x1 dans A et x2 dans B.				*)

Lemma coupl3 :
 forall (a b : Ensf) (x : Elt),
 dans x (prodcart a b) ->
 exists x1 : Elt,
   (exists x2 : Elt, dans x1 a /\ dans x2 b /\ x = couple x1 x2).
simple induction a.
intro b.
simpl in |- *.
intros x H.
apply (dans_empty_imp_P x); auto.

intros a0 b H b0 x.
simpl in |- *.
intro.
cut (dans x (singleprod a0 b0) \/ dans x (prodcart b b0)); auto.
intro H1; elim H1; clear H1.
intro.
cut (exists y : Elt, x = couple a0 y /\ dans y b0).
2: apply dans_singleprod2; auto.
intro H2; elim H2; clear H2.
intros x0 H2.
exists a0.
exists x0.
elim H2; clear H2.
intros.
split; auto.
intro.
cut
 (exists x1 : Elt,
    (exists x2 : Elt, dans x1 b /\ dans x2 b0 /\ x = couple x1 x2));
 auto.
intro H2; elim H2; clear H2.
intros x0 H2; elim H2; clear H2.
intros x1 H2; elim H2; clear H2.
intros H2 H3; elim H3; clear H3.
intros H4 H5.
exists x0.
exists x1.
split; auto.
Qed.