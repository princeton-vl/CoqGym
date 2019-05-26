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
(*                               Ensf_disj.v                                *)
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
Require Import Ensf_inclus.
Require Import Ensf_map.

(*									*)
(*  UNION DISJOINTE 							*)
(*    L'union disjointe de A et B est definie comme l'ensemble des 	*)
(*    des couples (x,zero) pour x dans A et (x,un) pour x dans B	*)
(*    Pour cela on definit 2 fonctions injgauche : x->(x,zero) et	*)
(*    injdroite : x->(x,un) et on fait l'union de (map injgauche A)	*)
(*    et de (map injdroite B).						*)
(*									*)

Definition injgauche (e : Elt) : Elt := couple e zero.

Definition injdroite (e : Elt) : Elt := couple e un.

Definition union_disj (e f : Ensf) : Ensf :=
  union (map injgauche e) (map injdroite f).


Lemma dans_map_injg :
 forall (e : Ensf) (x : Elt), dans x (map injgauche e) -> dans (first x) e.
intros.
cut (exists y : Elt, dans y e /\ x = injgauche y).
2: apply dans_map; auto.
intro Ht; elim Ht; clear Ht.
intros y Ht; elim Ht; clear Ht.
intros.  
unfold injgauche in H1.
replace (first x) with y; auto.
symmetry  in |- *.
replace y with (first (couple y zero)); auto.
apply (f_equal (A:=Elt) (B:=Elt)); auto.
Qed.

Lemma dans_map_injd :
 forall (e : Ensf) (x : Elt), dans x (map injdroite e) -> dans (first x) e.
intros.
cut (exists y : Elt, dans y e /\ x = injdroite y).
2: apply dans_map; auto.
intro Ht; elim Ht; clear Ht.
intros y Ht; elim Ht; clear Ht.
intros.  
unfold injdroite in H1.
replace (first x) with y; auto.
symmetry  in |- *.
replace y with (first (couple y un)); auto.
apply (f_equal (A:=Elt) (B:=Elt)); auto.
Qed.

Lemma absurd_injg_injd :
 forall (x : Elt) (e f : Ensf),
 dans x (map injgauche e) -> ~ dans x (map injdroite f).
intros.
cut (exists y : Elt, dans y e /\ x = injgauche y).
2: apply dans_map; auto.
intro Ht; elim Ht; clear Ht.
intros y Ht; elim Ht; clear Ht.
intros.  
red in |- *.
intro.
cut (exists y' : Elt, dans y' f /\ x = injdroite y' :>Elt).
2: apply dans_map; auto.
intro Ht; elim Ht; clear Ht.
intros y' Ht; elim Ht; clear Ht.
intros.  
absurd (zero = un :>Elt).
unfold zero in |- *.
unfold un in |- *.
discriminate.

unfold injdroite in H4.
unfold injgauche in H1.
replace zero with (second (couple y zero)); auto.
replace un with (second (couple y' un)); auto.
rewrite <- H4.
rewrite <- H1.
auto.
Qed.

(*									*)
(*  On montre ici que si x est dans l'union disjointe de A et B alors	*)
(*  x est soit de la forme (injgauche y) avec y dans A, soit de la 	*)
(*  forme (injdroite y) avec y dans B					*)
(*									*)

Lemma union_disj1 :
 forall (x : Elt) (a b : Ensf),
 dans x (union_disj a b) ->
 (exists y : Elt, dans y a /\ x = injgauche y :>Elt) \/
 (exists y : Elt, dans y b /\ x = injdroite y :>Elt).
unfold union_disj in |- *.
intros.
cut (dans x (map injgauche a) \/ dans x (map injdroite b)).
2: auto.
intro H0; elim H0; clear H0.
intro; left.
apply dans_map; auto.
intro; right.
apply dans_map; auto.
Qed.

Lemma union_disj_d :
 forall (x : Elt) (a b : Ensf),
 dans x b -> dans (injdroite x) (union_disj a b).
intros.
unfold union_disj in |- *.
apply union_d.
apply dans_map_inv.
auto.
Qed.

Lemma union_disj_g :
 forall (x : Elt) (a b : Ensf),
 dans x a -> dans (injgauche x) (union_disj a b).
intros.
unfold union_disj in |- *.
apply union_g.
apply dans_map_inv.
auto.
Qed.

Lemma inclus_union_disj :
 forall a b c d : Ensf,
 inclus a c -> inclus b d -> inclus (union_disj a b) (union_disj c d).
unfold inclus in |- *.
intros.
unfold union_disj in H1.
cut (dans x (map injgauche a) \/ dans x (map injdroite b)); auto.
intro Ht; elim Ht; clear Ht.

intro.
cut (exists y : Elt, dans y a /\ x = injgauche y).
2: apply dans_map; auto.
intro Ht; elim Ht; clear Ht.
intros y Ht; elim Ht; clear Ht; intros H3 H4.
cut (dans y c); auto.
intro.
unfold union_disj in |- *.
apply union_g.
rewrite H4.
apply dans_map_inv; auto.

intro.
cut (exists y : Elt, dans y b /\ x = injdroite y :>Elt).
2: apply dans_map; auto.
intro Ht; elim Ht; clear Ht.
intros y Ht; elim Ht; clear Ht; intros H3 H4.
cut (dans y d); auto.
intro.
unfold union_disj in |- *.
apply union_d.
rewrite H4.
apply dans_map_inv; auto.
Qed.

(* 									*)
(*  Resultats n'ayant rien a voir avec les ensembles finis mais n'ayant	*)
(*  pas de place dans un fichier particulier.				*)
(*									*)

Lemma pair_equal :
 forall (A B : Set) (x x' : A) (y y' : B),
 x = x' :>A -> y = y' :>B -> pair x y = pair x' y' :>A * B.
intros A B x x' y y' X Y.
rewrite X.
rewrite Y.
apply refl_equal.
Qed.
Hint Resolve pair_equal.