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
(*                               Ensf_dans.v                                *)
(****************************************************************************)
(*              Formal Language Theory                                      *)
(*                                                                          *)
(*              Judicael Courant - Jean-Christophe Filliatre                *)
(*                                                                          *)
(*              Developped in V5.8  June-July 1993                          *)
(*              Ported     to V5.10 October 1994                            *)
(****************************************************************************)


Require Import Ensf_types.

(*                                                                    *)
(*  APPARTENANCE :                                                    *)
(*    On definit le predicat (dans x E) pour un element x et un       *)
(*    ensemble E.                                                     *)
(*                                                                    *)
 
Inductive dans : Elt -> Ensf -> Prop :=
  | dans_add1 : forall (x : Elt) (e : Ensf), dans x (add x e)
  | dans_add2 : forall (x y : Elt) (e : Ensf), dans x e -> dans x (add y e).
Hint Resolve dans_add1 dans_add2.
 
(*  Quelques resultats concernant l'appartenance...  *)
 
Lemma dans_add :
 forall (x y : Elt) (e : Ensf), dans x (add y e) -> y = x \/ dans x e.
intros x y e H.
simple inversion H.
left.
injection H1.
intros.
apply trans_equal with x0; [ auto | assumption ].

intro.
right.
injection H2.
intros.
rewrite <- H3.
rewrite <- H1.
assumption.
Qed. 
 
Lemma dans_add_contr :
 forall (x y : Elt) (e : Ensf), y <> x -> ~ dans x e -> ~ dans x (add y e).
intros; red in |- *; intro.
absurd (y = x \/ dans x e).
2: apply dans_add; auto.
red in |- *.
intro.
elim H2; auto.
Qed.
 
Lemma empty_empty : forall E : Elt, ~ dans E empty.
unfold not in |- *; intros E H.
simple inversion H; [ discriminate H1 | discriminate H2 ].
Qed.
Hint Resolve empty_empty.
 
Lemma dans_empty_imp_P : forall (x : Elt) (P : Prop), dans x empty -> P.
intros.
elimtype False.
cut (~ dans x empty); auto.
Qed.
 
Lemma singl2 : forall x : Elt, dans x (singleton x).
unfold singleton in |- *.
auto.
Qed.
Hint Resolve singl2.

Unset Structural Injection.

Lemma singl2_inv : forall x e : Elt, dans x (singleton e) -> x = e :>Elt.
unfold singleton in |- *.
intros x e H.
simple inversion H.
injection H1; intros.
rewrite <- H0; assumption.
injection H2; intros.
apply dans_empty_imp_P with x0.
rewrite <- H0; assumption.
Qed.
Hint Resolve singl2_inv.
