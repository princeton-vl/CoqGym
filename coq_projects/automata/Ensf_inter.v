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
(*                               Ensf_inter.v                               *)
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
(*  INTERSECTION 							*)
(*   L'intersection de 2 ensembles est definie comme un predicat sur    *)
(*   3 ensembles A B C en disant que C est l'intresection de A et B     *)
(*   si C est le plus grand ensemble inclus dans A et dans B		*)
(*									*)

Definition inter (A B C : Ensf) : Prop :=
  inclus C A /\
  inclus C B /\ (forall x : Elt, dans x A -> dans x B -> dans x C).


Lemma union_inter :
 forall a b c : Ensf,
 inter a b empty -> inter a c empty -> inter a (union b c) empty.
unfold inter in |- *.
intros.
elim H0; clear H0.
intros H0 H1; elim H1; clear H1; intros H1 H2.
elim H; clear H.
intros H3 H4; elim H4; clear H4; intros H4 H5.
split; auto.
split.
apply empty_inclus.
intros.
cut (dans x b \/ dans x c); auto.
intro H7; elim H7; auto.
Qed.

Lemma inter_union :
 forall A B C : Ensf,
 inter A C empty -> inter B C empty -> inter (union A B) C empty.
unfold inter in |- *.
intros.
elim H0; clear H0.
intros H0 H1; elim H1; clear H1; intros H1 H2.
elim H; clear H.
intros H3 H4; elim H4; clear H4; intros H4 H5.
split; auto.
split; auto.
intros.
cut (dans x A \/ dans x B); auto.
intro H7; elim H7; auto.
Qed.

Lemma inter_dans :
 forall (A B : Ensf) (x : Elt), inter A B empty -> dans x A -> ~ dans x B.
unfold inter in |- *.
intros.
elim H; clear H; intros H Ht; elim Ht; clear Ht; intros H1 H2.
red in |- *; intro.
cut (dans x empty); auto.
intro.
apply dans_empty_imp_P with x; auto.
Qed.

Lemma sym_inter : forall A B C : Ensf, inter A B C -> inter B A C.
unfold inter in |- *.
intros.
elim H; clear H; intros H Ht; elim Ht; clear Ht; intros H0 H1.
auto.
Qed.