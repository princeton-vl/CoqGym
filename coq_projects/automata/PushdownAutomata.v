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
(*                            PushdownAutomata.v                            *)
(****************************************************************************)
(*              Formal Language Theory                                      *)
(*                                                                          *)
(*              Judicael Courant - Jean-Christophe Filliatre                *)
(*                                                                          *)
(*              Developped in V5.8  June-July 1993                          *)
(*              Ported     to V5.10 October 1994                            *)
(****************************************************************************)


Require Import Ensf.
Require Import Max.
Require Import Words.
Require Import fonctions.
Require Import need.
Require Import Relations.

Section pushdown_automata.

Variable X P : Ensf.
Variable wd : Word.
Variable wa : Word.
Variable d : Ensf.

Definition eps := natural (sup X).

Lemma not_dans_X_eps : ~ dans eps X.
unfold eps in |- *.
apply sup_out.
Qed.



Definition Transition : Prop :=
  forall x : Elt,
  dans x d ->
  exists2 w1 : Word,
    inmonoid P w1 &
    (exists2 y : Elt,
       dans y (add eps X) &
       (exists2 w2 : Word,
          inmonoid P w2 & x = couple (word w1) (couple y (word w2)) :>Elt)).



Definition P_automata := inmonoid P wd /\ inmonoid P wa /\ Transition.

Lemma P_automata_1 : P_automata -> inmonoid P wd.
unfold P_automata in |- *.
intro temp; elim temp.
auto.
Qed.

Lemma P_automata_2 : P_automata -> Transition.
unfold P_automata in |- *.
intro temp; elim temp; clear temp.
intros H temp; elim temp; clear temp.
auto.
Qed.



Definition Conf := (Word * Word)%type.


Inductive Derive_P_A : Conf -> Conf -> Prop :=
  | Derive_cons :
      forall (w w1 w2 u : Word) (x : Elt),
      dans x X ->
      dans (couple (word w1) (couple x (word w2))) d ->
      Derive_P_A (pair (Append w1 w) (cons x u)) (pair (Append w2 w) u)
  | Derive_eps :
      forall w w1 w2 u : Word,
      dans (couple (word w1) (couple eps (word w2))) d ->
      Derive_P_A (pair (Append w1 w) u) (pair (Append w2 w) u).


Definition Derivestar_P_A := Rstar Conf Derive_P_A.


Definition LA (u : Word) :=
  Derivestar_P_A (pair wd u) (pair wa nil) /\ inmonoid X u.

Lemma LA_langage : islanguage X LA.
unfold LA, islanguage in |- *.
intros w temp; elim temp; clear temp; auto.
Qed.


End pushdown_automata.