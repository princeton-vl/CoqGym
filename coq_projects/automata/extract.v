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
(*                                extract.v                                 *)
(****************************************************************************)
(*              Formal Language Theory                                      *)
(*                                                                          *)
(*              Judicael Courant - Jean-Christophe Filliatre                *)
(*                                                                          *)
(*              Developped in V5.8  June-July 1993                          *)
(*              Ported     to V5.10 October 1994                            *)
(****************************************************************************)


Require Import Ensf.
Require Import more_words.
Require Import PushdownAutomata.
Require Import gram.
Require Import gram_aut.

Section def_axiom_APD.

Variable X P : Ensf.
Variable wd : Word.
Variable wa : Word.
Variable d : Ensf.
Let L := LA X wd wa d.

Axiom axiom_APD : P_automata X P wd wa d -> forall u : Word, {L u} + {~ L u}.

End def_axiom_APD.


Section parser.

Variable X V R : Ensf.
Variable S' : Elt.
Hypothesis H : isGram X V R S'.
Let LL := LG X V R S'.

Let P := union X V.

Let f_R_d (a : Elt) :=
  couple (word (cons (first a) nil)) (couple (eps X) (second a)).

Let f_X_d (x : Elt) := couple (word (cons x nil)) (couple x (word nil)).

Let d := union (map f_R_d R) (map f_X_d X).

Let wd := cons S' nil.

Let wa := nil.

Let L := LA X wd wa d.

Theorem Parser1 : forall u : Word, {LL u} + {~ LL u}.
intros.
elimtype ({L u} + {~ L u}).

intro Hyp.
left.
cut (l_egal L LL).
intro temp; elim temp.
unfold l_inclus in |- *.
intros.
auto.
unfold L, LL, wa, wd, d, f_R_d, f_X_d in |- *.
apply equiv_APD_Gram.
exact H.

unfold not in |- *.
intro Hyp.
right.
intro LL_u.
apply Hyp.
cut (l_egal L LL).
intro temp; elim temp.
unfold l_inclus in |- *.
intros.
auto.
unfold L, LL, wa, wd, d, f_R_d, f_X_d in |- *.
apply equiv_APD_Gram.
exact H.

unfold L in |- *.
apply axiom_APD with P.
unfold P, wd, wa, d, f_R_d, f_X_d in |- *.
apply X_P_wd_wa_d.
exact H.
Qed.

End parser.