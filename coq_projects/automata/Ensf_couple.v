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
(*                              Ensf_couple.v                               *)
(****************************************************************************)
(*              Formal Language Theory                                      *)
(*                                                                          *)
(*              Judicael Courant - Jean-Christophe Filliatre                *)
(*                                                                          *)
(*              Developped in V5.8  June-July 1993                          *)
(*              Ported     to V5.10 October 1994                            *)
(****************************************************************************)


Require Import Ensf_types.

(*									*)
(*  first et second renvoient repsectivement le premier et le deuxieme 	*)
(*  element d'un couple.						*)
(*									*)
  
Definition first (x : Elt) : Elt :=
  match x return Elt with
  | natural n =>
      (* natural *)  zero
      (* couple  *) 
  | couple a b => a
      (* up      *) 
  | up e => zero
      (* word    *) 
  | word w => zero
  end.

Definition second (x : Elt) : Elt :=
  match x return Elt with
  | natural n =>
      (* natural *)  zero
      (* couple  *) 
  | couple a b => b
      (* up      *) 
  | up e => zero
      (* word    *) 
  | word w => zero
  end.

(* Grace a first et second on recupere facilement le lemme suivant : 	*)

Lemma equal_couple :
 forall x y z t : Elt,
 couple x y = couple z t :>Elt -> x = z :>Elt /\ y = t :>Elt.
intros x y z t H.
injection H; auto.
Qed.

Lemma couple_couple_inv1 :
 forall a b c d : Elt, couple a c = couple b d :>Elt -> a = b :>Elt.
intros a b c d H.
injection H; auto.
Qed.
 
Lemma couple_couple_inv2 :
 forall a b c d : Elt, couple a c = couple b d :>Elt -> c = d :>Elt.
intros a b c d H.
injection H; auto.
Qed.