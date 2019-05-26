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
(*                                 gram_g.v                                 *)
(****************************************************************************)
(*              Formal Language Theory                                      *)
(*                                                                          *)
(*              Judicael Courant - Jean-Christophe Filliatre                *)
(*                                                                          *)
(*              Developped in V5.8  June-July 1993                          *)
(*              Ported     to V5.10 October 1994                            *)
(****************************************************************************)

Require Import Ensf.
Require Import Words.
Require Import fonctions.
Require Import Relations.
Require Import gram.

Inductive Deriveg (X R : Ensf) : Word -> Word -> Prop :=
  | Deriveg1 :
      forall (u v : Word) (A : Elt),
      dans (couple A (word u)) R -> Deriveg X R (cons A v) (Append u v)
  | Deriveg2 :
      forall (u v : Word) (x : Elt),
      dans x X -> Deriveg X R u v -> Deriveg X R (cons x u) (cons x v).

Hint Resolve Deriveg1.
Hint Resolve Deriveg2.


Definition Derivegstar (X R : Ensf) := Rstar Word (Deriveg X R).

Lemma Deriveg_Derive :
 forall (X R : Ensf) (u v : Word), Deriveg X R u v -> Derive R u v.
intros X R u v Der_g.
elim Der_g.
intros.
apply Derive1; auto.
intros.
apply Derive2; auto.
Qed.

Lemma Derivegstar_Derivestar :
 forall (X R : Ensf) (u v : Word), Derivegstar X R u v -> Derivestar R u v.
unfold Derivegstar, Rstar, Derivestar in |- *.
intros X R x y Derivegstar_x_y.
pattern x, y in |- *.
apply Derivegstar_x_y.
intro. apply Rstar_reflexive.
intros u v w Der Der_star.
apply Rstar_R with v.
apply Deriveg_Derive with X; assumption.
assumption.
Qed.

 


Axiom
  Derivestar_Derivegstar :
    forall (X R : Ensf) (u v : Word), Derivestar R u v -> Derivegstar X R u v.

Hint Resolve Derivestar_Derivegstar.