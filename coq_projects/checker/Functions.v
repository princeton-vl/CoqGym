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
(*                               Functions.v                                *)
(****************************************************************************)

(* Basic Properties of functions over Set. G. Huet March 1996 *)

Section Mappings.
Variable X Y : Set.
Variable f : X -> Y.
Definition Injective := forall x x' : X, f x = f x' -> x = x'.
Definition Surjective := forall y : Y, exists x : X, y = f x.
End Mappings.

Notation One_one := (Injective _ _) (only parsing).
Notation Onto := (Surjective _ _) (only parsing).

Section Finiteness.
Variable X : Set.
Definition Finite := forall f : X -> X, Injective _ _ f -> Surjective _ _ f.
End Finiteness.

Section Composition.
Variable X Y Z : Set.
Variable f : X -> Y.
Variable g : Y -> Z.
Definition comp (x : X) := g (f x).
End Composition.

Notation "f 'o' g" := (comp _ _ _ f g) (at level 20, right associativity).

Hint Unfold Injective Surjective comp.

Section Preservation.
Variable X Y Z : Set.
Variable f : X -> Y.
Variable g : Y -> Z.

Lemma Injections_compose :
 Injective _ _ f -> Injective _ _ g -> Injective _ _ (f o g).
Proof.
auto.
Qed.

Lemma Surjections_right : Surjective _ _ (f o g) -> Surjective _ _ g.
Proof.
intro Sfg; red in |- *; intro z; elim (Sfg z).
intros x E; exists (f x); trivial.
Qed.

Lemma Surjections_compose :
 Surjective _ _ f -> Surjective _ _ g -> Surjective _ _ (f o g).
Proof.
unfold Surjective, comp in |- *; intros Sf Sg z.
elim (Sg z); intros y E; elim (Sf y); intros x E'.
exists x; rewrite E; rewrite E'; trivial.
Qed.

End Preservation.