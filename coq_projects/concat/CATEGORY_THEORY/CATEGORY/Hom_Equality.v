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


(*****************************************************************************)
(*          Projet Coq - Calculus of Inductive Constructions V5.10           *)
(*****************************************************************************)
(*                                                                           *)
(*          Category Theory : Hom Equality                                   *)
(*                                                                           *)
(*          Amokrane Saibi May 1994                                          *)
(*                                                                           *)
(*****************************************************************************)

Require Export Category.

Set Implicit Arguments.
Unset Strict Implicit.

Inductive Equal_hom (C : Category) (a b : C) (f : a --> b) :
forall c d : C, (c --> d) -> Prop :=
    Build_Equal_hom : forall g : a --> b, f =_S g -> Equal_hom f g. 

Hint Resolve Build_Equal_hom.

Infix "=_H" := Equal_hom (at level 70).

Section equal_hom_equiv.

Variables (C : Category) (a b : C) (f : a --> b).

Lemma Equal_hom_refl : f =_H f.
Proof.
apply Build_Equal_hom; apply Refl.
Qed.

Variables (c d : C) (g : c --> d).

Lemma Equal_hom_sym : f =_H g -> g =_H f.
Proof.
intros eqdep_fg.
elim eqdep_fg; intros h eq_fh.
apply Build_Equal_hom; apply Sym; assumption.
Qed.

Variables (i j : C) (h : i --> j).

Lemma Equal_hom_trans : f =_H g -> g =_H h -> f =_H h.
Proof.
intros eqdep_fg.
elim eqdep_fg; intros k eq_fk eqdep_kh.
elim eqdep_kh; intros l eq_kl.
apply Build_Equal_hom.
apply Trans with k; auto. 
Qed.

End equal_hom_equiv.

Hint Resolve Equal_hom_refl.
Hint Resolve Equal_hom_sym.


(* "set" of all morphisms of a category *)

Section arrs_setoid_def.

Variable C : Category.

Structure Arrs : Type :=  {Dom : C; Codom : C; Arrow : Dom --> Codom}.

Definition Equal_Arrs (f g : Arrs) := Arrow f =_H Arrow g.

Lemma Equal_Arrs_equiv : Equivalence Equal_Arrs.
Proof.
apply Build_Equivalence; [ trivial | apply Build_Partial_equivalence ];
 red in |- *; unfold Equal_Arrs in |- *.
intro x; auto.
intros f g h; exact (Equal_hom_trans (f:=Arrow f) (g:=Arrow g) (h:=Arrow h)).
intros f g; exact (Equal_hom_sym (f:=Arrow f) (g:=Arrow g)).
Qed.

(* Canonical Structure Arrs_setoid : Setoid := Equal_Arrs_equiv. *)

End arrs_setoid_def.