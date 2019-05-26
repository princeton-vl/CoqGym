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


(** * vecspaces_verybasic.v *)
Section MAIN.
Set Automatic Coercions Import.
Set Implicit Arguments.
Unset Strict Implicit.
From Algebra Require Export Field_facts.
Require Export equal_syntax.
Require Export more_syntax.
From Algebra Require Export Module_facts.

(** - The definition of a vectorspace, and some very easy lemma's.
 This file is basically the book's Section 1.2 *)

Section vecfielddef.

(** %\tocdef{vectorspace}% *)
Definition vectorspace (F : field) : Type := MODULE F.
Definition VECSP (F : field) : category :=
  full_subcat (fun V : vectorspace F => V:MODULE F).

End vecfielddef.


Section jargon.
Variable F : field.
Variable V : vectorspace F.
Definition carrier := module_carrier.
Definition scalar_mult (a : F) (x : V) : V := a mX x.
(** - Since scalar_mult is exactly the same as module_mult, ie mX, we will continue 
 to use that notation instead *)
Definition scalar_mult_comp :
  forall (x x' : F) (y y' : carrier V),
  x =' x' in _ -> y =' y' in _ -> x mX y =' x' mX y' in _ :=
  MODULE_comp (R:=F) (Mod:=V).
Definition one_acts_as_unit : forall x : carrier V, one mX x =' x in _ :=
  MODULE_unit_l (R:=F) (Mod:=V).
Definition quasi_associativity :
  forall (a b : F) (x : carrier V), (a rX b) mX x =' a mX b mX x in _ :=
  MODULE_assoc (R:=F) (Mod:=V).
Definition distributivity :
  forall (a : F) (x y : carrier V), a mX (x +' y) =' a mX x +' a mX y in _ :=
  MODULE_dist_l (R:=F) (Mod:=V).
Definition distributivity' :
  forall (a b : F) (x : carrier V), (a +' b) mX x =' a mX x +' b mX x in _ :=
  MODULE_dist_r (R:=F) (Mod:=V).
End jargon.



(* The following will be assumed throughout this file. These are defined
   outside all sections but the global one, lest we need state them 10 times *)
Variable F : field.
Variable V : vectorspace F.
Hint Unfold carrier module_carrier.
Hint Resolve scalar_mult_comp distributivity distributivity': algebra.



Section Lemmas1.
(** - %\intoc{\bf Proposition 1.1}%;
    the corollaries are immediate by construction/definition *)
Lemma vector_cancellation :
 forall x y z : V, x +' z =' y +' z in _ -> x =' y in _.
intros.
apply GROUP_reg_right with z; auto with algebra.
Qed.

(** - %\intoc{\bf Proposition 1.2}%, split into several separate lemmas *)
Lemma Zero_times_a_vector_gives_zero :
 forall v : V, (zero F) mX v =' (zero V) in _.
auto with algebra.
Qed.

Lemma a_scalar_times_zero_gives_zero :
 forall f : F, f mX (zero V) =' (zero V) in _.
auto with algebra.
Qed.
 
Section Lemmas1_2.

Lemma Mince_minus1 :
 forall (f : F) (v : V), (min f) mX v =' (min f mX v) in _.
auto with algebra.
Qed.
 
Lemma Mince_minus2 :
 forall (f : F) (v : V), (min f mX v) =' f mX (min v) in _.
auto with algebra.
Qed.
 
Lemma Mince_minus3 :
 forall (f : F) (v : V), (min f) mX v =' f mX (min v) in _.
intros.
apply Trans with (min f mX v); auto with algebra.
Qed.

Lemma vecspace_op_reg_l :
 forall (f : F) (v : V),
 ~ f =' (zero F) in _ -> f mX v =' (zero V) in _ -> v =' (zero V) in _.
intros.
apply Trans with (one mX v); auto with algebra.
apply Trans with ((field_inverse f rX f) mX v).
apply MODULE_comp; auto with algebra.
apply Sym; auto with algebra.
apply Trans with (field_inverse f mX f mX v); auto with algebra.
apply Trans with (field_inverse f mX (zero V)); auto with algebra.
Qed.


End Lemmas1_2.
End Lemmas1.

End MAIN.

Hint Resolve vector_cancellation Zero_times_a_vector_gives_zero
  a_scalar_times_zero_gives_zero Mince_minus1 Mince_minus2 Mince_minus3:
  algebra.
