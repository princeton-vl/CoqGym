(**
  This module defines the Abelian Group record type which can be
  used to represent abelian groups and provides a collection of
  axioms and theorems describing them.

  Copyright (C) 2018 Larry D. Lee Jr. <llee454@gmail.com>

  This program is free software: you can redistribute it and/or modify
  it under the terms of the GNU Lesser General Public License as
  published by the Free Software Foundation, either version 3 of the
  License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU Lesser General Public License for more details.

  You should have received a copy of the GNU Lesser General Public
  License along with this program. If not, see
  <https://www.gnu.org/licenses/>.
*)

Require Import Description.
Require Import base.
Require Import function.
Require Import monoid.
Require Import group.

Module Abelian_Group.

(**
  Accepts one argument: f, a binary function;
  and asserts that f is commutative.
*)
Definition is_comm (T : Type) (f : T -> T -> T)
  :  Prop
  := forall x y : T, f x y = f y x.

(** Represents algebraic abelian groups. *)
Structure Abelian_Group : Type := abelian_group {

  (** Represents the set of group elements. *)
  E : Set;

  (** Represents the identity element. *)
  E_0 : E;

  (** Represents the group operation. *)
  op : E -> E -> E;

  (** Asserts that the group operator is associative. *)
  op_is_assoc : Monoid.is_assoc E op;

  (** Asserts that the group operator is commutative. *)
  op_is_comm : is_comm E op;

  (** Asserts that E_0 is the left identity element. *)
  op_id_l : Monoid.is_id_l E op E_0;

  (**
    Asserts that every element has a left inverse.

    Strictly speaking, this axiom should be:

      forall x : E, exists y : E,
        Monoid.is_inv_l E op E_0 op_id x y

    which asserts and verifies that op y x equals
    the identity element. Technically, we haven't
    shown that E_0 is the identity element yet, so
    we're being a bit presumptuous defining inverses
    in this way. While we could prove op_id in this
    structure definition, we prefer not to to improve
    readability and instead use the form given below,
    which Monoid.is_inv_l reduces to anyway.
  *)
  op_inv_l_ex : forall x : E, exists y : E, op y x = E_0
}.

(** Enable implicit arguments for group properties. *)

Arguments E_0 {a}.

Arguments op {a} x y.

Arguments op_is_assoc {a} x y z.

Arguments op_is_comm {a} x y.

Arguments op_id_l {a} x.

Arguments op_inv_l_ex {a} x.

(** Define notations for group properties. *)

Notation "0" := E_0 : abelian_group_scope.

Notation "x + y" := (op x y) (at level 50, left associativity) : abelian_group_scope.

Notation "{+}" := op : abelian_group_scope.

Open Scope abelian_group_scope.

Section Theorems.

(**
  Represents an arbitrary abelian group.

  Note: we use Variable rather than Parameter
  to ensure that the following theorems are
  generalized w.r.t ag.
*)
Variable g : Abelian_Group.

(**
  Represents the set of group elements.

  Note: We use Let to define E as a 
  local abbreviation.
*)
Let E := E g.

(**
  Accepts one group element, x, and asserts
  that x is the left identity element.
*)
Definition op_is_id_l := Monoid.is_id_l E {+}.

(**
  Accepts one group element, x, and asserts
  that x is the right identity element.
*)
Definition op_is_id_r := Monoid.is_id_r E {+}.

(**
  Accepts one group element, x, and asserts
  that x is the identity element.
*)
Definition op_is_id := Monoid.is_id E {+}.

(**
  Proves that every left identity must also
  be a right identity.
*)
Theorem op_is_id_lr
  :  forall x : E, op_is_id_l x -> op_is_id_r x.
Proof
  fun x H y
    => H y
    || a = y @a by op_is_comm y x.

(**
  Proves that every left identity is an
  identity.
*)
Theorem op_is_id_lid
  : forall x : E, op_is_id_l x -> op_is_id x.
Proof
  fun x H
    => conj H (op_is_id_lr x H).

(** Proves that 0 is the right identity element. *)
Theorem op_id_r
  :  op_is_id_r 0.
Proof op_is_id_lr 0 op_id_l.

(** Proves that 0 is the identity element. *)
Theorem op_id
  :  op_is_id 0.
Proof conj op_id_l op_id_r.

(**
  Accepts two group elements, x and y, and
  asserts that y is x's left inverse.
*)
Definition op_is_inv_l := Monoid.is_inv_l E {+} 0 op_id.

(**
  Accepts two group elements, x and y, and
  asserts that y is x's right inverse.
*)
Definition op_is_inv_r := Monoid.is_inv_r E {+} 0 op_id.

(**
  Accepts two group elements, x and y, and
  asserts that y is x's inverse.
*)
Definition op_is_inv := Monoid.is_inv E {+} 0 op_id.

(** Proves that every element has a right inverse. *)
Theorem op_inv_r_ex
  :  forall x : E, exists y : E, op_is_inv_r x y.
Proof
  fun x
    => ex_ind
         (fun (y : E) (H : op_is_inv_l x y)
           => ex_intro
                (op_is_inv_r x)
                y
                (H || a = 0 @a by op_is_comm x y))
         (op_inv_l_ex x).

(**
  Represents the group structure formed by
  op over E.
*)
Definition op_group := Group.group E 0 {+} op_is_assoc op_id_l op_id_r op_inv_l_ex op_inv_r_ex.

(** Represents the monoid formed by op over E. *)
Definition op_monoid := Group.op_monoid op_group.

(**
  Accepts one argument, x, and asserts that
  x has a left inverse.
*)
Definition has_inv_l := Group.has_inv_l op_group.

(**
  Accepts one argument, x, and asserts that
  x has a right inverse.
*)
Definition has_inv_r := Group.has_inv_r op_group.

(**
  Accepts one argument, x, and asserts that
  x has an inverse.
*)
Definition has_inv := Group.has_inv op_group.

(** Proves that the left identity element is unique. *)
Theorem op_id_l_uniq
  :  forall x : E, Monoid.is_id_l E {+} x -> x = 0.
Proof Group.op_id_l_uniq op_group.

(** Proves that the right identity element is unique. *)
Theorem op_id_r_uniq
  :  forall x : E, Monoid.is_id_r E {+} x -> x = 0.
Proof Group.op_id_r_uniq op_group.

(** Proves that the identity element is unique. *)
Theorem op_id_uniq
  :  forall x : E, Monoid.is_id E {+} x -> x = 0.
Proof Group.op_id_uniq op_group.

(**
  Proves that for every group element, x,
  its left and right inverses are equal.
*)
Theorem op_inv_l_r_eq
  :  forall x y : E, op_is_inv_l x y -> forall z : E, op_is_inv_r x z -> y = z.
Proof Group.op_inv_l_r_eq op_group.

(**
  Proves that the inverse relation is
  symmetrical.
*)
Theorem op_inv_sym
  :  forall x y : E, op_is_inv x y <-> op_is_inv y x.
Proof Group.op_inv_sym op_group.

(**
  Proves that every group element has an
  inverse.
*)
Theorem op_inv_ex
  :  forall x : E, exists y : E, op_is_inv x y.
Proof Group.op_inv_ex op_group.

(** Proves the left introduction rule. *)
Theorem op_intro_l
  :  forall x y z : E, x = y -> z + x = z + y.
Proof Group.op_intro_l op_group.

(** Proves the right introduction rule. *)
Theorem op_intro_r
  :  forall x y z : E, x = y -> x + z = y + z.
Proof Group.op_intro_r op_group.

(** Proves the left cancellation rule. *)
Theorem op_cancel_l
  :   forall x y z : E, z + x = z + y -> x = y.
Proof Group.op_cancel_l op_group.

(** Proves the right cancellation rule. *)
Theorem op_cancel_r
  :   forall x y z : E, x + z = y + z -> x = y.
Proof Group.op_cancel_r op_group.

(**
  Proves that an element's left inverse
  is unique.
*)
Theorem op_inv_l_uniq
  :  forall x y z : E, op_is_inv_l x y -> op_is_inv_l x z -> z = y.
Proof Group.op_inv_l_uniq op_group.

(**
  Proves that an element's right inverse
  is unique.
*)
Theorem op_inv_r_uniq
  :  forall x y z : E, op_is_inv_r x y -> op_is_inv_r x z -> z = y.
Proof Group.op_inv_r_uniq op_group.

(** Proves that an element's inverse is unique. *)
Theorem op_inv_uniq
  :  forall x y z : E, op_is_inv x y -> op_is_inv x z -> z = y.
Proof Group.op_inv_uniq op_group.

(**
  Proves explicitly that every element has a
  unique inverse.
*)
Theorem op_inv_uniq_ex
  :  forall x : E, exists! y : E, op_is_inv x y.
Proof Group.op_inv_uniq_ex op_group.

(**
  Proves that the identity element is its own
  left inverse.
*)
Theorem op_inv_0_l
  :  op_is_inv_l 0 0.
Proof Group.op_inv_0_l op_group.

(**
  Proves that the identity element is its own
  right inverse.
*)
Theorem op_inv_0_r
  :  op_is_inv_r 0 0.
Proof Group.op_inv_0_r op_group.

(**
  Proves that the identity element is its own
  inverse.
*)
Theorem op_inv_0
  :  op_is_inv 0 0.
Proof Group.op_inv_0 op_group.

(**
  Proves that the identity element has a
  left inverse.
*)
Theorem op_has_inv_l_0
  :  has_inv_l 0.
Proof Group.op_has_inv_l_0 op_group.

(**
  Proves that the identity element has a
  right inverse.
*)
Theorem op_has_inv_r_0
  :  has_inv_r 0.
Proof Group.op_has_inv_r_0 op_group.

(**
  Proves that the identity element has an
  inverse.
*)
Theorem op_has_inv_0
  :  has_inv 0.
Proof Group.op_has_inv_0 op_group.

(**
  Proves that if an element's, x, inverse
  equals 0, x equals 0.
*)
Theorem op_inv_0_eq_0
  :  forall x : E, op_is_inv x 0 -> x = 0.
Proof Group.op_inv_0_eq_0 op_group.

(**
  Proves that 0 is the only element whose
  inverse is 0.
*)
Theorem op_inv_0_uniq
  :  unique (fun x => op_is_inv x 0) 0.
Proof Group.op_inv_0_uniq op_group.
 
(** Represents strongly-specified negation. *)
Definition op_neg_strong
  :  forall x : E, { y | op_is_inv x y }
  := Group.op_neg_strong op_group.

(** Represents negation. *)
Definition op_neg
  :  E -> E
  := Group.op_neg op_group.

Close Scope nat_scope.

Notation "{-}" := (op_neg) : abelian_group_scope.

Notation "- x" := (op_neg x) : abelian_group_scope.

(**
  Asserts that the negation returns the inverse
  of its argument.
*)
Theorem op_neg_def
  :  forall x : E, op_is_inv x (- x).
Proof Group.op_neg_def op_group.

(** Proves that negation is one-to-one *)
Theorem op_neg_inj
  :  is_injective E E op_neg.
Proof Group.op_neg_inj op_group.

(** Proves the cancellation property for negation. *)
Theorem op_cancel_neg
  :  forall x : E, op_neg (- x) = x.
Proof Group.op_cancel_neg op_group.

(** Proves that negation is onto *)
Theorem op_neg_onto
  :  is_onto E E op_neg.
Proof Group.op_neg_onto op_group.

(** Proves that negation is surjective *)
Theorem op_neg_bijective
  :  is_bijective E E op_neg.
Proof Group.op_neg_bijective op_group.

(** Proves that neg x = y -> neg y = x *)
Theorem op_neg_rev
  :  forall x y : E, - x = y -> - y = x.
Proof Group.op_neg_rev op_group.

(**
  Proves that the left inverse of x + y is -y + -x.
*)
Theorem op_neg_distrib_inv_l
  :  forall x y : E, op_is_inv_l (x + y) (- y + - x).
Proof Group.op_neg_distrib_inv_l op_group.

(**
  Proves that the right inverse of x + y is -y + -x.
*)
Theorem op_neg_distrib_inv_r
  :  forall x y : E, op_is_inv_r (x + y) (- y + - x).
Proof Group.op_neg_distrib_inv_r op_group.

(**
  Proves that the inverse of x + y is -y + -x.
*)
Theorem op_neg_distrib_inv
  :  forall x y : E, op_is_inv (x + y) (- y + - x).
Proof Group.op_neg_distrib_inv op_group.

(**
  Proves that negation is distributive: i.e.
  -(x + y) = -y + -x.
*)
Theorem op_neg_distrib
  :  forall x y : E, - (x + y) = - y + - x.
Proof Group.op_neg_distrib op_group.

End Theorems.

End Abelian_Group.

Notation "0" := (Abelian_Group.E_0) : abelian_group_scope.

Notation "x + y" := (Abelian_Group.op x y) (at level 50, left associativity) : abelian_group_scope.

Notation "{+}" := (Abelian_Group.op) : abelian_group_scope.

Notation "{-}" := (Abelian_Group.op_neg _) : abelian_group_scope.

Notation "- x" := (Abelian_Group.op_neg _ x) : abelian_group_scope.
