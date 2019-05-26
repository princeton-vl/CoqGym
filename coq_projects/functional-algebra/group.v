(**
  This module defines the Group record type which can be used to
  represent algebraic groups and provides a collection of theorems
  and axioms describing them.

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

Require Import ProofIrrelevance.
Require Import Description.
Require Import base.
Require Import function.
Require Import monoid.

Module Group.

(** Represents algebraic groups. *)
Structure Group : Type := group {

  (** Represents the set of group elements. *)
  E: Set;

  (** Represents the identity element. *)
  E_0: E;

  (** Represents the group operation. *)
  op: E -> E -> E;

  (** Asserts that the group operator is associative. *)
  op_is_assoc : Monoid.is_assoc E op;

  (** Asserts that E_0 is the left identity element. *)
  op_id_l : Monoid.is_id_l E op E_0;

  (** Asserts that E_0 is the right identity element. *)
  op_id_r : Monoid.is_id_r E op E_0;

  (**
    Asserts that every group element has a
    left inverse.
  *)
  op_inv_l_ex : forall x : E, exists y : E, Monoid.is_inv_l E op E_0 (conj op_id_l op_id_r) x y;

  (**
    Asserts that every group element has a
    right inverse.
  *)
  op_inv_r_ex : forall x : E, exists y : E, Monoid.is_inv_r E op E_0 (conj op_id_l op_id_r) x y
}.

(** Enable implicit arguments for group properties. *)

Arguments E_0 {g}.

Arguments op {g} x y.

Arguments op_is_assoc {g} x y z.

Arguments op_id_l {g} x.

Arguments op_id_r {g} x.

Arguments op_inv_l_ex {g} x.

Arguments op_inv_r_ex {g} x.

(** Define notations for group properties. *)

Notation "0" := E_0 : group_scope.

Notation "x + y" := (op x y) (at level 50, left associativity) : group_scope.

Notation "{+}" := op : group_scope.

Open Scope group_scope.

Section Theorems.

(**
  Represents an arbitrary group.

  Note: we use Variable rather than Parameter
  to ensure that the following theorems are
  generalized w.r.t g.
*)
Variable g : Group.

(** Represents the set of group elements. *)
Let E := E g.

(**
  Represents the monoid structure formed by
  op over E.
*)
Definition op_monoid := Monoid.monoid E 0 {+} op_is_assoc op_id_l op_id_r.

(**
  Accepts one group element, x, and asserts
  that x is the left identity element.
*)
Definition op_is_id_l := Monoid.op_is_id_l op_monoid.

(**
  Accepts one group element, x, and asserts
  that x is the right identity element.
*)
Definition op_is_id_r := Monoid.op_is_id_r op_monoid.

(**
  Accepts one group element, x, and asserts
  that x is the identity element.
*)
Definition op_is_id := Monoid.op_is_id op_monoid.

(** Proves that 0 is the identity element. *)
Theorem op_id
  :  op_is_id 0.
Proof Monoid.op_id op_monoid.

(**
  Accepts two group elements, x and y, and
  asserts that y is x's left inverse.
*)
Definition op_is_inv_l := Monoid.op_is_inv_l op_monoid.

(**
  Accepts two group elements, x and y, and
  asserts that y is x's right inverse.
*)
Definition op_is_inv_r := Monoid.op_is_inv_r op_monoid.

(** Proves that the left identity element is unique. *)
Theorem op_id_l_uniq
  :  forall x : E, (op_is_id_l x) -> x = 0.
Proof Monoid.op_id_l_uniq op_monoid.

(** Proves that the right identity element is unique. *)
Theorem op_id_r_uniq 
  :  forall x : E, (op_is_id_r x) -> x = 0.
Proof Monoid.op_id_r_uniq op_monoid.

(** Proves that the identity element is unique. *)
Theorem op_id_uniq
  :  forall x : E, (op_is_id x) -> x = 0.
Proof Monoid.op_id_uniq op_monoid.

(** Proves the left introduction rule. *)
Theorem op_intro_l
  :  forall x y z : E, x = y -> z + x = z + y.
Proof Monoid.op_intro_l op_monoid.

(** Proves the right introduction rule. *)
Theorem op_intro_r
  :  forall x y z : E, x = y -> x + z = y + z.
Proof Monoid.op_intro_r op_monoid.

(**
  Accepts two group elements, x and y, and
  asserts that y is x's inverse.
*)
Definition op_is_inv := Monoid.op_is_inv op_monoid.

(**
  Accepts one argument, x, and asserts that
  x has a left inverse.
*)
Definition has_inv_l := Monoid.has_inv_l op_monoid.

(**
  Accepts one argument, x, and asserts that
  x has a right inverse.
*)
Definition has_inv_r := Monoid.has_inv_r op_monoid.

(**
  Accepts one argument, x, and asserts that
  x has an inverse.
*)
Definition has_inv := Monoid.has_inv op_monoid.

(**
  Proves that for every group element, x,
  its left and right inverses are equal.
*)
Theorem op_inv_l_r_eq
  :  forall x y : E, op_is_inv_l x y -> forall z : E, op_is_inv_r x z -> y = z.
Proof Monoid.op_inv_l_r_eq op_monoid.

(**
  Proves that the inverse relation is
  symmetrical.
*)
Theorem op_inv_sym
  :  forall x y : E, op_is_inv x y <-> op_is_inv y x.
Proof Monoid.op_inv_sym op_monoid.

(**
  Proves that every group element has an
  inverse.
*)
Theorem op_inv_ex
  :  forall x : E, exists y : E, op_is_inv x y.
Proof
  fun x : E
    => ex_ind
            (fun y H
              => ex_ind
                   (fun z H0
                     => let H1
                          :  op_is_inv_r x y
                          :=  H0
                          || op_is_inv_r x a @a
                             by op_inv_l_r_eq x y H z H0 in
                        ex_intro
                          (fun a => op_is_inv x a)
                          y
                          (conj H H1))
                   (op_inv_r_ex x))
            (op_inv_l_ex x).

(** Proves the left cancellation rule. *)
Theorem op_cancel_l
  :  forall x y z : E, z + x = z + y -> x = y.
Proof
  fun x y z H 
    => Monoid.op_cancel_l op_monoid x y z (op_inv_l_ex z) H.

(** Proves the right cancellation rule. *)
Theorem op_cancel_r
  :  forall x y z : E, x + z = y + z -> x = y.
Proof
  fun x y z
    => Monoid.op_cancel_r op_monoid x y z (op_inv_r_ex z).

(**
  Proves that an element's left inverse
  is unique.
*)
Theorem op_inv_l_uniq
  :  forall x y z : E, op_is_inv_l x y -> op_is_inv_l x z -> z = y.
Proof
  fun x
    => Monoid.op_inv_l_uniq op_monoid x (op_inv_r_ex x).

(**
  Proves that an element's right inverse
  is unique.
*)
Theorem op_inv_r_uniq
  :  forall x y z : E, op_is_inv_r x y -> op_is_inv_r x z -> z = y.
Proof
  fun x
    => Monoid.op_inv_r_uniq op_monoid x (op_inv_l_ex x).

(** Proves that an element's inverse is unique. *)
Theorem op_inv_uniq
  :  forall x y z : E, op_is_inv x y -> op_is_inv x z -> z = y.
Proof Monoid.op_inv_uniq op_monoid.

(**
  Proves explicitly that every element has a
  unique inverse.
*)
Theorem op_inv_uniq_ex
  :  forall x : E, exists! y : E, op_is_inv x y.
Proof
  fun x
    => ex_ind
            (fun y (H : op_is_inv x y)
              => ex_intro 
                   (fun y => op_is_inv x y /\ forall z, op_is_inv x z -> y = z)
                   y
                   (conj H (fun z H0 => eq_sym (op_inv_uniq x y z H H0))))
            (op_inv_ex x).

(**
  Proves that the identity element is its own
  left inverse.
*)
Theorem op_inv_0_l
  :  op_is_inv_l 0 0.
Proof Monoid.op_inv_0_l op_monoid.

(**
  Proves that the identity element is its own
  right inverse.
*)
Theorem op_inv_0_r
  :  op_is_inv_r 0 0.
Proof Monoid.op_inv_0_r op_monoid.

(**
  Proves that the identity element is its own
  inverse.
*)
Theorem op_inv_0
  :  op_is_inv 0 0.
Proof Monoid.op_inv_0 op_monoid.

(**
  Proves that the identity element has a
  left inverse.
*)
Theorem op_has_inv_l_0
  :  has_inv_l 0.
Proof Monoid.op_has_inv_l_0 op_monoid.

(**
  Proves that the identity element has a
  right inverse.
*)
Theorem op_has_inv_r_0
  :  has_inv_r 0.
Proof Monoid.op_has_inv_r_0 op_monoid.

(**
  Proves that the identity element has an
  inverse.
*)
Theorem op_has_inv_0
  :  has_inv 0.
Proof Monoid.op_has_inv_0 op_monoid.

(**
  Proves that if an element's, x, inverse
  equals 0, x equals 0.
*)
Theorem op_inv_0_eq_0
  :  forall x : E, op_is_inv x 0 -> x = 0.
Proof Monoid.op_inv_0_eq_0 op_monoid.

(**
  Proves that 0 is the only element whose
  inverse is 0.
*)
Theorem op_inv_0_uniq
  :  unique (fun x => op_is_inv x 0) 0.
Proof Monoid.op_inv_0_uniq op_monoid.
 
(** Represents strongly-specified negation. *)
Definition op_neg_strong
  :  forall x : E, { y | op_is_inv x y }
  := fun x => Monoid.op_neg_strong op_monoid x (op_inv_ex x).

(** Represents negation. *)
Definition op_neg
  :  E -> E
  := fun x => Monoid.op_neg op_monoid x (op_inv_ex x).

Notation "{-}" := (op_neg) : group_scope.

Notation "- x" := (op_neg x) : group_scope.

(** Asserts that the negation returns the inverse of its argument *)
Theorem op_neg_def
  :  forall x : E, op_is_inv x (- x).
Proof
  fun x
    => Monoid.op_neg_def op_monoid x (op_inv_ex x).

(** Proves that negation is one-to-one *)
(** 0 = 0
   x + -x = 0
   x + -x = y + -y
   x + -x = y + -x
        x = y
*)
Theorem op_neg_inj
  :  is_injective E E op_neg.
Proof
  fun x y
    => Monoid.op_neg_inj op_monoid x (op_inv_ex x) y (op_inv_ex y).

(** Proves the cancellation property for negation. *)
Theorem op_cancel_neg
  :  forall x : E, - (- x) = x.
Proof
  fun x
    => Monoid.op_cancel_neg_gen op_monoid x (op_inv_ex x) (op_inv_ex (- x)).

(** Proves that negation is surjective - onto *)
Theorem op_neg_onto
  :  is_onto E E {-}.
Proof
  fun x => ex_intro (fun y => - y = x) (- x) (op_cancel_neg x).

(** Proves that negation is bijective. *)
Theorem op_neg_bijective
  :  is_bijective E E {-}.
Proof
  conj op_neg_inj op_neg_onto.

(** Proves that neg x = y -> neg y = x *)
Theorem op_neg_rev
  :  forall x y : E, - x = y -> - y = x.
Proof
  fun x y H
    => eq_sym
            (f_equal {-} H
             || a = - y @a by <- op_cancel_neg x).

(**
  Proves that the left inverse of x + y is -y + -x.
*)
Theorem op_neg_distrib_inv_l
  :  forall x y : E, op_is_inv_l (x + y) (- y + - x).
Proof
  fun x y
    => ((proj2 (op_neg_def (- y)))
            || - y + a = 0                 @a by <- op_cancel_neg y
            || - y + a = 0                 @a by op_id_l y
            || - y + (a + y) = 0           @a by proj2 (op_neg_def (- x))
            || - y + ((- x + a) + y) = 0 @a by <- op_cancel_neg x
            || - y + a = 0                 @a by op_is_assoc (- x) x y
            || a = 0                         @a by <- op_is_assoc (- y) (- x) (x + y)).

(**
  Proves that the right inverse of x + y is -y + -x.
*)
Theorem op_neg_distrib_inv_r
  :  forall x y : E, op_is_inv_r (x + y) (- y + - x).
Proof
  fun x y
    => ((proj2 (op_neg_def x))
            || x + a = 0           @a by op_id_l (- x)
            || x + (a + - x) = 0 @a by proj2 (op_neg_def y)
            || x + a = 0           @a by op_is_assoc y (- y) (- x)
            || a = 0               @a by <- op_is_assoc x y (- y + - x)).

(**
  Proves that the inverse of x + y is -y + -x.
*)
Theorem op_neg_distrib_inv
  :  forall x y : E, op_is_inv (x + y) (- y + - x).
Proof
  fun x y
    => conj
            (op_neg_distrib_inv_l x y)
            (op_neg_distrib_inv_r x y).

(**
  Proves that negation is distributive: i.e.
  -(x + y) = -y + -x.
*)
Theorem op_neg_distrib
  :  forall x y : E, - (x + y) = - y + - x.
Proof
  fun x y
    => ex_ind
            (fun z (H : unique (op_is_inv (x + y)) z)
              => let H0
                   :  z = - (x + y)
                   := (proj2 H) 
                       (- (x + y))
                       (op_neg_def (x + y)) in
                 let H1
                   :  z = (- y + - x)
                   := (proj2 H)
                        (- y + - x)
                        (op_neg_distrib_inv x y) in
                 (H1 || a = - y + - x @a by <- H0))
            (op_inv_uniq_ex (x + y)).

End Theorems.

End Group.

Notation "0" := (Group.E_0) : group_scope.

Notation "x + y" := (Group.op x y) (at level 50, left associativity) : group_scope.

Notation "{+}" := (Group.op) : group_scope.

Notation "{-}" := (Group.op_neg _) : group_scope.

Notation "- x" := (Group.op_neg _ x) : group_scope.
