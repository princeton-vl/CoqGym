(**
  This module defines the Field record type which can be used to
  represent algebraic fields and provides a collection of axioms
  and theorems describing them.

  Algebraic fields are rings in which every *non-zero* element
  has a multiplicative inverse. The subset of elements that have
  inverses form a group w.r.t multiplication.

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

Require Import Eqdep.
Require Import Description.

Require Import base.
Require Import function.
Require Import monoid.
Require Import monoid_group.
Require Import group.
Require Import abelian_group.
Require Import ring.
Require Import commutative_ring.

Module Field.

(** Represents algebraic fields. *)
Structure Field : Type := field {

  (** Represents the set of elements. *)
  E: Set;

  (** Represents 0 - the additive identity. *)
  E_0: E;

  (** Represents 1 - the multiplicative identity. *)
  E_1: E;

  (** Represents addition. *)
  sum: E -> E -> E;

  (** Represents multiplication. *)
  prod: E -> E -> E;

  (** Asserts that 0 <> 1. *)
  distinct_0_1: E_0 <> E_1;

  (** Asserts that addition is associative. *)
  sum_is_assoc : Monoid.is_assoc E sum;

  (** Asserts that addition is commutative. *)
  sum_is_comm : Abelian_Group.is_comm E sum;

  (** Asserts that 0 is the left identity element. *)
  sum_id_l : Monoid.is_id_l E sum E_0;

  (**
    Asserts that every element has an additive
    inverse.
  *)
  sum_inv_l_ex : forall x : E, exists y : E, sum y x = E_0;

  (** Asserts that multiplication is associative. *)
  prod_is_assoc : Monoid.is_assoc E prod;

  (** Asserts that multiplication is commutative. *)
  prod_is_comm : Abelian_Group.is_comm E prod;
  
  (** Asserts that 1 is the left identity element. *)
  prod_id_l : Monoid.is_id_l E prod E_1;

  (**
    Asserts that every *non-zero* element has a
    multiplicative inverse.

    Note: this is the property that distinguishes
    fields from commutative rings.
  *)
  prod_inv_l_ex : forall x : E, x <> E_0 -> exists y : E, prod y x = E_1;

  (**
    Asserts that multiplication is left distributive
    over addition.
  *)
  prod_sum_distrib_l : Ring.is_distrib_l E prod sum
}.

(** Enable implicit arguments for field properties. *)

Arguments E_0 {f}.

Arguments E_1 {f}.

Arguments sum {f} x y.

Arguments prod {f} x y.

Arguments distinct_0_1 {f} _.

Arguments sum_is_assoc {f} x y z.

Arguments sum_is_comm {f} x y.

Arguments sum_id_l {f} x.

Arguments sum_inv_l_ex {f} x.

Arguments prod_is_assoc {f} x y z.

Arguments prod_is_comm {f} x y.

Arguments prod_id_l {f} x.

Arguments prod_inv_l_ex {f} x _.

Arguments prod_sum_distrib_l {f} x y z.

(** Define notations for field properties. *)

Notation "0" := E_0 : field_scope.

Notation "1" := E_1 : field_scope.

Notation "x + y" := (sum x y) (at level 50, left associativity) : field_scope.

Notation "{+}" := sum : field_scope.

Notation "x # y" := (prod x y) (at level 50, left associativity) : field_scope.

Notation "{#}" := prod : field_scope.

Open Scope field_scope.

Section Theorems.

(**
  Represents an arbitrary commutative ring.

  Note: we use Variable rather than Parameter
  to ensure that the following theorems are
  generalized w.r.t r.
*)
Variable f : Field.

(**
  Represents the set of group elements.

  Note: We use Let to define E as a 
  local abbreviation.
*)
Let E := E f.

(**
  Accepts one ring element, x, and asserts
  that x is the left identity element.
*)
Definition sum_is_id_l := Monoid.is_id_l E {+}.

(**
  Accepts one ring element, x, and asserts
  that x is the right identity element.
*)
Definition sum_is_id_r := Monoid.is_id_r E {+}.

(**
  Accepts one ring element, x, and asserts
  that x is the identity element.
*)
Definition sum_is_id := Monoid.is_id E {+}.

(**
  Accepts one ring element, x, and asserts
  that x is the left identity element.
*)
Definition prod_is_id_l := Monoid.is_id_l E {#}.

(**
  Accepts one ring element, x, and asserts
  that x is the right identity element.
*)
Definition prod_is_id_r := Monoid.is_id_r E {#}.

(**
  Accepts one ring element, x, and asserts
  that x is the identity element.
*)
Definition prod_is_id := Monoid.is_id E {#}.

(**
  Represents the commutative ring that addition
  and multiplication form over E.
*)
Definition commutative_ring
  := Commutative_Ring.commutative_ring E 0 1 {+} {#}
       distinct_0_1 sum_is_assoc sum_is_comm sum_id_l sum_inv_l_ex
       prod_is_assoc prod_is_comm prod_id_l prod_sum_distrib_l.

(**
  Represents the non-commutative ring formed
  by addition and multiplication over E.
*)
Definition ring := Commutative_Ring.ring commutative_ring.

(**
  Represents the abelian group formed by
  addition over E.
*)
Definition sum_abelian_group := Commutative_Ring.sum_abelian_group commutative_ring.

(**
  Represents the abelian group formed by
  addition over E.
*)
Definition sum_group := Commutative_Ring.sum_group commutative_ring.

(**
  Represents the monoid formed by addition
  over E.
*)
Definition sum_monoid := Commutative_Ring.sum_monoid commutative_ring.

(**
  Represents the monoid formed by
  multiplication over E.
*)
Definition prod_monoid := Commutative_Ring.prod_monoid commutative_ring.

(** Proves that 1 <> 0. *)
Definition distinct_1_0
  :  1 <> 0
  := Commutative_Ring.distinct_1_0 commutative_ring.

(**
  A predicate that accepts one element, x,
  and asserts that x is nonzero.
*)
Definition nonzero
  :  E -> Prop
  := Commutative_Ring.nonzero commutative_ring.

(** Proves that 0 is the right identity element. *)
Definition sum_id_r
  :  sum_is_id_r 0
  := Commutative_Ring.sum_id_r commutative_ring.

(** Proves that 0 is the identity element. *)
Definition sum_id := Commutative_Ring.sum_id commutative_ring.

(**
  Accepts two elements, x and y, and
  asserts that y is x's left inverse.
*)
Definition sum_is_inv_l := Monoid.is_inv_l E {+} 0 sum_id. 

(**
  Accepts two elements, x and y, and
  asserts that y is x's right inverse.
*)
Definition sum_is_inv_r := Monoid.is_inv_r E {+} 0 sum_id.

(**
  Accepts two elements, x and y, and
  asserts that y is x's inverse.
*)
Definition sum_is_inv := Monoid.is_inv E {+} 0 sum_id.

(** Asserts that every element has a right inverse. *)
Definition sum_inv_r_ex
  :  forall x : E, exists y : E, sum_is_inv_r x y
  := Commutative_Ring.sum_inv_r_ex commutative_ring.

(** Proves that the left identity element is unique. *)
Definition sum_id_l_uniq
  :  forall x : E, Monoid.is_id_l E {+} x -> x = 0
  := Commutative_Ring.sum_id_l_uniq commutative_ring.

(** Proves that the right identity element is unique. *)
Definition sum_id_r_uniq
  :  forall x : E, Monoid.is_id_r E {+} x -> x = 0
  := Commutative_Ring.sum_id_r_uniq commutative_ring.

(** Proves that the identity element is unique. *)
Definition sum_id_uniq
  :  forall x : E, Monoid.is_id E {+} x -> x = 0
  := Commutative_Ring.sum_id_uniq commutative_ring.

(**
  Proves that for every group element, x,
  its left and right inverses are equal.
*)
Definition sum_inv_l_r_eq
  :  forall x y : E, sum_is_inv_l x y -> forall z : E, sum_is_inv_r x z -> y = z
  := Commutative_Ring.sum_inv_l_r_eq commutative_ring.

(**
  Proves that the inverse relation is
  symmetrical.
*)
Definition sum_inv_sym
  :  forall x y : E, sum_is_inv x y <-> sum_is_inv y x
  := Commutative_Ring.sum_inv_sym commutative_ring.

(** Proves that an element's inverse is unique. *)
Definition sum_inv_uniq
  :  forall x y z :  E, sum_is_inv x y -> sum_is_inv x z -> z = y
  := Commutative_Ring.sum_inv_uniq commutative_ring.

(** Proves that every element has an inverse. *)
Definition sum_inv_ex
  :  forall x : E, exists y : E, sum_is_inv x y
  := Commutative_Ring.sum_inv_ex commutative_ring.

(**
  Proves explicitly that every element has a
  unique inverse.
*)
Definition sum_inv_uniq_ex
  :  forall x : E, exists! y : E, sum_is_inv x y
  := Commutative_Ring.sum_inv_uniq_ex commutative_ring.

(** Proves the left introduction rule. *)
Definition sum_intro_l
  :  forall x y z : E, x = y -> z + x = z + y
  := Commutative_Ring.sum_intro_l commutative_ring.

(** Proves the right introduction rule. *)
Definition sum_intro_r
  :  forall x y z : E, x = y -> x + z = y + z
  := Commutative_Ring.sum_intro_r commutative_ring.

(** Proves the left cancellation rule. *)
Definition sum_cancel_l
  :   forall x y z : E, z + x = z + y -> x = y
  := Commutative_Ring.sum_cancel_l commutative_ring.

(** Proves the right cancellation rule. *)
Definition sum_cancel_r
  :   forall x y z : E, x + z = y + z -> x = y
  := Commutative_Ring.sum_cancel_r commutative_ring.

(**
  Proves that an element's left inverse
  is unique.
*)
Definition sum_inv_l_uniq
  :  forall x y z : E, sum_is_inv_l x y -> sum_is_inv_l x z -> z = y
  := Commutative_Ring.sum_inv_l_uniq commutative_ring.

(**
  Proves that an element's right inverse
  is unique.
*)
Definition sum_inv_r_uniq
  :  forall x y z : E, sum_is_inv_r x y -> sum_is_inv_r x z -> z = y
  := Commutative_Ring.sum_inv_r_uniq commutative_ring.

(** Represents strongly-specified negation. *)
Definition sum_neg_strong
  :  forall x : E, { y | sum_is_inv x y }
  := Commutative_Ring.sum_neg_strong commutative_ring.

(** Represents negation. *)
Definition sum_neg
  :  E -> E
  := Commutative_Ring.sum_neg commutative_ring.

Notation "{-}" := (sum_neg) : field_scope.

Notation "- x" := (sum_neg x) : field_scope.

(**
  Asserts that the negation returns the inverse
  of its argument.
*)
Definition sum_neg_def
  :  forall x : E, sum_is_inv x (- x)
  := Commutative_Ring.sum_neg_def commutative_ring.

(** Proves that negation is one-to-one *)
Definition sum_neg_inj
  :  is_injective E E {-}
  := Commutative_Ring.sum_neg_inj commutative_ring.

(** Proves the cancellation property for negation. *)
Definition sum_cancel_neg
  :  forall x : E, {-} (- x) = x
  := Commutative_Ring.sum_cancel_neg commutative_ring.

(** Proves that negation is onto *)
Definition sum_neg_onto
  :  is_onto E E {-}
  := Commutative_Ring.sum_neg_onto commutative_ring.

(** Proves that negation is surjective *)
Definition sum_neg_bijective
  :  is_bijective E E {-}
  := Commutative_Ring.sum_neg_bijective commutative_ring.

(** Proves that 1 is the right identity element. *)
Definition prod_id_r
  :  prod_is_id_r 1
  := Commutative_Ring.prod_id_r commutative_ring.

(**
  Accepts one element, x, and asserts
  that x is the identity element.
*)
Definition prod_id
  :  prod_is_id 1
  := Commutative_Ring.prod_id commutative_ring.

(** Proves that the left identity element is unique. *)
Definition prod_id_l_uniq
  :  forall x : E, (Monoid.is_id_l E {#} x) -> x = 1
  := Commutative_Ring.prod_id_l_uniq commutative_ring.

(** Proves that the right identity element is unique. *)
Definition prod_id_r_uniq
  :  forall x : E, (Monoid.is_id_r E {#} x) -> x = 1
  := Commutative_Ring.prod_id_r_uniq commutative_ring.

(** Proves that the right identity element is unique. *)
Definition prod_id_uniq
  :  forall x : E, (Monoid.is_id E {#} x) -> x = 1
  := Commutative_Ring.prod_id_uniq commutative_ring.

(** Proves the left introduction rule. *)
Definition prod_intro_l
  :  forall x y z : E, x = y -> z # x = z # y
  := Commutative_Ring.prod_intro_l commutative_ring.

(** Proves the right introduction rule. *)
Definition prod_intro_r
  :  forall x y z : E, x = y -> x # z = y # z
  := Commutative_Ring.prod_intro_r commutative_ring.

(**
  Accepts two elements, x and y, and
  asserts that y is x's left inverse.
*)
Definition prod_is_inv_l := Commutative_Ring.prod_is_inv_l commutative_ring.

(**
  Accepts two elements, x and y, and
  asserts that y is x's right inverse.
*)
Definition prod_is_inv_r := Commutative_Ring.prod_is_inv_r commutative_ring.

(**
  Accepts two elements, x and y, and
  asserts that y is x's inverse.
*)
Definition prod_is_inv := Commutative_Ring.prod_is_inv commutative_ring.

(**
  Accepts one argument, x, and asserts that
  x has a left inverse.
*)
Definition prod_has_inv_l := Commutative_Ring.prod_has_inv_l commutative_ring.

(**
  Accepts one argument, x, and asserts that
  x has a right inverse.
*)
Definition prod_has_inv_r := Commutative_Ring.prod_has_inv_r commutative_ring.

(**
  Accepts one argument, x, and asserts that
  x has an inverse.
*)
Definition prod_has_inv := Commutative_Ring.prod_has_inv commutative_ring.

(**
  Proves that every left inverse must also
  be a right inverse.
*)
Definition prod_is_inv_lr := Commutative_Ring.prod_is_inv_lr commutative_ring.

(**
  Proves that every non-zero element has a
  right multiplicative inverse.
*)
Definition prod_inv_r_ex
  :  forall x : E, x <> 0 -> prod_has_inv_r x
  := fun x H
       => ex_ind
            (fun y H0
              => ex_intro (prod_is_inv_r x) y
                   (prod_is_inv_lr x y H0))
            (prod_inv_l_ex x H).

(**
  Proves that every non-zero element has a
  multiplicative inverse.
*)
Definition prod_inv_ex 
  :  forall x : E, nonzero x -> prod_has_inv x
  := fun x H
       => ex_ind
            (fun y H0
              => ex_intro (prod_is_inv x) y
                   (conj H0
                     (prod_is_inv_lr x y H0)))
            (prod_inv_l_ex x H).

(**
  Proves that the left and right inverses of
  an element must be equal.
*)
Definition prod_inv_l_r_eq
  :  forall x y : E, prod_is_inv_l x y -> forall z : E, prod_is_inv_r x z -> y = z
  := Commutative_Ring.prod_inv_l_r_eq commutative_ring.

(**
  Proves that the inverse relationship is
  symmetric.
*)
Definition prod_inv_sym
  :  forall x y : E, prod_is_inv x y <-> prod_is_inv y x
  := Commutative_Ring.prod_inv_sym commutative_ring.

(**
  Proves the left cancellation law for elements
  possessing a left inverse.
*)
Definition prod_cancel_l
  :   forall x y z : E, nonzero z -> z # x = z # y -> x = y
  := fun x y z H
       => Commutative_Ring.prod_cancel_l commutative_ring x y z (prod_inv_l_ex z H).

(**
  Proves the right cancellation law for
  elements possessing a right inverse.
*)
Definition prod_cancel_r
  :   forall x y z : E, nonzero z -> x # z = y # z -> x = y
  := fun x y z H
       => Commutative_Ring.prod_cancel_r commutative_ring x y z (prod_inv_r_ex z H).

(**
  Proves that an element's left inverse
  is unique.
*)
Definition prod_inv_l_uniq
  :  forall x : E, nonzero x -> forall y z : E, prod_is_inv_l x y -> prod_is_inv_l x z -> z = y
  := fun x H
       => Commutative_Ring.prod_inv_l_uniq commutative_ring x (prod_inv_r_ex x H).

(**
  Proves that an element's right inverse
  is unique.
*)
Definition prod_inv_r_uniq
  :  forall x : E, nonzero x -> forall y z : E, prod_is_inv_r x y -> prod_is_inv_r x z -> z = y
  := fun x H
       => Commutative_Ring.prod_inv_r_uniq commutative_ring x (prod_inv_l_ex x H).

(** Proves that an element's inverse is unique. *)
Definition prod_inv_uniq
  :  forall x y z : E, prod_is_inv x y -> prod_is_inv x z -> z = y
  := Commutative_Ring.prod_inv_uniq commutative_ring.

(**
  Proves that every nonzero element has a
  unique inverse.
*)
Definition prod_uniq_inv_ex
  :  forall x : E, nonzero x -> exists! y : E, prod_is_inv x y
  := fun x H
       => ex_ind
            (fun y (H0 : prod_is_inv x y)
              => ex_intro
                   (unique (prod_is_inv x))
                   y
                   (conj H0 (fun z H1 => eq_sym (prod_inv_uniq x y z H0 H1))))
            (prod_inv_ex x H).

(** Proves that 1 is its own left multiplicative inverse. *)
Definition recipr_1_l
  :  prod_is_inv_l 1 1
  := Commutative_Ring.recipr_1_l commutative_ring.

(** Proves that 1 is its own right multiplicative inverse. *)
Definition recipr_1_r
  :  prod_is_inv_r 1 1
  := Commutative_Ring.recipr_1_r commutative_ring.

(** Proves that 1 is its own recriprical. *)
Definition recipr_1
  :  prod_is_inv 1 1
  := Commutative_Ring.recipr_1 commutative_ring.

(** Proves that 1 has a left multiplicative inverse. *)
Definition prod_has_inv_l_1
  :  prod_has_inv_l 1
  := Commutative_Ring.prod_has_inv_l_1 commutative_ring.

(** Proves that 1 has a right multiplicative inverse. *)
Definition prod_has_inv_r_1
  :  prod_has_inv_r 1
  := Commutative_Ring.prod_has_inv_r_1 commutative_ring.

(** Proves that 1 has a reciprical *)
Definition prod_has_inv_1
  :  prod_has_inv 1
  := Commutative_Ring.prod_has_inv_1 commutative_ring.

(**
  Proves that multiplication is right distributive
  over addition.
*)
Definition prod_sum_distrib_r
  :  Ring.is_distrib_r E {#} {+}
  := Commutative_Ring.prod_sum_distrib_r commutative_ring.

(**
  Asserts that multiplication is
  distributive over addition.
*)
Definition prod_sum_distrib
  :  Ring.is_distrib E {#} {+}
  := Commutative_Ring.prod_sum_distrib commutative_ring.

(**
  Proves that 0 times every number equals 0.

  0 x = 0 x
  (0 + 0) x = 0 x
  0 x + 0 x = 0 x
        0 x = 0
*)
Definition prod_0_l
  :  forall x : E, 0 # x = 0
  := Commutative_Ring.prod_0_l commutative_ring.

(** Proves that 0 times every number equals 0. *)
Definition prod_0_r
  :  forall x : E, x # 0 = 0
  := Commutative_Ring.prod_0_r commutative_ring.

(** Proves that 0 does not have a left multiplicative inverse. *)
Definition prod_0_inv_l
  :  ~ prod_has_inv_l 0
  := Commutative_Ring.prod_0_inv_l commutative_ring.

(** Proves that 0 does not have a right multiplicative inverse. *)
Definition prod_0_inv_r
  :  ~ prod_has_inv_r 0
  := Commutative_Ring.prod_0_inv_r commutative_ring.

(**
  Proves that 0 does not have a multiplicative
  inverse - I.E. 0 does not have a
  reciprocal.
*)
Definition prod_0_inv
  :  ~ prod_has_inv 0
  := Commutative_Ring.prod_0_inv commutative_ring.

(**
  Proves that multiplicative inverses, when
  they exist are always nonzero.
*)
Definition prod_inv_0
  :  forall x y : E, prod_is_inv x y -> nonzero y
  := Commutative_Ring.prod_inv_0 commutative_ring.

(**
  Proves that the product of two non-zero
  values is non-zero.

  x * y <> 0
  x * y = 0 -> False

  assume x * y = 0 
  1/x * x * y = 1/x * 0
  y = 0
  which is a contradiction.
*)
Definition prod_nonzero_closed
  :  forall x : E, nonzero x -> forall y : E, nonzero y -> nonzero (x # y)
  := fun x H y H0 (H1 : x # y = 0)
       => ex_ind 
            (fun z (H2 : prod_is_inv_l x z)
              => H0 (prod_intro_l (x # y) 0 z H1 
                     || z # (x # y) = a @a by <- prod_0_r z 
                     || a           = 0 @a by <- prod_is_assoc z x y
                     || a # y       = 0 @a by <- H2
                     || a           = 0 @a by <- prod_id_l y))
            (prod_inv_l_ex x H).

(** Represents -1 and proves that it exists. *)
Definition E_n1_strong
  :  { x : E | sum_is_inv 1 x }
  := Commutative_Ring.E_n1_strong commutative_ring.

(** Represents -1. *)
Definition E_n1 : E := Commutative_Ring.E_n1 commutative_ring.

(**
  Defines a symbolic representation for -1
  
  Note: here we represent the inverse of 1
  rather than the negation of 1. Letter we prove
  that the negation equals the inverse.

  Note: brackets are needed to ensure Coq parses
  the symbol as a single token instead of a
  prefixed function call.
*)
Notation "{-1}" := E_n1 : field_scope.

(** Asserts that -1 is the additive inverse of 1. *)
Definition E_n1_def
  :  sum_is_inv 1 {-1}
  := Commutative_Ring.E_n1_def commutative_ring.
      
(** Asserts that -1 is the left inverse of 1. *)
Definition E_n1_inv_l
  :  sum_is_inv_l 1 {-1}
  := Commutative_Ring.E_n1_inv_l commutative_ring.

(** Asserts that -1 is the right inverse of 1. *)
Definition E_n1_inv_r
  :  sum_is_inv_r 1 {-1}
  := Commutative_Ring.E_n1_inv_r commutative_ring.

(**
  Asserts that every additive inverse
  of 1 must be equal to -1.
*)
Definition E_n1_uniq
  :  forall x : E, sum_is_inv 1 x -> x = {-1}
  := Commutative_Ring.E_n1_uniq commutative_ring.

(**
  Proves that -1 * x equals the multiplicative
  inverse of x.

  -1 x + x = 0
  -1 x + 1 x = 0
  (-1 + 1) x = 0
  0 x = 0
  0 = 0
*) 
Definition prod_n1_x_inv_l
  :  forall x : E, sum_is_inv_l x ({-1} # x)
  := Commutative_Ring.prod_n1_x_inv_l commutative_ring.

(**
  Proves that x * -1 equals the multiplicative
  inverse of x.

  x -1 + x = 0
*)
Definition prod_x_n1_inv_l
  :  forall x : E, sum_is_inv_l x (x # {-1})
  := Commutative_Ring.prod_x_n1_inv_l commutative_ring.

(** Proves that x + -1 x = 0. *)
Definition prod_n1_x_inv_r
  :  forall x : E, sum_is_inv_r x ({-1} # x)
  := Commutative_Ring.prod_n1_x_inv_r commutative_ring.

(** Proves that x + x -1 = 0. *)
Definition prod_x_n1_inv_r
  :  forall x : E, sum_is_inv_r x (x # {-1})
  := Commutative_Ring.prod_x_n1_inv_r commutative_ring.

(** Proves that -1 x is the additive inverse of x. *)
Definition prod_n1_x_inv
  :  forall x : E, sum_is_inv x ({-1} # x)
  := Commutative_Ring.prod_n1_x_inv commutative_ring.

(** Proves that x -1 is the additive inverse of x. *)
Definition prod_x_n1_inv
  :  forall x : E, sum_is_inv x (x # {-1})
  := Commutative_Ring.prod_x_n1_inv commutative_ring.

(**
  Proves that multiplying by -1 is equivalent
  to negation.
*)
Definition prod_n1_neg
  :  {#} {-1} = {-}
  := Commutative_Ring.prod_n1_neg commutative_ring.

(**
  Accepts one element, x, and proves that
  x -1 equals the additive negation of x.
*)
Definition prod_x_n1_neg
  :  forall x : E, x # {-1} = - x
  := Commutative_Ring.prod_x_n1_neg commutative_ring.

(**
  Accepts one element, x, and proves that
  -1 x equals the additive negation of x.
*)
Definition prod_n1_x_neg
  :  forall x : E, {-1} # x = - x
  := Commutative_Ring.prod_n1_x_neg commutative_ring.

(** Proves that -1 x = x -1. *)
Definition prod_n1_eq
  :  forall x : E, {-1} # x = x # {-1} 
  := Commutative_Ring.prod_n1_eq commutative_ring.

(** Proves that the additive negation of 1 equals -1. *)
Definition neg_1
  :  {-} 1 = {-1}
  := Commutative_Ring.neg_1 commutative_ring.

(** Proves that the additive negation of -1 equals 1. *)
Definition neg_n1
  :  - {-1} = 1
  := Commutative_Ring.neg_n1 commutative_ring.

(**
  Proves that -1 * -1 = 1.

  -1 * -1 = -1 * -1
  -1 * -1 = prod -1 -1
  -1 * -1 = {-} -1
  -1 * -1 = 1 
*)
Definition prod_n1_n1
  :  {-1} # {-1} = 1
  := Commutative_Ring.prod_n1_n1 commutative_ring.

(**
  Proves that -1 is its own multiplicative
  inverse.
*)
Definition E_n1_inv
  :  prod_is_inv {-1} {-1}
  := Commutative_Ring.E_n1_inv commutative_ring.

(** Proves that -1 is nonzero. *)
Definition nonzero_n1
  :  nonzero {-1}
  := fun H : {-1} = 0
       => distinct_1_0
            (prod_intro_l {-1} 0 {-1} H
              || a = {-1} # 0 @a by <- prod_n1_n1
              || 1 = a        @a by <- prod_0_r {-1}).

(** Represents the reciprical operation. *)
Definition recipr_strong
  :  forall x : E, nonzero x -> {y | prod_is_inv x y}
  := fun x H
       => constructive_definite_description (prod_is_inv x)
            (prod_uniq_inv_ex x H).

(** Represents the reciprical operation. *)
Definition recipr
  :  forall x : E, nonzero x -> E
  := fun x H
       => proj1_sig (recipr_strong x H).

Notation "{1/ x }" := (recipr x) : field_scope.

(**
  Proves that the reciprical operation correctly
  returns the inverse of the given element.
*)
Definition recipr_def
  :  forall (x : E) (H : nonzero x), prod_is_inv x ({1/x} H)
  := fun x H
       => proj2_sig (recipr_strong x H).

(** Proves that (1/-1) = -1. *)
Definition recipr_n1
  :  ({1/{-1}} nonzero_n1) = {-1}
  := prod_inv_uniq {-1} {-1} ({1/{-1}} nonzero_n1)
       E_n1_inv
       (recipr_def {-1} nonzero_n1).

(** Proves that recipricals are nonzero. *)
Definition recipr_nonzero
  :  forall (x : E) (H : nonzero x), nonzero ({1/x} H)
  := fun x H
       => prod_inv_0 x ({1/x} H) (recipr_def x H).

(** Proves that 1/(1/x) = x *)
Definition recipr_cancel
  :  forall (x : E) (H : nonzero x), ({1/({1/x} H)} (recipr_nonzero x H)) = x
  := fun x H
       => Monoid.op_cancel_neg_gen prod_monoid x
            (prod_inv_ex x H)
            (prod_inv_ex ({1/x} H) (recipr_nonzero x H)).

(** Represents division. *)
Definition div
  :  E -> forall x : E, nonzero x -> E
  := fun x y H
       => x # ({1/y} H).

Notation "x / y" := (div x y) : field_scope.

(** Proves that x y/x = y. *)
Definition div_cancel_l
  :  forall (x : E) (H : nonzero x) (y : E), x # ((y/x) H) = y
  := fun x H y
       => eq_refl (x # ((y/x) H))
          || x # ((y/x) H) = x # a @a by <- prod_is_comm y ({1/x} H)
          || x # ((y/x) H) = a     @a by <- prod_is_assoc x ({1/x} H) y
          || x # ((y/x) H) = a # y @a by <- proj2 (recipr_def x H)
          || x # ((y/x) H) = a     @a by <- prod_id_l y.

(** Proves that x/y y = x. *)
Definition div_cancel_r
  :  forall (x : E) (H : nonzero x) (y : E), ((y/x) H) # x = y
  := fun x H y
       => div_cancel_l x H y
          || a = y @a by <- prod_is_comm x ((y/x) H).

(**
  The following section proves that the set of
  nonzero elements forms an algebraic group
  over multiplication with 1 as the identity.

  To show this, we map every nonzero field
  element, x, onto a dependent product, (x, H),
  where H represents a proof that x is nonzero.

  We then define equality over these products
  such that two pair, (x, H) and (y, H0), are
  equal whenever x and y are.

  Continuing, we define multiplication reasonably
  so that (x, H) # (y, H0) = (x * y, H1) where
  # denotes multiplication over pairs.

  With these definitions in hand, we show that
  the resulting elements form a group and that
  this group is isomorphic with the set of
  nonzero field elements.
*)

(**
  Represents those field elements that are
  nonzero.

  Note: each value can be seen intuitively as
  a pair, (x, H), where x is a monoid element
  and H is a proof that x is invertable.
*)
Definition D : Set := {x : E | nonzero x}.

(**
  Accepts a field element and a proof that
  it is nonzero and returns its projection
  in D.
*)
Definition D_cons
  :  forall x : E, nonzero x -> D
  := exist nonzero.

(**
  Asserts that any two equal non-zero
  elements, x and y, are equivalent (using
  dependent equality).

  Note: to compare sig elements that differ
  only in their proof terms, such as (x, H) and
  (x, H0), we must introduce a new notion of
  equality called "dependent equality". This
  relationship is defined in the Eqdep module.
*)
Axiom D_eq_dep
  : forall (x : E) (H : nonzero x) (y : E) (H0 : nonzero y), y = x -> eq_dep E nonzero y H0 x H.

(**
  Given that two invertable monoid elements x
  and y are equal (using dependent equality),
  this lemma proves that their projections
  into D are equal.

  Note: this proof is equivalent to:

    eq_dep_eq_sig E (Monoid.has_inv m) y x H0 H
      (D_eq_dep x H y H0 H1).

  The definition for eq_dep_eq_sig has been
  expanded however for compatability with
  Coq v8.4.
*)
Definition D_eq
  :  forall (x : E) (H : nonzero x) (y : E) (H0 : nonzero y), y = x -> D_cons y H0 = D_cons x H
  := fun x H y H0 H1
       => eq_dep_ind E nonzero y H0
            (fun (z : E) (H2 : nonzero z)
              => D_cons y H0 = D_cons z H2)
            (eq_refl (D_cons y H0)) x H (D_eq_dep x H y H0 H1).

(**
  Represents the group identity element.
*)
Definition D_1 := D_cons 1 distinct_1_0.

(**
  Represents the group operation.

  Note: intuitively this function accepts two
  invertable monoid elements, (x, H) and (y,
  H0), and returns (x + y, H1), where H, H0,
  and H1 are generalized invertability proofs.
*)
Definition D_prod
  :  D -> D -> D
  := sig_rec
       (fun _ => D -> D)
       (fun (u : E) (H : nonzero u)
         => sig_rec
              (fun _ => D)
              (fun (v : E) (H0 : nonzero v)
                => D_cons
                     (u # v)
                     (prod_nonzero_closed u H v H0))).

(** TODO *)
(**
  Proves that D and D_prod are isomorphic with
  the set of nonzero field elements.
*)
(** Definition D_iso *)

(**
  Accepts a group element, x, and asserts
  that x is a left identity element.
*)
Definition D_prod_is_id_l := Monoid.is_id_l D D_prod.

(**
  Accepts a group element, x, and asserts
  that x is a right identity element.
*)
Definition D_prod_is_id_r := Monoid.is_id_r D D_prod.

(**
  Accepts a group element, x, and asserts
  that x is an/the identity element.
*)
Definition D_prod_is_id := Monoid.is_id D D_prod.


(** Proves that D_1 is a left identity element. *)
Definition D_prod_id_l
  :  D_prod_is_id_l D_1
  := sig_ind
       (fun x => D_prod D_1 x = x)
       (fun (u : E) (H : nonzero u)
          => D_eq u H (1 # u) (prod_nonzero_closed 1 distinct_1_0 u H)
               (prod_id_l u)).

(** Proves that D_1 is a right identity element. *)
Definition D_prod_id_r
  :  D_prod_is_id_r D_1
  := sig_ind
       (fun x => D_prod x D_1 = x)
       (fun (u : E) (H : nonzero u)
          => D_eq u H (u # 1) (prod_nonzero_closed u H 1 distinct_1_0)
               (prod_id_r u)).

(** Proves that D_1 is the identity element. *)
Definition D_prod_id
  :  D_prod_is_id D_1
  := conj D_prod_id_l D_prod_id_r.

(**
  Proves that the group operation is
  associative.
*)
Definition D_prod_assoc
  :  Monoid.is_assoc D D_prod
  := sig_ind
       (fun x => forall y z : D, D_prod x (D_prod y z) = D_prod (D_prod x y) z)
       (fun (u : E) (H : nonzero u)
         => sig_ind
              (fun y => forall z : D, D_prod (D_cons u H) (D_prod y z) = D_prod (D_prod (D_cons u H) y) z)
              (fun (v : E) (H0 : nonzero v)
                => sig_ind
                     (fun z => D_prod (D_cons u H) (D_prod (D_cons v H0) z) = D_prod (D_prod (D_cons u H) (D_cons v H0)) z)
                     (fun (w : E) (H1 : nonzero w)
                       => let a
                            :  E
                            := u # (v # w) in
                          let H2
                            :  nonzero a
                            := prod_nonzero_closed u H (v # w) (prod_nonzero_closed v H0 w H1) in
                          let b
                            :  E
                            := prod (u # v) w in
                          let H3
                            :  nonzero b
                            := prod_nonzero_closed (u # v) (prod_nonzero_closed u H v H0) w H1 in
                          let X
                            :  D
                            := D_cons a H2 in
                          let Y
                            :  D
                            := D_cons b H3 in
                          D_eq b H3 a H2
                            (prod_is_assoc u v w)
              ))).

(**
  Accepts two values, x and y, and asserts
  that y is a left inverse of x.
*)
Definition D_prod_is_inv_l := Monoid.is_inv_l D D_prod D_1 D_prod_id.

(**
  Accepts two values, x and y, and asserts
  that y is a right inverse of x.
*)
Definition D_prod_is_inv_r := Monoid.is_inv_r D D_prod D_1 D_prod_id.

(**
  Accepts two values, x and y, and asserts
  that y is an inverse of x.
*)
Definition D_prod_is_inv := Monoid.is_inv D D_prod D_1 D_prod_id.

(**
  Accepts two nonzero elements, x
  and y, where y is a left inverse of x and
  proves that y's projection into D is the
  left inverse of x's.
*)
Definition D_prod_inv_l
  :  forall (u : E) (H : nonzero u) (v : E) (H0 : nonzero v),
       prod_is_inv_l u v ->
       D_prod_is_inv_l (D_cons u H) (D_cons v H0)
  := fun (u : E) (H : nonzero u) (v : E) (H0 : nonzero v)
       => D_eq 1 distinct_1_0 (v # u) (prod_nonzero_closed v H0 u H).
      
(**
  Accepts two invertable monoid elements, x
  and y, where y is a right inverse of x and
  proves that y's projection into D is the
  right inverse of x's.
*)
Definition D_prod_inv_r
  :  forall (u : E) (H : nonzero u) (v : E) (H0 : nonzero v),
       prod_is_inv_r u v ->
       D_prod_is_inv_r (D_cons u H) (D_cons v H0)
  := fun (u : E) (H : nonzero u) (v : E) (H0 : nonzero v)
       => D_eq 1 distinct_1_0 (u # v) (prod_nonzero_closed u H v H0).

(**
  Accepts two invertable monoid elements, x
  and y, where y is the inverse of x and
  proves that y's projection into D is the
  inverse of x's.
*)
Definition D_prod_inv
  :  forall (u : E) (H : nonzero u) (v : E) (H0 : nonzero v),
       prod_is_inv u v ->
       D_prod_is_inv (D_cons u H) (D_cons v H0)
  := fun (u : E) (H : nonzero u) (v : E) (H0 : nonzero v) (H1 : prod_is_inv u v)
       => conj (D_prod_inv_l u H v H0 (proj1 H1))
               (D_prod_inv_r u H v H0 (proj2 H1)).

(**
  Accepts a nonzero element and returns its
  inverse, y, along with a proof that y is
  x's inverse.
*)
Definition D_prod_neg_strong
  :  forall x : D, { y : D | D_prod_is_inv x y }
  := sig_rec
       (fun x => { y : D | D_prod_is_inv x y })
       (fun (u : E) (H : nonzero u)
         => let v
              :  E
              := Monoid.op_neg prod_monoid u (prod_inv_ex u H) in
            let H0
              :  prod_is_inv u v
              := Monoid.op_neg_def prod_monoid u (prod_inv_ex u H) in
            let H1
              :  nonzero v
              := prod_inv_0 u v H0 in
            exist
              (fun y : D => D_prod_is_inv (D_cons u H) y)
              (D_cons v H1)
              (D_prod_inv u H v H1 H0)).

(**
  Proves that every group element has an
  inverse.
*)
Definition D_prod_inv_ex 
  :  forall x : D, exists y : D, D_prod_is_inv x y
  := fun x
       => let (y, H) := D_prod_neg_strong x in
          ex_intro
            (fun y => D_prod_is_inv x y)
            y H.

(**
  Proves that every group element has a left
  inverse.
*)
Definition D_prod_inv_l_ex
  :  forall x : D, exists y : D, D_prod_is_inv_l x y
  := fun x
       => ex_ind
            (fun y (H : D_prod_is_inv x y)
              => ex_intro (fun z => D_prod_is_inv_l x z) y (proj1 H))
            (D_prod_inv_ex x).

(**
  Proves that every group element has a right
  inverse.
*)
Definition D_prod_inv_r_ex
  :  forall x : D, exists y : D, D_prod_is_inv_r x y
  := fun x
       => ex_ind
            (fun y (H : D_prod_is_inv x y)
              => ex_intro (fun z => D_prod_is_inv_r x z) y (proj2 H))
            (D_prod_inv_ex x).

(**
  Proves that the set of nonzero elements form
  a group over multiplication.
*)
Definition nonzero_group := Group.group D D_1 D_prod D_prod_assoc
  D_prod_id_l D_prod_id_r D_prod_inv_l_ex
  D_prod_inv_r_ex.

End Theorems.

End Field.
