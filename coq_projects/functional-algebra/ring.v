(**
  This module defines the Ring record type which can be used to
  represent algebraic rings and provides a collection of axioms
  and theorems describing them.

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
Require Import FunctionalExtensionality.
Require Import base.
Require Import function.
Require Import monoid.
Require Import group.
Require Import abelian_group.

Module Ring.

Close Scope nat_scope.

(**
  Accepts two binary functions, f and g, and
  asserts that f is left distributive over g.
*)
Definition is_distrib_l (T : Type) (f g : T -> T -> T)
  :  Prop
  := forall x y z : T, f x (g y z) = g (f x y) (f x z).

(**
  Accepts two binary functions, f and g, and
  asserts that f is right distributive over g.
*)
Definition is_distrib_r (T : Type) (f g : T -> T -> T)
  :  Prop
  := forall x y z : T, f (g y z) x = g (f y x) (f z x).

(**
  Accepts two binary functions, f and g, and
  asserts that f is distributive over g.
*)
Definition is_distrib (T : Type) (f g : T -> T -> T)
  :  Prop
  := is_distrib_l T f g /\ is_distrib_r T f g.

(** Represents algebraic rings *)
Structure Ring : Type := ring {

  (** Represents the set of ring elements. *)
  E : Set;

  (** Represents 0 - the additive identity. *)
  E_0 : E;

  (** Represents 1 - the multiplicative identity. *)
  E_1 : E;

  (** Represents addition. *)
  sum : E -> E -> E;

  (** Represents multiplication. *)
  prod : E -> E -> E;

  (** Asserts that 0 /= 1. *)
  distinct_0_1 : E_0 <> E_1;

  (** Asserts that addition is associative. *)
  sum_is_assoc : Monoid.is_assoc E sum;

  (** Asserts that addition is commutative. *)
  sum_is_comm : Abelian_Group.is_comm E sum;

  (** Asserts that E_0 is the left identity element. *)
  sum_id_l : Monoid.is_id_l E sum E_0;

  (**
    Asserts that every element has an additive
    inverse.
  *)
  sum_inv_l_ex : forall x : E, exists y : E, sum y x = E_0;

  (** Asserts that multiplication is associative. *)
  prod_is_assoc : Monoid.is_assoc E prod;

  (**
    Asserts that 1 is the left identity
    element.
  *)
  prod_id_l : Monoid.is_id_l E prod E_1;

  (**
    Asserts that 1 is the right identity
    element.
  *)
  prod_id_r : Monoid.is_id_r E prod E_1;

  (**
    Asserts that multiplication is left
    distributive over addition.
  *)
  prod_sum_distrib_l : is_distrib_l E prod sum;
   
  (**
    Asserts that multiplication is right
    distributive over addition.
  *)
  prod_sum_distrib_r : is_distrib_r E prod sum
}.

(** Enable implicit arguments for ring properties. *)

Arguments E_0 {r}.

Arguments E_1 {r}.

Arguments sum {r} x y.

Arguments prod {r} x y.

Arguments distinct_0_1 {r} _.

Arguments sum_is_assoc {r} x y z.

Arguments sum_is_comm {r} x y.

Arguments sum_id_l {r} x.

Arguments sum_inv_l_ex {r} x.

Arguments prod_is_assoc {r} x y z.

Arguments prod_id_l {r} x.

Arguments prod_id_r {r} x.

Arguments prod_sum_distrib_l {r} x y z.

Arguments prod_sum_distrib_r {r} x y z.

(** Define notations for ring properties. *)

Notation "0" := E_0 : ring_scope.

Notation "1" := E_1 : ring_scope.

Notation "x + y" := (sum x y) (at level 50, left associativity) : ring_scope.

Notation "{+}" := sum : ring_scope.

Notation "x # y" := (prod x y) (at level 50, left associativity) : ring_scope.

Notation "{#}" := prod : ring_scope.

Open Scope ring_scope.

Section Theorems.

(**
  Represents an arbitrary ring.

  Note: we use Variable rather than Parameter
  to ensure that the following theorems are
  generalized w.r.t r.
*)
Variable r : Ring.

(**
  Represents the set of group elements.

  Note: We use Let to define E as a 
  local abbreviation.
*)
Let E := E r.

(**
  A predicate that accepts one element, x,
  and asserts that x is nonzero.
*)
Definition nonzero (x : E) : Prop := x <> 0.

(**
  Accepts one ring element, x, and asserts
  that x is the left identity element.
*)
Definition sum_is_id_l := Monoid.is_id_l E sum.

(**
  Accepts one ring element, x, and asserts
  that x is the right identity element.
*)
Definition sum_is_id_r := Monoid.is_id_r E sum.

(**
  Accepts one ring element, x, and asserts
  that x is the identity element.
*)
Definition sum_is_id := Monoid.is_id E sum.

(**
  Represents the abelian group formed by
  addition over E.
*)
Definition sum_abelian_group
  := Abelian_Group.abelian_group E 0 {+} sum_is_assoc sum_is_comm sum_id_l sum_inv_l_ex.

(**
  Represents the group formed by addition
  over E.
*)
Definition sum_group
  := Abelian_Group.op_group sum_abelian_group.

(**
  Represents the monoid formed by addition
  over E.
*)
Definition sum_monoid
  := Abelian_Group.op_monoid sum_abelian_group.

(** Proves that 0 is the right identity element. *)
Theorem sum_id_r
  :  sum_is_id_r 0.
Proof Abelian_Group.op_id_r sum_abelian_group.

(** Proves that 0 is the identity element. *)
Theorem sum_id
  :  sum_is_id 0.
Proof Abelian_Group.op_id sum_abelian_group.

(**
  Accepts two elements, x and y, and
  asserts that y is x's left inverse.
*)
Definition sum_is_inv_l
  := Abelian_Group.op_is_inv_l sum_abelian_group.

(**
  Accepts two elements, x and y, and
  asserts that y is x's right inverse.
*)
Definition sum_is_inv_r
  := Abelian_Group.op_is_inv_r sum_abelian_group.

(**
  Accepts two elements, x and y, and
  asserts that y is x's inverse.
*)
Definition sum_is_inv
  := Abelian_Group.op_is_inv sum_abelian_group.

(**
  Accepts one argument, x, and asserts that
  x has a left inverse.
*)
Definition sum_has_inv_l := Abelian_Group.has_inv_l sum_abelian_group.

(**
  Accepts one argument, x, and asserts that
  x has a right inverse.
*)
Definition sum_has_inv_r := Abelian_Group.has_inv_r sum_abelian_group.

(**
  Accepts one argument, x, and asserts that
  x has an inverse.
*)
Definition sum_has_inv := Abelian_Group.has_inv sum_abelian_group.

(** Asserts that every element has a right inverse. *)
Theorem sum_inv_r_ex
  :  forall x : E, exists y : E, sum_is_inv_r x y.
Proof Abelian_Group.op_inv_r_ex sum_abelian_group.

(** Proves that the left identity element is unique. *)
Theorem sum_id_l_uniq
  :  forall x : E, Monoid.is_id_l E {+} x -> x = 0.
Proof Abelian_Group.op_id_l_uniq sum_abelian_group.

(** Proves that the right identity element is unique. *)
Theorem sum_id_r_uniq
  :  forall x : E, Monoid.is_id_r E {+} x -> x = 0.
Proof Abelian_Group.op_id_r_uniq sum_abelian_group.

(** Proves that the identity element is unique. *)
Theorem sum_id_uniq
  :  forall x : E, Monoid.is_id E {+} x -> x = 0.
Proof Abelian_Group.op_id_uniq sum_abelian_group.

(**
  Proves that for every group element, x,
  its left and right inverses are equal.
*)
Theorem sum_inv_l_r_eq
  :  forall x y : E, sum_is_inv_l x y -> forall z : E, sum_is_inv_r x z -> y = z.
Proof Abelian_Group.op_inv_l_r_eq sum_abelian_group.

(**
  Proves that the inverse relation is
  symmetrical.
*)
Theorem sum_inv_sym
  :  forall x y : E, sum_is_inv x y <-> sum_is_inv y x.
Proof Abelian_Group.op_inv_sym sum_abelian_group.

(** Proves that an element's inverse is unique. *)
Theorem sum_inv_uniq
  :  forall x y z :  E, sum_is_inv x y -> sum_is_inv x z -> z = y.
Proof Abelian_Group.op_inv_uniq sum_abelian_group.

(**
  Proves that every group element has an
  inverse.
*)
Theorem sum_inv_ex
  :  forall x : E, exists y : E, sum_is_inv x y.
Proof Abelian_Group.op_inv_ex sum_abelian_group.

(**
  Proves explicitly that every element has a
  unique inverse.
*)
Theorem sum_inv_uniq_ex
  :  forall x : E, exists! y : E, sum_is_inv x y.
Proof Abelian_Group.op_inv_uniq_ex sum_abelian_group.

(** Proves the left introduction rule. *)
Theorem sum_intro_l
  :  forall x y z : E, x = y -> z + x = z + y.
Proof Abelian_Group.op_intro_l sum_abelian_group.

(** Proves the right introduction rule. *)
Theorem sum_intro_r
  :  forall x y z : E, x = y -> x + z = y + z.
Proof Abelian_Group.op_intro_r sum_abelian_group.

(** Proves the left cancellation rule. *)
Theorem sum_cancel_l
  :   forall x y z : E, z + x = z + y -> x = y.
Proof Abelian_Group.op_cancel_l sum_abelian_group.

(** Proves the right cancellation rule. *)
Theorem sum_cancel_r
  :   forall x y z : E, x + z = y + z -> x = y.
Proof Abelian_Group.op_cancel_r sum_abelian_group.

(**
  Proves that an element's left inverse
  is unique.
*)
Theorem sum_inv_l_uniq
  :  forall x y z : E, sum_is_inv_l x y -> sum_is_inv_l x z -> z = y.
Proof Abelian_Group.op_inv_l_uniq sum_abelian_group.

(**
  Proves that an element's right inverse
  is unique.
*)
Theorem sum_inv_r_uniq
  :  forall x y z : E, sum_is_inv_r x y -> sum_is_inv_r x z -> z = y.
Proof Abelian_Group.op_inv_r_uniq sum_abelian_group.

(**
  Proves that 0 is its own left additive
  inverse.
*)
Theorem sum_0_inv_l
  :  sum_is_inv_l 0 0.
Proof Abelian_Group.op_inv_0_l sum_abelian_group.

(**
  Proves that 0 is its own right additive
  inverse.
*)
Theorem sum_0_inv_r
  :  sum_is_inv_r 0 0.
Proof Abelian_Group.op_inv_0_r sum_abelian_group.

(** Proves that 0 is it's own additive inverse. *)
Theorem sum_0_inv
  :  sum_is_inv 0 0.
Proof Abelian_Group.op_inv_0 sum_abelian_group.

(**
  Proves that the identity element has a
  left inverse.
*)
Theorem sum_has_inv_l_0
  :  sum_has_inv_l 0.
Proof Abelian_Group.op_has_inv_l_0 sum_abelian_group.

(**
  Proves that the identity element has a
  right inverse.
*)
Theorem sum_has_inv_r_0
  :  sum_has_inv_r 0.
Proof Abelian_Group.op_has_inv_r_0 sum_abelian_group.

(**
  Proves that the identity element has an
  inverse.
*)
Theorem sum_has_inv_0
  :  sum_has_inv 0.
Proof Abelian_Group.op_has_inv_0 sum_abelian_group.

(**
  Proves that if an element's, x, inverse
  equals 0, x equals 0.
*)
Theorem sum_inv_0_eq_0
  :  forall x : E, sum_is_inv x 0 -> x = 0.
Proof Abelian_Group.op_inv_0_eq_0 sum_abelian_group.

(**
  Proves that 0 is the only element whose
  additive inverse is 0.
*)
Theorem sum_inv_0_uniq
  :  unique (fun x => sum_is_inv x 0) 0.
Proof Abelian_Group.op_inv_0_uniq sum_abelian_group.

(** Represents strongly-specified negation. *)
Definition sum_neg_strong
  :  forall x : E, { y | sum_is_inv x y }
  := Abelian_Group.op_neg_strong sum_abelian_group.

(** Represents negation. *)
Definition sum_neg 
  :  E -> E
  := Abelian_Group.op_neg sum_abelian_group.

Notation "{-}" := (sum_neg) : ring_scope.

Notation "- x" := (sum_neg x) : ring_scope.

(**
  Asserts that the negation returns the inverse
  of its argument.
*)
Definition sum_neg_def 
  :  forall x : E, sum_is_inv x (- x)
  := Abelian_Group.op_neg_def sum_abelian_group.

(** Proves that negation is one-to-one *)
Definition sum_neg_inj
  :  is_injective E E {-}
  := Abelian_Group.op_neg_inj sum_abelian_group.

(** Proves the cancellation property for negation. *)
Theorem sum_cancel_neg
  :  forall x : E, - (- x) = x.
Proof Abelian_Group.op_cancel_neg sum_abelian_group.

(** Proves that negation is onto *)
Theorem sum_neg_onto
  :  is_onto E E {-}.
Proof Abelian_Group.op_neg_onto sum_abelian_group.

(** Proves that negation is surjective *)
Theorem sum_neg_bijective
  :  is_bijective E E {-}.
Proof Abelian_Group.op_neg_bijective sum_abelian_group.

(** Proves that neg x = y -> neg y = x *)
Theorem sum_neg_rev
  :  forall x y : E, - x = y -> - y = x.
Proof Abelian_Group.op_neg_rev sum_abelian_group.

(**
  Proves that the left inverse of x + y is -y + -x.
*)
Theorem sum_neg_distrib_inv_l
  :  forall x y : E, sum_is_inv_l (x + y) (- y + - x).
Proof Abelian_Group.op_neg_distrib_inv_l sum_abelian_group.

(**
  Proves that the right inverse of x + y is -y + -x.
*)
Theorem sum_neg_distrib_inv_r
  :  forall x y : E, sum_is_inv_r (x + y) (- y + - x).
Proof Abelian_Group.op_neg_distrib_inv_r sum_abelian_group.

(**
  Proves that the inverse of x + y is -y + -x.
*)
Theorem sum_neg_distrib_inv
  :  forall x y : E, sum_is_inv (x + y) (- y + - x).
Proof Abelian_Group.op_neg_distrib_inv sum_abelian_group.

(**
  Proves that negation is distributive: i.e.
  -(x + y) = -y + -x.
*)
Theorem sum_neg_distrib
  :  forall x y : E, - (x + y) = - y + - x.
Proof Abelian_Group.op_neg_distrib sum_abelian_group.

(** Proves that 0's negation is 0. *)
Theorem sum_0_neg
  :  - 0 = 0.
Proof
  proj2 (sum_neg_def 0)
  || a = 0 @a by <- sum_id_l (- 0).

(**
  Proves that if an element's, x, negation
  equals 0, x must equal 0.
*)
Theorem sum_neg_0
  :  forall x : E, - x = 0 -> x = 0.
Proof
  fun x H
    => proj2 (sum_neg_def x)
      || x + a = 0 @a by <- H
      || a = 0     @a by <- sum_id_r x.

(**
  Prove that 0 is the only element whose additive
  inverse (negation) equals 0.
*)
Theorem sum_neg_0_uniq
  :  unique (fun x => - x = 0) 0.
Proof
  conj sum_0_neg 
    (fun x H => eq_sym (sum_neg_0 x H)).

(**
  Accepts one element, x, and asserts
  that x is the left identity element.
*)
Definition prod_is_id_l := Monoid.is_id_l E prod.

(**
  Accepts one element, x, and asserts
  that x is the right identity element.
*)
Definition prod_is_id_r := Monoid.is_id_r E prod.

(**
  Accepts one element, x, and asserts
  that x is the identity element.
*)
Definition prod_is_id := Monoid.is_id E prod.

(** Represents the monoid formed by op over E. *)
Definition prod_monoid := Monoid.monoid E 1 {#} prod_is_assoc prod_id_l prod_id_r.

(** Proves that 1 is the identity element. *)
Theorem prod_id
  :  prod_is_id 1.
Proof Monoid.op_id prod_monoid.

(** Proves that the left identity element is unique. *)
Theorem prod_id_l_uniq
  :  forall x : E, (Monoid.is_id_l E prod x) -> x = 1.
Proof Monoid.op_id_l_uniq prod_monoid.

(** Proves that the right identity element is unique. *)
Theorem prod_id_r_uniq
  :  forall x : E, (Monoid.is_id_r E prod x) -> x = 1.
Proof Monoid.op_id_r_uniq prod_monoid.

(** Proves that the identity element is unique. *)
Theorem prod_id_uniq
  :  forall x : E, (Monoid.is_id E prod x) -> x = 1.
Proof Monoid.op_id_uniq prod_monoid.

(** Proves the left introduction rule. *)
Theorem prod_intro_l
  :  forall x y z : E, x = y -> z # x = z # y.
Proof Monoid.op_intro_l prod_monoid.

(** Proves the right introduction rule. *)
Theorem prod_intro_r
  :  forall x y z : E, x = y -> x # z = y # z.
Proof Monoid.op_intro_r prod_monoid.

(**
  Accepts two elements, x and y, and
  asserts that y is x's left inverse.
*)
Definition prod_is_inv_l := Monoid.op_is_inv_l prod_monoid.

(**
  Accepts two elements, x and y, and
  asserts that y is x's right inverse.
*)
Definition prod_is_inv_r := Monoid.op_is_inv_r prod_monoid.

(**
  Accepts two elements, x and y, and
  asserts that y is x's inverse.
*)
Definition prod_is_inv := Monoid.op_is_inv prod_monoid.

(**
  Accepts one argument, x, and asserts that
  x has a left inverse.
*)
Definition prod_has_inv_l := Monoid.has_inv_l prod_monoid.

(**
  Accepts one argument, x, and asserts that
  x has a right inverse.
*)
Definition prod_has_inv_r := Monoid.has_inv_r prod_monoid.

(**
  Accepts one argument, x, and asserts that
  x has an inverse.
*)
Definition prod_has_inv := Monoid.has_inv prod_monoid.

(**
  Proves that the left and right inverses of
  an element must be equal.
*)
Theorem prod_inv_l_r_eq
  :  forall x y : E, prod_is_inv_l x y -> forall z : E, prod_is_inv_r x z -> y = z.
Proof Monoid.op_inv_l_r_eq prod_monoid.

(**
  Proves that the inverse relationship is
  symmetric.
*)
Theorem prod_inv_sym
  :  forall x y : E, prod_is_inv x y <-> prod_is_inv y x.
Proof Monoid.op_inv_sym prod_monoid.

(**
  Proves the left cancellation law for elements
  possessing a left inverse.
*)
Theorem prod_cancel_l
  :  forall x y z : E, prod_has_inv_l z -> z # x = z # y -> x = y.
Proof Monoid.op_cancel_l prod_monoid.

(**
  Proves the right cancellation law for
  elements possessing a right inverse.
*)
Theorem prod_cancel_r 
  :  forall x y z : E, prod_has_inv_r z -> x # z = y # z -> x = y.
Proof Monoid.op_cancel_r prod_monoid.

(**
  Proves that an element's left inverse
  is unique.
*)
Theorem prod_inv_l_uniq
  :  forall x : E, prod_has_inv_r x -> forall y z : E, prod_is_inv_l x y -> prod_is_inv_l x z -> z = y.
Proof Monoid.op_inv_l_uniq prod_monoid.

(**
  Proves that an element's right inverse
  is unique.
*)
Theorem prod_inv_r_uniq
  :  forall x : E, prod_has_inv_l x -> forall y z : E, prod_is_inv_r x y -> prod_is_inv_r x z -> z = y.
Proof Monoid.op_inv_r_uniq prod_monoid.

(**
  Proves that an element's inverse is unique.

  Note: this theorem is defined as transparent to
  allow a theorem in the field module to compile.
*)
Definition prod_inv_uniq
  :  forall x y z : E, prod_is_inv x y -> prod_is_inv x z -> z = y
  := Monoid.op_inv_uniq prod_monoid.

(**
  Proves that the identity element is its own
  left inverse.
*)
Theorem prod_inv_1_l
  :  prod_is_inv_l 1 1.
Proof Monoid.op_inv_0_l prod_monoid.

(**
  Proves that the identity element is its own
  right inverse.
*)
Theorem prod_inv_1_r
  :  prod_is_inv_r 1 1.
Proof Monoid.op_inv_0_l prod_monoid.

(**
  Proves that the identity element is its own
  inverse.
*)
Theorem prod_inv_1
  :  prod_is_inv 1 1.
Proof Monoid.op_inv_0 prod_monoid.

(** Proves that 1 has a left multiplicative inverse. *)
Theorem prod_has_inv_l_1
  :  prod_has_inv_l 1.
Proof Monoid.op_has_inv_l_0 prod_monoid.

(** Proves that 1 has a right multiplicative inverse. *)
Theorem prod_has_inv_r_1
  :  prod_has_inv_r 1.
Proof Monoid.op_has_inv_r_0 prod_monoid.

(** Proves that 1 has a reciprical *)
Theorem prod_has_inv_1
  :  prod_has_inv 1.
Proof Monoid.op_has_inv_0 prod_monoid.

(**
  Proves that if an element's, x, inverse
  equals 0, x equals 0.
*)
Theorem prod_inv_1_eq_1
  :  forall x : E, prod_is_inv x 1 -> x = 1.
Proof Monoid.op_inv_0_eq_0 prod_monoid.

(**
  Proves that 0 is the only element whose
  inverse is 0.
*)
Theorem prod_inv_1_uniq
  :  unique (fun x => prod_is_inv x 1) 1.
Proof Monoid.op_inv_0_uniq prod_monoid.

(** Proves that 1 is its own left multiplicative inverse. *)
Theorem recipr_1_l
  :  prod_is_inv_l 1 1.
Proof Monoid.op_inv_0_l prod_monoid.

(** Proves that 1 is its own right multiplicative inverse. *)
Theorem recipr_1_r
  :  prod_is_inv_r 1 1.
Proof Monoid.op_inv_0_r prod_monoid.

(** Proves that 1 is its own recriprical. *)
Theorem recipr_1
  :  prod_is_inv 1 1.
Proof Monoid.op_inv_0 prod_monoid.

(** TODO Reciprical functions (op_neg) from Monoid. *)

(**
  Asserts that multiplication is
  distributive over addition.
*)
Theorem prod_sum_distrib
  :  is_distrib E prod sum.
Proof conj prod_sum_distrib_l prod_sum_distrib_r.

(**
  Proves that 0 times every number equals 0.

  0 x = 0 x
  (0 + 0) x = 0 x
  0 x + 0 x = 0 x
        0 x = 0
*)
Theorem prod_0_l
  :  forall x : E, 0 # x = 0.
Proof
  fun x
    => let H
         : (0 # x) + (0 # x) = (0 # x) + 0
         := eq_refl (0 # x)
           || a # x = 0 # x         @a by (sum_id_l 0)
           || a = 0 # x             @a by <- prod_sum_distrib_r x 0 0
           || (0 # x) + (0 # x) = a @a by sum_id_r (0 # x)
       in sum_cancel_l (0 # x) 0 (0 # x) H.

(** Proves that 0 times every number equals 0. *)
Theorem prod_0_r
  :  forall x : E, x # 0 = 0.
Proof
  fun x
    => let H
         :  (x # 0) + (x # 0) = 0 + (x # 0)
         := eq_refl (x # 0)
           || x # a = x # 0         @a by sum_id_r 0
           || a = x # 0             @a by <- prod_sum_distrib_l x 0 0
           || (x # 0) + (x # 0) = a @a by sum_id_l (x # 0)
       in sum_cancel_r (x # 0) 0 (x # 0) H.

(**
  Proves that 0 does not have a left
  multiplicative inverse.
*)
Theorem prod_0_inv_l
  :  ~ prod_has_inv_l 0.
Proof
  ex_ind
    (fun x (H : x # 0 = 1)
      => distinct_0_1 (H || a = 1 @a by <- prod_0_r x)).

(**
  Proves that 0 does not have a right
  multiplicative inverse.
*)
Theorem prod_0_inv_r
  :  ~ prod_has_inv_r 0.
Proof
  ex_ind
    (fun x (H : 0 # x = 1)
      => distinct_0_1 (H || a = 1 @a by <- prod_0_l x)).

(**
  Proves that 0 does not have a multiplicative
  inverse - I.E. 0 does not have a
  reciprocal.
*)
Theorem prod_0_inv
  :  ~ prod_has_inv 0.
Proof
  ex_ind
    (fun x H
      => prod_0_inv_l
           (ex_intro
             (fun x
                => prod_is_inv_l 0 x)
             x (proj1 H))).

(**
  Proves that multiplicative inverses, when
  they exist are always nonzero.
*)
Theorem prod_inv_0
  :  forall x y : E, prod_is_inv x y -> nonzero y.
Proof
  fun x y H (H0 : y = 0)
    => distinct_0_1
         (proj1 H
          || a # x = 1 @a by <- H0
          || a = 1     @a by <- prod_0_l x).

(** Represents -1 and proves that it exists. *)
Definition E_n1_strong
  :  { x : E | sum_is_inv 1 x }
  := constructive_definite_description (sum_is_inv 1) (sum_inv_uniq_ex 1).

(** Represents -1. *)
Definition E_n1 : E := proj1_sig E_n1_strong.

(**
  Defines a symbolic representation for -1
  
  Note: here we represent the inverse of 1
  rather than the negation of 1. Letter we prove
  that the negation equals the inverse.

  Note: brackets are needed to ensure Coq parses
  the symbol as a single token instead of a
  prefixed function call.
*)
Notation "{-1}" := E_n1 : ring_scope.

(** Asserts that -1 is the additive inverse of 1. *)
Theorem E_n1_def
  :  sum_is_inv 1 {-1}.
Proof proj2_sig E_n1_strong.

(** Asserts that -1 is the left inverse of 1. *)
Theorem E_n1_inv_l
  :  sum_is_inv_l 1 {-1}.
Proof proj1 E_n1_def.

(** Asserts that -1 is the right inverse of 1. *)
Theorem E_n1_inv_r
  :  sum_is_inv_r 1 {-1}.
Proof proj2 E_n1_def.

(**
  Asserts that every additive inverse
  of 1 must be equal to -1.
*)
Theorem E_n1_uniq
  :  forall x : E, sum_is_inv 1 x -> x = {-1}.
Proof fun x => sum_inv_uniq 1 {-1} x E_n1_def.

(**
  Proves that -1 * x equals the multiplicative
  inverse of x.

  -1 x + x = 0
  -1 x + 1 x = 0
  (-1 + 1) x = 0
  0 x = 0
  0 = 0
*) 
Theorem prod_n1_x_inv_l
  :  forall x : E, sum_is_inv_l x ({-1} # x).
Proof
  fun x
    => prod_0_l x
       || a # x = 0          @a by E_n1_inv_l
       || a = 0              @a by <- prod_sum_distrib_r x {-1} 1
       || ({-1} # x) + a = 0 @a by <- prod_id_l x.

(**
  Proves that x * -1 equals the multiplicative
  inverse of x.

  x -1 + x = 0
*)
Theorem prod_x_n1_inv_l
  :  forall x : E, sum_is_inv_l x (x # {-1}).
Proof
  fun x
    => prod_0_r x
       || x # a = 0          @a by E_n1_inv_l
       || a = 0              @a by <- prod_sum_distrib_l x {-1} 1
       || (x # {-1}) + a = 0 @a by <- prod_id_r x.

(** Proves that x + -1 x = 0. *)
Theorem prod_n1_x_inv_r
  :  forall x : E, sum_is_inv_r x ({-1} # x).
Proof
  fun x
    => prod_0_l x
       || a # x = 0          @a by E_n1_inv_r
       || a = 0              @a by <- prod_sum_distrib_r x 1 {-1}
       || a + ({-1} # x) = 0 @a by <- prod_id_l x.

(** Proves that x + x -1 = 0. *)
Theorem prod_x_n1_inv_r
  :  forall x : E, sum_is_inv_r x (x # {-1}).
Proof
  fun x
    => prod_0_r x
       || x # a = 0          @a by E_n1_inv_r
       || a = 0              @a by <- prod_sum_distrib_l x 1 {-1}
       || a + (x # {-1}) = 0 @a by <- prod_id_r x.

(** Proves that -1 x is the additive inverse of x. *)
Theorem prod_n1_x_inv
  :  forall x : E, sum_is_inv x ({-1} # x).
Proof fun x => conj (prod_n1_x_inv_l x) (prod_n1_x_inv_r x).

(** Proves that x -1 is the additive inverse of x. *)
Theorem prod_x_n1_inv
  :  forall x : E, sum_is_inv x (x # {-1}).
Proof fun x => conj (prod_x_n1_inv_l x) (prod_x_n1_inv_r x).

(**
  Proves that multiplying by -1 is equivalent
  to negation.
*)
Theorem prod_n1_neg
  :  prod {-1} = {-}.
Proof
  functional_extensionality
    (prod {-1}) {-}
    (fun x
      => sum_inv_uniq x (- x) ({-1} # x)
           (sum_neg_def x)
           (prod_n1_x_inv x)).

(**
  Accepts one element, x, and proves that
  x -1 equals the additive negation of x.
*)
Theorem prod_x_n1_neg
  :  forall x : E, x # {-1} = - x.
Proof
  fun x
    => sum_inv_uniq x (- x) (x # {-1})
         (sum_neg_def x)
         (prod_x_n1_inv x).

(**
  Accepts one element, x, and proves that
  -1 x equals the additive negation of x.
*)
Theorem prod_n1_x_neg
  :  forall x : E, {-1} # x = - x.
Proof
  fun x
    => sum_inv_uniq x (- x) ({-1} # x)
         (sum_neg_def x)
         (prod_n1_x_inv x).

(** Proves that -1 x = x -1. *)
Theorem prod_n1_eq
  :  forall x : E, {-1} # x = x # {-1}.
Proof
  fun x
    => sum_inv_uniq x (x # {-1}) ({-1} # x)
         (prod_x_n1_inv x)
         (prod_n1_x_inv x).

(** Proves that the additive negation of 1 equals -1. *)
Theorem neg_1
  :  {-} 1 = {-1}.
Proof
  eq_refl ({-} 1)
    || {-} 1 = a @a by prod_x_n1_neg 1
    || {-} 1 = a @a by <- prod_id_l {-1}.

(** Proves that the additive negation of -1 equals 1. *)
Theorem neg_n1
  :  {-} {-1} = 1.
Proof sum_neg_rev 1 {-1} neg_1.

(**
  Proves that -1 * -1 = 1.

  -1 * -1 = -1 * -1
  -1 * -1 = prod -1 -1
  -1 * -1 = - -1
  -1 * -1 = 1 
*)
Theorem prod_n1_n1
  :  {-1} # {-1} = 1.
Proof
  eq_refl ({-1} # {-1})
    || {-1} # {-1} = a @a by <- prod_n1_x_neg {-1}
    || {-1} # {-1} = a @a by <- neg_n1.

(**
  Proves that -1 is its own multiplicative
  inverse.
*)
Theorem E_n1_inv
  :  prod_is_inv {-1} {-1}.
Proof conj prod_n1_n1 prod_n1_n1.

End Theorems.

End Ring.

Notation "0" := (Ring.E_0) : ring_scope.

Notation "1" := (Ring.E_1) : ring_scope.

Notation "x + y" := (Ring.sum x y) (at level 50, left associativity) : ring_scope.

Notation "{+}" := (Ring.sum) : ring_scope.

Notation "{-}" := (Ring.sum_neg _) : ring_scope.

Notation "- x" := (Ring.sum_neg _ x) : ring_scope.

Notation "x # y" := (Ring.prod x y) (at level 50, left associativity) : ring_scope.

Notation "{#}" := (Ring.prod) : ring_scope.
