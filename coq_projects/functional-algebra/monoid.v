(**
  This module defines the Monoid record type which represents
  algebraic structures called Monoids and provides a collection of
  theorems and axioms describing them.

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
Require Import ProofIrrelevance.
Require Import Bool.

Require Import Arith.
Require Import Wf.
Require Import Wellfounded.
Require Import Wf_nat.

Module Monoid.

(** Accepts a function, f, and asserts that f is associative. *)
Definition is_assoc (T : Type) (f : T -> T -> T) : Prop := forall x y z : T, f x (f y z) = f (f x y) z.

(**
  Accepts two arguments, f and x, and asserts
  that x is a left identity element w.r.t. f.
*)
Definition is_id_l (T : Type) (f : T -> T -> T) (E : T) : Prop := forall x : T, f E x = x.

(**
  Accepts two arguments, f and x, and asserts
  that x is a right identity element w.r.t. f.
*)
Definition is_id_r (T : Type) (f : T -> T -> T) (E : T) : Prop := forall x : T, f x E = x.

(**
  Accepts two arguments, f and x, and asserts
  that x is an identity element w.r.t. f.
*)
Definition is_id (T : Type) (f : T -> T -> T) (E : T) : Prop := is_id_l T f E /\ is_id_r T f E.

(**
  Accepts three arguments, f, e, and H, where
  H proves that e is the identity element
  w.r.t. f, and returns a function that accepts
  two arguments, x and y, and asserts that y is
  x's left inverse.
*)
Definition is_inv_l (T : Type) (f : T -> T -> T) (E : T) (_ : is_id T f E) (x y : T) : Prop := f y x = E.

(**
  Accepts three arguments, f, e, and H, where
  H proves that e is the identity element
  w.r.t. f, and returns a function that accepts
  two arguments, x and y, and asserts that y is
  x's right inverse.
*)
Definition is_inv_r (T : Type) (f : T -> T -> T) (E : T) (_ : is_id T f E) (x y : T) : Prop := f x y = E.

(**
  Accepts three arguments, f, e, and H, where
  H proves that e is the identity element
  w.r.t. f, and returns a function that accepts
  two arguments, x and y, and asserts that y is
  x's inverse.
*)
Definition is_inv (T : Type) (f : T -> T -> T) (E : T) (H : is_id T f E) (x y : T) : Prop := is_inv_l T f E H x y /\ is_inv_r T f E H x y.

(** Represents algebraic monoids. *)
Structure Monoid : Type := monoid {

  (** Represents the set of monoid elements. *)
  E: Set;

  (** Represents the identity element. *)
  E_0: E;

  (** Represents the monoid operation. *)
  op: E -> E -> E;

  (** Asserts that the monoid operator is associative. *)
  op_is_assoc : is_assoc E op;

  (** Asserts that E_0 is the left identity element. *)
  op_id_l : is_id_l E op E_0;

  (** Asserts that E_0 is the right identity element. *)
  op_id_r : is_id_r E op E_0
}.

(** Enable implicit arguments for monoid properties. *)

Arguments E_0 {m}.

Arguments op {m} x y.

Arguments op_is_assoc {m} x y z.

Arguments op_id_l {m} x.

Arguments op_id_r {m} x.

(** Define notations for monoid properties. *)

Notation "0" := E_0 : monoid_scope.

Notation "x + y" := (op x y) (at level 50, left associativity) : monoid_scope.

Notation "{+}" := op : monoid_scope.

Open Scope monoid_scope.

Section Theorems.

(**
  Represents an arbitrary monoid.

  Note: we use Variable rather than Parameter
  to ensure that the following theorems are
  generalized w.r.t m.
*)
Variable m : Monoid.

(** Represents the set of monoid elements. *)
Let M := E m.

(**
  Accepts one monoid element, x, and asserts
  that x is the left identity element.
*)
Definition op_is_id_l := is_id_l M {+}.

(**
  Accepts one monoid element, x, and asserts
  that x is the right identity element.
*)
Definition op_is_id_r := is_id_r M {+}.

(**
  Accepts one monoid element, x, and asserts
  that x is the identity element.
*)
Definition op_is_id := is_id M {+}.

(** Proves that 0 is the identity element. *)
Theorem op_id
  :  is_id M {+} 0.
Proof conj op_id_l op_id_r.

(** Proves that the left identity element is unique. *)
Theorem op_id_l_uniq
  :  forall x : M, (op_is_id_l x) -> x = 0.
Proof
  fun x H
    => H 0 || a = 0 @a by <- op_id_r x.

(** Proves that the right identity element is unique. *)
Theorem op_id_r_uniq
  :  forall x : M, (op_is_id_r x) -> x = 0.
Proof
  fun x H
    => H 0 || a = 0 @a by <- op_id_l x.

(** Proves that the identity element is unique. *)
Theorem op_id_uniq
  :  forall x : M, (op_is_id x) -> x = 0.
Proof
  fun x
    => and_ind (fun H _ => op_id_l_uniq x H).

(** Proves the left introduction rule. *)
Theorem op_intro_l
  :  forall x y z : M, x = y -> z + x = z + y.
Proof
  fun x y z H
    => f_equal ({+} z) H.

(** Proves the right introduction rule. *)
Theorem op_intro_r
  :  forall x y z : M, x = y -> x + z = y + z.
Proof
  fun x y z H
    =>  eq_refl (x + z)
       || x + z = a + z @a by <- H.

(**
  Accepts two monoid elements, x and y, and
  asserts  that y is x's left inverse.
*)
Definition op_is_inv_l := is_inv_l M {+} 0 op_id.

(**
  Accepts two monoid elements, x and y, and
  asserts  that y is x's right inverse.
*)
Definition op_is_inv_r := is_inv_r M {+} 0 op_id.

(**
  Accepts two monoid elements, x and y, and
  asserts  that y is x's inverse.
*)
Definition op_is_inv := is_inv M {+} 0 op_id.

(**
  Accepts one argument, x, and asserts that
  x has a left inverse.
*)
Definition has_inv_l
  := fun x => exists y : M, op_is_inv_l x y.

(**
  Accepts one argument, x, and asserts that
  x has a right inverse.
*)
Definition has_inv_r
  := fun x => exists y : M, op_is_inv_r x y.

(**
  Accepts one argument, x, and asserts that
  x has an inverse.
*)
Definition has_inv
  := fun x => exists y : M, op_is_inv x y.

(**
  Proves that the left and right inverses of
  an element must be equal.
*)
Theorem op_inv_l_r_eq
  :  forall x y : M, op_is_inv_l x y -> forall z : M, op_is_inv_r x z -> y = z.
Proof
  fun x y H1 z H2
    => op_is_assoc y x z
          || y + a = (y + x) + z @a by <- H2
          || a = (y + x) + z     @a by <- op_id_r y
          || y = a + z           @a by <- H1
          || y = a               @a by <- op_id_l z.

(**
  Proves that the inverse relationship is
  symmetric.
*)
Theorem op_inv_sym
  :  forall x y : M, op_is_inv x y <-> op_is_inv y x.
Proof
  fun x y
    => conj
            (fun H : op_is_inv x y
              => conj (proj2 H) (proj1 H))
            (fun H : op_is_inv y x
              => conj (proj2 H) (proj1 H)).

(**
  The next few lemmas define special cases
  where cancellation holds and culminate in
  the Unique Inverse theorem which asserts
  that, in a Monoid, every value has at most
  one inverse.
*)

(**
  Proves the left cancellation law for elements
  possessing a left inverse.
*)
Theorem op_cancel_l
  :  forall x y z : M, has_inv_l z -> z + x = z + y -> x = y.
Proof
  fun x y z H H0
    => ex_ind 
            (fun u H1
              => op_intro_l (z + x) (z + y) u H0
              || a = u + (z + y) @a by <- op_is_assoc u z x
              || (u + z) + x = a @a by <- op_is_assoc u z y
              || a + x = a + y   @a by <- H1
              || a = 0 + y       @a by <- op_id_l x
              || x = a           @a by <- op_id_l y)
            H.

(**
  Proves the right cancellation law for
  elements possessing a right inverse.
*)
Theorem op_cancel_r
  :  forall x y z : M, has_inv_r z -> x + z = y + z -> x = y.
Proof
  fun x y z H H0
    => ex_ind
            (fun u H1
              =>  op_intro_r (x + z) (y + z) u H0
              || a = (y + z) + u @a by op_is_assoc x z u
              || x + (z + u) = a @a by op_is_assoc y z u
              || x + a = y + a   @a by <- H1
              || a = y + 0       @a by <- op_id_r x
              || x = a           @a by <- op_id_r y)
            H.

(**
  Proves that an element's left inverse
  is unique.
*)
Theorem op_inv_l_uniq
  :  forall x : M, has_inv_r x -> forall y z : M, op_is_inv_l x y -> op_is_inv_l x z -> z = y.
Proof
  fun x H y z H0 H1
    => let H2
            :  z + x = y + x
            := H1 || z + x = a @a by H0 in
          let H3
            :  z = y
            := op_cancel_r z y x H H2 in
          H3.

(**
  Proves that an element's right inverse
  is unique.
*)
Theorem op_inv_r_uniq
  :  forall x : M, has_inv_l x -> forall y z : M, op_is_inv_r x y -> op_is_inv_r x z -> z = y.
Proof
  fun x H y z H0 H1
    => let H2
            :  x + z = x + y
            := H1 || x + z = a @a by H0 in
          let H3
            :  z = y
            := op_cancel_l z y x H H2 in
          H3.

(** Proves that an element's inverse is unique. *)
Theorem op_inv_uniq
  :  forall x y z : M, op_is_inv x y -> op_is_inv x z -> z = y.
Proof
  fun x y z H H0
    => op_inv_l_uniq x
            (ex_intro (fun y => op_is_inv_r x y) y (proj2 H))
            y z (proj1 H) (proj1 H0).

(**
  Proves that the identity element is its own
  left inverse.
*)
Theorem op_inv_0_l
  :  op_is_inv_l 0 0.
Proof op_id_l 0 : 0 + 0 = 0.

(**
  Proves that the identity element is its own
  right inverse.
*)
Theorem op_inv_0_r
  :  op_is_inv_r 0 0.
Proof op_id_r 0 : 0 + 0 = 0.

(**
  Proves that the identity element is its own
  inverse.
*)
Theorem op_inv_0
  :  op_is_inv 0 0.
Proof conj op_inv_0_l op_inv_0_r.

(**
  Proves that the identity element has a
  left inverse.
*)
Theorem op_has_inv_l_0
  :  has_inv_l 0.
Proof ex_intro (op_is_inv_l 0) 0 op_inv_0_l.

(**
  Proves that the identity element has a
  right inverse.
*)
Theorem op_has_inv_r_0
  :  has_inv_r 0.
Proof ex_intro (op_is_inv_r 0) 0 op_inv_0_r.

(**
  Proves that the identity element has an
  inverse.
*)
Theorem op_has_inv_0
  :  has_inv 0.
Proof ex_intro (op_is_inv 0) 0 op_inv_0.

(**
  Proves that if an element's, x, inverse
  equals 0, x equals 0.
*)
Theorem op_inv_0_eq_0
  :  forall x : M, op_is_inv x 0 -> x = 0.
Proof
  fun x H
    => proj1 H
       || a = 0 @a by <- op_id_l x.

(**
  Proves that 0 is the only element whose
  inverse is 0.
*)
Theorem op_inv_0_uniq
  :  unique (fun x => op_is_inv x 0) 0.
Proof
  conj op_inv_0
    (fun x H => eq_sym (op_inv_0_eq_0 x H)).

(**
  Every monoid has a subset of elements that
  possess inverses. This can be seen by noting
  that, by definition, every monoid has an
  identity element (this is what distinguishes
  a monoid from a semigroup) and the identity
  element is its own inverse. The following
  theorems explore the behavior of those
  elements that possess inverses. They will
  prove especially ueseful when we consider
  groups where every element possess an
  inverse.
*)

(**
  Accepts two arguments: x; and H, a proof that
  x has an inverse; and returns x's inverse,
  y, along with a proof that y is x's inverse.
*)
Definition op_neg_strong
  :  forall x : M, has_inv x -> { y | op_is_inv x y }
  := fun x H
       => constructive_definite_description (op_is_inv x) 
            (ex_ind
              (fun y (H0 : op_is_inv x y)
                => ex_intro
                     (fun y => op_is_inv x y /\ forall z, op_is_inv x z -> y = z)
                     y
                     (conj H0 (fun z H1 => eq_sym (op_inv_uniq x y z H0 H1))))
              H).

(**
  Accepts two arguments: x; and H, a proof that
  x has an inverse. and returns x's inverse.
*)
Definition op_neg
  :  forall x : M, has_inv x -> M
  := fun x H => proj1_sig (op_neg_strong x H).

Notation "{-}" := (op_neg) : monoid_scope.

(**
  Proves that, forall x and H, where H is a
  proof that x has an inverse, `op_neg x H`
  is x's inverse.
*)
Theorem op_neg_def
  :  forall (x : M) (H : has_inv x), op_is_inv x ({-} x H).
Proof
  fun x H
    => proj2_sig (op_neg_strong x H).

(**
  Proves that, forall x and H, where H is
  a proof that x has an inverse, x is the
  inverse of `- x H`.

  Note: this lemma is an immediate consequence
  of the symmetry of the inverse predicate.
*)
Theorem op_neg_inv
  :  forall (x : M) (H : has_inv x), op_is_inv ({-} x H) x.
Proof
  fun x H
    => (proj1 (op_inv_sym x ({-} x H))) (op_neg_def x H).

(**
  Proves that, forall x and H, where H is a
  proof that x has an inverse, `- x H`
  has an inverse.

  Note: this lemma is a weakening of
  `op_neg_inv` and is used to apply the lemmas
  and theorems in this section to expressions
  involving `op_neg`.
*)
Theorem op_neg_inv_ex
  :  forall (x : M) (H : has_inv x), has_inv ({-} x H).
Proof
  fun x H
    => ex_intro
         (op_is_inv ({-} x H))
         x
         (op_neg_inv x H).

(**
  Proves that negation is injective over the
  set of invertible elements - I.E. forall
  x and y if the negation of x equals the
  negation of y then x and y must be equal.
*)
Theorem op_neg_inj
  :  forall (x : M) (H : has_inv x) (y : M) (H0 : has_inv y),
     {-} x H = {-} y H0 ->
     x = y.
Proof
  fun x H y H0 H1
    => let H2
         :  x + ({-} x H) = y + ({-} x H) 
         := (proj2 (op_neg_def x H) : x + ({-} x H) = 0)
            || x + ({-} x H) = a     @a by proj2 (op_neg_def y H0)
            || x + ({-} x H) = y + a @a by H1 in
       let H3
         :  x = y
         := op_cancel_r x y ({-} x H)
            (ex_intro
              (op_is_inv_r ({-} x H))
              x
              (proj2 (proj1 (op_inv_sym x ({-} x H)) (op_neg_def x H))))
            H2 in
       H3.

(**
  Proves that double negation is equivalent to
  the identity function for all invertible
  values.

  Note: the monoid negation operation
  requires a proof that the value passed to it
  is invertible. The form of this theorem
  explicitly asserts that double negation is
  equivalent to the identity operation for
  any proof that the negative has an inverse.
*)
Theorem op_cancel_neg_gen
  :  forall (x : M) (H : has_inv x) (H0 : has_inv ({-} x H)), {-} ({-} x H) H0 = x.
Proof
  fun x H H0
    => let H1
         :  op_is_inv ({-} x H) ({-} ({-} x H) H0)
         := op_neg_def ({-} x H) H0 in
       let H3
         :  op_is_inv ({-} x H) x
         := op_neg_inv x H in
       op_inv_uniq ({-} x H) x ({-} ({-} x H) H0) H3 H1.

(**
  Proves that double negation is equivalent to
  the identity function for all invertible
  values.
*)
Theorem op_cancel_neg
  :  forall (x : M) (H : has_inv x), {-} ({-} x H) (op_neg_inv_ex x H) = x.
Proof
  fun x H
    => op_cancel_neg_gen x H (op_neg_inv_ex x H).

(**
  Proves that negation is onto over the subset
  of invertable values.
*)
Theorem op_neg_onto
  :  forall (y : M) (H : has_inv y), exists (x : M) (H0 : has_inv x), {-} x H0 = y.
Proof
  fun y H
    => ex_intro
            (fun x => exists H0 : has_inv x, {-} x H0 = y)
            ({-} y H)
            (ex_intro
              (fun H0 => {-} ({-} y H) H0 = y)
              (op_neg_inv_ex y H)
              (op_cancel_neg y H)).

(**
  Proves that invertability is closed over
  the monoid operation.

  Note: given this theorem, we can conclude
  that the set of invertible elements within
  a monoid, which must be nonempty, forms
  a group.
*)
Theorem op_inv_closed
  :  forall (x : M) (H : has_inv x) (y : M) (H0 : has_inv y), has_inv (x + y).
Proof
  fun x H y H0
    => ex_ind
         (fun u (H1 : op_is_inv x u)
           => ex_ind
                (fun v (H2 : op_is_inv y v)
                  => ex_intro
                       (op_is_inv (x + y))
                       (v + u)
                       (conj
                         (op_is_assoc (v + u) x y
                           || (v + u) + (x + y) = a + y @a by op_is_assoc v u x
                           || (v + u) + (x + y) = (v + a) + y @a by <- proj1 H1
                           || (v + u) + (x + y) = a + y @a by <- op_id_r v
                           || (v + u) + (x + y) = a @a by <- proj1 H2
                         ) 
                         (op_is_assoc (x + y) v u
                           || (x + y) + (v + u) = a + u @a by op_is_assoc x y v
                           || (x + y) + (v + u) = (x + a) + u @a by <- proj2 H2
                           || (x + y) + (v + u) = a + u @a by <- op_id_r x
                           || (x + y) + (v + u) = a @a by <- proj2 H1
                         )))
                H0)
         H.

End Theorems.

End Monoid.

(**
  Coq does not export notations outside of
  sections. Consequently the notationsdefined
  above are not visible to other modules. To
  fix this, we gather all the notations here
  for export.
*)

Notation "0" := (Monoid.E_0) : monoid_scope.

Notation "x + y" := (Monoid.op x y) (at level 50, left associativity) : monoid_scope.

Notation "{+}" := (Monoid.op) : monoid_scope.

Notation "{-}" := (Monoid.op_neg _) : monoid_scope.
