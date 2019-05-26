(**
  Every monoid has a nonempty subgroup consisting of the monoid's
  invertible elements.

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

Require Import base.
Require Import monoid.
Require Import group.
Require Import Eqdep.

Module Monoid_Group.

(**
  Represents the homomorphic mapping between
  the set of invertible elements within a monoid
  and the group formed over them by the monoid
  operation.
*)
Structure Monoid_Group : Type := monoid_group {

  (** Represents the set of monoid elements. *)
  E : Set;

  (** Represents the identity monoid element. *)
  E_0 : E;

  (** Represents the monoid operation. *)
  monoid_op: E -> E -> E;

  (** Asserts that the monoid operator is associative. *)
  monoid_op_is_assoc : Monoid.is_assoc E monoid_op;

  (**
    Accepts one monoid element, x, and asserts
    that x is the left identity element.
  *)
  monoid_op_is_id_l := Monoid.is_id_l E monoid_op;

  (**
    Accepts one monoid element, x, and asserts
    that x is the right identity element.
  *)
  monoid_op_is_id_r := Monoid.is_id_r E monoid_op;

  (**
    Accepts one monoid element, x, and asserts
    that x is the identity element.
  *)
  monoid_op_is_id := Monoid.is_id E monoid_op;

  (** Asserts that 0 is the left identity monoid element. *)
  monoid_op_id_l : Monoid.is_id_l E monoid_op E_0;

  (** Asserts that 0 is the right identity monoid element. *)
  monoid_op_id_r : Monoid.is_id_r E monoid_op E_0;

  (**
    Represents the monoid whose invertable
    elements we are going to map onto a group.
  *)
  m := Monoid.monoid E E_0 monoid_op monoid_op_is_assoc monoid_op_id_l monoid_op_id_r;

  (**
    Represents those monoid elements that are
    invertable.

    Note: each value can be seen intuitively as
    a pair, (x, H), where x is a monoid element
    and H is a proof that x is invertable.
  *)
  D : Set
    := { x : E | Monoid.has_inv m x };

  (**
    Accepts a monoid element and a proof that
    it is invertable and returns its projection
    in D.
  *)
  D_cons
    :  forall x : E, Monoid.has_inv m x -> D
    := exist (Monoid.has_inv m);

  (**
    Asserts that any two equal invertable monoid
    elements, x and y, are equivalent (using
    dependent equality).

    Note: to compare sig elements that differ
    only in their proof terms, such as (x, H) and
    (x, H0), we must introduce a new notion of
    equality called "dependent equality". This
    relationship is defined in the Eqdep module.
  *)
  D_eq_dep
    : forall (x : E) (H : Monoid.has_inv m x) (y : E) (H0 : Monoid.has_inv m y), y = x -> eq_dep E (Monoid.has_inv m) y H0 x H;

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
  D_eq
    :  forall (x : E) (H : Monoid.has_inv m x) (y : E) (H0 : Monoid.has_inv m y), y = x -> D_cons y H0 = D_cons x H
    := fun x H y H0 H1
         => eq_dep_ind E (Monoid.has_inv m) y H0
              (fun (z : E) (H2 : Monoid.has_inv m z)
                => D_cons y H0 = D_cons z H2)
              (eq_refl (D_cons y H0)) x H (D_eq_dep x H y H0 H1);

  (**
    Represents the group identity element.
  *)
  D_0 := D_cons E_0 (Monoid.op_has_inv_0 m);

  (**
    Represents the group operation.

    Note: intuitively this function accepts two
    invertable monoid elements, (x, H) and (y,
    H0), and returns (x + y, H1), where H, H0,
    and H1 are generalized invertability proofs.
  *)
  group_op
    :  D -> D -> D
    := sig_rec
         (fun _ => D -> D)
         (fun (u : E) (H : Monoid.has_inv m u)
           => sig_rec
                (fun _ => D)
                (fun (v : E) (H0 : Monoid.has_inv m v)
                  => D_cons
                       (monoid_op u v)
                       (Monoid.op_inv_closed m u H v H0)));


  (**
    Accepts a group element, x, and asserts
    that x is a left identity element.
  *)
  group_op_is_id_l := Monoid.is_id_l D group_op;

  (**
    Accepts a group element, x, and asserts
    that x is a right identity element.
  *)
  group_op_is_id_r := Monoid.is_id_r D group_op;

  (**
    Accepts a group element, x, and asserts
    that x is an/the identity element.
  *)
  group_op_is_id := Monoid.is_id D group_op;

  (** Proves that D_0 is a left identity element. *)
  group_op_id_l
    :  group_op_is_id_l D_0
    := sig_ind
         (fun x => group_op D_0 x = x)
         (fun (u : E) (H : Monoid.has_inv m u)
            => D_eq u H (monoid_op E_0 u) (Monoid.op_inv_closed m E_0 (Monoid.op_has_inv_0 m) u H)
                 (monoid_op_id_l u));

  (** Proves that D_0 is a right identity element. *)
  group_op_id_r
    :  group_op_is_id_r D_0
    := sig_ind
         (fun x => group_op x D_0 = x)
         (fun (u : E) (H : Monoid.has_inv m u)
            => D_eq u H (monoid_op u E_0) (Monoid.op_inv_closed m u H E_0 (Monoid.op_has_inv_0 m))
                 (monoid_op_id_r u));

  (** Proves that D_0 is the identity element. *)
  group_op_id
    :  group_op_is_id D_0
    := conj group_op_id_l group_op_id_r;

  (**
    Proves that the group operation is
    associative.
  *)
  group_op_assoc
    :  Monoid.is_assoc D group_op
    := sig_ind
         (fun x => forall y z : D, group_op x (group_op y z) = group_op (group_op x y) z)
         (fun (u : E) (H : Monoid.has_inv m u)
           => sig_ind
                (fun y => forall z : D, group_op (D_cons u H) (group_op y z) = group_op (group_op (D_cons u H) y) z)
                (fun (v : E) (H0 : Monoid.has_inv m v)
                  => sig_ind
                       (fun z => group_op (D_cons u H) (group_op (D_cons v H0) z) = group_op (group_op (D_cons u H) (D_cons v H0)) z)
                       (fun (w : E) (H1 : Monoid.has_inv m w)
                         => let a
                              :  E
                              := monoid_op u (monoid_op v w) in
                            let H2
                              :  Monoid.has_inv m a
                              := Monoid.op_inv_closed m u H (monoid_op v w) (Monoid.op_inv_closed m v H0 w H1) in
                            let b
                              :  E
                              := monoid_op (monoid_op u v) w in
                            let H3
                              :  Monoid.has_inv m b
                              := Monoid.op_inv_closed m (monoid_op u v) (Monoid.op_inv_closed m u H v H0) w H1 in
                            let X
                              :  D
                              := D_cons a H2 in
                            let Y
                              :  D
                              := D_cons b H3 in
                            D_eq b H3 a H2
                              (monoid_op_is_assoc u v w)
                )));

  (**
    Accepts two values, x and y, and asserts
    that y is a left inverse of x.
  *)
  group_op_is_inv_l := Monoid.is_inv_l D group_op D_0 group_op_id;

  (**
    Accepts two values, x and y, and asserts
    that y is a right inverse of x.
  *)
  group_op_is_inv_r := Monoid.is_inv_r D group_op D_0 group_op_id;

  (**
    Accepts two values, x and y, and asserts
    that y is an inverse of x.
  *)
  group_op_is_inv := Monoid.is_inv D group_op D_0 group_op_id;

  (**
    Accepts two invertable monoid elements, x
    and y, where y is a left inverse of x and
    proves that y's projection into D is the
    left inverse of x's.
  *)
  group_op_inv_l
    :  forall (u : E) (H : Monoid.has_inv m u) (v : E) (H0 : Monoid.has_inv m v),
         Monoid.op_is_inv_l m u v ->
         group_op_is_inv_l (D_cons u H) (D_cons v H0)
    := fun (u : E) (H : Monoid.has_inv m u) (v : E) (H0 : Monoid.has_inv m v)
         => D_eq E_0 (Monoid.op_has_inv_0 m) (monoid_op v u) (Monoid.op_inv_closed m v H0 u H);
        
  (**
    Accepts two invertable monoid elements, x
    and y, where y is a right inverse of x and
    proves that y's projection into D is the
    right inverse of x's.
  *)
  group_op_inv_r
    :  forall (u : E) (H : Monoid.has_inv m u) (v : E) (H0 : Monoid.has_inv m v),
         Monoid.op_is_inv_r m u v ->
         group_op_is_inv_r (D_cons u H) (D_cons v H0)
    := fun (u : E) (H : Monoid.has_inv m u) (v : E) (H0 : Monoid.has_inv m v)
         => D_eq E_0 (Monoid.op_has_inv_0 m) (monoid_op u v) (Monoid.op_inv_closed m u H v H0);

  (**
    Accepts two invertable monoid elements, x
    and y, where y is the inverse of x and
    proves that y's projection into D is the
    inverse of x's.
  *)
  group_op_inv
    :  forall (u : E) (H : Monoid.has_inv m u) (v : E) (H0 : Monoid.has_inv m v),
         Monoid.op_is_inv m u v ->
         group_op_is_inv (D_cons u H) (D_cons v H0)
    := fun (u : E) (H : Monoid.has_inv m u) (v : E) (H0 : Monoid.has_inv m v) (H1 : Monoid.op_is_inv m u v)
         => conj (group_op_inv_l u H v H0 (proj1 H1))
                 (group_op_inv_r u H v H0 (proj2 H1));

  (**
    Accepts a group element and returns its
    inverse, y, along with a proof that y is
    x's inverse.
  *)
  group_op_neg_strong
    :  forall x : D, { y : D | group_op_is_inv x y }
    := sig_rec
         (fun x => { y : D | group_op_is_inv x y })
         (fun (u : E) (H : Monoid.has_inv m u)
           => let v
                :  E
                := Monoid.op_neg m u H in
              let H0
                :  Monoid.op_is_inv m u v
                := Monoid.op_neg_def m u H in
              let H1
                :  Monoid.has_inv m v
                := Monoid.op_neg_inv_ex m u H in
              exist
                (fun y : D => group_op_is_inv (D_cons u H) y)
                (D_cons v H1)
                (group_op_inv u H v H1 H0));

  (**
    Proves that every group element has an
    inverse.
  *)
  group_op_inv_ex 
    :  forall x : D, exists y : D, group_op_is_inv x y
    := fun x
         => let (y, H) := group_op_neg_strong x in
            ex_intro
              (fun y => group_op_is_inv x y)
              y H;

  (**
    Proves that every group element has a left
    inverse.
  *)
  group_op_inv_l_ex
    :  forall x : D, exists y : D, group_op_is_inv_l x y
    := fun x
         => ex_ind
              (fun y (H : group_op_is_inv x y)
                => ex_intro (fun z => group_op_is_inv_l x z) y (proj1 H))
              (group_op_inv_ex x);

  (**
    Proves that every group element has a right
    inverse.
  *)
  group_op_inv_r_ex
    :  forall x : D, exists y : D, group_op_is_inv_r x y
    := fun x
         => ex_ind
              (fun y (H : group_op_is_inv x y)
                => ex_intro (fun z => group_op_is_inv_r x z) y (proj2 H))
              (group_op_inv_ex x);

  (**
    Proves that the set of invertable monoid
    elements form a group over the monoid
    operation.
  *)
  g := Group.group D D_0 group_op group_op_assoc
    group_op_id_l group_op_id_r group_op_inv_l_ex
    group_op_inv_r_ex
}.

End Monoid_Group.
