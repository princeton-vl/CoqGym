(**
  This module defines concrete expressions that can be used to
  represent monoid values and operations, and includes a collection
  of functions that can be used to manipulate these expressions,
  and a set of theorems describing these functions.

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
Require Import List.
Import ListNotations.
Require Import monoid.
Import Monoid.

Module MonoidExpr.

Open Scope monoid_scope.

(**
  I. This section defines binary trees.
*)
Section binary_trees.

(** Represents the values stored in binary trees. *)
Variable Term : Set.

(**
  Represents binary trees.

  Binary trees can be used to represent
  many different types of algebraic
  expressions. Importantly, when flattened,
  they are isomorphic with lists. Flattening,
  projecting onto lists, sorting, and folding
  may be used normalize ("simplify") algebraic
  expressions.
*)
Inductive BTree : Set
  := leaf : Term -> BTree
  |  node : BTree -> BTree -> BTree.

(**
  Accepts a binary tree and returns true iff
  the tree is a node term.
*)
Definition BTree_is_node
  :  BTree -> bool
  := BTree_rec
       (fun _ => bool)
       (fun _ => false)
       (fun _ _ _ _ => true).

(**
  Accepts a binary tree and returns true iff
  the tree is a leaf term.
*)
Definition BTree_is_leaf
  :  BTree -> bool
  := BTree_rec
       (fun _ => bool)
       (fun _ => true)
       (fun _ _ _ _ => false).

(**
  Accepts a binary tree and returns true
  iff the tree is right associative.

  Note: right associative trees are isomorphic
  to lists.
*)
Definition BTree_is_rassoc
  :  BTree -> bool
  := BTree_rec
       (fun _ => bool)
       (fun _ => true)
       (fun t _ _ f
         => BTree_is_leaf t && f).

(**
  Proves that the right subtree in a right
  associative binary tree is also right
  associative.
*)
Theorem BTree_rassoc_thm
  :  forall t u : BTree, BTree_is_rassoc (node t u) = true -> BTree_is_rassoc u = true.
Proof
  fun t u H
    => proj2 (
            andb_prop 
              (BTree_is_leaf t)
              (BTree_is_rassoc u)
              H).

End binary_trees.

Arguments leaf {Term} x.

Arguments node {Term} t u.

Arguments BTree_is_leaf {Term} t.

Arguments BTree_is_node {Term} t.

Arguments BTree_is_rassoc {Term} t.

Arguments BTree_rassoc_thm {Term} t u H.

(**
  II. Defines term maps which allow us to
    interpret abstract terms as monoid values.
*)

(**
  Represents a mapping from abstract terms
  to monoid set elements.
*)
Structure Term_map : Type := term_map {
  (**
    Represents the monoid set that terms will be 
    projected onto. 
  *)
  term_map_m: Monoid;

  (**
    Represents the set of terms that will be
    used to represent monoid values.
  *)
  term_map_term : Set;

  (**
    Accepts a term and returns its projection
    in E.
  *)
  term_map_eval : term_map_term -> E term_map_m;

  (**
    Accepts a term and returns true iff the term
    represents the monoid identity element (0).
  *)
  term_map_is_zero : term_map_term -> bool;

  (**
    Accepts a term and proves that zero terms
    evaluate to 0.
  *)
  term_map_is_zero_thm : forall t, term_map_is_zero t = true -> term_map_eval t = 0
}.

Arguments term_map_eval {t} x.

Arguments term_map_is_zero {t} x.

Arguments term_map_is_zero_thm {t} t0 H.

(**
  III. Defines functions for evaluating and
    transforming binary trees using term maps.
*) 

Section term_tree_functs.

(**
  Represents an arbitrary homomorphism mapping
  binary trees onto some set.
*)
Variable map : Term_map.

(** Represents the set of monoid values. *)
Let E := E (term_map_m map).

(** Represents the set of terms. *)
Let Term := term_map_term map.

(**
  Accepts a term and returns true iff it is not
  a zero constant term.
*)
Definition Term_is_nonzero
  :  Term -> bool
  := fun t => negb (term_map_is_zero t).

(** Maps binary trees onto monoid expressions. *)
Definition BTree_eval
  :  BTree Term -> E
  := BTree_rec Term
       (fun _ => E)
       (fun t => term_map_eval t)
       (fun _ f _ g => f + g).

(**
  Accepts two monoid expressions and returns
  true iff they are denotationally equivalent -
  I.E. represent the same monoid value.
*)
Definition BTree_eq
  :  BTree Term -> BTree Term -> Prop
  := fun t u => BTree_eval t = BTree_eval u.

(**
  Accepts two binary trees, t and u, where u is
  right associative, prepends t onto u in a way
  that produces a flat list.

  <<
        *          *
       / \        / \
      *   v => (t)   *
     / \             / \ 
    t   u          (u)  v
  >>
*)
Definition BTree_shift
  :  forall (t u : BTree Term), BTree_is_rassoc u = true -> { v : BTree Term | BTree_is_rassoc v = true /\ BTree_eq (node t u) v }
  := let P t u v
       := BTree_is_rassoc v = true /\ BTree_eq (node t u) v in
     let T t u
       := BTree_is_rassoc u = true -> { v | P t u v } in
     BTree_rec Term
       (fun t => forall u, T t u)
       (fun x u H
         => let v := node (leaf x) u in
            exist
              (P (leaf x) u)
              v
              (conj
                (andb_true_intro
                  (conj
                    (eq_refl true : BTree_is_leaf (leaf x) = true)
                    H))
                (eq_refl (BTree_eval v))))
       (fun t f u g v H
         => let (w, H0) := g v H in
            let (x, H1) := f w (proj1 H0) in
            exist
              (P (node t u) v)
              x
              (conj
                (proj1 H1)
                (proj2 H1
                  || BTree_eval t + a = BTree_eval x @a by proj2 H0
                  || a = BTree_eval x @a by <- op_is_assoc (BTree_eval t) (BTree_eval u) (BTree_eval v)))).

(**
  Accepts a binary tree and returns an equivalent
  tree that is right associative.
*)
Definition BTree_rassoc
  :  forall t : BTree Term, { u : BTree Term | BTree_is_rassoc u = true /\ BTree_eq t u }
  := let P t u
       := BTree_is_rassoc u = true /\ BTree_eq t u in
     let T t
       := { u | P t u } in
     BTree_rec Term
       (fun t => T t)
       (fun x
         => let t := leaf x in
            exist
              (P t)
              t
              (conj
                (eq_refl true : BTree_is_leaf t = true) 
                (eq_refl (BTree_eval t))))
       (fun t _ u g
         => let (v, H) := g in
            let (w, H0) := BTree_shift t v (proj1 H) in
            exist
              (P (node t u))
              w
              (conj
                (proj1 H0)
                (proj2 H0
                  || BTree_eval t + a = BTree_eval w @a by (proj2 H)))).

(**
  IV. Defines functions for evaluating and
    transforming lists of terms that can be mapped
    onto monoid values using a term map.


  In the following section, we use the
  isomorphism between right associative binary
  trees and lists to represent monoid expressions
  as lists and to use list filtering to eleminate
  identity elements. This is part of a larger
  effort to "simplify" momoid expressions.
*)

(**
  Accepts a list of monoid elements and computes
  their sum.
*)
Definition list_eval
  :  forall xs : list Term, E
  := list_rec
       (fun _ => E)
       0
       (fun x _ f => (term_map_eval x) + f).

(**
  Accepts two term lists and asserts that they
  are equivalent.
*)
Definition list_eq : list Term -> list Term -> Prop
  := fun xs ys : list Term
       => list_eval xs = list_eval ys.

(**
  Accepts a right associative binary tree and
  returns an equivalent list.
*)
Definition RABTree_list
  :  forall t : BTree Term, BTree_is_rassoc t = true -> { xs : list Term | BTree_eval t = list_eval xs }
  := let P t xs := BTree_eval t = list_eval xs in
     let T t := BTree_is_rassoc t = true -> { xs | P t xs } in
     BTree_rect Term
       (fun t => T t)
       (fun x _
         => let xs := [x] in
            exist
              (P (leaf x))
              xs
              (eq_sym (op_id_r (term_map_eval x))))
       (BTree_rect Term
         (fun t => T t -> forall u, T u -> T (node t u))
         (fun x _ u (g : T u) H
           => let H0
                :  BTree_is_rassoc u = true
                := BTree_rassoc_thm (leaf x) u H in
              let (ys, H1) := g H0 in
              let xs := x :: ys in
              exist
                (P (node (leaf x) u))
                xs
                (eq_refl ((term_map_eval x) + (BTree_eval u))
                  || (term_map_eval x) + (BTree_eval u) = (term_map_eval x) + a @a by <- H1))
         (fun t _ u _ _ v _ H
           => False_rec
                { xs | P (node (node t u) v) xs }
                (diff_false_true H))).

(**
  Accepts a list of monoid elements and filters
  out the 0 (identity) elements.

  Note: to define this function we must have
  a way to recognize identity elements. The
  original definition for monoids did not declare
  0 to be a distinguished element. In part this
  followed from the fact that the set of monoid
  elements was not declared inductively.

  While we cannot assume that models of monoids
  will define their element sets inductively
  (for example, note that reals are not defined
  inductively), we can reasonably expect these
  models to define 0 as a distinguished element.

  As this is somewhat conjectural however,
  we do not add this as a requirement to the
  monoid specification, but instead accept the
  decision procedure here.
*)
Definition list_filter_0
  :  forall xs : list Term, {ys : list Term | list_eq xs ys /\ Is_true (forallb Term_is_nonzero ys)}
  := let P xs ys := list_eq xs ys /\ Is_true (forallb Term_is_nonzero ys) in
     let T xs := { ys | P xs ys } in
     list_rec
       T
       (exist
         (P [])
         []
         (conj
           (eq_refl E_0)
           I))
       (fun x
         => (sumbool_rec
              (fun _ => forall xs : list Term, T xs -> T (cons x xs))
              (fun (H : term_map_is_zero x = true) xs f
                => let H0
                     :  term_map_eval x = 0
                     := term_map_is_zero_thm x H in
                   let (ys, H1) := f in
                   exist
                     (P (x :: xs))
                     ys
                     (conj
                       (op_id_l (list_eval xs)
                         || 0 + (list_eval xs) = a @a by <- (proj1 H1)
                         || a + (list_eval xs) = list_eval ys @a by H0)
                       (proj2 H1)))
              (fun (H : term_map_is_zero x = false) xs f
                => let (ys, H0) := f in
                   let zs := x :: ys in
                   exist
                     (P (x :: xs))
                     zs
                     (conj
                       (eq_refl (list_eval (x :: xs))
                         || term_map_eval x + (list_eval xs) = term_map_eval x + a @a by <- (proj1 H0))
                       (Is_true_eq_left
                         (forallb Term_is_nonzero zs)
                         (andb_true_intro
                           (conj
                             (eq_refl (Term_is_nonzero x)
                               || Term_is_nonzero x = negb a @a by <- H)
                             (Is_true_eq_true
                               (forallb Term_is_nonzero ys)
                               (proj2 H0)))))))
              (bool_dec0 (term_map_is_zero x)))).

(**
  Accepts a binary tree and returns an equivalent
  terms list in which all identity elements have
  been eliminated.
*)
Definition reduce
  :  forall t : BTree Term, { xs : list Term | BTree_eval t = list_eval xs }
  := fun t
       => let (u, H) := BTree_rassoc t in
          let (xs, H0) := RABTree_list u (proj1 H) in
          let (ys, H1) := list_filter_0 xs in
          exist
            (fun ys => BTree_eval t = list_eval ys)
            ys
            ((proj2 H)
              || BTree_eval t = a @a by <- H0
              || BTree_eval t = a @a by <- (proj1 H1)).

End term_tree_functs.

(**
  V. Defines a abstract terms to represent monoid
    expressions, and a term map for mapping these
    terms onto monoid values.
*)
Section monoid_term_map.

(** Represents an arbitrary monoid. *)
Variable m : Monoid.

(** Represents the set of monoid elements. *)
Let E := E m.

(**
  Represents monoid values.

  Note: In the development that follows, we
  will use binary trees and lists to represent
  monoid expressions. We will effectively flatten
  a tree and filter a list to "simplify"
  a given expression.

  The code that flattens the tree representation
  does not need to care whether or not the
  leaves in the tree represent 0 (the monoid
  identity element), inverses, etc. Accordingly,
  distinguishing these elements in the definition
  of BTree would unnecessarily complicate the
  tree algorithms by adding more recursion cases.

  Instead of doing this, we use two types
  to represent monoid expressions - trees to
  represent "terms" (expressions that are summed
  together) and Term. Term tracks whether or
  not a monoid value equals 0 (and later we will
  use a similar structure to indicate whether or
  not a given group element is an inverse). This
  makes this information available when needed
  (specifically when we eliminate 0s using
  list filtering) without complicating the
  tree algorithms.
*)
Inductive Term : Set
  := term_0 : Term
  |  term_const : E -> Term.

(**
  Accepts a term and returns the monoid value
  that it represents.
*)
Definition Term_eval
  :  Term -> E
  := Term_rec
       (fun _ => E)
       0
       (fun x => x).

(**
  Accepts a term and returns true iff the term
  is zero.
*)
Definition Term_is_zero
  :  Term -> bool
  := Term_rec
       (fun _ => bool)
       true
       (fun _ => false).

(** Proves that Term_is_zero is correct. *)
Theorem Term_is_zero_thm
  :  forall t, Term_is_zero t = true -> Term_eval t = 0.
Proof
  Term_ind
    (fun t => Term_is_zero t = true -> Term_eval t = 0)
       (fun _ => eq_refl 0)
       (fun x H
         => False_ind
              (Term_eval (term_const x) = 0)
              (diff_false_true H)).

(** Defines a map from Term to monoid elements. *)
Definition MTerm_map
  :  Term_map
  := term_map m Term Term_eval Term_is_zero Term_is_zero_thm.

End monoid_term_map.

Arguments term_0 {m}.

Arguments term_const {m} x.

(*
  Accepts a monoid term and returns an equivalent
  monoid expression.

  Note: This Ltac expression is an example of
  lightweight ltac. The idea behind this style
  is to use Gallina functions to generate proofs
  through reflection and then to use Ltac only
  as syntactic sugar to generate abstract terms.
*)
Ltac encode m x 
  := lazymatch x with
       | (0)
         => exact (MonoidExpr.leaf (MonoidExpr.term_0 (m:=m)))
       | ({+} ?X ?Y)
         => exact
              (MonoidExpr.node
                (ltac:(encode m X))
                (ltac:(encode m Y)))
       | (?X)
         => exact (MonoidExpr.leaf (MonoidExpr.term_const X))
     end.

End MonoidExpr.

(**
  Defines a notation that can be used to prove
  that two monoid expressions are equal using
  proof by reflection.

  We represent both expressions as binary trees
  and reduce both trees to the same canonical
  form demonstrating that their associated monoid
  expressions are equivalent.
*)
Notation "'reflect' x 'as' t ==> y 'as' u 'using' m"
  := (let r := MonoidExpr.reduce m t in
      let s := MonoidExpr.reduce m u in
      let v := proj1_sig r in
      let w := proj1_sig s in
      let H
        :  MonoidExpr.list_eval m v = MonoidExpr.list_eval m w
        := eq_refl (MonoidExpr.list_eval m v) : MonoidExpr.list_eval m v = MonoidExpr.list_eval m w in
      let H0
        :  MonoidExpr.BTree_eval m t = MonoidExpr.list_eval m v
        := proj2_sig r in
      let H1
        :  MonoidExpr.BTree_eval m u = MonoidExpr.list_eval m w
        := proj2_sig s in
      let H2
        :  MonoidExpr.BTree_eval m t = x
        := eq_refl (MonoidExpr.BTree_eval m t) : MonoidExpr.BTree_eval m t = x in
      let H3
        :  MonoidExpr.BTree_eval m u = y
        := eq_refl (MonoidExpr.BTree_eval m u) : MonoidExpr.BTree_eval m u = y in
      H
      || a = MonoidExpr.list_eval m w @a by H0
      || a = MonoidExpr.list_eval m w @a by H2
      || x = a @a by H1
      || x = a @a by H3
      : x = y)
      (at level 40, left associativity).

(**
  Defines a notation that can be used to prove
  that two monoid expressions, A and B, are
  equal given the term map C.
*)
Notation "'rewrite' A ==> B 'using' C"
  := (reflect A
       as (ltac:(MonoidExpr.encode (MonoidExpr.term_map_m C) A))
      ==> B
       as (ltac:(MonoidExpr.encode (MonoidExpr.term_map_m C) B)) using C
      : A = B)
     (at level 40, left associativity).

Section Unittests.

Variable m : Monoid.

Variables a b c d : E m.

Let map := MonoidExpr.MTerm_map m.

Let reflect_test_0
  :  (a + 0) = (0 + a)
  := rewrite (a + 0) ==> (0 + a) using map.

Let reflect_test_1
  :  (a + 0) + (0 + b) = a + b
  := rewrite ((a + 0) + (0 + b)) ==> (a + b) using map.

Let reflect_test_2
  :  (0 + a) + b = (a + b)
  := rewrite ((0 + a) + b) ==> (a + b) using map.

Let reflect_test_3
  :  (a + b) + (c + d) = a + ((b + c) + d)
  := rewrite (a + b) + (c + d) ==> a + ((b + c) + d) using map.

Let reflect_test_4
  :  (a + b) + (0 + c) = (a + 0) + (b + c)
  := rewrite (a + b) + (0 + c) ==> (a + 0) + (b + c) using map.

Let reflect_test_5
  :  (((a + b) + c) + 0) = (((0 + a) + b) + c)
  := rewrite (((a + b) + c) + 0) ==> (((0 + a) + b) + c) using map.

End Unittests.
