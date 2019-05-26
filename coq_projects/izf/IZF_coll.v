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


Require Import IZF_logic.
Require Import IZF_base.

(***************************************************)
(** * The intuitionistic Hilbert epsilon operator  *)
(***************************************************)

(** The following axioms mimick (a specialized version of) the
    intuitionistic Hilbert epsilon operator described in the
    author's LICS'03 submitted paper. *)

(** We first introduce a type of codes, that could be defined as a
    primitive type of natural numbers by following the paper.  But
    since the actual structure of its inhabitants will never be
    used in the forthcoming proofs, we prefer to keep it abstract. *)

Axiom Code : Typ1.  (* We could set Code := nat. *)

(** We now introduce a specialized version of the epsilon operator
    described in the paper.  This version only works for predicates
    over the (large) type Typ1, which is sufficent for what we want
    to prove (i.e. the collection scheme). *)

Axiom eps : (Typ1 -> Prop) -> Code -> Typ1.

(** The following axiom states that if a predicate P : Typ1->Prop
    holds for some type X : Typ1, then there exists a code c : Code
    such that P holds for (eps P c).

    Technically, this axiom shows that we can always replace an
    existential statement over a large type (i.e. Typ1) by an
    existential statement over a small type (i.e. Code), which is
    crucial for interpreting the collection scheme. *)

Axiom
  choice : forall P : Typ1 -> Prop, exT P -> ex Code (fun c => P (eps P c)).

(*********************************************)
(** * An implementation of a super-powerset  *)
(*********************************************)

(** On a fixed small type Z, we can build several pointed graphs of
    the form (Z, A, a), whose two extra parameters A and a range over
    (Rel Z) and Z respectively.  But since the cartesian product
    (Rel Z) * Z is itself a small type, it is not difficult to build
    a variant of the powerset (foo, FOO, foo_rt) that contains all the
    pointed graphs of the form (Z, A, a), that is, a pointed graph
    (called the "super-powerset" of Z) such that

                      (Z, A, a) \in (foo, FOO, foo_rt)

    for any edge relation A : (Rel A) and for any root a : Z.

    In what follows, we propose to achieve this construction, but in
    a more general setting.  For that, instead of considering a small
    type Z : Typ1, we will rather consider a family of small types
    Z : X->Y->Typ1 indexed by the inhabitants of two given small types
    X, Y : Typ1, and from these parameters, we propose to build a
    pointed graph ((foo X Y Z), (FOO X Y Z), (foo_rt X Y Z)) such that

      ((Z x y), A, a) \in ((foo X Y Z), (FOO X Y Z), (foo_rt X Y Z))

    for any x : X, y : Y, A : (Rel (Z x y)) and a : (Z x y).
    Intuitively, this pointed graph represents the union of the
    super-powersets associated to the carriers (Z x y) when x and
    y range over the small types X and Y respectively. *)

(** ** Building the carrier of the super-powerset **)

(** The carrier (foo X Y Z) of the super-powerset associated to a
    given family of small types Z : X->Y->Typ1 indexed by two small
    types X and Y would be naturally defined in Coq as follows:

      Inductive foo [X,Y:Typ1; Z:X->Y->Typ1] : Typ1 :=
      | foo_in : (x:X; y:Y)(Rel (Z x y))->(Z x y)->(foo X Y Z)
      | foo_rt : (foo X Y Z).

    Intuitively, this type is the disjoint union of the cartesian
    products (Rel (Z x y)) * (Z x y) where x and y range over X and
    Y respectively, plus an extra element (foo_rt X Y Z) that will
    be used as the new root.  In our framework, this inductive
    definition is easily mimicked as follows: *)

Definition foo (X Y : Typ1) (Z : X -> Y -> Typ1) : Typ1 :=
  (forall (x : X) (y : Y), Rel (Z x y) -> Z x y -> Prop) -> Prop.

Definition foo_in (X Y : Typ1) (Z : X -> Y -> Typ1) 
  (x : X) (y : Y) (R : Rel (Z x y)) (z : Z x y) : foo X Y Z :=
  fun f => f x y R z.

Definition foo_rt (X Y : Typ1) (Z : X -> Y -> Typ1) : 
  foo X Y Z := fun _ => bot.

(** It is then easy to check the expected property of non-confusion
    holds for the constructors foo_in and foo_rt: *)

Lemma eq_foo_in_rt :
 forall (X Y : Typ1) (Z : X -> Y -> Typ1) (x : X) (y : Y) 
   (R : Rel (Z x y)) (z : Z x y),
 eq (foo X Y Z) (foo_in X Y Z x y R z) (foo_rt X Y Z) -> bot.

Proof fun X Y Z x y R z e => e (fun u => u (fun _ _ _ _ => top)) top_intro.

Lemma eq_foo_rt_in :
 forall (X Y : Typ1) (Z : X -> Y -> Typ1) (x : X) (y : Y) 
   (R : Rel (Z x y)) (z : Z x y),
 eq (foo X Y Z) (foo_rt X Y Z) (foo_in X Y Z x y R z) -> bot.

Proof
  fun X Y Z x y R z e =>
  e (fun u => u (fun _ _ _ _ => top) -> bot) (fun p => p) top_intro.

(** On the other hand, proving the injectivity of the constructor

    (foo_in X Y Z) : (x:X; y:Y)(Rel (Z x y))->(Z x y)->(foo X Y Z)

    (of arity 4) is a little bit more tricky, since the types of its
    last two arguments actually depend on the values of its first two
    arguments.  (This is the same problem as for the dependent pair.)

    For this reason, we express the injectivity of the constructor
    (foo_in X Y Z) by using a dependent equality which is close to
    John Major's equality: *)

Lemma eq_foo_in_in :
 forall (X Y : Typ1) (Z : X -> Y -> Typ1) (x1 x2 : X) 
   (y1 y2 : Y) (R1 : Rel (Z x1 y1)) (R2 : Rel (Z x2 y2)) 
   (z1 : Z x1 y1) (z2 : Z x2 y2),
 (* Equality of the images... *)
 eq (foo X Y Z) (foo_in X Y Z x1 y1 R1 z1) (foo_in X Y Z x2 y2 R2 z2)
 (* ... implies dependent equality: *)
  ->
 forall P : forall (x : X) (y : Y), Rel (Z x y) -> Z x y -> Prop,
 P x1 y1 R1 z1 -> P x2 y2 R2 z2.

Proof fun X Y Z x1 x2 y1 y2 R1 R2 z1 z2 H P p => H (fun f => f P) p.

(** This kind of equality is actually sufficent for proving the
    expected delocation property (cf Lemma FOO_deloc below). *)

(** ** Building the edge relation of the super-powerset **)

(** The edge relation (FOO X Y Z) : (Rel (foo X Y Z)) of the super-powerset
    of the family of small types Z : X->Y->Typ1 is defined by the following
    clauses:

    1.  (Delocation of pointed graph structures:)

        For any x:X and y:Y, for any relation R:(Rel (Z x y)) and
        for any pair of vertices z,z':(Z x y),  (R z' z) implies
        (FOO X Y Z (foo_in X Y Z x y R z') (foo_in X Y Z x y R z))

    2.  (Connecting vertices to the new root:)

        For any x:X and y:Y, for any relation R:(Rel (Z x y)) and
        for any vertex z:(Z x y), then
        (FOO X Y Z (foo_in X Y Z x y R z) (foo_rt X Y Z)).

    Formally, we define this relation as follows: *)

Definition FOO (X Y : Typ1) (Z : X -> Y -> Typ1) (u' u : foo X Y Z) : Prop :=
  forall E : Prop,
  (forall (x : X) (y : Y) (R : Rel (Z x y)) (z' z : Z x y),
   eq (foo X Y Z) u' (foo_in X Y Z x y R z') ->
   eq (foo X Y Z) u (foo_in X Y Z x y R z) -> R z' z -> E) ->
  (forall (x : X) (y : Y) (R : Rel (Z x y)) (z' : Z x y),
   eq (foo X Y Z) u' (foo_in X Y Z x y R z') ->
   eq (foo X Y Z) u (foo_rt X Y Z) -> E) -> E.

(** Both clauses are given by the following constructors: *)

Lemma FOO_in :
 forall (X Y : Typ1) (Z : X -> Y -> Typ1) (x : X) (y : Y) 
   (R : Rel (Z x y)) (z' z : Z x y),
 R z' z -> FOO X Y Z (foo_in X Y Z x y R z') (foo_in X Y Z x y R z).

Proof
  fun X Y Z x y R z' z H E H1 H2 =>
  H1 x y R z' z (eq_refl (foo X Y Z) (foo_in X Y Z x y R z'))
    (eq_refl (foo X Y Z) (foo_in X Y Z x y R z)) H.

Lemma FOO_rt :
 forall (X Y : Typ1) (Z : X -> Y -> Typ1) (x : X) (y : Y) 
   (R : Rel (Z x y)) (z' : Z x y),
 FOO X Y Z (foo_in X Y Z x y R z') (foo_rt X Y Z).

Proof
  fun X Y Z x y R z' E H1 H2 =>
  H2 x y R z' (eq_refl (foo X Y Z) (foo_in X Y Z x y R z'))
    (eq_refl (foo X Y Z) (foo_rt X Y Z)).

(** We now prove that for any x:X, y:Y and R:(Rel (Z x y)), the function

          (foo_in X Y Z x y R)  :  (Z x y)->(foo X Y Z)

    induces a delocation from the graph ((Z x y), R) to the graph
    ((foo X Y Z), (FOO x y z)).  *)

Lemma FOO_deloc :
 forall (X Y : Typ1) (Z : X -> Y -> Typ1) (x : X) (y : Y) (R : Rel (Z x y)),
 deloc (Z x y) R (foo X Y Z) (FOO X Y Z) (foo_in X Y Z x y R).

Proof.
intros X Y Z x y R; unfold deloc in |- *; apply and_intro.
(* Deloc 1 *)
intros; apply FOO_in; assumption.
(* Deloc 2 *)
intros z f' H; apply H; clear H.
(* Deloc 2, case 1 *)
intros x0 y0 R0 z0' z0 H2 H3 H4; apply (eq_sym _ _ _ H2).
generalize z0' H4; clear H2 H4 f' z0'.
(* Use dependent equality: *)
apply (eq_foo_in_in X Y Z x x0 y y0 R R0 z z0 H3).
intros z' H4; apply ex2_intro with z'.
assumption. apply eq_refl.
(* Deloc 2, case 2 (absurd) *)
intros x0 y0 R0 z0' H1 H2; apply (eq_foo_in_rt _ _ _ _ _ _ _ H2).
Qed.

(** And from the latter result, we derive the expected property
    of bisimilarity: *)

Lemma FOO_eqv :
 forall (X Y : Typ1) (Z : X -> Y -> Typ1) (x : X) (y : Y) 
   (R : Rel (Z x y)) (z : Z x y),
 EQV (Z x y) R z (foo X Y Z) (FOO X Y Z) (foo_in X Y Z x y R z).

Proof.
intros; apply EQV_deloc; apply FOO_deloc.
Qed.

(** Finally, we show that our super-powerset meets its specification: *)

Lemma FOO_elt :
 forall (X Y : Typ1) (Z : X -> Y -> Prop) (x : X) (y : Y) 
   (R : Rel (Z x y)) (z : Z x y),
 ELT (Z x y) R z (foo X Y Z) (FOO X Y Z) (foo_rt X Y Z).

Proof.
intros X Y Z x y R z.
apply ELT_intro with (foo_in X Y Z x y R z).
apply FOO_rt.  apply FOO_eqv.
Qed.

(******************************************************)
(** * Compatible relations and the collection scheme  *)
(******************************************************)

(** ** Binary relations **)

(** The type of binary relations over pointed graphs: *)

Definition REL : Typ2 :=
  forall X : Typ1, Rel X -> X -> forall Y : Typ1, Rel Y -> Y -> Prop.

(** And the corresponding (left and right) compatibility properties: *)

Definition LCOMPAT (R : REL) : Prop :=
  forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) 
    (B : Rel Y) (b : Y) (Z : Typ1) (C : Rel Z) (c : Z),
  EQV X A a Y B b -> R Y B b Z C c -> R X A a Z C c.

Definition RCOMPAT (R : REL) : Prop :=
  forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) 
    (B : Rel Y) (b : Y) (Z : Typ1) (C : Rel Z) (c : Z),
  R X A a Y B b -> EQV Y B b Z C c -> R X A a Z C c.

(** It is convenient to define a relativized form (exG_rel X A a P) of
    the existential quantifier on the class of pointed graphs, that
    expresses that the predicate P holds for some element of the
    pointed graph (X, A, a). *)

Definition exG_rel (X : Typ1) (A : Rel X) (a : X)
  (P : forall Y : Typ1, Rel Y -> Y -> Prop) :=
  forall E : Prop,
  (forall (Y : Typ1) (B : Rel Y) (b : Y), ELT Y B b X A a -> P Y B b -> E) ->
  E.

Lemma exG_rel_intro :
 forall (X : Typ1) (A : Rel X) (a : X)
   (P : forall Y : Typ1, Rel Y -> Y -> Prop) (Y : Typ1) 
   (B : Rel Y) (b : Y), ELT Y B b X A a -> P Y B b -> exG_rel X A a P.

Proof fun X A a P Y B b H1 H2 E f => f Y B b H1 H2.

(** ** The collection scheme **)

(** Let (X, A, a) be a pointed graph and R a binary relation over the
    class of pointed graph (that we suppose compatible) such that each
    element of the pointed graph (X, A, a) is related to at least one
    pointed graph via the relation R.

    Since the elements of (X, A, a) are (up to a bisimulation) the
    pointed graphs of the form (X, A, x) where x : X is a vertex
    such that (A x a), our assumption can be reformulated as

      for any x : X such that (A x a), there exists a pointed
      graph (Y, B, b) such that (R X A x Y B b).

    (Of course, the equivalence of both formulations relies on the
    compatibility of R with respect to its first argument).  Now, let
    us consider the family of small types

            (coll_fam X A a R)  :  X->Code->Typ1

    defined by using the choice operator "eps" as follows: *)

Definition coll_fam (X : Typ1) (A : Rel X) (a : X) 
  (R : REL) (x : X) : Code -> Typ1 :=
  eps (fun Y => ex (Rel Y) (fun B => ex Y (fun b => R X A x Y B b))).

(** (Notice that the definition of (coll_fam X A a R) actually does not
    depend on the root a : X of the pointed graph (X, A, a).)

    By construction, the family of small types (coll_fam X A a R) is
    such that for any x : X, if there exists a pointed graph (Y, B, b)
    which is related to (X, A, x) via R, then there is a code c : Code
    such that (coll_fam X A a R x c) is the carrier of one of such
    pointed graphs, that is, such that

      (R X A x (coll_fam X A a R x c) B b)

    for some edge relation B and some root b on the carrier given by
    (coll_fam X A a R x c).

    It is now clear that if we take the super-powerset of the family
    (coll_fam X A a R) : X->Code->Typ1, we obtain a pointed graph that
    meets the specification of the collection scheme.

    Formally, the desired pointed graph

      ((coll X A a R), (COLL X A a R), (coll_rt X A a R))

    is defined as follows: *)

Definition coll (X : Typ1) (A : Rel X) (a : X) (R : REL) : Typ1 :=
  foo X Code (coll_fam X A a R).

Definition COLL (X : Typ1) (A : Rel X) (a : X) (R : REL) :
  Rel (coll X A a R) := FOO X Code (coll_fam X A a R).

Definition coll_rt (X : Typ1) (A : Rel X) (a : X) (R : REL) : 
  coll X A a R := foo_rt X Code (coll_fam X A a R).

(** (Notice that the components of this pointed graph actually do not
    depend on the root a : X of the pointed graph (X, A, a).)

    It is now a simple exercise to check that the pointed graph we have
    built meets the specification of the collection scheme: *)

Theorem collection :
 forall (X : Typ1) (A : Rel X) (a : X) (R : REL),
 LCOMPAT R ->
 RCOMPAT R ->
 (forall (X' : Typ1) (A' : Rel X') (a' : X'),
  ELT X' A' a' X A a -> exG (fun Y' B' b' => R X' A' a' Y' B' b')) ->
 forall (X' : Typ1) (A' : Rel X') (a' : X'),
 ELT X' A' a' X A a ->
 exG_rel (coll X A a R) (COLL X A a R) (coll_rt X A a R)
   (fun Y' B' b' => R X' A' a' Y' B' b').

Proof.
intros X A a R HL HR H0 X' A' a' H1.
apply H1; clear H1; intros x H1 H2.
(* Perform a cut *)
cut (exT (fun Y => ex (Rel Y) (fun B => ex Y (fun b => R X A x Y B b)))).
(* Main premise *)
intro H; apply (choice _ H); clear H; intros c H.
apply H; clear H; intros B H; change (Rel (coll_fam X A a R x c)) in B.
apply H; clear H; intros b H3; change (coll_fam X A a R x c) in b.
change (R X A x (coll_fam X A a R x c) B b) in H3.
apply exG_rel_intro with (coll_fam X A a R x c) B b.
apply ELT_intro with (foo_in X Code (coll_fam X A a R) x c B b).
unfold COLL, coll_rt in |- *; apply FOO_rt.
unfold coll, COLL in |- *; apply FOO_eqv.
apply HL with X A x; assumption.
(* Argument *)
apply (H0 X A x (ELT_direct X A a x H1)); intros Y B b H3.
apply exT_intro with Y.
apply ex_intro with B.
apply ex_intro with b.
assumption.
Qed.

(** In fact, our super-powerset meets a slightly stronger statement
    (but still classically equivalent) which is the following: *)

Theorem collection2 :
 forall (X : Typ1) (A : Rel X) (a : X) (R : REL),
 LCOMPAT R ->
 RCOMPAT R ->
 forall (X' : Typ1) (A' : Rel X') (a' : X'),
 ELT X' A' a' X A a ->
 exG (fun Y' B' b' => R X' A' a' Y' B' b') ->
 exG_rel (coll X A a R) (COLL X A a R) (coll_rt X A a R)
   (fun Y' B' b' => R X' A' a' Y' B' b').

Proof.
intros X A a R HL HR X' A' a' H H1.
apply H; clear H; intros x H2 H3.
(* Perform a cut *)
cut (exT (fun Y => ex (Rel Y) (fun B => ex Y (fun b => R X A x Y B b)))).
(* Main premise *)
intro H; apply (choice _ H); clear H; intros c H.
apply H; clear H; intros B H; change (Rel (coll_fam X A a R x c)) in B.
apply H; clear H; intros b H4; change (coll_fam X A a R x c) in b.
change (R X A x (coll_fam X A a R x c) B b) in H4.
apply exG_rel_intro with (coll_fam X A a R x c) B b.
apply ELT_intro with (foo_in X Code (coll_fam X A a R) x c B b).
unfold COLL, coll_rt in |- *; apply FOO_rt.
unfold coll, COLL in |- *; apply FOO_eqv.
apply HL with X A x; assumption.
(* Argument *)
apply H1; clear H1; intros Y B b H1.
apply exT_intro with Y.
apply ex_intro with B.
apply ex_intro with b.
apply HL with X' A' a'.
apply EQV_sym; assumption. 
assumption.
Qed.
