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

(** Sets as pointed graphs
    ~~~~~~~~~~~~~~~~~~~~~~
    In the following, we will interpret sets as pointed graphs, that
    is, as triples of the form (X, A, a) where :

    - X : Typ1     is the carrier (i.e. the small type of vertices);
    - A : (Rel X)  is the edge (or local membership) relation;
    - a : X        is the root.

    Naming conventions
    ~~~~~~~~~~~~~~~~~~
    Since the PTS Fw.2 does not provide any pairing mechanism, we will
    introduce the three components of each pointed graph separately.
    Of course, this separation is error-prone, and to avoid confusions
    we will name components according to the following scheme:

    Pointed graph   Vertices
    -------------   --------
    (X, A, a)       x, x', x0, x1, etc.
    (Y, B, b)       y, y', y0, y1, etc.
    (Z, C, c)       z, z', z0, z1, etc.
    etc.

    Moreover, a letter affected with a prime (such as x') will usually
    indicate that the vertex (or carrier, or relation) it denotes is in
    some sense an element of the corresponding unaffected letter. *)

(********************************)
(** * Equality as bisimilarity  *)
(********************************)

(** Two pointed graphs (X, A, a) and (Y, B, b) are bisimilar if there
    exists a relation R:X->Y->Prop satisfying the following conditions:

    (BIS1) (x,x':X; y:Y) (A x' x)/\(R x y) -> (Ex y':Y | (B y' y)/\(R x' y'))

    (BIS2) (x,x':X; y:Y) (A x' x)/\(R x y) -> (Ex y':Y | (B y' y)/\(R x' y'))

    (BIS3) (R a b)

    Instead of defining this relation by the mean of standard logical
    connectives, we give an equivalent impredicative encoding for it
    in order to make the forthcoming proofs a little bit shorter. *)

Definition EQV (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) 
  (B : Rel Y) (b : Y) : Prop :=
  forall E : Prop,
  (forall R : X -> Y -> Prop,
   (forall (x x' : X) (y : Y),
    A x' x -> R x y -> ex2 Y (fun y' => B y' y) (fun y' => R x' y')) ->
   (forall (y y' : Y) (x : X),
    B y' y -> R x y -> ex2 X (fun x' => A x' x) (fun x' => R x' y')) ->
   R a b -> E) -> E.

(** Here is the corresponding introduction rule: *)

Lemma EQV_intro :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) 
   (b : Y) (R : X -> Y -> Prop),
 (forall (x x' : X) (y : Y),
  A x' x -> R x y -> ex2 Y (fun y' => B y' y) (fun y' => R x' y')) ->
 (forall (y y' : Y) (x : X),
  B y' y -> R x y -> ex2 X (fun x' => A x' x) (fun x' => R x' y')) ->
 R a b -> EQV X A a Y B b.

Proof fun X A a Y B b R H1 H2 H3 E e => e R H1 H2 H3.

(** It would be useless to define the corresponding elimination rule
    whose behaviour is obtained by using [Apply H] instead of [Elim H]
    in the following proof scripts.

    We first check that bisimilarity is an equivalence relation: *)

Lemma EQV_refl : forall (X : Typ1) (A : Rel X) (a : X), EQV X A a X A a.

Proof.
intros X A a; apply EQV_intro with (fun x y => eq X x y).
(* BIS 1 *)
intros x x' y H1 H2; apply ex2_intro with x'.
apply H2; assumption. apply eq_refl.
(* BIS 2 *)
intros y y' x H1 H2; apply ex2_intro with y'.
apply (eq_sym _ _ _ H2); assumption. apply eq_refl.
(* BIS 3 *)
apply eq_refl.
Qed.

Lemma EQV_sym :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) (b : Y),
 EQV X A a Y B b -> EQV Y B b X A a.

Proof.
intros X A a Y B b H; apply H; clear H; intros R H1 H2 H3.
apply EQV_intro with (fun y x => R x y); assumption.
Qed.

Lemma EQV_trans :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) 
   (b : Y) (Z : Typ1) (C : Rel Z) (c : Z),
 EQV X A a Y B b -> EQV Y B b Z C c -> EQV X A a Z C c.

Proof.
intros X A a Y B b Z C c H1 H4.
apply H1; clear H1; intros R H1 H2 H3.
apply H4; clear H4; intros S H4 H5 H6.
apply EQV_intro with (fun x z => ex2 Y (fun y => R x y) (fun y => S y z)).
(* BIS1 *)
intros x x' z H7 H; apply H; clear H; intros y H8 H9.
apply (H1 x x' y H7 H8); intros y' H10 H11.
apply (H4 y y' z H10 H9); intros z' H12 H13.
apply ex2_intro with z'. assumption.
apply ex2_intro with y'; assumption.
(* BIS2 *)
intros z z' x H7 H; apply H; clear H; intros y H8 H9.
apply (H5 z z' y H7 H9); intros y' H10 H11.
apply (H2 y y' x H10 H8); intros x' H12 H13.
apply ex2_intro with x'. assumption.
apply ex2_intro with y'; assumption.
(* BIS3 *)
apply ex2_intro with b; assumption.
Qed.

(** The following lemma states that the bisimilarity relation can be
    shifted one vertex down by following the edges of both local
    membership relations. *)

Lemma EQV_shift :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) (b : Y),
 EQV X A a Y B b ->
 forall a' : X,
 A a' a -> ex2 Y (fun b' => B b' b) (fun b' => EQV X A a' Y B b').

Proof.
intros X A a Y B b H; eapply H; clear H; intros R H1 H2 H3.
intros a' H4; apply (H1 a a' b H4 H3); intros b' H5 H6.
apply ex2_intro with b'. assumption.
apply EQV_intro with R; assumption.
Qed.

(******************************************)
(** * Membership as shifted bisimilarity  *)
(******************************************)

(** A pointed graph (X, A, a) represents an element of a pointed graph
    (Y, B, b) if there is a vertex b':Y one edge below the root b such
    that the pointed graphs (X, A, a) and (Y, B, b') are bisimilar.

    This relation is impredicatively encoded as follows: *)

Definition ELT (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) 
  (B : Rel Y) (b : Y) : Prop :=
  forall E : Prop, (forall b' : Y, B b' b -> EQV X A a Y B b' -> E) -> E.

Lemma ELT_intro :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) (b b' : Y),
 B b' b -> EQV X A a Y B b' -> ELT X A a Y B b.

Proof fun X A a Y B b b' H1 H2 E e => e b' H1 H2.

(** Direct elements of a pointed graph (X, A, a) are simply the pointed
    graphs of the form (X, A, a') such that (A a' a), that is, the
    pointed graphs we obtain by shifting the root one edge downwards: *)

Lemma ELT_direct :
 forall (X : Typ1) (A : Rel X) (a a' : X), A a' a -> ELT X A a' X A a.

Proof.
intros X A a a' H; apply ELT_intro with a'.
assumption.  apply EQV_refl.
Qed.

(** We now state the (left and right) compatibility of the membership
    relation w.r.t. the bisimilarity relation.  Both compatibilities
    rely on the transitivity of the bisimilarity relation, and the
    right compatibility uses the EQV_shift lemma we proved above. *)

Lemma ELT_compat_l :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) 
   (b : Y) (Z : Typ1) (C : Rel Z) (c : Z),
 EQV X A a Y B b -> ELT Y B b Z C c -> ELT X A a Z C c.

Proof.
intros X A a Y B b Z C c H1 H.
apply H; clear H; intros c' H2 H3.
apply ELT_intro with c'.  assumption.
apply EQV_trans with Y B b; assumption.
Qed.

Lemma ELT_compat_r :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) 
   (b : Y) (Z : Typ1) (C : Rel Z) (c : Z),
 ELT X A a Y B b -> EQV Y B b Z C c -> ELT X A a Z C c.

Proof.
intros X A a Y B b Z C c H.
eapply H; clear H; intros b' H1 H2 H3.
apply (EQV_shift _ _ _ _ _ _ H3 b' H1); intros c' H4 H5.
apply ELT_intro with c'.  assumption.
apply EQV_trans with Y B b'; assumption.
Qed.

(************************************)
(** * Inclusion and extensionality  *)
(************************************)

(** The inclusion relation is defined as expected: *)

Definition SUB (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) 
  (B : Rel Y) (b : Y) : Prop :=
  forall (Z : Typ1) (C : Rel Z) (c : Z), ELT Z C c X A a -> ELT Z C c Y B b.

(** Inclusion is clearly reflexive and transitive: *)

Lemma SUB_refl : forall (X : Typ1) (A : Rel X) (a : X), SUB X A a X A a.

Proof.
unfold SUB in |- *; auto.
Qed.

Lemma SUB_trans :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) 
   (b : Y) (Z : Typ1) (C : Rel Z) (c : Z),
 SUB X A a Y B b -> SUB Y B b Z C c -> SUB X A a Z C c.

Proof.
unfold SUB in |- *; auto.
Qed.

(** We now state the extensionality property, which expresses that the
    inclusion relation is antisymmetric (thus being a partial ordering
    relation between sets).  Equivalently, this property says that two
    pointed graphs are bisimilar when they have the same elements. *)

Theorem extensionality :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) (b : Y),
 SUB X A a Y B b -> SUB Y B b X A a -> EQV X A a Y B b.

Proof.
intros X A a Y B b H1 H2.
(* Give the bisimulation: *)
apply
 EQV_intro with (fun x y => or (and (eq X x a) (eq Y y b)) (EQV X A x Y B y)).
(* BIS1 *)
intros x x' y H3 H4; apply H4; clear H4; intro H4.
(* BIS1, first case: x = a and y = b *)
apply H4; clear H4; intros H4 H5.
generalize (ELT_direct X A x x' H3); eapply (eq_sym _ _ _ H4).
intro H6; apply (H1 _ _ _ H6); intros y' H7 H8.
apply ex2_intro with y'.
apply (eq_sym _ _ _ H5); assumption.
apply or_inr; assumption.
(* BIS1, second case: (EQV X A x Y B y) *)
apply (EQV_shift _ _ _ _ _ _ H4 x' H3).
intros y' H5 H6; apply ex2_intro with y'.
assumption.  apply or_inr; assumption.
(* BIS2 *)
intros y y' x H3 H4; apply H4; clear H4; intro H4.
(* BIS2, first case: x = a and y = b *)
apply H4; clear H4; intros H4 H5.
generalize (ELT_direct Y B y y' H3); eapply (eq_sym _ _ _ H5).
intro H6; apply (H2 _ _ _ H6); intros x' H7 H8.
apply ex2_intro with x'.
apply (eq_sym _ _ _ H4); assumption.
apply or_inr; apply EQV_sym; assumption.
(* BIS2, second case: (EQV X A x Y B y) *)
apply (EQV_shift _ _ _ _ _ _ (EQV_sym _ _ _ _ _ _ H4) y' H3).
intros x' H5 H6; apply ex2_intro with x'.
assumption.  apply or_inr; apply EQV_sym; assumption.
(* BIS3 *)
apply or_inl; apply and_intro; apply eq_refl.
Qed.

(*******************)
(** * Delocations  *)
(*******************)

(** Let (X, A) and (Y, B) be two graphs.  A delocation from (X, A) to
    (Y, B) is a function f : X->Y such that:

    1. (x,x':X)    (A x' x) -> (B (f x') (f x))

    2. (x:X; y':Y) (B y' (f x)) -> (Ex x':X | (A x' x) /\ y'=(f x'))

    Intuitively, a delocation is a morphism of graphs in which any edge
    of the target graph (Y, B) which points to an element of the image
    of f can be tracked back as an edge in the source graph via f.
    This notion is formalized as follows: *)

Definition deloc (X : Typ1) (A : Rel X) (Y : Typ1) 
  (B : Rel Y) (f : X -> Y) : Prop :=
  and (forall x x' : X, A x' x -> B (f x') (f x))
    (forall (x : X) (y' : Y),
     B y' (f x) -> ex2 X (fun x' => A x' x) (fun x' => eq Y y' (f x'))).

(** The notion of delocation f:(X,A)->(Y,B) is interesting since it
    automatically induces a bisimulation from the pointed graph (X, A, x)
    to the pointed graph (Y, B, (f x)) for any vertex x:X in the source
    graph (X,A).  This property is stated by the following lemma: *)

Lemma EQV_deloc :
 forall (X : Typ1) (A : Rel X) (Y : Typ1) (B : Rel Y) (f : X -> Y),
 deloc X A Y B f -> forall x : X, EQV X A x Y B (f x).

Proof.
intros X A Y B f H.  eapply H; clear H; intros H1 H2 x0.
apply EQV_intro with (fun x y => eq Y y (f x)).
(* BIS1 *)
intros x x' y H3 H4; apply ex2_intro with (f x').
apply (eq_sym _ _ _ H4); apply H1; assumption.
apply eq_refl.
(* BIS2 *)
intros y y' x H3 H4.
exact (H2 x y' (H4 (B y') H3)).
(* BIS3 *)
apply eq_refl.
Qed.
