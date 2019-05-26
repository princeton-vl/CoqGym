(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                ex1_auto.v                                *)
(****************************************************************************)

Theorem trivial : forall A : Prop, A -> A.
auto.
Qed.

Theorem and_commutative : forall A B : Prop, A /\ B -> B /\ A.
intros A B H'; elim H'; auto.
Qed.

Theorem or_commutative : forall A B : Prop, A \/ B -> B \/ A.
intros A B H'; elim H'; auto.
Qed.

Theorem mp : forall A B : Prop, A -> (A -> B) -> B.
auto.
Qed.

Theorem S : forall A B C : Prop, (A -> B -> C) -> (A -> B) -> A -> C.
auto.
Qed.

Theorem Praeclarum :
 forall x y z t : Prop, (x -> z) /\ (y -> t) -> x /\ y -> z /\ t.
intros x y z t H'; elim H'.
intros H'0 H'1 H'2; elim H'2.
auto.
Qed.

Theorem resolution :
 forall (p q : Type -> Prop) (a : Type),
 p a -> (forall x : Type, p x -> q x) -> q a.
auto.
Qed.

Theorem Witnesses :
 forall (a b : Type) (p : Type -> Prop), p a \/ p b -> exists x : Type, p x.
intros a b p h; elim h;
 [ intro H'; clear h; try exact H' | clear h; intro H' ].
exists a; try assumption.
exists b; try assumption.
Qed.

Theorem Simple :
 forall (A : Set) (R : A -> A -> Prop),
 (forall x y z : A, R x y /\ R y z -> R x z) ->
 (forall x y : A, R x y -> R y x) ->
 forall x : A, (exists y : A, R x y) -> R x x.
intros A R H' H'0 x H'1; try assumption.
elim H'1; intros y E; clear H'1; try exact E.
apply H' with y; auto.
Qed.

Theorem not_not : forall a : Prop, a -> ~ ~ a.
unfold not in |- *; auto.
Qed.

Theorem mini_cases : forall x y : Prop, (x \/ ~ y) /\ y -> x.
intros x y h; elim h; intros h0 H'; elim h0;
 [ clear h h0; intro H'0 | intro H'0; elim H'0; clear h h0; try assumption ];
 auto.
Qed.

Require Import Classical.
(*This theorem needs classical logic*)

Theorem not_not_converse : forall a : Prop, ~ ~ a -> a.
intros a H'; try assumption; auto 10.
generalize (classic a); intro h; elim h;
 [ intro H'0; clear h; try exact H'0 | clear h; intro H'0 ].
elim H'; assumption.
Qed.

Theorem not_quite_classic : forall a : Prop, ~ ~ (a \/ ~ a).
unfold not in |- *; auto.
Qed.

Theorem Peirce : forall A B : Prop, ((((A -> B) -> A) -> A) -> B) -> B.
auto.
Qed.

