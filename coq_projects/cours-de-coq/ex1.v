(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                  ex1.v                                   *)
(****************************************************************************)


Theorem trivial : forall A : Prop, A -> A.
intros A H'; exact H'.
Qed.

Theorem and_commutative : forall A B : Prop, A /\ B -> B /\ A.
intros A B H'; split.
elim H'; intros H'0 H'1; clear H'; exact H'1.
elim H'; intros H'0 H'1; clear H'; exact H'0.
Qed.

Theorem or_commutative : forall A B : Prop, A \/ B -> B \/ A.
intros A B h; elim h; [ intro H'; clear h; try exact H' | clear h; intro H' ].
right; assumption.
left; assumption.
Qed.

Theorem mp : forall A B : Prop, A -> (A -> B) -> B.
intros A B H' H'0.
apply H'0.
exact H'.
Qed.

Theorem S : forall A B C : Prop, (A -> B -> C) -> (A -> B) -> A -> C.
intros A B C H' H'0 H'1.
apply H'.
exact H'1.
apply H'0.
exact H'1.
Qed.

Theorem Praeclarum :
 forall x y z t : Prop, (x -> z) /\ (y -> t) -> x /\ y -> z /\ t.
intros x y z t h; elim h; intros H' H'0; clear h.
intro h; elim h; intros H'1 H'2; clear h.
split.
apply H'; assumption.
apply H'0; assumption.
Qed.

Theorem resolution :
 forall (p q : Type -> Prop) (a : Type),
 p a -> (forall x : Type, p x -> q x) -> q a.
intros p q a H' H'0.
apply H'0.
exact H'.
Qed.

Theorem Witnesses :
 forall (a b : Type) (p : Type -> Prop), p a \/ p b -> exists x : Type, p x.
intros a b p h; elim h; intro H'; clear h.
exists a; assumption.
exists b; assumption.
Qed.

Theorem Simple :
 forall (A : Set) (R : A -> A -> Prop),
 (forall x y z : A, R x y /\ R y z -> R x z) ->
 (forall x y : A, R x y -> R y x) ->
 forall x : A, (exists y : A, R x y) -> R x x.
intros A R H' H'0 x h; elim h; intros y E; clear h.
apply H' with y.
split; [ assumption | idtac ].
apply H'0; assumption.
Qed.

Theorem not_not : forall a : Prop, a -> ~ ~ a.
intros a H'; red in |- *; intro H'0; elim H'0; assumption.
Qed.

Theorem mini_cases : forall x y : Prop, (x \/ ~ y) /\ y -> x.
intros x y h; elim h; intros h0 H'; elim h0;
 [ intro H'0; clear h h0; try exact H'0 | clear h h0; intro H'0 ].
elim H'0; try assumption.
Qed.

Require Import Classical.
(*This theorem needs classical logic*)

Theorem not_not_converse : forall a : Prop, ~ ~ a -> a.
intros a H'.
generalize (classic a); intro h; elim h;
 [ intro H'0; clear h; try exact H'0 | clear h; intro H'0 ].
elim H'; assumption.
Qed.

Theorem not_quite_classic : forall a : Prop, ~ ~ (a \/ ~ a).
intro a; red in |- *; intro H'; elim H'; right; red in |- *; intro H'0.
elim H'; left; try assumption.
Qed.

