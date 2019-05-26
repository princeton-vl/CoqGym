(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import List.

Lemma map_in :
 forall (A B : Set) (f : A -> B) (b : B) (xs : list A),
 In b (map f xs) -> ex (fun a : A => b = f a /\ In a xs).
intros A B f b xs; elim xs; simpl in |- *; auto.
intros H'; elim H'; auto.
intros a l H' H'0; elim H'0;
 [ intros H'1; clear H'0 | intros H'1; clear H'0 ]; 
 auto.
exists a; split; auto.
elim H'; [ intros a0 E; elim E; intros H'2 H'3; clear E H' | clear H' ]; auto.
exists a0; split; auto.
Qed.

Lemma map_app :
 forall (A B : Set) (f : A -> B) (l1 l2 : list A),
 map f (l1 ++ l2) = map f l1 ++ map f l2.
intros A B f l1; elim l1; simpl in |- *; auto with datatypes.
intros a l H' l2; rewrite H'; auto.
Qed.

Lemma map_rev :
 forall (A B : Set) (f : A -> B) (l : list A), map f (rev l) = rev (map f l).
intros A B f l; elim l; simpl in |- *; auto.
intros a l0 H'; rewrite <- H'; simpl in |- *; auto.
apply trans_equal with (y := map f (rev l0) ++ map f (a :: nil)); auto.
apply map_app; auto.
Qed.

Lemma rev_in : forall (A : Set) (a : A) (l : list A), In a (rev l) -> In a l.
intros A a l; elim l; simpl in |- *; auto.
intros a0 l0 H' H'0.
case (in_app_or _ _ _ H'0); simpl in |- *; intros H'1; auto.
elim H'1; auto.
intros H'2; elim H'2.
Qed.

Lemma in_rev : forall (A : Set) (a : A) (l : list A), In a l -> In a (rev l).
intros A a l H'.
apply rev_in with (A := A); auto.
rewrite (rev_involutive l); auto.
Qed.
