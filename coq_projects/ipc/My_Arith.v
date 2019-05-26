(* File: My_Arith.v  (last edited on 25/10/2000) (c) Klaus Weich  *)

Require Import Le.
Require Import Lt.
Require Import List.
Require Import Plus.

(******* List stuff ***********************************************)


Lemma fold_right_perm :
 forall (A B : Set) (f : B -> A -> A) (o : A) (l0 l1 : list B) (x : B),
 (forall (a b : B) (c : A), f a (f b c) = f b (f a c)) ->
 fold_right f o (l0 ++ x :: l1) = fold_right f o (x :: l0 ++ l1).
intros A B f o l0 l1 x f_perm.
elim l0; clear l0.
trivial.
intros a0 l0 ih.
simpl in |- *.
 rewrite ih. 
simpl in |- *.
apply f_perm.
Qed.




(********************************************************************)


Lemma plus_O : forall n : nat, n + 0 = n.
intros n.
 rewrite (plus_comm n 0).
simpl in |- *.
trivial.
Qed.


Lemma n_Sn_false : forall n : nat, n = S n -> False.
intros n; elim n; clear n.
intro u0;  discriminate u0.
intros n ih u0.
apply ih.
 injection u0; trivial.
Qed.

Lemma le_reg : forall m n : nat, n <= m -> S n <= S m.
intros m; elim m; clear m.
intros n; case n; clear n.
intros.
apply le_n.
intros.
inversion_clear H.
intros m ih n H.
inversion_clear H.
apply le_n.
apply le_S.
apply ih; assumption.
Qed.


Lemma eq_lt_trans : forall n m p : nat, n = m -> m < p -> n < p.
intros n m p eq lt.
 rewrite eq; assumption.
Qed.


Lemma S_reg : forall n m : nat, n = m -> S n = S m.
intros.
 rewrite H.
trivial.
Qed.



Lemma plus_reg : forall l m n : nat, m = n -> l + m = l + n.
intros.
elim l; clear l; simpl in |- *.
assumption.
intros l' ih.
 rewrite ih.
trivial.
Qed.


Lemma lt_plus_assoc_l :
 forall n m k l : nat, n + m + k < l -> n + (m + k) < l.
intros n m k l lt.
 rewrite (plus_assoc n m k); assumption.
Qed.


Lemma my_lt_weak : forall n m : nat, S n < m -> n < m.
intros n m H.
apply lt_S_n.
apply lt_trans with m; try assumption.
apply lt_n_Sn.
Qed.






(********************************************************************)
(*      max                                                         *)


Fixpoint max (n m : nat) {struct n} : nat :=
  match n with
  | O => m
  | S p => match m with
           | O => S p
           | S q => S (max p q)
           end
  end.

Lemma le_n_max1 : forall n m : nat, n <= max n m.
intros n; elim n; clear n.
simpl in |- *.
intros m.
apply le_O_n.
intros n ih m.
case m; clear m.
simpl in |- *.
trivial.
intros m0; simpl in |- *.
apply le_n_S.
apply ih.
Qed.


Lemma le_n_max2 : forall n m : nat, n <= max m n.
intros n; elim n; clear n.
intros m.
apply le_O_n.
intros n ih m.
case m; clear m.
simpl in |- *.
trivial.
intros m0; simpl in |- *.
apply le_n_S.
apply ih.
Qed.


Lemma max_n_n : forall n : nat, max n n = n.
simple induction n; clear n; simpl in |- *. 
trivial.
intros n ih.
 rewrite ih.
trivial.
Qed.

Lemma max_Sn_n : forall n : nat, max (S n) n = S n.
simple induction n; clear n; simpl in |- *. 
trivial.
intros n ih.
 rewrite ih.
trivial.
Qed.

Lemma max_n_Sn : forall n : nat, max n (S n) = S n.
simple induction n; clear n; simpl in |- *.
trivial.
intros n ih.
 rewrite ih.
trivial.
Qed.


Lemma max_n_O : forall n : nat, max n 0 = n.
intros n; elim n; clear n.
trivial.
intros n ih.
trivial.
Qed.

