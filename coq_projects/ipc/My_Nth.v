(* File: My_Nth.v  (last edited on 25/10/2000) (c) Klaus Weich  *)

Require Export List.
Require Export Plus.


Section My_Nth.

Variable B : Set.

Inductive my_nth : nat -> list B -> B -> Prop :=
  | My_NthO : forall (l : list B) (a : B), my_nth 0 (a :: l) a
  | My_NthS :
      forall (n : nat) (l : list B) (b : B),
      my_nth n l b -> forall a : B, my_nth (S n) (a :: l) b.


Lemma inv_nth_nil : forall (n : nat) (a : B), my_nth n nil a -> False.
intros.
inversion H.
Qed.


Lemma inv_nthO :
 forall (a : B) (l : list B) (b : B), my_nth 0 (a :: l) b -> a = b.
intros.
inversion H.
trivial.
Qed.


Lemma inv_nthS :
 forall (n : nat) (a : B) (l : list B) (b : B),
 my_nth (S n) (a :: l) b -> my_nth n l b.
intros.
inversion H.
assumption.
Qed.


Lemma my_nth_rec :
 forall P : nat -> list B -> B -> Set,
 (forall (l : list B) (a : B), P 0 (a :: l) a) ->
 (forall (n : nat) (l : list B) (b : B),
  my_nth n l b -> P n l b -> forall a : B, P (S n) (a :: l) b) ->
 forall (n : nat) (l : list B) (y : B), my_nth n l y -> P n l y.
intros P base step n.
elim n; clear n.
intros l; case l; clear l.
intros y nth; elimtype False.
apply (inv_nth_nil 0 y nth).
intros a l b nth.
 rewrite (inv_nthO a l b nth).
apply base.

intros n ih l.
case l; clear l.
intros y nth; elimtype False.
apply (inv_nth_nil (S n) y nth).
intros a l b nth.
apply step.
apply (inv_nthS n a l b nth).
apply ih.
apply (inv_nthS n a l b nth).
Qed.


Lemma nth_in : forall (n : nat) (l : list B) (a : B), my_nth n l a -> In a l.
intros n l a nth.
elim nth; clear nth.
intros.
simpl in |- *; left; trivial.
intros.
simpl in |- *; right; assumption.
Qed.


Lemma nth_app0 :
 forall (n : nat) (l0 l1 : list B) (a : B),
 my_nth n l0 a -> my_nth n (l0 ++ l1) a.
intros n l0.
generalize n; clear n.
elim l0; clear l0.
intros n l1 a nth; elimtype False.
apply (inv_nth_nil n a nth).
intros a0 l0 ih n.
case n; clear n.
intros l1 a nth.
 rewrite (inv_nthO a0 l0 a nth).
simpl in |- *; apply My_NthO.
intros n l1 a nth.
simpl in |- *; apply My_NthS.
apply ih.
apply (inv_nthS n a0 l0 a nth).
Qed.


Lemma nth_app1 :
 forall (n : nat) (l0 l1 : list B) (a : B),
 my_nth n l1 a -> my_nth (length l0 + n) (l0 ++ l1) a.
intros n l0; elim l0; clear l0.
simpl in |- *; trivial.
intros a0 l0 ih l1 a nth.
simpl in |- *.
apply My_NthS.
apply ih.
assumption.
Qed.


Inductive inv_my_nth_app (n : nat) (l0 l1 : list B) (a : B) : Set :=
  | Inv_Nth_App0 : my_nth n l0 a -> inv_my_nth_app n l0 l1 a
  | Inv_Nth_App1 :
      forall n' : nat, my_nth n' l1 a -> inv_my_nth_app n l0 l1 a.

Lemma inv_nth_app :
 forall (n : nat) (l0 l1 : list B) (a : B),
 my_nth n (l0 ++ l1) a -> inv_my_nth_app n l0 l1 a.
intros n l0 l1 a.
generalize n; clear n.
elim l0; clear l0; simpl in |- *.
intros n nth.
right with n.
assumption.
intros a0 l0 ih_l0 n.
case n; clear n.
intros nth.
left.
 rewrite (inv_nthO a0 (l0 ++ l1) a nth).
apply My_NthO.
intros n nth.
elim (ih_l0 n).
intros nth_l0.
left.
apply My_NthS; assumption.
intros n' nth_l1.
right with n'; assumption.
apply inv_nthS with a0; assumption.
Qed.



Inductive nth_split (a : B) (l : list B) : Set :=
    Nth_Split_Intro :
      forall l1 l2 : list B, l = l1 ++ a :: l2 -> nth_split a l.     

Lemma my_nth_split :
 forall (n : nat) (l : list B) (a : B), my_nth n l a -> nth_split a l.
intros n; elim n; clear n.
intros l a nth.
apply Nth_Split_Intro with (nil (A:=B)) (tail l).
inversion_clear nth.
simpl in |- *; trivial.
intros n ih l a. 
case l; clear l.
intros nth; elimtype False; inversion_clear nth.
intros a0 l nth.
elim (ih l a); clear ih.
intros l1 l2 H.
apply Nth_Split_Intro with (a0 :: l1) l2.
 rewrite H; simpl in |- *; trivial.
inversion_clear nth; assumption.
Qed.

Lemma in_nth :
 forall (a : B) (l : list B), In a l -> exists n : nat, my_nth n l a.
intros b l; elim l; clear l.
intros in_b; inversion_clear in_b.
intros a l ih in_a.
inversion_clear in_a.
exists 0.
 rewrite H.
apply My_NthO.
elim ih; try assumption.
intros n nth.
exists (S n).
apply My_NthS; assumption.
Qed.

End My_Nth.