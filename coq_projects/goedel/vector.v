Require Import Coq.Lists.List.
Require Import Eqdep_dec.
Require Import Peano_dec.

Inductive Vector (A : Set) : nat -> Set :=
  | Vnil : Vector A 0
  | Vcons : forall (a : A) (n : nat), Vector A n -> Vector A (S n).

Fixpoint vector2list (A : Set) (n : nat) (v : Vector A n) {struct v} :
 list A :=
  match v with
  | Vnil => nil (A:=A)
  | Vcons a n v' => a :: vector2list A n v'
  end.

Fixpoint list2vector (A : Set) (l : list A) {struct l} :
 Vector A (length l) :=
  match l return (Vector A (length l)) with
  | nil => Vnil A
  | a :: l' => Vcons A a (length l') (list2vector A l')
  end.

Section VectorSizes.

Let nilVectorHelp (A : Set) (n : nat) (p : n = 0) : Vector A n.
intros.
induction n as [| n Hrecn].
apply Vnil.
discriminate p.
Defined.

Lemma nilVector : forall (A : Set) (x : Vector A 0), Vnil A = x.
Proof.
intro.
replace (Vnil A) with (nilVectorHelp A 0 (refl_equal 0)).
generalize (refl_equal 0).
assert
 (forall (n : nat) (e : n = 0) (x : Vector A n), nilVectorHelp A n e = x).
intros.
induction x as [| a n x Hrecx].
reflexivity.
discriminate e.
apply H.
reflexivity.
Qed.

Let consVectorHelp (A : Set) (n m : nat) (p : n = S m) 
  (a : A) (v : Vector A m) : Vector A n.
intros.
destruct n.
discriminate p.
rewrite p.
apply Vcons.
apply a.
apply v.
Defined.

Lemma consVector :
 forall (A : Set) (n : nat) (x : Vector A (S n)),
 {pair : A * Vector A n | Vcons A (fst pair) n (snd pair) = x}.
Proof.
intros.
assert
 {pair : A * Vector A n |
 consVectorHelp A _ _ (refl_equal (S n)) (fst pair) (snd pair) = x}.
generalize (refl_equal (S n)).
assert
 (forall (m : nat) (x : Vector A m) (e : m = S n),
  {pair : A * Vector A n | consVectorHelp A m n e (fst pair) (snd pair) = x}).
intros.
destruct x0 as [| a n0 v].
discriminate e.
generalize e.
inversion e.
generalize v.
rewrite H0.
intros.
exists (a, v0).
simpl in |- *.
unfold eq_rec_r in |- *.
generalize (sym_eq e0). 
intro.
elim e1 using K_dec_set.
apply eq_nat_dec.
reflexivity.
apply H.
apply H.
Qed.

End VectorSizes.