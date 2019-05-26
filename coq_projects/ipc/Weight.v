(* File: Weight.v  (last edited on 27/10/2000) (c) Klaus Weich  *)


Require Import Rules.


Fixpoint weight (a : form) : nat :=
  match a with
  | Falsum => 1
  | Atom _ => 1
  | AndF a b => S (weight a + weight b)
  | OrF Falsum b => S (weight b)
  | OrF (Atom _) b => S (weight b)
  | OrF a b => S (S (weight b + weight a))
  | Imp a b => weight_neg a + weight b
  end
 
 with weight_neg (a : form) : nat :=
  match a with
  | Falsum => 0
  | Atom _ => 0
  | AndF a b => S (weight_neg a + weight_neg b)
  | OrF a b => S (S (S (weight_neg a + weight_neg b)))
  | Imp Falsum b => 1
  | Imp (Atom _) Falsum => 2
  | Imp (Atom _) (Atom _) => 1
  | Imp (Atom _) b => S (S (S (weight_neg b)))
  | Imp a b => S (S (S (S (weight_neg b + weight a))))
  end.


Fixpoint weight_goal (a : form) : nat :=
  match a with
  | Falsum => 0
  | Atom _ => 0
  | AndF _ _ => 1
  | OrF _ _ => 1
  | Imp _ b => S (weight_goal b)
  end.


Definition weight_gamma :=
  fold_right (fun (a : form) (n : nat) => weight a + n) 0.

(**********************************************************************)

Lemma weight_ge_1 : forall a : form, 1 <= weight a.
intros a; elim a; clear a.
trivial.
trivial.
intros; simpl in |- *.
apply le_n_S.
apply le_O_n.
intros a ih_a b ih_b.
clear ih_a ih_b.
case a; clear a; intros; simpl in |- *; apply le_n_S; apply le_O_n.
intros a ih_a b ih_b.
simpl in |- *.
fold weight_neg in |- *.
apply le_trans with (weight b); try assumption.
apply (plus_le_compat_r 0 (weight_neg a) (weight b)).
apply le_O_n.
Qed.

Lemma weight_neg_le :
 forall (j : Int) (a : form),
 weight_neg (Imp (Atom j) a) <= S (S (S (weight_neg a))).
intros j a; case a; clear a.
apply le_n_Sn.
intros; apply le_trans with 2; apply le_n_Sn.
intros; apply le_n.
intros; apply le_n.
intros; apply le_n.
Qed.


Lemma weight_vimp :
 forall (l : list Int) (a : form), weight (vimp l a) = weight a.
intros l.
elim l; clear l.
intro a; trivial.
intros i l ih a.
simpl in |- *.
apply ih with (a := Imp (Atom i) a).
Qed.



Lemma weight_gamma_weak :
 forall (a b : form) (gamma : flist) (n : nat),
 weight a < weight b ->
 weight_gamma (b :: gamma) < S n -> weight_gamma (a :: gamma) < n.
intros.
simpl in |- *.
apply lt_S_n.
apply le_lt_trans with (weight_gamma (b :: gamma)); try assumption.
simpl in |- *.
apply lt_le_S.
apply plus_lt_compat_r.
assumption.
Qed.


Lemma weight_gamma_weak' :
 forall (a b : form) (gamma : flist) (n : nat),
 weight a < weight b ->
 weight b + weight_gamma gamma < S n -> weight a + weight_gamma gamma < n.
intros.
apply (weight_gamma_weak a b gamma n); assumption.
Qed.


Lemma weight_gamma_weak2 :
 forall (a b c : form) (gamma : flist) (n : nat),
 weight a + weight b < weight c ->
 weight_gamma (c :: gamma) < S n -> weight_gamma (a :: b :: gamma) < n.
intros.
simpl in |- *.
apply lt_plus_assoc_l.
apply lt_S_n.
apply le_lt_trans with (weight_gamma (c :: gamma)); try assumption.
simpl in |- *.
apply lt_le_S.
apply plus_lt_compat_r.
assumption.
Qed.


Lemma weight_gamma_weak2' :
 forall (a b c : form) (gamma : flist) (n : nat),
 weight a + weight b < weight c ->
 weight c + weight_gamma gamma < S n ->
 weight a + (weight b + weight_gamma gamma) < n.
intros.
apply (weight_gamma_weak2 a b c gamma n); assumption.
Qed.


Lemma weight_gamma_weak3 :
 forall (a b c d : form) (gamma : flist) (n : nat),
 weight a + weight b + weight c < weight d ->
 weight_gamma (d :: gamma) < S n -> weight_gamma (a :: b :: c :: gamma) < n.
intros.
simpl in |- *.
apply lt_plus_assoc_l.
apply lt_plus_assoc_l.
apply lt_S_n.
apply le_lt_trans with (weight_gamma (d :: gamma)); try assumption.
simpl in |- *.
apply lt_le_S.
apply plus_lt_compat_r.
assumption.
Qed.


Lemma weight_gamma_weak3' :
 forall (a b c d : form) (gamma : flist) (n : nat),
 weight a + weight b + weight c < weight d ->
 weight d + weight_gamma gamma < S n ->
 weight a + (weight b + (weight c + weight_gamma gamma)) < n.
intros.
apply (weight_gamma_weak3 a b c d gamma n); assumption.
Qed.
