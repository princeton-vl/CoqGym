(* File: Normal_Form.v  (last edited on 27/10/2000) (c) Klaus Weich  *)

Require Export Forms.


(*******   Normal forms    ***********************************************)

Inductive normal_form : Set :=
  | NFalsum : normal_form
  | NAtom : Int -> normal_form
  | NDisj : Int -> Int -> normal_form
  | AImp : Int -> normal_form -> normal_form
  | NImp_NF : nimp -> normal_form
with nimp : Set :=
    NImp : Int -> Int -> normal_form -> nimp.




Fixpoint nf2form (x : normal_form) : form :=
  match x with
  | NFalsum => Falsum
  | NAtom i => Atom i
  | NDisj i j => OrF (Atom i) (Atom j)
  | AImp i b => Imp (Atom i) (nf2form b)
  | NImp_NF x => nimp2form x
  end
 
 with nimp2form (x : nimp) : form :=
  match x with
  | NImp i j b => Imp (Imp (Atom i) (Atom j)) (nf2form b)
  end.

Definition nf_list := list normal_form.
Definition nf_nil := nil (A:=normal_form).


Fixpoint nvimp (l : list Int) : normal_form -> normal_form :=
  match l with
  | nil => fun a : normal_form => a
  | i :: l => fun a : normal_form => nvimp l (AImp i a)
  end.


Lemma vimp2nform :
 forall (l : list Int) (a : normal_form),
 {b : normal_form | nf2form b = vimp l (nf2form a)}.
intros l; elim l; clear l.
intros a; exists a; trivial.
intros i l ih a.
elim (ih (AImp i a)); clear ih.
intros b nf_b.
exists b; assumption.
Qed.


Lemma vimp2nvimp :
 forall (l : list Int) (a : normal_form), {b : normal_form | b = nvimp l a}.
intros l; elim l; clear l.
intros a; exists a; trivial.
intros i l ih a.
elim (ih (AImp i a)); clear ih.
intros b nf_b.
exists b; assumption.
Qed.


Lemma vimp_eq_nvimp :
 forall (l : list Int) (a : normal_form),
 vimp l (nf2form a) = nf2form (nvimp l a).
intros l; elim l; clear l.
intros a; trivial.
intros i l ih a.
apply (ih (AImp i a)).
Qed.
