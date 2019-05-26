(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import List.
Require Import Bar.
Section OpenIndGoodRel.
Variable A : Set.
Variable lt R : Rel A.
Variable wflt : well_founded lt.

Inductive Min : list A -> Set :=
  | nmin : Min nil
  | cmin :
      forall (a : A) (l : list A),
      Min l -> (forall y : A, lt y a -> GRBar A R (y :: l)) -> Min (a :: l).
Hint Resolve nmin cmin.

Lemma OpenInd :
 forall xs : list A,
 Min xs ->
 (forall a : A, Min (a :: xs) -> GRBar A R (a :: xs)) -> GRBar A R xs.
intros; red in |- *.
apply Ind; auto.
intros a; elim (wflt a); auto.
intros x H' H'0; red in H0; auto.
Qed.
End OpenIndGoodRel.
