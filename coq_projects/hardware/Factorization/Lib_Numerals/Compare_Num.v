(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*                   Solange Coupet-Grimal & Line Jakubiec                  *)
(*                                                                          *)
(*                                                                          *)
(*              Laboratoire d'Informatique de Marseille                     *)
(*               CMI-Technopole de Chateau-Gombert                          *)
(*                   39, Rue F. Joliot Curie                                *)
(*                   13453 MARSEILLE Cedex 13                               *)
(*           e-mail:{Solange.Coupet,Line.Jakubiec}@lim.univ-mrs.fr          *)
(*                                                                          *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              May 30th 1996                               *)
(*                                                                          *)
(****************************************************************************)
(*                             Compare_Num.v                                *)
(****************************************************************************)
Require Export Numerals.
Require Export Compare_Nat.

Section compare_num.

  Variable BASE : BT.
  Let Digit := digit BASE.
  Let valB := val BASE.
  Let ValB := Val BASE.
  Let Num := num BASE.
  Let Val_bound := val_bound BASE.
  Let Cons := cons Digit.
  Let Nil := nil Digit.

  Lemma Comp_dif :
   forall (n : nat) (x y : Digit) (X Y : Num n),
   valB x < valB y ->
   Compare_Nat.comparison (ValB (S n) (Cons n x X)) (ValB (S n) (Cons n y Y)) =
   L.
  intros n x y X Y l.
  apply comparisonL.
  unfold ValB in |- *.
  unfold Cons in |- *.
  unfold Digit in |- *.
  apply comp_dif.
  auto.
  Qed.
  Hint Resolve Comp_dif.

  Lemma Comp_eq :
   forall (n : nat) (x y : Digit) (X Y : Num n),
   valB x = valB y ->
   Compare_Nat.comparison (ValB (S n) (Cons n x X)) (ValB (S n) (Cons n y Y)) =
   Compare_Nat.comparison (ValB n X) (ValB n Y).

  intros n x y X Y e.
  cut
   (Compare_Nat.comparison (ValB n X) (ValB n Y) =
    Compare_Nat.comparison (ValB n X) (ValB n Y)); 
   auto.
  pattern (Compare_Nat.comparison (ValB n X) (ValB n Y)) at 2 3 in |- *.
  case (Compare_Nat.comparison (ValB n X) (ValB n Y)); intros c.
  unfold ValB in |- *; unfold Cons in |- *; unfold Digit in |- *.
  apply comparisonL.
  apply comp_eq_most; auto.
  simpl in |- *.
  unfold valB in e.
  rewrite e.
  rewrite (inv_comparisonE (ValB n X) (ValB n Y) c).
  apply comparisonE; auto.
  apply comparisonG.
  unfold gt in |- *.
  unfold ValB in |- *; unfold Cons in |- *; unfold Digit in |- *.
  apply comp_eq_most.
  auto.
  cut (Val BASE n X > Val BASE n Y); auto.
  Qed.

End compare_num.

Hint Resolve Comp_eq.
Hint Resolve Comp_dif.