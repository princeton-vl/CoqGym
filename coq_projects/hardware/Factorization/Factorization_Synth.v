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
(*                         Factorization_Synth.v                            *)
(****************************************************************************)



Require Export Factorization.

 Section Factorization_for_Synthesis.
 
   Variable A : Set.
   Variable BASE : BT.
   Let b := base BASE.
   Let Num := num BASE.
   Let Digit := digit BASE.
   Let Val_bound := val_bound BASE.
   Definition Tl := tl Digit.

   Variable FR : forall n : nat, A -> inf n -> inf n -> A.

   Let R (n : nat) (a : A) (x y : inf n) (a' : A) : Prop := a' = FR n a x y.

   Notation Factorizable := (factorizable _) (only parsing).
   Notation Proper := (proper _) (only parsing).

   Theorem factorization_for_synthesis :
    factorizable _ R ->
    proper _ BASE R ->
    forall (n : nat) (X Y : Num n) (a : A),
    {a' : A | R (exp b n) a (Val_bound n X) (Val_bound n Y) a'}.
  intros F P.
  simple induction n.
  intros X Y a.
  exists a.
  simpl in |- *.
  unfold R in |- *; unfold Val_bound in |- *; apply prop_Rel.
  try trivial.
  clear n; intros n H_rec X Y a.
  elim
   (H_rec (Tl (S n) X) (Tl (S n) Y) (FR b a (Hd Digit n X) (Hd Digit n Y))).
  intros a' H; exists a'.
  unfold b in |- *; unfold R in |- *; unfold Val_bound in |- *.
  apply fact_Rel; try trivial.
  Defined.

End Factorization_for_Synthesis.

 
(*************************************************************************************)