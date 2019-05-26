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
(*                           Factorization_Verif.v                          *)
(****************************************************************************)



Require Export Linear_Structures. 
Require Export Factorization.

Section Factorization_for_Verification.

  Variable A : Set.
  Variable BASE : BT.
  Let b := base BASE.
  Let Num := num BASE.
  Let Digit := digit BASE.
  Let Val_bound := val_bound BASE.
             
  Variable R : forall n : nat, A -> inf n -> inf n -> A -> Prop.

  Definition Connection := connection A Digit Digit (R b).

  Notation Factorizable := (factorizable _) (only parsing).
  Notation Proper := (proper _) (only parsing).

  Theorem factorization_for_verification :
   factorizable _ R ->
   proper _ BASE R ->
   forall (n : nat) (X Y : Num n) (a a' : A),
   Connection n a X Y a' -> R (exp b n) a (Val_bound n X) (Val_bound n Y) a'.
    intros F P.
    simple induction 1.
    unfold proper in P; auto.
    clear H X Y n a a'.
    intros n a a1 a' d d' D D' H C H_rec.
    simpl in |- *.
    apply F with d d' (Val_bound n D) (Val_bound n D') a1;
     try trivial; unfold Diveucl in |- *; 
     split; simpl in |- *.
    elim (mult_comm (exp (base BASE) n) (val BASE d)); unfold val in |- *;
     unfold val_inf in |- *; auto.
    unfold b in |- *; apply upper_bound.
    elim (mult_comm (exp (base BASE) n) (val BASE d')); unfold val in |- *;
     unfold val_inf in |- *; auto.
    unfold b in |- *; apply upper_bound.
    Qed.

End Factorization_for_Verification.


(*************************************************************************************)