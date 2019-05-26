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
(*                       Factorization_Prog.v                               *)
(****************************************************************************)


Require Export Factorization.

Section Factorization_for_Realizer.
   
  Variable A : Set.
  Variable BASE : BT.
  Let b := base BASE.
  Let Num := num BASE.
  Let Val_bound := val_bound BASE.
  Let Digit := digit BASE.
  Let Tl := tl Digit.
   
  Variable FR : forall n : nat, A -> inf n -> inf n -> A.

  Let R (n : nat) (a : A) (x y : inf n) (a' : A) : Prop := a' = FR n a x y.

  Notation Factorizable := (factorizable _) (only parsing).
  Notation Proper := (proper _) (only parsing).

  Theorem factorization_for_realizer :
   factorizable _ R ->
   proper _ BASE R ->
   forall (n : nat) (a : A) (X Y : Num n),
   {a' : A | R (exp b n) a (Val_bound n X) (Val_bound n Y) a'}.

  Fixpoint Impl (n : nat) : A -> Num n -> Num n -> A :=
    fun a : A =>
    match n return (Num n -> Num n -> A) with
    | O => fun X Y : Num 0 => a
    | S p =>
        fun X Y : Num (S p) =>
        Impl p (FR b a (Hd Digit p X) (Hd Digit p Y)) 
          (Tl (S p) X) (Tl (S p) Y)
    end.
  refine (fun H H' n a X Y => exist _ (Impl n a X Y) _).
  generalize X Y a; clear X Y a; elim n.
  intros X Y a.
  simpl in |- *; unfold Val_bound in |- *; unfold R in |- *; apply prop_Rel;
   auto.    (*is_proper*)
  unfold R in |- *; unfold Val_bound in |- *; unfold b in |- *;
   intros m Hr a X Y.
  apply fact_Rel; simpl in |- *; auto.  (*is_factorizable*)
  Qed.


End Factorization_for_Realizer.


(*************************************************************************************)