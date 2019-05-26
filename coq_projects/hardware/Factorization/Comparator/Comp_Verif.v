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
(*                               Comp_Verif.v                               *)
(****************************************************************************)

Require Import Factorization_Verif.
Require Import Comparator_Relation.

Parameter BASE : BT.
Definition b := base BASE.
Definition Digit := digit BASE.
Definition Num := num BASE.
Definition Val_bound := val_bound BASE.
Definition Value := Val BASE.

Definition Connection := connection order (inf b) (inf b) (R b). 
 

Theorem general_correct :
 forall (n : nat) (X Y : Num n) (o o' : order),
 Connection n o X Y o' -> R (exp b n) o (Val_bound n X) (Val_bound n Y) o'.
intros n X Y o o' C.
unfold b in |- *.
apply factorization_for_verification with (A := order) (BASE := BASE).
exact is_factorizable.
exact (is_proper BASE).
try trivial.
Qed.
 

Theorem correctness :
 forall (n : nat) (X Y : Num n) (o : order),
 Connection n E X Y o -> o = Compare_Nat.comparison (Value n X) (Value n Y).
intros n X Y o.
generalize (general_correct n X Y E o).
unfold R in |- *; simpl in |- *; auto.
Qed.

 

(*************************************************************************************)