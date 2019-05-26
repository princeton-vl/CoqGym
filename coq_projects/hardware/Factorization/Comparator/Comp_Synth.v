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
(*                              Comp_Synth .v                               *)
(****************************************************************************)

Require Import Factorization_Synth.
Require Import Comparator_Relation.

Parameter BASE : BT.
Definition b := base BASE.
Definition Num := num BASE.
Definition Val_bound := val_bound BASE.
 
Lemma Comparator :
 forall (n : nat) (o : order) (X Y : Num n),
 {o' : order | R (exp b n) o (Val_bound n X) (Val_bound n Y) o'}.
intros n o X Y.
unfold R in |- *; unfold b in |- *; unfold Val_bound in |- *.
apply factorization_for_synthesis.
exact is_factorizable.
exact (is_proper BASE).
Defined.


(*************************************************************************************)