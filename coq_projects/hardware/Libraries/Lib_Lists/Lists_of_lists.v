(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*                          Solange Coupet-Grimal                           *)
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
(*                              August 6th 1996                             *)
(*                                                                          *)
(****************************************************************************)
(*                           Lists_of_lists.v                               *)
(****************************************************************************)

Require Import Dependent_lists.

Section Lists_of_lists.

(* list_of_heads takes as argument a list of non-empty lists and builds 
the list of each component heads *)

  Definition list_of_heads (A : Set) (i : nat) :=
    map (list A (S i)) A (Head A i).


(* list_of_tails takes as argument a list of lists and builds the list of 
   of each component tails *)

  Definition list_of_tails (A : Set) (i : nat) :=
    map (list A i) (list A (pred i)) (tl A i).

End Lists_of_lists.