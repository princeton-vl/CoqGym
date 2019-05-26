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
(*                              Linear_Structures.v                               *)
(****************************************************************************)

Require Export Dependent_lists.


Section Linear_Structures.

  Variable A B C : Set.
  Variable cell : A -> B -> C -> A -> Prop.

  Inductive connection :
  forall n : nat, A -> list B n -> list C n -> A -> Prop :=
    | C_O : forall a : A, connection 0 a (nil B) (nil C) a
    | C_Sn :
        forall (n : nat) (a a1 a' : A) (b : B) (c : C) 
          (lb : list B n) (lc : list C n),
        cell a b c a1 ->
        connection n a1 lb lc a' ->
        connection (S n) a (cons B n b lb) (cons C n c lc) a'.


End Linear_Structures.

