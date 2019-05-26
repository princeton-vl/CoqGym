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
(*                                Lib_Fact.v                                *)
(****************************************************************************)

Require Export Arith.


Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S p => S p * factorial p
  end.



Lemma fact_pred :
 forall n : nat, 0 < n -> factorial n = n * factorial (pred n).
simple induction n; auto with arith.
Qed.
Hint Resolve fact_pred.


(************************************************************************)
