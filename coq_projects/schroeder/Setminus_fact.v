(* Contribution to the Coq Library   V6.3 (July 1999)                       *)
(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.11                                 *)
(*                              Feb 2nd 1996                                *)
(*                                                                          *)
(*                (notations and layout updated March 2009)                 *)
(****************************************************************************)
(*                            Setminus_fact.v                               *)
(****************************************************************************)
(* This file is distributed under the terms of the                          *) 
(* GNU Lesser General Public License Version 2.1                            *)
(****************************************************************************)

Require Import Ensembles.    (* Ensemble, In, Included, Setminus *)

Section Contravariance_of_Setminus.

Variable U : Type.

Lemma Setminus_contravariant :
 forall A B B' : Ensemble U,
 Included U B' B -> Included U (Setminus U A B) (Setminus U A B').
intros A B B' B'_Included_B; unfold Setminus in |- *.
red in |- *; intros x x_in_B.
elim x_in_B; intros x_in_A x_in_nonB.
split.
  assumption.
red in |- *; intro x_in_B'.
apply x_in_nonB.
apply B'_Included_B.
assumption.
Qed.

End Contravariance_of_Setminus.


(* $Id$ *)
