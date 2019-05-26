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
(*                                  Sum.v                                   *)
(****************************************************************************)
(* This file is distributed under the terms of the                          *) 
(* GNU Lesser General Public License Version 2.1                            *)
(****************************************************************************)

Require Import Ensembles.    (* Ensemble, In, Included, Setminus *)

Section Set_Sums.

Variable U : Type.

Inductive Set_Sum (D : Ensemble (Ensemble U)) : U -> Prop :=
    Set_Sum_intro :
      forall B : Ensemble U,
      In (Ensemble U) D B -> forall x : U, In U B x -> Set_Sum D x.

Lemma Set_Sum_is_majoring :
 forall (D : Ensemble (Ensemble U)) (A : Ensemble U),
 (forall C : Ensemble U, D C -> Included U C A) -> Included U (Set_Sum D) A.
intros.
red in |- *; intros x x_in_Set_Sum_D.
red in x_in_Set_Sum_D.
elim x_in_Set_Sum_D.
assumption.
Qed.

Lemma Set_Sum_is_minoring :
 forall (D : Ensemble (Ensemble U)) (A : Ensemble U),
 In (Ensemble U) D A -> Included U A (Set_Sum D).
do 2 intro; red in |- *; intros A_in_D x x_in_A.
red in |- *; apply Set_Sum_intro with A; assumption.
Qed.

End Set_Sums.

(* $Id$ *)
