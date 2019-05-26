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
(*                               Functions.v                                *)
(****************************************************************************)
(* This file is distributed under the terms of the                          *) 
(* GNU Lesser General Public License Version 2.1                            *)
(****************************************************************************)

Require Import Ensembles.    (* Ensemble, In, Included, Setminus *)
Require Import Relations_1.  (* Relation *)

(****************************************************************************)
(** In contrast with the definition of functions in Relations_1, we         *)
(** consider, here, functions as binary relations                           *)

Section Functions.

Variable U : Type.

(****************************************************************************)
(** Characterization of a relation over two sets                            *)

Inductive Rel (U : Type) (A B : Ensemble U) (R : Relation U) : Prop :=
    Rel_intro :
      (forall x y : U, R x y -> In U A x) ->
      (forall x y : U, R x y -> In U B y) -> Rel U A B R.
 

(****************************************************************************)
(**              Image of a set through a relation                          *)

Section Image.

Inductive Im (R : Relation U) (A : Ensemble U) (y : U) : Prop :=
    Im_intro : forall x : U, R x y -> In U A x -> Im R A y.

Lemma Im_stable_par_incl :
 forall (R : Relation U) (A1 A2 : Ensemble U),
 Included U A1 A2 -> Included U (Im R A1) (Im R A2).
do 3 intro; intros A1_Included_A2; red in |- *; red in |- *;
 intros x x_in_Im_A1.
elim x_in_Im_A1.
intros.
apply Im_intro with x0; try assumption.
apply A1_Included_A2; assumption.
Qed.

End Image.


Variable A B : Ensemble U.
Variable f : Relation U.


Definition to_at_most_one_output := forall x y z : U, f x y -> f x z -> y = z.

Definition to_at_least_one_output := forall x : U, In U A x -> exists y, f x y.

Definition from_at_most_one_input := forall x y z : U, f x z -> f y z -> x = y.

Definition from_at_least_one_input := forall y : U, In U B y -> exists x, f x y.


Inductive function : Prop := (* fun_in *)
    function_intro :
      Rel U A B f -> to_at_most_one_output -> to_at_least_one_output -> function.

Inductive surjection : Prop := (* fun_on *)
    surjection_intro :
      Rel U A B f ->
      to_at_most_one_output -> to_at_least_one_output -> from_at_least_one_input -> surjection.

Inductive injection : Prop := (* map_in *)
    injection_intro :
      Rel U A B f ->
      to_at_most_one_output -> to_at_least_one_output -> from_at_most_one_input -> injection.

Inductive bijection : Prop := (* map_on *)
    bijection_intro :
      Rel U A B f ->
      to_at_most_one_output ->
      to_at_least_one_output -> from_at_most_one_input -> from_at_least_one_input -> bijection.

End Functions.


(* $Id$ *)
