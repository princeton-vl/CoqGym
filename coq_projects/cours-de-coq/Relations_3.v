(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                              Relations_3.v                               *)
(****************************************************************************)

Require Import Relations_1.
Require Import Relations_2.

Section Relations_3.
   Variable U : Type.
   Variable R : Relation U.
   
   Definition coherent (x y : U) : Prop :=
     exists z : U, Rstar U R x z /\ Rstar U R y z.
   
   Definition locally_confluent (x : U) : Prop :=
     forall y z : U, R x y -> R x z -> coherent y z.
   
   Definition Locally_confluent : Prop := forall x : U, locally_confluent x.
   
   Definition confluent (x : U) : Prop :=
     forall y z : U, Rstar U R x y -> Rstar U R x z -> coherent y z.
   
   Definition Confluent : Prop := forall x : U, confluent x.
   
   Inductive noetherian : U -> Prop :=
       definition_of_noetherian :
         forall x : U, (forall y : U, R x y -> noetherian y) -> noetherian x.
   
   Definition Noetherian : Prop := forall x : U, noetherian x.
   
End Relations_3.
Hint Unfold coherent.
Hint Unfold locally_confluent.
Hint Unfold confluent.
Hint Unfold Confluent.
Hint Resolve definition_of_noetherian.
Hint Unfold Noetherian.