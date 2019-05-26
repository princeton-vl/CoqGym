(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                              Relations_2.v                               *)
(****************************************************************************)

Require Import Relations_1.

Section Relations_2.
   Variable U : Type.
   Variable R : Relation U.
   
   Inductive Rstar : Relation U :=
     | Rstar_0 : forall x : U, Rstar x x
     | Rstar_n : forall x y z : U, R x y -> Rstar y z -> Rstar x z.
   
   Inductive Rstar1 : Relation U :=
     | Rstar1_0 : forall x : U, Rstar1 x x
     | Rstar1_1 : forall x y : U, R x y -> Rstar1 x y
     | Rstar1_n : forall x y z : U, Rstar1 x y -> Rstar1 y z -> Rstar1 x z.
   
   Inductive Rplus : Relation U :=
     | Rplus_0 : forall x y : U, R x y -> Rplus x y
     | Rplus_n : forall x y z : U, R x y -> Rplus y z -> Rplus x z.
   
   Definition Strongly_confluent : Prop :=
     forall x a b : U, R x a -> R x b -> exists z : U, R a z /\ R b z.
   
End Relations_2.
Hint Resolve Rstar_0.
Hint Resolve Rstar1_0.
Hint Resolve Rstar1_1.
Hint Resolve Rplus_0.