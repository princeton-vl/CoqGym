(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                podefs_1.v                                *)
(****************************************************************************)

Require Import Ensembles.
Require Import Relations_1.
Require Import podefs.

Section Bounds.
   Variable U : Type.
   Variable D : PO U.
   
   Let C := Carrier_of U D.
   
   Let R := Rel_of U D.
   
   Inductive Totally_ordered (B : Ensemble U) : Prop :=
       Totally_ordered_definition :
         (Included U B C ->
          forall x y : U, Included U (Couple U x y) B -> R x y \/ R y x) ->
         Totally_ordered B.
   
   Inductive Upper_Bound (B : Ensemble U) (x : U) : Prop :=
       Upper_Bound_definition :
         In U C x -> (forall y : U, In U B y -> R y x) -> Upper_Bound B x.
   
   Inductive Lower_Bound (B : Ensemble U) (x : U) : Prop :=
       Lower_Bound_definition :
         In U C x -> (forall y : U, In U B y -> R x y) -> Lower_Bound B x.
   
   Inductive Lub (B : Ensemble U) (x : U) : Prop :=
       Lub_definition :
         Upper_Bound B x ->
         (forall y : U, Upper_Bound B y -> R x y) -> Lub B x.
   
   Inductive Glb (B : Ensemble U) (x : U) : Prop :=
       Glb_definition :
         Lower_Bound B x ->
         (forall y : U, Lower_Bound B y -> R y x) -> Glb B x.
   
   Inductive Bottom (bot : U) : Prop :=
       Bottom_definition :
         In U C bot -> (forall y : U, In U C y -> R bot y) -> Bottom bot.
   
   Definition Compatible (x y : U) : Prop :=
     exists z : U,
       In U C x -> In U C y -> In U C z /\ Upper_Bound (Couple U x y) z.
   
   Inductive Directed (X : Ensemble U) : Prop :=
       Definition_of_Directed :
         Included U X C ->
         Non_empty U X ->
         (forall x1 x2 : U,
          Included U (Couple U x1 x2) X ->
          exists x3 : U, In U X x3 /\ Upper_Bound (Couple U x1 x2) x3) ->
         Directed X.
   
   Inductive Complete : Prop :=
       Definition_of_Complete :
         (exists bot : U, Bottom bot) ->
         (forall X : Ensemble U, Directed X -> exists bsup : U, Lub X bsup) ->
         Complete.
   
   Definition Cpo : Prop := Complete.
   
   Definition Chain : Prop := Totally_ordered C.
   
   Inductive Conditionally_complete : Prop :=
       Definition_of_Conditionally_complete :
         (forall X : Ensemble U,
          Included U X C ->
          (exists maj : U, Upper_Bound X maj) -> exists bsup : U, Lub X bsup) ->
         Conditionally_complete.
   
End Bounds.
Hint Unfold Carrier_of.
Hint Unfold Rel_of.
Hint Resolve Totally_ordered_definition Upper_Bound_definition
  Lower_Bound_definition Lub_definition Glb_definition Bottom_definition
  Definition_of_Complete Definition_of_Complete
  Definition_of_Conditionally_complete.