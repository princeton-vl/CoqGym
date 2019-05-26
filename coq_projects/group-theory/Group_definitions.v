(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(*                           Group Theory in Coq                            *)
(*                                                                          *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*									    *)
(*			         Gilles Kahn 				    *)
(*									    *)
(*                                  INRIA                                   *)
(*                             Sophia-Antipolis                             *)
(*									    *)
(*				 January 1996				    *)
(*                                                                          *)
(****************************************************************************)

Require Import Ensembles.
Require Import Laws.
Section group_definition.
Variable U : Type.

Record Group : Type := group
  {G_ : Ensemble U;
   star_ : U -> U -> U;
   inv_ : U -> U;
   e_ : U;
   G0_ : endo_operation U G_ star_;
   G1_ : associative U star_;
   G2a_ : In U G_ e_;
   G2b_ : left_neutral U star_ e_;
   G2c_ : right_neutral U star_ e_;
   G3a_ : endo_function U G_ inv_;
   G3b_ : right_inverse U star_ inv_ e_;
   G3c_ : left_inverse U star_ inv_ e_}.

Inductive subgroup (g1 g2 : Group) : Prop :=
    Definition_of_subgroup :
      Included U (G_ g1) (G_ g2) -> star_ g1 = star_ g2 -> subgroup g1 g2.

Definition Setsubgroup (E : Ensemble U) (Gr : Group) : Prop :=
  ex (fun g : Group => subgroup g Gr /\ G_ g = E).
End group_definition.

