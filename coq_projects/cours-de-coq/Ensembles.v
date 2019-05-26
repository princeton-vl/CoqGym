(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                                                          *)
(*      Initial Version: Frederic Prost, July 1993                          *)
(*      Revised Version: Gilles Kahn, September 1993                        *)
(*      Revised Version: Gilles Kahn, November 1993                         *)
(*      Revised Version: Gilles Kahn, April 1994                            *)
(*                               INRIA Sophia-Antipolis, FRANCE             *)
(*      Revised Version: Jean-Christophe Filliatre, January 1995            *)
(*                               ENS-Lyon, FRANCE                           *)
(*                                                                          *)
(****************************************************************************)
(*                               Ensembles.v                                *)
(****************************************************************************)

Require Import Classical.

Section Ensembles.
   Variable U : Type.
   
   Definition Ensemble := U -> Prop.
   
   Definition In (B : Ensemble) (x : U) : Prop := B x.
   
   Definition Included (B C : Ensemble) : Prop :=
     forall x : U, In B x -> In C x.
   
   Inductive Empty_set : Ensemble :=.
   
   Inductive Singleton (x : U) : Ensemble :=
       In_singleton : In (Singleton x) x.
   
   Inductive Union (B C : Ensemble) : Ensemble :=
     | Union_introl : forall x : U, In B x -> In (Union B C) x
     | Union_intror : forall x : U, In C x -> In (Union B C) x.
   
   Inductive Intersection (B C : Ensemble) : Ensemble :=
       Intersection_intro :
         forall x : U, In B x -> In C x -> In (Intersection B C) x.
   
   Inductive Couple (x y : U) : Ensemble :=
     | Couple_l : In (Couple x y) x
     | Couple_r : In (Couple x y) y.
   
   Inductive Setminus (B C : Ensemble) : Ensemble :=
       Setminus_intro :
         forall x : U, In B x -> ~ In C x -> In (Setminus B C) x.
   
   Inductive Disjoint (B C : Ensemble) : Prop :=
       Disjoint_intro :
         (forall x : U, ~ In (Intersection B C) x) -> Disjoint B C.
   
   Inductive Non_empty (B : Ensemble) : Prop :=
       Non_empty_intro : forall x : U, In B x -> Non_empty B.
   
   Inductive Finite : Ensemble -> Prop :=
     | Empty_is_finite : Finite Empty_set
     | Union_is_finite :
         forall A : Ensemble,
         Finite A -> forall x : U, ~ In A x -> Finite (Union (Singleton x) A).

 (*************************************************************************)
 (*** Initialement, la definition de Same_set etait :
   
   Inductive Same_set [B,C: Ensemble]: Prop :=
         Same_set_intro: (Included B C) -> (Included C B) -> (Same_set B C).

  *** mais dans le lemme Same_set_equivalence de ps.v (par exemple)
      	(Same_set U)
      n'est plus unifie avec
      	[x,y:(Ensemble U)](and (Included x y) (Included y x))

  *** on redefinit donc Same_set et Same_Set_intro de la maniere
      suivante : ***)
 (*************************************************************************)

   Definition Same_set (B C : Ensemble) : Prop :=
     Included B C /\ Included C B.
      
   Lemma Same_set_intro :
    forall B C : Ensemble, Included B C -> Included C B -> Same_set B C.
   intros B C H H'.
   unfold Same_set in |- *.
   split; [ exact H | exact H' ].
   Qed.

 (*************************************************************************)

   Axiom
     Extensionality_Ensembles :
       forall A B : Ensemble, Same_set A B -> A = B :>Ensemble.
   
End Ensembles.
Hint Unfold In.
Hint Unfold Included.
Hint Resolve Same_set_intro.
Hint Resolve Union_introl Union_intror.
Hint Resolve Intersection_intro.
Hint Resolve In_singleton.
Hint Resolve Couple_l Couple_r.
Hint Resolve Setminus_intro.
Hint Resolve Disjoint_intro.
Hint Resolve Empty_is_finite Union_is_finite.
Hint Resolve Extensionality_Ensembles.

