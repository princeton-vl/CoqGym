(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                                                          *)
(*        Initial Version: Frederic Prost, July 1993                        *)
(*        Revised Version: Gilles Kahn, September 1993                      *)
(*        Revised for a tutorial on Coq:  Gilles Kahn, March 1994           *)
(*                                     INRIA Sophia-Antipolis, FRANCE       *)
(*                                                                          *)
(****************************************************************************)
(*                              Relations_1.v                               *)
(****************************************************************************)

Section Relations_1.
   Variable U : Type.
   
   Definition Relation := U -> U -> Prop.
   Variable R : Relation.
   
   Definition Reflexive : Prop := forall x : U, R x x.
   
   Definition Transitive : Prop := forall x y z : U, R x y -> R y z -> R x z.
   
   Definition Symmetric : Prop := forall x y : U, R x y -> R y x.
   
   Definition Antisymmetric : Prop :=
     forall x y : U, R x y -> R y x -> x = y :>U.
   
   Definition contains (R R' : Relation) : Prop :=
     forall x y : U, R' x y -> R x y.
   
   Definition same_relation (R R' : Relation) : Prop :=
     contains R R' /\ contains R' R.
   
   Inductive Preorder : Prop :=
       Definition_of_preorder : Reflexive -> Transitive -> Preorder.
   
   Inductive Order : Prop :=
       Definition_of_order :
         Reflexive -> Transitive -> Antisymmetric -> Order.
   
   Inductive Equivalence : Prop :=
       Definition_of_equivalence :
         Reflexive -> Transitive -> Symmetric -> Equivalence.
   
   Inductive PER : Prop :=
       Definition_of_PER : Symmetric -> Transitive -> PER.
   
End Relations_1.
Hint Unfold Reflexive.
Hint Unfold Transitive.
Hint Unfold Antisymmetric.
Hint Unfold Symmetric.
Hint Unfold contains.
Hint Unfold same_relation.
Hint Resolve Definition_of_preorder.
Hint Resolve Definition_of_order.
Hint Resolve Definition_of_equivalence.
Hint Resolve Definition_of_PER.