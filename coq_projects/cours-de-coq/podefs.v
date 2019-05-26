(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                 podefs.v                                 *)
(****************************************************************************)

Require Import Ensembles.
Require Import Relations_1.

Section Partial_orders.
   Variable U : Type.
   
   Definition Carrier := Ensemble U.
   
   Definition Rel := Relation U.
   
   Inductive PO : Type :=
       Definition_of_PO :
         forall (C : Carrier) (R : Rel), Non_empty U C -> Order U R -> PO.
   
   Theorem Carrier_of : PO -> Carrier.
   intro H'; elim H'.
   intros C R H'0 H'1; exact C.
   Defined.

   Theorem Rel_of : PO -> Rel.
   intro H'; elim H'.
   intros C R H'0 H'1; exact R.
   Defined.

   Definition SRel_of (p : PO) : Rel := fun x y : U => Rel_of p x y /\ x <> y.
   
End Partial_orders.
Hint Unfold Carrier_of Rel_of.