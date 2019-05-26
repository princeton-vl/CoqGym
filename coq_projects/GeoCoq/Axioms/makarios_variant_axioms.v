(*  Roland Coghetto, 17 March 2018
     GNU Lesser General Public License v3.0 
     See LICENSE GeoCoq 2.3.0 

    MODIFY makarios_variant_axioms,v, Version GeoCoq 2.3.0
    SPLIT Tarski_neutral_dimensionless_variant
     a) Tarski_neutral_dimensionless_variant 
     b) Tarski_neutral_dimensionless_variant_with_decidable_point_equality
*)

(** We describe here a variant of the axiom system proposed by T.J.M. Makarios in June 2013. *)
(** This variant has a slightly different five_segment  axioms and allows to remove the 
    cong_pseudo_reflexivity axiom.
    All axioms have been shown to be independent except cong_identity and inner_pasch. *)

Class Tarski_neutral_dimensionless_variant := {
 MTpoint : Type;
 BetM : MTpoint -> MTpoint -> MTpoint -> Prop;
 CongM : MTpoint -> MTpoint -> MTpoint -> MTpoint -> Prop;
 Mcong_identity : forall A B C, CongM A B C C -> A = B;
 Mcong_inner_transitivity : forall A B C D E F,
   CongM A B C D -> CongM A B E F -> CongM C D E F;
 Msegment_construction : forall A B C D,
   exists E, BetM A B E /\ CongM B E C D;
 Mfive_segment : forall A A' B B' C C' D D',
   CongM A B A' B' ->
   CongM B C B' C' ->
   CongM A D A' D' ->
   CongM B D B' D' ->
   BetM A B C -> BetM A' B' C' -> A <> B ->
   CongM D C C' D';
 Mbetween_identity : forall A B, BetM A B A -> A = B;
 Minner_pasch : forall A B C P Q,
   BetM A P C -> BetM B Q C ->
   exists X, BetM P X B /\ BetM Q X A;
 MPA : MTpoint;
 MPB : MTpoint;
 MPC : MTpoint;
 Mlower_dim : ~ (BetM MPA MPB MPC \/ BetM MPB MPC MPA \/ BetM MPC MPA MPB)
 }.

Class Tarski_neutral_dimensionless_variant_with_decidable_point_equality
 `(Tn : Tarski_neutral_dimensionless_variant) :=
{
 Mpoint_equality_decidability : forall A B : MTpoint, A = B \/ ~ A = B
}.
