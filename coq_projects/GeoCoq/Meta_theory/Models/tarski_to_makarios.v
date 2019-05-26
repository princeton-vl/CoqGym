(*   Roland Coghetto, 17 March 2018
     GNU Lesser General Public License v3.0
     See LICENSE GeoCoq 2.3.0

     MODIFY, tarski_to_makarios,v Version GeoCoq 2.3.0
     MOTIVATION:
     in [1] Lemma 5: A' implies (RE)
     CHANGES: {(Point equality decidability),(TE),(IE),(SC),(FS')} |- (RE)
                                                                    i
     in [1] Lemma 6: if (RE) and (TE) holds, then (FS') is equivalent to (FS).
     CHANGES: a) {(RE), (TE),(FS)} |- (FS')
                                    i
              b) {(Point equality decidability), (TE), (IE) (SC), (FS')} |- (FS)
                                                                          i
     SOURCES:
       [1] Timothy James McKenzie Makarios. A further simplification of
             Tarski’s axioms of geometry. Note di Matematica, 33(2):123–132, 2013.
       [2] tarski_to_makarios,v GeoCoq 2.3.0
       [3] Mizar Mathematical Library (MML 5.46.1331):
             gtarski3.miz, Roland Coghetto and Adam Grabowski.
       [4] Tarski Geometry Axioms, part III.
             R. Coghetto & A. Grabowski.
             Formalized Mathematics Vol. 25 N° 4, 2017.(In preparation).

     in: Section Tarski83_to_Makarios_variant
         ------------------------------------
     REMOVE: cong_reflexivity, cong_symmetry, cong_left_commutativity.
     MODIFY: five_segment'.

     in: Section Makarios_variant_to_Tarski83
         ------------------------------------
     REMOVE: between_symmetry, Mcong_left_commutativity.
     ADD: LmCoghGrab, cong_pre_pseudo_reflexivity.
     MODIFY: cong_pseudo_reflexivity (Minner_pasch &
                  Mbetween_identity are not used to
                  prove cong_pseudo_reflexivity)
*)

Require Import GeoCoq.Axioms.tarski_axioms.
Require Import GeoCoq.Axioms.makarios_variant_axioms.

(** In this file we formalize the result given in T. J. M. Makarios:
 A further simplification of Tarski's axioms of geometry, June 2013. *)

Section Tarski83_to_Makarios_variant.

Context `{TnEQD:Tarski_neutral_dimensionless}.

Lemma five_segment' : forall A A' B B' C C' D D',
  Cong A B A' B' ->
  Cong B C B' C' ->
  Cong A D A' D' ->
  Cong B D B' D' ->
  Bet A B C -> Bet A' B' C' -> A <> B ->
  Cong D C C' D'.
Proof.
  intros.
  assert(Cong C D C' D').
  intros.
  eapply five_segment with A A' B B';assumption.
  assert(Cong C D D C).
  eapply cong_pseudo_reflexivity;eauto.
  apply cong_inner_transitivity with C D;assumption.
Qed.

Lemma lower_dim_ex :
  exists A B C, ~ (Bet A B C \/ Bet B C A \/ Bet C A B).
Proof.
exists PA.
exists PB.
exists PC.
apply lower_dim.
Qed.

Instance Makarios_Variant_follows_from_Tarski : Tarski_neutral_dimensionless_variant.
Proof.
exact (Build_Tarski_neutral_dimensionless_variant
 Tpoint Bet Cong
 cong_identity
 cong_inner_transitivity
 segment_construction
 five_segment'
 between_identity
 inner_pasch
 PA PB PC
 lower_dim).
Qed.

End Tarski83_to_Makarios_variant.