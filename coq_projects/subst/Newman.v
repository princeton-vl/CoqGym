(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              Nov 25th 1994                               *)
(*                                                                          *)
(****************************************************************************)
(*                                 Newman.v                                 *)
(****************************************************************************)

(*****************************************************************************)
(*          Projet Coq  - Calculus of Inductive Constructions V5.8           *)
(*****************************************************************************)
(*                                                                           *)
(*      Meta-theory of the explicit substitution calculus lambda-env         *)
(*      Amokrane Saibi                                                       *)
(*                                                                           *)
(*      September 1993                                                       *)
(*                                                                           *)
(*****************************************************************************)


                               (* Theoreme de Newman *)

Require Import sur_les_relations.

Section NewmanS.
 Variable A : Set.
 Variable R : A -> A -> Prop.
 Hypothesis N : explicit_noetherian _ R.
 Hypothesis C : explicit_local_confluence _ R.

   Theorem Newman : explicit_confluence _ R.
   unfold explicit_confluence in |- *; intro x; pattern x in |- *;
    apply (noetherian_induction1 A R N).
   intros y H1; unfold confluence_en in |- *.
   intros y0 z H2 H3; elim (star_case A R y z H3); intro H4.
   exists y0; split.
   apply star_refl.
   rewrite <- H4; assumption.
   elim (star_case A R y y0 H2); intro H5.
   exists z; split.
   rewrite <- H5; assumption.
   apply star_refl.
   elim H5; intros y0' H6; elim H6; intros H7 H8.
   elim H4; intros z' H9; elim H9; intros H10 H11.
   elim (C y y0' z' H7 H10); intros y' H12.
   elim H12; intros H13 H14.
   elim (H1 y0' H7 y0 y' H8 H13); intros y'' H15.
   elim H15; intros H16 H17.
   elim (H1 z' H10 y'' z (star_trans A R z' y' y'' H14 H17) H11).
   intros u H18; elim H18; intros H19 H20.
   exists u; split.
   apply star_trans with y''; assumption.
   assumption.
   Qed.
End NewmanS.


