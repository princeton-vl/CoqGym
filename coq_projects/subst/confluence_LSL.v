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
(*                             confluence_LSL.v                             *)
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


                 (* Confluence du lambda-sigma-lift *)

Require Import TS.
Require Import sur_les_relations.
Require Import sigma_lift.
Require Import lambda_sigma_lift.
Require Import terminaison_SL.
Require Import conf_local_SL.
Require Import betapar.
Require Import SLstar_bpar_SLstar.
Require Import conf_strong_betapar.
Require Import commutation.
Require Import Newman.
Require Import Yokouchi.


Goal forall b : wsort, explicit_confluence _ (e_relSL b).
intros b.
apply Newman.
apply relSL_noetherian.
apply conf_local_SL.
Save confluence_SL.

Goal forall b : wsort, explicit_strong_confluence _ (e_slstar_bp_slstar b).
intro b; unfold e_slstar_bp_slstar in |- *.
change
  (explicit_strong_confluence _
     (Rstar_S_Rstar (TS b) (e_relSL b) (e_beta_par b))) 
 in |- *.
apply Yokouchi.
apply confluence_SL.
apply relSL_noetherian.
apply sconf_betapar.
intros f g h H H0.
unfold Rstar_S_Rstar in |- *.
change (exists k : TS b, e_relSLstar _ g k /\ e_slstar_bp_slstar _ h k)
 in |- *.
apply commutation with f; assumption.
Save strong_confluence_slbpsl.

Goal forall b : wsort, explicit_confluence _ (e_slstar_bp_slstar b).
intro b; apply strong_conf_conf; apply strong_confluence_slbpsl.
Save confluence_slbpsl.


(**********************************************)
(*        lambda-sigma-lift est confluent     *)
(**********************************************)

Theorem confluence_LSL : forall b : wsort, explicit_confluence _ (e_relLSL b).
Proof.
intro b; apply inclus_conf with (e_slstar_bp_slstar b).
apply relLSL_inclus_slbpsl.
change (explicit_inclus _ (e_slstar_bp_slstar b) (e_relLSLstar b)) in |- *.
apply slbpsl_inclus_relLSLstar.
apply confluence_slbpsl.
Qed.


