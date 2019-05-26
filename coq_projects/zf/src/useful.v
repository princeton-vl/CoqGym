(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(***************************************************************************)
(* File: useful.v                                                          *)
(* auteur: alex@sysal.ibp.fr                                               *)
(* date: 19/10/95                                                          *)
(***************************************************************************)
Require Import nothing.

(***************************************************************************)
(* Many useful lemmas                                                      *)
(***************************************************************************)

(***************************************************************************)
(* Distributivity and factorisation of /\ and \/                           *)
(***************************************************************************)
Lemma lem_and_fact :
 forall P0 P1 P2 : Prop, (P0 \/ P1) /\ P2 -> P0 /\ P2 \/ P1 /\ P2.
(* Proof of lem_and_fact                                                   *)
intros; tauto.
Qed.
(* End of proof of lem_and_fact                                            *)

Lemma lem_and_dist :
 forall P0 P1 P2 : Prop, P0 /\ P2 \/ P1 /\ P2 -> (P0 \/ P1) /\ P2.
(* Proof of lem_and_dist                                                   *)
intros; tauto.

Qed.
(* End of proof of lem_and_dist                                            *)

Lemma lem_or_fact :
 forall P0 P1 P2 : Prop, P0 /\ P1 \/ P2 -> (P0 \/ P2) /\ (P1 \/ P2).
(* Proof of lem_or_fact                                                    *)
intros; tauto.

Qed.
(* End of proof of lem_or_fact                                             *)

Lemma lem_or_dist :
 forall P0 P1 P2 : Prop, (P0 \/ P2) /\ (P1 \/ P2) -> P0 /\ P1 \/ P2.
(* Proof of lem_or_dist                                                    *)
intros; tauto.

Qed.
(* End of proof of lem_or_dist                                             *)

(***************************************************************************)
(* Rewriting                                                               *)
(***************************************************************************)
Lemma lem_or_and_conv_l :
 forall a b c d : Prop,
 a /\ b \/ c /\ d -> (a \/ c) /\ (b \/ c) /\ (a \/ d) /\ (b \/ d).
(* Proof                                                                   *)
intros; tauto.
Qed.
(* End of proof                                                            *)

Lemma lem_or_and_conv_r :
 forall a b c d : Prop,
 (a \/ c) /\ (b \/ c) /\ (a \/ d) /\ (b \/ d) -> a /\ b \/ c /\ d.
(* Proof                                                                   *)
intros; tauto.
Qed.
(* End of proof                                                            *)

Lemma lem_and_rew_r :
 forall P Q1 Q2 : Prop, (Q1 <-> Q2) -> (P /\ Q1 <-> P /\ Q2).
(* Proof                                                                   *)
intros; tauto.
Qed.
(* End of proof                                                            *)

Lemma lem_and_rew_l :
 forall P Q1 Q2 : Prop, (Q1 <-> Q2) -> (Q1 /\ P <-> Q2 /\ P).
(* Proof                                                                   *)
intros; tauto.
Qed.
(* End of proof                                                            *)

Lemma lem_and_assoc_l : forall a b c : Prop, (a /\ b) /\ c <-> a /\ b /\ c.
(* Proof                                                                   *)
intros; tauto.
Qed.
(* End of proof                                                            *)

(* Note : le /\ est associatif a droite en CoQ don pas de lemme symmetrique*)

Lemma lem_or_rew_l :
 forall P Q1 Q2 : Prop, (Q1 <-> Q2) -> (Q1 \/ P <-> Q2 \/ P).
(* Proof                                                                   *)
intros; tauto.
Qed.
(* End of proof                                                            *)

Lemma lem_or_rew_r :
 forall P Q1 Q2 : Prop, (Q1 <-> Q2) -> (P \/ Q1 <-> P \/ Q2).
(* Proof                                                                   *)
intros; tauto.
Qed.
(* End of proof                                                            *)

Lemma lem_or_assoc_l : forall a b c : Prop, (a \/ b) \/ c <-> a \/ b \/ c.
(* Proof                                                                   *)
intros; tauto.
Qed.
(* End of proof                                                            *)

(* Note : le \/ est associatif a droite en CoQ don pas de lemme symmetrique*)

Lemma lem_and_rew_lr :
 forall al bl ar br : Prop,
 (al <-> ar) -> (bl <-> br) -> (al /\ bl <-> ar /\ br).
(* Proof                                                                   *)
intros; tauto.
Qed.
(* End of proof                                                            *)

Lemma lem_or_rew_lr :
 forall al bl ar br : Prop,
 (al <-> ar) -> (bl <-> br) -> (al \/ bl <-> ar \/ br).
(* Proof                                                                   *)
intros; tauto.
Qed.
(* End of proof                                                            *)

(***************************************************************************)
(* Symmetry properties                                                     *)
(***************************************************************************)
Lemma lem_iff_sym : forall a b : Prop, (a <-> b) -> (b <-> a).
(* Proof of lem_iff_sym                                                    *)
intros; tauto.
Qed.
(* End of proof of lem_iff_sym                                             *)

Lemma lem_or_sym : forall a b : Prop, a \/ b -> b \/ a.
(* Proof of lem_or_sym                                                     *)
intros.
elim H; clear H; intros.
right; assumption.

left; assumption.

Qed.
(* End of proof of lem_or_sym                                              *)

Lemma lem_and_sym : forall a b : Prop, a /\ b -> b /\ a.
(* Proof of lem_and_sym                                                    *)
intros; tauto.

Qed.
(* End of proof of lem_and_sym                                             *)

(***************************************************************************)
(* Contraction and expansion                                               *)
(***************************************************************************)
Lemma lem_or_expand : forall a : Prop, a -> a \/ a.
(* Proof of lem_or_expand                                                  *)
intros; tauto.

Qed.
(* End of proof of lem_or_expand                                           *)

Lemma lem_and_expand : forall a : Prop, a -> a /\ a.
(* Proof of lem_and_expand                                                 *)
intros; tauto.

Qed.
(* End of proof of lem_and_expand                                          *)

Lemma lem_or_contract : forall a : Prop, a \/ a -> a.
(* Proof of lem_or_contract                                                *)
intros; tauto.

Qed.
(* End of proof of lem_or_contract                                         *)

Lemma lem_and_contract : forall a : Prop, a /\ a -> a.
(* Proof of lem_and_contract                                               *)
intros; tauto.

Qed.
(* End of proof of lem_and_contract                                        *)

(***************************************************************************)
(* Existenciel et unicite                                                  *)
(***************************************************************************)
Definition exUniq (A : Set) (P : A -> Prop) :=
  exists x : A, P x /\ (forall y : A, P y -> x = y).

Notation ExU := (exUniq _) (only parsing).

(***************************************************************************)
(*                     Next : any file you want                            *)
(***************************************************************************)