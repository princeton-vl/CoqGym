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
(*                              Z_succ_pred.v                               *)
(****************************************************************************)
Require Export Arith.
Require Export Zbase.

(* Succ and Pred on Z *)

(**************)
Definition succZ (x : Z) :=
  match x return Z with
  | OZ =>
      (* OZ *)  IZ 
      (* pos n *) 
  | pos n => pos (S n)
      (* neg n *) 
  | neg n =>
      match n return Z with
      | O =>
          (* O *)  OZ
          (* S m *) 
      | S m => neg m
      end
  end.

(**************)
Definition predZ (x : Z) :=
  match x return Z with
  | OZ =>
      (* OZ *)  neg 0
      (* pos n *) 
  | pos n =>
      match n return Z with
      | O =>
          (* O *)  OZ
          (* S m *) 
      | S m => pos m
      end
      (* neg n *) 
  | neg n => neg (S n)
  end.
    
(***************)
Lemma pred_succZ : forall x : Z, predZ (succZ x) = x.

Proof.
intros; pattern x in |- *; elim x.
(* OZ *)
simpl in |- *; reflexivity.
(* pos n *)
simpl in |- *; reflexivity.
(* neg n *)
intros; elim n.
simpl in |- *; reflexivity.
intros; simpl in |- *; reflexivity.
Qed.

(***************)
Lemma succ_predZ : forall x : Z, succZ (predZ x) = x.

Proof.
intros; pattern x in |- *; elim x.
(* OZ *)
simpl in |- *; reflexivity.
(* pos n *)
intros; elim n.
simpl in |- *; reflexivity.
intros; simpl in |- *; reflexivity.
(* neg n *)
simpl in |- *; reflexivity.
Qed.

(*************************)
Lemma succ_pred_pred_succZ : forall x : Z, succZ (predZ x) = predZ (succZ x).

Proof.
intros; rewrite (pred_succZ x); exact (succ_predZ x).
Qed.

(******************)
Lemma tech_pred_posZ : forall n : nat, 0 < n -> predZ (pos n) = pos (pred n).

Proof.
intro; elim n; intro. elim (lt_n_O 0); exact H. intros; simpl in |- *; reflexivity.
Qed.

(********************)
Lemma tech_succ_posOZ : forall n : nat, succZ (posOZ n) = pos n.

Proof.
intros; elim n; simpl in |- *; reflexivity; simpl in |- *; reflexivity.
Qed.