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
(*                                   TS.v                                   *)
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


              (* Termes et Substitutions *)


Inductive wsort : Set :=
  | ws : wsort
  | wt : wsort.

Inductive TS : wsort -> Set :=
  | var : nat -> TS wt
  | app : TS wt -> TS wt -> TS wt
  | lambda : TS wt -> TS wt
  | env : TS wt -> TS ws -> TS wt
  | id : TS ws
  | shift : TS ws
  | cons : TS wt -> TS ws -> TS ws
  | comp : TS ws -> TS ws -> TS ws
  | lift : TS ws -> TS ws
  | meta_X : nat -> TS wt
  | meta_x : nat -> TS ws.

Definition terms := TS wt.

Definition sub_explicits := TS ws.
 
(* Principe d induction pour les terms *)
 
Goal (terms -> Prop) -> forall b : wsort, TS b -> Prop.
intros P b; elim b.
exact (fun x : TS ws => True).
exact P.
Defined Pterms.

Lemma terms_ind :
 forall P : terms -> Prop,
 (forall n : nat, P (var n)) ->
 (forall a b : terms, P a -> P b -> P (app a b)) ->
 (forall a : terms, P a -> P (lambda a)) ->
 (forall a : terms, P a -> forall s : sub_explicits, P (env a s)) ->
 (forall n : nat, P (meta_X n)) -> forall a : terms, P a.
intros; change (Pterms P wt a) in |- *; elim a; simpl in |- *; auto.
Qed.

(* Principe d induction pour les sub_explicits *)

Goal (sub_explicits -> Prop) -> forall b : wsort, TS b -> Prop.
intros P b; elim b.
exact P.
exact (fun x : TS wt => True).
Defined Psubst.

Lemma sub_explicits_ind :
 forall P : sub_explicits -> Prop,
 P id ->
 P shift ->
 (forall s : sub_explicits, P s -> forall a : terms, P (cons a s)) ->
 (forall s t : sub_explicits, P s -> P t -> P (comp s t)) ->
 (forall s : sub_explicits, P s -> P (lift s)) ->
 (forall n : nat, P (meta_x n)) -> forall s : sub_explicits, P s.
intros; change (Psubst P ws s) in |- *; elim s; simpl in |- *; auto.
Qed.



