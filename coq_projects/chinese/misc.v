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
(*                                  misc.v                                  *)
(****************************************************************************)
Require Export Lci.

(****************)
Definition antisym (A : Set) (R : A -> A -> Prop) :=
  forall x y : A, R x y -> R y x -> x = y :>A.

(********************)
Definition pi1 : forall (A : Set) (P : A -> Prop), {x : A | P x} -> A.

Proof.
simple induction 1; auto.
Defined.

(********************)
Lemma pi2 :
 forall (A : Set) (P : A -> Prop) (p : {x : A | P x}), P (pi1 A P p).

Proof.
simple induction p; unfold pi1 in |- *; trivial.
Qed.

(*******************)
Definition inversible (S : Set) (Mult : S -> S -> S) 
  (I x : S) := exists y : S, Mult x y = I /\ Mult y x = I.

(************)
Lemma inv_com :
 forall (S : Set) (Mult : S -> S -> S) (I x : S),
 commutativity S Mult ->
 (exists y : S, Mult x y = I) -> inversible S Mult I x.

Proof.
intros; unfold inversible in |- *.
elim H0; intros.
exists x0.
split. 
assumption.
elim (H x x0); assumption.
Qed.  