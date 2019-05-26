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
(*                                  Lci.v                                   *)
(****************************************************************************)

(* Proprie'te's des lois de composition interne *)

(*****************************************************************************)
Section Internal.

Variable S : Set.
Variable G : S -> Prop.
Variable Add : S -> S -> S.
Variable O I : S.
Variable Opp Inv : S -> S.
(*****************************************************************************)

(***************)
Definition intern := forall x y : S, G x -> G y -> G (Add x y).

(**********************)
Definition commutativity := forall x y : S, Add x y = Add y x.

(**********************)
Definition associativity :=
  forall x y z : S, Add x (Add y z) = Add (Add x y) z :>S.

(****************)
Definition neutral (S : Set) (G : S -> Prop) (Add : S -> S -> S) 
  (O : S) := G O /\ (forall x : S, G x -> Add x O = x /\ Add O x = x).

(****************)
Lemma neutral_add : neutral S G Add O -> O = Add O O.

Proof.
intros; symmetry  in |- *.
elim H; intros; elim (H1 O H0); trivial.
Qed.

(********************)
Definition is_opposite (x y : S) := G x /\ G y /\ Add x y = O /\ Add y x = O.

(************)
Lemma opp_com :
 commutativity ->
 forall x y : S, G x -> G y -> Add x y = O -> is_opposite x y.

Proof.
intros. unfold is_opposite in |- *. 
split. exact H0. split. exact H1. split. exact H2. elim (H x y). exact H2.
Qed.

(*****************)
Definition opposite := forall x : S, G x -> is_opposite x (Opp x).

(***********************)
Definition distributivity (S : Set) (Add Mult : S -> S -> S) :=
  forall x y z : S,
  Mult (Add x y) z = Add (Mult x z) (Mult y z) /\
  Mult x (Add y z) = Add (Mult x y) (Mult x z).

End Internal.
(*****************************************************************************)