(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** Object-level encoding of bounded universal quantification II *)

Require Import Arith Nat Omega List Bool Setoid.
Require Import utils_tac gcd prime binomial sums bool_nat luca.
Require Import cipher dio_logic dio_expo dio_binary.

Set Implicit Arguments.

Local Infix "≲" := binary_le (at level 70, no associativity).
Local Notation power := (mscal mult 1).
Local Notation "∑" := (msum plus 0).
Local Infix "⇣" := nat_meet (at level 40, left associativity).
Local Infix "⇡" := nat_join (at level 50, left associativity).

Theorem seqs_of_ones_diophantine l q u u1 : 𝔻P l -> 𝔻P q -> 𝔻P u -> 𝔻P u1
          -> 𝔻R (fun v => seqs_of_ones (l v) (q v) (u v) (u1 v)).
Proof.
  intros.
  apply dio_rel_equiv with (1 := fun v => seqs_of_ones_dio (l v) (q v) (u v) (u1 v)).
  dio_rel_auto.
Defined.

Hint Resolve seqs_of_ones_diophantine.

(* a is the q-cipher of some l-tuple *)

Theorem Code_diophantine l q a : 𝔻P l -> 𝔻P q -> 𝔻P a
                              -> 𝔻R (fun v => Code (l v) (q v) (a v)).
Proof.
  intros.
  apply dio_rel_equiv with (1 := fun v => Code_dio (l v) (q v) (a v)).
  dio_rel_auto.
Defined.

Hint Resolve Code_diophantine.

(* c is the q-cipher of the l-tuple <x,...,x> *)

Theorem Const_diophantine l q c x : 𝔻P l -> 𝔻P q -> 𝔻P c -> 𝔻P x
                                 -> 𝔻R (fun v => Const (l v) (q v) (c v) (x v)).
Proof.
  intros.
  apply dio_rel_equiv with (1 := fun v => Const_dio (l v) (q v) (c v) (x v)).
  dio_rel_auto.
Defined.

Hint Resolve Const_diophantine.

(* a is the q-cipher of the l-tuple <0,...,l-1> *)

Theorem CodeNat_diophantine l q a : 𝔻P l -> 𝔻P q -> 𝔻P a -> 𝔻R (fun v => CodeNat (l v) (q v) (a v)).
Proof.
  intros.
  apply dio_rel_equiv with (1 := fun v => CodeNat_dio (l v) (q v) (a v)).
  dio_rel_auto.
Defined.

Hint Resolve CodeNat_diophantine.

(* Testing whether a is the q cipher of the sum of the tuples of q-ciphers b and c *)

Theorem Code_plus_diophantine a b c : 𝔻P a -> 𝔻P b -> 𝔻P c
                                   -> 𝔻R (fun v => Code_plus (a v) (b v) (c v)).
Proof. intros; unfold Code_plus; dio_rel_auto. Defined.

(* Testing whether a is the q cipher of the product of the tuples of q-ciphers b and c *)

Theorem Code_mult_diophantine l q a b c : 𝔻P l -> 𝔻P q -> 𝔻P a -> 𝔻P b -> 𝔻P c
                                       -> 𝔻R (fun v => Code_mult (l v) (q v) (a v) (b v) (c v)).
Proof. intros; unfold Code_mult; dio_rel_auto. Defined.

Hint Resolve Code_plus_diophantine Code_mult_diophantine.

(** Now we have diophantine representations of q-cipher of the following l-tuple

    1) <x,...,x>  (for x < 2^q)
    2) <0,...,l-1> 
    3) testing whether some code is a q-cipher of some tuple
    4) testing sum and product equality among q-ciphers 

*)
