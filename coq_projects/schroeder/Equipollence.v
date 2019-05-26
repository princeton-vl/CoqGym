(* Contribution to the Coq Library   V6.3 (July 1999)                       *)
(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.11                                 *)
(*                               Feb 2nd 1996                               *)
(*                                                                          *)
(*                (notations and layout updated March 2009)                 *)
(****************************************************************************)
(*                             Equipollence.v                               *)
(****************************************************************************)
(* This file is distributed under the terms of the                          *) 
(* GNU Lesser General Public License Version 2.1                            *)
(****************************************************************************)

Require Import Ensembles.    (* Ensemble, In, Included, Setminus *)
Require Import Relations_1.  (* Relation *)
Require Import Functions.

(****************************************************************************)
(**         Equipollence and relation "is of cardinal less than"            *)

Section Equipollence.

Variable U : Type.
Variable A B : Ensemble U.
Let Rela := Relation U.

Inductive equipollence : Prop :=
    equipollence_intro : forall f : Rela, bijection U A B f -> equipollence.

Inductive inf_card : Prop :=
    inf_card_intro : forall f : Rela, injection U A B f -> inf_card.

End Equipollence.

Notation "A <=_card B" := (inf_card _ A B) (at level 70).

Notation "A =_card B" := (equipollence _ A B) (at level 70).

(* $Id$ *)
