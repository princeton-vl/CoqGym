(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*                   Solange Coupet-Grimal & Line Jakubiec                  *)
(*                                                                          *)
(*                                                                          *)
(*              Laboratoire d'Informatique de Marseille                     *)
(*               CMI-Technopole de Chateau-Gombert                          *)
(*                   39, Rue F. Joliot Curie                                *)
(*                   13453 MARSEILLE Cedex 13                               *)
(*           e-mail:{Solange.Coupet,Line.Jakubiec}@lim.univ-mrs.fr          *)
(*                                                                          *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              May 30th 1996                               *)
(*                                                                          *)
(****************************************************************************)
(*                              Lib_Dec.v                                *)
(****************************************************************************)

Require Export Arith.
Require Export Compare_dec.
Require Export Lib_Prop.


Lemma lt_or_eq_O_dec : forall n : nat, {0 < n} + {n = 0}.
simple induction n; auto with arith.
Qed.
Hint Resolve lt_or_eq_O_dec.


Lemma lt_SO_or_eq_O_or_SO_dec : forall n : nat, {1 < n} + {n = 0} + {n = 1}.
intros n; case n; auto with arith.
intros p; case p; auto with arith.
Qed.
Hint Resolve lt_SO_or_eq_O_or_SO_dec.


Lemma O_or_no_dec : forall n : nat, {n = 0} + {n <> 0}.
simple induction n; auto with arith.
Qed.
Hint Resolve O_or_no_dec.

Lemma eq_or_not : forall n m : nat, {n = m} + {n <> m}.
auto with arith.
Qed.



Lemma nat_order_dec : forall a b : nat, or3 (a < b) (a = b) (b < a).
simple induction a; simple induction b.
apply or3_Middle; auto with arith.
intros.
apply or3_Left; auto with arith.
apply or3_Right; auto with arith.
intros.
elim (H n0).
intro.
apply or3_Left.
apply lt_n_S; assumption.
intro.
apply or3_Middle.
apply eq_S; assumption.
intro.
apply or3_Right.
apply lt_n_S; assumption.
Qed.


(************************************************************************)
