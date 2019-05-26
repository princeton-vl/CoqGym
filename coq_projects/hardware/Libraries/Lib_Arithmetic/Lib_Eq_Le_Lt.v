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
(*                             Lib_Eq_Le_Lt.v                               *)
(****************************************************************************)


Require Export Arith.
Require Export Compare.


Lemma not_S_eq : forall n m : nat, S n <> S m -> n <> m.
red in |- *; intros.
apply H; auto with arith.
Qed.
Hint Resolve not_S_eq.


Lemma neq_O_le : forall n : nat, n <> 0 -> 1 <= n.
simple induction n; auto with arith.
Qed.
Hint Resolve neq_O_le.


Lemma lt_O : forall m n : nat, m < n -> 0 < n.
intros m n H.
apply le_lt_trans with m; auto with arith.
Qed.
Hint Immediate lt_O.


Lemma lt_Ex_n : forall n : nat, 0 < n -> exists n0 : nat, n = S n0.
intros.
elim H.
exists 0; try trivial with arith.
intros; exists m; try trivial with arith.
Qed.
Hint Resolve lt_Ex_n.


Lemma lt_m_neq : forall m n : nat, m < n -> n <> m.
simple induction m.
simple induction n; auto with arith.
clear m; intros m H_rec n H.
cut (exists p : nat, n = S p).
intros G; elim G; clear G.
intros p e.
rewrite e.
apply not_eq_S.
apply H_rec.
apply lt_S_n.
elim e; try trivial with arith.
apply lt_Ex_n.
apply lt_O with (S m); try trivial with arith.
Qed.

Hint Resolve lt_m_neq.
(************************************************************************)
