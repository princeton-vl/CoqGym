(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require  Import area_method.

(** The Pappus line theorem *)

Theorem Pappus : forall A B C A' B' C' P Q R :Point,
  on_line C A B ->
  on_line C' A' B' ->
  inter_ll P A' B A B' ->
  inter_ll Q A C' A' C ->
  inter_ll R B' C B C' ->
  Col P Q R.
Proof.
area_method.
Qed.

(** This version uses an extra point *)

Theorem Pappus_2 : forall A B C A' B' C' P Q R T:Point,
  on_line C A B ->
  on_line C' A' B' ->
  inter_ll P A' B A B' ->
  inter_ll Q A C' A' C ->
  inter_ll R B' C B C' ->
  inter_ll T B' C P Q ->
  C<>R -> C<>T ->
  parallel B' R C R ->
  parallel B' T C T ->
  B'**R / C**R = B'**T / C**T.
Proof.
area_method.
Qed.
