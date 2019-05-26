(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(*****************************************************************************)
(*                                                                           *)
(*          Buchberger : let construct                                       *)
(*                                                                           *)
(*          Laurent Thery March 98 (revised Mai 98)                          *)
(*                                                                           *)
(*****************************************************************************)

Definition LetP : forall (A B : Set) (h : A), (forall u : A, u = h -> B) -> B.
intros A B h H'.
apply H' with (u := h).
auto.
Defined.