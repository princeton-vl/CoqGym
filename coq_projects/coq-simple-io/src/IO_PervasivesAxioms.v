(** Theory for [IO_Pervasives] *)

(* begin hide *)
From SimpleIO Require Import IO_Pervasives.
(* end hide *)

Axiom char_of_int_of_char :
  forall c, char_of_int_opt (int_of_char c) = Some c.
