(** Unsafe but convenient primitives.
 *)

From Coq.extraction Require Import
     ExtrOcamlIntConv.

From SimpleIO Require Import
     IO_Pervasives.

(* Throws an exception if the divisor is 0. *)
Parameter unsafe_int_div : int -> int -> int.
Extract Inlined Constant unsafe_int_div => "Pervasives.(/)".

(* Throws an exception if the divisor is 0. *)
Parameter unsafe_int_mod : int -> int -> int.
Extract Inlined Constant unsafe_int_mod => "Pervasives.(mod)".

(* Throws an exception if the argument is smaller than 0 or
   greater than 255. *)
Parameter unsafe_char_of_int : int -> char.
Extract Constant unsafe_char_of_int => "Pervasives.char_of_int".

(* Throws an exception if the argument string does not represent
   an integer. *)
Parameter unsafe_int_of_ostring : ocaml_string -> int.
Extract Inlined Constant unsafe_int_of_ostring => "Pervasives.int_of_string".

(* N.B.: I am not sure whether these are actually unsafe.
   It depends on what "undefined" means here. It might be fine if
   the result is architecture dependent but still constant. They
   would be really unsafe if the result could change from one
   operation to the next. *)

(* Logical shift left (treats [int] as unsigned).
   Undefined result if shift is negative or greater than [int] size. *)
Parameter unsafe_lsl : int -> int -> int.

(* Logical shift right (treats [int] as unsigned).
   Undefined result if shift is negative or greater than [int] size. *)
Parameter unsafe_lsr : int -> int -> int.

(* Arithmetic shift right (replicates the bit sign).
   Undefined result if shift is negative or greater than [int] size. *)
Parameter unsafe_asr : int -> int -> int.

Extract Inlined Constant unsafe_lsl => "Pervasives.(lsl)".
Extract Inlined Constant unsafe_lsr => "Pervasives.(lsr)".
Extract Inlined Constant unsafe_asr => "Pervasives.(asr)".
