(** The [String] module from OCaml's standard library.

    Operations are meant to be used qualified, e.g., [OString.length].

    The inner module is named [OString] to avoid the conflict with
    with [Coq.Strings.String].
 *)

(* begin hide *)
From Coq Require Import
     Strings.String
     Strings.Ascii
     extraction.ExtrOcamlIntConv.

From SimpleIO Require Import
     IO_Pervasives.

Extraction Blacklist Bytes Pervasives String .
(* end hide *)

Module OString.

(** Length of an [ocaml_string]. *)
Parameter length : ocaml_string -> int.
Extract Inlined Constant length => "String.length".

(** Index into an [ocaml_string].

    Equals [None] if out of bounds. *)
Parameter get_opt : ocaml_string -> int -> option char.
Extract Constant get_opt =>
  "fun s i -> try Some (String.get s i)
              with Invalid_argument _ -> None".

(** Concatenates strings with a separator. *)
Parameter concat : ocaml_string -> list ocaml_string -> ocaml_string.
Extract Inlined Constant concat => "String.concat".

(** ** Unsafe functions *)

Module Unsafe.

(** Index into an [ocaml_string], without an [option] wrapper.

    Throws an exception if out of bounds. *)
Parameter get : ocaml_string -> int -> char.
Extract Inlined Constant get => "String.get".

(** Create a string of repeated characters.

    Throws an exception if [n < 0] or [n > Sys.max_string_length]. *)
Parameter make : int -> char -> ocaml_string.
Extract Inlined Constant make => "String.make".

(** Create a string with a function from indices to characters.

    Throws an exception if [n < 0] or [n > Sys.max_string_length]. *)
Parameter init : int -> (int -> char) -> ocaml_string.
Extract Inlined Constant init => "String.init".

(** [sub i len s] is the substring of [s] with length [len]
    starting at index [i].

    Throws an exception if out of bounds. *)
Parameter sub : ocaml_string -> int -> int -> ocaml_string.
Extract Inlined Constant sub => "String.sub".

End Unsafe.

(** * Extras *)

(** Conversion between [ocaml_string] and [list char]. *)
Parameter to_list : ocaml_string -> list char.
Parameter of_list : list char -> ocaml_string.

Axiom from_to_list :
  forall s, to_list (of_list s) = s.
Axiom to_from_list :
  forall s, of_list (to_list s) = s.

(** ** Extraction *)

Extract Constant to_list =>
  "fun s ->
    let rec go n z =
      if n = -1 then z
      else go (n-1) (String.get s n :: z)
    in go (String.length s - 1) []".

Extract Constant of_list =>
  "fun z -> Bytes.unsafe_to_string (
    let b = Bytes.create (List.length z) in
    let rec go z i =
      match z with
      | c :: z -> Bytes.set b i c; go z (i+1)
      | [] -> b
    in go z 0)".

End OString.
