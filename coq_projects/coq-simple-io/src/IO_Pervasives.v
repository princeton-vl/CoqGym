(**
  Extraction of Ocaml's [Pervasives] module.

  This depends on [ExtrOcamlBasic] and [ExtrOcamlIntConv] that define
  extraction for a few basic types ([option], [list], [int]).
  Other types that do not have a natural counterpart in Coq are left
  abstract.
  In particular, this module does not assume any particular
  representation of Coq's [string] and [ascii] (as opposed to the
  [RawChar] module).
*)

(* begin hide *)
From Coq.extraction Require Import
     Extraction
     ExtrOcamlBasic
     ExtrOcamlIntConv.

From SimpleIO Require Import
     IO_Monad.

Extraction Blacklist Pervasives.
(* end hide *)

(** * Types *)

(** The native [string] type in OCaml. *)
Parameter ocaml_string : Type.

(** Mutable bytestrings. *)
Parameter bytes : Type.

(** The native [char] type in OCaml (8 bit integers). *)
Parameter char : Type.

(** Input-output channels. *)
Parameter in_channel : Type.
Parameter out_channel : Type.

(** Mutable references. *)
Parameter ref : Type -> Type.

(** * Operations on [int] *)

Parameter int_add : int -> int -> int.
Parameter int_sub : int -> int -> int.
Parameter int_mul : int -> int -> int.
Parameter int_div_opt : int -> int -> option int.
Parameter int_mod_opt : int -> int -> option int.
Parameter int_eqb : int -> int -> bool.
Parameter int_neqb : int -> int -> bool.
Parameter int_le : int -> int -> bool.
Parameter int_lt : int -> int -> bool.
Parameter int_min : int -> int -> int.
Parameter int_max : int -> int -> int.

Parameter land : int -> int -> int.
Parameter lor : int -> int -> int.
Parameter lxor : int -> int -> int.
Parameter lnot : int -> int -> int.

Parameter max_int : int.
Parameter min_int : int.

Delimit Scope int_scope with int.
Bind Scope int_scope with int.
Infix "+" := int_add : int_scope.
Infix "-" := int_sub : int_scope.
Infix "*" := int_mul : int_scope.
Infix "<?" := int_lt (at level 70, no associativity) : int_scope.
Infix "<=?" := int_le (at level 70, no associativity) : int_scope.
Infix "=?" := int_eqb (at level 70, no associativity) : int_scope.
Infix "<>?" := int_neqb (at level 70, no associativity) : int_scope.

(** * Strings and char *)

(** Append strings. *)
Parameter ostring_app : ocaml_string -> ocaml_string -> ocaml_string.

(** Compare strings. *)
Parameter ostring_eqb : ocaml_string -> ocaml_string -> bool.

(** Compare characters. *)
Parameter char_eqb : char -> char -> bool.

(** Convert a [char] to an [int]. *)
Parameter int_of_char : char -> int.

(** Convert an [int] to a [char].

    Equals [None] if the argument is greater than 255. *)
Parameter char_of_int_opt : int -> option char.

(** Convert an [int] to a [char], in [IO].

    Throws an [Invalid_argument] exception if the argument is
    greater than 255. *)
Parameter char_of_int_io : int -> IO char.

(** Show an [int] as an [ocaml_string]. *)
Parameter ostring_of_int : int -> ocaml_string.

(** Parse an [ocaml_string] into an [int]. *)
Parameter int_of_ostring_opt : ocaml_string -> option int.

(** Notes:
   - There is no total [int_of_ostring].
     (See [IO_Unsafe.unsafe_int_of_ostring].)
   - Comparisons between mutable structures ([bytes], [ref]) should
     happen in IO.
 *)

(** * Exceptions *)

(** Throw an [Invalid_argument] exception. *)
Parameter invalid_arg : forall {a}, ocaml_string -> IO a.

(** Throw a [Failure] exception. *)
Parameter failwith : forall {a}, ocaml_string -> IO a.

(** * Standard channels *)

Parameter stdin : in_channel.
Parameter stdout : out_channel.
Parameter stderr : out_channel.

(** ** [stdout] *)

Parameter print_char : char -> IO unit.
Parameter print_bytes : bytes -> IO unit.
Parameter print_int : int -> IO unit.
Parameter print_string : ocaml_string -> IO unit.
Parameter print_endline : ocaml_string -> IO unit.
Parameter print_newline : IO unit.

(** ** [stderr] *)

Parameter prerr_char : char -> IO unit.
Parameter prerr_bytes : bytes -> IO unit.
Parameter prerr_int : int -> IO unit.
Parameter prerr_string : ocaml_string -> IO unit.
Parameter prerr_endline : ocaml_string -> IO unit.
Parameter prerr_newline : IO unit.

(** ** [stdin] *)

Parameter read_line : IO ocaml_string.
Parameter read_int : IO int.
Parameter read_int_opt : IO (option int).

(** * File handles *)

(** ** Output *)

(** Open a file for output. *)
Parameter open_out : ocaml_string -> IO out_channel.

(** Close an output file. *)
Parameter close_out : out_channel -> IO unit.

(** Flush output buffers. *)
Parameter flush : out_channel -> IO unit.
Parameter flush_all : IO unit.

Parameter output_char : out_channel -> char -> IO unit.
Parameter output_string : out_channel -> ocaml_string -> IO unit.
Parameter output_bytes : out_channel -> bytes -> IO unit.
Parameter output_substring : out_channel -> ocaml_string -> int -> int -> IO unit.
Parameter output_byte : out_channel -> int -> IO unit.

(** ** Input *)

(** Open a file for input. *)
Parameter open_in : ocaml_string -> IO in_channel.

(** Close an input file. *)
Parameter close_in : in_channel -> IO unit.

Parameter input_char : in_channel -> IO char.
Parameter input_line : in_channel -> IO ocaml_string.
Parameter input_byte : in_channel -> IO int.

(** * Mutable references *)

Parameter new_ref : forall {a}, a -> IO (ref a).
Parameter read_ref : forall {a}, ref a -> IO a.
Parameter write_ref : forall {a}, ref a -> a -> IO unit.
Parameter incr_ref : ref int -> IO unit.
Parameter decr_ref : ref int -> IO unit.

(** * Program termination *)

(** Terminate with an exit code. (0 for success.) *)
Parameter exit : forall {a}, int -> IO a.

(** * Extraction *)

(** ** Types *)

Extract Inlined Constant ocaml_string => "String.t".
Extract Inlined Constant char => "char".

Extract Inlined Constant bytes => "bytes".
Extract Inlined Constant in_channel => "Pervasives.in_channel".
Extract Inlined Constant out_channel => "Pervasives.out_channel".
Extract Constant ref "'a" => "'a Pervasives.ref".

(** ** Operations on [int] *)

Extract Inlined Constant int_add => "Pervasives.(+)".
Extract Inlined Constant int_sub => "Pervasives.(-)".
Extract Inlined Constant int_mul => "Pervasives.( * )".
Extract Inlined Constant int_div_opt =>
  "fun x y -> try Some (x Pervasives./ y)
              with Division_by_zero -> None".
Extract Inlined Constant int_mod_opt =>
  "fun x y -> try Some Pervasives.(x mod y)
              with Division_by_zero -> None".
Extract Inlined Constant int_eqb => "Pervasives.(=)".
Extract Inlined Constant int_neqb => "Pervasives.(<>)".
Extract Inlined Constant int_le => "Pervasives.(<=)".
Extract Inlined Constant int_lt => "Pervasives.(<)".

Extract Inlined Constant int_min => "Pervasives.min".
Extract Inlined Constant int_max => "Pervasives.max".

Extract Inlined Constant land => "Pervasives.(land)".
Extract Inlined Constant lor => "Pervasives.(lor)".
Extract Inlined Constant lxor => "Pervasives.(lxor)".
Extract Inlined Constant lnot => "Pervasives.lnot".

Extract Inlined Constant max_int => "Pervasives.max_int".
Extract Inlined Constant min_int => "Pervasives.min_int".

(** ** Misc *)

Extract Inlined Constant ostring_app => "Pervasives.(^)".

Extract Inlined Constant ostring_eqb => "Pervasives.(=)".
Extract Inlined Constant char_eqb => "Pervasives.(=)".

Extract Inlined Constant int_of_char => "Pervasives.int_of_char".

Extract Constant char_of_int_opt =>
  "fun n ->
     try Some (Pervasives.char_of_int n)
     with Invalid_argument _ -> None".

Extract Constant char_of_int_io => "fun n k -> k (Pervasives.char_of_int n)".

Extract Inlined Constant ostring_of_int => "Pervasives.string_of_int".
Extract Inlined Constant int_of_ostring_opt => "Pervasives.int_of_string_opt".

(** ** Exceptions *)

Extract Inlined Constant invalid_arg => "Pervasives.invalid_arg".
Extract Inlined Constant failwith => "Pervasives.failwith".

(** ** Standard channels *)

Extract Inlined Constant stdin  => "Pervasives.stdin".
Extract Inlined Constant stdout => "Pervasives.stdout".
Extract Inlined Constant stderr => "Pervasives.stderr".

(** *** [stdout] *)

Extract Constant print_char     => "fun c k -> k (Pervasives.print_char    c)".
Extract Constant print_bytes    => "fun b k -> k (Pervasives.print_bytes   b)".
Extract Constant print_int      => "fun n k -> k (Pervasives.print_int     n)".
Extract Constant print_string   => "fun s k -> k (Pervasives.print_string  s)".
Extract Constant print_endline  => "fun s k -> k (Pervasives.print_endline s)".
Extract Constant print_newline  => "fun   k -> k (Pervasives.print_newline ())".

(** *** [stderr] *)

Extract Constant prerr_char     => "fun c  k -> k (Pervasives.prerr_char    c)".
Extract Constant prerr_bytes    => "fun bs k -> k (Pervasives.prerr_bytes   bs)".
Extract Constant prerr_int      => "fun n  k -> k (Pervasives.prerr_int     n)".
Extract Constant prerr_string   => "fun s  k -> k (Pervasives.prerr_string  s)".
Extract Constant prerr_endline  => "fun s  k -> k (Pervasives.prerr_endline s)".
Extract Constant prerr_newline  => "fun    k -> k (Pervasives.prerr_newline ())".

(** *** [stdin] *)

Extract Constant read_line    => "fun k -> k (Pervasives.read_line ())".
Extract Constant read_int     => "fun k -> k (Pervasives.read_int  ())".
Extract Constant read_int_opt => "fun k -> k (Pervasives.read_int_opt ())".

(** ** File handles *)

(** *** Output *)

Extract Constant open_out  => "fun s k -> k (Pervasives.open_out s)".
Extract Constant flush     => "fun h k -> k (Pervasives.flush h)".
Extract Constant flush_all => "fun   k -> k (Pervasives.flush_all ())".

Extract Constant output_char    => "fun h c k -> k (Pervasives.output_char h c)".
Extract Constant output_string  => "fun h s k -> k (Pervasives.output_string h s)".
Extract Constant output_bytes   => "fun h b k -> k (Pervasives.output_bytes h b)".
Extract Constant output_byte    => "fun h b k -> k (Pervasives.output_byte h b)".
Extract Constant output_substring =>
  "fun h s i n k -> k (Pervasives.output_substring h s i n)".

Extract Constant close_out => "fun h k -> k (close_out h)".

(** *** Input *)

Extract Constant open_in     => "fun s k -> k (Pervasives.open_in s)".

Extract Constant input_char  => "fun h k -> k (Pervasives.input_char h)".
Extract Constant input_line  => "fun h k -> k (Pervasives.input_line h)".
Extract Constant input_byte  => "fun h k -> k (Pervasives.input_byte h)".

Extract Constant close_in => "fun h k -> k (Pervasives.close_in h)".

(** ** Mutable references *)

Extract Constant new_ref   =>
  "fun x k -> k (Pervasives.ref x)".
Extract Constant read_ref  =>
  "fun r k -> k (Pervasives.(!) r)".
Extract Constant write_ref =>
  "fun r x k -> k (Pervasives.(:=) r x)".
Extract Constant incr_ref  => "fun r k -> k (Pervasives.incr r)".
Extract Constant decr_ref  => "fun r k -> k (Pervasives.decr r)".

(** ** Program termination *)

Extract Constant exit => "fun n k -> k (Pervasives.exit n)".
