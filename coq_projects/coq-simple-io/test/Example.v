From Coq Require Import
     Strings.String
     extraction.ExtrOcamlIntConv.

From SimpleIO Require Import SimpleIO.
Import IO.Notations.

Open Scope string_scope.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
(* end hide *)

Parameter print_bool : bool -> IO unit.
Extract Constant print_bool =>
  "fun b k -> k (Pervasives.print_endline (Pervasives.string_of_bool b))".

Parameter int_constant : int.
Extract Constant int_constant => "3".

Definition f : IO unit := IO.while_loop (fun b =>
  match b with
  | true =>
      print_bool false;;
      print_endline "Hello";;
      IO.ret None
  | false =>
      print_bool true ;;
      print_int int_constant;;
      print_newline;;
      IO.ret (Some true)
  end) false.

Definition y : io_unit := IO.unsafe_run f.

Separate Extraction y.
