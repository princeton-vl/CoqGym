(** * Exception handling *)

(* begin hide *)
From Coq.extraction Require
     Extraction.

From SimpleIO Require Import
     IO_Monad.
(* end hide *)

(** Catch [End_of_file] exceptions. *)
Parameter catch_eof : forall {a : Type}, IO a -> IO (option a).
Extract Constant catch_eof =>
  "(fun io k ->
     k (try Obj.magic io (fun a -> Some a) with
        | End_of_file -> None))".

(** Catch [Invalid_argument _] exceptions. *)
Parameter catch_invalid_arg : forall {a : Type}, IO a -> IO (option a).
Extract Constant catch_invalid_arg =>
  "(fun io k ->
     k (try Obj.magic io (fun a -> Some a) with
        | Invalid_argument _ -> None))".

(** Catch [Failure _] exceptions. *)
Parameter catch_failure : forall {a : Type}, IO a -> IO (option a).
Extract Constant catch_failure =>
  "(fun io k ->
     k (try Obj.magic io (fun a -> Some a) with
        | Failure _ -> None))".

(** Catch [Not_found] exceptions. *)
Parameter catch_not_found : forall {a : Type}, IO a -> IO (option a).
Extract Constant catch_not_found =>
  "(fun io k ->
     k (try Obj.magic io (fun a -> Some a) with
        | Not_found -> None)".
