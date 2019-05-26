Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.

(** A string is a list of characters. *)
Definition t : Set := list Ascii.ascii.