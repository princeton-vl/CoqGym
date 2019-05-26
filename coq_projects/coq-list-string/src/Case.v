Require Import Coq.Lists.List.
Require Char.
Require Import LString.

Import ListNotations.
Import LString.

(** Convert the first character to uppercase. *)
Definition capitalize (s : t) : t :=
  match s with
  | [] => []
  | c :: s => Char.up_case c :: s
  end.

(** Replace uppercase letters by lowercase ones (only characters from a to z are affected). *)
Definition down_case (s : t) : t :=
  List.map Char.down_case s.

(** Replace lowercase letters by uppercase ones (only characters from a to z are affected). *)
Definition up_case (s : t) : t :=
  List.map Char.up_case s.