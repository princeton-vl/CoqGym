Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Char.
Require Import LString.

Import ListNotations.
Import LString.
Local Open Scope char.

(** Remove one end of line at the end, if present (can be \n, \r or \r\n). *)
Fixpoint chomp (s : t) : t :=
  match s with
  | [] => []
  | ["010"] | ["013"] | ["013"; "010"] => []
  | c :: s => c :: chomp s
  end.

(** Remove white spaces at the beginning of a string (spaces, \t, \n, \v, \f or \r). *)
Fixpoint trim_head (s : t) : t :=
  match s with
  | [] => []
  | c :: s' =>
    if Char.is_white_space c then
      trim_head s'
    else
      s
  end.

(** Remove white spaces at the end of a string (spaces, \t, \n, \v, \f or \r). *)
Fixpoint trim_tail (s : t) : t :=
  match s with
  | [] => []
  | c :: s =>
    match trim_tail s with
    | [] =>
      if Char.is_white_space c then
        []
      else
        [c]
    | s => c :: s
    end
  end.

(** Remove white spaces at the beginning and the end of a string
    (spaces, \t, \n, \v, \f or \r). *)
Definition trim (s : t) : t :=
  trim_head (trim_tail s).