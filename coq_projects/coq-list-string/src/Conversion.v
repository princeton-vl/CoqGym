Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import ErrorHandlers.All.
Require Import ListPlus.All.
Require Char.
Require Import LString.

Import ListNotations.
Import LString.
Local Open Scope char.

(** Export to a standard string. *)
Fixpoint to_string (s : t) : String.string :=
  match s with
  | [] => String.EmptyString
  | c :: s => String.String c (to_string s)
  end.

(** Import a standard string. See the alias `s`. *)
Fixpoint of_string (s : String.string) : t :=
  match s with
  | String.EmptyString => []
  | String.String c s => c :: of_string s
  end.

(** Alias for `of_string`. *)
Definition s := of_string.

Fixpoint of_N_aux (base : N) (digits : nat) (padding : option Ascii.ascii)
  (n : N) : t :=
  match n with
  | 0%N =>
    match padding with
    | None => []
    | Some padding => List.repeat padding digits
    end
  | _ =>
    match digits with
    | O => []
    | S digits =>
      Char.of_N (N.modulo n base) ::
        of_N_aux base digits padding (N.div n base)
    end
  end.

(** Convert an integer to a string in base `base` with up to `digits` digits.
    Padding with the character `padding` if given, to make sure the result is of
    width `digits`. *)
Definition of_N (base : N) (digits : nat) (padding : option Ascii.ascii) (n : N)
  : t :=
  match n with
  | 0%N =>
    match digits with
    | O => []
    | S digits =>
      match padding with
      | None => ["0"]
      | Some padding => List.repeat padding digits ++ ["0"]
      end
    end
  | _ => List.rev' (of_N_aux base digits padding n)
  end.

(** Convert an integer to a string in base `base` with up to `digits` digits. *)
Definition of_Z (base : N) (digits : nat) (n : Z) : t :=
  (if Z.leb 0 n then s "" else s "-") ++
  of_N base digits None (Z.to_N (Z.abs n)).

Fixpoint to_N_aux (base : N) (s : t) : option N :=
  match s with
  | [] => Some 0%N
  | c :: s =>
    Option.bind (Char.to_N c) (fun d =>
    if andb (N.leb 0 d) (N.ltb d base) then
      Option.bind (to_N_aux base s) (fun n =>
      Some (d + base * n)%N)
    else
      None)
  end.

(** The integer represented by a string in base `base`. *)
Definition to_N (base : N) (s : t) : option N :=
  to_N_aux base (List.rev' s).
