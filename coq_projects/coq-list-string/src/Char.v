Require Import Coq.NArith.NArith.
Require Import Coq.Strings.Ascii.
Require Bool.

Local Open Scope char.
Local Open Scope N.

(** Total order on characters. *)
Definition compare (x y : Ascii.ascii) : comparison :=
  N.compare (Ascii.N_of_ascii x) (Ascii.N_of_ascii y).

Lemma compare_implies_eq : forall (x y : Ascii.ascii),
  compare x y = Eq -> x = y.
  unfold compare; intros x y H.
  rewrite <- ascii_N_embedding with (a := x);
    rewrite <- ascii_N_embedding with (a := y).
  f_equal.
  now apply N.compare_eq_iff.
Qed.

Lemma compare_same_is_eq : forall (x : Ascii.ascii), compare x x = Eq.
  intro x; unfold compare.
  now apply N.compare_eq_iff.
Qed.

(** Test if two characters are equal. *)
Definition eqb (x y : Ascii.ascii) : bool :=
  match compare x y with
  | Eq => true
  | _ => false
  end.

(** The character of a digit (0, 1, ..., 9, A, B, ...). *)
Definition of_N (n : N) : Ascii.ascii :=
  if N.leb n 9 then
    Ascii.ascii_of_N (Ascii.N_of_ascii "0" + n)
  else
    Ascii.ascii_of_N (Ascii.N_of_ascii "A" + n - 10).

(** The digit of a character (for 0, 1, ..., 9, A, B, ...). *)
Definition to_N (c : Ascii.ascii) : option N :=
  let n := Ascii.N_of_ascii c in
  if andb (N.leb (Ascii.N_of_ascii "0") n) (N.leb n (Ascii.N_of_ascii "9")) then
    Some (n - Ascii.N_of_ascii "0")
  else if N.leb (Ascii.N_of_ascii "A") n then
    Some (n - Ascii.N_of_ascii "A" + 10)
  else
    None.

(** Test if the character is in the ASCII range. *)
Definition is_ascii (c : Ascii.ascii) : bool :=
  match c with
  | Ascii.Ascii _ _ _ _ _ _ _ false => true
  | _ => false
  end.

(** Test if the character is a white space (space, \t, \n, \v, \f or \r). *)
Definition is_white_space (c : Ascii.ascii) : bool :=
  match c with
  | "009" | "010" | "011" | "012" | "013" | " " => true
  | _ => false
  end.

(** Replace uppercase letters by lowercase ones (only characters from a to z are affected). *)
Definition down_case (c : Ascii.ascii) : Ascii.ascii :=
  let n := Ascii.N_of_ascii c in
  let n_A := Ascii.N_of_ascii "A" in
  let n_Z := Ascii.N_of_ascii "Z" in
  let n_a := Ascii.N_of_ascii "a" in
  if andb (N.leb n_A n) (N.leb n n_Z) then
    Ascii.ascii_of_N ((n + n_a) - n_A)
  else
    c.

(** Replace lowercase letters by uppercase ones (only characters from a to z are affected). *)
Definition up_case (c : Ascii.ascii) : Ascii.ascii :=
  let n := Ascii.N_of_ascii c in
  let n_a := Ascii.N_of_ascii "a" in
  let n_z := Ascii.N_of_ascii "z" in
  let n_A := Ascii.N_of_ascii "A" in
  if andb (N.leb n_a n) (N.leb n n_z) then
    Ascii.ascii_of_N ((n + n_A) - n_a)
  else
    c.

(** * Special characters. *)
(** Bell. *)
Definition a : Ascii.ascii := "007".

(** Backspace. *)
Definition b : Ascii.ascii := "008".

(** Horizontal tabulation. *)
Definition t : Ascii.ascii := "009".

(** Line feed. *)
Definition n : Ascii.ascii := "010".

(** Vertical tabulation. *)
Definition v : Ascii.ascii := "011".

(** Form feed. *)
Definition f : Ascii.ascii := "012".

(** Carriage return. *)
Definition r : Ascii.ascii := "013".

(** Escape. *)
Definition e : Ascii.ascii := "027".