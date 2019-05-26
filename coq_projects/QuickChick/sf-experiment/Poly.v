(** * Poly: Polymorphism and Higher-Order Functions *)

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".
Require Import List ZArith.
Import ListNotations.
Set Warnings "-notation-overridden,-parsing".
(* Require Export Lists. *)

(*
Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.
Derive Arbitrary for list.
Derive Show for list.
Instance list_eq (X : Type) (H : forall (a b : X), Dec (a = b)) (x y : list X) : Dec (x = y).
constructor. unfold ssrbool.decidable. repeat (decide equality). apply H. Defined.
*)

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil 
  | S count' => cons x (repeat X x count')
  end.

(** As with [nil] and [cons], we can use [repeat] by applying it
    first to a type and then to its list argument: *)

QuickChick (
  (repeat nat 4 2 = cons 4 (cons 4 (nil)))? ).

Arguments repeat {X} x count.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(** **** Exercise: 2 stars, recommended (split)  *)
(** The function [split] is the right inverse of [combine]: it takes a
    list of pairs and returns a pair of lists.  In many functional
    languages, it is called [unzip].

    Fill in the definition of [split] below.  Make sure it passes the
    given unit test. *)

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) := ([],[]).

Definition split_combineP l1 l2 :=
  (split (combine l1 l2) = (l1,l2))?.

QuickChick (expectFailure split_combineP).

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

(** **** Exercise: 3 stars (partition)  *)
(** Use [filter] to write a Coq function [partition]:

      partition : forall X : Type,
                  (X -> bool) -> list X -> list X * list X

   Given a set [X], a test function of type [X -> bool] and a [list
   X], [partition] should return a pair of lists.  The first member of
   the pair is the sublist of the original list containing the
   elements that satisfy the test, and the second is the sublist
   containing those that fail the test.  The order of elements in the
   two sublists should be the same as their order in the original
   list. *)

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *) := ([],[]).

(*
QuickCheck (fun {X:Type} (l: list X) => checker false).
==> Error: Conversion test raised an anomaly *)

From QuickChick Require Import CoArbitrary.

Require Import String.
Open Scope string.

Instance show_natfun : Show (nat -> bool) :=
  {|
    show f := "{"
               ++ "0 |-> " ++ (show (f 0) )
               ++ ", 1 |-> " ++ (show (f 1) )
               ++ ", 2 |-> " ++ (show (f 2) )
               ++ ", 3 |-> " ++ (show (f 3) )
               ++ ", 4 |-> " ++ (show (f 4))
               ++ "}"
  |}.

QuickCheck (fun (test: nat -> bool) (l: list nat) => checker false).



Fixpoint map {X Y:Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
    map f (rev l) = rev (map f l).
Admitted.
(* LEO: Uh oh -- same issue *)

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X)
                   : (list Y)
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *) := [].


Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.


Fixpoint fold {X Y:Type} (f: X->Y->Y) (l:list X) (b:Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.


Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Definition fold_length_correctP := fun X (l : list X) =>
  (fold_length l = length (l++l))?.
(*! QuickCheck fold_length_correctP. *)

Definition fold_length_correctP_bad := fun X (l : list X) =>
  (fold_length l = length (l++l))?.
QuickCheck (expectFailure fold_length_correctP).


Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** Write down a theorem [fold_map_correct] in Coq stating that
   [fold_map] is correct, and prove it. *)
(* LEO: ... :-? *)


Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

(** As an exercise, define its inverse, [prod_uncurry].  Then prove
    the theorems below to show that the two are inverses. *)

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** As a (trivial) example of the usefulness of currying, we can use it
    to shorten one of the examples that we saw above: *)

(* LEO: Getting even more challenging... *)

Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)



(** **** Exercise: 4 stars, advanced (church_numerals)  *)
(** This exercise explores an alternative way of defining natural
    numbers, using the so-called _Church numerals_, named after
    mathematician Alonzo Church.  We can represent a natural number
    [n] as a function that takes a function [f] as a parameter and
    returns [f] iterated [n] times. *)

Module Church.
Definition nat := forall X : Type, (X -> X) -> X -> X.

(** Let's see how to write some numbers with this notation. Iterating
    a function once should be the same as just applying it.  Thus: *)

Definition one : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

(** Similarly, [two] should apply [f] twice to its argument: *)

Definition two : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

(** Defining [zero] is somewhat trickier: how can we "apply a function
    zero times"?  The answer is actually simple: just return the
    argument untouched. *)

Definition zero : nat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

(** More generally, a number [n] can be written as [fun X f x => f (f
    ... (f x) ...)], with [n] occurrences of [f].  Notice in
    particular how the [doit3times] function we've defined previously
    is actually just the Church representation of [3]. *)


(** Complete the definitions of the following functions. Make sure
    that the corresponding unit tests pass by proving them with
    [reflexivity]. *)

(** Successor of a natural number: *)

Definition succ (n : nat) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example succ_1 : succ zero = one.
Proof. (* FILL IN HERE *) Admitted.

Example succ_2 : succ one = two.
Proof. (* FILL IN HERE *) Admitted.


(** Addition of two natural numbers: *)

Definition plus (n m : nat) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example plus_1 : plus zero one = one.
Proof. (* FILL IN HERE *) Admitted.


(** Multiplication: *)

Definition mult (n m : nat) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example mult_1 : mult one one = one.
Proof. (* FILL IN HERE *) Admitted.


(** Exponentiation: *)

(** (_Hint_: Polymorphism plays a crucial role here.  However,
    choosing the right type to iterate over can be tricky.  If you hit
    a "Universe inconsistency" error, try iterating over a different
    type: [nat] itself is usually problematic.) *)

Definition exp (n m : nat) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example exp_1 : exp two two = plus two two.
Proof. (* FILL IN HERE *) Admitted.

End Church.


