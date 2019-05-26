(** * Basics: Functional Programming in Coq *)

From QuickChick Require Import QuickChick.
Import QcNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".
Require Import List ZArith.
Import ListNotations.
(* 
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import seq ssreflect ssrbool ssrnat eqtype.
*)

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

Definition test_next_weekday :=
  (next_weekday (next_weekday saturday)) = tuesday.

(* BCP: Needs an equality test. 
QuickCheck test_next_weekday. *)

(* BCP: QC needs the native one.  (Unless we make this Checkable somehow.)
Inductive bool : Type :=
  | true : bool
  | false : bool.
*)

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Definition nandb (b1:bool) (b2:bool) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *) := false.

Definition test_nandb1 := (nandb true false).
(*! QuickChick test_nandb1. *)

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool   :=   negb (evenb n).

Definition test_oddb1 :=    oddb 1.
(*! QuickChick test_oddb1. *)

Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Definition test_mult1 := (mult 3 3) =? 9.
(*! QuickChick test_mult1. *)

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O   , _    => O
  | S _ , O    => n
  | S n', S m' => minus n' m'
  end.

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

Fixpoint factorial (n:nat) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *) := 0.

Definition test_factorial1 :=          (factorial 3) =? 6.
(*! QuickChick test_factorial1. *)

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Check ((0 + 1) + 1).

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Notation "'FORALLX' x : T , c" :=
  (forAllShrink (@arbitrary T _) shrink (fun x => c))
  (at level 200, x ident, T at level 200, c at level 200, right associativity
   (* , format "'[' 'exists' '/ ' x .. y , '/ ' p ']'" *) )
  : type_scope.

Definition plus_O_n := FORALL n:nat, 0 + n =? n.
(*! QuickChick plus_O_n. *)
 
(* BCP: This should be automatable, we guessed... *)
Instance bool_eq (x y : bool) : Dec (x = y).
constructor. unfold ssrbool.decidable. repeat (decide equality). Defined.

(* BCP: Should be able to use Dec everywhere now  :-)  *)
Definition negb_involutive (b: bool) :=
  (negb (negb b) = b)?.
Check negb_involutive.
QuickChick negb_involutive.

Definition negb_involutive2 (b: bool) :=
  Bool.eqb (negb (negb b)) b.
(*! QuickChick negb_involutive2. *)

Definition andb_commutative := fun b c => Bool.eqb (andb b c) (andb c b).
(*! QuickCheck andb_commutative. *)

(* BCP: Don't know what to do with this one! 
Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
*)

Definition andb_eq_orb :=
  fun (b c : bool) =>
        (Bool.eqb (andb b c) (orb b c)) 
        ==>
        (Bool.eqb b c).
(*! QuickCheck andb_eq_orb. *)

