(* QuickChick Prelude *)
Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import String List. Open Scope string.

From QuickChick Require Import QuickChick Tactics.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Import QcDefaultNotation. Open Scope qc_scope.

Set Bullet Behavior "Strict Subproofs".

(* End prelude *)

Require Export Poly.

Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Admitted. (* Leo: OUT-OF-SCOPE *)

Theorem silly2 : forall (n m o p : nat),
     n = m  ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Admitted. (* Higher-order *)

Theorem silly3_firsttry : forall (n : nat),
     n = 5 ->
(*     true = beq_nat n 5  -> *)
     beq_nat (S (S n)) 7 = true.
Admitted. (* (*N*) QuickChick silly3_firsttry. *)


Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Admitted. (* (*N*) QuickChick rev_exercise1. *)

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Admitted. (* (*N*) QuickChick trans_eq. *)

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Admitted. (* Leo: OUT-OF-SCOPE *)

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Admitted. (* Leo: OUT-OF-SCOPE *)

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Admitted. (* Leo: OUT-OF-SCOPE *)

Theorem beq_nat_0_l : forall n,
    0 = n -> n = 0.
Admitted. (* (*N*) QuickChick beq_nat_0_l. *)

Theorem inversion_ex4 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Admitted. (* Leo: OUT-OF-SCOPE *)

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Admitted. (* Leo: CoArb Weirdness *)

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Admitted. (* Leo: OUT-OF-SCOPE *)

Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Admitted. (* Leo: OUT-OF-SCOPE *)

Theorem beq_id_true : forall (x y : id),
  x = y -> x = y.
Admitted. (* (*N*) QuickChick beq_id_true. *)

(* Leo: Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X), *)
Theorem nth_error_after_last: forall  (X : Type) (l : list X) (n : nat),
     length l = n ->
     nth_error l n = None.
Admitted. (* (*N*) QuickChick nth_error_after_last. *)

Definition square n := n * n.

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Admitted. (* QuickChick square_mult *)

Definition foo (x: nat) := 5.

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Admitted. (* QuickChick silly_fact_1. *)

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Admitted. (* QuickChick silly_fact_2. *)

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Admitted. (* QuickChick sillyfun_false. *)

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Admitted. (* Leo: OUT-OF-SCOPE *)

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Admitted. (* Coarbitrary *)

Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Admitted. (* QuickChick beq_nat_sym. *)

Theorem beq_nat_trans : forall n m p,
  beq_nat n m = true ->
  beq_nat m p = true ->
  beq_nat n p = true.
Admitted. (* Leo: OUT-OF-SCOPE *)

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Admitted.


