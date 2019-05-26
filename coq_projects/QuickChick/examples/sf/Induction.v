(* QuickChick Prelude *)
Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import String List. Open Scope string.

From QuickChick Require Import QuickChick Tactics.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Import QcDefaultNotation. Open Scope qc_scope.

Set Bullet Behavior "Strict Subproofs".

(* End prelude *)

Require Export Basics.

Theorem plus_n_O_firsttry : forall n:nat,
  n = n + 0.
Admitted. (* QuickChick plus_n_O_firsttry. *)

Theorem minus_diag : forall n,
  minus n n = 0.
Admitted. (* QuickChick minus_diag. *)

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Admitted. (* QuickChick mult_0_r. *)

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Admitted. (* QuickChick plus_n_Sm. *)

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Admitted. (* QuickChick plus_comm. *)

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Admitted. (* QuickChick plus_comm *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Admitted. (* QuickChick double_plus. *)

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Admitted. (* QuickChick evenb_S. *)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Admitted. (* QuickChick mult_0_plus'. *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Admitted. (* QuickChick plus_rearrange. *)

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Admitted. (* QuickChick plus_assoc'. *)

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Admitted. (* QuickChick plus_swap. *)

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Admitted. (* QuickChick mult_comm. *)

Theorem leb_refl : forall n:nat,
  true = leb n n.
Admitted. (* QuickChick leb_refl. *)

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Admitted. (* QuickChick zero_nbeq_S. *)

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Admitted. (* QuickChick andb_false_r. *)

Derive ArbitrarySizedSuchThat for (fun m => le n m).
Derive SizeMonotonicSuchThatOpt for (fun m => le n m).
Derive GenSizedSuchThatSizeMonotonicOpt for (fun m => le n m).
Derive SizedProofEqs for (fun m => le n m).
Derive GenSizedSuchThatCorrect for (fun m => le n m).

Theorem plus_ble_compat_l : forall n m p : nat,
  leb n m = true -> leb (p + n) (p + m) = true.
Admitted.

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Admitted. (* QuickChick S_nbeq_0 *)

Theorem mult_1_l : forall n:nat, 1 * n = n.
Admitted. (* QuickChick mult_1_l. *)

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Admitted. (* QuickChick all3_spec.*)

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Admitted. (* QuickChick mult_plus_distr_r. *)

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Admitted. (* QuickChick mult_assoc. *)

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Admitted. (* QuickChick beq_nat_refl. *)

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Admitted. (* QuickChick plus_swap'. *)
