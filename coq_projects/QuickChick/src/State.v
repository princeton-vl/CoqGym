Set Implicit Arguments.

Require Import GenLow.
Require Import RandomQC.
Require Import Coq.Strings.String.

Require Import StringOT.
Require Import FSets.FMapAVL.

Module Map := FMapAVL.Make(StringOT).

Record State := MkState
  { maxSuccessTests   : nat
  ; maxDiscardedTests : nat
  ; maxShrinkNo       : nat
  ; computeSize       : nat -> nat -> nat

  ; numSuccessTests   : nat
  ; numDiscardedTests : nat

  ; labels            : Map.t nat

  ; expectedFailure   : bool
  ; randomSeed        : RandomSeed

  ; numSuccessShrinks : nat
  ; numTryShrinks     : nat
  }.

Definition updTryShrinks (st : State) (f : nat -> nat) : State :=
  match st with
    | MkState mst mdt ms cs nst ndt ls e r nss nts =>
      MkState mst mdt ms cs nst ndt ls e r nss (f nts)
  end.

Definition updSuccessShrinks (st : State) (f : nat -> nat) : State :=
  match st with
    | MkState mst mdt ms cs nst ndt ls e r nss nts =>
      MkState mst mdt ms cs nst ndt ls e r (f nss) nts
  end.
