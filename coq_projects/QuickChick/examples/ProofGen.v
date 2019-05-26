From QuickChick Require Import QuickChick Tactics.
Require Import String. Open Scope string.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Import GenLow GenHigh.
Require Import List.
Import ListNotations.
Import QcDefaultNotation. Open Scope qc_scope.

Import QcDoNotation.


Set Bullet Behavior "Strict Subproofs".

Inductive ty : nat -> Type :=
| pi : forall n i , i <= n -> ty n.

Program Definition gen_ty (p : nat) :  G (ty p) :=
  bindGen' (choose (0, p)) (fun m H =>
  returnGen (pi p m  _) ).
Next Obligation.
  apply semChoose in H; auto.
Defined.
