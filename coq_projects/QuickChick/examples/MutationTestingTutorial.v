From QuickChick Require Import QuickChick Tactics.
Require Import String. Open Scope string.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Import GenLow GenHigh.
Require Import List.
Import ListNotations.
Import QcDefaultNotation. Open Scope qc_scope.
Import QcDoNotation.

Require Import Arith.

Set Bullet Behavior "Strict Subproofs".

(*! Section Prop12 *)

Definition testProp1 (x : nat) := x =? 0.

Definition testProp2 (x : nat) := x =? x.

(* quickChick <filename> (-m test) -s Prop12 *)
(*!
QuickChick testProp1. 
*)

(*! QuickChick testProp2. *)

(*! Section Prop3 *)(*! extends Prop12 *)
Definition testProp3 (x y : nat) := x =? y.

(*!
QuickChick testProp3.
*)

(*! Section Prop4 *)
Definition testProp4 (x y : nat) := x =? y.

(*!
QuickChick testProp4.
*)

(*! Section Mutant *)
Definition plus1 (x : nat) := (*!*) x + 1 (*! x *) (*! x + x *) .

(*! Section PropPlus *)(*! extends Mutant *)

(* quickChick <filename> -m mutate -s PropPlus *)
Definition propPlus x := x <? plus1 x.

(*!
QuickChick propPlus.
*)


