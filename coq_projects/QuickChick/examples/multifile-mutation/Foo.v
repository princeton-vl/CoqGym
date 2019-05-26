Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

From QuickChick Require Import QuickChick.
Require Import Arith.

(*! Section plus_one *)

Definition plus_one (x : nat) := (*! *) x + 1 (*!! DROP+1 *) (*! x *) (*!! DOUBLE *) (*! x + x *) .  

(*! Section plus_two *)

Definition plus_two (x : nat) := (*! *) x + 2 (*! x *) .
