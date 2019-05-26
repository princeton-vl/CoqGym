Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

From QuickChick Require Import QuickChick.
Require Import Arith.

Require Import Foo.

(*! Section prop_plus_one_again *)(*! extends plus_one *)
Definition prop_plus_one_again x := 
  whenFail (show (x, plus_one x)) (x <? plus_one x).

(*! QuickChick prop_plus_one_again. *)
