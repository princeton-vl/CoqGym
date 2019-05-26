Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

From QuickChick Require Import QuickChick.
Require Import Arith.

Require Import Foo.

(*! Section prop_plus_one *)(*! extends plus_one *)
Definition prop_plus_one x := 
  whenFail (show (x, plus_one x)) (x <? plus_one x).

(*! QuickChick prop_plus_one. *)

(*! Section prop_plus_one_two *)(*! extends plus_one plus_two *)
Definition prop_plus_one_two x := 
  whenFail (show (x, (plus_one x, plus_two x))) (plus_one x <? plus_two x).

(*! QuickChick prop_plus_one_two. *)
