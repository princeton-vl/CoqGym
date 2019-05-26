Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

From QuickChick Require Import QuickChick.

Theorem foo : forall (x y: nat) , x = y -> x = 0.
Proof.
  quickchick.