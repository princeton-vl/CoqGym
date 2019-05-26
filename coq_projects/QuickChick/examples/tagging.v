From QuickChick Require Import QuickChick.
Require Import Arith.

Definition tag_prop (x : nat) : Checker := 
  collect x (
  if x = 3 ? then tag "3" false
  else if 2 <? x then tag "more than 2" false 
       else checker true).

QuickChick tag_prop.