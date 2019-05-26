From QuickChick Require Import QuickChick.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
(* end hide *)
Declare ML Module "extract".

Parameter plus' : nat -> nat -> nat.

Extract Constant plus' => "Extract.plus".

Definition plus_prop x y :=
  plus' x y = x + y?.

(*! QuickChick plus_prop. *)
