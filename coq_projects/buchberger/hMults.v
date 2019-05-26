(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

 Load "hPlus".
Notation mults1 := (mults (A:=A) multA (n:=n)) (only parsing).

Hint Resolve (canonical_mults _ _ _ _ _ _ _ _ _ cs eqA_dec n).

Hint Resolve (mults_comp _ _ _ _ _ _ _ _ _ cs n).
Hint Resolve (mults_com _ _ _ _ _ _ _ _ _ cs n).
Hint Resolve (mults_multTerm _ _ _ _ _ _ _ _ _ cs n).
Hint Resolve (mults_invTerm _ _ _ _ _ _ _ _ _ cs eqA_dec n).
Hint Resolve (mults_dist1 _ _ _ _ _ _ _ _ _ cs eqA_dec n).
Hint Resolve (mults_dist2 _ _ _ _ _ _ _ _ _ cs eqA_dec n).
Hint Resolve (mults_dist_pluspf _ _ _ _ _ _ _ _ _ cs eqA_dec n).
Hint Resolve (mults_multTerm _ _ _ _ _ _ _ _ _ cs n).
Hint Resolve (mults_T1 _ _ _ _ _ _ _ _ _ cs).