(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

 Load "hEq".

Notation pluspf1 :=
  (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec)
  (only parsing).
Hint Resolve (canonical_pluspf _ A0 _ plusA eqA_dec _ _ ltM_dec os).
Hint Resolve (pluspf_assoc _ _ _ _ _ _ _ _ _ cs).
Hint Resolve (pluspf_com _ _ _ _ _ _ _ _ _ cs).
Hint Resolve (eqp_pluspf_com _ _ _ _ _ _ _ _ _ cs).
Hint Resolve (p0_pluspf_l _ _ _ _ _ _ _ _ _ cs).
Hint Resolve (p0_pluspf_r _ _ _ _ _ _ _ _ _ cs).