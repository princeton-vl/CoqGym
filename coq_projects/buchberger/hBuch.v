(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

 Load "hBuchAux".

Notation unit1 := (unit A A0 A1 eqA divA n ltM) (only parsing).
Notation buch1 :=
  (buch A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os)
  (only parsing).
Notation stable1 := (stable A A0 eqA plusA multA eqA_dec n ltM ltM_dec)
  (only parsing).