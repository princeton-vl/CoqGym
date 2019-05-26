(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

 Load "hReducestar".

Notation spolyf1 :=
  (spolyf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec)
  (only parsing).
Notation SpolyQ1 :=
  (SpolyQ A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec)
  (only parsing).
Notation ReduStarConfluent1 :=
  (ReduStarConfluent A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec)
  (only parsing).