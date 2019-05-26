(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

 Load "hSpoly".

Notation CombLinear1 :=
  (CombLinear A A0 eqA plusA multA eqA_dec n ltM ltM_dec) 
  (only parsing).
Notation Spoly1 :=
  (Spoly_1 A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec)
  (only parsing).
Notation Grobner1 :=
  (Grobner A A0 A1 eqA plusA invA minusA multA divA eqA_dec n ltM ltM_dec)
  (only parsing).
