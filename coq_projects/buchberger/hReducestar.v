(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

 Load "hReduceplus".

Notation reducestar1 :=
  (reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec)
  (only parsing).
Notation reducestar_trans1 :=
  (reducestar_trans A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
     ltM_dec os) (only parsing).
Notation mks1 := (mks A A0 eqA n ltM) (only parsing).
Notation Reducef1 :=
  (Reducef A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
     os) (only parsing).


