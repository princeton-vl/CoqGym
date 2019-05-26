(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

 Load "hComb".

Notation zerop1 := (zerop A A0 eqA n ltM) (only parsing).
Notation nf1 :=
  (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os)
  (only parsing).
Notation addEnd1 := (addEnd A A0 eqA n ltM) (only parsing).
Notation Cb1 := (Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec)
  (only parsing).
Notation red1 :=
  (red A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec)
  (only parsing).
Notation spolyp1 :=
  (spolyp A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
     os) (only parsing).
Notation divp1 := (divp A A0 eqA multA divA n ltM) (only parsing).
Notation ppcp1 := (ppcp A A0 A1 eqA plusA invA minusA multA divA cs n ltM)
  (only parsing).
Notation foreigner1 := (foreigner A A0 A1 eqA multA n ltM) (only parsing).
Notation foreigner_dec1 := (foreigner_dec A A0 A1 eqA multA n ltM)
  (only parsing).
Notation divp_dec1 := (divp_dec _ _ _ _ _ _ _ _ _ cs n ltM) (only parsing).
Notation divp_trans1 := (divp_trans _ _ _ _ _ _ _ _ _ cs n ltM)
  (only parsing).
Notation zerop_dec1 := (zerop_dec A A0 eqA n ltM) (only parsing).