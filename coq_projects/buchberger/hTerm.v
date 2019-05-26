(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

 Hint Resolve (fun a n => eqTerm_refl _ _ _ _ _ _ _ _ _ cs a n).

Notation Term1 := (Term A n) (only parsing).
Notation eqTerm1 := (eqTerm (A:=A) eqA (n:=n)) (only parsing).
Notation zeroP1 := (zeroP (A:=A) A0 eqA (n:=n)) (only parsing).
Notation eqTerm_sym1 := (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n) (only parsing).
Notation eqTerm_trans1 := (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  (only parsing).
Notation eqTerm_dec1 := (eqTerm_dec _ _ eqA_dec n) (only parsing).
Notation zeroP_dec1 := (zeroP_dec A A0 eqA eqA_dec n) (only parsing).
Notation plusTerm1 := (plusTerm (A:=A) plusA (n:=n)) (only parsing).
Notation minusTerm1 := (minusTerm (A:=A) minusA (n:=n)) (only parsing).
Notation multTerm1 := (multTerm (A:=A) multA (n:=n)) (only parsing).
Notation invTerm1 := (invTerm (A:=A) invA (n:=n)) (only parsing).


Hint Resolve (multTerm_assoc _ _ _ _ _ _ _ _ _ cs).
Hint Resolve (multTerm_com _ _ _ _ _ _ _ _ _ cs).
Hint Resolve (eqTerm_plusTerm_comp _ _ _ _ _ _ _ _ _ cs).
Hint Resolve (eqTerm_multTerm_comp _ _ _ _ _ _ _ _ _ cs).
Hint Resolve (eqTerm_invTerm_comp _ _ _ _ _ _ _ _ _ cs).
Hint Resolve (T1_nz _ _ _ _ _ _ _ _ _ cs n).
Hint Resolve (nZero_invTerm_nZero _ _ _ _ _ _ _ _ _ cs).
Hint Resolve (zeroP_multTerm_l _ _ _ _ _ _ _ _ _ cs).
Hint Resolve (zeroP_multTerm_r _ _ _ _ _ _ _ _ _ cs).
Hint Resolve (nzeroP_multTerm _ _ _ _ _ _ _ _ _ cs). 
Hint Resolve (T1_multTerm_l _ _ _ _ _ _ _ _ _ cs n).
Hint Resolve (T1_multTerm_r _ _ _ _ _ _ _ _ _ cs n).
Hint Resolve (invTerm_invol _ _ _ _ _ _ _ _ _ cs n).
Hint Resolve (zeroP_minusTerm _ _ _ _ _ _ _ _ _ cs n).

Hint Resolve multTerm_eqT invTerm_eqT.