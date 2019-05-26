(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import Factorization_Synth.
Require Import Comp_Synth.
Require Extraction.

(* The parameter BASE is in fact not necessary in extracted code,
   the following commands help making it disappear from the code. *)
  
Extraction Inline Tl val_inf.
Extraction Implicit Comparator_Relation.FR [n].
 
(* some more optimizations *)

Extraction Inline factorization_for_synthesis.

Extraction "Factorization/Comparator/comp.ml" Comparator.
