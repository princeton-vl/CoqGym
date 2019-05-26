(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

 Variable A : Set.
Variable A0 : A.
Variable A1 : A.
Variable eqA : A -> A -> Prop.
Variable plusA : A -> A -> A.
Variable invA : A -> A.
Variable minusA : A -> A -> A.
Variable multA : A -> A -> A.
Variable divA : A -> forall b : A, ~ eqA b A0 -> A.
Variable cs : CoefStructure A A0 A1 eqA plusA invA minusA multA divA.
Variable eqA_dec : forall a b : A, {eqA a b} + {~ eqA a b}.
