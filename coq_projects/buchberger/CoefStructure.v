(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import Relation_Definitions.

Record CoefStructure (A : Set) (A0 A1 : A) (eqA : A -> A -> Prop)
  (plusA : A -> A -> A) (invA : A -> A) (minusA multA : A -> A -> A)
  (divA : A -> forall b : A, ~ eqA b A0 -> A) : Prop := mkCoefStructure
  {A1_diff_A0 : ~ eqA A1 A0;
   eqA_ref : reflexive A eqA;
   eqA_sym : symmetric A eqA;
   eqA_trans : transitive A eqA;
   plusA_assoc :
    forall a b c : A, eqA (plusA a (plusA b c)) (plusA (plusA a b) c);
   plusA_com : forall a b : A, eqA (plusA a b) (plusA b a);
   plusA_eqA_comp :
    forall a b c d : A, eqA a c -> eqA b d -> eqA (plusA a b) (plusA c d);
   plusA_A0 : forall a : A, eqA a (plusA a A0);
   invA_plusA : forall a : A, eqA A0 (plusA a (invA a));
   invA_eqA_comp : forall a b : A, eqA a b -> eqA (invA a) (invA b);
   minusA_def : forall a b : A, eqA (minusA a b) (plusA a (invA b));
   multA_eqA_comp :
    forall a b c d : A, eqA a c -> eqA b d -> eqA (multA a b) (multA c d);
   multA_assoc :
    forall a b c : A, eqA (multA a (multA b c)) (multA (multA a b) c);
   multA_com : forall a b : A, eqA (multA a b) (multA b a);
   multA_dist_l :
    forall a b c : A,
    eqA (plusA (multA c a) (multA c b)) (multA c (plusA a b));
   multA_A0_l : forall a : A, eqA (multA A0 a) A0;
   multA_A1_l : forall a : A, eqA (multA A1 a) a;
   divA_rew :
    forall (a b : A) (nZ1 nZ2 : ~ eqA b A0), divA a b nZ1 = divA a b nZ2;
   divA_is_multA :
    forall (a b : A) (nZb : ~ eqA b A0), eqA a (multA (divA a b nZb) b);
   divA_eqA_comp :
    forall (a b c d : A) (nZb : ~ eqA b A0) (nZd : ~ eqA d A0),
    eqA a c -> eqA b d -> eqA (divA a b nZb) (divA c d nZd);
   divA_multA_comp_r :
    forall (a b c : A) (nZc : ~ eqA c A0),
    eqA (divA (multA a b) c nZc) (multA (divA a c nZc) b);
   divA_invA_r :
    forall (a b : A) (nZb : ~ eqA b A0) (nZib : ~ eqA (invA b) A0),
    eqA (divA a (invA b) nZib) (invA (divA a b nZb))}.
