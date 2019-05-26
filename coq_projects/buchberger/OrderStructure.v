(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import Relation_Definitions.

Record OrderStructure (A : Set) (M1 : A) (ltM : A -> A -> Prop)
  (plusM : A -> A -> A) : Prop := mkOrderStructure
  {M1_min : forall x : A, ~ ltM x M1;
   ltM_nonrefl : forall x : A, ~ ltM x x;
   ltM_trans : transitive A ltM;
   ltM_wf : well_founded ltM;
   ltM_plusr : forall x y z : A, ltM x y -> ltM (plusM x z) (plusM y z);
   ltM_plusl : forall x y z : A, ltM x y -> ltM (plusM z x) (plusM z y)}.
