Require Import List.
Require Import ExtLib.Programming.With.

Record RTest : Set := mkRTest {
  a : bool ; b : nat ; c : bool
}.

Bind Scope struct_scope with RTest.

Global Instance Struct_RTest : Struct RTest := {
  fields := ((@existT _ _ _ a) :: (@existT _ _ _ b) :: (@existT _ _ _ c):: nil) ;
  ctor   := mkRTest
}.

Global Instance Acc_RTest_a : Accessor a := { acc := Here }.

Global Instance Acc_RTest_b : Accessor b := { acc := Next Here }.

Global Instance Acc_RTest_c : Accessor c := { acc := Next (Next Here) }.


Eval compute in {$ mkRTest true 1 true with c := false $}%record.

Eval compute in forall x : RTest, c {$ x with c := false $}%record = false.
