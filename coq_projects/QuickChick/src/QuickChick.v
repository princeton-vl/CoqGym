Require Import Extraction.
Require Import Ltac.

(*
Declare ML Module "Error".
Declare ML Module "genericLib".
Declare ML Module "coqLib".
Declare ML Module "setLib".
Declare ML Module "semLib".
Declare ML Module "genLib".
Declare ML Module "unify".

Declare ML Module "weightmap".

Declare ML Module "quickChick".

Declare ML Module "Sized".
Declare ML Module "ArbitrarySized".
Declare ML Module "SizeMon".
Declare ML Module "SizeSMon".
Declare ML Module "SizeCorr".
Declare ML Module "ArbitrarySizedST".
Declare ML Module "GenSizedSTMonotonic".
Declare ML Module "GenSizedSTSizeMonotonic".
Declare ML Module "SizedProofs".
Declare ML Module "GenSTCorrect".

Declare ML Module "simplDriver".
Declare ML Module "depDriver".
Declare ML Module "driver".
*)
Declare ML Module "quickchick_plugin".

Axiom _W : nat -> Prop.
Axiom _Size : Prop.

Require Export Show.
Require Export RandomQC.
Require Export Sets.
Require Export Nat_util.
Require Export GenLow.
Require Export GenHigh.
Require Export State.
Require Export Checker.
Require Export SemChecker.
Require Export Test.
Require Export ExtractionQC.
Require Export Decidability.
Require Export Classes. 
Require Export Instances.
Require Export DependentClasses.
Require Export Typeclasses.
Require Export Mutation.
Export GenLow GenHigh.

Global Unset Asymmetric Patterns.
Global Set Bullet Behavior "Strict Subproofs".

(* TODO: Figure out better place for these *)
(* String and Ascii Instances *)

Require Export Ascii String.

(* Derive (Arbitrary, Show) for ascii. *)

(* Derive (Arbitrary, Show) for string. *)



