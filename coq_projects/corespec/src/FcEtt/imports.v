Require Export Coq.Unicode.Utf8.

Require Export Coq.Program.Basics.
Require Export Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export FcEtt.ett_ott.

(* SSR *)

Require Export mathcomp.ssreflect.ssreflect.
Close Scope boolean_if_scope.
Global Open Scope general_if_scope.

(*
From mathcomp Require Export ssrfun ssrmatching.
*)


Global Set Implicit Arguments.
Global Set Bullet Behavior "Strict Subproofs".

(* Masking this nasty notation from the stdlib *)
Notation sort := sort (only parsing).
