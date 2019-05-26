(** DepMap: Maps with explicit domain contained in their type *)
Require Import Orders.

(** Interfaces **)
Require Export DepMapInterface.
Require Export DepMapFactsInterface.

(** Implementations **)
Require Export DepMapImplementation.
Require Export DepMapFactsImplementation.

Module Make (X : OrderedType) : DepMapFacts (X).
  Module Map := DepMapImpl(X).
  Module Facts := DepMapFactsOn(X)(Map).
  Include Facts.
End Make.