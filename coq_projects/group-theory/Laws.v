(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(*                           Group Theory in Coq                            *)
(*                                                                          *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*									    *)
(*			         Gilles Kahn 				    *)
(*									    *)
(*                                  INRIA                                   *)
(*                             Sophia-Antipolis                             *)
(*									    *)
(*				 January 1996				    *)
(*                                                                          *)
(****************************************************************************)

Require Import Ensembles.
Section Basic_laws.
Variable U : Type.
Variable op : U -> U -> U.

Definition commutative := forall x y : U, op x y = op y x.

Definition associative := forall x y z : U, op x (op y z) = op (op x y) z.

Definition left_neutral (e : U) := forall x : U, op e x = x.

Definition right_neutral (e : U) := forall x : U, op x e = x.

Definition left_inverse (inv : U -> U) (e : U) :=
  forall x : U, op (inv x) x = e.

Definition right_inverse (inv : U -> U) (e : U) :=
  forall x : U, op x (inv x) = e.
Variable D : Ensemble U.

Definition endo_function (f : U -> U) :=
  forall x : U, In U D x -> In U D (f x).

Definition endo_operation (op : U -> U -> U) :=
  forall x y : U, In U D x -> In U D y -> In U D (op x y).
End Basic_laws.
Hint Unfold endo_function endo_operation commutative associative left_neutral
  right_neutral left_inverse right_inverse.


