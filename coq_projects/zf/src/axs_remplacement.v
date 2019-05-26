(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(***************************************************************************)
(* File: axs_remplacement.v                                                *)
(* auteur: alex@sysal.ibp.fr                                               *)
(* date: 19/10/95                                                          *)
(***************************************************************************)
Require Export axs_comprehension.

(***************************************************************************)
(* 0.5 Schema d'axiome de remplacement                                     *)
(***************************************************************************)
Parameter remp : (E -> E -> Prop) -> E -> E.
Axiom
  axs_remplacement :
    forall (F : E -> E -> Prop) (v0 : E),
    (forall w0 w1 w2 : E, F w0 w1 /\ F w0 w2 -> w1 = w2) ->
    forall y : E, In y (remp F v0) <-> (exists x : E, In x v0 /\ F x y).
(***************************************************************************)
(*                     Next : couples.v                                    *)
(***************************************************************************)