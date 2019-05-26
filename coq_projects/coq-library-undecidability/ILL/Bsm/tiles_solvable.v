(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Max Omega Wellfounded Bool.

Require Import utils list_bool.

Set Implicit Arguments.

Fixpoint tile_concat ln lt : (list bool) * list bool:=
  match ln with
    | nil   => (nil,nil)
    | x::ln => match nth x lt (nil,nil), tile_concat ln lt with
                 | (th,tl), (hh,ll) => (hh++th,ll++tl)
               end
  end.

Definition tiles_solvable lt := 
   exists ln, ln <> nil 
           /\ Forall (fun x => x < length lt) ln 
           /\ let (hh,ll) := tile_concat ln lt in hh = ll.


