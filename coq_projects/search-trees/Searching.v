(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
(*     A development written by Pierre Castéran for Coq V6.1
     
Coq : A product of inria : "http://pauillac.inria.fr/coq/coq-eng.html"

Pierre Castéran : A product of LaBRI : 


LaBRI, Universite Bordeaux-I      |    12 place Puy Paulin
351 Cours de la Liberation        |    33000 Bordeaux
F-33405 TALENCE Cedex             |    France
France                            |    (+ 33) 5 56 81 15 80
tel : (+ 33) 5 56 84 69 31
fax : (+ 33) 5 56 84 66 69
email: casteran@labri.u-bordeaux.fr       
www: http://dept-info.labri.u-bordeaux.fr/~casteran

"Les rêves sont aussi beaux que la réalité, mais ils ne sont pas mieux".
( J.L.Borges )



*)

Require Import nat_trees.
Require Import search_trees.
Require Import Compare_dec.


(*    IV: Searching  in a binary search tree 
*********************************************
*********************************************)

(* we give the validation of the classical searching algorithm,
   which uses the go_left and go_right lemmas *)

Theorem sch :
 forall (p : nat) (t : nat_tree), search t -> {occ t p} + {~ occ t p}.
(**************************************************************)
Proof.
simple induction t;
 [ intros s; right
 | intros n t1 hr1 t2 hr2 s; elim (le_gt_dec p n); intros h;
    [ elim (le_lt_eq_dec p n h); intros h';
       [ elim hr1; [ intro k; left | intro k; right | idtac ] | left ]
    | elim hr2; [ intro k; left | intro k; right | idtac ] ] ];
 auto with searchtrees.

(*
Realizer Fix sch{sch/2 :  nat -> nat_tree -> bool :=
                   [p:nat][t:nat_tree]
                    <bool>Cases t of
                       NIL => false
                    | (bin n t1 t2) =>
                       <bool> if (le_gt_dec p n)
                                then <bool> if (le_lt_eq_dec p n)
                                             then (sch p t1) 
                                             else true
                                else (sch p t2) 
                    end}.
 Program_all.
 *)
 Hint Resolve search_l search_r go_left go_right: searchtrees.
 eauto with searchtrees.
 eauto with searchtrees.
 rewrite h'; eauto with searchtrees.
 unfold not in |- *; eauto with searchtrees.
 eauto with searchtrees.
Defined.
