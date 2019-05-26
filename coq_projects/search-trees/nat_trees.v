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

(* binary nat trees *)

Global Set Asymmetric Patterns.
Require Export Peano_dec.


(*       II The binary tree data structure
******************************************
******************************************
 

   We define here the "nat_tree" inductive data type.
   In the remaining of this file, the term "binary tree" will
   denote a complete binary tree, the internal nodes of which are
   labeled by natural integers.
*)

Inductive nat_tree : Set :=
  | NIL : nat_tree
  | bin : nat -> nat_tree -> nat_tree -> nat_tree.

(*
    Example:


         3
       /  \
      /    \
     7      8          Coq representation:
    / \    / \
   NIL \  NIL NIL      (bin three (bin seven NIL (bin nine NIL NIL))
        9                         (bin eight NIL NIL))
       / \             where three is the term (S (S (S O))) and so on ...
      /   \
     NIL  NIL
*)


(* II.1   Some definitions and lemmas 
   ************************************)


(* (binp t) means "t is not NIL"  *)

Inductive binp : nat_tree -> Prop :=
    binp_intro : forall (n : nat) (t1 t2 : nat_tree), binp (bin n t1 t2).

Hint Resolve binp_intro: searchtrees.


Lemma NIL_not_bin : ~ binp NIL.
(******************************)
Proof.
 unfold not in |- *; intros H.
 inversion_clear H.
 Qed.
Hint Resolve NIL_not_bin: searchtrees.


Lemma diff_nil_bin : forall (n : nat) (t1 t2 : nat_tree), bin n t1 t2 <> NIL.
(************************************************************)
Proof.
 intros; discriminate.
Qed.

Hint Resolve diff_nil_bin: searchtrees.




(* II.2 membership
*******************************************
(occ t p) means: "t has an occurrence of p" *)




Inductive occ : nat_tree -> nat -> Prop :=
  | occ_root : forall (n : nat) (t1 t2 : nat_tree), occ (bin n t1 t2) n
  | occ_l :
      forall (n p : nat) (t1 t2 : nat_tree), occ t1 p -> occ (bin n t1 t2) p
  | occ_r :
      forall (n p : nat) (t1 t2 : nat_tree), occ t2 p -> occ (bin n t1 t2) p.

Hint Resolve occ_root occ_l occ_r: searchtrees.

Definition member (n : nat) (t : nat_tree) := occ t n.


Derive Inversion_clear OCC_INV with
 (forall (n p : nat) (t1 t2 : nat_tree), occ (bin n t1 t2) p).

(* Coq < Check OCC_INV.
OCC_INV : (P:nat->nat->nat_tree->nat_tree->Prop)
        (n,p:nat)(t1,t2:nat_tree)
            (P p p t1 t2)
             ->((occ t1 p)->(P n p t1 t2))
                ->((occ t2 p)->(P n p t1 t2))
                   ->(occ (bin n t1 t2) p)->(P n p t1 t2) *)

Lemma occ_inv :
 forall (n p : nat) (t1 t2 : nat_tree),
 occ (bin n t1 t2) p -> n = p \/ occ t1 p \/ occ t2 p.
(**********************************************)
Proof.
intros.
inversion H using OCC_INV; auto with searchtrees.
Qed.

Hint Resolve occ_inv: searchtrees.

Lemma not_occ_nil : forall p : nat, ~ occ NIL p.
(**************************************)
Proof.
unfold not in |- *; intros p H.
inversion_clear H.
Qed.

Hint Resolve not_occ_nil: searchtrees.


