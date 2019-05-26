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


Set Nested Proofs Allowed.
Require Import nat_trees.
Require Import More_on_Lists.
Require Import search_trees.
Require Import Adding.


(* Construction of a binary search tree containing the elements of
  a list of natural numbers *)

Theorem list2trees :
 forall l : list nat,
 {t : nat_tree | search t /\ (forall p : nat, In p l <-> occ t p)}.

Proof.

 Lemma list2trees_aux :
  forall (l : list nat) (t : nat_tree),
  search t ->
  {t' : nat_tree |
  search t' /\ (forall p : nat, In p l \/ occ t p <-> occ t' p)}.
 Proof.
simple induction l;
 [ intros t s; exists t
 | intros hd tl hr t H; elim (insert hd t H); intros x i; elim (hr x);
    [ intros n a; exists n | idtac ] ].
(*
Realizer Fix list2trees_aux{list2trees_aux/1 :
                         (list nat) -> nat_tree -> nat_tree :=
                   [l:(list nat)][t:nat_tree]
                    <nat_tree>Cases l of
                        nil =>  t
                      | (cons  hd tl) =>
                           (list2trees_aux tl (insert hd t))
                    end}.
  Program_all.
*)
  (* the logical subgoals ... *)
  
  (* first logical subgoal  :
    l : (list nat)
    t : nat_tree
    H : (search t)
    ============================
     (search t)/\((p:nat)(In nat p (nil nat))\/(occ t p) <-> (occ t p))
   
    An uninteresting sequence of connective eliminations :-)
  
  *)


  split; auto with searchtrees datatypes.
  intro p; unfold iff in |- *; split; intros H0.
  elim H0; auto with searchtrees datatypes.
  intro; absurd (In p nil); auto with searchtrees datatypes.
  auto with searchtrees datatypes.

  (* second logical subgoal :
                 /\((p:nat)(In nat p l)\/(occ t p) <-> (occ t' p)))}
    l : (list nat)
    t : nat_tree
    H : (search nt)
    hd : nat
    tl : (list nat)
    x : nat_tree
    i : (INSERT hd t x)
    ============================
     (search x)
  *)
2: elim i; auto with searchtrees datatypes.
  
  (* third logical subgoal 
  
    l : (list nat)
    t : nat_tree
    H : (search t)
    hd : nat
    tl : (list nat)
    x : nat_tree
    i : (INSERT hd t x)
    n : nat_tree
    a : (search n)/\((p:nat)(In nat p tl)\/(occ x p) <-> (occ n p))
    ============================
     (search n)
     /\((p:nat)(In nat p (cons nat hd tl))\/(occ t p) <-> (occ n p))
  
  *)
  (* we first deal with the two occurrences of (search n) *)
  split; elim a; auto with searchtrees datatypes.
  (* ok ; now the heavy part ! *)
  intros; unfold iff in |- *; split; intros.
  elim H2; intros.
  inversion_clear H3.
  rewrite <- H4.
  elim (H1 hd); intros.
  apply H3. 
  right; elim i; auto with searchtrees datatypes.
  elim (H1 p); auto with searchtrees datatypes.
  elim (H1 p); intros.
  apply H4.
  right; elim i; auto with searchtrees datatypes.
  elim (H1 p); intros.
  elim (H4 H2); intros. 
  auto with searchtrees datatypes.
  elim i; intros.
  elim (H8 p).
  auto with searchtrees datatypes.
  simple induction 1; auto with searchtrees datatypes.
  auto with searchtrees datatypes.
 Defined.

 intros l; elim (list2trees_aux l NIL); [ intros x a; exists x | idtac ].
 
(*
 Realizer [l:(list nat)](list2trees_aux l NIL).
 Program_all.
*)
 elim a; split; [ auto with searchtrees datatypes | idtac ].
 intro p0; unfold iff in |- *; split; intros.
 elim (H0 p0); intros.
 auto with searchtrees datatypes.
 elim (H0 p0); intros. 
 elim (H3 H1); auto with searchtrees datatypes.
 intro; absurd (occ NIL p0); auto with searchtrees datatypes.
 auto with searchtrees datatypes.
Defined.


