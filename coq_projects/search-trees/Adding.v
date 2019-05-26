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


(* V:        INSERTION 
**********************************
**********************************


V.1   Definition of an INSERT predicate (a la  Prolog)
***************************************************


We begin with the definition of a predicate:

(INSERT n t t') if t' is a binary search tree containing exactly
  n and the elements of t *)


Inductive INSERT (n : nat) (t t' : nat_tree) : Prop :=
    insert_intro :
      (forall p : nat, occ t p -> occ t' p) ->
      occ t' n ->
      (forall p : nat, occ t' p -> occ t p \/ n = p) ->
      search t' -> INSERT n t t'.

Hint Resolve insert_intro: searchtrees.

(* ZZZZ ! insert_rec is defined ! yep ! *)


(* the specification of an insertion algorithm *)

Definition INSERT_SPEC (n : nat) (t : nat_tree) :=
  {t' : nat_tree | INSERT n t t'}.



(* technical lemmas preparing our algorithm *)



Lemma insert_nil : forall n : nat, INSERT n NIL (bin n NIL NIL).
(******************************************************)
Proof.
 intro n; split; auto with searchtrees.
 intros p H; inversion_clear H; auto with searchtrees. (* miraculous, no ? *)
Defined.
Hint Resolve insert_nil: searchtrees.



(* Inserting in the left son *)

Lemma insert_l :
 forall (n p : nat) (t1 t'1 t2 : nat_tree),
 n < p ->
 search (bin p t1 t2) ->
 INSERT n t1 t'1 -> INSERT n (bin p t1 t2) (bin p t'1 t2).
(**********************************************************)
Proof.
 intros n p t1 t'1 t2 H H0 H1; split.
 intros p0 H2; inversion_clear H2.
 auto with searchtrees.
 elim H1; auto with searchtrees.
 auto with searchtrees.
 constructor 2; elim H1; auto with searchtrees.
 intros p0 H2.
 inversion_clear H2.
 auto with searchtrees.
 elim H1; intros. 
 elim (H5 p0); auto with searchtrees.
 auto with searchtrees.
 elim H1; constructor 2; auto with searchtrees.
 eapply search_r; eauto with searchtrees.
 split; intros.
 elim (H4 q).
 intro; cut (maj p t1).
 simple induction 1; auto with searchtrees.
 eapply maj_l; eauto with searchtrees.
 simple induction 1; auto with searchtrees.
 auto with searchtrees.
 eapply min_r; eauto with searchtrees.
Defined.

(*  inserting in the right son *)
(* ici *)

Lemma insert_r :
 forall (n p : nat) (t1 t2 t'2 : nat_tree),
 p < n ->
 search (bin p t1 t2) ->
 INSERT n t2 t'2 -> INSERT n (bin p t1 t2) (bin p t1 t'2).
(*******************************************************)
Proof.
 intros n p t1 t2 t'2 H H0 H1; split.
 intros p0 H2; inversion_clear H2; auto with searchtrees.
 elim H1; auto with searchtrees.
 constructor 3; elim H1; auto with searchtrees.
 intros p0 H2; inversion_clear H2; auto with searchtrees.
 elim H1; intros. 
 elim (H5 p0); auto with searchtrees.
 elim H1; constructor 2; auto with searchtrees.
 eapply search_l; eauto with searchtrees.
 split; intros.
 elim (maj_l _ _ _ H0); auto with searchtrees.
 split; intros q H6.
 elim (H4 q H6).
 intro.
 elim (min_r _ _ _ H0); auto with searchtrees.
 simple induction 1; auto with searchtrees.
Defined.


(* no need for insertion  ! *)

Lemma insert_eq :
 forall (n : nat) (t1 t2 : nat_tree),
 search (bin n t1 t2) -> INSERT n (bin n t1 t2) (bin n t1 t2).
(******************************************************)
Proof.
 auto with searchtrees.
Defined.

Hint Resolve insert_l insert_r insert_eq: searchtrees.


(* V.2   The insertion algorithm itself
***************************************)



(* realization *)

Lemma insert : forall (n : nat) (t : nat_tree), search t -> INSERT_SPEC n t.
Proof.
 refine
  (fix insert (n : nat) (t : nat_tree) {struct t} :
     search t -> INSERT_SPEC n t :=
     match t return (search t -> INSERT_SPEC n t) with
     | NIL => fun s => exist _ (bin n NIL NIL) _
     | bin p t1 t2 =>
         fun s =>
         match le_gt_dec n p with
         | left h =>
             match le_lt_eq_dec n p h with
             | left _ =>
                 match insert n t1 _ with
                 | exist t3 _ => exist _ (bin p t3 t2) _
                 end
             | right _ => exist _ (bin n t1 t2) _
             end
         | right _ =>
             match insert n t2 _ with
             | exist t3 _ => exist _ (bin p t1 t3) _
             end
         end
     end).
(*
 Realizer Fix insert{insert/2 : nat-> nat_tree -> nat_tree :=
               [n:nat][t:nat_tree]<nat_tree> 
                Cases t of
                NIL  =>  (bin n NIL NIL )
               |( bin p t1 t2 ) =>
                  <nat_tree> if (le_gt_dec n p)
                            then <nat_tree> if (le_lt_eq_dec n p)
                                           then  (bin p (insert n t1) t2)
                                           else (bin n t1 t2)
                            else (bin p t1 (insert n t2)) end}.
 Program_all.
*)
 auto with searchtrees.
 eapply search_l; eauto with searchtrees.
 auto with searchtrees. 
 rewrite e; auto with searchtrees.
 eapply search_r; eauto with searchtrees.
 auto with searchtrees.

Defined.
Hint Resolve insert: searchtrees.


