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

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                                                          *)
(*Author: Pierre Casteran.                                                  *)
(*    LABRI, URA CNRS 1304,                                                 *)
(*    Departement d'Informatique, Universite Bordeaux I,                    *)
(*    33405 Talence CEDEX,                                                  *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                                 *)
(*                                                                          *)
(*Date: May, 3, 1993                                                        *)
(*                                                                          *)
(*Pro[gramm,v]ing with continuations:A development in Coq.                  *)
(*                                                                          *)
(*(see the file "leavemult.dvi" for more explanations )                     *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                               leavemult.v                                *)
(****************************************************************************)

Set Asymmetric Patterns.

Require Import Arith.


(* Binary trees on some domain:*)

Section Domain.

Variable Dom : Set.

Inductive tree : Set :=
  | leaf : Dom -> tree
  | cons : tree -> tree -> tree.

End Domain.


(* Binary trees labeled by natural numbers
*)

Definition nat_tree := tree nat.
Definition nat_cons := cons nat.
Definition nat_leaf := leaf nat.


(* Product of all the leaves of some nat_tree 
*)

Fixpoint leavemult (t : nat_tree) : nat :=
  match t return nat with
  | leaf n1 => 
      (* (nat_leaf n1) *)  n1
      (* (nat_cons t1 t2) *) 
  | cons t1 t2 => leavemult t1 * leavemult t2
  end.


(* the specification  of our problem:
*)

Definition SPECIF (t : nat_tree) := {n : nat | n = leavemult t}.


(* A (too much) trivial proof 
*)

Theorem trivialalgo : forall t : nat_tree, SPECIF t.

intro t.
unfold SPECIF in |- *. 
apply exist with (leavemult t); auto.
Defined.


(* Here we  define a predicate "Has an occurrence of O" 
*)

Fixpoint Has_Zero (t : nat_tree) : Prop :=
  match t return Prop with
  | leaf n1 =>
      (* (nat_leaf n1) *) n1 = 0
                          (* (nat_cons t1 t2) *)
  | cons t1 t2 => Has_Zero t1 \/ Has_Zero t2
  end.


(* If some tree t has an occurence of 0, then (leavmult t)=0 
*)

Lemma zero_occ : forall t : nat_tree, Has_Zero t -> leavemult t = 0.

simple induction t.
simple induction d; simpl in |- *; auto. intros t1 H1 t2 H2 H.
simpl in |- *. elim H; intro H0.
cut (leavemult t1 = 0). intro H3. rewrite H3; simpl in |- *; auto. auto.
cut (leavemult t2 = 0). intro H3. rewrite H3; simpl in |- *.
symmetry  in |- *; apply mult_n_O. auto.
Qed.



(* A  proof of (t:nat_tree)(SPECIF t)
   which uses the preceding lemma
*)


Let subtree_ersatz (t' t : nat_tree) := Has_Zero t' -> Has_Zero t.

Let kappa (t t' : nat_tree) := forall n' : nat, n' = leavemult t' -> SPECIF t.

Theorem cpsalgo : forall t : nat_tree, SPECIF t.

intro.
cut (Has_Zero t -> SPECIF t).
intro ESCAPE_O.

(*
2 subgoals
  (SPECIF t)
  ============================
    ESCAPE_O : (Has_Zero t)->(SPECIF t)
    t : nat_tree
subgoal 2 is:
  (Has_Zero t)->(SPECIF t)
*)

2: intro.
2: unfold SPECIF in |- *.
2: apply exist with 0.
2: symmetry  in |- *.
2: apply zero_occ.
2: auto.

(*
1 subgoal
  (SPECIF t)
  ============================
    ESCAPE_O : (Has_Zero t)->(SPECIF t)
    t : nat_tree

*)

Hint Unfold subtree_ersatz.
Hint Unfold kappa.

cut (forall t' : nat_tree, subtree_ersatz t' t -> kappa t t' -> SPECIF t).
Hint Unfold SPECIF.

intro AUX.
apply AUX with t.
auto.
unfold kappa in |- *.
intros n H.
unfold SPECIF in |- *; apply exist with n; auto.

(*
1 subgoal
  (t':nat_tree)(subtree_ersatz t' t)->(kappa t t')->(SPECIF t)
  ============================
    ESCAPE_O : (Has_Zero t)->(SPECIF t)
    t : nat_tree

*)

simple induction t'.
simple induction d.
intros H H0.
apply ESCAPE_O.
apply H. simpl in |- *.
auto.
intros y H1 H2 H3.
unfold kappa in H3.
apply H3 with (S y).
simpl in |- *.
auto.

intro t1. intro ind1. intro t2. intro ind2. intros H H0.
apply ind2.
intro H1.
apply H.
unfold Has_Zero in |- *.
unfold Has_Zero in H1. auto.
(*

1 subgoal
  (kappa t t2)
  ============================
    H0 : (kappa t (cons nat t1 t2))
    H : (subtree_ersatz (cons nat t1 t2) t)
    ind2 : (subtree_ersatz t2 t)->(kappa t t2)->(SPECIF t)
    t2 : (tree nat)
    ind1 : (subtree_ersatz t1 t)->(kappa t t1)->(SPECIF t)
    t1 : (tree nat)
    t' : nat_tree
    ESCAPE_O : (Has_Zero t)->(SPECIF t)
    t : nat_tree



*)


unfold kappa in |- *.
unfold kappa in H0.
intros n2 eg2.

(*

1 subgoal
  (SPECIF t)
  ============================
    eg2 : <nat>n2=(leavemult t2)
    n2 : nat
    H0 : (n':nat)(<nat>n'=(leavemult (cons nat t1 t2)))->(SPECIF t)
    H : (subtree_ersatz (cons nat t1 t2) t)
    ind2 : (subtree_ersatz t2 t)->(kappa t t2)->(SPECIF t)
    t2 : (tree nat)
    ind1 : (subtree_ersatz t1 t)->(kappa t t1)->(SPECIF t)
    t1 : (tree nat)
    t' : nat_tree
    ESCAPE_O : (Has_Zero t)->(SPECIF t)
    t : nat_tree


*)


apply ind1.
intro.
apply H.
simpl in |- *; auto.
unfold kappa in |- *.
intros n1 eg1.
apply H0 with (n1 * n2).
simpl in |- *.
rewrite eg2; rewrite eg1.
auto.

Defined.


(* Old extraction

Coq < Extraction cpsalgo.
cpsalgo ==> [t:nat_tree]
             (tree_rec nat kappa->SPECIF
               [d:nat]
                (nat_rec kappa->SPECIF [_:kappa] O
                  [y:nat][_:kappa->SPECIF] ([H3:kappa](H3 (S y))) d)
               [_:(tree nat)]
                ([ind1:kappa->SPECIF]
                  [_:(tree nat)]
                   ([ind2:kappa->SPECIF]
                     [H0:kappa]
                      (ind2 [n2:nat](ind1 [n1:nat](H0 (mult n1 n2))))))
               t [n:nat]n)

Coq < Extraction SPECIF.
SPECIF ==> nat

Coq < Extraction kappa.
kappa ==> nat->SPECIF

*)

Require Extraction.
Extraction "leavemult.ml" SPECIF kappa trivialalgo cpsalgo.
