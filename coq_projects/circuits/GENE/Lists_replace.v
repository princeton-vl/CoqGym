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

(****************************************************************)
(*           The Calculus of Inductive Constructions            *)
(*                       COQ v5.10                              *)
(*                                                              *)
(* Laurent Arditi.  Laboratoire I3S. CNRS ura 1376.             *)
(* Universite de Nice - Sophia Antipolis                        *)
(* arditi@unice.fr, http://wwwi3s.unice.fr/~arditi/lolo.html    *)
(*                                                              *)
(* date: june 1995                                              *)
(* file: Lists_replace                                          *)
(* contents: definition of replace for polymorphic lists        *)
(*                                                              *)
(****************************************************************)

Require Export Lists_field.

Section Lists_replace.
Variable A : Set.

(* Remplace l'element de l a la position par new *)
Fixpoint replace (l : list A) : nat -> A -> list A :=
  fun (position : nat) (new : A) =>
  match l return (list A) with
  | nil =>
      (* nil *)  nil
  | x :: l' =>
      (* (cons x l') *)
      match position return (list A) with
      | O =>
          (* O *)  new :: l'
          (* (S n') *)
      | S n' => x :: replace l' n' new
      end
  end.

Lemma replace_ok :
 forall (l : list A) (i : nat) (x : A),
 (***************)
 i < length l -> elemlist A (replace l i x) i = x :: nil.
simple induction l. simpl in |- *. intros. absurd (i < 0). apply lt_n_O.
exact H.
simple induction i. intros. simpl in |- *.
unfold elemlist in |- *. rewrite strip_O. simpl in |- *. rewrite trunc_O; trivial with arith.
intros. simpl in |- *. clear H0. unfold elemlist in |- *. rewrite strip_cons_S.
rewrite elemlist_inv.
apply H. apply lt_S_n. generalize H1. simpl in |- *. trivial with arith.
Qed.

(* On montre que tous les elements, sauf celui que l'on remplace,
   ne sont pas modifies: *)
Lemma replace_keep_others :
 forall (l : list A) (i p : nat) (x : A),
 (************************)
 i < length l ->
 p < length l -> i <> p -> elemlist A (replace l p x) i = elemlist A l i.
simple induction l. simpl in |- *. intros. absurd (i < 0). apply lt_n_O.
exact H.
simple induction i.
intros. unfold elemlist in |- *. rewrite elemlist_inv. rewrite elemlist_inv.
generalize H1 H2. elim p. intros. absurd (0 <> 0). unfold not in |- *; auto with arith.
exact H4.
intros. simpl in |- *. rewrite elemlist_cons_O. rewrite elemlist_cons_O. trivial with arith.
simple induction p. intros. simpl in |- *.
rewrite elemlist_cons_S. rewrite elemlist_cons_S. trivial with arith.
intros. clear H1. simpl in |- *. do 2 rewrite elemlist_cons_S.
clear H0. apply H. apply lt_S_n. generalize H2; simpl in |- *; trivial with arith.
apply lt_S_n. generalize H3; simpl in |- *; trivial with arith.
generalize H4. red in |- *. auto with arith.
Qed.

Lemma length_replace :
 forall (l : list A) (p : nat) (x : A),
 (*******************)
 p < length l -> length (replace l p x) = length l.
simple induction l. simpl in |- *. try trivial with arith.
simple induction p. intros. simpl in |- *. apply eq_S. try trivial with arith.
intros. clear H0. simpl in |- *. rewrite H. try trivial with arith.
auto with arith.
Qed.

Lemma replace_sym :
 forall (l : list A) (p p' : nat) (x x' : A),
 (****************)
 p < length l ->
 p' < length l ->
 p <> p' -> replace (replace l p' x') p x = replace (replace l p x) p' x'.
simple induction l. simpl in |- *. trivial with arith.
simple induction p. intros. generalize H1 H2.
elim p'. intros. absurd (0 <> 0); unfold not in |- *; auto with arith.
intros. simpl in |- *. trivial with arith.
simple induction p'. intros. simpl in |- *. trivial with arith.
intros. clear H1. clear H0. simpl in |- *. rewrite H. trivial with arith.
auto with arith.
auto with arith.
red in |- *. auto with arith.
Qed.

Lemma replace_newer :
 forall (l : list A) (p : nat) (x x' : A),
 (*****************)
 p < length l -> replace (replace l p x) p x' = replace l p x'.
simple induction l. simpl in |- *. trivial with arith.
simple induction p. simpl in |- *. intros. trivial with arith.
intros. clear H0. simpl in |- *. rewrite H. trivial with arith.
auto with arith.
Qed.

End Lists_replace.