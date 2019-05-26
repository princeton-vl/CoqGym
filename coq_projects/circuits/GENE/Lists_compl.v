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
(* date: may 1995                                               *)
(* file: Lists_compl.v                                          *)
(* contents: definitions and lemmas on polymorphic lists,       *)
(* length, append, map, reverse, list_constant                  *)
(* decidability of equality on lists *** TO BE PROVED ***       *)
(****************************************************************)

Require Export List.
Require Export Arith_compl.

Section Lists_compl.
Variable A B : Set.

Lemma length_eq1 : length (nil:list A) = 0.
auto with arith. Qed.
Lemma length_eq2 :
 forall (x : A) (l : list A), length (x :: l) = S (length l).
auto with arith. Qed.

Lemma app_eq1 : forall l' : list A, nil ++ l' = l'. 
auto with arith. Qed.
Lemma app_eq2 : forall (x : A) (l l' : list A), (x :: l) ++ l' = x :: l ++ l'.
auto with arith. Qed.

Inductive len : list A -> nat -> Prop :=
 (************)
  | len_nil : len nil 0
  | len_cons :
      forall (b : A) (v : list A) (l : nat), len v l -> len (b :: v) (S l).
Hint Resolve len_nil len_cons.

Lemma nil_cons : forall (b : A) (v : list A), nil <> b :: v.
(*************)
intros. discriminate.
Qed.

Lemma not_cons_eq : forall (v : list A) (b : A), v <> b :: v.
(****************)
simple induction v. intro. discriminate.
intros. injection. intros. absurd (l = a :: l). apply H.
exact H1.
Qed.

Lemma app_v_nil : forall v : list A, v ++ nil = v.
(**************)
intro.
rewrite <- app_nil_end; trivial with arith.
Qed. Hint Resolve app_v_nil.

Lemma app_v_nil_idem : forall v v' : list A, v = v' -> v ++ nil = v'.
(********************)
intros. inversion H. apply app_v_nil.
Qed.

Lemma app_v_nil_inv : forall v1 v2 : list A, v1 ++ v2 = v1 -> v2 = nil.
(******************)
simple induction v1. simpl in |- *. trivial with arith.
intros. generalize H0. rewrite app_eq2. intros. injection H1. intro. apply H. exact H2.
Qed.

Lemma app_v_nil_sym : forall v1 v2 : list A, v1 = nil -> v1 ++ v2 = v2 ++ v1.
(******************)
simple induction v2. intro. rewrite H. trivial with arith.
intros. rewrite H0. auto with arith.
Qed.

Definition app_assoc_r := app_ass.
(*********************)
Definition app_assoc_l := ass_app.
(*********************)

Lemma len_cons_not_O :
 forall (b : A) (v : list A) (l : nat),
 (*******************)
 len (b :: v) l -> l <> 0.
simple induction v. intros. inversion H. discriminate.
intros. inversion H0. discriminate.
Qed.

Lemma len_nil_inv : forall l : nat, len nil l -> l = 0.
(****************)
intros; inversion H; trivial with arith.
Qed.

Lemma not_len_nil_Sn : forall l : nat, ~ len nil (S l).
(*******************)
simple induction l. red in |- *. intro. inversion H. unfold not in |- *. intros. inversion H0.
Qed.

Lemma len_app :
 forall (l1 l2 : nat) (v1 v2 : list A),
 (************)
 len v1 l1 -> len v2 l2 -> len (v1 ++ v2) (l1 + l2).
simple induction l1. simpl in |- *. intros. inversion H. simpl in |- *. assumption.
intros. inversion H0. simpl in |- *. apply len_cons. apply H. exact H4.
exact H1.
Qed.


Lemma len_length : forall v : list A, len v (length v).
(***************)
simple induction v. auto with arith.
intros. rewrite length_eq2. apply len_cons. exact H.
Qed. Hint Resolve len_length.

Lemma length_eq : forall v1 v2 : list A, v1 = v2 -> length v1 = length v2.
(**************)
intros. rewrite H. trivial with arith.
Qed.

Lemma not_nil : forall v : list A, length v <> 0 -> v <> nil.
(************)
simple induction v. simpl in |- *; intro. absurd (0 <> 0). unfold not in |- *; auto with arith. exact H.
simpl in |- *. intros. discriminate.
Qed.

Lemma length_app :
 forall v1 v2 : list A,
 (***************)
 length (v1 ++ v2) = length v1 + length v2.
simple induction v1. simpl in |- *. trivial with arith.
intros. simpl in |- *. rewrite H. trivial with arith.
Qed.

Lemma v_not_nil_length :
 forall v : list A,
 (*********************)
 v <> nil -> 1 <= length v.
simple induction v. intro. absurd (nil <> nil :>list A). unfold not in |- *. auto with arith.
exact H.
intros. simpl in |- *. apply le_n_S. auto with arith.
Qed.

Lemma le_SO_length_v :
 forall v : list A,
 (*******************)
 length v <> 0 -> 1 <= length v.
intros. apply v_not_nil_length. apply not_nil. exact H.
Qed.

(****************************************************************)
(* Rend une liste de longueur n dont tous les elements sont x *)

Fixpoint list_const (n : nat) : A -> list A :=
  
 (*****************)
 fun x : A =>
 match n return (list A) with
 | O => nil
 | S n' => x :: list_const n' x
 end.

Lemma list_const_eq1 : forall x : A, list_const 0 x = nil.
auto with arith. Qed.
Lemma list_const_eq2 :
 forall (n' : nat) (x : A), list_const (S n') x = x :: list_const n' x.
auto with arith. Qed.

Lemma len_list_const : forall (n : nat) (x : A), len (list_const n x) n.
(*******************)
simple induction n. auto with arith. intros. simpl in |- *. auto with arith.
Qed. Hint Resolve len_list_const.

Lemma length_list_const :
 forall (n : nat) (x : A), length (list_const n x) = n.
(**********************)
simple induction n. auto with arith. intros. simpl in |- *. auto with arith.
Qed. Hint Resolve length_list_const.

(****************************************************************)
(* rev: renverse une liste *)

Fixpoint rev (l : list A) : list A :=
  
 (************************)
 match l return (list A) with
 | nil => nil
 | b :: l' => rev l' ++ b :: nil
 end.

Lemma rev_eq1 : rev nil = nil.
auto with arith. Qed.
Lemma rev_eq2 :
 forall (b : A) (l' : list A), rev (b :: l') = rev l' ++ b :: nil.
auto with arith. Qed.


Lemma rev_eq : forall l n : list A, l = n -> rev l = rev n.
(***********)
intros; replace l with n; auto with arith.
Qed.

Lemma rev_app : forall l n : list A, rev (l ++ n) = rev n ++ rev l.
(************)
simple induction l; auto with arith. intros. simpl in |- *. rewrite H. apply app_assoc_r.
Qed.

Lemma rev_rev : forall l : list A, rev (rev l) = l.
(************)
simple induction l; auto with arith. intros; simpl in |- *. rewrite rev_app. rewrite H. auto with arith.
Qed.

Lemma length_rev : forall l : list A, length (rev l) = length l.
(***************)
simple induction l; auto with arith. intros. simpl in |- *.
rewrite length_app. simpl in |- *. rewrite plus_n_SO. rewrite H. trivial with arith.
Qed.

(****************************************************************)
(* map *)

Fixpoint map (l : list A) : (A -> B) -> list B :=
  
 (************************)
 fun f : A -> B =>
 match l return (list B) with
 | nil => nil
 | b :: l' => f b :: map l' f
 end.


Lemma length_map :
 forall (l : list A) (f : A -> B), length (map l f) = length l.
simple induction l. auto with arith.
intros. simpl in |- *. rewrite H. trivial with arith.
Qed.

(****************************************************************)
(* Decidabilite *)

Lemma eq_cons :
 forall (l1 l2 : list A) (a1 a2 : A), a1 :: l1 = a2 :: l2 -> l1 = l2.
intros.
change (tail (a1 :: l1) = tail (a2 :: l2)) in |- *.
apply (f_equal (A:=list A)).
exact H.
Qed.
Hint Immediate eq_cons.

(*
Lemma eq_cons2 : (l1,l2:(list A))(a1,a2:A)
		(cons a1 l1)=(cons a2 l2) -> a1=a2.
*)

Lemma not_eq_cons :
 forall (l1 l2 : list A) (a1 a2 : A), l1 <> l2 -> a1 :: l1 <> a2 :: l2.
red in |- *. intros. absurd (l1 = l2). exact H.
apply (eq_cons l1 l2 a1 a2). exact H0.
Qed.

Axiom eq_list_dec : forall l m : list A, {l = m} + {l <> m}.

(*
(Induction l;Induction m). Auto with arith.
(Right;Discriminate).(Right;Discriminate). Intros.
*)


End Lists_compl.

