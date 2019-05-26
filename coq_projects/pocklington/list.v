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


(**
   list.
   Polymorphic lists with some operations.
 
   @author Olga Caprotti and Martijn Oostdijk
   @version $Revision$
*)

Require Import Arith.
Require Import ZArith.
Require Import EqNat.

Require Import dec.
Require Import natZ.

(** * Polymorphic lists *)

Inductive list (A : Set) : Set :=
  | Nil : list A
  | Cons : A -> list A -> list A.

(** Length of a list *)

Fixpoint length (A : Set) (l : list A) {struct l} : nat :=
  match l with
  | Nil => 0
  | Cons a r => S (length A r)
  end.

Lemma length_0 : forall (A : Set) (l : list A), length A l = 0 -> l = Nil A.
Proof.
   intros A l. case l.
   reflexivity.
   simpl in |- *. intros. discriminate H.
Qed.

Lemma length_S :
 forall (A : Set) (l : list A) (n : nat),
 length A l = S n ->
 exists h : A, (exists t : list A, l = Cons A h t /\ length A t = n).
Proof.
   intros A l. case l.
   simpl in |- *. intros. discriminate H.
   simpl in |- *. intros h0 t0 n H. injection H. intro. 
   split with h0. split with t0. split.
   reflexivity. assumption.
Qed.

(** Map a function over a list *)

Fixpoint map (A B : Set) (f : A -> B) (l : list A) {struct l} : 
 list B :=
  match l with
  | Nil => Nil B
  | Cons a r => Cons B (f a) (map A B f r)
  end.

Notation Map := (map _ _) (only parsing).

Lemma map_length :
 forall (A B : Set) (f : A -> B) (l : list A),
 length A l = length B (map A B f l).
Proof.
   simple induction l.
   simpl in |- *. reflexivity.
   simpl in |- *. intros. rewrite H. reflexivity.
Qed.

(** Checks that all members of a list are P *)

Fixpoint alllist (A : Set) (P : A -> Prop) (qlist : list A) {struct qlist} :
 Prop :=
  match qlist with
  | Nil => True
  | Cons m l => P m /\ alllist A P l
  end.

Lemma alllist_dec :
 forall (A : Set) (P : A -> Prop) (l : list A),
 (forall x : A, P x \/ ~ P x) -> alllist A P l \/ ~ alllist A P l.
Proof.
   simple induction l.
   simpl in |- *. left. trivial.
   intros h t IH H. simpl in |- *.
   elim IH. elim (H h).
   left. split. assumption. assumption.
   right. intro. apply H0. elim H2. intros. assumption.
   right. intro. apply H0. elim H1. intros. assumption.
   assumption.
Qed.

(** Checks that some member of a list is P *)

Fixpoint exlist (A : Set) (P : A -> Prop) (qlist : list A) {struct qlist} :
 Prop :=
  match qlist with
  | Nil => False
  | Cons m l => P m \/ exlist A P l
  end.

Lemma exlist_dec :
 forall (A : Set) (P : A -> Prop) (l : list A),
 (forall x : A, P x \/ ~ P x) -> exlist A P l \/ ~ exlist A P l.
Proof.
   simple induction l.
   simpl in |- *. right. intro. assumption.
   intros h t IH H. simpl in |- *.
   elim (H h).
   left. left. assumption.
   elim IH.
   left. right. assumption.
   right. intro. elim H2.
   assumption. assumption.
   assumption.
Qed.

(** Membership *)

Definition inlist (A : Set) (a : A) := exlist A (fun b : A => a = b).

Lemma inlist_head_eq :
 forall (A : Set) (x y : A) (l : list A), x = y -> inlist A x (Cons A y l).
Proof.
   intros. unfold inlist in |- *. simpl in |- *.
   left. assumption.
Qed.

Lemma inlist_head_neq :
 forall (A : Set) (x y : A) (l : list A),
 x <> y -> (inlist A x (Cons A y l) <-> inlist A x l).
Proof.
   intros. unfold inlist in |- *. simpl in |- *.
   split.
   intros. elim H0. intro. elim H. assumption.
   intros. assumption.
   intros. right. assumption.
Qed.

Lemma inlist_tail :
 forall (A : Set) (x y : A) (l : list A),
 inlist A x l -> inlist A x (Cons A y l).
Proof.
   intros. unfold inlist in |- *. simpl in |- *. right. assumption.
Qed.

Lemma inlist_dec :
 forall (A : Set) (x : A) (l : list A),
 (forall a b : A, a = b \/ a <> b) -> inlist A x l \/ ~ inlist A x l.
Proof.
   intros. unfold inlist in |- *.
   apply exlist_dec. exact (H x).
Qed.

(** alllist and exlist behave nicely *)

Theorem alllist_ok :
 forall (A : Set) (P : A -> Prop) (qlist : list A),
 alllist A P qlist <-> (forall q : A, inlist A q qlist -> P q).
Proof.
   split.

   (* -> *)
   elim qlist.
   unfold inlist in |- *. simpl in |- *. intros. elim H0.
   unfold inlist in |- *. simpl in |- *. intros q l IH H. elim H. intros. elim H2.
   intro. rewrite H3. assumption.  
   intro. apply IH. assumption. assumption.

   (* <- *)
   elim qlist.
   unfold inlist in |- *. simpl in |- *. intros. trivial.
   unfold inlist in |- *. simpl in |- *. intros q l IH H. split.
   apply H. left. reflexivity.
   apply IH. intros. apply H. right. assumption.
Qed.

Theorem exlist_ok :
 forall (A : Set) (P : A -> Prop) (qlist : list A),
 exlist A P qlist <-> (exists q : A, inlist A q qlist /\ P q).
Proof.
   split.

   (* -> *)
   elim qlist.
   unfold inlist in |- *. simpl in |- *. intros. elim H.
   unfold inlist in |- *. simpl in |- *. intros q l IH H. elim H.
   intro. split with q. split. left. reflexivity. assumption.
   intro. elim IH. intros q1 Hq1. elim Hq1. intros. split with q1.
   split. right. assumption. assumption. assumption.

   (* <- *)
   elim qlist.
   unfold inlist in |- *. simpl in |- *. intros. elim H. intros. elim H0. intros. elim H1.
   unfold inlist in |- *. simpl in |- *. intros q l IH H. elim H.
   intros q1 Hq1. elim Hq1. intros. elim H0.
   intro. left. rewrite <- H2. assumption.
   intro. right. apply IH. split with q1. split. assumption. assumption.
Qed.

(** * Lists of natural numbers. *)

Definition natlist := list nat.

(** Multiply all elements of a natlist *)

Fixpoint product (qlist : natlist) : nat :=
  match qlist with
  | Nil => 1
  | Cons m l => m * product l
  end.

(** Drop the first occurance of q from qlist *)

Fixpoint drop (q : nat) (qlist : natlist) {struct qlist} : natlist :=
  match qlist with
  | Nil => Nil nat
  | Cons q' l => if beq_nat q q' then l else Cons nat q' (drop q l)
  end.

(** Multiply all elements of qlist, except for (first occurance of) q *)

Definition multDrop (q : nat) (l : natlist) := product (drop q l).

Lemma multdrop_cons_eq :
 forall (q : nat) (l : natlist), multDrop q (Cons nat q l) = product l.
Proof.
   unfold multDrop in |- *. simpl in |- *. intros. elim (beq_nat_eq q q). intros.
   rewrite H. reflexivity. reflexivity.
Qed.

Lemma multdrop_cons_neq :
 forall (p q : nat) (l : natlist),
 p <> q -> multDrop p (Cons nat q l) = q * multDrop p l.
Proof.
   unfold multDrop in |- *. simpl in |- *. intros. elim (beq_nat_neq p q). intros.
   rewrite H0. simpl in |- *. reflexivity. assumption.
Qed.

Lemma multdrop_mult :
 forall (qlist : natlist) (q : nat),
 inlist nat q qlist -> q * multDrop q qlist = product qlist.
Proof.
   simple induction qlist.
   simpl in |- *. intros. elim H.
   simpl in |- *. intros q1 l IH. intros. elim (eqdec q q1).

   (* case q=q1 *)
   intro. rewrite H0. rewrite multdrop_cons_eq. reflexivity.

   (* case ~q=q1 *)
   intro. rewrite multdrop_cons_neq.
   rewrite <- (IH q). rewrite mult_assoc.
   rewrite (mult_comm q q1). rewrite mult_assoc. reflexivity.
   unfold inlist in H. simpl in H. elim H.
   intro. elim H0. assumption.  
   intro. assumption.
   assumption.
Qed.

(** * Lists of integers. *)

Definition Zlist := list Z.

(** allPos checks whether all members of a Zlist are non-negative. *)

Definition allPos : Zlist -> Prop := alllist Z (fun x : Z => (x >= 0)%Z).

(** Multiply all elements of a Zlist *)

Fixpoint zproduct (l : Zlist) : Z :=
  match l with
  | Nil => 1%Z
  | Cons x t => (x * zproduct t)%Z
  end.

Lemma productzproduct :
 forall l : natlist, Z_of_nat (product l) = zproduct (map nat Z Z_of_nat l).
Proof.
   simple induction l.
   simpl in |- *. reflexivity.
   intros h t IH.
   simpl in |- *. rewrite <- IH.
   rewrite Znat.inj_mult.
   reflexivity.
Qed.

Lemma zproductproduct :
 forall l : Zlist, Zabs_nat (zproduct l) = product (map Z nat Zabs_nat l).
Proof.
   simple induction l.
   simpl in |- *. reflexivity.
   intros h t IH.
   simpl in |- *. rewrite abs_mult.
   rewrite IH. reflexivity.
Qed.

(** Drop an element from a Zlist *)

Fixpoint zdrop (x : Z) (l : Zlist) {struct l} : Zlist :=
  match l with
  | Nil => Nil Z
  | Cons h t => if Zeq_bool x h then t else Cons Z h (zdrop x t)
  end.

Lemma zdrop_head_eq :
 forall (x y : Z) (l : Zlist), x = y -> zdrop x (Cons Z y l) = l.
Proof.
   simpl in |- *. intros. elim (zeq_bool_eq x y). intros.
   rewrite H0. reflexivity. assumption.
Qed.

Lemma zdrop_head_neq :
 forall (x y : Z) (l : Zlist),
 x <> y -> zdrop x (Cons Z y l) = Cons Z y (zdrop x l).
Proof.
   simpl in |- *. intros. elim (zeq_bool_neq x y). intros.
   rewrite H0. reflexivity. assumption.
Qed.

Lemma zdrop_length :
 forall (x : Z) (l : Zlist),
 inlist Z x l -> S (length Z (zdrop x l)) = length Z l.
Proof.
   simple induction l.
   unfold inlist in |- *. simpl in |- *. intros. elim H.
   intros h t IH. intros. elim (zeqdec x h).

   (* case x=h *)
   intro. simpl in |- *. elim (zeq_bool_eq x h).
   intros. rewrite H1. reflexivity. assumption.

   (* case x<>h *)
   intro. simpl in |- *. elim (zeq_bool_neq x h).
   intros. rewrite H1. simpl in |- *. rewrite IH. reflexivity.
   elim H. intros. elim H0. assumption. intros. assumption. assumption.
Qed.

Lemma zdrop_neq_inlist :
 forall (x y : Z) (l : Zlist),
 x <> y -> inlist Z x l -> inlist Z x (zdrop y l).
Proof.
   simple induction l.
   intros. elim H0.
   intros h t IH.
   intros. elim (zeqdec x h).
   intro. rewrite zdrop_head_neq.
   apply inlist_head_eq. assumption.
   rewrite <- H1. intro. apply H. symmetry  in |- *. assumption.
   intro. elim (zeqdec y h).
   intro. rewrite zdrop_head_eq.
   elim (inlist_head_neq Z x h t).
   intros. apply H3. assumption.
   assumption. assumption.
   intro. rewrite zdrop_head_neq.
   elim (inlist_head_neq Z x h (zdrop y t)). intros.
   apply H4. apply IH. assumption.
   elim (inlist_head_neq Z x h t). intros.
   apply H5. assumption.
   assumption. assumption. assumption.
Qed.

Lemma zdrop_inlist_weak :
 forall (x y : Z) (l : Zlist), inlist Z x (zdrop y l) -> inlist Z x l.
Proof.
   simple induction l.
   unfold inlist in |- *. simpl in |- *. intro. assumption.
   intros h t IH. intros.
   elim (zeqdec x h).
   intro. rewrite H0. unfold inlist in |- *. simpl in |- *. left. reflexivity.
   intro. elim (zeqdec y h).
   intro. rewrite H1 in H. rewrite zdrop_head_eq in H.
   apply inlist_tail. assumption. reflexivity.
   intro. rewrite zdrop_head_neq in H.
   unfold inlist in H. simpl in H. elim H.
   intro. elim H0. assumption.
   intros. apply inlist_tail. apply IH. assumption.
   assumption.
Qed.

Lemma zdrop_swap :
 forall (x y : Z) (l : Zlist), zdrop x (zdrop y l) = zdrop y (zdrop x l).
Proof.
   simple induction l.
   simpl in |- *. reflexivity.
   intros h t IH.
   elim (zeqdec x h). elim (zeqdec y h).

   (* y=h, x=h *)
   intros. rewrite H. rewrite H0. reflexivity.

   (* y<>h, x=h *)
   intros.
   rewrite (zdrop_head_eq x h t).
   rewrite (zdrop_head_neq y h t).
   rewrite zdrop_head_eq. reflexivity.
   assumption. assumption. assumption.

   elim (zeqdec y h).

   (* y=h, x<>h *)
   intros.
   rewrite (zdrop_head_eq y h).
   rewrite (zdrop_head_neq x h).
   rewrite zdrop_head_eq. reflexivity.
   assumption. assumption. assumption.

   (* y<>h, x<>h *)
   intros.
   rewrite (zdrop_head_neq y h).
   rewrite (zdrop_head_neq x h).
   rewrite (zdrop_head_neq x h).
   rewrite (zdrop_head_neq y h).
   rewrite IH. reflexivity.
   assumption. assumption.
   assumption. assumption.
Qed.

Lemma zdrop_inlist_swap :
 forall (x y : Z) (l : Zlist),
 inlist Z y l -> inlist Z x (zdrop y l) -> inlist Z y (zdrop x l).
Proof.
   simple induction l.
   simpl in |- *. intro H. elim H.
   intros h t IH.
   elim (zeqdec x h). elim (zeqdec y h).

   (* y=h,x=h *)
   intros Hyh Hxh. rewrite Hyh. rewrite Hxh.
   intros. assumption.

   (* y<>h,x=h *)
   intros Hyh Hxh.
   rewrite (zdrop_head_neq y).
   rewrite (zdrop_head_eq x).
   intros. elim (inlist_head_neq Z y h t).
   intros. apply H1. assumption.
   assumption. assumption. assumption.

   elim (zeqdec y h).

   (* y=h,x<>h *)
   intros Hyh Hxh.
   rewrite (zdrop_head_eq y).
   rewrite (zdrop_head_neq x).
   intros. apply inlist_head_eq. assumption.
   assumption. assumption.

   (* y<>h, x<>h *)
   intros Hyh Hxh.
   rewrite (zdrop_head_neq y).
   rewrite (zdrop_head_neq x).
   intros. elim (inlist_head_neq Z y h (zdrop x t)).
   intros. apply H2. apply IH.
   elim (inlist_head_neq Z y h t). intros.
   apply H3. assumption. assumption.
   elim (inlist_head_neq Z x h (zdrop y t)). intros.
   apply H3. assumption.
   assumption. assumption. assumption. assumption.
Qed.

Lemma zdrop_product :
 forall (x : Z) (l : Zlist),
 inlist Z x l -> (x * zproduct (zdrop x l))%Z = zproduct l.
Proof.
   simple induction l.
   simpl in |- *. intro. elim H.
   intros h t IH. elim (zeqdec x h).
   intros. rewrite zdrop_head_eq.
   rewrite H. reflexivity. assumption.
   intros. rewrite zdrop_head_neq.
   simpl in |- *. rewrite Zmult_assoc.
   rewrite Zmult_comm with x h.
   rewrite Zmult_assoc_reverse.
   rewrite IH. reflexivity.
   elim inlist_head_neq with Z x h t. intros.
   apply H1. assumption.
   assumption. assumption.
Qed.

(** Multiply all elements except first occurance of x *)

Definition zmultDrop (x : Z) (l : Zlist) := zproduct (zdrop x l).

Lemma zmultdrop_cons_eq :
 forall (q : Z) (l : Zlist), zmultDrop q (Cons Z q l) = zproduct l.
Proof.
   unfold zmultDrop in |- *. simpl in |- *. intros. elim (zeq_bool_eq q q). intros.
   rewrite H. reflexivity. reflexivity.
Qed.

Lemma zmultdrop_cons_neq :
 forall (p q : Z) (l : Zlist),
 p <> q -> zmultDrop p (Cons Z q l) = (q * zmultDrop p l)%Z.
Proof.
   unfold zmultDrop in |- *. simpl in |- *. intros. elim (zeq_bool_neq p q). intros.
   rewrite H0. simpl in |- *. reflexivity. assumption.
Qed.

Lemma zmultdrop_mult :
 forall (qlist : Zlist) (q : Z),
 inlist Z q qlist -> (q * zmultDrop q qlist)%Z = zproduct qlist.
Proof.
   simple induction qlist.
   simpl in |- *. intros. elim H.
   simpl in |- *. intros q1 l IH. intros. elim (zeqdec q q1).

   (* case q=q1 *)
   intro. rewrite H0. rewrite zmultdrop_cons_eq. reflexivity.

   (* case ~q=q1 *)
   intro. rewrite zmultdrop_cons_neq.
   rewrite <- (IH q). rewrite Zmult_assoc.
   rewrite (Zmult_comm q q1). rewrite Zmult_assoc. reflexivity.
   unfold inlist in H. simpl in H. elim H.
   intro. elim H0. assumption.
   intro. assumption.
   assumption.
Qed.

Lemma multdropzmultdrop :
 forall (q : nat) (qlist : natlist),
 Z_of_nat (multDrop q qlist) =
 zmultDrop (Z_of_nat q) (map nat Z Z_of_nat qlist).
Proof.
   simple induction qlist.
   simpl in |- *. reflexivity. 
   intros h t.
   elim (eqdec q h).

   (* q=h *)
   intro H. rewrite H. simpl in |- *.
   rewrite multdrop_cons_eq.
   rewrite zmultdrop_cons_eq.
   rewrite productzproduct.
   intro IH. reflexivity.

   (* ~q=h *)
   intro H. simpl in |- *.
   rewrite multdrop_cons_neq.
   rewrite zmultdrop_cons_neq.
   intro IH. rewrite <- IH.
   rewrite Znat.inj_mult. reflexivity.
   intro. apply H.
   rewrite <- (abs_inj q). rewrite <- (abs_inj h).
   rewrite H0. reflexivity.
   assumption.
Qed.

(** Multiply all elements in list with a *)

Definition mapmult (a : Z) (l : Zlist) := map Z Z (fun x : Z => (a * x)%Z) l.

Lemma mapmult_image :
 forall (a : Z) (l : Zlist) (x : Z),
 inlist Z x l -> inlist Z (a * x)%Z (mapmult a l).
Proof.
   unfold mapmult in |- *. unfold inlist in |- *. simple induction l.
   simpl in |- *. intros. assumption.
   simpl in |- *. intros h t IH. intros. elim H.
   left. rewrite H0. reflexivity.
   right. apply IH. assumption.
Qed.

Lemma mapmult_orig :
 forall (a : Z) (l : Zlist) (y : Z),
 inlist Z y (mapmult a l) -> exists x : Z, inlist Z x l /\ y = (a * x)%Z.
Proof.
   unfold mapmult in |- *. unfold inlist in |- *. simple induction l.
   simpl in |- *. intros. elim H.
   simpl in |- *. intros h t IH. intros.
   elim H.
   intro. split with h. split. left. reflexivity. assumption.
   intro. elim (IH y). intros. elim H1. intros.
   split with x. split. right.
   assumption. assumption. assumption.
Qed.

(** Lift inject_nat and absolu to natlist and Zlist. *)

Lemma abs_inj_list :
 forall l : natlist, map _ _ Zabs_nat (map _ _ Z_of_nat l) = l.
Proof.
   simple induction l.
   simpl in |- *. reflexivity.
   simpl in |- *. intros h t IH.
   rewrite abs_inj. rewrite IH. reflexivity.
Qed.

Lemma inj_abs_pos_list :
 forall l : Zlist, allPos l -> map _ _ Z_of_nat (map _ _ Zabs_nat l) = l.
Proof.
   simple induction l.
   simpl in |- *. intros. reflexivity.
   simpl in |- *. intros h t IH H. elim H. intros.
   rewrite inj_abs_pos. rewrite IH. reflexivity.
   assumption. assumption.
Qed.

Lemma inlist_inj_abs_pos_list :
 forall (q : nat) (l : Zlist),
 allPos l -> inlist nat q (map Z nat Zabs_nat l) -> inlist Z (Z_of_nat q) l.
Proof.
   simple induction l.
   unfold inlist in |- *. simpl in |- *. intros. assumption.
   unfold inlist in |- *. unfold allPos in |- *. simpl in |- *.
   intros h t IH Hp H. elim Hp. elim H.
   left. rewrite H0. rewrite inj_abs_pos. reflexivity.
   intros. assumption.
   right. apply IH. assumption. assumption.
Qed.
