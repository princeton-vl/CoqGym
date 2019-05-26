(* File: Regular_Avl.v  (last edited on 27/10/2000) (c) Klaus Weich  *)

(* An AVL tree of lists is called regular iff, for each entry l,   *)
(* we have l\not= nil                                             *)

Require Import List.
Require Import ML_Int.
Require Import AvlTrees.

Section Regular_Avl.

Variable A : Set.

Definition Regular (t : avl_tree (list A)) :=
  forall (k : Int) (d : list A), lookup (list A) k t d -> d = nil -> False.

Remark regular_nil : Regular (Avl_Nil (list A)).
unfold Regular in |- *.
intros k d lookup eq_d.
inversion_clear lookup.
Qed.


Remark regular_equiv_del :
 forall (key : Int) (t t' : avl_tree (list A)),
 Regular t -> equiv_del (list A) key t t' -> Regular t'.
intros key t t' reg_t equiv_del.
unfold Regular in |- *.
intros k d lookup eq_d.
elim (equal_dec k key).
intros eq_k.
inversion_clear equiv_del.
apply H with k d; assumption.
intros not_eq_k.
apply reg_t with k d.
inversion_clear equiv_del.
apply H1; assumption.
assumption.
Qed.



Remark regular_equiv_ins :
 forall (key : Int) (data : A) (t t' : avl_tree (list A)),
 is_avl (list A) t ->
 is_avl (list A) t' ->
 Regular t -> equiv_ins (list A) key (cons data) nil t t' -> Regular t'.
intros key data t t' avl_t avl_t' reg_t equiv_ins.
unfold Regular in |- *.
intros k d lookup eq_d.
elim (equal_dec k key).
intros eq_k.
inversion_clear equiv_ins.
clear H1 H2.
elim (lookup_dec (list A) k t avl_t).
intros d0 lookup0.
cut (d = data :: d0).
 rewrite eq_d.
intro x;  discriminate x.
apply (lookup_avl_equal (list A) k k t').
assumption.
assumption.
apply H; assumption.
apply equal_refl.
intros not_lookup0.
cut (d = data :: nil).
 rewrite eq_d.
intro x;  discriminate x.
apply (lookup_avl_equal (list A) k k t').
assumption.
assumption.
apply H0; assumption.
apply equal_refl.

intros not_equal_k.
apply reg_t with k d.
inversion_clear equiv_ins.
clear H H0.
apply H2; assumption.
assumption.
Qed.


(***********************************************************************)

Definition REGULAR (t : AVL (list A)) :=
  match t with
  | AVL_intro t _ => Regular t
  end.


Lemma regular_AVL_NIL : REGULAR (AVL_NIL (list A)).
simpl in |- *.
exact regular_nil.
Qed.


Lemma regular_EQUIV_DEL :
 forall (key : Int) (T T' : AVL (list A)),
 REGULAR T -> EQUIV_DEL (list A) key T T' -> REGULAR T'.
intros key T T'.
elim T; clear T; intros t avl_t.
elim T'; clear T'; intros t' avl_t'.
simpl in |- *.
intros reg_t equiv_del.
apply regular_equiv_del with key t; assumption.
Qed.


Lemma regular_EQUIV_INS :
 forall (key : Int) (data : A) (T T' : AVL (list A)),
 REGULAR T -> EQUIV_INS (list A) key (cons data) nil T T' -> REGULAR T'.
intros key data T T'.
elim T; clear T; intros t avl_t.
elim T'; clear T'; intros t' avl_t'.
simpl in |- *.
intros reg_t equiv_ins.
apply regular_equiv_ins with key data t; assumption.
Qed.



End Regular_Avl.