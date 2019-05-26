(* File: Trees.v  (last edited on 25/10/2000) (c) Klaus Weich  *)

Require Export My_Arith.
Require Import Le.


(******   Tree stuff  ********************************************)

Section Trees.


Variable A : Set.


Inductive Tree : Set :=
    node : A -> Forest -> Tree
with Forest : Set :=
  | Nil_Forest : Forest
  | Cons_Forest : Tree -> Forest -> Forest.


Fixpoint height_tree (t : Tree) : nat :=
  match t with
  | node a succs => S (height_forest succs)
  end
 
 with height_forest (succs : Forest) : nat :=
  match succs with
  | Nil_Forest => 0
  | Cons_Forest t0 succs => max (height_tree t0) (height_forest succs)
  end.


(*
Inductive Tree : Set :=
| node : A -> (list Tree) -> Tree.

Fixpoint height_tree [t:Tree] : nat :=
  Cases t of
  | (node a succs) => (S (height_forest succs))
  end
with height_forest[succs:(list Tree)] : nat :=
  Cases succs of
  | nil => O
  | (cons t0 succs) => (max (height_tree t0) (height_forest succs))
  end.
Does not work!!
*)


Definition root (t : Tree) := match t with
                              | node a _ => a
                              end.
Definition successors (t : Tree) := match t with
                                    | node _ succs => succs
                                    end.


Inductive In_Forest (t0 : Tree) : Forest -> Prop :=
  | in_forest_head :
      forall succs : Forest, In_Forest t0 (Cons_Forest t0 succs)
  | in_forest_tail :
      forall (t1 : Tree) (succs : Forest),
      In_Forest t0 succs -> In_Forest t0 (Cons_Forest t1 succs).


Lemma height_in_le :
 forall (t : Tree) (succs : Forest),
 In_Forest t succs -> height_tree t <= height_forest succs.                    
intros t succs in_t.
elim in_t; clear in_t succs.

intros succs.
simpl in |- *.
apply le_n_max1.

intros t1 succs in_t le_t.
apply le_trans with (height_forest succs).
assumption.
simpl in |- *.
apply le_n_max2.
Qed.


Lemma My_Tree_ind :
 forall P : Tree -> Prop,
 (forall (a : A) (succs : Forest),
  (forall t : Tree, In_Forest t succs -> P t) -> P (node a succs)) ->
 forall t : Tree, P t.
intros P step.
cut (forall (n : nat) (t : Tree), height_tree t <= n -> P t).
intro claim.
intro t.
apply claim with (height_tree t).
trivial.
intros n; elim n; clear n.

intros t; elim t; clear t.
intros a succs u0.
elimtype False.
inversion_clear u0.

intros n ih t.
elim t; clear t.
intros a succs u0.
apply step; clear step.
intros t in_t.
apply ih; clear ih P.
apply le_S_n.
apply le_trans with (S (height_forest succs)).
apply le_n_S.
apply height_in_le; assumption.
assumption.
Qed.


Lemma My_Tree_rec :
 forall P : Tree -> Set,
 (forall (a : A) (succs : Forest),
  (forall t : Tree, In_Forest t succs -> P t) -> P (node a succs)) ->
 forall t : Tree, P t.
intros P step.
cut (forall (n : nat) (t : Tree), height_tree t <= n -> P t).
intro claim.
intro t.
apply claim with (height_tree t).
trivial.
intros n; elim n; clear n.

intros t; elim t; clear t.
intros a succs u0.
elimtype False.
inversion_clear u0.

intros n ih t.
elim t; clear t.
intros a succs u0.
apply step; clear step.
intros t in_t.
apply ih; clear ih P.
apply le_S_n.
apply le_trans with (S (height_forest succs)).
apply le_n_S.
apply height_in_le; assumption.
assumption.
Qed.


(* Successor relation  *)

Inductive Successor : Tree -> Tree -> Prop :=
  | successor_refl : forall t : Tree, Successor t t
  | successor_trans :
      forall t0 t1 : Tree,
      In_Forest t1 (successors t0) ->
      forall t2 : Tree, Successor t2 t1 -> Successor t2 t0.


Lemma succs_trans :
 forall t1 t2 : Tree,
 Successor t2 t1 -> forall t0 : Tree, Successor t1 t0 -> Successor t2 t0.
intros t1 t2 u0 t0 u1.
generalize u0; clear u0.
elim u1; clear u1 t0 t1.
trivial.

intros t0 t1 in_t1 t3 suc_t3_t1 ih suc_t2_t3.
apply (successor_trans t0 t1 in_t1 t2).
apply ih; assumption.
Qed.


Lemma succs_refl : forall t : Tree, Successor t t.
intros.
apply successor_refl.
Qed.



Lemma Succs_Tree_ind :
 forall P : Tree -> Prop,
 (forall a : A, P (node a Nil_Forest)) ->
 (forall t0 t1 : Tree, Successor t0 t1 -> P t0 -> P t1) ->
 forall t : Tree, P t.
intros P leaf step t.
apply My_Tree_ind.
intros a succs; case succs; clear succs. 
intros.
apply leaf.
intros t0 succs ih.
apply step with t0.
apply successor_trans with t0.
simpl in |- *.
apply in_forest_head.
apply successor_refl.
apply ih.
apply in_forest_head.
Qed.


(* In_tree *)
(* ------- *)

Inductive In_tree : A -> Tree -> Prop :=
  | in_leave : forall (a : A) (succs : Forest), In_tree a (node a succs)
  | in_succs :
      forall (succs : Forest) (t : Tree),
      In_Forest t succs ->
      forall a : A, In_tree a t -> forall a' : A, In_tree a (node a' succs).


Lemma in_successor_in :
 forall (a : A) (t : Tree),
 In_tree a t -> forall t' : Tree, Successor t t' -> In_tree a t'.
intros a t in_t t' suc.
generalize in_t; clear in_t.
elim suc; clear suc.
trivial.
clear t t'.
intros t0 t1 in_t1 t2 suc_t2 ih in_t2.
generalize in_t1; clear in_t1.
elim t0; clear t0.
intros a' succs in_t1.
apply in_succs with (t := t1).
assumption.
apply ih.
assumption.
Qed.

(********************************************************************)
(*  Monotone Trees                                                  *)

Variable I : Set.
Variable P : A -> I -> Prop.

Inductive Is_Monotone_Tree : Tree -> Prop :=
    is_monotone_tree_intro :
      forall (a : A) (succs : Forest),
      Is_Monotone_Forest a succs -> Is_Monotone_Tree (node a succs)
with Is_Monotone_Forest : A -> Forest -> Prop :=
  | is_monotone_forest_nil : forall a : A, Is_Monotone_Forest a Nil_Forest
  | is_monotone_forest_cons :
      forall (a : A) (t : Tree) (succs : Forest),
      (forall i : I, P a i -> P (root t) i) ->
      Is_Monotone_Tree t ->
      Is_Monotone_Forest a succs ->
      Is_Monotone_Forest a (Cons_Forest t succs).




Lemma is_monotone_tree_successor :
 forall t : Tree,
 Is_Monotone_Tree t ->
 forall t0 : Tree, Successor t0 t -> Is_Monotone_Tree t0.
intros t is_mon_t t0 suc_t0.
generalize is_mon_t; clear is_mon_t.
elim suc_t0; clear suc_t0 t0.
trivial.
intros t0 t1 in_t1 t2 suc_t2 ih is_mon_t0.
apply ih; clear ih suc_t2 t2.
generalize in_t1; clear in_t1.
inversion_clear is_mon_t0.
simpl in |- *.
generalize H; clear H.
elim succs; clear succs.
intros H in_t1.
inversion_clear in_t1.
intros t2 succs ih H in_t1.
inversion_clear in_t1.
inversion_clear H; assumption.
apply ih.
inversion_clear H; assumption.
assumption.
Qed.


Inductive Is_Monotone (t : Tree) : Prop :=
    is_monotone_intro :
      (forall t0 : Tree,
       Successor t0 t ->
       forall i : I,
       P (root t0) i -> forall t1 : Tree, Successor t1 t0 -> P (root t1) i) ->
      Is_Monotone t.



Lemma is_monotone_successor :
 forall T : Tree,
 Is_Monotone T -> forall t : Tree, Successor t T -> Is_Monotone t.
intros T mon_T t suc_t.
apply is_monotone_intro.
intros t0 suc_t0 i Pa t1 suc_1.
inversion_clear mon_T.
apply H with t0.
apply succs_trans with t; assumption.
assumption.
assumption.
Qed.


Lemma is_monotone_tree_is_monotone :
 forall t : Tree, Is_Monotone_Tree t -> Is_Monotone t.
intros t H.
apply is_monotone_intro.
intros t0 suc_t0.
generalize (is_monotone_tree_successor t H t0 suc_t0); clear H suc_t0 t.
intros H i P0 t1 suc_t1.
generalize P0; clear P0.
generalize H; clear H.
elim suc_t1; clear suc_t1 t0 t1.
trivial.
intros t0 t1 in_t1 t2 suc_t2 ih H P0.
apply ih; clear ih.
apply is_monotone_tree_successor with t0. 
assumption.
apply successor_trans with t1.
assumption.
apply successor_refl.
generalize P0; clear P0.
generalize in_t1; clear in_t1.
inversion_clear H.
simpl in |- *.
intros in_t1 Pa.
generalize H0; clear H0.
generalize in_t1; clear in_t1.
elim succs; clear succs.
intros in_t1 H0.
inversion_clear in_t1.
intros t3 succs ih in_t1 H0.
inversion_clear in_t1.
inversion_clear H0.
apply H; assumption.
apply ih.
assumption.
inversion_clear H0; assumption.
Qed.


End Trees.
