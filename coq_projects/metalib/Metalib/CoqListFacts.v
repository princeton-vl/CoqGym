(* This file is distributed under the terms of the MIT License, also
   known as the X11 Licence.  A copy of this license is in the README
   file that accompanied the original distribution of this file.

   Based on code written by:
     Brian Aydemir *)

(** Assorted facts about lists. *)

Require Import Coq.Lists.List.
Require Import Coq.Lists.SetoidList.

Require Import Metalib.CoqUniquenessTac.

Open Scope list_scope.


(* ********************************************************************** *)
(** * List structure *)

Lemma cons_eq_app : forall (A : Type) (z : A) (xs ys zs : list A),
  z :: zs = xs ++ ys ->
  (exists qs, xs = z :: qs /\ zs = qs ++ ys) \/
  (xs = nil /\ ys = z :: zs).
Proof.
  destruct xs; intros ? ? H; simpl in *.
    auto.
    injection H. intros. subst. eauto.
Qed.

Lemma app_eq_cons : forall (A : Type) (z : A) (xs ys zs : list A),
  xs ++ ys = z :: zs ->
  (exists qs, xs = z :: qs /\ zs = qs ++ ys) \/
  (xs = nil /\ ys = z :: zs).
Proof. auto using cons_eq_app. Qed.

Lemma nil_eq_app : forall (A : Type) (xs ys : list A),
  nil = xs ++ ys ->
  xs = nil /\ ys = nil.
Proof. auto using List.app_eq_nil. Qed.

Lemma app_cons_not_nil : forall (A : Type) (y : A) (xs ys : list A),
  xs ++ y :: ys <> nil.
Proof.
  intros ? ? ? ? H. symmetry in H. revert H. apply List.app_cons_not_nil.
Qed.


(* ********************************************************************** *)
(** * List membership *)

Lemma In_map : forall (A B : Type) (xs : list A) (x : A) (f : A -> B),
  In x xs ->
  In (f x) (map f xs).
Proof.
  induction xs; intros ? ? H; simpl in *.
    auto.
    destruct H; subst; auto.
Qed.


(* ********************************************************************** *)
(** * List non-membership *)

Lemma not_In_cons : forall (A : Type) (ys : list A) (x y : A),
  x <> y ->
  ~ In x ys ->
  ~ In x (y :: ys).
Proof. unfold not. inversion 3; auto. Qed.

Lemma not_In_app : forall (A : Type) (xs ys : list A) (x : A),
  ~ In x xs ->
  ~ In x ys ->
  ~ In x (xs ++ ys).
Proof. intros ? xs ys x ? ? H. apply in_app_or in H. intuition. Qed.

Lemma elim_not_In_cons : forall (A : Type) (y : A) (ys : list A) (x : A),
  ~ In x (y :: ys) ->
  x <> y /\ ~ In x ys.
Proof. simpl. intuition. Qed.

Lemma elim_not_In_app : forall (A : Type) (xs ys : list A) (x : A),
  ~ In x (xs ++ ys) ->
  ~ In x xs /\ ~ In x ys.
Proof. split; auto using in_or_app. Qed.


(* ********************************************************************** *)
(** * List inclusion *)

Lemma incl_nil : forall (A : Type) (xs : list A),
  incl nil xs.
Proof. unfold incl. inversion 1. Qed.

Lemma In_incl : forall (A : Type) (x : A) (ys zs : list A),
  In x ys ->
  incl ys zs ->
  In x zs.
Proof. unfold incl. auto. Qed.

Lemma elim_incl_cons : forall (A : Type) (x : A) (xs zs : list A),
  incl (x :: xs) zs ->
  In x zs /\ incl xs zs.
Proof. unfold incl. auto with datatypes. Qed.

Lemma elim_incl_app : forall (A : Type) (xs ys zs : list A),
  incl (xs ++ ys) zs ->
  incl xs zs /\ incl ys zs.
Proof. unfold incl. auto with datatypes. Qed.


(* ********************************************************************** *)
(** * Setoid facts *)

(** [InA] and [In] are related when the relation is [eq].  The lemma
    [In_InA], the converse of [InA_In], is in Coq's standard
    library. *)

Lemma InA_In : forall (A : Type) (x : A) (xs : list A),
  InA (@eq _) x xs -> In x xs.
Proof.
  induction xs; intros H.
    inversion H.
    inversion H; subst; simpl in *; auto.
Qed.

Lemma InA_iff_In : forall (A : Type) (x : A) (xs : list A),
  InA (@eq _) x xs <-> In x xs.
Proof.
  split; auto using InA_In.
  apply SetoidList.In_InA. apply eq_equivalence.
Qed.

(** Whether a list is sorted is a decidable proposition. *)

Section DecidableSorting.

  Variable A : Type.
  Variable leA : relation A.
  Hypothesis leA_dec : forall x y, {leA x y} + {~ leA x y}.

  Theorem lelistA_dec : forall a xs,
    {lelistA leA a xs} + {~ lelistA leA a xs}.
  Proof with auto.
    destruct xs as [ | x xs ]...
    destruct (leA_dec a x)...
    right. intros J. inversion J...
  Defined.

  Theorem sort_dec : forall xs,
    {sort leA xs} + {~ sort leA xs}.
  Proof with auto.
    induction xs as [ | x xs [Yes | No] ]...
    destruct (lelistA_dec x xs)...
      right. intros K. inversion K...
    right. intros K. inversion K...
  Defined.

End DecidableSorting.

(** Two sorted lists with the same elements are equal to each other.*)

Section SortedListEquality.

  Variable A : Type.
  Variable ltA : relation A.
  Hypothesis ltA_trans : forall x y z, ltA x y -> ltA y z -> ltA x z.
  Hypothesis ltA_not_eqA : forall x y, ltA x y -> x <> y.
  Hypothesis ltA_eqA : forall x y z, ltA x y -> y = z -> ltA x z.
  Hypothesis eqA_ltA : forall x y z, x = y -> ltA y z -> ltA x z.

  Hint Resolve ltA_trans.
  Hint Immediate ltA_eqA eqA_ltA.

  Notation Inf := (lelistA ltA).
  Notation Sort := (sort ltA).

  Lemma eqlist_eq : forall (xs ys : list A),
    eqlistA (@eq _) xs ys ->
    xs = ys.
  Proof. induction xs; destruct ys; inversion 1; f_equal; auto. Qed.

  Lemma Sort_InA_eq : forall xs ys,
    Sort xs ->
    Sort ys ->
    (forall a, InA (@eq _) a xs <-> InA (@eq _) a ys) ->
    xs = ys.
  Proof.
    intros xs ys ? ? ?.
    cut (eqlistA (@eq _) xs ys).
    auto using eqlist_eq.
    apply SetoidList.SortA_equivlistA_eqlistA with (ltA := ltA); eauto.
      apply eq_equivalence. firstorder.
      reduce. subst. split; auto.
  Qed.

  Lemma Sort_In_eq : forall xs ys,
    Sort xs ->
    Sort ys ->
    (forall a, In a xs <-> In a ys) ->
    xs = ys.
  Proof with auto using In_InA, InA_In.
    intros ? ? ? ? H.
    apply Sort_InA_eq...
    intros a; specialize (H a).
      split; intros; apply In_InA; intuition...
  Qed.

End SortedListEquality.


(* ********************************************************************** *)
(** * Uniqueness of proofs *)

(** Uniqueness of proofs for predicates on lists often comes up when
    discussing extensional equality on finite sets, as implemented by
    the FSets library. *)

Section Uniqueness_Of_SetoidList_Proofs.

  Variable A : Type.
  Variable R : A -> A -> Prop.

  Hypothesis R_unique : forall (x y : A) (p q : R x y), p = q.
  Hypothesis list_eq_dec : forall (xs ys : list A), {xs = ys} + {xs <> ys}.

  Scheme lelistA_ind' := Induction for lelistA Sort Prop.
  Scheme sort_ind'    := Induction for sort Sort Prop.
  Scheme eqlistA_ind' := Induction for eqlistA Sort Prop.

  Theorem lelistA_unique :
    forall (x : A) (xs : list A) (p q : lelistA R x xs), p = q.
  Proof. induction p using lelistA_ind'; uniqueness 1. Qed.

  Theorem sort_unique :
    forall (xs : list A) (p q : sort R xs), p = q.
  Proof. induction p using sort_ind'; uniqueness 1. apply lelistA_unique. Qed.

  Theorem eqlistA_unique :
    forall (xs ys : list A) (p q : eqlistA R xs ys), p = q.
  Proof. induction p using eqlistA_ind'; uniqueness 2. Qed.

End Uniqueness_Of_SetoidList_Proofs.
