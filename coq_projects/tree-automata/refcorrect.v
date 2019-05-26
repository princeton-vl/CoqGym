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


Require Import Bool.
Require Import NArith Ndec.
From IntMap Require Import Allmaps.
Require Import bases.
Require Import defs.

(* correction d'un preDTA : pas de référence à des adresses extérieures à l'automate *)

Definition prec_list_ref_ok (p : prec_list) (d : preDTA) : Prop :=
  forall a : ad,
  prec_occur p a -> exists s : state, MapGet state d a = Some s.

Definition state_ref_ok (s : state) (d : preDTA) : Prop :=
  forall (a : ad) (p : prec_list),
  MapGet prec_list s a = Some p -> prec_list_ref_ok p d.

Definition preDTA_ref_ok (d : preDTA) : Prop :=
  forall (a : ad) (s : state) (c : ad) (pl : prec_list) (b : ad),
  MapGet state d a = Some s ->
  MapGet prec_list s c = Some pl ->
  prec_occur pl b -> exists s0 : state, MapGet state d b = Some s0.

Definition preDTA_ref_ok_distinct (d d' : preDTA) : Prop :=
  forall (a : ad) (s : state),
  MapGet state d a = Some s -> state_ref_ok s d'.

Definition DTA_ref_ok (d : DTA) : Prop :=
  match d with
  | dta p a => preDTA_ref_ok p
  end.

Lemma prec_list_ref_ok_destr :
 forall (a : ad) (la ls : prec_list) (d : preDTA),
 prec_list_ref_ok (prec_cons a la ls) d ->
 prec_list_ref_ok la d /\ prec_list_ref_ok ls d.
Proof.
	unfold prec_list_ref_ok in |- *. intros. split. intros.
	exact (H a0 (prec_int0 a a0 la ls H0)). intros.
	exact (H a0 (prec_int1 a a0 la ls H0)).
Qed.

Lemma state_ref_ok_M2_destr :
 forall (s0 s1 : state) (d : preDTA),
 state_ref_ok (M2 prec_list s0 s1) d ->
 state_ref_ok s0 d /\ state_ref_ok s1 d.
Proof.
	unfold state_ref_ok in |- *. intros. split; intros. apply (H (Ndouble a) p). induction  a as [| p0]; exact H0. apply (H (Ndouble_plus_one a) p).
	induction  a as [| p0]; exact H0.
Qed.

Lemma preDTA_ref_ok_def :
 forall d : preDTA,
 preDTA_ref_ok d <->
 (forall (a : ad) (s : state),
  MapGet state d a = Some s -> state_ref_ok s d).
Proof.
	intros. unfold preDTA_ref_ok in |- *. unfold state_ref_ok in |- *. unfold prec_list_ref_ok in |- *. split. intros. exact (H a s a0 p a1 H0 H1 H2).
	intros. exact (H a s H0 c pl H1 b H2).
Qed.

Lemma preDTA_ref_ok_distinct_dest :
 forall d0 d1 d : preDTA,
 preDTA_ref_ok_distinct (M2 state d0 d1) d ->
 preDTA_ref_ok_distinct d0 d /\ preDTA_ref_ok_distinct d1 d.
Proof.
	unfold preDTA_ref_ok_distinct in |- *. intros. split. intros.
	apply (H (Ndouble a) s). induction  a as [| p]; exact H0. intros.
	apply (H (Ndouble_plus_one a) s). induction  a as [| p]; exact H0.
Qed.

(* une fonction permettant de décider la propriété preDTA_ref_ok *)

Definition addr_in_dta_check (d : preDTA) (a : ad) : bool :=
  match MapGet state d a with
  | None => false
  | Some _ => true
  end.

Fixpoint prec_list_ref_ok_check (p : prec_list) : preDTA -> bool :=
  fun d : preDTA =>
  match p with
  | prec_empty => true
  | prec_cons a la ls =>
      addr_in_dta_check d a &&
      (prec_list_ref_ok_check la d && prec_list_ref_ok_check ls d)
  end.

Lemma prec_list_ref_ok_check_correct :
 forall (p : prec_list) (d : preDTA),
 prec_list_ref_ok p d -> prec_list_ref_ok_check p d = true.
Proof.
	simple induction p. simpl in |- *. intros. elim (prec_list_ref_ok_destr a p0 p1 d H1).
	intros. rewrite (H d H2). rewrite (H0 d H3). unfold prec_list_ref_ok in H1.
	unfold addr_in_dta_check in |- *. elim (H1 a (prec_hd a p0 p1)). intros. rewrite H4. reflexivity. intros. reflexivity.
Qed.

Lemma prec_list_ref_ok_check_complete :
 forall (p : prec_list) (d : preDTA),
 prec_list_ref_ok_check p d = true -> prec_list_ref_ok p d.
Proof.
	simple induction p. intros. simpl in H1. elim (bool_is_true_or_false (addr_in_dta_check d a)); intros;
  rewrite H2 in H1. elim (bool_is_true_or_false (prec_list_ref_ok_check p0 d)). intros.
	rewrite H3 in H1. elim (bool_is_true_or_false (prec_list_ref_ok_check p1 d)); intros;
  rewrite H4 in H1. unfold prec_list_ref_ok in |- *. intros.
	inversion H5. unfold addr_in_dta_check in H2. elim (option_sum state (MapGet state d a)). intro y. elim y. intros x y0. split with x. rewrite H6 in y0. exact y0. intro y. rewrite y in H2. inversion H2. exact (H d H3 a0 H10). exact (H0 d H4 a0 H10). inversion H1. intros.
	rewrite H3 in H1. inversion H1. inversion H1. intros. unfold prec_list_ref_ok in |- *. intros. inversion H0.
Qed.

Fixpoint state_ref_ok_check (s : state) : preDTA -> bool :=
  fun d : preDTA =>
  match s with
  | M0 => true
  | M1 a p => prec_list_ref_ok_check p d
  | M2 x y => state_ref_ok_check x d && state_ref_ok_check y d
  end.

Lemma state_ref_ok_check_correct :
 forall (s : state) (d : preDTA),
 state_ref_ok s d -> state_ref_ok_check s d = true.
Proof.
	unfold state_ref_ok in |- *. simple induction s. intros. reflexivity. intros.
	simpl in |- *. apply (prec_list_ref_ok_check_correct a0 d). apply (H a a0).
	simpl in |- *. rewrite (Neqb_correct a). reflexivity. intros. simpl in |- *.
	rewrite (H d). rewrite (H0 d). reflexivity. intros. apply (H1 (Ndouble_plus_one a) p). induction  a as [| p0]; simpl in |- *; exact H2. intros.
	apply (H1 (Ndouble a) p). induction  a as [| p0]; simpl in |- *; exact H2.
Qed.

Lemma state_ref_ok_check_complete :
 forall (s : state) (d : preDTA),
 state_ref_ok_check s d = true -> state_ref_ok s d.
Proof.
	unfold state_ref_ok in |- *. simple induction s. intros. inversion H0. intros.
	simpl in H0. elim (bool_is_true_or_false (Neqb a a1)); intros; rewrite H1 in H0. inversion H0. simpl in H. rewrite H3 in H.
	exact (prec_list_ref_ok_check_complete p d H). inversion H0. intros.
	simpl in H1. elim (bool_is_true_or_false (state_ref_ok_check m d)); intros;
  rewrite H3 in H1. elim (bool_is_true_or_false (state_ref_ok_check m0 d)); intros;
  rewrite H4 in H1. induction  a as [| p0]. simpl in H2.
	exact (H d H3 N0 p H2). induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]; simpl in H2. exact (H0 d H4 (Npos p0) p H2). exact (H d H3 (Npos p0) p H2). exact (H0 d H4 N0 p H2). inversion H1. inversion H1.
Qed.

Fixpoint predta_ref_ok_check_0 (d : preDTA) : preDTA -> bool :=
  fun d' : preDTA =>
  match d with
  | M0 => true
  | M1 a s => state_ref_ok_check s d'
  | M2 x y => predta_ref_ok_check_0 x d' && predta_ref_ok_check_0 y d'
  end.

Definition predta_ref_ok_check (d : preDTA) : bool :=
  predta_ref_ok_check_0 d d.

Lemma predta_ref_ok_check_correct_0 :
 forall d d' : preDTA,
 preDTA_ref_ok_distinct d d' -> predta_ref_ok_check_0 d d' = true.
Proof.
	intros. unfold preDTA_ref_ok_distinct in H. induction  d as [| a a0| d1 Hrecd1 d0 Hrecd0]. intros.
	reflexivity. simpl in |- *. apply (state_ref_ok_check_correct a0 d'). apply (H a a0). simpl in |- *. rewrite (Neqb_correct a). reflexivity. simpl in |- *.
	rewrite Hrecd1. rewrite Hrecd0. reflexivity. intros. apply (H (Ndouble_plus_one a) s). induction  a as [| p]; simpl in |- *; exact H0. intros.
	apply (H (Ndouble a) s). induction  a as [| p]; simpl in |- *; exact H0. 
Qed.

Lemma predta_ref_ok_check_complete_0 :
 forall d d' : preDTA,
 predta_ref_ok_check_0 d d' = true -> preDTA_ref_ok_distinct d d'.
Proof.
	unfold preDTA_ref_ok_distinct in |- *. simple induction d; simpl in |- *; intros. inversion H0.
	elim (bool_is_true_or_false (Neqb a a1)); intros; rewrite H1 in H0;
  inversion H0. rewrite <- H3. exact (state_ref_ok_check_complete _ _ H).
 	elim (bool_is_true_or_false (predta_ref_ok_check_0 m d')); intros;
   rewrite H3 in H1. elim (bool_is_true_or_false (predta_ref_ok_check_0 m0 d')); intros;
  rewrite H4 in H1. induction  a as [| p]. exact (H d' H3 N0 s H2).
	induction  p as [p Hrecp| p Hrecp| ]. exact (H0 d' H4 (Npos p) s H2). exact (H d' H3 (Npos p) s H2).
	exact (H0 d' H4 N0 s H2). inversion H1. inversion H1.
Qed.

Lemma predta_ref_ok_check_correct :
 forall d : preDTA, preDTA_ref_ok d -> predta_ref_ok_check d = true.
Proof.
	unfold predta_ref_ok_check in |- *. intros. elim (preDTA_ref_ok_def d). intros.
	apply (predta_ref_ok_check_correct_0 d d). unfold preDTA_ref_ok_distinct in |- *.
	exact (H0 H).
Qed.

Lemma predta_ref_ok_check_complete :
 forall d : preDTA, predta_ref_ok_check d = true -> preDTA_ref_ok d.
Proof.
	intros. elim (preDTA_ref_ok_def d). intros. apply H1. unfold predta_ref_ok_check in H. exact (predta_ref_ok_check_complete_0 d d H).
Qed.

Definition dta_ref_ok_check (d : DTA) : bool :=
  match d with
  | dta p a => predta_ref_ok_check p
  end.

Lemma dta_ref_ok_check_correct :
 forall d : DTA, DTA_ref_ok d -> dta_ref_ok_check d = true.
Proof.
	simple induction d. simpl in |- *. intro. intro. exact (predta_ref_ok_check_correct p).
Qed.

Lemma dta_ref_ok_check_complete :
 forall d : DTA, dta_ref_ok_check d = true -> DTA_ref_ok d.
Proof.
	simple induction d. simpl in |- *. intro. intro. exact (predta_ref_ok_check_complete p).
Qed.

(* autre correction a verifier : appartenance du dernier etat *)

Definition addr_in_preDTA (d : preDTA) (a : ad) : Prop :=
  exists s : state, MapGet state d a = Some s.

Definition DTA_main_state_correct (d : DTA) : Prop :=
  match d with
  | dta p a => addr_in_preDTA p a
  end.

Definition DTA_main_state_correct_check (d : DTA) : bool :=
  match d with
  | dta p a =>
      match MapGet state p a with
      | None => false
      | Some _ => true
      end
  end.

Lemma DTA_main_state_correct_check_correct :
 forall d : DTA,
 DTA_main_state_correct d -> DTA_main_state_correct_check d = true.
Proof.
	simple induction d. simpl in |- *. intros. unfold addr_in_preDTA in H. elim H. intros. rewrite H0. reflexivity.
Qed.

Lemma DTA_main_state_correct_check_complete :
 forall d : DTA,
 DTA_main_state_correct_check d = true -> DTA_main_state_correct d.
Proof.
	simple induction d. simpl in |- *. intros. elim (option_sum state (MapGet state p a)); intro y. elim y.
	intros x y0. split with x. exact y0. rewrite y in H.
	inversion H.
Qed.