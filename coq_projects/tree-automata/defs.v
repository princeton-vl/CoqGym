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
Require Import Arith.
Require Import ZArith.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Import bases.

(* définition inductive du type des termes : *)
Inductive term : Set :=
    app : ad -> term_list -> term
with term_list : Set :=
  | tnil : term_list
  | tcons : term -> term_list -> term_list.

(* les principes d'induction *)
Scheme term_term_list_rec := Induction for term
  Sort Set
  with term_list_term_rec := Induction for term_list 
  Sort Set.

Scheme term_term_list_ind := Induction for term
  Sort Prop
  with term_list_term_ind := Induction for term_list 
  Sort Prop.

Lemma term_list_disj :
 forall l : term_list,
 l = tnil \/ (exists hd : term, (exists tl : term_list, l = tcons hd tl)).
Proof.
	simple induction l. left. trivial. right. split with t. split with t0.
	trivial.
Qed.

Fixpoint lst_length (l : term_list) : nat :=
  match l with
  | tnil => 0
  | tcons _ l' => S (lst_length l')
  end.

Fixpoint term_high (t : term) : nat :=
  match t with
  | app a l => S (term_high_0 l)
  end
 
 with term_high_0 (l : term_list) : nat :=
  match l with
  | tnil => 0
  | tcons hd tl => max (term_high hd) (term_high_0 tl)
  end.

Lemma high_aux_0 :
 forall (a : ad) (l : term_list), S (term_high_0 l) <= term_high (app a l).
Proof.
	intros. unfold term_high in |- *. unfold term_high_0 in |- *. exact (le_n_n _).
Qed.

Lemma high_aux_1 :
 forall (a : ad) (l : term_list), S (term_high_0 l) = term_high (app a l).
Proof.
	intros. unfold term_high in |- *. unfold term_high_0 in |- *. trivial.
Qed.

Lemma high_aux_2 : forall (l : term_list) (c : ad), 1 <= term_high (app c l).
Proof.
	intros. cut (S (term_high_0 l) <= term_high (app c l)).
	intro. cut (1 <= S (term_high_0 l)). intro.
	exact (le_trans 1 (S (term_high_0 l)) (term_high (app c l)) H0 H).
	exact (le_n_S 0 (term_high_0 l) (le_O_n (term_high_0 l))).
	exact (high_aux_0 c l).
Qed.

Lemma high_aux_3 :
 forall (t : term) (tl : term_list), term_high t <= term_high_0 (tcons t tl).
Proof.
	intros. simpl in |- *. unfold term_high in |- *. exact (le_max_l _ (term_high_0 tl)).
Qed.

Lemma high_aux_4 :
 forall (t : term) (tl : term_list),
 term_high_0 tl <= term_high_0 (tcons t tl).
Proof.
	intros.
	cut (term_high_0 (tcons t tl) = max (term_high t) (term_high_0 tl)).
	intro. rewrite H. exact (le_max_r (term_high t) (term_high_0 tl)).
	unfold term_high_0 in |- *. trivial.
Qed.

(* taille des termes : *)

Fixpoint taille_term (t : term) : nat :=
  match t with
  | app c l => S (mtaille_term_list l)
  end
 
 with mtaille_term_list (l : term_list) : nat :=
  match l with
  | tnil => 0
  | tcons hd tl => max (taille_term hd) (mtaille_term_list tl)
  end.

(* définition des structures prec_list : adjacence des états de l'automate *)

Inductive prec_list : Set :=
  | prec_cons : ad -> prec_list -> prec_list -> prec_list
  | prec_empty : prec_list.

Lemma pl_sum :
 forall pl : prec_list,
 pl = prec_empty \/
 (exists a : ad,
    (exists la : prec_list, (exists ls : prec_list, pl = prec_cons a la ls))).
Proof.
	intros. induction  pl as [a pl1 Hrecpl1 pl0 Hrecpl0| ]. right. split with a. split with pl1.
	split with pl0. reflexivity. left. reflexivity.
Qed.

(* définition des états *)

Definition state := Map prec_list.

(* définition des automates *)

Definition preDTA := Map state.

Inductive DTA : Set :=
    dta : preDTA -> ad -> DTA.

(* calcul de la taille de l'automate : *)

Fixpoint taille_0 (l : prec_list) : nat :=
  match l with
  | prec_empty => 0
  | prec_cons x y z => S (taille_0 y + taille_0 z)
  end.

Fixpoint taille_1 (s : state) : nat :=
  match s with
  | M0 => 0
  | M1 x y => taille_0 y
  | M2 x y => max (taille_1 x) (taille_1 y)
  end.

Fixpoint DTA_taille (d : preDTA) : nat :=
  match d with
  | M0 => 0
  | M1 x y => taille_1 y
  | M2 x y => max (DTA_taille x) (DTA_taille y)
  end.

Lemma taille_aux_0 :
 forall (a : ad) (la ls : prec_list),
 S (taille_0 la) <= taille_0 (prec_cons a la ls).
Proof.
	intros. simpl in |- *.
	apply (le_n_S (taille_0 la) (taille_0 la + taille_0 ls)).
	exact (le_plus_l (taille_0 la) (taille_0 ls)).
Qed.

Lemma taille_aux_1 :
 forall (a : ad) (la ls : prec_list), 1 <= taille_0 (prec_cons a la ls).
Proof.
	intros. unfold taille_0 in |- *. 
	exact (le_n_S 0 _ (le_O_n _)).
Qed.

Lemma taille_aux_2 :
 forall (a : ad) (la ls : prec_list),
 S (taille_0 ls) <= taille_0 (prec_cons a la ls).
Proof.
	intros. simpl in |- *.
	apply (le_n_S (taille_0 ls) (taille_0 la + taille_0 ls)).
	exact (le_plus_r (taille_0 la) (taille_0 ls)).
Qed.

(* relation d'une adresse d'occurence dans les prec_list *)

Inductive prec_occur : prec_list -> ad -> Prop :=
  | prec_hd :
      forall (a : ad) (pl0 pl1 : prec_list),
      prec_occur (prec_cons a pl0 pl1) a
  | prec_int0 :
      forall (a b : ad) (pl0 pl1 : prec_list),
      prec_occur pl0 b -> prec_occur (prec_cons a pl0 pl1) b
  | prec_int1 :
      forall (a b : ad) (pl0 pl1 : prec_list),
      prec_occur pl1 b -> prec_occur (prec_cons a pl0 pl1) b.

(* relation de "contenu" pour les prec_list *)

Inductive prec_contained : prec_list -> prec_list -> Prop :=
  | prec_id : forall p : prec_list, prec_contained p p
  | prec_c_int0 :
      forall (p p0 p1 : prec_list) (a : ad),
      prec_contained p p0 -> prec_contained p (prec_cons a p0 p1)
  | prec_c_int1 :
      forall (p p0 p1 : prec_list) (a : ad),
      prec_contained p p1 -> prec_contained p (prec_cons a p0 p1).

(* définition de l'appartenance d'un état à un pre dta *)

Definition state_in_dta (d : preDTA) (s : state) : Prop :=
  exists a : ad, MapGet state d a = Some s.

Definition state_in_dta_diff (d : preDTA) (s : state) 
  (a : ad) : Prop := exists b : ad, MapGet state d b = Some s /\ a <> b.

(* définition de l'appartenance d'une adjacence à un pre dta *)

Definition prec_in_dta (d : preDTA) (p : prec_list) : Prop :=
  exists s : state,
    (exists a : ad,
       (exists c : ad,
          MapGet state d a = Some s /\
          MapGet prec_list s c = Some p)).

Definition prec_in_dta_cont (d : preDTA) (p : prec_list) : Prop :=
  exists s : state,
    (exists b : ad,
       (exists c : ad,
          (exists p0 : prec_list,
             MapGet state d b = Some s /\
             MapGet prec_list s c = Some p0 /\ prec_contained p p0))).

Definition prec_in_dta_diff (d : preDTA) (p : prec_list) 
  (a : ad) : Prop :=
  exists s : state,
    (exists b : ad,
       (exists c : ad,
          MapGet state d b = Some s /\
          MapGet prec_list s c = Some p /\ a <> b)).

Definition prec_in_dta_diff_cont (d : preDTA) (p : prec_list) 
  (a : ad) : Prop :=
  exists s : state,
    (exists b : ad,
       (exists c : ad,
          (exists p0 : prec_list,
             MapGet state d b = Some s /\
             MapGet prec_list s c = Some p0 /\
             prec_contained p p0 /\ a <> b))).

(* définition de l'appartenance d'une adjacence à un etat *)

Definition prec_in_state (s : state) (p : prec_list) : Prop :=
  exists c : ad, MapGet prec_list s c = Some p.

Lemma prec_in_state_M0_false :
 forall p : prec_list, ~ prec_in_state (M0 prec_list) p.
Proof.
	intros. exact (in_M0_false prec_list p).
Qed.

Lemma state_in_dta_M0_false : forall s : state, ~ state_in_dta (M0 state) s.
Proof.
	intros. exact (in_M0_false state s).
Qed.

(* lemmes sur prec_occur, contained : *)

Lemma prec_occur_1 :
 forall (a : ad) (p0 p1 p2 : prec_list),
 prec_contained (prec_cons a p0 p1) p2 -> prec_occur p2 a.
Proof.
	intros. induction  p2 as [a0 p2_1 Hrecp2_1 p2_0 Hrecp2_0| ]. inversion H. exact (prec_hd a0 p2_1 p2_0).
	exact (prec_int0 a0 a p2_1 p2_0 (Hrecp2_1 H2)).
	exact (prec_int1 a0 a p2_1 p2_0 (Hrecp2_0 H2)).
	inversion H.
Qed.

Lemma prec_contained_0 :
 forall (a : ad) (p0 p1 p2 : prec_list),
 prec_contained (prec_cons a p0 p1) p2 -> prec_contained p0 p2.
Proof.
	intros. induction  p2 as [a0 p2_1 Hrecp2_1 p2_0 Hrecp2_0| ]. inversion H. 
	exact (prec_c_int0 p2_1 p2_1 p2_0 a0 (prec_id p2_1)).
	exact (prec_c_int0 _ _ _ _ (Hrecp2_1 H2)).
	exact (prec_c_int1 _ _ _ _ (Hrecp2_0 H2)). 
	inversion H.
Qed.

Lemma prec_contained_1 :
 forall (a : ad) (p0 p1 p2 : prec_list),
 prec_contained (prec_cons a p0 p1) p2 -> prec_contained p1 p2.
Proof.
	intros. induction  p2 as [a0 p2_1 Hrecp2_1 p2_0 Hrecp2_0| ]. inversion H. 
	exact (prec_c_int1 _ _ _ _ (prec_id p2_0)).
	exact (prec_c_int0 _ _ _ _ (Hrecp2_1 H2)).
	exact (prec_c_int1 _ _ _ _ (Hrecp2_0 H2)).
	inversion H.
Qed.

(* occurence de termes dans les listes *)

Inductive term_occur : term -> term -> Prop :=
  | to_eq : forall t : term, term_occur t t
  | to_st :
      forall (t : term) (a : ad) (tl : term_list),
      term_list_occur t tl -> term_occur t (app a tl)
with term_list_occur : term -> term_list -> Prop :=
  | tlo_head :
      forall (t hd : term) (tl : term_list),
      term_occur t hd -> term_list_occur t (tcons hd tl)
  | tlo_tail :
      forall (t hd : term) (tl : term_list),
      term_list_occur t tl -> term_list_occur t (tcons hd tl).

Definition term_occur_def_0 (t : term) :=
  forall u : term, term_occur u t -> term_high u <= term_high t.

Definition term_occur_def_1 (t : term_list) :=
  forall u : term, term_list_occur u t -> term_high u <= term_high_0 t.

Lemma term_occur_0_0 :
 forall (a : ad) (t : term_list),
 term_occur_def_1 t -> term_occur_def_0 (app a t).
Proof.
	unfold term_occur_def_1 in |- *. unfold term_occur_def_0 in |- *. intros. inversion H0.
	exact (le_n_n _). apply
  (le_trans (term_high u) (term_high_0 t) (term_high (app a t)) (H u H3)). unfold term_high in |- *. exact (le_n_Sn _).
Qed.

Lemma term_occur_0_1 : term_occur_def_1 tnil.
Proof.
	unfold term_occur_def_1 in |- *. intros. induction  u as (a, t). inversion H.
Qed.

Lemma term_occur_0_2 :
 forall t : term,
 term_occur_def_0 t ->
 forall t0 : term_list, term_occur_def_1 t0 -> term_occur_def_1 (tcons t t0).
Proof.
	unfold term_occur_def_0 in |- *. unfold term_occur_def_1 in |- *. intros. inversion H1.
	apply (le_trans (term_high u) (term_high t) (term_high_0 (tcons t t0))).
	exact (H u H4). exact (le_max_l _ _). apply (le_trans (term_high u) (term_high_0 t0) (term_high_0 (tcons t t0))). exact (H0 u H4).
	exact (le_max_r _ _).
Qed.

Lemma term_occur_0 :
 forall t u : term, term_occur u t -> term_high u <= term_high t.
Proof.
	exact
  (term_term_list_ind term_occur_def_0 term_occur_def_1 term_occur_0_0
     term_occur_0_1 term_occur_0_2).
Qed.

Lemma term_occur_1 :
 forall (t : term_list) (u : term),
 term_list_occur u t -> term_high u <= term_high_0 t.
Proof.
	exact
  (term_list_term_ind term_occur_def_0 term_occur_def_1 term_occur_0_0
     term_occur_0_1 term_occur_0_2).
Qed.

Definition indprinciple_3_aux (n : nat) :=
  forall P : term -> Prop,
  (forall (a : ad) (tl : term_list),
   (forall u : term, term_list_occur u tl -> P u) -> P (app a tl)) ->
  forall t : term, term_high t <= n -> P t.

Lemma indprinciple_3_0 : indprinciple_3_aux 0.
Proof.
	unfold indprinciple_3_aux in |- *. intros. induction  t as (a, t). simpl in H0. inversion H0.
Qed.

Lemma indprinciple_3_1 :
 forall n : nat, indprinciple_3_aux n -> indprinciple_3_aux (S n).
Proof.
	unfold indprinciple_3_aux in |- *. intros. induction  t as (a, t). apply (H0 a t).
	intros. apply (H P H0 u). apply (le_trans (term_high u) (term_high_0 t) n).
	exact (term_occur_1 t u H2). exact (le_S_n _ _ H1).
Qed.

Lemma indprinciple_3_2 :
 forall (n : nat) (P : term -> Prop),
 (forall (a : ad) (tl : term_list),
  (forall u : term, term_list_occur u tl -> P u) -> P (app a tl)) ->
 forall t : term, term_high t <= n -> P t.
Proof.
	exact (nat_ind indprinciple_3_aux indprinciple_3_0 indprinciple_3_1).
Qed.

Lemma indprinciple_term :
 forall P : term -> Prop,
 (forall (a : ad) (tl : term_list),
  (forall u : term, term_list_occur u tl -> P u) -> P (app a tl)) ->
 forall t : term, P t.
Proof.
	intros. exact (indprinciple_3_2 (term_high t) P H t (le_n_n _)).
Qed.

(* lemmes sur Ndouble, Ndouble_plus_one *)

Lemma Ndouble_inv_N0 : forall x : ad, Ndouble x = N0 -> x = N0.
Proof.
	simple induction x. intros. reflexivity. simpl in |- *. intros. inversion H.
Qed.

Lemma Ndouble_inv_xO :
 forall (x : ad) (p : positive), Ndouble x = Npos (xO p) -> x = Npos p.
Proof.
	simple induction x. intros. inversion H. intros. simpl in H.
	inversion H. reflexivity.
Qed.

Lemma Ndouble_plus_one_inv_xH :
 forall x : ad, Ndouble_plus_one x = Npos 1 -> x = N0.
Proof.
	simple induction x. intros. reflexivity. simpl in |- *. intros. inversion H.
Qed.

Lemma Ndouble_plus_one_inv_xI :
 forall (x : ad) (p : positive),
 Ndouble_plus_one x = Npos (xI p) -> x = Npos p.
Proof.
	simple induction x. intros. inversion H. intros. simpl in H.
	inversion H. reflexivity.
Qed.