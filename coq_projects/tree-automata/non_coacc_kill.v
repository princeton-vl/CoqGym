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
Require Import NArith Ndec.
Require Import ZArith.
From IntMap Require Import Allmaps.
Require Import bases.
Require Import defs.
Require Import semantics.
Require Import refcorrect.
Require Import lattice_fixpoint.
Require Import coacc_test.

(* fonction de suppression des états non coaccessibles *)

Fixpoint non_coacc_kill (d : preDTA) (m : Map bool) {struct m} : preDTA :=
  match d, m with
  | M0, M0 => M0 state
  | M1 a s, M1 a' b => if Neqb a a' && b then M1 state a s else M0 state
  | M2 x y, M2 z t => M2 state (non_coacc_kill x z) (non_coacc_kill y t)
  | _, _ => M0 state
  end.

Definition predta_kill_non_coacc (d : preDTA) (a : ad) : preDTA :=
  non_coacc_kill d (predta_coacc_states d a).

Definition dta_kill_non_coacc (d : DTA) : DTA :=
  match d with
  | dta p a => dta (predta_kill_non_coacc p a) a
  end.

Definition predta_kill_non_coacc_lazy (d : preDTA) 
  (a : ad) : preDTA := non_coacc_kill d (predta_coacc_states_0 d a).

Definition dta_kill_non_coacc_lazy (d : DTA) : DTA :=
  match d with
  | dta p a => dta (predta_kill_non_coacc_lazy p a) a
  end.

Lemma kill_non_coacc_lazy_eq_kill_non_coacc :
 forall d : DTA, dta_kill_non_coacc_lazy d = dta_kill_non_coacc d.
Proof.
	intros. unfold dta_kill_non_coacc_lazy, dta_kill_non_coacc in |- *.
	unfold predta_kill_non_coacc_lazy, predta_kill_non_coacc in |- *.
	unfold predta_coacc_states, predta_coacc_states_0 in |- *. induction  d as (p, a).
	rewrite
  (lazy_power_eg_power bool eqm_bool (predta_coacc p a) 
     (map_mini state p) (S (MapCard state p))). reflexivity.
	split. exact (eqm_bool_equal a0 b). intros. rewrite H.
	exact (equal_eqm_bool b).
Qed.

(* démo : un état apparait dans non_coacc_kill ssi il est coacc *)

Lemma non_coacc_kill_0 :
 forall (d : preDTA) (a : ad) (s : state) (m : Map bool),
 ensemble_base state d m ->
 MapGet state d a = Some s ->
 MapGet bool m a = Some true ->
 MapGet state (non_coacc_kill d m) a = Some s.
Proof.
	simple induction d; intros. inversion H0. induction  m as [| a2 a3| m1 Hrecm1 m0 Hrecm0]; simpl in H1. inversion H1. simpl in H0. simpl in |- *. elim (bool_is_true_or_false (Neqb a a1)); intros. rewrite H2 in H0. elim (bool_is_true_or_false (Neqb a2 a1)); intros; rewrite H3 in H1;
  inversion H1. rewrite (Neqb_complete _ _ H2). rewrite (Neqb_complete _ _ H3).
	rewrite (Neqb_correct a1). simpl in |- *. rewrite (Neqb_correct a1). inversion H0. reflexivity. rewrite H2 in H0.
	inversion H0. inversion H. induction  m1 as [| a0 a1| m1_1 Hrecm1_1 m1_0 Hrecm1_0]. inversion H1.
	inversion H1. simpl in |- *. unfold ensemble_base in H1. elim H1.
	intros. induction  a as [| p]; simpl in |- *; simpl in H2; simpl in H3.
	exact (H _ _ _ H4 H2 H3). induction  p as [p Hrecp| p Hrecp| ]; simpl in |- *; simpl in H2;
  simpl in H3. exact (H0 _ _ _ H5 H2 H3). exact (H _ _ _ H4 H2 H3). exact (H0 _ _ _ H5 H2 H3).
Qed.

Lemma non_coacc_kill_1 :
 forall (d : preDTA) (a : ad) (s : state) (m : Map bool),
 ensemble_base state d m ->
 MapGet state (non_coacc_kill d m) a = Some s ->
 MapGet state d a = Some s /\ MapGet bool m a = Some true.
Proof.
	simple induction d; intros. induction  m as [| a0 a1| m1 Hrecm1 m0 Hrecm0]; inversion H0.
	induction  m as [| a2 a3| m1 Hrecm1 m0 Hrecm0]. inversion H. simpl in H. simpl in H0.
	elim (bool_is_true_or_false (Neqb a a2)); intros; rewrite H1 in H0. elim (bool_is_true_or_false a3); intros; rewrite H2 in H0. simpl in H0. elim (bool_is_true_or_false (Neqb a a1)); intros; rewrite H3 in H0;
  inversion H0. rewrite (Neqb_complete _ _ H1).
	simpl in |- *. rewrite <- (Neqb_complete _ _ H1). rewrite <- (Neqb_complete _ _ H3). rewrite H2. rewrite (Neqb_correct a). split; reflexivity. simpl in H0.
	inversion H0. simpl in H0. inversion H0. inversion H.
	induction  m1 as [| a0 a1| m1_1 Hrecm1_1 m1_0 Hrecm1_0]. inversion H1. inversion H1. unfold ensemble_base in H1. elim H1. intros. induction  a as [| p]; simpl in |- *; simpl in H2. exact (H _ _ _ H3 H2). induction  p as [p Hrecp| p Hrecp| ]; simpl in |- *; simpl in H2. exact (H0 _ _ _ H4 H2).
	exact (H _ _ _ H3 H2). exact (H0 _ _ _ H4 H2).
Qed.

Lemma predta_kill_non_coacc_0 :
 forall (d : preDTA) (a a0 : ad) (s : state),
 preDTA_ref_ok d ->
 (MapGet state d a0 = Some s /\ coacc d a a0 <->
  MapGet state (predta_kill_non_coacc d a) a0 = Some s).
Proof.
	intros. split. intros. intros. elim (predta_coacc_fix d a a0). intros. intros. elim H0. intros. apply
  (fun p : ensemble_base state d (predta_coacc_states d a) =>
   non_coacc_kill_0 d a0 s (predta_coacc_states d a) p H3 (H2 H4)). unfold predta_coacc_states in |- *. apply
  (power_def_ok bool (ensemble_base state d) (predta_coacc d a)
     (map_mini state d) (S (MapCard state d))). unfold def_ok_app in |- *.
	intros. exact (predta_coacc_def_ok d a x). exact (map_mini_appartient state d). exact H. intros. unfold predta_kill_non_coacc in H0. elim
  (fun p : ensemble_base state d (predta_coacc_states d a) =>
   non_coacc_kill_1 d a0 s (predta_coacc_states d a) p H0). intros. split. exact H1.
	elim (predta_coacc_fix d a a0 H). intros. exact (H3 H2).
	unfold predta_coacc_states in |- *. apply
  (power_def_ok bool (ensemble_base state d) (predta_coacc d a)
     (map_mini state d) (S (MapCard state d))). unfold def_ok_app in |- *.
	intros. exact (predta_coacc_def_ok d a x). exact (map_mini_appartient state d).
Qed.

(* coaccessibilité des états conservée en supprimant les coaccessibles *)

Definition predta_kill_non_coacc_def_0 (d : preDTA) 
  (a0 a1 : ad) : Prop :=
  preDTA_ref_ok d ->
  coacc d a0 a1 -> coacc (predta_kill_non_coacc d a0) a0 a1.

Lemma predta_kill_non_coacc_1 :
 forall (d : preDTA) (a : ad) (s : state),
 MapGet state d a = Some s -> predta_kill_non_coacc_def_0 d a a.
Proof.
	unfold predta_kill_non_coacc_def_0 in |- *. intros. elim (predta_coacc_fix d a a H0). intros. apply (coacc_id (predta_kill_non_coacc d a) a s).
	unfold predta_kill_non_coacc in |- *. apply (non_coacc_kill_0 d a s (predta_coacc_states d a)). unfold predta_coacc_states in |- *.
	apply
  (power_def_ok bool (ensemble_base state d) (predta_coacc d a)
     (map_mini state d) (S (MapCard state d))). unfold def_ok_app in |- *.
	intros. exact (predta_coacc_def_ok d a x). exact (map_mini_appartient state d). exact H. exact (H3 H1).
Qed.

Lemma predta_kill_non_coacc_2 :
 forall (d : preDTA) (a0 a1 a2 : ad) (s1 s2 : state) 
   (pl : prec_list) (c : ad),
 MapGet state d a2 = Some s2 ->
 MapGet state d a1 = Some s1 ->
 MapGet prec_list s1 c = Some pl ->
 prec_occur pl a2 ->
 coacc d a0 a1 ->
 predta_kill_non_coacc_def_0 d a0 a1 -> predta_kill_non_coacc_def_0 d a0 a2.
Proof.
	unfold predta_kill_non_coacc_def_0 in |- *. intros. apply (coacc_nxt (predta_kill_non_coacc d a0) a0 a1 a2 s1 s2 pl c). elim (predta_kill_non_coacc_0 d a0 a2 s2 H5). intros. apply H7.
	split. exact H. exact H6. elim (predta_kill_non_coacc_0 d a0 a1 s1 H5). intros. apply H7. split; assumption. exact H1. exact H2.
	exact (H4 H5 H3).
Qed.

Lemma predta_kill_non_coacc_3 :
 forall (d : preDTA) (a0 a1 : ad),
 preDTA_ref_ok d -> coacc d a0 a1 -> coacc (predta_kill_non_coacc d a0) a0 a1.
Proof.
	intros. exact
  (coacc_ind predta_kill_non_coacc_def_0 predta_kill_non_coacc_1
     predta_kill_non_coacc_2 d a0 a1 H0 H H0).
Qed.

(* sémantique de reconnaissance dans les coaccessibles *)

(* sens trivial : si un terme est reconnu par l'automate où on a kille
les non coaccessibles alors il est reconnu dans l automate *)

Definition predta_kill_non_coacc_rec_def_0 (p : preDTA) 
  (a : ad) (t : term) (pr : reconnaissance p a t) :=
  forall (p0 : preDTA) (m : Map bool),
  p = non_coacc_kill p0 m ->
  ensemble_base state p0 m -> reconnaissance p0 a t.

Definition predta_kill_non_coacc_rec_def_1 (p : preDTA) 
  (s : state) (t : term) (pr : state_reconnait p s t) :=
  forall (p0 : preDTA) (m : Map bool),
  p = non_coacc_kill p0 m ->
  ensemble_base state p0 m -> state_reconnait p0 s t.

Definition predta_kill_non_coacc_rec_def_2 (p : preDTA) 
  (pl : prec_list) (lt : term_list) (pr : liste_reconnait p pl lt) :=
  forall (p0 : preDTA) (m : Map bool),
  p = non_coacc_kill p0 m ->
  ensemble_base state p0 m -> liste_reconnait p0 pl lt.

Lemma predta_kill_non_coacc_rec_0 :
 forall (d : preDTA) (a : ad) (t : term) (ladj : state)
   (e : MapGet state d a = Some ladj) (s : state_reconnait d ladj t),
 predta_kill_non_coacc_rec_def_1 d ladj t s ->
 predta_kill_non_coacc_rec_def_0 d a t (rec_dta d a t ladj e s).
Proof.
	unfold predta_kill_non_coacc_rec_def_1, predta_kill_non_coacc_rec_def_0
  in |- *.
	intros. rewrite H0 in e. apply (rec_dta p0 a t ladj). elim (non_coacc_kill_1 _ _ _ _ H1 e). intros. exact H2. exact (H _ _ H0 H1).
Qed.

Lemma predta_kill_non_coacc_rec_1 :
 forall (d : preDTA) (s : state) (c : ad) (tl : term_list) 
   (l : prec_list) (e : MapGet prec_list s c = Some l)
   (l0 : liste_reconnait d l tl),
 predta_kill_non_coacc_rec_def_2 d l tl l0 ->
 predta_kill_non_coacc_rec_def_1 d s (app c tl) (rec_st d s c tl l e l0).
Proof.
	unfold predta_kill_non_coacc_rec_def_1, predta_kill_non_coacc_rec_def_2
  in |- *.
	intros. exact (rec_st p0 s c tl l e (H _ _ H0 H1)).
Qed.

Lemma predta_kill_non_coacc_rec_2 :
 forall d : preDTA,
 predta_kill_non_coacc_rec_def_2 d prec_empty tnil (rec_empty d).
Proof.
	unfold predta_kill_non_coacc_rec_def_2 in |- *. intros.
	exact (rec_empty p0).
Qed.

Lemma predta_kill_non_coacc_rec_3 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list) (r : reconnaissance d a hd),
 predta_kill_non_coacc_rec_def_0 d a hd r ->
 forall l : liste_reconnait d la tl,
 predta_kill_non_coacc_rec_def_2 d la tl l ->
 predta_kill_non_coacc_rec_def_2 d (prec_cons a la ls) 
   (tcons hd tl) (rec_consi d a la ls hd tl r l).
Proof.
	unfold predta_kill_non_coacc_rec_def_0, predta_kill_non_coacc_rec_def_2
  in |- *.
	intros. exact (rec_consi p0 a la ls hd tl (H _ _ H1 H2) (H0 _ _ H1 H2)).
Qed.

Lemma predta_kill_non_coacc_rec_4 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list) (l : liste_reconnait d ls (tcons hd tl)),
 predta_kill_non_coacc_rec_def_2 d ls (tcons hd tl) l ->
 predta_kill_non_coacc_rec_def_2 d (prec_cons a la ls) 
   (tcons hd tl) (rec_consn d a la ls hd tl l).
Proof.
	unfold predta_kill_non_coacc_rec_def_2 in |- *. intros.
	exact (rec_consn p0 a la ls hd tl (H _ _ H0 H1)).
Qed.

Lemma predta_kill_non_coacc_rev :
 forall (p : preDTA) (a : ad) (t : term) (m : Map bool),
 reconnaissance (non_coacc_kill p m) a t ->
 ensemble_base state p m -> reconnaissance p a t.
Proof.
	intros. exact
  (mreconnaissance_ind predta_kill_non_coacc_rec_def_0
     predta_kill_non_coacc_rec_def_1 predta_kill_non_coacc_rec_def_2
     predta_kill_non_coacc_rec_0 predta_kill_non_coacc_rec_1
     predta_kill_non_coacc_rec_2 predta_kill_non_coacc_rec_3
     predta_kill_non_coacc_rec_4 (non_coacc_kill p m) a t H p m
     (refl_equal (non_coacc_kill p m)) H0).
Qed.

(* sens moins trivial : si un terme est reconnu par ... *)

Inductive reconnaissance_co : preDTA -> ad -> ad -> term -> Prop :=
    rec_co_dta :
      forall (d : preDTA) (a b : ad) (t : term) (ladj : state),
      MapGet state d a = Some ladj ->
      state_reconnait_co d ladj b t ->
      coacc d b a -> reconnaissance_co d a b t
with state_reconnait_co : preDTA -> state -> ad -> term -> Prop :=
    rec_co_st :
      forall (d : preDTA) (s : state) (c b : ad) (tl : term_list)
        (l : prec_list),
      MapGet prec_list s c = Some l ->
      liste_reconnait_co d l b tl -> state_reconnait_co d s b (app c tl)
with liste_reconnait_co : preDTA -> prec_list -> ad -> term_list -> Prop :=
  | rec_co_empty :
      forall (d : preDTA) (b : ad), liste_reconnait_co d prec_empty b tnil
  | rec_co_consi :
      forall (d : preDTA) (a : ad) (la ls : prec_list) 
        (hd : term) (b : ad) (tl : term_list),
      reconnaissance_co d a b hd ->
      liste_reconnait_co d la b tl ->
      liste_reconnait_co d (prec_cons a la ls) b (tcons hd tl)
  | rec_co_consn :
      forall (d : preDTA) (a : ad) (la ls : prec_list) 
        (hd : term) (b : ad) (tl : term_list),
      liste_reconnait_co d ls b (tcons hd tl) ->
      liste_reconnait_co d (prec_cons a la ls) b (tcons hd tl).

Scheme mreconnaissance_co_ind := Induction for reconnaissance_co
  Sort Prop
  with mstrec_co_ind := Induction for state_reconnait_co
  Sort Prop
  with mlrec_co_ind := Induction for liste_reconnait_co 
  Sort Prop.

Definition rec_co_def_0 (d : preDTA) (a a1 : ad) (t : term)
  (pr : reconnaissance_co d a a1 t) :=
  forall a0 : ad, coacc d a0 a1 -> reconnaissance_co d a a0 t.

Definition rec_co_def_1 (d : preDTA) (s : state) (a1 : ad) 
  (t : term) (pr : state_reconnait_co d s a1 t) :=
  forall a0 : ad, coacc d a0 a1 -> state_reconnait_co d s a0 t.

Definition rec_co_def_2 (d : preDTA) (p : prec_list) 
  (a1 : ad) (tl : term_list) (pr : liste_reconnait_co d p a1 tl) :=
  forall a0 : ad, coacc d a0 a1 -> liste_reconnait_co d p a0 tl.

Lemma rec_co_0 :
 forall (d : preDTA) (a b : ad) (t : term) (ladj : state)
   (e : MapGet state d a = Some ladj)
   (s : state_reconnait_co d ladj b t),
 rec_co_def_1 d ladj b t s ->
 forall c : coacc d b a, rec_co_def_0 d a b t (rec_co_dta d a b t ladj e s c).
Proof.
	unfold rec_co_def_1, rec_co_def_0 in |- *. intros. exact (rec_co_dta d a a0 t ladj e (H _ H0) (coacc_transitive _ _ _ _ H0 c)).
Qed.

Lemma rec_co_1 :
 forall (d : preDTA) (s : state) (c b : ad) (tl : term_list) 
   (l : prec_list) (e : MapGet prec_list s c = Some l)
   (l0 : liste_reconnait_co d l b tl),
 rec_co_def_2 d l b tl l0 ->
 rec_co_def_1 d s b (app c tl) (rec_co_st d s c b tl l e l0).
Proof.
	unfold rec_co_def_2, rec_co_def_1 in |- *. intros. exact (rec_co_st d s c a0 tl l e (H _ H0)).
Qed.

Lemma rec_co_2 :
 forall (d : preDTA) (b : ad),
 rec_co_def_2 d prec_empty b tnil (rec_co_empty d b).
Proof.
	unfold rec_co_def_2 in |- *. intros. exact (rec_co_empty d a0).
Qed.

Lemma rec_co_3 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) 
   (b : ad) (tl : term_list) (r : reconnaissance_co d a b hd),
 rec_co_def_0 d a b hd r ->
 forall l : liste_reconnait_co d la b tl,
 rec_co_def_2 d la b tl l ->
 rec_co_def_2 d (prec_cons a la ls) b (tcons hd tl)
   (rec_co_consi d a la ls hd b tl r l).
Proof.
	unfold rec_co_def_0, rec_co_def_2 in |- *. intros. exact (rec_co_consi d a la ls hd a0 tl (H _ H1) (H0 _ H1)).
Qed.

Lemma rec_co_4 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) 
   (b : ad) (tl : term_list) (l : liste_reconnait_co d ls b (tcons hd tl)),
 rec_co_def_2 d ls b (tcons hd tl) l ->
 rec_co_def_2 d (prec_cons a la ls) b (tcons hd tl)
   (rec_co_consn d a la ls hd b tl l).
Proof.
	unfold rec_co_def_2 in |- *. intros. exact (rec_co_consn d a la ls hd a0 tl (H _ H0)).
Qed.

Lemma rec_co_5 :
 forall (d : preDTA) (a a0 a1 : ad) (t : term),
 reconnaissance_co d a a1 t -> coacc d a0 a1 -> reconnaissance_co d a a0 t.
Proof.
	intros. exact
  (mreconnaissance_co_ind rec_co_def_0 rec_co_def_1 rec_co_def_2 rec_co_0
     rec_co_1 rec_co_2 rec_co_3 rec_co_4 d a a1 t H a0 H0).
Qed.

Definition rec_co_def_3 (t : term) : Prop :=
  forall (d : preDTA) (a : ad),
  preDTA_ref_ok d -> reconnaissance d a t -> reconnaissance_co d a a t.

Definition rec_co_def_4 (d : preDTA) (l : prec_list) 
  (tl : term_list) : Prop :=
  forall a : ad,
  preDTA_ref_ok d ->
  liste_reconnait d l tl ->
  (forall u : term,
   term_list_occur u tl ->
   forall (d : preDTA) (a : ad),
   preDTA_ref_ok d -> reconnaissance d a u -> reconnaissance_co d a a u) ->
  (forall b : ad, prec_occur l b -> coacc d a b) ->
  liste_reconnait_co d l a tl.

Lemma rec_co_6 : forall d : preDTA, rec_co_def_4 d prec_empty tnil.
Proof.
	unfold rec_co_def_4 in |- *. intros. exact (rec_co_empty d a).
Qed.

Lemma rec_co_7 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list),
 reconnaissance d a hd ->
 liste_reconnait d la tl ->
 rec_co_def_4 d la tl -> rec_co_def_4 d (prec_cons a la ls) (tcons hd tl).
Proof.
	unfold rec_co_def_4 in |- *. intros. apply (rec_co_consi d a la ls hd a0 tl).
	exact
  (rec_co_5 d a a0 a hd (H4 hd (tlo_head hd hd tl (to_eq hd)) d a H2 H)
     (H5 a (prec_hd a la ls))). apply (H1 a0 H2 H0). intros. exact (H4 u (tlo_tail u hd tl H6) d0 a1 H7 H8). intros. exact (H5 _ (prec_int0 a b la ls H6)).
Qed.

Lemma rec_co_8 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list),
 liste_reconnait d ls (tcons hd tl) ->
 rec_co_def_4 d ls (tcons hd tl) ->
 rec_co_def_4 d (prec_cons a la ls) (tcons hd tl).
Proof.
	unfold rec_co_def_4 in |- *. intros. apply (rec_co_consn d a la ls hd a0 tl).
	apply (H0 a0 H1 H). intros. exact (H3 u H5 d0 a1 H6 H7). intros.
	exact (H4 b (prec_int1 a b la ls H5)).
Qed.

Lemma rec_co_9 :
 forall (d : preDTA) (tl : term_list) (a : ad) (l : prec_list),
 liste_reconnait d l tl ->
 (forall u : term,
  term_list_occur u tl ->
  forall (d : preDTA) (a : ad),
  preDTA_ref_ok d -> reconnaissance d a u -> reconnaissance_co d a a u) ->
 (forall b : ad, prec_occur l b -> coacc d a b) ->
 preDTA_ref_ok d -> liste_reconnait_co d l a tl.
Proof.
	intros. exact
  (liste_reconnait_ind rec_co_def_4 rec_co_6 rec_co_7 rec_co_8 d l tl H a H2
     H H0 H1).
Qed.

Lemma rec_co_10 :
 forall (a : ad) (tl : term_list),
 (forall u : term, term_list_occur u tl -> rec_co_def_3 u) ->
 rec_co_def_3 (app a tl).
Proof.
	unfold rec_co_def_3 in |- *. intros. inversion H1. inversion H3.
	apply (rec_co_dta d a0 a0 (app a tl) ladj H2). apply (rec_co_st d ladj a a0 tl l H11). apply (rec_co_9 d tl a0 l H12 H). intros. elim (H0 a0 ladj a l b H2 H11 H13). intros.
	exact
  (coacc_nxt d a0 a0 b ladj x l a H14 H2 H11 H13 (coacc_id d a0 ladj H2)). exact H0. exact (coacc_id _ _ _ H2).
Qed.

Lemma rec_co :
 forall (d : preDTA) (a : ad) (t : term),
 preDTA_ref_ok d -> reconnaissance d a t -> reconnaissance_co d a a t.
Proof.
	intros. exact (indprinciple_term rec_co_def_3 rec_co_10 t d a H H0). 
Qed.

Definition rec_co_rec_def_0 (d : preDTA) (a a0 : ad) 
  (t : term) (pr : reconnaissance_co d a a0 t) := reconnaissance d a t.

Definition rec_co_rec_def_1 (d : preDTA) (s : state) 
  (a0 : ad) (t : term) (pr : state_reconnait_co d s a0 t) :=
  state_reconnait d s t.

Definition rec_co_rec_def_2 (d : preDTA) (p : prec_list) 
  (a0 : ad) (tl : term_list) (pr : liste_reconnait_co d p a0 tl) :=
  liste_reconnait d p tl.

Lemma rec_co_rec_0 :
 forall (d : preDTA) (a b : ad) (t : term) (ladj : state)
   (e : MapGet state d a = Some ladj)
   (s : state_reconnait_co d ladj b t),
 rec_co_rec_def_1 d ladj b t s ->
 forall c : coacc d b a,
 rec_co_rec_def_0 d a b t (rec_co_dta d a b t ladj e s c).
Proof.
	unfold rec_co_rec_def_0, rec_co_rec_def_1 in |- *. intros. exact (rec_dta d a t ladj e H).
Qed.

Lemma rec_co_rec_1 :
 forall (d : preDTA) (s : state) (c b : ad) (tl : term_list) 
   (l : prec_list) (e : MapGet prec_list s c = Some l)
   (l0 : liste_reconnait_co d l b tl),
 rec_co_rec_def_2 d l b tl l0 ->
 rec_co_rec_def_1 d s b (app c tl) (rec_co_st d s c b tl l e l0).
Proof.
	unfold rec_co_rec_def_1, rec_co_rec_def_2 in |- *. intros. exact (rec_st d s c tl l e H).
Qed.

Lemma rec_co_rec_2 :
 forall (d : preDTA) (b : ad),
 rec_co_rec_def_2 d prec_empty b tnil (rec_co_empty d b).
Proof.
	unfold rec_co_rec_def_2 in |- *. intros. exact (rec_empty d).
Qed.

Lemma rec_co_rec_3 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) 
   (b : ad) (tl : term_list) (r : reconnaissance_co d a b hd),
 rec_co_rec_def_0 d a b hd r ->
 forall l : liste_reconnait_co d la b tl,
 rec_co_rec_def_2 d la b tl l ->
 rec_co_rec_def_2 d (prec_cons a la ls) b (tcons hd tl)
   (rec_co_consi d a la ls hd b tl r l).
Proof.
	unfold rec_co_rec_def_0, rec_co_rec_def_2 in |- *. intros.
	exact (rec_consi d a la ls hd tl H H0).
Qed.

Lemma rec_co_rec_4 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) 
   (b : ad) (tl : term_list) (l : liste_reconnait_co d ls b (tcons hd tl)),
 rec_co_rec_def_2 d ls b (tcons hd tl) l ->
 rec_co_rec_def_2 d (prec_cons a la ls) b (tcons hd tl)
   (rec_co_consn d a la ls hd b tl l).
Proof.
	unfold rec_co_rec_def_2 in |- *. intros. exact (rec_consn d a la ls hd tl H).
Qed.

Lemma rec_co_rec :
 forall (d : preDTA) (a a0 : ad) (t : term),
 reconnaissance_co d a a0 t -> reconnaissance d a t.
Proof.
	exact
  (mreconnaissance_co_ind rec_co_rec_def_0 rec_co_rec_def_1 rec_co_rec_def_2
     rec_co_rec_0 rec_co_rec_1 rec_co_rec_2 rec_co_rec_3 rec_co_rec_4).
Qed.

Definition rec_nonco_kill_def_0 (d : preDTA) (a a0 : ad) 
  (t : term) (pr : reconnaissance_co d a a0 t) :=
  preDTA_ref_ok d -> reconnaissance_co (predta_kill_non_coacc d a0) a a0 t.

Definition rec_nonco_kill_def_1 (d : preDTA) (s : state) 
  (a0 : ad) (t : term) (pr : state_reconnait_co d s a0 t) :=
  preDTA_ref_ok d -> state_reconnait_co (predta_kill_non_coacc d a0) s a0 t.

Definition rec_nonco_kill_def_2 (d : preDTA) (p : prec_list) 
  (a0 : ad) (tl : term_list) (pr : liste_reconnait_co d p a0 tl) :=
  preDTA_ref_ok d -> liste_reconnait_co (predta_kill_non_coacc d a0) p a0 tl.

Lemma rec_nonco_kill_0 :
 forall (d : preDTA) (a b : ad) (t : term) (ladj : state)
   (e : MapGet state d a = Some ladj)
   (s : state_reconnait_co d ladj b t),
 rec_nonco_kill_def_1 d ladj b t s ->
 forall c : coacc d b a,
 rec_nonco_kill_def_0 d a b t (rec_co_dta d a b t ladj e s c).
Proof.
	unfold rec_nonco_kill_def_0, rec_nonco_kill_def_1 in |- *. intros.
	apply (rec_co_dta (predta_kill_non_coacc d b) a b t ladj).
	unfold predta_kill_non_coacc in |- *. apply (non_coacc_kill_0 d a ladj (predta_coacc_states d b)). unfold predta_coacc_states in |- *. apply
  (power_def_ok bool (ensemble_base state d) (predta_coacc d b)
     (map_mini state d) (S (MapCard state d))). unfold def_ok_app in |- *.
	intros. exact (predta_coacc_def_ok d b x). exact (map_mini_appartient state d). exact e. elim (predta_coacc_fix d b a H0). intros.
	exact (H2 c). exact (H H0). exact (predta_kill_non_coacc_3 _ _ _ H0 c).
Qed.

Lemma rec_nonco_kill_1 :
 forall (d : preDTA) (s : state) (c b : ad) (tl : term_list) 
   (l : prec_list) (e : MapGet prec_list s c = Some l)
   (l0 : liste_reconnait_co d l b tl),
 rec_nonco_kill_def_2 d l b tl l0 ->
 rec_nonco_kill_def_1 d s b (app c tl) (rec_co_st d s c b tl l e l0).
Proof.
	unfold rec_nonco_kill_def_1, rec_nonco_kill_def_2 in |- *. intros.
	exact (rec_co_st (predta_kill_non_coacc d b) s c b tl l e (H H0)).
Qed.

Lemma rec_nonco_kill_2 :
 forall (d : preDTA) (b : ad),
 rec_nonco_kill_def_2 d prec_empty b tnil (rec_co_empty d b).
Proof.
	unfold rec_nonco_kill_def_2 in |- *. intros. exact (rec_co_empty (predta_kill_non_coacc d b) b).
Qed.

Lemma rec_nonco_kill_3 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) 
   (b : ad) (tl : term_list) (r : reconnaissance_co d a b hd),
 rec_nonco_kill_def_0 d a b hd r ->
 forall l : liste_reconnait_co d la b tl,
 rec_nonco_kill_def_2 d la b tl l ->
 rec_nonco_kill_def_2 d (prec_cons a la ls) b (tcons hd tl)
   (rec_co_consi d a la ls hd b tl r l).
Proof.
	unfold rec_nonco_kill_def_0, rec_nonco_kill_def_2 in |- *. intros.
	exact
  (rec_co_consi (predta_kill_non_coacc d b) a la ls hd b tl (H H1) (H0 H1)).
Qed.

Lemma rec_nonco_kill_4 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) 
   (b : ad) (tl : term_list) (l : liste_reconnait_co d ls b (tcons hd tl)),
 rec_nonco_kill_def_2 d ls b (tcons hd tl) l ->
 rec_nonco_kill_def_2 d (prec_cons a la ls) b (tcons hd tl)
   (rec_co_consn d a la ls hd b tl l).
Proof.
	unfold rec_nonco_kill_def_2 in |- *. intros. exact (rec_co_consn _ a la ls hd b tl (H H0)).
Qed.

Lemma rec_nonco_kill :
 forall (d : preDTA) (a a0 : ad) (t : term),
 reconnaissance_co d a a0 t ->
 preDTA_ref_ok d -> reconnaissance_co (predta_kill_non_coacc d a0) a a0 t.
Proof.
	intros. exact
  (mreconnaissance_co_ind rec_nonco_kill_def_0 rec_nonco_kill_def_1
     rec_nonco_kill_def_2 rec_nonco_kill_0 rec_nonco_kill_1 rec_nonco_kill_2
     rec_nonco_kill_3 rec_nonco_kill_4 d a a0 t H H0).
Qed.

Lemma predta_kill_non_coacc_dir :
 forall (d : preDTA) (a : ad) (t : term),
 preDTA_ref_ok d ->
 reconnaissance d a t ->
 reconnaissance (non_coacc_kill d (predta_coacc_states d a)) a t.
Proof.
	intros. exact (rec_co_rec _ _ _ _ (rec_nonco_kill d a a t (rec_co d a t H H0) H)).
Qed.

(* sémantique du kill non coacc states : *)

Lemma predta_kill_non_coacc_semantics :
 forall (d : DTA) (t : term),
 DTA_ref_ok d -> (reconnait d t <-> reconnait (dta_kill_non_coacc d) t).
Proof.
	simple induction d. simpl in |- *. intros. split. exact (predta_kill_non_coacc_dir p a t H).
	unfold predta_kill_non_coacc in |- *. intros. apply (predta_kill_non_coacc_rev p a t (predta_coacc_states p a) H0). unfold predta_coacc_states in |- *. apply
  (power_def_ok bool (ensemble_base state p) (predta_coacc p a)
     (map_mini state p) (S (MapCard state p))). unfold def_ok_app in |- *. intros. exact (predta_coacc_def_ok p a x). exact (map_mini_appartient state p).
Qed.

Lemma predta_kill_non_coacc_lazy_semantics :
 forall (d : DTA) (t : term),
 DTA_ref_ok d -> (reconnait d t <-> reconnait (dta_kill_non_coacc_lazy d) t).
Proof.
	intros. rewrite (kill_non_coacc_lazy_eq_kill_non_coacc d).
	exact (predta_kill_non_coacc_semantics d t H).
Qed.