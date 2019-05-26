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


Require Import Classical_Prop.
Require Import Bool.
Require Import Arith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import bases.

Fixpoint domain_equal (A B : Set) (m0 : Map A) (m1 : Map B) {struct m1} :
 Prop :=
  match m0, m1 with
  | M0, M0 => True
  | M0, M1 _ _ => False
  | M0, M2 _ _ => False
  | M1 _ _, M0 => False
  | M1 a _, M1 b _ => a = b
  | M1 _ _, M2 _ _ => False
  | M2 _ _, M0 => False
  | M2 _ _, M1 _ _ => False
  | M2 a b, M2 c d => domain_equal A B a c /\ domain_equal A B b d
  end.

Lemma domain_equal_mapget :
 forall (A B : Set) (m0 : Map A) (m1 : Map B) (a : ad) (x : A),
 domain_equal A B m0 m1 ->
 MapGet A m0 a = Some x -> exists y : B, MapGet B m1 a = Some y.
Proof.
	simple induction m0. intros. inversion H0. intros. induction  m1 as [| a2 a3| m1_1 Hrecm1_1 m1_0 Hrecm1_0]. inversion H.
	simpl in H0. simpl in H. elim (bool_is_true_or_false (Neqb a a1)); intros; rewrite H1 in H0. inversion H0. simpl in |- *. rewrite <- H. rewrite H1.
	split with a3. reflexivity. inversion H0. inversion H. simple induction m2.
	intros. inversion H1. intros. inversion H1. intros. elim H3. intros.
	induction  a as [| p]. simpl in |- *. exact (H _ _ _ H5 H4). induction  p as [p Hrecp| p Hrecp| ]. simpl in |- *. simpl in H4.
	exact (H0 _ _ _ H6 H4). simpl in H4. simpl in |- *. exact (H _ _ _ H5 H4). simpl in |- *.
	simpl in H4. exact (H0 _ _ _ H6 H4).
Qed.

Lemma domain_equal_reflexive :
 forall (A : Set) (m : Map A), domain_equal A A m m.
Proof.
	intros. induction  m as [| a a0| m1 Hrecm1 m0 Hrecm0]. exact I. simpl in |- *. reflexivity. split.
	exact Hrecm1. exact Hrecm0.
Qed.

Lemma domain_equal_symmetric :
 forall (A B : Set) (m0 : Map A) (m1 : Map B),
 domain_equal A B m0 m1 -> domain_equal B A m1 m0.
Proof.
	simple induction m0. simple induction m1. intros. exact I. intros. inversion H.
	intros. inversion H1. simple induction m1; intros. inversion H. simpl in H.
	simpl in |- *. exact (sym_eq H). inversion H1. simple induction m2; intros.
	inversion H1. inversion H1. simpl in |- *. elim H3; intros. split. exact (H _ H4). exact (H0 _ H5).
Qed.

Lemma domain_equal_transitive :
 forall (A0 A1 A2 : Set) (m0 : Map A0) (m1 : Map A1) (m2 : Map A2),
 domain_equal A0 A1 m0 m1 ->
 domain_equal A1 A2 m1 m2 -> domain_equal A0 A2 m0 m2.
Proof.
	intro. intro. intro. simple induction m0. simple induction m1. simple induction m2.
	intros. exact I. intros. inversion H0. intros. inversion H2.
	intros. inversion H. intros. inversion H1. intro. intro.
	simple induction m1. intros. inversion H. simple induction m2. intros.
	inversion H0. intros. simpl in H. simpl in H0. rewrite H.
	rewrite H0. simpl in |- *. reflexivity. intros. inversion H2. intros.
	inversion H1. simple induction m2. intros. inversion H1. intros.
	inversion H1. simple induction m5. intros. inversion H4. intros.
	inversion H4. intros. simpl in |- *. simpl in H5. simpl in H6.
	elim H5. elim H6. intros. split. exact (H _ _ H9 H7).
	exact (H0 _ _ H10 H8).
Qed.

Lemma map_sum :
 forall (A : Set) (m : Map A),
 m = M0 A \/
 (exists a : ad, (exists x : A, m = M1 A a x)) \/
 (exists x : Map A, (exists y : Map A, m = M2 A x y)).
Proof.
	intros. induction  m as [| a a0| m1 Hrecm1 m0 Hrecm0]. left. reflexivity. right.
	left. split with a. split with a0. reflexivity.
	right. right. split with m1. split with m0. reflexivity.
Qed.

Definition mEnsemble (A : Set) := Map A -> Prop.

Definition mRelation (A : Set) := Map A -> Map A -> Prop.

Definition r_symmetric (A : Set) (r : mRelation A) :=
  forall x y : Map A, r x y -> r y x.

Definition r_antisymmetric (A : Set) (r : mRelation A) :=
  forall x y : Map A, r x y -> r y x -> x = y.

Definition r_transitive (A : Set) (r : mRelation A) :=
  forall x y z : Map A, r x y -> r y z -> r x z.

Definition r_reflexive (A : Set) (r : mRelation A) := forall x : Map A, r x x.

Definition r_order (A : Set) (r : mRelation A) :=
  r_reflexive A r /\ r_antisymmetric A r /\ r_transitive A r.

Definition mini (A : Set) (r : mRelation A) (T : mEnsemble A) 
  (e : Map A) := T e /\ (forall x : Map A, T x -> r e x).

Definition maxi (A : Set) (r : mRelation A) (T : mEnsemble A) 
  (e : Map A) := T e /\ (forall x : Map A, T x -> r x e).

Definition mLattice (A : Set) (r : mRelation A) (T : mEnsemble A)
  (e f : Map A) := r_order A r /\ mini A r T e /\ maxi A r T f.

Inductive prechain (A : Set) : Set :=
  | single : Map A -> prechain A
  | concat : prechain A -> Map A -> prechain A.

Lemma prechain_sum :
 forall (A : Set) (p : prechain A),
 (exists x : Map A, p = single A x) \/
 (exists x : Map A, (exists y : prechain A, p = concat A y x)).
Proof.
	intros. induction  p as [m| p Hrecp m]. left. split with m. reflexivity. right.
	split with m. split with p. reflexivity.
Qed.

Inductive prechain_dom_ok (A : Set) : mEnsemble A -> prechain A -> Prop :=
  | domok_single :
      forall (x : Map A) (T : mEnsemble A),
      T x -> prechain_dom_ok A T (single A x)
  | domok_concat :
      forall (x : Map A) (T : mEnsemble A) (p : prechain A),
      T x -> prechain_dom_ok A T p -> prechain_dom_ok A T (concat A p x).

Fixpoint chain_length (A : Set) (p : prechain A) {struct p} : nat :=
  match p with
  | single x => 1
  | concat x y => S (chain_length A x)
  end.

Definition prechain_last (A : Set) (p : prechain A) : 
  Map A := match p with
           | single x => x
           | concat z x => x
           end.

Inductive prechain_incr (A : Set) : mRelation A -> prechain A -> Prop :=
  | incr_single :
      forall (x : Map A) (r : mRelation A), prechain_incr A r (single A x)
  | incr_concat :
      forall (x : Map A) (r : mRelation A) (p : prechain A),
      r (prechain_last A p) x ->
      prechain_incr A r p -> prechain_incr A r (concat A p x).

Inductive chain (A : Set) :
mEnsemble A -> mRelation A -> prechain A -> Prop :=
  | chain_single :
      forall (x : Map A) (T : mEnsemble A) (r : mRelation A),
      T x -> chain A T r (single A x)
  | chain_concat_s :
      forall (x y : Map A) (T : mEnsemble A) (r : mRelation A),
      T x -> T y -> r x y -> chain A T r (concat A (single A x) y)
  | chain_concat_m :
      forall (x y : Map A) (z : prechain A) (T : mEnsemble A)
        (r : mRelation A),
      T y ->
      r x y ->
      chain A T r (concat A z x) -> chain A T r (concat A (concat A z x) y).

Lemma chain_def_ok :
 forall (A : Set) (T : mEnsemble A) (r : mRelation A) (p : prechain A),
 chain A T r p -> prechain_dom_ok A T p.
Proof.
	intros. induction  p as [m| p Hrecp m]. inversion H. exact (domok_single A m T H3). inversion H.
	exact (domok_concat A m T (single A x) H5 (domok_single A x T H2)). rewrite <- H0 in Hrecp. exact (domok_concat A m T (concat A z x) H2 (Hrecp H6)).
Qed.

Lemma chain_incr :
 forall (A : Set) (T : mEnsemble A) (r : mRelation A) (p : prechain A),
 chain A T r p -> prechain_incr A r p.
Proof.
	intros. induction  p as [m| p Hrecp m]. inversion H. exact (incr_single A m r). inversion H.
	apply (incr_concat A m r (single A x)). simpl in |- *. exact H6. exact (incr_single A x r).
	rewrite <- H0 in Hrecp. apply (incr_concat A m r (concat A z x)). simpl in |- *. exact H5.
	exact (Hrecp H6).
Qed.

Definition pre_domok_incr_chain_def (A : Set) (p : prechain A) :=
  forall (T : mEnsemble A) (r : mRelation A),
  prechain_dom_ok A T p /\ prechain_incr A r p -> chain A T r p.

Lemma pre_domok_incr_chain_0 :
 forall (A : Set) (m : Map A), pre_domok_incr_chain_def A (single A m).
Proof.
	unfold pre_domok_incr_chain_def in |- *. intros. elim H. intros. inversion H0. inversion H1.
	exact (chain_single A m T r H4).
Qed.

Lemma pre_domok_incr_chain_1 :
 forall (A : Set) (p : prechain A),
 pre_domok_incr_chain_def A p ->
 forall m : Map A, pre_domok_incr_chain_def A (concat A p m).
Proof.
	unfold pre_domok_incr_chain_def in |- *. intros. induction  p as [m0| p Hrecp m0]. elim H0. intros. inversion H1.
	inversion H2. inversion H7. simpl in H11. exact (chain_concat_s A m0 m T r H15 H6 H11). elim H0. intros. inversion H1. inversion H2. simpl in H11. apply (chain_concat_m A m0 m p T r H6 H11). apply (H T r). split; assumption.
Qed.

Lemma pre_domok_incr_chain_2 :
 forall (A : Set) (p : prechain A), pre_domok_incr_chain_def A p.
Proof.
	intro. exact
  (prechain_ind A (pre_domok_incr_chain_def A) (pre_domok_incr_chain_0 A)
     (pre_domok_incr_chain_1 A)).
Qed.

Lemma pre_domok_incr_chain :
 forall (A : Set) (p : prechain A) (T : mEnsemble A) (r : mRelation A),
 prechain_dom_ok A T p /\ prechain_incr A r p -> chain A T r p.
Proof.
	intro. exact
  (prechain_ind A (pre_domok_incr_chain_def A) (pre_domok_incr_chain_0 A)
     (pre_domok_incr_chain_1 A)).
Qed.

Inductive dist_chain (A : Set) : prechain A -> Prop :=
  | dist_single : forall x : Map A, dist_chain A (single A x)
  | dist_concat_s :
      forall x y : Map A, x <> y -> dist_chain A (concat A (single A x) y)
  | dist_concat_m :
      forall (x y : Map A) (z : prechain A),
      x <> y ->
      dist_chain A (concat A z x) -> dist_chain A (concat A (concat A z x) y).

Inductive non_dist_chain (A : Set) : prechain A -> Prop :=
  | non_dist_concat_s :
      forall x : Map A, non_dist_chain A (concat A (single A x) x)
  | non_dist_concat_m_hd :
      forall (x : Map A) (z : prechain A),
      non_dist_chain A (concat A (concat A z x) x)
  | non_dist_concat_m_tl :
      forall (x y : Map A) (z : prechain A),
      non_dist_chain A (concat A z x) ->
      non_dist_chain A (concat A (concat A z x) y).

Definition sas_chain (A : Set) (T : mEnsemble A) (r : mRelation A)
  (p : prechain A) : Prop := chain A T r p /\ dist_chain A p.

Definition dist_compl_def_0 (A : Set) (p : prechain A) : Prop :=
  dist_chain A p \/ non_dist_chain A p.

Lemma dist_compl_0 :
 forall (A : Set) (m : Map A), dist_compl_def_0 A (single A m).
Proof.
	unfold dist_compl_def_0 in |- *. intros. left. exact (dist_single A m).
Qed.

Definition dist_compl_def_1 (A : Set) (p : prechain A) : Prop :=
  dist_compl_def_0 A p -> forall m : Map A, dist_compl_def_0 A (concat A p m).

Lemma dist_compl_1 :
 forall (A : Set) (m : Map A), dist_compl_def_1 A (single A m).
Proof.
	unfold dist_compl_def_1 in |- *. intros. unfold dist_compl_def_0 in |- *. intros.
	elim (classic (m = m0)). intros. right. rewrite <- H0. exact (non_dist_concat_s A m). intros. left. exact (dist_concat_s A m m0 H0).
Qed.

Lemma dist_compl_2 :
 forall (A : Set) (p : prechain A),
 dist_compl_def_1 A p -> forall m : Map A, dist_compl_def_1 A (concat A p m).
Proof.
	unfold dist_compl_def_1 in |- *. unfold dist_compl_def_0 in |- *. intros.
	elim H0. intros. elim (classic (m = m0)). intro. right. rewrite H2.
	exact (non_dist_concat_m_hd A m0 p). intro. left. exact (dist_concat_m A m m0 p H2 H1). intros. right. exact (non_dist_concat_m_tl A m m0 p H1).
Qed.

Lemma dist_compl_3 :
 forall (A : Set) (p : prechain A),
 dist_compl_def_0 A p -> forall m : Map A, dist_compl_def_0 A (concat A p m).
Proof.
	intro. exact
  (prechain_ind A (dist_compl_def_1 A) (dist_compl_1 A) (dist_compl_2 A)).
Qed.

Lemma dist_compl_4 :
 forall (A : Set) (p : prechain A), dist_chain A p \/ non_dist_chain A p.
Proof.
	intro. exact
  (prechain_ind A (dist_compl_def_0 A) (dist_compl_0 A) (dist_compl_3 A)).
Qed.

Lemma dist_compl_5 :
 forall (A : Set) (x : Map A), ~ dist_chain A (concat A (single A x) x).
Proof.
	intros. intro. inversion H. exact (H1 (refl_equal x)).
Qed.

Lemma dist_compl_6 :
 forall (A : Set) (x : Map A) (z : prechain A),
 ~ dist_chain A (concat A (concat A z x) x).
Proof.
	intros. intro. inversion H. exact (H2 (refl_equal x)).
Qed.

Lemma dist_compl_7 :
 forall (A : Set) (x y : Map A) (z : prechain A),
 non_dist_chain A (concat A z x) ->
 ~ dist_chain A (concat A z x) -> ~ dist_chain A (concat A (concat A z x) y).
Proof.
	intros. intro. inversion H1. exact (H0 H6).
Qed.

Lemma dist_compl_8 :
 forall (A : Set) (p : prechain A), non_dist_chain A p -> ~ dist_chain A p.
Proof.
	exact
  (fun A : Set =>
   non_dist_chain_ind A (fun p : prechain A => ~ dist_chain A p)
     (dist_compl_5 A) (dist_compl_6 A) (dist_compl_7 A)).
Qed.

Lemma dist_compl :
 forall (A : Set) (p : prechain A), ~ dist_chain A p <-> non_dist_chain A p.
Proof.
	intros. split. intros. elim (dist_compl_4 A p); intros. elim (H H0).
	exact H0. exact (dist_compl_8 A p).
Qed.

(* propriété de chaine strictement croissante bornée *)

Definition bounded_sas_chain (A : Set) (T : mEnsemble A) 
  (r : mRelation A) (n : nat) : Prop :=
  forall p : prechain A, sas_chain A T r p -> chain_length A p <= n.

Definition def_ok_app (A : Set) (T : mEnsemble A) (f : Map A -> Map A) :
  Prop := forall x : Map A, T x -> T (f x).

Definition increasing_app (A : Set) (r : mRelation A) 
  (f : Map A -> Map A) : Prop := forall x y : Map A, r x y -> r (f x) (f y).

Definition fix_point (A : Set) (T : mEnsemble A) (f : Map A -> Map A)
  (x : Map A) : Prop := T x /\ f x = x.

Definition inf_fix_points (A : Set) (T : mEnsemble A) 
  (r : mRelation A) (f : Map A -> Map A) (x : Map A) : Prop :=
  forall y : Map A, fix_point A T f y -> r x y.

Definition lower_fix_point (A : Set) (T : mEnsemble A) 
  (r : mRelation A) (f : Map A -> Map A) (x : Map A) : Prop :=
  fix_point A T f x /\ inf_fix_points A T r f x.

(* itération d'une fonction *)

Fixpoint iteres (A : Set) (f : Map A -> Map A) (x : Map A) 
 (n : nat) {struct n} : prechain A :=
  match n with
  | O => single A x
  | S p =>
      match iteres A f x p with
      | single y => concat A (single A y) (f y)
      | concat z y => concat A (concat A z y) (f y)
      end
  end.

Fixpoint power (A : Set) (f : A -> A) (x : A) (n : nat) {struct n} : A :=
  match n with
  | O => x
  | S n => f (power A f x n)
  end.

Inductive MapFlag (A : Set) : Set :=
  | flag_true : Map A -> MapFlag A
  | flag_false : Map A -> MapFlag A.

Lemma MapFlag_sum :
 forall (A : Set) (f : MapFlag A),
 exists x : Map A, f = flag_true A x \/ f = flag_false A x.
Proof.
	intros. induction  f as [m| m]. split with m. left. reflexivity.
	split with m. right. reflexivity.
Qed.

Fixpoint lazy_power_aux (A : Set) (egalite : Map A -> Map A -> bool)
 (f : Map A -> Map A) (x : Map A) (n : nat) {struct n} : 
 MapFlag A :=
  match n with
  | O => flag_false A x
  | S p =>
      match lazy_power_aux A egalite f x p with
      | flag_true y => flag_true A y
      | flag_false y =>
          match f y with
          | z => if egalite y z then flag_true A y else flag_false A z
          end
      end
  end.

Definition lazy_power (A : Set) (egalite : Map A -> Map A -> bool)
  (f : Map A -> Map A) (x : Map A) (n : nat) : Map A :=
  match lazy_power_aux A egalite f x n with
  | flag_false z => z
  | flag_true z => z
  end.
 
Lemma lazy_power_eg_power_0 :
 forall (A : Set) (egalite : Map A -> Map A -> bool) 
   (f : Map A -> Map A) (x : Map A) (n : nat),
 (forall a b : Map A, egalite a b = true <-> a = b) ->
 forall z : Map A,
 (lazy_power_aux A egalite f x n = flag_true A z ->
  z = power (Map A) f x n /\ z = f z) /\
 (lazy_power_aux A egalite f x n = flag_false A z -> z = power (Map A) f x n).
Proof.
	simple induction n. intros. simpl in |- *. intros. split; intros; inversion H0.
	reflexivity. intros. simpl in |- *. intros. elim (MapFlag_sum A (lazy_power_aux A egalite f x n0)). intros. elim H1; intros; rewrite H2.
	split; intros. inversion H3. rewrite <- H5. elim (H H0 x0); intros.
	elim (H4 H2); intros. rewrite <- H7. split; exact H8. inversion H3.
	elim (bool_is_true_or_false (egalite x0 (f x0))); intros. rewrite H3.
	split. intros. inversion H4. rewrite <- H6. elim (H H0 x0). intros.
	rewrite <- (H7 H2). elim (H0 x0 (f x0)); intros. split; exact (H8 H3).
	intros. inversion H4. rewrite H3. split; intros. inversion H4.
	inversion H4. elim (H H0 x0). intros. rewrite <- (H7 H2). reflexivity.
Qed.

Lemma lazy_power_eg_power :
 forall (A : Set) (egalite : Map A -> Map A -> bool) 
   (f : Map A -> Map A) (x : Map A) (n : nat),
 (forall a b : Map A, egalite a b = true <-> a = b) ->
 lazy_power A egalite f x n = power (Map A) f x n.
Proof.
	intros. intros. unfold lazy_power in |- *. elim (MapFlag_sum A (lazy_power_aux A egalite f x n)). intros. elim H0; intros; rewrite H1. elim (lazy_power_eg_power_0 A egalite f x n H x0). intros. elim (H2 H1).
	intros. exact H4. elim (lazy_power_eg_power_0 A egalite f x n H x0).
	intros. exact (H3 H1).
Qed.

Fixpoint iteres_0 (A : Set) (f : Map A -> Map A) (x : Map A) 
 (n : nat) {struct n} : prechain A :=
  match n with
  | O => single A x
  | S p =>
      match iteres_0 A f x p with
      | single y => concat A (single A y) (power (Map A) f x (S p))
      | concat z y => concat A (concat A z y) (power (Map A) f x (S p))
      end
  end.

Lemma iteres_eq_0 :
 forall (A : Set) (f : Map A -> Map A) (x : Map A) (n : nat),
 prechain_last A (iteres A f x n) = power (Map A) f x n.
Proof.
	intros. induction  n as [| n Hrecn]. reflexivity. elim (prechain_sum A (iteres A f x n)); intros. elim H. intros. rewrite H0 in Hrecn. simpl in |- *.
	rewrite H0. simpl in |- *. simpl in Hrecn. rewrite Hrecn. reflexivity.
	elim H. intros. elim H0. intros. simpl in |- *. rewrite H1. rewrite H1 in Hrecn. simpl in |- *. simpl in Hrecn. rewrite Hrecn. reflexivity.
Qed.

Lemma iteres_eq :
 forall (A : Set) (f : Map A -> Map A) (x : Map A) (n : nat),
 iteres A f x n = iteres_0 A f x n.
Proof.
	intros. induction  n as [| n Hrecn]. reflexivity. simpl in |- *. rewrite <- (iteres_eq_0 A f x n). elim (prechain_sum A (iteres A f x n)); intros. elim H.
	intros. rewrite H0. rewrite H0 in Hrecn. rewrite Hrecn. rewrite <- Hrecn. reflexivity. elim H. intros. elim H0. intros. rewrite H1.
	rewrite H1 in Hrecn. rewrite <- Hrecn. reflexivity.
Qed.

Lemma iteres_def_ok :
 forall (A : Set) (T : mEnsemble A) (f : Map A -> Map A) 
   (x : Map A) (n k : nat),
 def_ok_app A T f -> T (power (Map A) f x n) -> T (power (Map A) f x (n + k)).
Proof.
	intros. induction  k as [| k Hreck]. rewrite (plus_comm n 0). simpl in |- *. exact H0.
	rewrite <- (plus_Snm_nSm n k). simpl in |- *. exact (H (power (Map A) f x (n + k)) Hreck).
Qed.

Lemma power_def_ok :
 forall (A : Set) (T : mEnsemble A) (f : Map A -> Map A) 
   (x : Map A) (n : nat), def_ok_app A T f -> T x -> T (power (Map A) f x n).
Proof.
	intros. replace n with (0 + n). apply (iteres_def_ok A T f x 0 n H). simpl in |- *. exact H0. simpl in |- *. reflexivity.
Qed.

Definition iteres_ult_const_def_0 (A : Set) (p : prechain A) : Prop :=
  forall (f : Map A -> Map A) (x : Map A) (n : nat),
  p = iteres A f x n ->
  non_dist_chain A p ->
  exists q : nat, S q <= n /\ power (Map A) f x q = power (Map A) f x (S q).

Lemma iteres_ult_const_0 :
 forall (A : Set) (x : Map A),
 iteres_ult_const_def_0 A (concat A (single A x) x).
Proof.
	unfold iteres_ult_const_def_0 in |- *. intros. elim (nat_sum n); intros.
	rewrite H1 in H. inversion H. elim H1. intros. rewrite H2 in H.
	elim (nat_sum x1); intros. rewrite H3 in H. simpl in H.
	inversion H. split with 0. rewrite H2. rewrite H3. split.
	exact (le_n_n _). simpl in |- *. rewrite <- H6. exact H6. elim H3.
	intros. rewrite H4 in H. simpl in H. elim (prechain_sum A (iteres A f x0 x2)); intros. elim H5. intros. rewrite H6 in H.
	inversion H. elim H5. intros. elim H6. intros. rewrite H7 in H.
	inversion H.
Qed.

Lemma iteres_ult_const_1 :
 forall (A : Set) (x : Map A) (z : prechain A),
 iteres_ult_const_def_0 A (concat A (concat A z x) x).
Proof.
	unfold iteres_ult_const_def_0 in |- *. intros. elim (nat_sum n); intros.
	rewrite H1 in H. inversion H. elim H1. intros. elim (nat_sum x1); intros. rewrite H3 in H2. rewrite H2 in H. simpl in H. inversion H.
	elim H3. intros. rewrite H4 in H2. rewrite H2 in H. rewrite (iteres_eq A f x0 (S (S x2))) in H. simpl in H. elim (prechain_sum A (iteres_0 A f x0 x2)); intros. elim H5. intros. rewrite H6 in H.
	inversion H. split with (S x2). rewrite H2. split. exact (le_n_n _).
	simpl in |- *. exact H10. elim H5. intros. elim H6. intros. rewrite H7 in H.
	inversion H. split with (S x2). rewrite H2. split. exact (le_n_n _).
	simpl in |- *. exact H11.
Qed.

Lemma iteres_ult_const_2 :
 forall (A : Set) (x y : Map A) (z : prechain A),
 non_dist_chain A (concat A z x) ->
 iteres_ult_const_def_0 A (concat A z x) ->
 iteres_ult_const_def_0 A (concat A (concat A z x) y).
Proof.
	unfold iteres_ult_const_def_0 in |- *. intros. elim (nat_sum n); intros.
	rewrite H3 in H1. inversion H1. elim H3. intros. elim (nat_sum x1); intros. rewrite H5 in H4. rewrite H4 in H1. inversion H1. elim H5.
	intros. rewrite H6 in H4. rewrite H4 in H1. elim (H0 f x0 (S x2)).
	intros. elim H7. intros. split with x3. split. rewrite H4.
	exact (le_trans (S x3) (S x2) (S (S x2)) H8 (le_n_Sn _)). exact H9.
	simpl in |- *. simpl in H1. elim (prechain_sum A (iteres A f x0 x2)); intros.
	elim H7. intros. rewrite H8 in H1. rewrite H8. inversion H1. 
	reflexivity. elim H7. intros. elim H8. intros. rewrite H9 in H1.
	rewrite H9. inversion H1. reflexivity. exact H.
Qed.

Lemma iteres_ult_const_3 :
 forall (A : Set) (p : prechain A),
 non_dist_chain A p -> iteres_ult_const_def_0 A p.
Proof.
	intro. exact
  (non_dist_chain_ind A (iteres_ult_const_def_0 A) 
     (iteres_ult_const_0 A) (iteres_ult_const_1 A) 
     (iteres_ult_const_2 A)).
Qed.

Lemma iteres_ult_const_4 :
 forall (A : Set) (f : Map A -> Map A) (x : Map A) (n : nat),
 non_dist_chain A (iteres A f x n) ->
 exists p : nat, S p <= n /\ power (Map A) f x p = power (Map A) f x (S p).
Proof.
	intros. exact (iteres_ult_const_3 A (iteres A f x n) H f x n (refl_equal _) H).
Qed.

Lemma iteres_last :
 forall (A : Set) (f : Map A -> Map A) (x : Map A) 
   (n : nat) (y : prechain A) (z : Map A),
 iteres A f x n = concat A y z -> z = f (prechain_last A y).
Proof.
	intros. elim (nat_sum n); intros. rewrite H0 in H. simpl in H.
	inversion H. elim H0. intros. rewrite H1 in H. simpl in H. elim (prechain_sum A (iteres A f x x0)). intros. elim H2. intros.
	rewrite H3 in H. inversion H. reflexivity. intros. elim H2. intros.
	elim H3. intros. rewrite H4 in H. inversion H. reflexivity.
Qed.

Lemma iteres_dom_ok :
 forall (A : Set) (T : mEnsemble A) (f : Map A -> Map A) 
   (x : Map A) (n : nat),
 T x -> def_ok_app A T f -> prechain_dom_ok A T (iteres A f x n).
Proof.
	intros. induction  n as [| n Hrecn]. simpl in |- *. exact (domok_single A x T H). simpl in |- *.
	elim (prechain_sum A (iteres A f x n)); intro. elim H1. intros.
	rewrite H2. rewrite H2 in Hrecn. inversion Hrecn. exact (domok_concat A (f x0) T (single A x0) (H0 x0 H5) Hrecn). elim H1. intros. elim H2.
	intros. rewrite H3. rewrite H3 in Hrecn. inversion Hrecn. exact (domok_concat A (f x0) T (concat A x1 x0) (H0 x0 H7) Hrecn).
Qed.

Lemma iteres_incr :
 forall (A : Set) (r : mRelation A) (f : Map A -> Map A) 
   (x : Map A) (n : nat),
 r x (f x) -> increasing_app A r f -> prechain_incr A r (iteres A f x n).
Proof.
	intros. induction  n as [| n Hrecn]. simpl in |- *. exact (incr_single A x r). elim (nat_sum n).
	intro. rewrite H1. simpl in |- *. rewrite H1 in Hrecn. inversion Hrecn.
	simpl in H4. apply (incr_concat A (f x) r (single A x)). simpl in |- *. exact H.
	simpl in Hrecn. exact Hrecn. intros. elim H1. intros. elim (prechain_sum A (iteres A f x n)). intros. elim H3. intros. rewrite H2 in H4. simpl in H4. elim (prechain_sum A (iteres A f x x0)); intro. elim H5. intros.
	rewrite H6 in H4. inversion H4. elim H5. intros. elim H6. intros.
	rewrite H7 in H4. inversion H4. intros. elim H3. intros. elim H4. intros.
	rewrite H5 in Hrecn. simpl in |- *. rewrite H5. inversion Hrecn. rewrite (iteres_last A f x n x2 x1 H5). rewrite (iteres_last A f x n x2 x1 H5) in H9. rewrite (iteres_last A f x n x2 x1 H5) in Hrecn. apply
  (incr_concat A (f (f (prechain_last A x2))) r
     (concat A x2 (f (prechain_last A x2)))).
	simpl in |- *. exact (H0 (prechain_last A x2) (f (prechain_last A x2)) H9).
	exact Hrecn.
Qed.

Lemma iteres_increasing_chain :
 forall (A : Set) (T : mEnsemble A) (r : mRelation A) 
   (f : Map A -> Map A) (x : Map A) (n : nat),
 T x ->
 def_ok_app A T f ->
 increasing_app A r f -> r x (f x) -> chain A T r (iteres A f x n).
Proof.
	intros. apply (pre_domok_incr_chain A (iteres A f x n) T r). split.
	exact (iteres_dom_ok A T f x n H H0). exact (iteres_incr A r f x n H2 H1).
Qed.

Lemma iteres_length :
 forall (A : Set) (f : Map A -> Map A) (x : Map A) (n : nat),
 chain_length A (iteres A f x n) = S n.
Proof.
	intros. induction  n as [| n Hrecn]. simpl in |- *. reflexivity. simpl in Hrecn.
	elim (prechain_sum A (iteres A f x n)). intro. elim H. intros.
	simpl in |- *. rewrite H0. simpl in |- *. rewrite H0 in Hrecn. simpl in Hrecn.
	rewrite <- Hrecn. reflexivity. intros. elim H. intros. elim H0.
	intros. simpl in |- *. rewrite H1. simpl in |- *. rewrite H1 in Hrecn. simpl in Hrecn. rewrite <- Hrecn. reflexivity.
Qed.

Lemma iteres_non_sas_chain :
 forall (A : Set) (T : mEnsemble A) (r : mRelation A) 
   (f : Map A -> Map A) (x : Map A) (n m : nat),
 T x ->
 def_ok_app A T f ->
 increasing_app A r f ->
 r x (f x) ->
 bounded_sas_chain A T r m ->
 m <= n -> chain A T r (iteres A f x n) /\ ~ dist_chain A (iteres A f x n).
Proof.
	intros. cut (chain A T r (iteres A f x n)). split. assumption. intro.
	apply (fun p : n < m => lt_not_le n m p H4). apply (lt_S_n n m). apply (le_lt_n_Sm (S n) m). rewrite <- (iteres_length A f x n). apply (H3 (iteres A f x n)). split; assumption. exact (iteres_increasing_chain A T r f x n H H0 H1 H2).
Qed.

Lemma iteres_non_sas_chain_fp_0 :
 forall (A : Set) (T : mEnsemble A) (r : mRelation A) 
   (f : Map A -> Map A) (x : Map A) (n m : nat),
 T x ->
 def_ok_app A T f ->
 increasing_app A r f ->
 r x (f x) ->
 bounded_sas_chain A T r m ->
 m <= n ->
 exists p : nat, S p <= n /\ power (Map A) f x p = power (Map A) f x (S p).
Proof.
	intros. elim (iteres_non_sas_chain A T r f x n m H H0 H1 H2 H3 H4).
	intros. apply (iteres_ult_const_4 A f x n). elim (dist_compl A (iteres A f x n)). intros. exact (H7 H6).
Qed.

Lemma iteres_non_sas_chain_fp_1 :
 forall (A : Set) (T : mEnsemble A) (f : Map A -> Map A) 
   (x : Map A) (k p : nat),
 def_ok_app A T f ->
 fix_point A T f (power (Map A) f x p) ->
 fix_point A T f (power (Map A) f x (p + k)).
Proof.
	intros. unfold fix_point in H0. induction  k as [| k Hreck]. rewrite (plus_comm p 0).
	simpl in |- *. exact H0. elim Hreck; intros. split. rewrite <- (plus_Snm_nSm p k). simpl in |- *. exact (H _ H1). rewrite <- (plus_Snm_nSm p k). simpl in |- *.
	rewrite H2. exact H2.
Qed.

Lemma iteres_non_sas_chain_fp_2 :
 forall (A : Set) (T : mEnsemble A) (r : mRelation A) 
   (f : Map A -> Map A) (x : Map A) (n m : nat),
 T x ->
 def_ok_app A T f ->
 increasing_app A r f ->
 r x (f x) ->
 bounded_sas_chain A T r m -> m <= n -> fix_point A T f (power (Map A) f x n).
Proof.
	intros. elim (iteres_non_sas_chain_fp_0 A T r f x n m H H0 H1 H2 H3 H4); intros. elim H5. intros. rewrite (le_plus_minus x0 n). split. apply (iteres_def_ok A T f x x0 (n - x0) H0). exact (iteres_def_ok A T f x 0 x0 H0 H). generalize (n - x0). intros. induction  n0 as [| n0 Hrecn0]. rewrite (plus_comm x0 0). simpl in |- *. simpl in H7. exact (sym_equal H7).
	rewrite <- (plus_Snm_nSm x0 n0). simpl in |- *. rewrite Hrecn0. exact Hrecn0.
	exact (le_trans _ _ _ (le_n_Sn x0) H6).
Qed.

Lemma iteres_inf_fps :
 forall (A : Set) (T : mEnsemble A) (r : mRelation A) 
   (f : Map A -> Map A) (e x : Map A) (n : nat),
 mini A r T e ->
 fix_point A T f x -> increasing_app A r f -> r (power (Map A) f e n) x.
Proof.
	intros. induction  n as [| n Hrecn]. simpl in |- *. elim H. intros. elim H0. intros.
	exact (H3 x H4). elim H. elim H0. intros. rewrite <- H3. simpl in |- *.
	exact (H1 _ _ Hrecn).
Qed.

Lemma iteres_lower_fix_point :
 forall (A : Set) (T : mEnsemble A) (r : mRelation A) 
   (f : Map A -> Map A) (e : Map A) (n m : nat),
 mini A r T e ->
 def_ok_app A T f ->
 increasing_app A r f ->
 bounded_sas_chain A T r m ->
 m <= n -> lower_fix_point A T r f (power (Map A) f e n).
Proof.
	intros. split. elim H. intros. apply (iteres_non_sas_chain_fp_2 A T r f e n m H4 H0 H1). exact (H5 (f e) (H0 e H4)). exact H2.
	exact H3. unfold inf_fix_points in |- *. intros. exact (iteres_inf_fps A T r f e y n H H4 H1).
Qed.

(* définition d'un ordre sur bool et sur le treillis des (Map bool) à domaine fixé*)

Definition leb (b0 b1 : bool) : Prop :=
  match b0, b1 with
  | false, false => True
  | false, true => True
  | true, false => False
  | true, true => True
  end.

Lemma leb_reflexive : forall b : bool, leb b b.
Proof.
	simple induction b; simpl in |- *; exact I.
Qed.

Lemma leb_antisymmetric : forall b c : bool, leb b c -> leb c b -> b = c.
Proof.
	simple induction b; simple induction c. intros. reflexivity. intros. elim H.
	intros. elim H0. intros. reflexivity.
Qed.

Lemma leb_transitive : forall a b c : bool, leb a b -> leb b c -> leb a c.
Proof.
	simple induction a; simple induction b. simple induction c. intros. exact I.
	intros. elim H0. intros. elim H. intros. induction  c as [| ]. exact I.
	elim H0. intros. induction  c as [| ]; exact I.
Qed.

Fixpoint lem (m0 m1 : Map bool) {struct m1} : Prop :=
  match m0, m1 with
  | M0, M0 => True
  | M0, M1 _ _ => False
  | M0, M2 _ _ => False
  | M1 _ _, M0 => False
  | M1 a b, M1 a' b' => if Neqb a a' then leb b b' else False
  | M1 _ _, M2 _ _ => False
  | M2 _ _, M0 => False
  | M2 _ _, M1 _ _ => False
  | M2 a b, M2 c d => lem a c /\ lem b d
  end.

Lemma lem_reflexive : r_reflexive bool lem.
Proof.
	unfold r_reflexive in |- *. simple induction x. exact I. simpl in |- *. intros.
	rewrite (Neqb_correct a). exact (leb_reflexive a0). intros.
	simpl in |- *. split. exact H. exact H0.
Qed.

Lemma lem_antisymmetric : r_antisymmetric bool lem.
Proof.
	unfold r_antisymmetric in |- *. simple induction x; simple induction y. intros.
	reflexivity. intros. elim H. intros. elim H1. intros. elim H.
	intros. simpl in H. elim (bool_is_true_or_false (Neqb a a1)).
	intros. rewrite H1 in H. simpl in H0. rewrite (Neqb_comm a1 a) in H0. rewrite H1 in H0. rewrite (Neqb_complete _ _ H1). rewrite (leb_antisymmetric _ _ H H0). reflexivity. intros. rewrite H1 in H.
	elim H. intros. elim H1. intros. elim H1. intros. elim H1. intros.
	elim H3. intros. elim H4. intros. rewrite (H m1 H5 H7). rewrite (H0 m2 H6 H8). reflexivity.
Qed.

Lemma lem_transitive : r_transitive bool lem.
Proof.
	unfold r_transitive in |- *. simple induction x; simple induction y; simple induction z. intros.
	exact I. intros. elim H0. intros. elim H2. intros. elim H. intros.
	elim H. intros. elim H1. intros. elim H1. intros. elim H1. intros.
	elim H3. intros. elim H. intros. elim H. intros. elim H1. intros.
	elim H0. intros. simpl in H. simpl in H0. elim (bool_is_true_or_false (Neqb a a1)); intro. rewrite H1 in H. elim (bool_is_true_or_false (Neqb a1 a3)); intro. rewrite (Neqb_complete _ _ H1). rewrite (Neqb_complete _ _ H2). rewrite H2 in H0. simpl in |- *. rewrite (Neqb_correct a3). exact (leb_transitive _ _ _ H H0). rewrite H2 in H0.
	elim H0. rewrite H1 in H. elim H. intros. elim H2. intros. elim H2.
 	intros. elim H2. intros. elim H3. intros. elim H1. intros. elim H1.
	intros. elim H3. intros. elim H1. intros. elim H1. intros. elim H3.
	intros. elim H3. intros. elim H4. intros. elim H4. intros. simpl in |- *.
	elim H5. intros. elim H6. intros. split. exact (H m1 m3 H7 H9).
	exact (H0 m2 m4 H8 H10).
Qed.

Lemma lem_order : r_order bool lem.
Proof.
	unfold r_order in |- *. split. exact lem_reflexive. split.
	exact lem_antisymmetric. exact lem_transitive.
Qed.

Definition ensemble_base (A : Set) (m : Map A) (x : Map bool) :=
  domain_equal A bool m x.

Fixpoint map_fill (A : Set) (m : Map A) {struct m} : 
 bool -> Map bool :=
  fun b : bool =>
  match m with
  | M0 => M0 bool
  | M1 a _ => M1 bool a b
  | M2 m0 m1 => M2 bool (map_fill A m0 b) (map_fill A m1 b)
  end.

Definition map_mini (A : Set) (m : Map A) : Map bool := map_fill A m false.

Definition map_maxi (A : Set) (m : Map A) : Map bool := map_fill A m true.

Lemma map_mini_appartient :
 forall (A : Set) (x : Map A), ensemble_base A x (map_mini A x).
Proof.
	unfold ensemble_base in |- *. intros. induction  x as [| a a0| x1 Hrecx1 x0 Hrecx0]. simpl in |- *. exact I. simpl in |- *.
	reflexivity. simpl in |- *. split. exact Hrecx1. exact Hrecx0.
Qed.

Lemma map_maxi_appartient :
 forall (A : Set) (x : Map A), ensemble_base A x (map_maxi A x).
Proof.
	unfold ensemble_base in |- *. intros. induction  x as [| a a0| x1 Hrecx1 x0 Hrecx0]. simpl in |- *. exact I. simpl in |- *.
	reflexivity. simpl in |- *. split. exact Hrecx1. exact Hrecx0.
Qed.

Lemma map_mini_mini :
 forall (A : Set) (x : Map A),
 mini bool lem (ensemble_base A x) (map_mini A x).
Proof.
	intros. unfold mini in |- *. split. exact (map_mini_appartient A x). induction  x as [| a a0| x1 Hrecx1 x0 Hrecx0].
	intros. induction  x as [| a a0| x1 Hrecx1 x0 Hrecx0]. simpl in |- *. exact I. elim H. elim H. intros. induction  x as [| a1 a2| x1 Hrecx1 x0 Hrecx0].
	elim H. unfold ensemble_base in H. simpl in H. rewrite H. simpl in |- *.
	rewrite (Neqb_correct a1). elim (bool_is_true_or_false a2); intro; rewrite H0; exact I. elim H. intros. induction  x as [| a a0| x2 Hrecx2 x3 Hrecx3]. elim H. elim H. simpl in |- *.
	unfold ensemble_base in H. simpl in H. elim H. intros. split. exact (Hrecx1 x2 H0). exact (Hrecx0 x3 H1).
Qed.

Lemma map_maxi_maxi :
 forall (A : Set) (x : Map A),
 maxi bool lem (ensemble_base A x) (map_maxi A x).
Proof.
	intros. unfold maxi in |- *. split. exact (map_maxi_appartient A x). induction  x as [| a a0| x1 Hrecx1 x0 Hrecx0].
	intros. induction  x as [| a a0| x1 Hrecx1 x0 Hrecx0]. simpl in |- *. exact I. elim H. elim H. intros. induction  x as [| a1 a2| x1 Hrecx1 x0 Hrecx0].
	elim H. unfold ensemble_base in H. simpl in H. rewrite H. simpl in |- *.
	rewrite (Neqb_correct a1). elim (bool_is_true_or_false a2); intro; rewrite H0; exact I. elim H. intros. induction  x as [| a a0| x2 Hrecx2 x3 Hrecx3]. elim H. elim H. simpl in |- *.
	unfold ensemble_base in H. simpl in H. elim H. intros. split. exact (Hrecx1 x2 H0). exact (Hrecx0 x3 H1).
Qed.

Lemma map_mini_mapget_false :
 forall (A : Set) (x : Map A) (a : ad) (b : bool),
 MapGet bool (map_mini A x) a = Some b -> b = false.
Proof.
	intro. simple induction x. intros. inversion H. intros. simpl in H.
	elim (bool_is_true_or_false (Neqb a a1)); intro; rewrite H0 in H. inversion H. reflexivity. inversion H. intros. induction  a as [| p].
	simpl in H1. exact (H _ _ H1). induction  p as [p Hrecp| p Hrecp| ]; simpl in H1. exact (H0 _ _ H1). exact (H _ _ H1). exact (H0 _ _ H1).
Qed.

Lemma map_mini_mapget_true :
 forall (A : Set) (x : Map A) (a : ad),
 MapGet bool (map_mini A x) a = Some true -> False.
Proof.
	intros. cut (true <> false). intros. exact (H0 (map_mini_mapget_false _ _ _ _ H)). intro.
	inversion H0.
Qed.

Lemma mlattice :
 forall (A : Set) (x : Map A),
 mLattice bool lem (ensemble_base A x) (map_mini A x) (map_maxi A x).
Proof.
	intros. split. exact lem_order. split. exact (map_mini_mini A x).
	exact (map_maxi_maxi A x).
Qed.

(* démonstration de la propriété de hauteur de chaine bornée dans le treillis *)

Definition lattice_bounded_def_0 (p : prechain bool) : Prop :=
  forall (A : Set) (m0 m1 : Map A),
  sas_chain bool (ensemble_base A (M2 A m0 m1)) lem p ->
  exists p0 : prechain bool,
    (exists p1 : prechain bool,
       sas_chain bool (ensemble_base A m0) lem p0 /\
       sas_chain bool (ensemble_base A m1) lem p1 /\
       lem (M2 bool (prechain_last bool p0) (prechain_last bool p1))
         (prechain_last bool p) /\
       chain_length bool p0 + chain_length bool p1 = S (chain_length bool p)).

Lemma lattice_bounded_0 :
 forall m : Map bool, lattice_bounded_def_0 (single bool m).
Proof.
	unfold lattice_bounded_def_0 in |- *. intros. elim H. intros. inversion H0. 
	induction  m as [| a a0| m2 Hrecm1 m3 Hrecm0]. elim H5. elim H5. clear Hrecm0. clear Hrecm1. split with (single bool m2). split with (single bool m3). split. split. elim H5.
	intros. apply (chain_single bool m2 (ensemble_base A m0) lem). exact H6.
	exact (dist_single bool m2). split. split. apply (chain_single bool m3 (ensemble_base A m1) lem). elim H5. intros. exact H7. exact (dist_single bool m3). split. simpl in |- *. split. exact (lem_reflexive m2). exact (lem_reflexive m3). simpl in |- *. reflexivity.
Qed.

Definition lattice_bounded_def_1 (p : prechain bool) : Prop :=
  lattice_bounded_def_0 p ->
  forall m : Map bool, lattice_bounded_def_0 (concat bool p m).

Lemma lattice_bounded_1 :
 forall m : Map bool, lattice_bounded_def_1 (single bool m).
Proof.
	unfold lattice_bounded_def_1 in |- *. unfold lattice_bounded_def_0 in |- *. intros. elim (H A m1 m2). intros. elim H1. intros. elim H2. intros. elim H4. intros. elim H6.
	intros. inversion H0. inversion H9. induction  m as [| a a0| m3 Hrecm1 m4 Hrecm0]. inversion H13. inversion H13.
	clear Hrecm0. clear Hrecm1. induction  m0 as [| a a0| m0_1 Hrecm0_1 m0_0 Hrecm0_0]. inversion H16. inversion H16.
	clear Hrecm0_0. clear Hrecm0_1. elim (classic (m3 = m0_1)). elim (classic (m4 = m0_0)).
	intros. inversion H10. rewrite H18 in H21. rewrite H19 in H21. elim (H21 (refl_equal _)). intros. split with (single bool m0_1). split with (concat bool (single bool m4) m0_0). split. split. elim H16. intros. exact (chain_single bool m0_1 (ensemble_base A m1) lem H20). exact (dist_single bool m0_1). split. split. apply (chain_concat_s bool m4 m0_0 (ensemble_base A m2) lem).
	elim H13. intros. exact H21. elim H16. intros. exact H21. simpl in H7. simpl in H17.
	elim H17. intros. exact H21. exact (dist_concat_s bool m4 m0_0 H18). split.
	simpl in |- *. split. exact (lem_reflexive _). exact (lem_reflexive _). simpl in |- *.
	reflexivity. intros. split with (concat bool (single bool m3) m0_1). split with (single bool m4). split. split. apply (chain_concat_s bool m3 m0_1 (ensemble_base A m1) lem). elim H13. intros. assumption. elim H16. intros. assumption. elim H17.
	intros. assumption. exact (dist_concat_s bool m3 m0_1 H18). split. split.
	apply (chain_single bool m4 (ensemble_base A m2) lem). elim H13. intros. 
	assumption. exact (dist_single bool m4). split. simpl in |- *. split. exact (lem_reflexive _). elim H17. intros. assumption. simpl in |- *. reflexivity. inversion H0. inversion H1.
	split. exact (chain_single bool m (ensemble_base A (M2 A m1 m2)) lem H5).
	exact (dist_single bool m).
Qed.

Lemma lattice_bounded_2 :
 forall p : prechain bool,
 lattice_bounded_def_1 p ->
 forall m : Map bool, lattice_bounded_def_1 (concat bool p m).
Proof.
	unfold lattice_bounded_def_1 in |- *. unfold lattice_bounded_def_0 in |- *. intros. inversion H1.
	inversion H2. induction  m0 as [| a a0| m0_1 Hrecm0_1 m0_0 Hrecm0_0]. elim H9. elim H9. clear Hrecm0_1. clear Hrecm0_0.
	elim (H0 A m1 m2). intros. elim H12. intros. elim H13. intros. elim H15. intros.
	elim H17. intros. clear H12. clear H13. clear H15. clear H17. inversion H11.
	induction  m as [| a a0| m0 Hrecm1 m3 Hrecm0]. elim H21. elim H21. clear Hrecm1. clear Hrecm0. elim (classic (m0 = m0_1)). elim (classic (m3 = m0_0)). intros. rewrite H23 in H3. rewrite H24 in H3.
	inversion H3. elim (H27 (refl_equal _)). intros. split with x0.
	split with (concat bool x1 m0_0). split. exact H14. split. split. elim (prechain_sum bool x1). intros. elim H25. intros. rewrite H26. apply (chain_concat_s bool x3 m0_0 (ensemble_base A m2) lem). rewrite H26 in H16. inversion H16.
	inversion H27. assumption. elim H9. intros. assumption. rewrite H26 in H18.
	simpl in H18. elim H10. intros. elim H18. intros. exact (lem_transitive _ _ _ H30 H28). intros. elim H25. intros. elim H26. intros. rewrite H27. apply (chain_concat_m bool x3 m0_0 x4 (ensemble_base A m2) lem). elim H9. intros. assumption. rewrite H27 in H18. simpl in H18. elim H18. elim H10. intros. exact (lem_transitive _ _ _ H31 H29).
	rewrite H27 in H16. inversion H16. assumption. elim (prechain_sum bool x1). intros.
	elim H25. intros. rewrite H26. apply (dist_concat_s bool x3 m0_0). rewrite H26 in H18.
	simpl in H18. elim H10. intros. intro. elim H18. intros. rewrite H29 in H31.
	elim (H23 (lem_antisymmetric _ _ H28 H31)). intros. elim H25. intros. elim H26.
	intros. rewrite H27. apply (dist_concat_m bool x3 m0_0 x4). rewrite H27 in H18.
	elim H18. intros. simpl in H29. elim H10. intros. intro. rewrite H32 in H29.
	exact (H23 (lem_antisymmetric _ _ H31 H29)). rewrite H27 in H16. inversion H16.
	assumption. split. simpl in |- *. simpl in H18. elim H10. elim H18. intros. split.
	exact (lem_transitive _ _ _ H25 H27). exact (lem_reflexive _). simpl in |- *. simpl in H19. rewrite <- (plus_Snm_nSm (chain_length bool x0) (chain_length bool x1)).
	simpl in |- *. rewrite H19. rewrite <- H12. reflexivity. intro. split with (concat bool x0 m0_1). split with x1. split. elim (prechain_sum bool x0). intro. elim H24.
	intros. rewrite H25. split. apply (chain_concat_s bool x3 m0_1 (ensemble_base A m1) lem). rewrite H25 in H14. inversion H14. inversion H26. assumption. elim H9. intros.
	assumption. rewrite H25 in H19. rewrite H25 in H18. simpl in H18. elim H10. elim H18.
	intros. exact (lem_transitive _ _ _ H26 H28). apply (dist_concat_s bool x3 m0_1).
	rewrite H25 in H18. simpl in H18. elim H18. elim H10. intros. intro. rewrite H30 in H28. exact (H23 (lem_antisymmetric _ _ H26 H28)). intros. elim H24. intros.
	elim H25. intros. rewrite H26. split. apply (chain_concat_m bool x3 m0_1 x4 (ensemble_base A m1) lem). elim H9. intros. assumption. rewrite H26 in H18.
	elim H10. elim H18. intros. simpl in H27. exact (lem_transitive _ _ _ H27 H29).
	rewrite H26 in H14. inversion H14. assumption. apply (dist_concat_m bool x3 m0_1 x4). intro. rewrite H26 in H18. elim H10. elim H18. intros. simpl in H28. rewrite H27 in H28. exact (H23 (lem_antisymmetric _ _ H30 H28)). rewrite H26 in H14.
	inversion H14. assumption. split. assumption. simpl in |- *. split. split. exact (lem_reflexive _). elim H18. elim H10. intros. exact (lem_transitive _ _ _ H27 H25).
	rewrite H19. rewrite <- H12. reflexivity. induction  m as [| a a0| m0 Hrecm1 m3 Hrecm0]. elim H15. elim H15.
	clear Hrecm0. clear Hrecm1. elim (classic (m0 = m0_1)). elim (classic (m3 = m0_0)).
	intros. rewrite H23 in H3. rewrite H24 in H3. inversion H3. elim (H27 (refl_equal _)). intros. split with x0. split with (concat bool x1 m0_0).
	split. assumption. split. elim (prechain_sum bool x1). intros. elim H25.
	intros. rewrite H26. split. apply (chain_concat_s bool x3 m0_0 (ensemble_base A m2) lem). rewrite H26 in H16. inversion H16. inversion H27. assumption.
	elim H9. intros. assumption. rewrite H26 in H18. elim H10. elim H18. intros.
	simpl in H28. exact (lem_transitive _ _ _ H28 H30). apply (dist_concat_s bool x3 m0_0). intro. elim H18. elim H10. intros. rewrite H26 in H31. simpl in H31.
	rewrite H27 in H31. exact (H23 (lem_antisymmetric _ _ H29 H31)). intros.
	elim H25. intros. elim H26. intros. rewrite H27. split. apply (chain_concat_m bool x3 m0_0 x4 (ensemble_base A m2) lem). elim H9. intros. assumption.
	rewrite H27 in H18. elim H10. elim H18. intros. simpl in H29. exact (lem_transitive _ _ _ H29 H31). rewrite H27 in H16. inversion H16. assumption. apply (dist_concat_m bool x3 m0_0 x4). intro. elim H10. elim H18. intros. rewrite H27 in H30. simpl in H30. rewrite H28 in H30. exact (H23 (lem_antisymmetric _ _ H32 H30)). rewrite H27 in H16. inversion H16. assumption. simpl in |- *. split. split.
	elim H18. elim H10. intros. exact (lem_transitive _ _ _ H27 H25). exact (lem_reflexive _). rewrite <- (plus_Snm_nSm (chain_length bool x0) (chain_length bool x1)). simpl in |- *. rewrite H19. rewrite <- H12. reflexivity. intro. split with (concat bool x0 m0_1). split with x1. split. elim (prechain_sum bool x0). intros.
	elim H24. intros. rewrite H25. split. apply (chain_concat_s bool x3 m0_1 (ensemble_base A m1) lem). rewrite H25 in H14. inversion H14. inversion H26.
	assumption. elim H9. intros. assumption. rewrite H25 in H18. elim H10. elim H18.
	intros. simpl in H26. exact (lem_transitive _ _ _ H26 H28). apply (dist_concat_s bool x3 m0_1). intro. rewrite H25 in H18. elim H18. elim H10. intros. simpl in H19.
	rewrite H26 in H29. simpl in H29. exact (H23 (lem_antisymmetric _ _ H27 H29)).
	intros. elim H24. intros. elim H25. intros. rewrite H26. split. apply (chain_concat_m bool x3 m0_1 x4 (ensemble_base A m1) lem). elim H9. intros.
	assumption. rewrite H26 in H18. elim H10. elim H18. intros. simpl in H27.
	exact (lem_transitive _ _ _ H27 H29). rewrite H26 in H14. inversion H14.
	assumption. apply (dist_concat_m bool x3 m0_1 x4). intro. rewrite H26 in H18.
	elim H10. elim H18. intros. rewrite H27 in H28. simpl in H28. exact (H23 (lem_antisymmetric _ _ H30 H28)). rewrite H26 in H14. inversion H14. assumption.
	split. assumption. simpl in |- *. split. split. exact (lem_reflexive _). elim H18.
	elim H10. intros. exact (lem_transitive _ _ _ H27 H25). rewrite H19. simpl in |- *.
	rewrite <- H12. reflexivity. split. assumption. inversion H3. assumption.
Qed.

Lemma lattice_bounded_3 :
 forall p : prechain bool,
 lattice_bounded_def_0 p ->
 forall m : Map bool, lattice_bounded_def_0 (concat bool p m).
Proof.
	exact
  (prechain_ind bool lattice_bounded_def_1 lattice_bounded_1
     lattice_bounded_2).
Qed.

Lemma lattice_bounded_4 : forall p : prechain bool, lattice_bounded_def_0 p.
Proof.
	exact
  (prechain_ind bool lattice_bounded_def_0 lattice_bounded_0
     lattice_bounded_3).
Qed.

Lemma lattice_bounded_5 :
 forall (p : prechain bool) (A : Set) (m0 m1 : Map A),
 sas_chain bool (ensemble_base A (M2 A m0 m1)) lem p ->
 exists p0 : prechain bool,
   (exists p1 : prechain bool,
      sas_chain bool (ensemble_base A m0) lem p0 /\
      sas_chain bool (ensemble_base A m1) lem p1 /\
      lem (M2 bool (prechain_last bool p0) (prechain_last bool p1))
        (prechain_last bool p) /\
      chain_length bool p0 + chain_length bool p1 = S (chain_length bool p)).
Proof.
	exact
  (prechain_ind bool lattice_bounded_def_0 lattice_bounded_0
     lattice_bounded_3).
Qed.

Definition lattice_bounded_def_2 (A : Set) (m : Map A) : Prop :=
  forall p : prechain bool,
  sas_chain bool (ensemble_base A m) lem p ->
  chain_length bool p <= S (MapCard A m).

Lemma lattice_bounded_6 : forall A : Set, lattice_bounded_def_2 A (M0 A).
Proof.
	unfold lattice_bounded_def_2 in |- *. intros. induction  p as [m| p Hrecp m]. simpl in |- *. exact (le_n_n _).
	elim (prechain_sum bool p); intros. elim H0. intros. rewrite H1 in H.
	inversion H. inversion H2. inversion H3. induction  x as [| a a0| x2 Hrecx1 x3 Hrecx0]. induction  m as [| a a0| m1 Hrecm1 m0 Hrecm0].
	elim H12. reflexivity. elim H9. elim H9. elim H6. elim H6. elim H0.
	intros. elim H1. intros. rewrite H2 in H. inversion H. inversion H3.
	inversion H4. induction  x as [| a a0| x3 Hrecx1 x4 Hrecx0]. induction  m as [| a a0| m1 Hrecm1 m0 Hrecm0]. elim H15. reflexivity. elim H10.
	elim H10. inversion H12. elim H23. elim H20. inversion H12. elim H23.
	elim H20.
Qed.

Lemma lattice_bounded_7 :
 forall (A : Set) (a : ad) (a0 : A), lattice_bounded_def_2 A (M1 A a a0).
Proof.
	unfold lattice_bounded_def_2 in |- *. intros. induction  p as [m| p Hrecp m]. simpl in |- *. exact (le_n_Sn _).
	elim (prechain_sum bool p). intros. elim H0. intros. rewrite H1. simpl in |- *.
	exact (le_n_n _). intros. elim H0. intros. elim H1. intros. rewrite H2 in H. elim (prechain_sum bool x0). intros. elim H3. intros. rewrite H4 in H. inversion H. inversion H5. inversion H14. induction  m as [| a1 a2| m1 Hrecm1 m0 Hrecm0]. elim H12.
	induction  x as [| a3 a4| x4 Hrecx1 x5 Hrecx0]. elim H20. induction  x1 as [| a5 a6| x1_1 Hrecx1_1 x1_0 Hrecx1_0]. elim H17. simpl in H13. simpl in H21. elim (bool_is_true_or_false (Neqb a3 a1)); intro; rewrite H22 in H13. elim (bool_is_true_or_false (Neqb a5 a3)); intro; rewrite H23 in H21. inversion H6. inversion H28. rewrite (Neqb_complete _ _ H22) in H26.
	rewrite (Neqb_complete _ _ H23) in H30. induction  a6 as [| ]. induction  a4 as [| ].
	elim H30. reflexivity. elim H21. induction  a4 as [| ]. induction  a2 as [| ]. elim H26.
	reflexivity. elim H13. elim H30. reflexivity. elim H21. elim H13. elim H17.
	elim H20. elim H12. intros. elim H3. intros. elim H4. intros. rewrite H5 in H. inversion H. inversion H6. inversion H15. inversion H23. induction  m as [| a1 a2| m1 Hrecm1 m0 Hrecm0].
	elim H13. induction  x as [| a3 a4| x6 Hrecx1 x7 Hrecx0]. elim H21. induction  x1 as [| a5 a6| x1_1 Hrecx1_1 x1_0 Hrecx1_0]. elim H29. simpl in H14.
	simpl in H22. elim (bool_is_true_or_false (Neqb a3 a1)); intro; rewrite H31 in H14. elim (bool_is_true_or_false (Neqb a5 a3)); intro; rewrite H32 in H22. inversion H7. inversion H37. rewrite (Neqb_complete _ _ H31) in H35. rewrite (Neqb_complete _ _ H32) in H40. induction  a6 as [| ]. induction  a4 as [| ].
	elim H40. reflexivity. elim H22. induction  a4 as [| ]. induction  a2 as [| ]. elim H35.
	reflexivity. elim H14. elim H40. reflexivity. elim H22. elim H14. elim H29.
	elim H21. elim H13. induction  m as [| a1 a2| m1 Hrecm1 m0 Hrecm0]. elim H13. induction  x as [| a3 a4| x6 Hrecx1 x7 Hrecx0]. elim H21.
	induction  x1 as [| a5 a6| x1_1 Hrecx1_1 x1_0 Hrecx1_0]. elim H26. simpl in H14. simpl in H22. elim (bool_is_true_or_false (Neqb a3 a1)); intro; rewrite H31 in H14.
	elim (bool_is_true_or_false (Neqb a5 a3)); intro; rewrite H32 in H22.
	inversion H7. inversion H37. rewrite (Neqb_complete _ _ H31) in H35.
	rewrite (Neqb_complete _ _ H32) in H40. induction  a6 as [| ]. induction  a4 as [| ].
	elim H40. reflexivity. elim H22. induction  a4 as [| ]. induction  a2 as [| ]. elim H35.
	reflexivity. elim H14. elim H40. reflexivity. elim H22. elim H14. elim H26.
	elim H21. elim H13.
Qed.

Lemma lattice_bounded_8 :
 forall (A : Set) (m : Map A),
 lattice_bounded_def_2 A m ->
 forall m0 : Map A,
 lattice_bounded_def_2 A m0 -> lattice_bounded_def_2 A (M2 A m m0).
Proof.
	unfold lattice_bounded_def_2 in |- *. intros. elim (lattice_bounded_5 p A m m0 H1).
	intros. elim H2. intros. elim H3. intros. elim H5. intros. elim H7.
	intros. simpl in |- *. apply (le_S_n (chain_length bool p) (S (MapCard A m + MapCard A m0))). rewrite <- H9. replace (S (S (MapCard A m + MapCard A m0))) with
  (S (MapCard A m) + S (MapCard A m0)). exact (plus_le_compat _ _ _ _ (H x H4) (H0 x0 H6)). simpl in |- *. rewrite <- (plus_Snm_nSm (MapCard A m) (MapCard A m0)). simpl in |- *. reflexivity.
Qed.

Lemma lattice_bounded_9 :
 forall (A : Set) (m : Map A), lattice_bounded_def_2 A m.
Proof.
	intro. exact
  (Map_ind A (lattice_bounded_def_2 A) (lattice_bounded_6 A)
     (lattice_bounded_7 A) (lattice_bounded_8 A)).
Qed.

Lemma lattice_bounded_10 :
 forall (A : Set) (m : Map A) (p : prechain bool),
 sas_chain bool (ensemble_base A m) lem p ->
 chain_length bool p <= S (MapCard A m).
Proof.
	intro. exact
  (Map_ind A (lattice_bounded_def_2 A) (lattice_bounded_6 A)
     (lattice_bounded_7 A) (lattice_bounded_8 A)).
Qed.

Lemma lattice_bounded :
 forall (A : Set) (x : Map A),
 bounded_sas_chain bool (ensemble_base A x) lem (S (MapCard A x)).
Proof.
	unfold bounded_sas_chain in |- *. intros. exact (lattice_bounded_10 A x p H).
Qed.

(* égalité dans bool puis sur les (Map bool) (dans bool) *)

Definition eq_bool (b0 b1 : bool) : bool :=
  match b0, b1 with
  | false, false => true
  | false, true => false
  | true, false => false
  | true, true => true
  end.

Lemma eq_bool_equal : forall b0 b1 : bool, eq_bool b0 b1 = true -> b0 = b1.
Proof.
	simple induction b0. simple induction b1. intro. reflexivity. intro. elim H.
	reflexivity. simple induction b1. intro. elim H. reflexivity. intro.
	reflexivity.
Qed.

Lemma equal_eq_bool : forall b : bool, eq_bool b b = true.
Proof.
	simple induction b. reflexivity. reflexivity.
Qed.

Fixpoint eqm_bool (x y : Map bool) {struct y} : bool :=
  match x, y with
  | M0, M0 => true
  | M0, M1 _ _ => false
  | M0, M2 _ _ => false
  | M1 _ _, M0 => false
  | M1 a b, M1 c d => Neqb a c && eq_bool b d
  | M1 _ _, M2 _ _ => false
  | M2 _ _, M0 => false
  | M2 _ _, M1 _ _ => false
  | M2 a b, M2 c d => eqm_bool a c && eqm_bool b d
  end.

Lemma eqm_bool_equal : forall x y : Map bool, eqm_bool x y = true -> x = y.
Proof.
	simple induction x. simple induction y. intros. reflexivity. intros. inversion H.
	intros. inversion H1. intros. induction  y as [| a1 a2| y1 Hrecy1 y0 Hrecy0]. inversion H. simpl in H.
	elim (bool_is_true_or_false (Neqb a a1)); intro; rewrite H0 in H.
	rewrite (Neqb_complete _ _ H0). elim (bool_is_true_or_false (eq_bool a0 a2)); intro; rewrite H1 in H. rewrite (eq_bool_equal _ _ H1).
	reflexivity. inversion H. inversion H. inversion H. intros.
	induction  y as [| a a0| y1 Hrecy1 y0 Hrecy0]. inversion H1. inversion H1. simpl in H1. elim (bool_is_true_or_false (eqm_bool m y1)); intro; rewrite H2 in H1.
	elim (bool_is_true_or_false (eqm_bool m0 y0)); intro; rewrite H3 in H1.
	rewrite (H _ H2). rewrite (H0 _ H3). reflexivity. inversion H1.
	inversion H1.
Qed.

Lemma equal_eqm_bool : forall x : Map bool, eqm_bool x x = true.
Proof.
	simple induction x. reflexivity. intros. simpl in |- *. rewrite (Neqb_correct a).
	rewrite (equal_eq_bool a0). reflexivity. intros. simpl in |- *. rewrite H.
	rewrite H0. reflexivity.
Qed.

(* lemmes auxilliaires sur les comparaisons *)

Lemma lem_get_leb :
 forall (m0 m1 : Map bool) (a : ad) (b0 b1 : bool),
 lem m0 m1 ->
 MapGet bool m0 a = Some b0 ->
 MapGet bool m1 a = Some b1 -> leb b0 b1.
Proof.
	simple induction m0. intros. inversion H0. simple induction m1. intros. inversion H1.
	intros. simpl in H. elim (bool_is_true_or_false (Neqb a a1)); intros; rewrite H2 in H. simpl in H0. simpl in H1. elim (bool_is_true_or_false (Neqb a a3)); intro; rewrite H3 in H0. inversion H0. elim (bool_is_true_or_false (Neqb a1 a3)); intros; rewrite H4 in H1.
	inversion H1. rewrite H7 in H. rewrite H5 in H. exact H. inversion H1.
	inversion H0. elim H. intros. inversion H1. simple induction m2. intros.
	inversion H3. intros. simpl in H1. elim H1. intros. simpl in H3.
	elim H3. intros. induction  a as [| p]. simpl in H4. simpl in H5. exact (H _ _ _ _ H6 H4 H5). induction  p as [p Hrecp| p Hrecp| ]; simpl in H4; simpl in H5. exact (H0 _ _ _ _ H7 H4 H5). exact (H _ _ _ _ H6 H4 H5). exact (H0 _ _ _ _ H7 H4 H5).
Qed.

Lemma lem_domain_equal :
 forall m0 m1 : Map bool, lem m0 m1 -> domain_equal bool bool m0 m1.
Proof.
	simple induction m0. simple induction m1. intros. exact I. intros. inversion H.
	intros. inversion H1. simple induction m1. intros. inversion H. intros.
	simpl in |- *. simpl in H. elim (bool_is_true_or_false (Neqb a a1)); intros.
	exact (Neqb_complete _ _ H0). rewrite H0 in H. elim H. intros.
	inversion H1. intros. induction  m2 as [| a a0| m2_1 Hrecm2_1 m2_0 Hrecm2_0]. inversion H1. inversion H1.
	elim H1; intros. simpl in |- *. split. exact (H _ H2). exact (H0 _ H3).
Qed.

(* croissance des fonctions and et or *)

Lemma andb_inc_r :
 forall b b0 b1 : bool, leb b0 b1 -> leb (b && b0) (b && b1).
Proof.
	simple induction b0; simple induction b1. intros. induction  b as [| ]; exact I.
	intros. inversion H. intros. induction  b as [| ]; exact I. intros.
	induction  b as [| ]; exact I.
Qed.

Lemma andb_inc_l :
 forall b b0 b1 : bool, leb b0 b1 -> leb (b0 && b) (b1 && b).
Proof.
	simple induction b0; simple induction b1. intros. induction  b as [| ]; exact I.
	intros. inversion H. intros. induction  b as [| ]; exact I. intros.
	induction  b as [| ]; exact I.
Qed.

Lemma orb_inc_r : forall b b0 b1 : bool, leb b0 b1 -> leb (b || b0) (b || b1).
Proof.
	simple induction b0; simple induction b1. intros. induction  b as [| ]; exact I.
	intros. inversion H. intros. induction  b as [| ]; exact I. intros.
	induction  b as [| ]; exact I.
Qed.

Lemma orb_inc_l : forall b b0 b1 : bool, leb b0 b1 -> leb (b0 || b) (b1 || b).
Proof.
	simple induction b0; simple induction b1. intros. induction  b as [| ]; exact I.
	intros. inversion H. intros. induction  b as [| ]; exact I. intros.
	induction  b as [| ]; exact I.
Qed.

Lemma andb_incr :
 forall b0 b1 b2 b3 : bool,
 leb b0 b1 -> leb b2 b3 -> leb (b0 && b2) (b1 && b3).
Proof.
	intros. apply (leb_transitive (b0 && b2) (b1 && b2) (b1 && b3)).
	exact (andb_inc_l _ _ _ H). exact (andb_inc_r _ _ _ H0).
Qed.

Lemma orb_incr :
 forall b0 b1 b2 b3 : bool,
 leb b0 b1 -> leb b2 b3 -> leb (b0 || b2) (b1 || b3).
Proof.
	intros. apply (leb_transitive (b0 || b2) (b1 || b2) (b1 || b3)).
	exact (orb_inc_l _ _ _ H). exact (orb_inc_r _ _ _ H0).
Qed.