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

(* définition inductive de la coaccessibilité *)

Inductive coacc : preDTA -> ad -> ad -> Prop :=
  | coacc_id :
      forall (d : preDTA) (a : ad) (s : state),
      MapGet state d a = Some s -> coacc d a a
  | coacc_nxt :
      forall (d : preDTA) (a0 a1 a2 : ad) (s1 s2 : state) 
        (pl : prec_list) (c : ad),
      MapGet state d a2 = Some s2 ->
      MapGet state d a1 = Some s1 ->
      MapGet prec_list s1 c = Some pl ->
      prec_occur pl a2 -> coacc d a0 a1 -> coacc d a0 a2.

Definition coacc_transitive_def (d : preDTA) (a0 a1 : ad) : Prop :=
  forall a2 : ad, coacc d a0 a1 -> coacc d a2 a0 -> coacc d a2 a1.

Lemma coacc_transitive_0 :
 forall (d : preDTA) (a : ad) (s : state),
 MapGet state d a = Some s -> coacc_transitive_def d a a.
Proof.
	unfold coacc_transitive_def in |- *. intros. exact H1.
Qed.

Lemma coacc_transitive_1 :
 forall (d : preDTA) (a0 a1 a2 : ad) (s1 s2 : state) 
   (pl : prec_list) (c : ad),
 MapGet state d a2 = Some s2 ->
 MapGet state d a1 = Some s1 ->
 MapGet prec_list s1 c = Some pl ->
 prec_occur pl a2 ->
 coacc d a0 a1 ->
 coacc_transitive_def d a0 a1 -> coacc_transitive_def d a0 a2.
Proof.
	unfold coacc_transitive_def in |- *. intros. exact (coacc_nxt d a3 a1 a2 s1 s2 pl c H H0 H1 H2 (H4 _ H3 H6)).
Qed.

Lemma coacc_transitive :
 forall (d : preDTA) (a0 a1 a2 : ad),
 coacc d a0 a1 -> coacc d a1 a2 -> coacc d a0 a2.
Proof.
	intros. exact
  (coacc_ind coacc_transitive_def coacc_transitive_0 coacc_transitive_1 d a1
     a2 H0 a0 H0 H).
Qed.

(* fonction dont on va calculer le point fixe : *)

Fixpoint map_replace (A : Set) (m : Map A) {struct m} : 
 ad -> A -> Map A :=
  fun (a : ad) (x : A) =>
  match m with
  | M0 => M0 A
  | M1 b y => if Neqb a b then M1 A b x else M1 A b y
  | M2 m n =>
      match a with
      | N0 => M2 A (map_replace A m N0 x) n
      | Npos q =>
          match q with
          | xH => M2 A m (map_replace A n N0 x)
          | xO p => M2 A (map_replace A m (Npos p) x) n
          | xI p => M2 A m (map_replace A n (Npos p) x)
          end
      end
  end.

Fixpoint map_or (m0 m1 : Map bool) {struct m1} : Map bool :=
  match m0, m1 with
  | M0, _ => M0 bool
  | _, M0 => M0 bool
  | M1 a0 b0, M1 a1 b1 =>
      if Neqb a0 a1 then M1 bool a0 (b0 || b1) else M0 bool
  | M1 _ _, M2 _ _ => M0 bool
  | M2 _ _, M1 _ _ => M0 bool
  | M2 x0 y0, M2 x1 y1 => M2 bool (map_or x0 x1) (map_or y0 y1)
  end.

Fixpoint pl_coacc (d : preDTA) (pl : prec_list) {struct pl} : 
 Map bool :=
  match pl with
  | prec_empty => map_mini state d
  | prec_cons a la ls =>
      map_replace bool (map_or (pl_coacc d la) (pl_coacc d ls)) a true
  end.

Fixpoint st_coacc (d : preDTA) (s : state) {struct s} : 
 Map bool :=
  match s with
  | M0 => map_mini state d
  | M1 a pl => pl_coacc d pl
  | M2 x y => map_or (st_coacc d x) (st_coacc d y)
  end.

Fixpoint predta_coacc_0 (d d' : preDTA) {struct d'} : 
 Map bool -> Map bool :=
  fun m : Map bool =>
  match d', m with
  | M0, M0 => map_mini state d
  | M1 a s, M1 a' b =>
      if Neqb a a' && b then st_coacc d s else map_mini state d
  | M2 x y, M2 z t => map_or (predta_coacc_0 d x z) (predta_coacc_0 d y t)
  | _, _ => map_mini state d
  end.

Definition predta_coacc (d : preDTA) (a : ad) (m : Map bool) : 
  Map bool := map_replace bool (predta_coacc_0 d d m) a true.

Definition predta_coacc_states (d : preDTA) (a : ad) : 
  Map bool :=
  power (Map bool) (predta_coacc d a) (map_mini state d)
    (S (MapCard state d)).

Definition predta_coacc_states_0 (d : preDTA) (a : ad) : 
  Map bool :=
  lazy_power bool eqm_bool (predta_coacc d a) (map_mini state d)
    (S (MapCard state d)).

(* lemmes sur map_or *)

Lemma map_or_mapget_true_l :
 forall (m0 m1 : Map bool) (a : ad),
 domain_equal bool bool m0 m1 ->
 MapGet bool m0 a = Some true ->
 MapGet bool (map_or m0 m1) a = Some true.
Proof.
	simple induction m0. intros. inversion H0. simple induction m1.
	intros. inversion H. intros. simpl in H. simpl in H0.
	elim (bool_is_true_or_false (Neqb a a3)); intros; rewrite H1 in H0. inversion H0. rewrite <- (Neqb_complete _ _ H1). rewrite <- H. simpl in |- *. rewrite (Neqb_correct a).
	simpl in |- *. rewrite (Neqb_correct a). reflexivity. inversion H0.
	intros. inversion H1. simple induction m2. intros. inversion H1.
	intros. inversion H1. intros. simpl in |- *. elim H3; intros.
	induction  a as [| p]. exact (H _ _ H5 H4). induction  p as [p Hrecp| p Hrecp| ]. exact (H0 _ _ H6 H4). exact (H _ _ H5 H4). exact (H0 _ _ H6 H4).
Qed.

Lemma map_or_mapget_true_ld :
 forall (d : preDTA) (m0 m1 : Map bool) (a : ad),
 ensemble_base state d m0 ->
 ensemble_base state d m1 ->
 MapGet bool m0 a = Some true ->
 MapGet bool (map_or m0 m1) a = Some true.
Proof.
	intros. exact
  (map_or_mapget_true_l m0 m1 a
     (domain_equal_transitive bool state bool m0 d m1
        (domain_equal_symmetric state bool d m0 H) H0) H1).
Qed.

Lemma map_or_mapget_true_r :
 forall (m0 m1 : Map bool) (a : ad),
 domain_equal bool bool m0 m1 ->
 MapGet bool m0 a = Some true ->
 MapGet bool (map_or m1 m0) a = Some true.
Proof.
	simple induction m0. intros. inversion H0. simple induction m1; intros.
	inversion H. simpl in H. simpl in H0. rewrite <- H.
	elim (bool_is_true_or_false (Neqb a a3)); intros; rewrite H1 in H0;
  inversion H0. rewrite <- (Neqb_complete _ _ H1). simpl in |- *. rewrite (Neqb_correct a). simpl in |- *.
	rewrite (Neqb_correct a). elim (bool_is_true_or_false a2); intros; rewrite H2; reflexivity. inversion H1. intros.
	induction  m2 as [| a0 a1| m2_1 Hrecm2_1 m2_0 Hrecm2_0]. inversion H1. inversion H1. simpl in |- *.
	elim H1; intros. induction  a as [| p]. exact (H _ _ H3 H2).
	induction  p as [p Hrecp| p Hrecp| ]. exact (H0 _ _ H4 H2). exact (H _ _ H3 H2).
	exact (H0 _ _ H4 H2).
Qed.

Lemma map_or_mapget_true_rd :
 forall (d : preDTA) (m0 m1 : Map bool) (a : ad),
 ensemble_base state d m0 ->
 ensemble_base state d m1 ->
 MapGet bool m1 a = Some true ->
 MapGet bool (map_or m0 m1) a = Some true.
Proof.
	intros. exact
  (map_or_mapget_true_r m1 m0 a
     (domain_equal_transitive bool state bool m1 d m0
        (domain_equal_symmetric state bool d m1 H0) H) H1).
Qed.

Lemma map_or_mapget_true_inv :
 forall (m0 m1 : Map bool) (a : ad),
 MapGet bool (map_or m0 m1) a = Some true ->
 MapGet bool m0 a = Some true \/ MapGet bool m1 a = Some true.
Proof.
	simple induction m0; intros. induction  m1 as [| a0 a1| m1_1 Hrecm1_1 m1_0 Hrecm1_0]. simpl in H. inversion H.
	simpl in H. inversion H. simpl in H. inversion H. induction  m1 as [| a2 a3| m1_1 Hrecm1_1 m1_0 Hrecm1_0]. simpl in H. inversion H. simpl in H. elim (bool_is_true_or_false (Neqb a a2)); intros; rewrite H0 in H.
	simpl in H. elim (bool_is_true_or_false (Neqb a a1)); intros; rewrite H1 in H;
  inversion H. rewrite H3. elim (bool_is_true_or_false a0); intros; rewrite H2 in H3; rewrite H2. left. rewrite <- (Neqb_complete _ _ H1). simpl in |- *.
	rewrite (Neqb_correct a). reflexivity. elim (bool_is_true_or_false a3); intros; rewrite H4 in H3; rewrite H4.
	right. rewrite <- (Neqb_complete _ _ H0). rewrite <- (Neqb_complete _ _ H1). simpl in |- *. rewrite (Neqb_correct a).
	reflexivity. inversion H3. inversion H. inversion H.
	induction  m2 as [| a0 a1| m2_1 Hrecm2_1 m2_0 Hrecm2_0]. inversion H1. inversion H1. simpl in H1.
	induction  a as [| p]. elim (H _ _ H1). intros. left. simpl in |- *. assumption.
	intros. right. simpl in |- *. assumption. induction  p as [p Hrecp| p Hrecp| ]. elim (H0 _ _ H1); intros; simpl in |- *. left. assumption. right. assumption.
	elim (H _ _ H1); intros; simpl in |- *. left. assumption. right.
	assumption. elim (H0 _ _ H1); intros; simpl in |- *. left. assumption.
	right. assumption.
Qed.

(* lemmes sur map_replace : *)

Lemma map_replace_mapget_ins_true_0 :
 forall (m : Map bool) (a : ad) (b : bool),
 MapGet bool m a = Some b ->
 MapGet bool (map_replace bool m a true) a = Some true.
Proof.
	simple induction m. intros. inversion H. intros. simpl in H.
	elim (bool_is_true_or_false (Neqb a a1)); intros; rewrite H0 in H;
  inversion H. simpl in |- *. rewrite <- (Neqb_complete _ _ H0). rewrite (Neqb_correct a).
	simpl in |- *. rewrite (Neqb_correct a). reflexivity. intros.
	induction  a as [| p]; simpl in H1. simpl in |- *. exact (H _ _ H1).
	induction  p as [p Hrecp| p Hrecp| ]; simpl in |- *. exact (H0 _ _ H1). exact (H _ _ H1). exact (H0 _ _ H1).
Qed.

Lemma map_replace_mapget_ins_true_1 :
 forall (m : Map bool) (a a' : ad),
 MapGet bool m a = Some true ->
 MapGet bool (map_replace bool m a' true) a = Some true.
Proof.
	simple induction m. intros. inversion H. intros. simpl in H.
	elim (bool_is_true_or_false (Neqb a a1)); intros; rewrite H0 in H. inversion H. simpl in |- *. elim (bool_is_true_or_false (Neqb a' a)); intros; rewrite H1.
	simpl in |- *. rewrite H0. reflexivity. simpl in |- *. rewrite H0.
	reflexivity. inversion H. intros. induction  a as [| p]; simpl in H1; simpl in |- *. induction  a' as [| p]. simpl in |- *. exact (H _ _ H1).
	induction  p as [p Hrecp| p Hrecp| ]. simpl in |- *. exact H1. exact (H _ _ H1). exact H1.
	induction  p as [p Hrecp| p Hrecp| ]. induction  a' as [| p0]; simpl in |- *. exact H1. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]; simpl in |- *. exact (H0 _ _ H1). exact H1. exact (H0 _ _ H1).
	induction  a' as [| p0]; simpl in |- *. exact (H _ _ H1). induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]; simpl in |- *. exact H1. exact (H _ _ H1). exact H1. induction  a' as [| p]; simpl in |- *. exact H1. induction  p as [p Hrecp| p Hrecp| ]; simpl in |- *. exact (H0 _ _ H1). exact H1. exact (H0 _ _ H1).
Qed.

Lemma map_replace_mapget_true_inv :
 forall (m : Map bool) (a b : ad),
 MapGet bool (map_replace bool m a true) b = Some true ->
 b = a \/ MapGet bool m b = Some true.
Proof.
	simple induction m. intros. inversion H. simpl in |- *. intros. elim (bool_is_true_or_false (Neqb a1 a)); intros; rewrite H0 in H. simpl in H. elim (bool_is_true_or_false (Neqb a b)); intros; rewrite H1 in H. rewrite H1. left.
	rewrite (Neqb_complete _ _ H0). rewrite <- (Neqb_complete _ _ H1). reflexivity. inversion H. simpl in H. elim (bool_is_true_or_false (Neqb a b)); intros; rewrite H1 in H;
  inversion H. rewrite H1. right. reflexivity. intros.
	simpl in H1. induction  a as [| p]; simpl in H1. induction  b as [| p]; simpl in |- *; simpl in H1. exact (H _ _ H1). induction  p as [p Hrecp| p Hrecp| ]. right. exact H1.
	elim (H _ _ H1). intros. inversion H2. intros. right.
	exact H2. right. exact H1. induction  p as [p Hrecp| p Hrecp| ]. induction  b as [| p0].
	simpl in |- *. simpl in H1. right. exact H1. simpl in H1. 
	induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. elim (H0 _ _ H1). intros. inversion H2.
	left. reflexivity. intros. simpl in |- *. right. exact H2. simpl in |- *.
	right. exact H1. elim (H0 _ _ H1). intros. inversion H2.
	intros. simpl in |- *. right. exact H2. induction  b as [| p0]; simpl in |- *; simpl in H1. elim (H _ _ H1). intros. inversion H2.
	right. exact H2. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. right. exact H1. elim (H _ _ H1). intros. inversion H2. left. reflexivity.
	intros. right. exact H2. right. exact H1. induction  b as [| p].
	simpl in H1. simpl in |- *. right. exact H1. induction  p as [p Hrecp| p Hrecp| ]; simpl in |- *; simpl in H1. elim (H0 _ _ H1). intros. inversion H2.
	intros. right. exact H2. right. exact H1. left. reflexivity.
Qed.

(* définition ok de l'application predta_coacc *)

Lemma map_or_def_ok :
 forall m0 m1 : Map bool,
 domain_equal bool bool m0 m1 -> domain_equal bool bool m0 (map_or m0 m1).
Proof.
	simple induction m0. simple induction m1. intros. exact I. intros. inversion H.
	intros. inversion H1. simple induction m1. intros. inversion H. intros.
	simpl in H. simpl in |- *. rewrite H. rewrite (Neqb_correct a1). simpl in |- *.
	reflexivity. intros. inversion H1. simple induction m2. intros. inversion H1.
	intros. inversion H1. intros. elim H3. intros. simpl in |- *. split.
	exact (H _ H4). exact (H0 _ H5).
Qed.

Lemma map_or_def_ok_d :
 forall (d : preDTA) (m0 m1 : Map bool),
 ensemble_base state d m0 ->
 ensemble_base state d m1 -> ensemble_base state d (map_or m0 m1).
Proof.
	unfold ensemble_base in |- *. intros. apply (domain_equal_transitive state bool bool d m0 (map_or m0 m1)). exact H. apply (map_or_def_ok m0 m1). apply (domain_equal_transitive bool state bool m0 d m1).
	exact (domain_equal_symmetric state bool d m0 H). exact H0.
Qed.

Lemma map_replace_def_ok :
 forall (A : Set) (m : Map A) (a : ad) (x : A),
 domain_equal A A m (map_replace A m a x).
Proof.
	intro. simple induction m. intros. exact I. intros. simpl in |- *. elim (bool_is_true_or_false (Neqb a1 a)); intros; rewrite H.
	simpl in |- *. reflexivity. simpl in |- *. reflexivity. intros. simpl in |- *.
	induction  a as [| p]. simpl in |- *. split. exact (H N0 x). exact (domain_equal_reflexive A m1). induction  p as [p Hrecp| p Hrecp| ]. split. exact (domain_equal_reflexive A m0). exact (H0 (Npos p) x). split.
	exact (H (Npos p) x). exact (domain_equal_reflexive A m1).
	split. exact (domain_equal_reflexive A m0). exact (H0 N0 x).
Qed.

Lemma map_replace_def_ok_d :
 forall (d : preDTA) (m : Map bool) (a : ad) (x : bool),
 ensemble_base state d m -> ensemble_base state d (map_replace bool m a x).
Proof.
	unfold ensemble_base in |- *. intros. apply
  (domain_equal_transitive state bool bool d m (map_replace bool m a x) H).
	exact (map_replace_def_ok bool m a x).
Qed.

Lemma pl_coacc_def_ok :
 forall (d : preDTA) (pl : prec_list), ensemble_base state d (pl_coacc d pl).
Proof.
	simple induction pl. simpl in |- *. intros. exact
  (map_replace_def_ok_d d (map_or (pl_coacc d p) (pl_coacc d p0)) a true
     (map_or_def_ok_d _ _ _ H H0)).
	simpl in |- *. exact (map_mini_appartient state d).
Qed.

Lemma st_coacc_def_ok :
 forall (d : preDTA) (s : state), ensemble_base state d (st_coacc d s).
Proof.
	simple induction s. simpl in |- *. exact (map_mini_appartient state d). simpl in |- *.
	intros. exact (pl_coacc_def_ok d a0). intros. simpl in |- *. exact (map_or_def_ok_d _ _ _ H H0).
Qed.

Lemma predta_coacc_0_def_ok :
 forall (d d' : preDTA) (m : Map bool),
 ensemble_base state d (predta_coacc_0 d d' m).
Proof.
	simple induction d'. simpl in |- *. intros. induction  m as [| a a0| m1 Hrecm1 m0 Hrecm0];
  exact (map_mini_appartient state d). simpl in |- *. intros. induction  m as [| a1 a2| m1 Hrecm1 m0 Hrecm0].
	exact (map_mini_appartient state d). elim (bool_is_true_or_false (Neqb a a1 && a2)); intros; rewrite H. exact (st_coacc_def_ok d a0). exact (map_mini_appartient state d). exact (map_mini_appartient state d). intros. induction  m1 as [| a a0| m1_1 Hrecm1_1 m1_0 Hrecm1_0]. simpl in |- *.
	exact (map_mini_appartient state d). simpl in |- *. exact (map_mini_appartient state d). simpl in |- *. exact (map_or_def_ok_d _ _ _ (H m1_1) (H0 m1_0)).
Qed.

Lemma predta_coacc_def_ok :
 forall (d : preDTA) (a : ad) (m : Map bool),
 ensemble_base state d (predta_coacc d a m).
Proof.
	unfold predta_coacc in |- *. intros. exact (map_replace_def_ok_d d _ a true (predta_coacc_0_def_ok d d m)).
Qed.

(* croissance de predta_coacc *)

Definition lemd (d : preDTA) : mRelation bool :=
  fun m0 m1 : Map bool =>
  ensemble_base state d m0 /\ ensemble_base state d m1 /\ lem m0 m1.

Lemma lemd_reflexive :
 forall (d : preDTA) (m : Map bool), ensemble_base state d m -> lemd d m m.
Proof.
	unfold ensemble_base in |- *. simple induction d. intros. unfold lemd in |- *.
	unfold ensemble_base in |- *. induction  m as [| a a0| m1 Hrecm1 m0 Hrecm0]. split. exact I.
	split; exact I. inversion H. inversion H. intros.
	unfold lemd in |- *. unfold ensemble_base in |- *. induction  m as [| a1 a2| m1 Hrecm1 m0 Hrecm0]. inversion H.
	simpl in H. rewrite H. simpl in |- *. split. reflexivity. split.
	reflexivity. rewrite (Neqb_correct a1). exact (leb_reflexive a2). inversion H. unfold lemd in |- *. unfold ensemble_base in |- *.
	simple induction m1. intros. inversion H1. intros. inversion H1.
 	intros. elim H3. intros. elim (H _ H4). elim (H0 _ H5).
	intros. split; split. exact H4. exact H5. split. exact H4.
	exact H5. split. elim H9. intros. exact H11. elim H7.
	intros. exact H11.
Qed.

Lemma lemd_antisymmetric :
 forall (d : preDTA) (m0 m1 : Map bool),
 lemd d m0 m1 -> lemd d m1 m0 -> m0 = m1.
Proof.
	unfold lemd in |- *. unfold ensemble_base in |- *. simple induction d. simple induction m0.
	intros. elim H. intros. elim H0. intros. elim H4. intros.
	induction  m1 as [| a a0| m1_1 Hrecm1_1 m1_0 Hrecm1_0]. reflexivity. inversion H6. inversion H6.
	intros. elim H0. intros. elim H2. intros. decompose [and] H.
	induction  m1 as [| a1 a2| m1_1 Hrecm1_1 m1_0 Hrecm1_0]. inversion H8. inversion H5. inversion H8.
	intros. decompose [and] H1.  inversion H3. intros.
	decompose [and] H. decompose [and] H0. induction  m0 as [| a1 a2| m0_1 Hrecm0_1 m0_0 Hrecm0_0].
	inversion H1. induction  m1 as [| a3 a4| m1_1 Hrecm1_1 m1_0 Hrecm1_0]. inversion H3. simpl in H1.
	simpl in H2. rewrite <- H1. rewrite <- H2. simpl in H4.
	simpl in H7. rewrite <- H2 in H4. rewrite <- H1 in H4.
	rewrite (Neqb_correct a) in H4. rewrite <- H1 in H7.
	rewrite <- H2 in H7. rewrite (Neqb_correct a) in H7.
	rewrite (leb_antisymmetric _ _ H4 H7). reflexivity.
	inversion H2. inversion H1. intros. decompose [and] H1.
	decompose [and] H2. induction  m1 as [| a a0| m1_1 Hrecm1_1 m1_0 Hrecm1_0]. inversion H3. inversion H3.
	induction  m2 as [| a a0| m2_1 Hrecm2_1 m2_0 Hrecm2_0]. inversion H4. inversion H9. elim H4. elim H3.
	elim H6. intros. rewrite (H m1_1 m2_1). rewrite (H0 m1_0 m2_0). reflexivity. split. exact H12. split. exact H14.
	exact H10. split. exact H14. split. exact H12. elim H9.
	intros. exact H16. elim H9. intros. split. exact H11.
	split. exact H13. exact H7. elim H9. intros. split.
	exact H13. split. exact H11. exact H15.
Qed.

Lemma lemd_transitive :
 forall (d : preDTA) (m0 m1 m2 : Map bool),
 lemd d m0 m1 -> lemd d m1 m2 -> lemd d m0 m2.
Proof.
	simple induction d. unfold lemd in |- *. unfold ensemble_base in |- *. intros.
	decompose [and] H. decompose [and] H0. induction  m0 as [| a a0| m0_1 Hrecm0_1 m0_0 Hrecm0_0].
	induction  m1 as [| a a0| m1_1 Hrecm1_1 m1_0 Hrecm1_0]. induction  m2 as [| a a0| m2_1 Hrecm2_1 m2_0 Hrecm2_0]. split. exact I. split; exact I.
	inversion H6. inversion H7. inversion H2. inversion H2.
	inversion H1. inversion H1. unfold lemd in |- *. unfold ensemble_base in |- *.
	intros. decompose [and] H. decompose [and] H0. induction  m0 as [| a1 a2| m0_1 Hrecm0_1 m0_0 Hrecm0_0].
	inversion H1. induction  m1 as [| a3 a4| m1_1 Hrecm1_1 m1_0 Hrecm1_0]. inversion H2. induction  m2 as [| a5 a6| m2_1 Hrecm2_1 m2_0 Hrecm2_0].
	inversion H6. simpl in H2. simpl in H1. simpl in H6.
	simpl in H4. rewrite <- H2 in H4. rewrite <- H1 in H4.
	rewrite (Neqb_correct a) in H4. simpl in H7. rewrite <- H3 in H7. rewrite <- H6 in H7. rewrite (Neqb_correct a) in H7.
	rewrite <- H1. rewrite <- H6. split. simpl in |- *. reflexivity.
	simpl in |- *. split. reflexivity. rewrite (Neqb_correct a).
	exact (leb_transitive _ _ _ H4 H7). inversion H6.
	inversion H3. inversion H1. unfold lemd in |- *. unfold ensemble_base in |- *.
	intros. decompose [and] H1. decompose [and] H2. induction  m1 as [| a a0| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
        inversion H3. inversion H3. clear Hrecm1_1 Hrecm1_0.
	induction  m2 as [| a a0| m2_1 Hrecm2_1 m2_0 Hrecm2_0]. inversion H5. inversion H5. clear Hrecm2_1.
	clear Hrecm2_0. intros. induction  m3 as [| a a0| m3_1 Hrecm3_1 m3_0 Hrecm3_0]. inversion H8.
	inversion H8. clear Hrecm3_1. clear Hrecm3_0. simpl in |- *.
	elim H3. elim H8. elim H6. elim H5. elim H9. intros.
	split. split. exact H17. exact H18. split. split. exact H15.
	exact H16. split. exact (lem_transitive _ _ _ H13 H7).
	exact (lem_transitive _ _ _ H14 H10).
Qed.

Lemma map_or_inc_ld :
 forall (d : preDTA) (m m0 m1 : Map bool),
 ensemble_base state d m ->
 lemd d m0 m1 -> lemd d (map_or m0 m) (map_or m1 m).
Proof.
	unfold lemd in |- *. unfold ensemble_base in |- *. simple induction d. intros.
	decompose [and] H0. induction  m as [| a a0| m2 Hrecm1 m3 Hrecm0]. induction  m0 as [| a a0| m0_1 Hrecm0_1 m0_0 Hrecm0_0]. induction  m1 as [| a a0| m1_1 Hrecm1_1 m1_0 Hrecm1_0]. simpl in |- *. split. exact I. split; exact I. inversion H3.
	inversion H3. inversion H1. inversion H1. inversion H.
	inversion H. intros. decompose [and] H0. induction  m as [| a1 a2| m2 Hrecm1 m3 Hrecm0].
	inversion H. induction  m0 as [| a3 a4| m0_1 Hrecm0_1 m0_0 Hrecm0_0]. inversion H1. induction  m1 as [| a5 a6| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
	inversion H3. simpl in |- *. simpl in H1. simpl in H3. simpl in H4. simpl in H. rewrite <- H. rewrite <- H3. rewrite <- H1. rewrite (Neqb_correct a). simpl in |- *. rewrite (Neqb_correct a). split. reflexivity. split. reflexivity. rewrite <- H3 in H4. rewrite <- H1 in H4. rewrite (Neqb_correct a) in H4. exact (orb_inc_l a2 _ _ H4). inversion H4.
	inversion H1. inversion H. intros. decompose [and] H2.
	induction  m1 as [| a a0| m1_1 Hrecm1_1 m1_0 Hrecm1_0]. inversion H1. inversion H1. induction  m2 as [| a a0| m2_1 Hrecm2_1 m2_0 Hrecm2_0].
	inversion H3. inversion H3. induction  m3 as [| a a0| m3_1 Hrecm3_1 m3_0 Hrecm3_0]. inversion H5.
	inversion H5. clear Hrecm3_1 Hrecm3_0 Hrecm2_1 Hrecm2_0 Hrecm1_1 Hrecm1_0. simpl in |- *. elim H5. elim H3. elim H6.
	intros. elim H1. intros. elim (H m1_1 m2_1 m3_1).
	elim (H0 m1_0 m2_0 m3_0). intros. split. split; assumption.
	split. split. elim H17; intros. assumption. elim H15; intros; assumption. elim H15. intros. elim H17. intros.
	split; assumption. assumption. split. assumption. split; assumption. assumption. split. assumption. split; assumption.
Qed.

Lemma map_or_inc_rd :
 forall (d : preDTA) (m m0 m1 : Map bool),
 ensemble_base state d m ->
 lemd d m0 m1 -> lemd d (map_or m m0) (map_or m m1).
Proof.
	unfold lemd in |- *. unfold ensemble_base in |- *. simple induction d. intros.
	decompose [and] H0. induction  m as [| a a0| m2 Hrecm1 m3 Hrecm0]. induction  m0 as [| a a0| m0_1 Hrecm0_1 m0_0 Hrecm0_0]. induction  m1 as [| a a0| m1_1 Hrecm1_1 m1_0 Hrecm1_0]. simpl in |- *. split. exact I. split; exact I. inversion H3.
	inversion H3. inversion H1. inversion H1. inversion H.
	inversion H. intros. decompose [and] H0. induction  m as [| a1 a2| m2 Hrecm1 m3 Hrecm0].
	inversion H. induction  m0 as [| a3 a4| m0_1 Hrecm0_1 m0_0 Hrecm0_0]. inversion H1. induction  m1 as [| a5 a6| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
	inversion H3. simpl in |- *. simpl in H1. simpl in H3. simpl in H4. simpl in H. rewrite <- H. rewrite <- H3. rewrite <- H1. rewrite (Neqb_correct a). simpl in |- *. rewrite (Neqb_correct a). split. reflexivity. split. reflexivity. rewrite <- H3 in H4. rewrite <- H1 in H4. rewrite (Neqb_correct a) in H4. exact (orb_inc_r a2 _ _ H4). inversion H4.
	inversion H1. inversion H. intros. decompose [and] H2.
	induction  m1 as [| a a0| m1_1 Hrecm1_1 m1_0 Hrecm1_0]. inversion H1. inversion H1. induction  m2 as [| a a0| m2_1 Hrecm2_1 m2_0 Hrecm2_0].
	inversion H3. inversion H3. induction  m3 as [| a a0| m3_1 Hrecm3_1 m3_0 Hrecm3_0]. inversion H5.
	inversion H5. clear Hrecm3_1 Hrecm3_0 Hrecm2_1 Hrecm2_0 Hrecm1_1 Hrecm1_0. simpl in |- *. elim H5. elim H3. elim H6.
	intros. elim H1. intros. elim (H m1_1 m2_1 m3_1).
	elim (H0 m1_0 m2_0 m3_0). intros. split. split; assumption.
	split. split. elim H17; intros. assumption. elim H15; intros; assumption. elim H15. intros. elim H17. intros.
	split; assumption. assumption. split. assumption. split; assumption. assumption. split. assumption. split; assumption.
Qed.

Lemma map_or_inc_d :
 forall (d : preDTA) (m0 m1 m2 m3 : Map bool),
 lemd d m0 m1 -> lemd d m2 m3 -> lemd d (map_or m0 m2) (map_or m1 m3).
Proof.
	intros. apply (lemd_transitive d (map_or m0 m2) (map_or m1 m2) (map_or m1 m3)). apply (map_or_inc_ld d m2 m0 m1).
	unfold lemd in H0. decompose [and] H0. exact H1. exact H.
	apply (map_or_inc_rd d m1 m2 m3). unfold lemd in H.
	decompose [and] H. exact H3. exact H0.
Qed.

Lemma predta_coacc_0_incr :
 forall (d d' : preDTA) (m0 m1 : Map bool),
 lemd d' m0 m1 -> lemd d (predta_coacc_0 d d' m0) (predta_coacc_0 d d' m1).
Proof.
	unfold lemd in |- *. unfold ensemble_base in |- *. simple induction d'. intros.
	decompose [and] H. induction  m0 as [| a a0| m0_1 Hrecm0_1 m0_0 Hrecm0_0]. induction  m1 as [| a a0| m1_1 Hrecm1_1 m1_0 Hrecm1_0]. simpl in |- *.
	split. exact (map_mini_appartient state d). split.
	exact (map_mini_appartient state d). exact (lem_reflexive (map_mini state d)). inversion H2. inversion H2. induction  m1 as [| a1 a2| m1_1 Hrecm1_1 m1_0 Hrecm1_0]. inversion H0. simpl in H3. simpl in |- *. apply (lemd_reflexive d (map_mini state d)). exact (map_mini_appartient state d).
	inversion H2. simpl in |- *. induction  m1 as [| a a0| m1_1 Hrecm1_1 m1_0 Hrecm1_0];
  exact (lemd_reflexive d (map_mini state d) (map_mini_appartient state d)). intros.
	decompose [and] H. induction  m0 as [| a1 a2| m0_1 Hrecm0_1 m0_0 Hrecm0_0]. induction  m1 as [| a1 a2| m1_1 Hrecm1_1 m1_0 Hrecm1_0]. simpl in |- *.
	exact (lemd_reflexive d (map_mini state d) (map_mini_appartient state d)). inversion H0. inversion H0. induction  m1 as [| a3 a4| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
	inversion H2. simpl in |- *. simpl in H0. simpl in H2.
        simpl in H3.
        rewrite <- H0; rewrite <- H2; rewrite <- H0 in H3;
         rewrite <- H2 in H3.  rewrite (Neqb_correct a); simpl in |- *.
        rewrite (Neqb_correct a) in H3. elim (bool_is_true_or_false a2); intros; rewrite H1;
  elim (bool_is_true_or_false a4); intros; rewrite H4. 
	exact (lemd_reflexive d (st_coacc d a0) (st_coacc_def_ok d a0)). rewrite H4 in H3. rewrite H1 in H3. 
	inversion H3. 
	split. exact (map_mini_appartient state d). split. exact (st_coacc_def_ok d a0). elim (map_mini_mini state d). intros. exact (H6 (st_coacc d a0) (st_coacc_def_ok d a0)). exact (lemd_reflexive d (map_mini state d) (map_mini_appartient state d)). 
        inversion H3. inversion H0. intros. decompose [and] H1.
	induction  m1 as [| a a0| m1_1 Hrecm1_1 m1_0 Hrecm1_0]. inversion H2. inversion H2. induction  m2 as [| a a0| m2_1 Hrecm2_1 m2_0 Hrecm2_0].
	inversion H4. inversion H4. clear Hrecm2_0 Hrecm2_1 Hrecm1_0 Hrecm1_1. elim H5. intros. elim H4. elim H2. intros. simpl in |- *.
	elim (H m1_1 m2_1). intros. elim H12. intros. elim (H0 m1_0 m2_0). intros. elim H16. intros. split. exact (map_or_def_ok_d d _ _ H11 H15). split. exact (map_or_def_ok_d _ _ _ H13 H17). elim
  (map_or_inc_d d (predta_coacc_0 d m m1_1) (predta_coacc_0 d m m2_1)
     (predta_coacc_0 d m0 m1_0) (predta_coacc_0 d m0 m2_0)).
	intros. elim H20. intros. exact H22. unfold lemd in |- *.
	split. assumption. split; assumption. unfold lemd in |- *.
	split. assumption. split; assumption.  split.
	assumption. split; assumption. split. assumption.
	split; assumption.
Qed.

Lemma map_replace_inc :
 forall (m0 m1 : Map bool) (a : ad) (b : bool),
 lem m0 m1 -> lem (map_replace bool m0 a b) (map_replace bool m1 a b).
Proof.
	simple induction m0. simple induction m1. intros. exact (lem_reflexive (map_replace bool (M0 bool) a b)). intros. inversion H.
	intros. inversion H1. simple induction m1. intros. inversion H.
	simpl in |- *. intros. elim (bool_is_true_or_false (Neqb a a1)); intros; rewrite H0 in H. elim (bool_is_true_or_false (Neqb a3 a)); intros; rewrite H1. rewrite (Neqb_complete _ _ H1). rewrite H0. rewrite (Neqb_complete _ _ H0).
	exact (lem_reflexive (M1 bool a1 b)). elim (bool_is_true_or_false (Neqb a3 a1)); intros; rewrite H2.
	rewrite <- (Neqb_complete _ _ H0) in H2. rewrite H2 in H1.
	inversion H1. rewrite <- (Neqb_complete _ _ H0). simpl in |- *.
	rewrite (Neqb_correct a). exact H. elim H. intros.
	inversion H1. simple induction m2. intros. inversion H1.
	intros. inversion H1. intros. simpl in |- *. elim H3; intros.
	induction  a as [| p]. simpl in |- *. split. exact (H m3 N0 b H4).
	exact H5. induction  p as [p Hrecp| p Hrecp| ]; simpl in |- *; split. exact H4. exact (H0 m4 (Npos p) b H5). exact (H m3 (Npos p) b H4). exact H5.
	exact H4. exact (H0 m4 N0 b H5).
Qed.

Lemma map_replace_inc_d :
 forall (d : preDTA) (m0 m1 : Map bool) (a : ad) (b : bool),
 lemd d m0 m1 -> lemd d (map_replace bool m0 a b) (map_replace bool m1 a b).
Proof.
	unfold lemd in |- *. intros. decompose [and] H. split.
	exact (map_replace_def_ok_d d m0 a b H0). split.
	exact (map_replace_def_ok_d d m1 a b H2). exact (map_replace_inc m0 m1 a b H3).
Qed.

Lemma predta_coacc_increasing :
 forall (d : preDTA) (a : ad),
 increasing_app bool (lemd d) (predta_coacc d a).
Proof.
	unfold increasing_app in |- *. unfold predta_coacc in |- *. intros.
	exact
  (map_replace_inc_d d (predta_coacc_0 d d x) (predta_coacc_0 d d y) a true
     (predta_coacc_0_incr d d x y H)).
Qed.

(* démonstration : propriété de chaine croissantes bornées *)

Definition lattice_lemd_bounded_0_def (p : prechain bool) : Prop :=
  forall d : preDTA,
  chain bool (ensemble_base state d) (lemd d) p ->
  chain bool (ensemble_base state d) lem p.

Lemma lattice_lemd_bounded_0 :
 forall m : Map bool, lattice_lemd_bounded_0_def (single bool m).
Proof.
	unfold lattice_lemd_bounded_0_def in |- *. intros. inversion H.
	exact (chain_single bool m (ensemble_base state d) lem H3).
Qed.

Definition lattice_lemd_bounded_1_def (p : prechain bool) : Prop :=
  lattice_lemd_bounded_0_def p ->
  forall m : Map bool, lattice_lemd_bounded_0_def (concat bool p m).

Lemma lattice_lemd_bounded_1 :
 forall m : Map bool, lattice_lemd_bounded_1_def (single bool m).
Proof.
	unfold lattice_lemd_bounded_1_def in |- *. unfold lattice_lemd_bounded_0_def in |- *. intros. inversion H0.
	inversion H7. inversion H9. exact (chain_concat_s bool m m0 (ensemble_base state d) lem H8 H10 H11).
Qed.

Lemma lattice_lemd_bounded_2 :
 forall p : prechain bool,
 lattice_lemd_bounded_1_def p ->
 forall m : Map bool, lattice_lemd_bounded_1_def (concat bool p m).
Proof.
	unfold lattice_lemd_bounded_1_def in |- *. unfold lattice_lemd_bounded_0_def in |- *.
	intros. inversion H1. inversion H8. inversion H11. exact
  (chain_concat_m bool m m0 p (ensemble_base state d) lem H12 H13 (H0 _ H9)).
Qed.

Lemma lattice_lemd_bounded_3 :
 forall (p : prechain bool) (d : preDTA),
 chain bool (ensemble_base state d) (lemd d) p ->
 chain bool (ensemble_base state d) lem p.
Proof.
	exact
  (prechain_ind bool lattice_lemd_bounded_0_def lattice_lemd_bounded_0
     (prechain_ind bool lattice_lemd_bounded_1_def lattice_lemd_bounded_1
        lattice_lemd_bounded_2)).
Qed.

Lemma lattice_lemd_bounded :
 forall (p : prechain bool) (d : preDTA),
 sas_chain bool (ensemble_base state d) (lemd d) p ->
 sas_chain bool (ensemble_base state d) lem p.
Proof.
	intros. inversion H. split. exact (lattice_lemd_bounded_3 p d H0). exact H1.
Qed.

Lemma lattice_bounded :
 forall d : preDTA,
 bounded_sas_chain bool (ensemble_base state d) (lemd d)
   (S (MapCard state d)).
Proof.
	unfold bounded_sas_chain in |- *. intros. exact (lattice_bounded state d p (lattice_lemd_bounded p d H)).
Qed.

(* démo : si un état est coaccessible alors il existe n tel que ... *)

Lemma pl_coacc_contain_coacc_ads :
 forall (d : preDTA) (p : prec_list) (a : ad),
 prec_occur p a ->
 prec_list_ref_ok p d -> MapGet bool (pl_coacc d p) a = Some true.
Proof.
	simple induction p. intros. inversion H1. simpl in |- *. elim (H2 _ H1).
	intros. elim
  (domain_equal_mapget state bool d (map_or (pl_coacc d p0) (pl_coacc d p1))
     a0 x
     (map_or_def_ok_d _ _ _ (pl_coacc_def_ok d p0) (pl_coacc_def_ok d p1)) H7).
	intros. exact (map_replace_mapget_ins_true_0 _ _ _ H8).
	simpl in |- *. apply
  (map_replace_mapget_ins_true_1 (map_or (pl_coacc d p0) (pl_coacc d p1)) a0
     a). apply
  (map_or_mapget_true_ld _ _ _ a0 (pl_coacc_def_ok d p0)
     (pl_coacc_def_ok d p1)). elim (prec_list_ref_ok_destr _ _ _ _ H2). intros. exact (H _ H7 H8). simpl in |- *. apply
  (map_replace_mapget_ins_true_1 (map_or (pl_coacc d p0) (pl_coacc d p1)) a0
     a). apply
  (map_or_mapget_true_rd _ _ _ a0 (pl_coacc_def_ok d p0)
     (pl_coacc_def_ok d p1)).
	elim (prec_list_ref_ok_destr _ _ _ _ H2). intros.
	exact (H0 _ H7 H9). simpl in |- *. intros. inversion H.
Qed.

Lemma st_coacc_contain_coacc_ads :
 forall (d : preDTA) (s : state) (c : ad) (p : prec_list) (a : ad),
 state_ref_ok s d ->
 MapGet prec_list s c = Some p ->
 prec_occur p a -> MapGet bool (st_coacc d s) a = Some true.
Proof.
	simple induction s. intros. inversion H0. intros. simpl in H0.
	elim (bool_is_true_or_false (Neqb a c)); intros; rewrite H2 in H0. simpl in |- *. apply (pl_coacc_contain_coacc_ads d a0 a1). inversion H0. exact H1. apply (H a a0). simpl in |- *.
	rewrite (Neqb_correct a). reflexivity. inversion H0.
	intros. elim (state_ref_ok_M2_destr _ _ _ H1); intros.
	simpl in |- *. induction  c as [| p0]. simpl in H2. apply
  (map_or_mapget_true_ld _ _ _ a (st_coacc_def_ok d m) (st_coacc_def_ok d m0)).
	apply (H _ _ _ H4 H2 H3). induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. apply
  (map_or_mapget_true_rd _ _ _ a (st_coacc_def_ok d m) (st_coacc_def_ok d m0)). exact (H0 _ _ _ H5 H2 H3).
	apply
  (map_or_mapget_true_ld _ _ _ a (st_coacc_def_ok d m) (st_coacc_def_ok d m0)). apply (H _ _ _ H4 H2 H3).
	apply
  (map_or_mapget_true_rd _ _ _ a (st_coacc_def_ok d m) (st_coacc_def_ok d m0)). exact (H0 _ _ _ H5 H2 H3).
Qed.

Lemma predta_coacc_0_contain_coacc_ads :
 forall (d d' : preDTA) (a : ad) (s : state) (c : ad) 
   (p : prec_list) (b : ad) (m : Map bool),
 preDTA_ref_ok_distinct d' d ->
 MapGet state d' a = Some s ->
 MapGet prec_list s c = Some p ->
 prec_occur p b ->
 ensemble_base state d' m ->
 MapGet bool m a = Some true ->
 MapGet bool (predta_coacc_0 d d' m) b = Some true.
Proof.
	simple induction d'. intros. inversion H0. simpl in |- *. intros.
	induction  m as [| a2 a3| m1 Hrecm1 m0 Hrecm0]. inversion H3. unfold ensemble_base in H3.
	simpl in H3. rewrite <- H3. rewrite (Neqb_correct a).
	simpl in H4. elim (bool_is_true_or_false (Neqb a2 a1)); intros; rewrite H5 in H4;
  inversion H4. simpl in |- *. apply (st_coacc_contain_coacc_ads d a0 c p b). elim (bool_is_true_or_false (Neqb a a1)); intros; rewrite H6 in H0;
  inversion H0. rewrite H9 in H. apply (H a s).
	simpl in |- *. rewrite (Neqb_correct a). reflexivity. elim (bool_is_true_or_false (Neqb a a1)); intros; rewrite H6 in H0. inversion H0. exact H1. inversion H0. exact H2.
	inversion H3. intros. induction  m1 as [| a0 a1| m1_1 Hrecm1_1 m1_0 Hrecm1_0]. inversion H5.
	inversion H5. elim H5. intros. elim (preDTA_ref_ok_distinct_dest _ _ _ H1). intros. simpl in |- *.
	induction  a as [| p0]. simpl in H6. simpl in H2. apply
  (map_or_mapget_true_ld _ _ _ b (predta_coacc_0_def_ok d m m1_1)
     (predta_coacc_0_def_ok d m0 m1_0)). exact (H _ _ _ _ _ _ H9 H2 H3 H4 H7 H6). induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]; simpl in H2; simpl in H6. apply
  (map_or_mapget_true_rd _ _ _ b (predta_coacc_0_def_ok d m m1_1)
     (predta_coacc_0_def_ok d m0 m1_0)). exact (H0 _ _ _ _ _ _ H10 H2 H3 H4 H8 H6).
	exact
  (map_or_mapget_true_ld _ _ _ b (predta_coacc_0_def_ok d m m1_1)
     (predta_coacc_0_def_ok d m0 m1_0) (H _ _ _ _ _ _ H9 H2 H3 H4 H7 H6)). exact
  (map_or_mapget_true_rd _ _ _ b (predta_coacc_0_def_ok d m m1_1)
     (predta_coacc_0_def_ok d m0 m1_0) (H0 _ _ _ _ _ _ H10 H2 H3 H4 H8 H6)).
Qed.

Lemma predta_coacc_contain_coacc_ads_0 :
 forall (d : preDTA) (a0 a : ad) (s : state) (c : ad) 
   (p : prec_list) (b : ad) (m : Map bool),
 preDTA_ref_ok d ->
 MapGet state d a = Some s ->
 MapGet prec_list s c = Some p ->
 prec_occur p b ->
 ensemble_base state d m ->
 MapGet bool m a = Some true ->
 MapGet bool (predta_coacc d a0 m) b = Some true.
Proof.
	unfold predta_coacc in |- *. intros. apply (map_replace_mapget_ins_true_1 (predta_coacc_0 d d m) b a0). apply
  (fun hyp : preDTA_ref_ok_distinct d d =>
   predta_coacc_0_contain_coacc_ads d d a s c p b m hyp H0 H1 H2 H3 H4). elim (preDTA_ref_ok_def d). intros. exact (H5 H).
Qed.

Definition predta_coacc_contain_coacc_ads_def_0 (d : preDTA) 
  (a0 a1 : ad) : Prop :=
  coacc d a0 a1 ->
  preDTA_ref_ok d ->
  exists n : nat,
    MapGet bool (power (Map bool) (predta_coacc d a0) (map_mini state d) n)
      a1 = Some true.

Lemma predta_coacc_contain_coacc_ads_1 :
 forall (d : preDTA) (a : ad) (s : state),
 MapGet state d a = Some s ->
 predta_coacc_contain_coacc_ads_def_0 d a a.
Proof.
	unfold predta_coacc_contain_coacc_ads_def_0 in |- *. intros.
	split with 1. simpl in |- *. unfold predta_coacc in |- *. elim
  (domain_equal_mapget state bool d (predta_coacc_0 d d (map_mini state d)) a
     s (predta_coacc_0_def_ok d d (map_mini state d)) H). intros. apply
  (map_replace_mapget_ins_true_0 (predta_coacc_0 d d (map_mini state d)) a x
     H2).
Qed.

Lemma predta_coacc_contain_coacc_ads_2 :
 forall (d : preDTA) (a0 a1 a2 : ad) (s1 s2 : state) 
   (pl : prec_list) (c : ad),
 MapGet state d a2 = Some s2 ->
 MapGet state d a1 = Some s1 ->
 MapGet prec_list s1 c = Some pl ->
 prec_occur pl a2 ->
 coacc d a0 a1 ->
 predta_coacc_contain_coacc_ads_def_0 d a0 a1 ->
 predta_coacc_contain_coacc_ads_def_0 d a0 a2.
Proof.
	unfold predta_coacc_contain_coacc_ads_def_0 in |- *. intros.
	elim (H4 H3 H6). intros. split with (S x). simpl in |- *.
	apply
  (predta_coacc_contain_coacc_ads_0 d a0 a1 s1 c pl a2
     (power (Map bool) (predta_coacc d a0) (map_mini state d) x) H6 H0 H1 H2). apply
  (power_def_ok bool (ensemble_base state d) (predta_coacc d a0)
     (map_mini state d) x). unfold def_ok_app in |- *. intros. exact (predta_coacc_def_ok d a0 x0).
	exact (map_mini_appartient state d). exact H7.
Qed.

Lemma predta_coacc_contain_coacc_ads_3 :
 forall (d : preDTA) (a0 a1 : ad),
 coacc d a0 a1 ->
 preDTA_ref_ok d ->
 exists n : nat,
   MapGet bool (power (Map bool) (predta_coacc d a0) (map_mini state d) n) a1 =
   Some true.
Proof.
	intros. exact
  (coacc_ind predta_coacc_contain_coacc_ads_def_0
     predta_coacc_contain_coacc_ads_1 predta_coacc_contain_coacc_ads_2 d a0
     a1 H H H0).
Qed.

(* démo si mapget power predta_coacc = true alors l'état est coaccessible *)

Lemma pl_coacc_rev :
 forall (d : preDTA) (pl : prec_list) (a : ad),
 MapGet bool (pl_coacc d pl) a = Some true -> prec_occur pl a.
Proof.
	simple induction pl. simpl in |- *. intros. elim
  (map_replace_mapget_true_inv (map_or (pl_coacc d p) (pl_coacc d p0)) _ _ H1). intros. rewrite <- H2.
	exact (prec_hd a0 p p0). intros. elim (map_or_mapget_true_inv (pl_coacc d p) (pl_coacc d p0) a0 H2). intros. exact (prec_int0 a a0 p p0 (H _ H3)). intros. exact (prec_int1 a a0 p p0 (H0 _ H3)). intros. simpl in H. cut (true <> false).
	intro. elim (H0 (map_mini_mapget_false _ _ _ _ H)). intro.
	inversion H0.
Qed.

Lemma st_coacc_rev :
 forall (d : preDTA) (s : state) (a : ad),
 MapGet bool (st_coacc d s) a = Some true ->
 exists c : ad,
   (exists p : prec_list,
      MapGet prec_list s c = Some p /\ prec_occur p a).
Proof.
	simple induction s. intros. simpl in H. elim (map_mini_mapget_true _ _ _ H). intros. simpl in H. split with a. split with a0.
	simpl in |- *. rewrite (Neqb_correct a). split. reflexivity.
	exact (pl_coacc_rev _ _ _ H). intros. simpl in H1.
	elim (map_or_mapget_true_inv (st_coacc d m) (st_coacc d m0) a H1). intros. elim (H _ H2). intros. elim H3. intros.
	split with (Ndouble x). split with x0. induction  x as [| p]; simpl in |- *; exact H4. intros. elim (H0 _ H2). intros. elim H3. intros.
	split with (Ndouble_plus_one x). split with x0.
	induction  x as [| p]; simpl in |- *; exact H4.
Qed.

Lemma predta_coacc_0_rev :
 forall (d d' : preDTA) (b : ad) (m : Map bool),
 MapGet bool (predta_coacc_0 d d' m) b = Some true ->
 ensemble_base state d' m ->
 exists a : ad,
   (exists s : state,
      (exists c : ad,
         (exists p : prec_list,
            MapGet state d' a = Some s /\
            MapGet prec_list s c = Some p /\
            prec_occur p b /\ MapGet bool m a = Some true))).
Proof.
	simple induction d'; intros. induction  m as [| a a0| m1 Hrecm1 m0 Hrecm0]. simpl in H. elim (map_mini_mapget_true _ _ _ H). inversion H0.
	inversion H0. induction  m as [| a1 a2| m1 Hrecm1 m0 Hrecm0]. inversion H0. unfold ensemble_base in H0. simpl in H0. rewrite <- H0 in H.
	rewrite <- H0. simpl in H. rewrite (Neqb_correct a) in H. elim (bool_is_true_or_false a2); intros; rewrite H1 in H. simpl in H. split with a. split with a0. elim (st_coacc_rev _ _ _ H). intros. elim H2. intros. split with x. split with x0. simpl in |- *. rewrite (Neqb_correct a). rewrite H1. elim H3. intros. split. reflexivity. split. assumption.
	split. assumption. reflexivity. simpl in H. elim (map_mini_mapget_true _ _ _ H). inversion H0. induction  m1 as [| a a0| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
	inversion H2. inversion H2. clear Hrecm1_0 Hrecm1_1.
	unfold ensemble_base in H2. elim H2. intros. simpl in H1.
	elim (map_or_mapget_true_inv _ _ _ H1). intros. elim (H _ _ H5 H3). intros. elim H6. intros. elim H7. intros.
	elim H8. intros. decompose [and] H9. split with (Ndouble x). split with x0. split with x1. split with x2. split. induction  x as [| p]; simpl in |- *; exact H10. split. exact H12. split. exact H11. induction  x as [| p]; simpl in |- *; exact H14.
	intros. elim (H0 _ _ H5 H4). intros. elim H6. intros.
	elim H7. intros. elim H8. intros. decompose [and] H9.
	split with (Ndouble_plus_one x). split with x0.
	split with x1. split with x2. induction  x as [| p]; simpl in |- *; exact H9.
Qed.

Lemma predta_coacc_rev :
 forall (d : preDTA) (a : ad) (m : Map bool) (b : ad),
 MapGet bool (predta_coacc d a m) b = Some true ->
 ensemble_base state d m ->
 (exists a0 : ad,
    (exists s : state,
       (exists c : ad,
          (exists p : prec_list,
             MapGet state d a0 = Some s /\
             MapGet prec_list s c = Some p /\
             prec_occur p b /\ MapGet bool m a0 = Some true)))) \/ 
 a = b.
Proof.
	unfold predta_coacc in |- *. intros. elim (map_replace_mapget_true_inv _ _ _ H). intros.
	right. symmetry  in |- *. exact H1. intros. left. elim (predta_coacc_0_rev d d b m H1 H0). elim (predta_coacc_0_rev d d b m H1 H0). intros. elim H3.
	intros. elim H4. intros. elim H5. intros. decompose [and] H6. split with x0. split with x1. exact H4.
Qed.

Lemma predta_coacc_reverse :
 forall (n : nat) (d : preDTA) (a b : ad),
 MapGet bool (power (Map bool) (predta_coacc d a) (map_mini state d) n) b =
 Some true -> coacc d a b.
Proof.
	simple induction n. simpl in |- *. intros. elim (map_mini_mapget_true _ _ _ H). intros. simpl in H0. elim (predta_coacc_rev d a _ _ H0).
	intros. elim H1. intros. elim H2. intros. elim H3. intros.
	elim H4. intros. decompose [and] H5. elim
  (domain_equal_mapget bool state
     (predta_coacc d a
        (power (Map bool) (predta_coacc d a) (map_mini state d) n0)) d b true). intros. apply (coacc_nxt d a x b x0 x3 x2 x1 H9 H6 H8 H7). exact (H d a x H10). exact
  (domain_equal_symmetric state bool _ _
     (predta_coacc_def_ok d a
        (power (Map bool) (predta_coacc d a) (map_mini state d) n0))). exact H0. intros. rewrite H1. elim
  (domain_equal_mapget bool state
     (predta_coacc d a
        (power (Map bool) (predta_coacc d a) (map_mini state d) n0)) d b true). intros. exact (coacc_id d b x H2). apply
  (domain_equal_symmetric state bool d
     (predta_coacc d a
        (power (Map bool) (predta_coacc d a) (map_mini state d) n0))).
	exact
  (predta_coacc_def_ok d a
     (power (Map bool) (predta_coacc d a) (map_mini state d) n0)). exact H0.
	apply
  (power_def_ok bool (ensemble_base state d) (predta_coacc d a)
     (map_mini state d) n0). unfold def_ok_app in |- *. intros. exact (predta_coacc_def_ok d a x).
	exact (map_mini_appartient state d).
Qed.

Lemma predta_coacc_fix_0 :
 forall (d : preDTA) (a : ad),
 lower_fix_point bool (ensemble_base state d) (lemd d) 
   (predta_coacc d a) (predta_coacc_states d a).
Proof.
	intros. unfold predta_coacc_states in |- *. apply
  (iteres_lower_fix_point bool (ensemble_base state d) 
     (lemd d) (predta_coacc d a) (map_mini state d) 
     (S (MapCard state d)) (S (MapCard state d))). unfold mini in |- *.
	split. exact (map_mini_appartient state d). intros.
	split. exact (map_mini_appartient state d). split.
	exact H. elim (map_mini_mini state d). intros.
	exact (H1 x H). unfold def_ok_app in |- *. intros. exact (predta_coacc_def_ok d a x). exact (predta_coacc_increasing d a). exact (lattice_bounded d). exact (le_n_n _).
Qed.

Lemma predta_coacc_fix_1 :
 forall (d : preDTA) (a a0 : ad) (n : nat),
 MapGet bool (power (Map bool) (predta_coacc d a) (map_mini state d) n) a0 =
 Some true -> MapGet bool (predta_coacc_states d a) a0 = Some true.
Proof.
	intros. elim
  (domain_equal_mapget bool bool
     (power (Map bool) (predta_coacc d a) (map_mini state d) n)
     (predta_coacc_states d a) a0 true). intros. elim (bool_is_true_or_false x); intros; rewrite H1 in H0.
	exact H0. elim (predta_coacc_fix_0 d a); intros.
	unfold inf_fix_points in H3. elim
  (lem_get_leb (power (Map bool) (predta_coacc d a) (map_mini state d) n)
     (predta_coacc_states d a) a0 true false).
	elim
  (iteres_inf_fps bool (ensemble_base state d) (lemd d) 
     (predta_coacc d a) (map_mini state d) (predta_coacc_states d a) n). intros. elim H5. intros.
	exact H7. unfold mini in |- *. split. exact (map_mini_appartient state d). intros. split. exact (map_mini_appartient state d). split. exact H4. elim (map_mini_mini state d). intros. exact (H6 x0 H4). exact H2. exact (predta_coacc_increasing d a). exact H. exact H0.
	apply
  (domain_equal_transitive bool state bool
     (power (Map bool) (predta_coacc d a) (map_mini state d) n) d
     (predta_coacc_states d a)). apply
  (domain_equal_symmetric state bool d
     (power (Map bool) (predta_coacc d a) (map_mini state d) n)). apply
  (power_def_ok bool (ensemble_base state d) (predta_coacc d a)
     (map_mini state d) n). unfold def_ok_app in |- *. intros.
	exact (predta_coacc_def_ok d a x). exact (map_mini_appartient state d). unfold predta_coacc_states in |- *.
	apply
  (power_def_ok bool (ensemble_base state d) (predta_coacc d a)
     (map_mini state d) (S (MapCard state d))). unfold def_ok_app in |- *. intros. exact (predta_coacc_def_ok d a x). exact (map_mini_appartient state d). exact H.
Qed.

Lemma predta_coacc_fix_2 :
 forall (d : preDTA) (a a0 : ad),
 MapGet bool (predta_coacc_states d a) a0 = Some true ->
 exists n : nat,
   MapGet bool (power (Map bool) (predta_coacc d a) (map_mini state d) n) a0 =
   Some true.
Proof.
	unfold predta_coacc_states in |- *. intros. split with (S (MapCard state d)). exact H.        
Qed.

Lemma predta_coacc_fix :
 forall (d : preDTA) (a a0 : ad),
 preDTA_ref_ok d ->
 (MapGet bool (predta_coacc_states d a) a0 = Some true <-> coacc d a a0).
Proof.
	intros. split. intros. elim (predta_coacc_fix_2 _ _ _ H0). intros. exact (predta_coacc_reverse x d a a0 H1). intros. elim (predta_coacc_contain_coacc_ads_3 _ _ _ H0). intros. exact (predta_coacc_fix_1 d a a0 x H1). exact H.
Qed.

Lemma predta_coacc_0_fix :
 forall (d : preDTA) (a a0 : ad),
 preDTA_ref_ok d ->
 (MapGet bool (predta_coacc_states_0 d a) a0 = Some true <->
  coacc d a a0).
Proof.
	intros. unfold predta_coacc_states_0 in |- *. rewrite
  (lazy_power_eg_power bool eqm_bool (predta_coacc d a) 
     (map_mini state d) (S (MapCard state d))). exact (predta_coacc_fix d a a0 H). split. exact (eqm_bool_equal a1 b). intros. rewrite H0. exact (equal_eqm_bool b).
Qed.