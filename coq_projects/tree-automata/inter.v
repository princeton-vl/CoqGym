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


Require Import Arith.
Require Import NArith Ndec.
Require Import ZArith.
Require Import Bool.
From IntMap Require Import Allmaps.
Require Import bases.
Require Import defs.
Require Import semantics.
Require Import pl_path.
Require Import signature.

(* définition des adresses d'états produits *)

Fixpoint iad_conv_aux_0 (p : positive) : positive :=
  match p with
  | xH => 2%positive
  | xO p' => xO (xO (iad_conv_aux_0 p'))
  | xI p' => xO (xI (iad_conv_aux_0 p'))
  end.

Fixpoint iad_conv_aux_1 (p : positive) : positive :=
  match p with
  | xH => 1%positive
  | xO p' => xO (xO (iad_conv_aux_1 p'))
  | xI p' => xI (xO (iad_conv_aux_1 p'))
  end.

Fixpoint iad_conv_aux_2 (p0 p1 : positive) {struct p1} : positive :=
  match p0, p1 with
  | xH, xH => 3%positive
  | xH, xO p1' => xI (xO (iad_conv_aux_0 p1'))
  | xH, xI p1' => xI (xI (iad_conv_aux_0 p1'))
  | xO p0', xH => xO (xI (iad_conv_aux_1 p0'))
  | xO p0', xO p1' => xO (xO (iad_conv_aux_2 p0' p1'))
  | xO p0', xI p1' => xO (xI (iad_conv_aux_2 p0' p1'))
  | xI p0', xH => xI (xI (iad_conv_aux_1 p0'))
  | xI p0', xO p1' => xI (xO (iad_conv_aux_2 p0' p1'))
  | xI p0', xI p1' => xI (xI (iad_conv_aux_2 p0' p1'))
  end.

Definition iad_conv (a0 a1 : ad) : ad :=
  match a0, a1 with
  | N0, N0 => N0
  | N0, Npos p1 => Npos (iad_conv_aux_0 p1)
  | Npos p0, N0 => Npos (iad_conv_aux_1 p0)
  | Npos p0, Npos p1 => Npos (iad_conv_aux_2 p0 p1)
  end.

Lemma iad_conv_aux_0_inj :
 forall p0 p1 : positive, iad_conv_aux_0 p0 = iad_conv_aux_0 p1 -> p0 = p1.
Proof.
	simple induction p0. simple induction p1. intros. simpl in H1. inversion H1.
	rewrite (H p2 H3). trivial. intros. simpl in H1. inversion H1.
	intros. simpl in H0. inversion H0. intros. induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]. simpl in H0.
	inversion H0. simpl in H0. inversion H0. rewrite (H p1 H2). trivial.
	inversion H0. simple induction p1. intros. inversion H0. intros. inversion H0.
	intros. trivial.
Qed.

Lemma iad_conv_aux_1_inj :
 forall p0 p1 : positive, iad_conv_aux_1 p0 = iad_conv_aux_1 p1 -> p0 = p1.
Proof.
	simple induction p0. simple induction p1. intros. simpl in H1. inversion H1.
	rewrite (H p2 H3). trivial. intros. inversion H1. intros.
	inversion H0. intros. induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]. inversion H0. simpl in H0.
	inversion H0. rewrite (H p1 H2). trivial. inversion H0. simple induction p1.
	intros. inversion H0. intros. inversion H0. intros. trivial.
Qed.

Lemma iad_conv_aux_0_1_img_disj :
 forall p0 p1 : positive, iad_conv_aux_0 p0 <> iad_conv_aux_1 p1.
Proof.
	simple induction p0. simple induction p1. intros. intro. simpl in H1. inversion H1.
	intros. intro. inversion H1. intro. inversion H0. intros. induction  p1 as [p1 Hrecp1| p1 Hrecp1| ].
	intro. inversion H0. intro. unfold iad_conv_aux_0 in H0.
	unfold iad_conv_aux_1 in H0. inversion H0. exact (H p1 H2). intro.
	inversion H0. simple induction p1. intros. intro. inversion H0. intros. intro.
	inversion H0. intro. inversion H.
Qed.

Lemma iad_conv_aux_img_disj :
 forall p0 p1 p2 : positive,
 iad_conv_aux_0 p0 <> iad_conv_aux_2 p1 p2 /\
 iad_conv_aux_1 p0 <> iad_conv_aux_2 p1 p2.
Proof.
	simple induction p0. simple induction p1. simple induction p3. intros. split; intro.
	inversion H2. inversion H2. intros. split; intro. inversion H2.
	simpl in H2. inversion H2. elim (H p2 p4); intros. exact (H5 H4).
	split; intro. inversion H1. inversion H1. simple induction p3. intros.
	split; intro. simpl in H2. inversion H2. elim (H p2 p4); intros.
	exact (H3 H4). inversion H2. intros. split; intro. inversion H2.
	inversion H2. split; intro. simpl in H1. inversion H1.
	exact (iad_conv_aux_0_1_img_disj p p2 H3). inversion H1. simple induction p2.
	intros. split; intro. inversion H1. inversion H1. intros. 
	split; intro. inversion H1. simpl in H1. inversion H1.
	exact (iad_conv_aux_0_1_img_disj _ _ (sym_equal H3)).
	split; intro. inversion H0. inversion H0. intros. induction  p1 as [p1 Hrecp1| p1 Hrecp1| ].
	induction  p2 as [p2 Hrecp2| p2 Hrecp2| ]. split; intro. inversion H0. inversion H0.
	split; intro. inversion H0. inversion H0. split; intro. inversion H0.
	inversion H0. induction  p2 as [p2 Hrecp2| p2 Hrecp2| ]. split; intro. inversion H0. inversion H0.
	split; intro. simpl in H0. inversion H0. elim (H p1 p2). intros.
	exact (H1 H2). simpl in H0. inversion H0. elim (H p1 p2); intros.
	exact (H3 H2). split; intro. inversion H0. inversion H0. induction  p2 as [p2 Hrecp2| p2 Hrecp2| ].
	split; intro. inversion H0. inversion H0. split; intro. inversion H0.
	inversion H0. split; intro. inversion H0. inversion H0. simple induction p1.
	intros. induction  p2 as [p2 Hrecp2| p2 Hrecp2| ]. split; intro. inversion H0. inversion H0.
	split; intro. inversion H0. inversion H0. split; intro. inversion H0.
	inversion H0. intros. induction  p2 as [p2 Hrecp2| p2 Hrecp2| ]. split; intro. inversion H0.
	inversion H0. split; intro. inversion H0. inversion H0. split; intro.
	inversion H0. inversion H0. intros. induction  p2 as [p2 Hrecp2| p2 Hrecp2| ]. split; intro.
	inversion H. inversion H. split; intro. inversion H. inversion H.
	split; intro. inversion H. inversion H.
Qed.

Lemma iad_conv_aux_0_2_img_disj :
 forall p0 p1 p2 : positive, iad_conv_aux_0 p0 <> iad_conv_aux_2 p1 p2.
Proof.
	intros. elim (iad_conv_aux_img_disj p0 p1 p2). intros. assumption.
Qed.

Lemma iad_conv_aux_1_2_img_disj :
 forall p0 p1 p2 : positive, iad_conv_aux_1 p0 <> iad_conv_aux_2 p1 p2.
Proof.
	intros. elim (iad_conv_aux_img_disj p0 p1 p2). intros. assumption.
Qed.

Lemma iad_conv_aux_2_inj :
 forall p0 p1 p2 p3 : positive,
 iad_conv_aux_2 p0 p1 = iad_conv_aux_2 p2 p3 -> p0 = p2 /\ p1 = p3.
Proof.
	simple induction p0. intros. induction  p2 as [p2 Hrecp2| p2 Hrecp2| ]. induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]. induction  p3 as [p3 Hrecp3| p3 Hrecp3| ].
	simpl in H0. inversion H0. elim (H p1 p2 p3). intros. rewrite H1.
	rewrite H3. split. trivial. trivial. assumption. inversion H0.
	simpl in H0. inversion H0. elim (iad_conv_aux_1_2_img_disj p2 p p1 (sym_equal H2)). induction  p3 as [p3 Hrecp3| p3 Hrecp3| ]. inversion H0. simpl in H0.
	inversion H0. elim (H p1 p2 p3 H2). intros. rewrite H1. rewrite H3.
	split; trivial. inversion H0. induction  p3 as [p3 Hrecp3| p3 Hrecp3| ]. simpl in H0. inversion H0.
	elim (iad_conv_aux_1_2_img_disj p p2 p3 H2). inversion H0.
	simpl in H0. inversion H0. rewrite (iad_conv_aux_1_inj p p2 H2).
	split; trivial. induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]. induction  p3 as [p3 Hrecp3| p3 Hrecp3| ]. simpl in H0. inversion H0.
	inversion H0. inversion H0. induction  p3 as [p3 Hrecp3| p3 Hrecp3| ]. inversion H0. inversion H0.
	inversion H0. induction  p3 as [p3 Hrecp3| p3 Hrecp3| ]. inversion H0. inversion H0. inversion H0.
	induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]. induction  p3 as [p3 Hrecp3| p3 Hrecp3| ]. simpl in H0. inversion H0.
	elim (iad_conv_aux_0_2_img_disj p3 p p1 (sym_equal H2)).
	inversion H0. inversion H0. induction  p3 as [p3 Hrecp3| p3 Hrecp3| ]. inversion H0. simpl in H0.
	inversion H0. elim (iad_conv_aux_0_2_img_disj p3 p p1 (sym_equal H2)). inversion H0. induction  p3 as [p3 Hrecp3| p3 Hrecp3| ]. simpl in H0. 
	inversion H0. elim (iad_conv_aux_0_1_img_disj p3 p (sym_equal H2)). inversion H0. inversion H0. simple induction p1. intros. induction  p3 as [p3 Hrecp3| p3 Hrecp3| ].
	induction  p4 as [p4 Hrecp4| p4 Hrecp4| ]. inversion H1. inversion H1. inversion H1. induction  p4 as [p4 Hrecp4| p4 Hrecp4| ].
	simpl in H1. inversion H1. elim (H p2 p3 p4 H3). intros. rewrite H2.
	rewrite H4. split; trivial. inversion H1. simpl in H1. inversion H1.
	elim (iad_conv_aux_1_2_img_disj p3 p p2 (sym_equal H3)).
	induction  p4 as [p4 Hrecp4| p4 Hrecp4| ]. inversion H1. inversion H1. inversion H1. intros.
	induction  p3 as [p3 Hrecp3| p3 Hrecp3| ]. induction  p4 as [p4 Hrecp4| p4 Hrecp4| ]. inversion H1. inversion H1. inversion H1.
	induction  p4 as [p4 Hrecp4| p4 Hrecp4| ]. inversion H1. simpl in H1. inversion H1. 
	elim (H p2 p3 p4 H3). intros. rewrite H2. rewrite H4. split; trivial.
	inversion H1. induction  p4 as [p4 Hrecp4| p4 Hrecp4| ]; inversion H1. intros. induction  p2 as [p2 Hrecp2| p2 Hrecp2| ].
	induction  p3 as [p3 Hrecp3| p3 Hrecp3| ]. inversion H0. inversion H0. inversion H0. induction  p3 as [p3 Hrecp3| p3 Hrecp3| ].
	simpl in H0. inversion H0. elim (iad_conv_aux_1_2_img_disj p p2 p3 H2).
	inversion H0. simpl in H0. inversion H0. rewrite (iad_conv_aux_1_inj _ _ H2). split; trivial. induction  p3 as [p3 Hrecp3| p3 Hrecp3| ]; inversion H0. intros.
	induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]. induction  p2 as [p2 Hrecp2| p2 Hrecp2| ]. induction  p3 as [p3 Hrecp3| p3 Hrecp3| ]. simpl in H. inversion H.
	elim (iad_conv_aux_0_2_img_disj _ _ _ H1). inversion H. simpl in H.
	inversion H. elim (iad_conv_aux_0_1_img_disj _ _ H1). 
	induction  p3 as [p3 Hrecp3| p3 Hrecp3| ]; inversion H. induction  p3 as [p3 Hrecp3| p3 Hrecp3| ]. simpl in H. inversion H.
	rewrite (iad_conv_aux_0_inj _ _ H1). split; trivial. inversion H.
	simpl in H. inversion H.  induction  p2 as [p2 Hrecp2| p2 Hrecp2| ]. induction  p3 as [p3 Hrecp3| p3 Hrecp3| ]. inversion H.
	simpl in H. inversion H. elim (iad_conv_aux_0_2_img_disj _ _ _ H1).
	inversion H. induction  p3 as [p3 Hrecp3| p3 Hrecp3| ]; inversion H. induction  p3 as [p3 Hrecp3| p3 Hrecp3| ]. inversion H.
	simpl in H. inversion H. rewrite (iad_conv_aux_0_inj _ _ H1).
	split; trivial. inversion H. induction  p2 as [p2 Hrecp2| p2 Hrecp2| ]. induction  p3 as [p3 Hrecp3| p3 Hrecp3| ]. simpl in H.
	inversion H. inversion H. simpl in H. inversion H.
	induction  p3 as [p3 Hrecp3| p3 Hrecp3| ]; inversion H. induction  p3 as [p3 Hrecp3| p3 Hrecp3| ]. simpl in H. inversion H.
	inversion H. split; trivial.
Qed.

Lemma iad_conv_inj :
 forall a0 a1 a2 a3 : ad,
 iad_conv a0 a1 = iad_conv a2 a3 -> a0 = a2 /\ a1 = a3.
Proof.
	simple induction a0; simple induction a1; simple induction a2;
  simple induction a3; intros.
	split; trivial. inversion H. inversion H. inversion H. inversion H.
	simpl in H. inversion H. rewrite (iad_conv_aux_0_inj _ _ H1).
	split; trivial. simpl in H. inversion H. elim (iad_conv_aux_0_1_img_disj _ _ H1). simpl in H. inversion H.
	elim (iad_conv_aux_0_2_img_disj _ _ _ H1). inversion H.
	simpl in H. inversion H. elim (iad_conv_aux_0_1_img_disj _ _ (sym_equal H1)). simpl in H. inversion H. rewrite (iad_conv_aux_1_inj _ _ H1). split; trivial. simpl in H.
	inversion H. elim (iad_conv_aux_1_2_img_disj _ _ _ H1).
	inversion H. simpl in H. inversion H. 
	elim (iad_conv_aux_0_2_img_disj _ _ _ (sym_equal H1)).
	simpl in H. inversion H.
	elim (iad_conv_aux_1_2_img_disj _ _ _ (sym_equal H1)).
	simpl in H. inversion H. elim (iad_conv_aux_2_inj _ _ _ _ H1).
	intros. rewrite H0. rewrite H2. split; trivial.
Qed.

(* surjectivité de iad_conv *)

Definition iad_conv_prop (p : positive) : Prop :=
  (exists q : positive, p = iad_conv_aux_0 q) \/
  (exists q : positive, p = iad_conv_aux_1 q) \/
  (exists q : positive, (exists r : positive, p = iad_conv_aux_2 q r)).

Lemma iad_conv_surj_0 :
 forall p : positive, iad_conv_prop p -> iad_conv_prop (xO (xO p)).
Proof.
	intros. elim H. intro. elim H0. intros. left. split with (xO x).
	simpl in |- *. rewrite <- H1. trivial. intros. elim H0. intros. elim H1.
	intros. right. left. split with (xO x). simpl in |- *. rewrite <- H2.
	trivial. intro. elim H1. intros. elim H2. intros. right. right.
	split with (xO x). split with (xO x0). simpl in |- *. rewrite <- H3.
	trivial.
Qed.

Lemma iad_conv_surj_1 :
 forall p : positive, iad_conv_prop p -> iad_conv_prop (xO (xI p)).
intros.
	elim H; intros. elim H0. intros. left. split with (xI x).
	simpl in |- *. rewrite <- H1. trivial. elim H0; intros. elim H1. intros.
	right. right. split with (xO x). split with 1%positive. simpl in |- *. rewrite H2.
	trivial. elim H1. intros. elim H2. intros. right. right.
	split with (xO x). split with (xI x0). simpl in |- *. rewrite H3.
	trivial.
Qed.

Lemma iad_conv_surj_2 :
 forall p : positive, iad_conv_prop p -> iad_conv_prop (xI (xO p)).
Proof.
	intros. elim H; intros. elim H0. intros. right. right. 
	split with 1%positive. split with (xO x). simpl in |- *. rewrite H1. trivial.
	elim H0; intros. right. left. elim H1. intros. split with (xI x).
	simpl in |- *. rewrite H2. trivial. elim H1. intros. elim H2. intros.
	right. right. split with (xI x). split with (xO x0). simpl in |- *.
	rewrite H3. trivial.
Qed.

Lemma iad_conv_surj_3 :
 forall p : positive, iad_conv_prop p -> iad_conv_prop (xI (xI p)).
Proof.
	intros. elim H; intros. elim H0. intros. right. right.
	split with 1%positive. split with (xI x). simpl in |- *. rewrite H1. trivial.
	elim H0; intros. right. right. elim H1. intros. split with (xI x).
	split with 1%positive. simpl in |- *. rewrite H2. trivial. elim H1. intros.
	elim H2. intros. right. right. split with (xI x). split with (xI x0).
	simpl in |- *. rewrite H3. trivial.
Qed.

Lemma iad_conv_surj_4 :
 forall p : positive,
 iad_conv_prop p /\ iad_conv_prop (xO p) /\ iad_conv_prop (xI p).
Proof.
	simple induction p. intros. elim H. intros. elim H1. intros. split.
	exact H3. split. exact (iad_conv_surj_1 p0 H0). 
	exact (iad_conv_surj_3 p0 H0). intros. elim H. intros. elim H1. 
	intros. split. exact H2. split. exact (iad_conv_surj_0 p0 H0).
	exact (iad_conv_surj_2 p0 H0). split. right. left. split with 1%positive.
	trivial. split. left. split with 1%positive. reflexivity. right. right.
	split with 1%positive. split with 1%positive. reflexivity.
Qed.

Lemma iad_conv_surj_5 : forall p : positive, iad_conv_prop p.
Proof.
	intros. elim (iad_conv_surj_4 p). intros. assumption.
Qed.

Lemma iad_conv_surj :
 forall a : ad, exists b : ad, (exists c : ad, a = iad_conv b c).
Proof.
	simple induction a. split with N0. split with N0. reflexivity.
	intro. elim (iad_conv_surj_5 p). intros. elim H. intros.
	split with N0. split with (Npos x). simpl in |- *. rewrite H0.
	trivial. intros. elim H. intros. elim H0. intros. split with (Npos x). split with N0. simpl in |- *. rewrite H1. trivial. intros.
	elim H0. intros. elim H1. intros. split with (Npos x). split with (Npos x0). simpl in |- *. rewrite H2. trivial.
Qed.

(* fonctions réciproques gauche et droite de iad_conv *)

Inductive ad_couple : Set :=
    cpla : ad -> ad -> ad_couple.

Fixpoint iad_conv_inv_0 (p : positive) : ad_couple :=
  match p with
  | xH => cpla (Npos 1) N0
  | xO xH => cpla N0 (Npos 1)
  | xI xH => cpla (Npos 1) (Npos 1)
  | xO (xO p') =>
      match iad_conv_inv_0 p' with
      | cpla N0 N0 => cpla N0 N0
      | cpla N0 (Npos p1) => cpla N0 (Npos (xO p1))
      | cpla (Npos p0) N0 => cpla (Npos (xO p0)) N0
      | cpla (Npos p0) (Npos p1) => cpla (Npos (xO p0)) (Npos (xO p1))
      end
  | xO (xI p') =>
      match iad_conv_inv_0 p' with
      | cpla N0 N0 => cpla N0 (Npos 1)
      | cpla N0 (Npos p1) => cpla N0 (Npos (xI p1))
      | cpla (Npos p0) N0 => cpla (Npos (xO p0)) (Npos 1)
      | cpla (Npos p0) (Npos p1) => cpla (Npos (xO p0)) (Npos (xI p1))
      end
  | xI (xO p') =>
      match iad_conv_inv_0 p' with
      | cpla N0 N0 => cpla (Npos 1) N0
      | cpla N0 (Npos p1) => cpla (Npos 1) (Npos (xO p1))
      | cpla (Npos p0) N0 => cpla (Npos (xI p0)) N0
      | cpla (Npos p0) (Npos p1) => cpla (Npos (xI p0)) (Npos (xO p1))
      end
  | xI (xI p') =>
      match iad_conv_inv_0 p' with
      | cpla N0 N0 => cpla (Npos 1) (Npos 1)
      | cpla N0 (Npos p1) => cpla (Npos 1) (Npos (xI p1))
      | cpla (Npos p0) N0 => cpla (Npos (xI p0)) (Npos 1)
      | cpla (Npos p0) (Npos p1) => cpla (Npos (xI p0)) (Npos (xI p1))
      end
  end.

Definition iad_conv_inv (a : ad) : ad_couple :=
  match a with
  | N0 => cpla N0 N0
  | Npos p => iad_conv_inv_0 p
  end.

Lemma iad_inv_0 :
 forall p : positive, iad_conv_inv_0 (iad_conv_aux_0 p) = cpla N0 (Npos p).
Proof.
	intros. induction  p as [p Hrecp| p Hrecp| ]. unfold iad_conv_aux_0 in |- *. simpl in |- *.
	unfold iad_conv_aux_0 in Hrecp. rewrite Hrecp. reflexivity.
	unfold iad_conv_aux_0 in |- *. unfold iad_conv_aux_0 in Hrecp.
	simpl in |- *. rewrite Hrecp. reflexivity. simpl in |- *. reflexivity.
Qed.

Lemma iad_inv_1 :
 forall p : positive, iad_conv_inv_0 (iad_conv_aux_1 p) = cpla (Npos p) N0.
Proof.
	simple induction p. intros. unfold iad_conv_aux_1 in |- *. unfold iad_conv_aux_1 in H.
	simpl in |- *. rewrite H. reflexivity. intros. unfold iad_conv_aux_1 in H.
	unfold iad_conv_aux_1 in |- *. simpl in |- *. rewrite H. reflexivity. simpl in |- *.
	reflexivity.
Qed.

Lemma iad_inv_2 :
 forall p0 p1 : positive,
 iad_conv_inv_0 (iad_conv_aux_2 p0 p1) = cpla (Npos p0) (Npos p1).
Proof.
	simple induction p0. simple induction p1. intros. simpl in |- *. rewrite (H p2). reflexivity. 
	intros. simpl in |- *. rewrite (H p2). reflexivity. simpl in |- *. rewrite (iad_inv_1 p).
	reflexivity. simple induction p1. intros. simpl in |- *. rewrite (H p2). reflexivity.
	intros. simpl in |- *. rewrite (H p2). reflexivity. simpl in |- *. rewrite (iad_inv_1 p).
	reflexivity. simple induction p1. intros. simpl in |- *. rewrite (iad_inv_0 p).
	reflexivity. intros. simpl in |- *. rewrite (iad_inv_0 p). reflexivity.
	simpl in |- *. reflexivity.
Qed.

Lemma iad_inv_inv_0 :
 forall a0 a1 : ad, iad_conv_inv (iad_conv a0 a1) = cpla a0 a1.
Proof.
	simple induction a0. simple induction a1. simpl in |- *. reflexivity. simpl in |- *.
	exact iad_inv_0. simple induction a1. simpl in |- *. exact (iad_inv_1 p).
	intros. exact (iad_inv_2 p p0).
Qed.

Lemma iad_inv_inv_1 :
 forall a a0 a1 : ad, iad_conv_inv a = cpla a0 a1 -> iad_conv a0 a1 = a.
Proof.
	intros. elim (iad_conv_surj a). intros. elim H0. intros.
	rewrite H1 in H. rewrite (iad_inv_inv_0 x x0) in H. inversion H.
	rewrite H3 in H1. rewrite H4 in H1. rewrite H1. reflexivity.
Qed.

(* algorithme de calcul d'intersection : calcul de l'état produit *)

(* calcul d'une prec_list produit *)

Fixpoint pl_produit_0 (a : ad) (la pl : prec_list) 
 (n : nat) {struct n} : prec_list -> prec_list :=
  fun l : prec_list =>
  match n with
  | O => prec_empty
  | S m =>
      match pl with
      | prec_empty => l
      | prec_cons a0 la0 ls0 =>
          prec_cons (iad_conv a a0) (pl_produit_1 la m la0)
            (pl_produit_0 a la ls0 m l)
      end
  end
 
 with pl_produit_1 (pl0 : prec_list) (n : nat) {struct n} :
 prec_list -> prec_list :=
  fun pl1 : prec_list =>
  match n with
  | O => prec_empty
  | S m =>
      match pl0, pl1 with
      | prec_empty, prec_empty => prec_empty
      | prec_empty, prec_cons a1 la1 ls1 => prec_empty
      | prec_cons a0 la0 ls0, prec_empty => prec_empty
      | prec_cons a0 la0 ls0, prec_cons a1 la1 ls1 =>
          pl_produit_0 a0 la0 (prec_cons a1 la1 ls1) m
            (pl_produit_1 ls0 m (prec_cons a1 la1 ls1))
      end
  end.

Fixpoint pl_card (pl : prec_list) : nat :=
  match pl with
  | prec_empty => 1
  | prec_cons a la ls => S (pl_card la + pl_card ls)
  end.

(* terminaison des fonctions précédantes *)

Definition pl_essence (pl0 pl1 : prec_list) : nat :=
  pl_card pl0 + pl_card pl1.

Definition pl_produit (pl0 pl1 : prec_list) : prec_list :=
  pl_produit_1 pl0 (pl_essence pl0 pl1) pl1.

Lemma pl_card_0 : forall pl : prec_list, 1 <= pl_card pl.
Proof.
	simple induction pl. intros. simpl in |- *. exact (le_n_S 0 (pl_card p + pl_card p0) (le_O_n (pl_card p + pl_card p0))). simpl in |- *. exact (le_n_n 1).
Qed.

Lemma pl_ess_aux_0 : forall pl : prec_list, 1 <= pl_card pl.
Proof.
	simple induction pl. intros. simpl in |- *. exact (le_n_S _ _ (le_O_n _)).
	simpl in |- *. exact (le_n_n _).
Qed.

Lemma pl_ess_aux_1 :
 forall (a : ad) (la ls : prec_list),
 S (pl_card la) <= pl_card (prec_cons a la ls).
Proof.
	intros. simpl in |- *. apply (le_n_S (pl_card la) (pl_card la + pl_card ls)). exact (le_plus_l (pl_card la) (pl_card ls)).
Qed.

Lemma pl_ess_aux_2 :
 forall (a : ad) (la ls : prec_list),
 S (pl_card ls) <= pl_card (prec_cons a la ls).
Proof.
	intros. simpl in |- *. exact
  (le_n_S (pl_card ls) (pl_card la + pl_card ls)
     (le_plus_r (pl_card la) (pl_card ls))).
Qed.

Lemma pl_ess_invar_0 : forall pl0 pl1 : prec_list, 1 <= pl_essence pl0 pl1.
Proof.
	intros. unfold pl_essence in |- *. apply (le_plus_trans 1 (pl_card pl0) (pl_card pl1)). exact (pl_ess_aux_0 pl0).
Qed.

Lemma pl_ess_invar_1 :
 forall (a a' : ad) (la ls la' ls' : prec_list),
 S (pl_essence la (prec_cons a' la' ls')) <=
 pl_essence (prec_cons a la ls) (prec_cons a' la' ls').
Proof.
	intros. unfold pl_essence in |- *. rewrite (S_plus_l (pl_card la) (pl_card (prec_cons a' la' ls'))). exact
  (plus_le_compat (S (pl_card la)) (pl_card (prec_cons a la ls))
     (pl_card (prec_cons a' la' ls')) (pl_card (prec_cons a' la' ls'))
     (pl_ess_aux_1 a la ls) (le_n_n (pl_card (prec_cons a' la' ls')))).
Qed.

Lemma pl_ess_invar_2 :
 forall (a a' : ad) (la ls la' ls' : prec_list),
 S (pl_essence ls (prec_cons a' la' ls')) <=
 pl_essence (prec_cons a la ls) (prec_cons a' la' ls').
Proof.
	intros. unfold pl_essence in |- *. rewrite (S_plus_l (pl_card ls) (pl_card (prec_cons a' la' ls'))). exact
  (plus_le_compat (S (pl_card ls)) (pl_card (prec_cons a la ls))
     (pl_card (prec_cons a' la' ls')) (pl_card (prec_cons a' la' ls'))
     (pl_ess_aux_2 a la ls) (le_n_n (pl_card (prec_cons a' la' ls')))).
Qed.

Lemma pl_ess_invar_3 :
 forall (a' : ad) (la la' ls' : prec_list),
 S (pl_essence la la') <= pl_essence la (prec_cons a' la' ls').
Proof.
	intros. unfold pl_essence in |- *. rewrite (S_plus_r (pl_card la) (pl_card la')). exact
  (plus_le_compat (pl_card la) (pl_card la) (S (pl_card la'))
     (pl_card (prec_cons a' la' ls')) (le_n_n (pl_card la))
     (pl_ess_aux_1 a' la' ls')).
Qed.

Lemma pl_ess_invar_4 :
 forall (a' : ad) (la la' ls' : prec_list),
 S (pl_essence la ls') <= pl_essence la (prec_cons a' la' ls').
Proof.
	intros. unfold pl_essence in |- *. rewrite (S_plus_r (pl_card la) (pl_card ls')). exact
  (plus_le_compat (pl_card la) (pl_card la) (S (pl_card ls'))
     (pl_card (prec_cons a' la' ls')) (le_n_n (pl_card la))
     (pl_ess_aux_2 a' la' ls')).
Qed.

Lemma pl_ess_invar_5 : forall pl0 pl1 : prec_list, 2 <= pl_essence pl0 pl1.
Proof.
	intros. exact
  (plus_le_compat 1 (pl_card pl0) 1 (pl_card pl1) (pl_card_0 pl0)
     (pl_card_0 pl1)).
Qed.

(* invariance du résultat de pl_produit lorsqu'on augmente la quantité d'essence *)

Fixpoint pl_prof (pl : prec_list) : nat :=
  match pl with
  | prec_empty => 0
  | prec_cons a la ls => S (max (pl_prof la) (pl_prof ls))
  end.

Lemma indprinciple_0 :
 forall P0 P1 : prec_list -> prec_list -> Prop,
 (forall p : prec_list, P0 p prec_empty) ->
 (forall p : prec_list, P1 p prec_empty) ->
 (forall p : prec_list, P1 prec_empty p) ->
 (forall (a : ad) (la ls p : prec_list),
  P0 p ls -> P1 p la -> P0 p (prec_cons a la ls)) ->
 (forall (a : ad) (la ls p : prec_list),
  P0 la p -> P1 ls p -> P1 (prec_cons a la ls) p) ->
 forall n : nat,
 (forall p p' : prec_list,
  pl_prof p <= n -> pl_prof p' <= n -> P0 p p' /\ P1 p p') ->
 forall p p' : prec_list,
 pl_prof p <= S n -> pl_prof p' <= S n -> P0 p p' /\ P1 p p'.
Proof.
	intros. induction  p as [a p1 Hrecp1 p0 Hrecp0| ]. induction  p' as [a0 p'1 Hrecp'1 p'0 Hrecp'0| ]. simpl in H5. simpl in H6. cut (pl_prof p1 <= n).
	cut (pl_prof p0 <= n). cut (pl_prof p'1 <= n). cut (pl_prof p'0 <= n). intros.
	split. apply (H2 a0 p'1 p'0 (prec_cons a p1 p0)). elim Hrecp'0. intros. assumption.
	exact (le_trans (pl_prof p'0) n (S n) H7 (le_n_Sn n)). intros. exact (H4 p1 p'0 H10 H7).
	intros. exact (H4 p0 p'0 H9 H7). elim Hrecp'1. intros. exact H12. exact (le_trans (pl_prof p'1) n (S n) H8 (le_n_Sn n)). intros. exact (H4 p1 p'1 H10 H8). intros.
	exact (H4 p0 p'1 H9 H8). apply (H3 a p1 p0 (prec_cons a0 p'1 p'0)). elim Hrecp1.
	intros. assumption. exact (le_trans (pl_prof p1) n (S n) H10 (le_n_Sn n)). elim Hrecp0.
	intros. assumption. exact (le_trans (pl_prof p0) n (S n) H9 (le_n_Sn n)).  
	exact
  (le_trans (pl_prof p'0) (max (pl_prof p'1) (pl_prof p'0)) n
     (le_max_r (pl_prof p'1) (pl_prof p'0)) (le_S_n _ _ H6)). exact
  (le_trans (pl_prof p'1) (max (pl_prof p'1) (pl_prof p'0)) n
     (le_max_l (pl_prof p'1) (pl_prof p'0)) (le_S_n _ _ H6)). exact
  (le_trans (pl_prof p0) (max (pl_prof p1) (pl_prof p0)) n
     (le_max_r (pl_prof p1) (pl_prof p0)) (le_S_n _ _ H5)).
	exact
  (le_trans (pl_prof p1) (max (pl_prof p1) (pl_prof p0)) n
     (le_max_l (pl_prof p1) (pl_prof p0)) (le_S_n _ _ H5)). split. exact (H (prec_cons a p1 p0)). exact (H0 (prec_cons a p1 p0)). induction  p' as [a p'1 Hrecp'1 p'0 Hrecp'0| ]. split. apply (H2 a p'1 p'0 prec_empty). elim Hrecp'0. intros.
	assumption. simpl in H6. exact
  (le_trans (pl_prof p'0) n (S n)
     (le_trans _ _ _ (le_max_r (pl_prof p'1) (pl_prof p'0)) (le_S_n _ _ H6))
     (le_n_Sn n)). exact (H1 p'1).
	exact (H1 (prec_cons a p'1 p'0)). split. exact (H prec_empty). exact (H0 prec_empty).
Qed.

Lemma indprinciple_1 :
 forall P0 P1 : prec_list -> prec_list -> Prop,
 (forall p : prec_list, P0 p prec_empty) ->
 (forall p : prec_list, P1 p prec_empty) ->
 (forall p : prec_list, P1 prec_empty p) ->
 (forall (a : ad) (la ls p : prec_list),
  P0 p ls -> P1 p la -> P0 p (prec_cons a la ls)) ->
 (forall (a : ad) (la ls p : prec_list),
  P0 la p -> P1 ls p -> P1 (prec_cons a la ls) p) ->
 forall p p' : prec_list,
 pl_prof p <= 0 -> pl_prof p' <= 0 -> P0 p p' /\ P1 p p'.
Proof.
	intros. induction  p as [a p1 Hrecp1 p0 Hrecp0| ]. induction  p' as [a0 p'1 Hrecp'1 p'0 Hrecp'0| ]. simpl in H4. elim (le_Sn_O (max (pl_prof p1) (pl_prof p0)) H4). simpl in H4. elim (le_Sn_O (max (pl_prof p1) (pl_prof p0)) H4).
	induction  p' as [a p'1 Hrecp'1 p'0 Hrecp'0| ]. simpl in H5. elim (le_Sn_O (max (pl_prof p'1) (pl_prof p'0)) H5).
	split. exact (H prec_empty). exact (H0 prec_empty).
Qed.

Lemma indprinciple_2 :
 forall P0 P1 : prec_list -> prec_list -> Prop,
 (forall p : prec_list, P0 p prec_empty) ->
 (forall p : prec_list, P1 p prec_empty) ->
 (forall p : prec_list, P1 prec_empty p) ->
 (forall (a : ad) (la ls p : prec_list),
  P0 p ls -> P1 p la -> P0 p (prec_cons a la ls)) ->
 (forall (a : ad) (la ls p : prec_list),
  P0 la p -> P1 ls p -> P1 (prec_cons a la ls) p) ->
 forall (n : nat) (p p' : prec_list),
 pl_prof p <= n -> pl_prof p' <= n -> P0 p p' /\ P1 p p'.
Proof.
	simple induction n. exact (indprinciple_1 P0 P1 H H0 H1 H2 H3). exact (indprinciple_0 P0 P1 H H0 H1 H2 H3).
Qed.

Lemma indprinciple_pl :
 forall P0 P1 : prec_list -> prec_list -> Prop,
 (forall p : prec_list, P0 p prec_empty) ->
 (forall p : prec_list, P1 p prec_empty) ->
 (forall p : prec_list, P1 prec_empty p) ->
 (forall (a : ad) (la ls p : prec_list),
  P0 p ls -> P1 p la -> P0 p (prec_cons a la ls)) ->
 (forall (a : ad) (la ls p : prec_list),
  P0 la p -> P1 ls p -> P1 (prec_cons a la ls) p) ->
 forall p p' : prec_list, P0 p p' /\ P1 p p'.
Proof.
	intros. elim
  (indprinciple_2 P0 P1 H H0 H1 H2 H3 (max (pl_prof p) (pl_prof p')) p p').
	intros. split; assumption. exact (le_max_l _ _). exact (le_max_r _ _).
Qed.

Definition pl_produit_0_incr (p0 p1 : prec_list) : Prop :=
  forall (a : ad) (l : prec_list) (n : nat),
  pl_essence p0 p1 <= n ->
  pl_produit_0 a p0 p1 (pl_essence p0 p1) l = pl_produit_0 a p0 p1 n l.

Definition pl_produit_1_incr (p0 p1 : prec_list) : Prop :=
  forall n : nat,
  pl_essence p0 p1 <= n ->
  pl_produit_1 p0 (pl_essence p0 p1) p1 = pl_produit_1 p0 n p1.

Lemma pl_product_0_0 : forall p : prec_list, pl_produit_0_incr p prec_empty.
Proof.
	unfold pl_produit_0_incr in |- *. intros. induction  p as [a0 p1 Hrecp1 p0 Hrecp0| ]. simpl in |- *. 
	unfold pl_essence in H. induction  n as [| n Hrecn]. elim
  (le_Sn_O 0
     (le_trans (pl_card prec_empty)
        (pl_card (prec_cons a0 p1 p0) + pl_card prec_empty) 0 
        (le_plus_l _ _) H)). simpl in |- *. reflexivity. simpl in |- *.
	induction  n as [| n Hrecn]. unfold pl_essence in H. simpl in H. elim (le_Sn_O 1 H).
	simpl in |- *. reflexivity.
Qed.

Lemma pl_product_0_1 : forall p : prec_list, pl_produit_1_incr p prec_empty.
Proof.
	simple induction p. unfold pl_produit_1_incr in |- *. intros. simpl in |- *. induction  n as [| n Hrecn].
	simpl in |- *. reflexivity. simpl in |- *. reflexivity. unfold pl_produit_1_incr in |- *.
	intros. induction  n as [| n Hrecn]; simpl in |- *. reflexivity. reflexivity.
Qed.

Lemma pl_product_0_2 : forall p : prec_list, pl_produit_1_incr prec_empty p.
Proof.
	unfold pl_produit_1_incr in |- *. intros. induction  p as [a p1 Hrecp1 p0 Hrecp0| ]. simpl in |- *. induction  n as [| n Hrecn].
	simpl in |- *. reflexivity. simpl in |- *. reflexivity. simpl in |- *. induction  n as [| n Hrecn]. simpl in |- *.
	reflexivity. reflexivity.
Qed.

Lemma pl_product_0_3 :
 forall (a : ad) (la ls p : prec_list),
 pl_produit_0_incr p ls ->
 pl_produit_1_incr p la -> pl_produit_0_incr p (prec_cons a la ls).
Proof.
	unfold pl_produit_0_incr in |- *. unfold pl_produit_1_incr in |- *. intros.
	induction  n as [| n Hrecn]. elim
  (le_Sn_O 0
     (le_trans 1 (pl_essence p (prec_cons a la ls)) 0
        (pl_ess_invar_0 p (prec_cons a la ls)) H1)). elim (nat_sum (pl_essence p (prec_cons a la ls))). intros. elim (le_Sn_O 0). exact
  (eq_ind (pl_essence p (prec_cons a la ls)) (fun n : nat => 1 <= n)
     (pl_ess_invar_0 p (prec_cons a la ls)) 0 H2). intros. elim H2. intros.
	rewrite H3. replace (pl_produit_0 a0 p (prec_cons a la ls) (S x) l) with
  (prec_cons (iad_conv a0 a) (pl_produit_1 p x la) (pl_produit_0 a0 p ls x l)). replace (pl_produit_0 a0 p (prec_cons a la ls) (S n) l) with
  (prec_cons (iad_conv a0 a) (pl_produit_1 p n la) (pl_produit_0 a0 p ls n l)). rewrite <- (H0 x). rewrite <- (H0 n). rewrite <- (H a0 l x).
	rewrite <- (H a0 l n). reflexivity. exact (le_S_n _ _ (le_trans _ _ _ (pl_ess_invar_4 a p la ls) H1)). exact
  (le_S_n _ _
     (le_trans _ _ _ (pl_ess_invar_4 a p la ls)
        (eq_ind (pl_essence p (prec_cons a la ls))
           (fun z : nat => pl_essence p (prec_cons a la ls) <= z)
           (le_n_n (pl_essence p (prec_cons a la ls))) 
           (S x) H3))). exact (le_S_n _ _ (le_trans _ _ _ (pl_ess_invar_3 a p la ls) H1)). exact
  (le_S_n _ _
     (le_trans _ _ _ (pl_ess_invar_3 a p la ls)
        (eq_ind (pl_essence p (prec_cons a la ls))
           (fun z : nat => pl_essence p (prec_cons a la ls) <= z)
           (le_n_n (pl_essence p (prec_cons a la ls))) 
           (S x) H3))). reflexivity. reflexivity.
Qed.

Lemma pl_product_0_4 :
 forall (a : ad) (la ls p : prec_list),
 pl_produit_0_incr la p ->
 pl_produit_1_incr ls p -> pl_produit_1_incr (prec_cons a la ls) p.
Proof.
	unfold pl_produit_0_incr in |- *. unfold pl_produit_1_incr in |- *. intros. induction  n as [| n Hrecn].
	elim (le_Sn_O 0 (le_trans _ _ _ (pl_ess_invar_0 (prec_cons a la ls) p) H1)).
	elim (nat_sum (pl_essence (prec_cons a la ls) p)); intro. elim (le_Sn_O 0).
	exact
  (eq_ind (pl_essence (prec_cons a la ls) p) (fun n : nat => 1 <= n)
     (pl_ess_invar_0 (prec_cons a la ls) p) 0 H2). elim H2. intros. rewrite H3.
	induction  p as [a0 p1 Hrecp1 p0 Hrecp0| ]. replace (pl_produit_1 (prec_cons a la ls) (S x) (prec_cons a0 p1 p0)) with
  (pl_produit_0 a la (prec_cons a0 p1 p0) x
     (pl_produit_1 ls x (prec_cons a0 p1 p0))). replace (pl_produit_1 (prec_cons a la ls) (S n) (prec_cons a0 p1 p0)) with
  (pl_produit_0 a la (prec_cons a0 p1 p0) n
     (pl_produit_1 ls n (prec_cons a0 p1 p0))). rewrite <- (H0 x). rewrite <- (H0 n). rewrite <-
  (H a
     (pl_produit_1 ls (pl_essence ls (prec_cons a0 p1 p0))
        (prec_cons a0 p1 p0)) x). rewrite <-
  (H a
     (pl_produit_1 ls (pl_essence ls (prec_cons a0 p1 p0))
        (prec_cons a0 p1 p0)) n). reflexivity.
	exact (le_S_n _ _ (le_trans _ _ _ (pl_ess_invar_1 a a0 la ls p1 p0) H1)).
	exact
  (le_S_n _ _
     (le_trans _ _ _ (pl_ess_invar_1 a a0 la ls p1 p0)
        (eq_ind (pl_essence (prec_cons a la ls) (prec_cons a0 p1 p0))
           (fun z : nat =>
            pl_essence (prec_cons a la ls) (prec_cons a0 p1 p0) <= z)
           (le_n_n (pl_essence (prec_cons a la ls) (prec_cons a0 p1 p0)))
           (S x) H3))).
	exact (le_S_n _ _ (le_trans _ _ _ (pl_ess_invar_2 a a0 la ls p1 p0) H1)).
	exact
  (le_S_n _ _
     (le_trans _ _ _ (pl_ess_invar_2 a a0 la ls p1 p0)
        (eq_ind (pl_essence (prec_cons a la ls) (prec_cons a0 p1 p0))
           (fun z : nat =>
            pl_essence (prec_cons a la ls) (prec_cons a0 p1 p0) <= z)
           (le_n_n _) (S x) H3))). reflexivity. reflexivity. simpl in |- *. reflexivity.
Qed.

Lemma pl_product_0_5 :
 forall p p' : prec_list, pl_produit_0_incr p p' /\ pl_produit_1_incr p p'.
Proof.
	exact
  (indprinciple_pl pl_produit_0_incr pl_produit_1_incr pl_product_0_0
     pl_product_0_1 pl_product_0_2 pl_product_0_3 pl_product_0_4).
Qed.

Lemma pl_product_0 :
 forall p0 p1 : prec_list,
 (forall (a : ad) (l : prec_list) (n : nat),
  pl_essence p0 p1 <= n ->
  pl_produit_0 a p0 p1 (pl_essence p0 p1) l = pl_produit_0 a p0 p1 n l) /\
 (forall n : nat,
  pl_essence p0 p1 <= n ->
  pl_produit_1 p0 (pl_essence p0 p1) p1 = pl_produit_1 p0 n p1).
Proof.
	exact
  (indprinciple_pl pl_produit_0_incr pl_produit_1_incr pl_product_0_0
     pl_product_0_1 pl_product_0_2 pl_product_0_3 pl_product_0_4).
Qed.

Lemma pl_product_0_invar_essence :
 forall (p0 p1 : prec_list) (n : nat),
 pl_essence p0 p1 <= n ->
 pl_produit_1 p0 (pl_essence p0 p1) p1 = pl_produit_1 p0 n p1.
Proof.
	intro. intro. elim (pl_product_0 p0 p1). intros. exact (H0 n H1).
Qed.

Lemma pl_product_1 :
 forall (a : ad) (la pl l : prec_list) (n : nat),
 pl_essence la pl <= n ->
 pl_produit_0 a la pl n l = prec_empty -> pl = prec_empty.
Proof.
	intros. induction  n as [| n Hrecn]. elim (le_Sn_n 0 (le_trans _ _ _ (pl_ess_invar_0 la pl) H)).
	induction  pl as [a0 pl1 Hrecpl1 pl0 Hrecpl0| ]. simpl in H0. inversion H0. reflexivity.
Qed.

(* passage au produit de la propriété pl_tl_length *)

Definition pl_tl_length_prod_def_0 (pl0 pl1 : prec_list) : Prop :=
  forall (l : prec_list) (a : ad) (n m : nat),
  pl_essence pl0 pl1 <= m ->
  pl_tl_length pl0 n ->
  pl_tl_length l (S n) \/ l = prec_empty ->
  (pl_tl_length pl1 (S n) -> pl_tl_length (pl_produit_0 a pl0 pl1 m l) (S n)) /\
  (pl1 = prec_empty ->
   (pl_tl_length l (S n) -> pl_tl_length (pl_produit_0 a pl0 pl1 m l) (S n)) /\
   (l = prec_empty -> pl_produit_0 a pl0 pl1 m l = prec_empty)).

Definition pl_tl_length_prod_def_1 (pl0 pl1 : prec_list) : Prop :=
  forall n m : nat,
  pl_tl_length pl0 n ->
  pl_tl_length pl1 n ->
  pl_essence pl0 pl1 <= m -> pl_tl_length (pl_produit_1 pl0 m pl1) n.

Lemma pl_tl_length_prod_0 :
 forall p : prec_list, pl_tl_length_prod_def_0 p prec_empty.
Proof.
	unfold pl_tl_length_prod_def_0 in |- *. intros. split. intros. inversion H2.
	intros. split. intros. elim (nat_sum m); intro. rewrite H4 in H.
	elim (le_Sn_n 0 (le_trans _ _ _ (pl_ess_invar_0 p prec_empty) H)).
	elim H4. intros. rewrite H5. simpl in |- *. exact H3. intros. elim (nat_sum m).
	intro. rewrite H4. reflexivity. intros. elim H4. elim H4. intros.
	rewrite H5. simpl in |- *. exact H3.
Qed.

Lemma pl_tl_length_prod_1 :
 forall p : prec_list, pl_tl_length_prod_def_1 p prec_empty.
Proof.
	unfold pl_tl_length_prod_def_1 in |- *. intros. elim (nat_sum m); intros. 
	rewrite H2. simpl in |- *. exact H0. elim H2. intros. rewrite H3. simpl in |- *.
	induction  p as [a p1 Hrecp1 p0 Hrecp0| ]; exact H0.
Qed.

Lemma pl_tl_length_prod_2 :
 forall p : prec_list, pl_tl_length_prod_def_1 prec_empty p.
Proof.
	unfold pl_tl_length_prod_def_1 in |- *. intros. elim (nat_sum m); intros.
	rewrite H2. simpl in |- *. exact H. elim H2. intros. rewrite H3. simpl in |- *.
	induction  p as [a p1 Hrecp1 p0 Hrecp0| ]; exact H.
Qed.

Lemma pl_tl_length_prod_3 :
 forall (a : ad) (la ls p : prec_list),
 pl_tl_length_prod_def_0 p ls ->
 pl_tl_length_prod_def_1 p la ->
 pl_tl_length_prod_def_0 p (prec_cons a la ls).
Proof.
	unfold pl_tl_length_prod_def_0 in |- *. unfold pl_tl_length_prod_def_1 in |- *.
	intros. split. intros. elim (nat_sum m); intro. rewrite H5 in H1.
	elim (le_Sn_O 0 (le_trans _ _ _ (pl_ess_invar_0 p (prec_cons a la ls)) H1)). elim H5. intros. rewrite H6. replace (pl_produit_0 a0 p (prec_cons a la ls) (S x) l) with
  (prec_cons (iad_conv a0 a) (pl_produit_1 p x la) (pl_produit_0 a0 p ls x l)). elim (H l a0 n x).
	intros. cut (pl_tl_length (pl_produit_1 p x la) n). intro. inversion H4.
	elim H3. intros. elim (H8 (sym_eq H13)). intros.
	apply
  (pl_tl_propag (iad_conv a0 a) (pl_produit_1 p x la)
     (pl_produit_0 a0 p prec_empty x l) n H9). elim (nat_sum x); intro. rewrite H18 in H16.
	simpl in H16. cut (pl_tl_length prec_empty (S n)). intro. inversion H19.
	exact (H16 H15). elim H18. intros. rewrite H19. simpl in |- *. exact H15.
	intro. replace (pl_produit_0 a0 p prec_empty x l) with prec_empty.
	exact (pl_tl_S (iad_conv a0 a) (pl_produit_1 p x la) n H9).
	elim (nat_sum x); intro. rewrite H16. reflexivity. elim H16. intros.
	rewrite H17. simpl in |- *. symmetry  in |- *. exact H15. exact
  (pl_tl_propag (iad_conv a0 a) (pl_produit_1 p x la)
     (pl_produit_0 a0 p ls x l) n H9 (H7 H15)).
	apply (H0 n x H2). inversion H4. exact H10. exact H11. unfold pl_essence in |- *.
	unfold pl_essence in H1. rewrite H6 in H1. simpl in H1. elim (le_or_lt (pl_card p + pl_card la) x); intro. exact H9. elim (le_Sn_n (S x)).
	apply (le_trans (S (S x)) (pl_card p + S (pl_card la + pl_card ls)) (S x)). rewrite <- (plus_Snm_nSm (pl_card p) (pl_card la + pl_card ls)). simpl in |- *. apply (le_n_S (S x) (pl_card p + (pl_card la + pl_card ls))). exact
  (le_trans _ _ _ (lt_le_S _ _ H9)
     (plus_le_compat (pl_card p) (pl_card p) (pl_card la)
        (pl_card la + pl_card ls) (le_n_n _) (le_plus_l _ _))). exact H1. unfold pl_essence in |- *.
	unfold pl_essence in H1. rewrite H6 in H1. simpl in H1. elim (le_or_lt (pl_card p + pl_card ls) x); intro. exact H7. elim (le_Sn_n (S x)).
	apply (le_trans (S (S x)) (pl_card p + S (pl_card la + pl_card ls)) (S x)). rewrite <- (plus_Snm_nSm (pl_card p) (pl_card la + pl_card ls)). simpl in |- *. apply (le_n_S (S x) (pl_card p + (pl_card la + pl_card ls))). exact
  (le_trans _ _ _ (lt_le_S _ _ H7)
     (plus_le_compat (pl_card p) (pl_card p) (pl_card ls)
        (pl_card la + pl_card ls) (le_n_n _) (le_plus_r _ _))). exact H1. exact H2. exact H3.
	reflexivity. intros. inversion H4.
Qed.

Lemma pl_tl_length_prod_4 :
 forall (a : ad) (la ls p : prec_list),
 pl_tl_length_prod_def_0 la p ->
 pl_tl_length_prod_def_1 ls p ->
 pl_tl_length_prod_def_1 (prec_cons a la ls) p.
Proof.
	unfold pl_tl_length_prod_def_0 in |- *. unfold pl_tl_length_prod_def_1 in |- *. intros.
	elim (nat_sum m); intros. rewrite H4 in H3. elim (le_Sn_O 0 (le_trans _ _ _ (pl_ess_invar_0 (prec_cons a la ls) p) H3)). elim H4. intros. 
	rewrite H5. elim (pl_sum p). intros. rewrite H6 in H2. inversion H2.
	rewrite <- H8 in H1. inversion H1. intros. elim H6. intros. elim H7.
	intros. elim H8. intros. rewrite H9. replace (pl_produit_1 (prec_cons a la ls) (S x) (prec_cons x0 x1 x2)) with
  (pl_produit_0 a la (prec_cons x0 x1 x2) x
     (pl_produit_1 ls x (prec_cons x0 x1 x2))). inversion H1.
	rewrite <- H9. elim (H (pl_produit_1 prec_empty x p) a n0 x). intros.
	rewrite <- H11 in H2. exact (H15 H2). rewrite H5 in H3. unfold pl_essence in H3. unfold pl_essence in |- *. simpl in H3. elim (le_or_lt (pl_card la + pl_card p) x). intro. exact H15. intro. elim (le_Sn_n (S x)). apply (le_trans (S (S x)) (S (pl_card la + pl_card ls + pl_card p)) (S x)). apply (le_n_S (S x) (pl_card la + pl_card ls + pl_card p)). exact
  (le_trans _ _ _ (lt_le_S _ _ H15)
     (plus_le_compat (pl_card la) (pl_card la + pl_card ls) 
        (pl_card p) (pl_card p) (le_plus_l _ _) (le_n_n _))). exact H3. exact H14. right. elim (nat_sum x).
	intro. rewrite H15. reflexivity. intros. elim H15. intros. rewrite H16.
	induction  p as [a1 p1 Hrecp1 p0 Hrecp0| ]; reflexivity. elim (H (pl_produit_1 ls x (prec_cons x0 x1 x2)) a n0 x). intros. rewrite <- H12 in H2. rewrite H9 in H16. rewrite H9 in H2.
	exact (H16 H2). unfold pl_essence in |- *. unfold pl_essence in H3. rewrite H5 in H3.
	simpl in H3. elim (le_or_lt (pl_card la + pl_card p) x). intro.
	exact H16. intro. elim (le_Sn_n (S x)). apply (le_trans (S (S x)) (S (pl_card la + pl_card ls + pl_card p)) (S x)).
	apply (le_n_S (S x) (pl_card la + pl_card ls + pl_card p)).
	exact
  (le_trans _ _ _ (lt_le_S _ _ H16)
     (plus_le_compat (pl_card la) (pl_card la + pl_card ls) 
        (pl_card p) (pl_card p) (le_plus_l _ _) (le_n_n _))). exact H3. exact H14. left. rewrite <- H9. apply (H0 (S n0) x H15).
	rewrite H12. exact H2. unfold pl_essence in |- *. unfold pl_essence in H3.
	rewrite H5 in H3. simpl in H3. elim (le_or_lt (pl_card ls + pl_card p) x); intro. exact H16. elim (le_Sn_n (S x)). apply (le_trans (S (S x)) (S (pl_card la + pl_card ls + pl_card p)) (S x)).
	apply (le_n_S (S x) (pl_card la + pl_card ls + pl_card p)).
	exact
  (le_trans _ _ _ (lt_le_S _ _ H16)
     (plus_le_compat (pl_card ls) (pl_card la + pl_card ls) 
        (pl_card p) (pl_card p) (le_plus_r _ _) (le_n_n _))). exact H3. reflexivity.
Qed.

Lemma pl_tl_length_prod_5 :
 forall p p' : prec_list,
 pl_tl_length_prod_def_0 p p' /\ pl_tl_length_prod_def_1 p p'.
Proof.
	exact
  (indprinciple_pl pl_tl_length_prod_def_0 pl_tl_length_prod_def_1
     pl_tl_length_prod_0 pl_tl_length_prod_1 pl_tl_length_prod_2
     pl_tl_length_prod_3 pl_tl_length_prod_4).
Qed.

Lemma pl_tl_length_prod :
 forall (pl0 pl1 : prec_list) (n : nat),
 pl_tl_length pl0 n ->
 pl_tl_length pl1 n -> pl_tl_length (pl_produit pl0 pl1) n.
Proof.
	intros. elim (pl_tl_length_prod_5 pl0 pl1). intros. unfold pl_produit in |- *.
	exact (H2 n (pl_essence pl0 pl1) H H0 (le_n_n _)).
Qed.

(* lemmes de conservation des pl_path_incl par passage au pl_produit *)

Lemma pl_produit_path_incl_0 :
 forall (n : nat) (a : ad) (la pl l : prec_list) (plp : pl_path),
 pl_path_incl plp l ->
 plp <> pl_path_nil ->
 pl_essence la pl <= n -> pl_path_incl plp (pl_produit_0 a la pl n l).
Proof.
	simple induction n. intros. elim (le_Sn_O 0 (le_trans _ _ _ (pl_ess_invar_0 la pl) H1)). intros. induction  pl as [a0 pl1 Hrecpl1 pl0 Hrecpl0| ]. replace (pl_produit_0 a la (prec_cons a0 pl1 pl0) (S n0) l) with
  (prec_cons (iad_conv a a0) (pl_produit_1 la n0 pl1)
     (pl_produit_0 a la pl0 n0 l)). apply
  (pl_path_incl_next plp (iad_conv a a0) (pl_produit_1 la n0 pl1)
     (pl_produit_0 a la pl0 n0 l)). apply (H a la pl0 l plp H0 H1). unfold pl_essence in |- *. unfold pl_essence in H2. elim (le_or_lt (pl_card la + pl_card pl0) n0). intro. exact H3. intro. simpl in H2.
	cut
  (pl_card la + S (S (pl_card pl0)) <=
   pl_card la + S (pl_card pl1 + pl_card pl0)). intro. cut (pl_card la + S (S (pl_card pl0)) <= S n0). intros. cut (pl_card la + S (S (pl_card pl0)) = S (S (pl_card la + pl_card pl0))). intro. rewrite H6 in H5.
	elim
  (le_Sn_n _
     (le_trans _ _ _
        (le_trans _ _ _ (le_n_S _ _ (le_n_S _ _ (lt_le_S _ _ H3))) H5)
        (le_n_Sn (S n0)))). rewrite <- (plus_Snm_nSm (pl_card la) (S (pl_card pl0))). simpl in |- *. rewrite <- (plus_Snm_nSm (pl_card la) (pl_card pl0)). simpl in |- *. reflexivity. exact (le_trans _ _ _ H4 H2). apply
  (plus_le_compat (pl_card la) (pl_card la) (S (S (pl_card pl0)))
     (S (pl_card pl1 + pl_card pl0))). exact (le_n_n _). apply (le_n_S (S (pl_card pl0)) (pl_card pl1 + pl_card pl0)). exact
  (plus_le_compat 1 (pl_card pl1) (pl_card pl0) (pl_card pl0) 
     (pl_card_0 pl1) (le_n_n _)). exact H1.
	reflexivity. simpl in |- *. exact H0.
Qed.

Fixpoint pl_path_product (p0 p1 : pl_path) {struct p1} : pl_path :=
  match p0, p1 with
  | pl_path_nil, pl_path_nil => pl_path_nil
  | pl_path_nil, pl_path_cons a b => pl_path_nil
  | pl_path_cons a b, pl_path_nil => pl_path_nil
  | pl_path_cons a0 b0, pl_path_cons a1 b1 =>
      pl_path_cons (iad_conv a0 a1) (pl_path_product b0 b1)
  end.

Lemma pl_path_product_n :
 forall (n : nat) (p0 p1 : pl_path),
 pl_path_length p0 = n ->
 pl_path_length p1 = n -> pl_path_length (pl_path_product p0 p1) = n.
Proof.
	simple induction n. intros. induction  p0 as [| a p0 Hrecp0]. induction  p1 as [| a p1 Hrecp1]. simpl in |- *. reflexivity.
	inversion H0. inversion H. intros. induction  p0 as [| a p0 Hrecp0]. inversion H0. induction  p1 as [| a0 p1 Hrecp1].
	inversion H1. simpl in |- *. simpl in H0. simpl in H1. inversion H0. inversion H1.
	rewrite H3. rewrite (H p0 p1 H3 H4). reflexivity.
Qed.

Lemma pl_produit_path_incl_inj :
 forall (plp0 plp1 plp2 plp3 : pl_path) (n : nat),
 pl_path_length plp0 = n ->
 pl_path_length plp1 = n ->
 pl_path_length plp2 = n ->
 pl_path_length plp3 = n ->
 pl_path_product plp0 plp1 = pl_path_product plp2 plp3 ->
 plp0 = plp2 /\ plp1 = plp3.
Proof.
	simple induction plp0. simple induction plp1. simple induction plp2. simple induction plp3. intros.
	split; reflexivity. intros. simpl in H2. rewrite <- H2 in H3. simpl in H3.
	inversion H3. intros. simpl in H0. rewrite <- H0 in H2. simpl in H2.
	inversion H2. intros. simpl in H0. rewrite <- H0 in H1. simpl in H1.
	inversion H1. intros. induction  plp1 as [| a0 plp1 Hrecplp1]. simpl in H0. simpl in H1. rewrite <- H1 in H0. inversion H0. induction  plp2 as [| a1 plp2 Hrecplp2]. simpl in H2. rewrite <- H2 in H0.
	simpl in H0. inversion H0. induction  plp3 as [| a2 plp3 Hrecplp3]. simpl in H3. rewrite <- H3 in H0.
	simpl in H0. inversion H0. simpl in H4. inversion H4. elim (iad_conv_inj _ _ _ _ H6). intros. rewrite H5. rewrite H8. elim (nat_sum n). intros.
	rewrite H9 in H0. simpl in H0. inversion H0. intros. elim H9. intros.
	rewrite H10 in H0. rewrite H10 in H1. rewrite H10 in H2. rewrite H10 in H3.
	simpl in H0. simpl in H1. simpl in H2. simpl in H3. inversion H0. inversion H1.
	inversion H2. inversion H3. elim (H plp1 plp2 plp3 x H12 H13 H14 H15 H7).
	intros. rewrite H11. rewrite H16. split; reflexivity.
Qed.

Definition pl_produit_path_incl_def_0 (pl0 pl1 : prec_list) :=
  forall (n m : nat) (plp0 plp1 : pl_path) (a : ad) (l : prec_list),
  pl_path_incl plp0 (prec_cons a pl0 prec_empty) ->
  pl_tl_length pl0 n ->
  pl_path_incl plp1 pl1 ->
  pl_tl_length pl1 (S n) ->
  pl_essence pl0 pl1 <= m ->
  pl_path_incl (pl_path_product plp0 plp1) (pl_produit_0 a pl0 pl1 m l).

Definition pl_produit_path_incl_def_1 (pl0 pl1 : prec_list) :=
  forall (n m : nat) (plp0 plp1 : pl_path),
  pl_path_incl plp0 pl0 ->
  pl_tl_length pl0 n ->
  pl_path_incl plp1 pl1 ->
  pl_tl_length pl1 n ->
  pl_essence pl0 pl1 <= m ->
  pl_path_incl (pl_path_product plp0 plp1) (pl_produit_1 pl0 m pl1).

Lemma pl_produit_path_incl_1_0 :
 forall p : prec_list, pl_produit_path_incl_def_0 p prec_empty.
Proof.
	unfold pl_produit_path_incl_def_0 in |- *. intros. inversion H2.
Qed.

Lemma pl_produit_path_incl_1_1 :
 forall p : prec_list, pl_produit_path_incl_def_1 p prec_empty.
Proof.
	unfold pl_produit_path_incl_def_1 in |- *. intros. inversion H1. inversion H2.
	rewrite <- H6 in H0. inversion H0. rewrite <- H5 in H. inversion H. simpl in |- *.
	elim (nat_sum m). intros. rewrite H8. simpl in |- *. exact pl_path_incl_nil.
	intros. elim H8. intros. rewrite H9. simpl in |- *. exact pl_path_incl_nil.
Qed.

Lemma pl_produit_path_incl_1_2 :
 forall p : prec_list, pl_produit_path_incl_def_1 prec_empty p.
Proof.
	unfold pl_produit_path_incl_def_1 in |- *. intros. inversion H0. rewrite <- H5 in H2.
	inversion H2. rewrite <- H4 in H1. inversion H1. inversion H. simpl in |- *.
	elim (nat_sum m); intros. rewrite H8. simpl in |- *. exact pl_path_incl_nil.
	elim H8. intros. rewrite H9. simpl in |- *. exact pl_path_incl_nil.
Qed.

Lemma pl_produit_path_incl_1_3 :
 forall (a : ad) (la ls p : prec_list),
 pl_produit_path_incl_def_0 p ls ->
 pl_produit_path_incl_def_1 p la ->
 pl_produit_path_incl_def_0 p (prec_cons a la ls).
Proof.
	unfold pl_produit_path_incl_def_1 in |- *. unfold pl_produit_path_incl_def_0 in |- *.
	intros. elim (nat_sum m); intros. rewrite H6 in H5. elim (le_Sn_O 0 (le_trans _ _ _ (pl_ess_invar_0 p (prec_cons a la ls)) H5)). elim H6.
	intros. rewrite H7. replace (pl_produit_0 a0 p (prec_cons a la ls) (S x) l) with
  (prec_cons (iad_conv a0 a) (pl_produit_1 p x la) (pl_produit_0 a0 p ls x l)). inversion H3. inversion H1. simpl in |- *. apply
  (pl_path_incl_cons (pl_path_product plp2 plp) (iad_conv a0 a)
     (pl_produit_1 p x la) (pl_produit_0 a0 p ls x l)). apply (H0 n x plp2 plp H15 H2 H10). 
	inversion H4. exact H19. exact H20.  rewrite H7 in H5. unfold pl_essence in |- *.
	unfold pl_essence in H5. elim (le_or_lt (pl_card p + pl_card la) x); intros. exact H18. cut (S (pl_card la) <= pl_card (prec_cons a la ls)).
	intro. elim (le_Sn_n (S x)). apply (le_trans (S (S x)) (pl_card p + S (pl_card la)) (S x)). rewrite <- (plus_Snm_nSm (pl_card p) (pl_card la)). simpl in |- *. exact (le_n_S _ _ (lt_le_S _ _ H18)). exact
  (le_trans _ _ _
     (plus_le_compat (pl_card p) (pl_card p) (S (pl_card la))
        (pl_card (prec_cons a la ls)) (le_n_n _) H19) H5). simpl in |- *. exact
  (le_n_S (pl_card la) (pl_card la + pl_card ls)
     (le_plus_l (pl_card la) (pl_card ls))).
	inversion H16. elim (H18 (sym_eq H19)). apply
  (pl_path_incl_next (pl_path_product plp0 plp1) (iad_conv a0 a)
     (pl_produit_1 p x la) (pl_produit_0 a0 p ls x l)). apply (H n x plp0 plp1 a0 l H1 H2). exact H11. inversion H4. rewrite <- H17 in H11.
	inversion H11. elim (H13 (sym_eq H19)). exact H19.
	rewrite H7 in H5. unfold pl_essence in |- *. unfold pl_essence in H5.
	elim (le_or_lt (pl_card p + pl_card ls) x). intro. exact H14.
	intro. simpl in H5. rewrite <- (plus_Snm_nSm (pl_card p) (pl_card la + pl_card ls)) in H5. simpl in H5. elim (le_Sn_n (S x)).
	apply (le_trans (S (S x)) (S (pl_card p + (pl_card la + pl_card ls))) (S x)). apply (le_n_S (S x) (pl_card p + (pl_card la + pl_card ls))). exact
  (le_trans _ _ _ (lt_le_S _ _ H14)
     (plus_le_compat (pl_card p) (pl_card p) (pl_card ls)
        (pl_card la + pl_card ls) (le_n_n _)
        (le_plus_r (pl_card la) (pl_card ls)))). exact H5. 
	inversion H1. induction  plp1 as [| a3 plp1 Hrecplp1]. elim (H13 (refl_equal _)).
	simpl in |- *. intro. inversion H19. inversion H17. elim (H19 (sym_eq H20)). reflexivity.
Qed.

Lemma pl_produit_path_incl_1_4 :
 forall (a : ad) (la ls p : prec_list),
 pl_produit_path_incl_def_0 la p ->
 pl_produit_path_incl_def_1 ls p ->
 pl_produit_path_incl_def_1 (prec_cons a la ls) p.
Proof.
	unfold pl_produit_path_incl_def_0 in |- *. unfold pl_produit_path_incl_def_1 in |- *.
	intros. induction  p as [a0 p1 Hrecp1 p0 Hrecp0| ]. clear Hrecp0. clear Hrecp1. elim (nat_sum m).
	intro. rewrite H6 in H5. elim
  (le_Sn_O 0
     (le_trans _ _ _
        (pl_ess_invar_0 (prec_cons a la ls) (prec_cons a0 p1 p0)) H5)).
	intros. elim H6. intros. rewrite H7. replace (pl_produit_1 (prec_cons a la ls) (S x) (prec_cons a0 p1 p0)) with
  (pl_produit_0 a la (prec_cons a0 p1 p0) x
     (pl_produit_1 ls x (prec_cons a0 p1 p0))). inversion H1.
	elim (nat_sum n). intros. rewrite H13 in H2. inversion H2. intros.
	elim H13. intros. rewrite <- H8. rewrite H9. rewrite H8. apply (H x0 x plp0 plp1 a (pl_produit_1 ls x (prec_cons a0 p1 p0))). rewrite H8 in H9. rewrite <- H9. exact (pl_path_incl_cons plp a la prec_empty H10).
	rewrite H14 in H2. inversion H2. exact H16. exact H17. exact H3.
	rewrite H14 in H4. exact H4. unfold pl_essence in |- *. unfold pl_essence in H5.
	elim (le_or_lt (pl_card la + pl_card (prec_cons a0 p1 p0)) x).
	intro. exact H15. intro. rewrite H7 in H5. elim (le_Sn_n (S x)).
	apply
  (le_trans (S (S x))
     (pl_card (prec_cons a la ls) + pl_card (prec_cons a0 p1 p0)) 
     (S x)). simpl in |- *. simpl in H15.
	apply (le_n_S (S x) (pl_card la + pl_card ls + S (pl_card p1 + pl_card p0))). apply
  (le_trans (S x) (pl_card la + S (pl_card p1 + pl_card p0))
     (pl_card la + pl_card ls + S (pl_card p1 + pl_card p0))). exact (lt_le_S _ _ H15).
	exact
  (plus_le_compat (pl_card la) (pl_card la + pl_card ls)
     (S (pl_card p1 + pl_card p0)) (S (pl_card p1 + pl_card p0))
     (le_plus_l (pl_card la) (pl_card ls)) (le_n_n _)). exact H5.
	apply
  (pl_produit_path_incl_0 x a la (prec_cons a0 p1 p0)
     (pl_produit_1 ls x (prec_cons a0 p1 p0)) (pl_path_product plp0 plp1)). apply (H0 n x plp0 plp1). exact H11. inversion H2. rewrite <- H17 in H11. inversion H11.
	rewrite <- H19 in H13. elim (H13 (refl_equal pl_path_nil)).
	exact H19. exact H3. exact H4. rewrite H7 in H5. unfold pl_essence in |- *.
	unfold pl_essence in H5. elim (le_or_lt (pl_card ls + pl_card (prec_cons a0 p1 p0)) x). intro. exact H14. intro. simpl in H14.
	simpl in H5. elim (le_Sn_n (S x)). apply
  (le_trans (S (S x))
     (S (pl_card la + pl_card ls + S (pl_card p1 + pl_card p0))) 
     (S x)). apply (le_n_S (S x) (pl_card la + pl_card ls + S (pl_card p1 + pl_card p0))). exact
  (le_trans (S x) (pl_card ls + S (pl_card p1 + pl_card p0))
     (pl_card la + pl_card ls + S (pl_card p1 + pl_card p0))
     (lt_le_S x (pl_card ls + S (pl_card p1 + pl_card p0)) H14)
     (plus_le_compat (pl_card ls) (pl_card la + pl_card ls)
        (S (pl_card p1 + pl_card p0)) (S (pl_card p1 + pl_card p0))
        (le_plus_r (pl_card la) (pl_card ls)) (le_n_n _))). exact H5. 
	inversion H3. inversion H1. simpl in |- *. intro. inversion H24. induction  plp0 as [| a4 plp0 Hrecplp0].
	elim (H24 (refl_equal pl_path_nil)). simpl in |- *. intro. inversion H25.
	induction  plp0 as [| a3 plp0 Hrecplp0]. elim (H13 (refl_equal _)). induction  plp1 as [| a4 plp1 Hrecplp1].
	elim (H19 (refl_equal _)). simpl in |- *. intro. inversion H20.
	rewrite H7 in H5. unfold pl_essence in H5. unfold pl_essence in |- *. simpl in H5.
	simpl in |- *. elim (le_or_lt (pl_card la + S (pl_card p1 + pl_card p0)) x). intro. exact H14. intro. elim (le_Sn_n (S x)). apply
  (le_trans (S (S x))
     (S (pl_card la + pl_card ls + S (pl_card p1 + pl_card p0)))). apply (le_n_S (S x) (pl_card la + pl_card ls + S (pl_card p1 + pl_card p0))). exact
  (le_trans (S x) (pl_card la + S (pl_card p1 + pl_card p0))
     (pl_card la + pl_card ls + S (pl_card p1 + pl_card p0))
     (lt_le_S _ _ H14)
     (plus_le_compat (pl_card la) (pl_card la + pl_card ls)
        (S (pl_card p1 + pl_card p0)) (S (pl_card p1 + pl_card p0))
        (le_plus_l _ _) (le_n_n _))). exact H5. reflexivity. inversion H4.
	rewrite <- H7 in H2. inversion H2.
Qed.

Lemma pl_produit_path_incl_1_5 :
 forall p p' : prec_list,
 pl_produit_path_incl_def_0 p p' /\ pl_produit_path_incl_def_1 p p'.
Proof.
	exact
  (indprinciple_pl pl_produit_path_incl_def_0 pl_produit_path_incl_def_1
     pl_produit_path_incl_1_0 pl_produit_path_incl_1_1
     pl_produit_path_incl_1_2 pl_produit_path_incl_1_3
     pl_produit_path_incl_1_4).
Qed.

Lemma pl_produit_path_incl_1 :
 forall (pl0 pl1 : prec_list) (n m : nat) (plp0 plp1 : pl_path),
 pl_path_incl plp0 pl0 ->
 pl_tl_length pl0 n ->
 pl_path_incl plp1 pl1 ->
 pl_tl_length pl1 n ->
 pl_essence pl0 pl1 <= m ->
 pl_path_incl (pl_path_product plp0 plp1) (pl_produit_1 pl0 m pl1).
Proof.
	intros. elim (pl_produit_path_incl_1_5 pl0 pl1). intros.
	unfold pl_produit_path_incl_def_1 in H5.
	exact (H5 n m plp0 plp1 H H0 H1 H2 H3).
Qed.

Lemma pl_produit_path_incl_2 :
 forall (pl0 pl1 : prec_list) (n : nat) (plp0 plp1 : pl_path),
 pl_path_incl plp0 pl0 ->
 pl_tl_length pl0 n ->
 pl_path_incl plp1 pl1 ->
 pl_tl_length pl1 n ->
 pl_path_incl (pl_path_product plp0 plp1) (pl_produit pl0 pl1).
Proof.
	intros. unfold pl_produit in |- *. exact
  (pl_produit_path_incl_1 pl0 pl1 n (pl_essence pl0 pl1) plp0 plp1 H H0 H1 H2
     (le_n_n _)).
Qed.

Definition pl_produit_path_incl_def_2 (pl0 pl1 : prec_list) :=
  forall (n m : nat) (plp : pl_path) (a : ad) (l : prec_list),
  pl_path_incl plp (pl_produit_0 a pl0 pl1 m l) ->
  pl_tl_length pl0 n ->
  pl_tl_length pl1 (S n) ->
  pl_essence pl0 pl1 <= m ->
  (exists plp0 : pl_path,
     (exists plp1 : pl_path,
        plp = pl_path_product plp0 plp1 /\
        pl_path_incl plp0 (prec_cons a pl0 prec_empty) /\
        pl_path_incl plp1 pl1)) \/ pl_path_incl plp l.

Definition pl_produit_path_incl_def_3 (pl0 pl1 : prec_list) :=
  forall (n m : nat) (plp : pl_path),
  pl_path_incl plp (pl_produit_1 pl0 m pl1) ->
  pl_tl_length pl0 n ->
  pl_tl_length pl1 n ->
  pl_essence pl0 pl1 <= m ->
  exists plp0 : pl_path,
    (exists plp1 : pl_path,
       plp = pl_path_product plp0 plp1 /\
       pl_path_incl plp0 pl0 /\ pl_path_incl plp1 pl1).

Lemma pl_produit_path_incl_3_0 :
 forall p : prec_list, pl_produit_path_incl_def_2 p prec_empty.
Proof.
	unfold pl_produit_path_incl_def_2 in |- *. intros. elim (nat_sum m). intro.
	rewrite H3 in H2. elim (le_Sn_n 0 (le_trans _ _ _ (pl_ess_invar_0 p prec_empty) H2)). intros. elim H3. intros. rewrite H4 in H. simpl in H.
	right. exact H.
Qed.

Lemma pl_produit_path_incl_3_1 :
 forall p : prec_list, pl_produit_path_incl_def_3 p prec_empty.
Proof.
	unfold pl_produit_path_incl_def_3 in |- *. intros. split with pl_path_nil.
	split with pl_path_nil. split. elim (nat_sum m). intro. rewrite H3 in H.
	simpl in H. inversion H. reflexivity. intro. elim H3. intros. rewrite H4 in H. simpl in H. induction  p as [a p1 Hrecp1 p0 Hrecp0| ]; inversion H; reflexivity. split. inversion H1.
	rewrite <- H4 in H0. inversion H0. exact pl_path_incl_nil.
	exact pl_path_incl_nil.
Qed.

Lemma pl_produit_path_incl_3_2 :
 forall p : prec_list, pl_produit_path_incl_def_3 prec_empty p.
Proof.
	unfold pl_produit_path_incl_def_3 in |- *. intros. split with pl_path_nil.
	split with pl_path_nil. split. elim (nat_sum m). intro. rewrite H3 in H.
	simpl in H. inversion H. reflexivity. intros. elim H3. intros. rewrite H4 in H.
	simpl in H. induction  p as [a p1 Hrecp1 p0 Hrecp0| ]; simpl in H; inversion H;
  reflexivity. split.
	exact pl_path_incl_nil. inversion H0. rewrite <- H4 in H1. inversion H1.
	exact pl_path_incl_nil.
Qed.

Lemma pl_produit_path_incl_3_3 :
 forall (a : ad) (la ls p : prec_list),
 pl_produit_path_incl_def_2 p ls ->
 pl_produit_path_incl_def_3 p la ->
 pl_produit_path_incl_def_2 p (prec_cons a la ls).
Proof.
	unfold pl_produit_path_incl_def_2 in |- *. unfold pl_produit_path_incl_def_3 in |- *. intros.
	elim (nat_sum m); intros. rewrite H5 in H4. elim (le_Sn_n 0 (le_trans _ _ _ (pl_ess_invar_0 p (prec_cons a la ls)) H4)). elim H5. intros. rewrite H6 in H1.
	cut
  (pl_produit_0 a0 p (prec_cons a la ls) (S x) l =
   prec_cons (iad_conv a0 a) (pl_produit_1 p x la) (pl_produit_0 a0 p ls x l)). intro. rewrite H7 in H1.
	clear H7. inversion H1. elim (H0 n x plp0 H9 H2). intros. elim H12. intros.
	left. split with (pl_path_cons a0 x0). split with (pl_path_cons a x1). elim H13.
	intros. elim H15. intros. split. simpl in |- *. rewrite <- H14. reflexivity. split.
	exact (pl_path_incl_cons x0 a0 p prec_empty H16). exact (pl_path_incl_cons x1 a la ls H17). inversion H3. exact H13. exact H14. unfold pl_essence in |- *. unfold pl_essence in H4. rewrite H6 in H4. simpl in H4. elim (le_or_lt (pl_card p + pl_card la) x). intro. exact H12. intro. elim (le_Sn_n (S x)). apply (le_trans (S (S x)) (pl_card p + S (pl_card la + pl_card ls)) (S x)).
	rewrite <- (plus_Snm_nSm (pl_card p) (pl_card la + pl_card ls)). simpl in |- *.
	apply (le_n_S (S x) (pl_card p + (pl_card la + pl_card ls))).
	exact
  (le_trans _ _ _ (lt_le_S _ _ H12)
     (plus_le_compat (pl_card p) (pl_card p) (pl_card la)
        (pl_card la + pl_card ls) (le_n_n _)
        (le_plus_l (pl_card la) (pl_card ls)))). exact H4. elim (pl_sum ls); intro. rewrite H13 in H10.
	elim (nat_sum x). intros. rewrite H14 in H10. simpl in H10. inversion H10.
	elim (H12 (sym_eq H15)). intros. elim H14. intros. rewrite H15 in H10.
	simpl in H10. right. exact H10. elim (H n x plp a0 l H10 H2). intros. elim H14.
	intros. elim H15. intros. elim H16. intros. elim H18. intros. left. split with x0.
	split with x1. split. exact H17. split. exact H19. apply (pl_path_incl_next x1 a la ls H20). intro. rewrite H21 in H17. induction  x0 as [| a2 x0 Hrecx0]; inversion H17; rewrite H17 in H12;
  elim (H12 (refl_equal _)). intro. right. exact H14. inversion H3.
	rewrite <- H17 in H13. elim H13. intros. elim H19. intros. elim H20. intros.
	inversion H21. exact H19. unfold pl_essence in |- *. unfold pl_essence in H4. rewrite H6 in H4. simpl in H4. elim (le_or_lt (pl_card p + pl_card ls) x); intro.
	exact H14. elim (le_Sn_n (S x)). apply (le_trans (S (S x)) (pl_card p + S (pl_card la + pl_card ls)) (S x)). rewrite <- (plus_Snm_nSm (pl_card p) (pl_card la + pl_card ls)). simpl in |- *. apply (le_n_S (S x) (pl_card p + (pl_card la + pl_card ls))). exact
  (le_trans (S x) (pl_card p + pl_card ls)
     (pl_card p + (pl_card la + pl_card ls)) (lt_le_S _ _ H14)
     (plus_le_compat (pl_card p) (pl_card p) (pl_card ls)
        (pl_card la + pl_card ls) (le_n_n _) (le_plus_r _ _))). exact H4. reflexivity.
Qed.

Lemma pl_produit_path_incl_3_4 :
 forall (a : ad) (la ls p : prec_list),
 pl_produit_path_incl_def_2 la p ->
 pl_produit_path_incl_def_3 ls p ->
 pl_produit_path_incl_def_3 (prec_cons a la ls) p.
Proof.
	unfold pl_produit_path_incl_def_3 in |- *. unfold pl_produit_path_incl_def_2 in |- *. intros.
	elim (nat_sum m). intro. rewrite H5 in H4. elim (le_Sn_n 0 (le_trans _ _ _ (pl_ess_invar_0 (prec_cons a la ls) p) H4)). intros. elim H5. intros. rewrite H6 in H1. elim (pl_sum p). intros. rewrite H7 in H1. rewrite H7 in H3. inversion H3.
	rewrite <- H9 in H2. inversion H2. intros. cut
  (pl_produit_1 (prec_cons a la ls) (S x) p =
   pl_produit_0 a la p x (pl_produit_1 ls x p)). intro. rewrite H8 in H1.
	clear H8. inversion H1. rewrite (pl_product_1 a la p (pl_produit_1 ls x p) x) in H7.
	elim H7. intros. elim H9. intros. elim H11. intros. inversion H12. rewrite H6 in H4.
	unfold pl_essence in |- *. unfold pl_essence in H4. simpl in H4. elim (le_or_lt (pl_card la + pl_card p) x). intro. exact H9. intro. elim (le_Sn_n (S x)).
	apply (le_trans (S (S x)) (S (pl_card la + pl_card ls + pl_card p)) (S x)). apply (le_n_S (S x) (pl_card la + pl_card ls + pl_card p)).
	exact
  (le_trans _ _ _ (lt_le_S _ _ H9)
     (plus_le_compat (pl_card la) (pl_card la + pl_card ls) 
        (pl_card p) (pl_card p) (le_plus_l _ _) (le_n_n _))). exact H4.
	exact (sym_eq H10). elim (nat_sum n). intro. rewrite H11 in H2.
	inversion H2. intro. elim H11. intros. rewrite H12 in H2. elim (H x0 x plp a (pl_produit_1 ls x p) H1). intros. elim H13. intros. elim H14. intros. elim H15.
	intros. elim H17. intros. split with x1. split with x2. split. rewrite <- H16.
	exact H9. split. inversion H18. exact (pl_path_incl_cons plp1 a la ls H22).
	inversion H23. elim (H25 (sym_eq H26)). exact H19. intro. elim (pl_sum ls). intro. rewrite H14 in H13. induction  x as [| x Hrecx]; simpl in H13. inversion H13.
	rewrite <- H15 in H9. inversion H9. induction  p as [a1 p1 Hrecp1 p0 Hrecp0| ]; inversion H13. rewrite <- H15 in H9.
	inversion H9. rewrite <- H15 in H9. inversion H9. intros. elim (H0 n x plp H13).
	intros. elim H15. intros. elim H16. intros. elim H18. intros. split with x1.
	split with x2. split. rewrite <- H17. exact H9. split. apply (pl_path_incl_next x1 a la ls H19). intro. rewrite H21 in H17. induction  x2 as [| a1 x2 Hrecx2]; inversion H17; rewrite H17 in H9;
  inversion H9. exact H20. inversion H2. rewrite <- H18 in H14. elim H14.
	intros. elim H20. intros. elim H21. intros. inversion H22. rewrite H12. exact H20.
	exact H3. rewrite H6 in H4. unfold pl_essence in |- *. unfold pl_essence in H4. simpl in H4.
	elim (le_or_lt (pl_card ls + pl_card p) x). intro. exact H15. intros.
	elim (le_Sn_n (S x)). apply (le_trans (S (S x)) (S (pl_card la + pl_card ls + pl_card p)) (S x)). apply (le_n_S (S x) (pl_card la + pl_card ls + pl_card p)). exact
  (le_trans _ _ _ (lt_le_S _ _ H15)
     (plus_le_compat (pl_card ls) (pl_card la + pl_card ls) 
        (pl_card p) (pl_card p) (le_plus_r _ _) (le_n_n _))). exact H4. inversion H2. exact H14. exact H15.
	rewrite H12 in H3. exact H3. unfold pl_essence in |- *. unfold pl_essence in H4. 
	rewrite H6 in H4. simpl in H4. elim (le_or_lt (pl_card la + pl_card p) x).
	intro. exact H13. intro. elim (le_Sn_n (S x)). apply (le_trans (S (S x)) (S (pl_card la + pl_card ls + pl_card p)) (S x)). apply (le_n_S (S x) (pl_card la + pl_card ls + pl_card p)). apply
  (le_trans (S x) (pl_card la + pl_card p)
     (pl_card la + pl_card ls + pl_card p)).
	exact (lt_le_S _ _ H13). exact
  (plus_le_compat (pl_card la) (pl_card la + pl_card ls) 
     (pl_card p) (pl_card p) (le_plus_l _ _) (le_n_n _)). exact H4. elim (nat_sum n).
	intro. rewrite H12 in H2. inversion H2. intro. elim H12. intros. elim (H x0 x plp a (pl_produit_1 ls x p) H1). intros. elim H14. intros. elim H15. intros. elim H16.
	intros. elim H18. intros. split with x1. split with x2. split. exact H17. split.
	inversion H19. exact (pl_path_incl_cons plp1 a la ls H23). inversion H24.
	rewrite <- H27 in H26. elim (H26 (refl_equal _)). exact H20. intro.
	elim (pl_sum ls). intro. rewrite H15 in H14. elim (nat_sum x); intro.
	rewrite H16 in H14. inversion H14. elim (H11 (sym_eq H17)). elim H16.
	intros. rewrite H17 in H14. elim (pl_sum p). intro. rewrite H18 in H14. simpl in H14.
	inversion H14. elim (H11 (sym_eq H19)). intros. elim H18. intros.
	elim H19. intros. elim H20. intros. rewrite H21 in H14. simpl in H14. inversion H14.
	elim (H11 (sym_eq H22)). intro. inversion H2. rewrite <- H19 in H15.
	elim H15. intros. elim H21. intros. elim H22. intros. inversion H23.
	elim (H0 (S n0) x plp H14 H21). intros. elim H22. intros. elim H23. intros. elim H25.
	intros. split with x1. split with x2. split. exact H24. split. apply (pl_path_incl_next x1 a la ls H26). intro. rewrite H28 in H24. induction  x2 as [| a2 x2 Hrecx2]; inversion H24; rewrite H24 in H11;
  elim (H11 (refl_equal pl_path_nil)).
	exact H27. rewrite H18. exact H3. unfold pl_essence in |- *. rewrite H6 in H4.
	unfold pl_essence in H4. simpl in H4. elim (le_or_lt (pl_card ls + pl_card p) x); intro. exact H22. elim (le_Sn_n (S x)). apply (le_trans (S (S x)) (S (pl_card la + pl_card ls + pl_card p)) (S x)). apply (le_n_S (S x) (pl_card la + pl_card ls + pl_card p)). exact
  (le_trans _ _ _ (lt_le_S _ _ H22)
     (plus_le_compat (pl_card ls) (pl_card la + pl_card ls) 
        (pl_card p) (pl_card p) (le_plus_r _ _) (le_n_n _))). exact H4. rewrite H13 in H2. inversion H2; assumption.
	rewrite H13 in H3. exact H3. unfold pl_essence in H4. rewrite H6 in H4. simpl in H4.
	unfold pl_essence in |- *. elim (le_or_lt (pl_card la + pl_card p) x). intro.
	exact H14. intro. elim (le_Sn_n (S x)). apply (le_trans (S (S x)) (S (pl_card la + pl_card ls + pl_card p)) (S x)). apply (le_n_S (S x) (pl_card la + pl_card ls + pl_card p)). exact
  (le_trans _ _ _ (lt_le_S _ _ H14)
     (plus_le_compat (pl_card la) (pl_card la + pl_card ls) 
        (pl_card p) (pl_card p) (le_plus_l _ _) (le_n_n _))). exact H4. elim H7. intros. elim H8; intros.
	elim H9. intros. rewrite H10. reflexivity.
Qed.

Lemma pl_produit_path_incl_3_5 :
 forall p p' : prec_list,
 pl_produit_path_incl_def_2 p p' /\ pl_produit_path_incl_def_3 p p'.
Proof.
	exact
  (indprinciple_pl pl_produit_path_incl_def_2 pl_produit_path_incl_def_3
     pl_produit_path_incl_3_0 pl_produit_path_incl_3_1
     pl_produit_path_incl_3_2 pl_produit_path_incl_3_3
     pl_produit_path_incl_3_4).
Qed.

Lemma pl_produit_path_incl_3 :
 forall (pl0 pl1 : prec_list) (n m : nat) (plp : pl_path),
 pl_path_incl plp (pl_produit_1 pl0 m pl1) ->
 pl_tl_length pl0 n ->
 pl_tl_length pl1 n ->
 pl_essence pl0 pl1 <= m ->
 exists plp0 : pl_path,
   (exists plp1 : pl_path,
      plp = pl_path_product plp0 plp1 /\
      pl_path_incl plp0 pl0 /\ pl_path_incl plp1 pl1).
Proof.
	intro. intro. elim (pl_produit_path_incl_3_5 pl0 pl1). intro. intro. exact H0.
Qed.

Lemma pl_produit_path_incl_4 :
 forall (pl0 pl1 : prec_list) (n : nat) (plp : pl_path),
 pl_path_incl plp (pl_produit pl0 pl1) ->
 pl_tl_length pl0 n ->
 pl_tl_length pl1 n ->
 exists plp0 : pl_path,
   (exists plp1 : pl_path,
      plp = pl_path_product plp0 plp1 /\
      pl_path_incl plp0 pl0 /\ pl_path_incl plp1 pl1).
Proof.
	intros. unfold pl_produit in H. exact
  (pl_produit_path_incl_3 pl0 pl1 n (pl_essence pl0 pl1) plp H H0 H1
     (le_n_n _)).
Qed.

(* calcul de l'état produit *)

Fixpoint s_produit_l (a : ad) (p : prec_list) (s : state) {struct s} :
 state :=
  match s with
  | M0 => M0 prec_list
  | M1 a' p' =>
      if Neqb a a' then M1 prec_list a (pl_produit p p') else M0 prec_list
  | M2 s0 s1 =>
      match a with
      | N0 => M2 prec_list (s_produit_l N0 p s0) (M0 prec_list)
      | Npos q =>
          match q with
          | xH => M2 prec_list (M0 prec_list) (s_produit_l N0 p s1)
          | xO q' => M2 prec_list (s_produit_l (Npos q') p s0) (M0 prec_list)
          | xI q' => M2 prec_list (M0 prec_list) (s_produit_l (Npos q') p s1)
          end
      end
  end.

Definition sproductl_0_def (s : state) : Prop :=
  forall (a : ad) (p : prec_list) (c : ad) (r0 r1 : prec_list),
  MapGet prec_list (M1 prec_list a p) c = Some r0 ->
  MapGet prec_list s c = Some r1 ->
  MapGet prec_list (s_produit_l a p s) c = Some (pl_produit r0 r1).

Lemma sproductl_0_0 : sproductl_0_def (M0 prec_list).
Proof.
	unfold sproductl_0_def in |- *. intros. inversion H0.
Qed.

Lemma sproductl_0_1 :
 forall (a : ad) (a0 : prec_list), sproductl_0_def (M1 prec_list a a0).
Proof.
	unfold sproductl_0_def in |- *. intros. simpl in H. simpl in H0.
	elim (bool_is_true_or_false (Neqb a1 c)); intro; rewrite H1 in H.
	elim (bool_is_true_or_false (Neqb a c)); intro; rewrite H2 in H0.
	inversion H. inversion H0. rewrite (Neqb_complete _ _ H1).
	rewrite (Neqb_complete _ _ H2). simpl in |- *. rewrite (Neqb_correct c).
	simpl in |- *. rewrite (Neqb_correct c). trivial. inversion H0. inversion H.
Qed.

Lemma sproductl_0_2 :
 forall m : state,
 sproductl_0_def m ->
 forall m0 : state, sproductl_0_def m0 -> sproductl_0_def (M2 prec_list m m0).
Proof.
	unfold sproductl_0_def in |- *.
	intros. simpl in H1. elim (bool_is_true_or_false (Neqb a c)); intro.
	rewrite H3 in H1. inversion H1. rewrite (Neqb_complete _ _ H3). 
	induction  c as [| p0]. simpl in |- *. elim (H N0 r0 N0 r0 r1). reflexivity. reflexivity.
	simpl in H2. exact H2.  induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. simpl in |- *. elim (H0 (Npos p0) r0 (Npos p0) r0 r1). reflexivity. simpl in |- *. rewrite (aux_Neqb_1_0 p0).
	reflexivity. simpl in H2. exact H2. simpl in |- *. elim (H (Npos p0) r0 (Npos p0) r0 r1). reflexivity. simpl in |- *. rewrite (aux_Neqb_1_0 p0). reflexivity.
	simpl in H2. exact H2. simpl in |- *. elim (H0 N0 r0 N0 r0 r1). reflexivity.
	reflexivity. simpl in H2. exact H2. rewrite H3 in H1. inversion H1.
Qed.

Lemma sproductl_0_3 : forall m : state, sproductl_0_def m.
Proof.
	exact
  (Map_ind prec_list sproductl_0_def sproductl_0_0 sproductl_0_1
     sproductl_0_2).
Qed.

Lemma sproductl_0 :
 forall (s : state) (a : ad) (p : prec_list) (c : ad) (r0 r1 : prec_list),
 MapGet prec_list (M1 prec_list a p) c = Some r0 ->
 MapGet prec_list s c = Some r1 ->
 MapGet prec_list (s_produit_l a p s) c = Some (pl_produit r0 r1).
Proof.
	exact
  (Map_ind prec_list sproductl_0_def sproductl_0_0 sproductl_0_1
     sproductl_0_2).
Qed.

Definition sproductl_1_def (s : state) : Prop :=
  forall (a : ad) (p : prec_list) (c : ad) (r : prec_list),
  MapGet prec_list (s_produit_l a p s) c = Some r ->
  exists r0 : prec_list,
    (exists r1 : prec_list,
       MapGet prec_list (M1 prec_list a p) c = Some r0 /\
       MapGet prec_list s c = Some r1).

Lemma sproductl_1_0 : sproductl_1_def (M0 prec_list).
Proof.
	unfold sproductl_1_def in |- *. intros. inversion H.
Qed.

Lemma sproductl_1_1 :
 forall (a : ad) (a0 : prec_list), sproductl_1_def (M1 prec_list a a0).
Proof.
	unfold sproductl_1_def in |- *. intros. simpl in H. elim (bool_is_true_or_false (Neqb a1 a)); intro; rewrite H0 in H. simpl in H. elim (bool_is_true_or_false (Neqb a1 c)); intro; rewrite H1 in H. split with p. split with a0. simpl in |- *.
	split. rewrite H1. reflexivity. rewrite <- (Neqb_complete _ _ H0).
	rewrite H1. reflexivity. inversion H. inversion H.
Qed.

Lemma sproductl_1_2 :
 forall m : state,
 sproductl_1_def m ->
 forall m0 : state, sproductl_1_def m0 -> sproductl_1_def (M2 prec_list m m0).
Proof.
	unfold sproductl_1_def in |- *. intros. induction  a as [| p0]. induction  c as [| p0]. simpl in H1.
	elim (H N0 p N0 r H1). intros. elim H2. intros. elim H3. intros.
	split with x. split with x0. split. exact H4. simpl in |- *. exact H5. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ].
	simpl in H1. inversion H1. simpl in H1. elim (H N0 p (Npos p0) r H1).
	intros. elim H2. intros. elim H3. intros. split with x. split with x0.
	split. exact H4. simpl in |- *. exact H5. simpl in H1. inversion H1. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ].
	induction  c as [| p1]. simpl in H1. inversion H1. simpl in H1. induction  p1 as [p1 Hrecp1| p1 Hrecp1| ].
	elim (H0 (Npos p0) p (Npos p1) r H1). intros. elim H2. intros. elim H3.
	intros. intros. split with x. split with x0. split. exact H4. simpl in |- *.
	exact H5. inversion H1. elim (H0 (Npos p0) p N0 r H1). intros. elim H2.
	intros. elim H3. intros. split with x. split with x0. simpl in |- *. split. simpl in H4. exact H4. exact H5. induction  c as [| p1]. simpl in H1. elim (H (Npos p0) p N0 r H1). intros. elim H2. intros. elim H3. intros. split with x.
	split with x0. simpl in |- *. split. simpl in H4. exact H4. exact H5. simpl in H1.
	induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]. inversion H1. elim (H (Npos p0) p (Npos p1) r H1). intros.
	elim H2. intros. elim H3. intros. split with x. split with x0. simpl in |- *.
	split. simpl in H4. exact H4. exact H5. inversion H1. induction  c as [| p0]. simpl in H1.
	inversion H1. simpl in H1. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. elim (H0 N0 p (Npos p0) r H1).
	intros. elim H2. intros. elim H3. intros. split with x. split with x0.
	simpl in |- *. simpl in H4. split. exact H4. exact H5. inversion H1. elim (H0 N0 p N0 r H1). intros. elim H2. intros. elim H3. intros. split with x.
	split with x0. simpl in |- *. split. simpl in H4. exact H4. exact H5.
Qed.

Lemma sproductl_1_3 : forall m : state, sproductl_1_def m.
Proof.
	exact
  (Map_ind prec_list sproductl_1_def sproductl_1_0 sproductl_1_1
     sproductl_1_2).
Qed.

Lemma sproductl_1 :
 forall (s : state) (a : ad) (p : prec_list) (c : ad) (r : prec_list),
 MapGet prec_list (s_produit_l a p s) c = Some r ->
 exists r0 : prec_list,
   (exists r1 : prec_list,
      MapGet prec_list (M1 prec_list a p) c = Some r0 /\
      MapGet prec_list s c = Some r1).
Proof.
	exact
  (Map_ind prec_list sproductl_1_def sproductl_1_0 sproductl_1_1
     sproductl_1_2).
Qed.

Fixpoint s_produit_r (a : ad) (p : prec_list) (s : state) {struct s} :
 state :=
  match s with
  | M0 => M0 prec_list
  | M1 a' p' =>
      if Neqb a a' then M1 prec_list a (pl_produit p' p) else M0 prec_list
  | M2 s0 s1 =>
      match a with
      | N0 => M2 prec_list (s_produit_r N0 p s0) (M0 prec_list)
      | Npos q =>
          match q with
          | xH => M2 prec_list (M0 prec_list) (s_produit_r N0 p s1)
          | xO q' => M2 prec_list (s_produit_r (Npos q') p s0) (M0 prec_list)
          | xI q' => M2 prec_list (M0 prec_list) (s_produit_r (Npos q') p s1)
          end
      end
  end.

Definition sproductr_0_def (s : state) : Prop :=
  forall (a : ad) (p : prec_list) (c : ad) (r0 r1 : prec_list),
  MapGet prec_list (M1 prec_list a p) c = Some r0 ->
  MapGet prec_list s c = Some r1 ->
  MapGet prec_list (s_produit_r a p s) c = Some (pl_produit r1 r0).

Lemma sproductr_0_0 : sproductr_0_def (M0 prec_list).
Proof.
	unfold sproductr_0_def in |- *. intros. inversion H0.
Qed.

Lemma sproductr_0_1 :
 forall (a : ad) (a0 : prec_list), sproductr_0_def (M1 prec_list a a0).
Proof.
	unfold sproductr_0_def in |- *. intros. simpl in H. simpl in H0.
	elim (bool_is_true_or_false (Neqb a1 c)); intro; rewrite H1 in H.
	elim (bool_is_true_or_false (Neqb a c)); intro; rewrite H2 in H0.
	inversion H. inversion H0. rewrite (Neqb_complete _ _ H1).
	rewrite (Neqb_complete _ _ H2). simpl in |- *. rewrite (Neqb_correct c).
	simpl in |- *. rewrite (Neqb_correct c). trivial. inversion H0. inversion H.
Qed.

Lemma sproductr_0_2 :
 forall m : state,
 sproductr_0_def m ->
 forall m0 : state, sproductr_0_def m0 -> sproductr_0_def (M2 prec_list m m0).
Proof.
	unfold sproductr_0_def in |- *.
	intros. simpl in H1. elim (bool_is_true_or_false (Neqb a c)); intro; rewrite H3 in H1. inversion H1. rewrite (Neqb_complete _ _ H3).
	induction  c as [| p0]. simpl in |- *. elim (H N0 r0 N0 r0 r1). reflexivity. reflexivity.
	simpl in H2. exact H2. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. simpl in |- *. elim (H0 (Npos p0) r0 (Npos p0) r0 r1). reflexivity. simpl in |- *. rewrite (aux_Neqb_1_0 p0). reflexivity.
	simpl in H2. exact H2. simpl in |- *. elim (H (Npos p0) r0 (Npos p0) r0 r1).
	reflexivity. simpl in |- *. rewrite (aux_Neqb_1_0 p0). reflexivity.
	simpl in H2. exact H2. simpl in |- *. elim (H0 N0 r0 N0 r0 r1). reflexivity.
	reflexivity. simpl in H2. exact H2. inversion H1.
Qed.

Lemma sproductr_0_3 : forall m : state, sproductr_0_def m.
Proof.
	exact
  (Map_ind prec_list sproductr_0_def sproductr_0_0 sproductr_0_1
     sproductr_0_2).
Qed.

Lemma sproductr_0 :
 forall (s : state) (a : ad) (p : prec_list) (c : ad) (r0 r1 : prec_list),
 MapGet prec_list (M1 prec_list a p) c = Some r0 ->
 MapGet prec_list s c = Some r1 ->
 MapGet prec_list (s_produit_r a p s) c = Some (pl_produit r1 r0).
Proof.
	exact
  (Map_ind prec_list sproductr_0_def sproductr_0_0 sproductr_0_1
     sproductr_0_2).
Qed.

Definition sproductr_1_def (s : state) : Prop :=
  forall (a : ad) (p : prec_list) (c : ad) (r : prec_list),
  MapGet prec_list (s_produit_r a p s) c = Some r ->
  exists r0 : prec_list,
    (exists r1 : prec_list,
       MapGet prec_list (M1 prec_list a p) c = Some r0 /\
       MapGet prec_list s c = Some r1).

Lemma sproductr_1_0 : sproductr_1_def (M0 prec_list).
Proof.
	unfold sproductr_1_def in |- *. intros. inversion H.
Qed.

Lemma sproductr_1_1 :
 forall (a : ad) (a0 : prec_list), sproductr_1_def (M1 prec_list a a0).
Proof.
	unfold sproductr_1_def in |- *.
	intros. simpl in H. elim (bool_is_true_or_false (Neqb a1 a)); intro; rewrite H0 in H. simpl in H. elim (bool_is_true_or_false (Neqb a1 c)); intro; rewrite H1 in H. split with p. split with a0. simpl in |- *. split. rewrite H1.
	reflexivity. rewrite <- (Neqb_complete _ _ H0). rewrite H1. reflexivity.
	inversion H. inversion H.
Qed.

Lemma sproductr_1_2 :
 forall m : state,
 sproductr_1_def m ->
 forall m0 : state, sproductr_1_def m0 -> sproductr_1_def (M2 prec_list m m0).
Proof.
	unfold sproductr_1_def in |- *.
	intros. induction  a as [| p0]. induction  c as [| p0]. simpl in H1. elim (H N0 p N0 r H1).
	intros. elim H2. intros. elim H3. intros. elim H4. intros. split with x.
	split with x0. simpl in |- *. split. simpl in H4. exact H4. exact H5. simpl in H1.
	induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. inversion H1. simpl in H1. elim (H N0 p (Npos p0) r H1).
	intros. elim H2. intros. elim H3. intros. elim H4. intros. split with x.
	split with x0. simpl in |- *. split. simpl in H4. exact H4. exact H5. inversion H1.
	induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. induction  c as [| p1]. simpl in H1. inversion H1. simpl in H1.
	induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]. elim (H0 (Npos p0) p (Npos p1) r H1). intros. elim H2.
	intros. elim H3. intros. elim H4. intros. split with x. split with x0.
	simpl in |- *. split. simpl in H4. exact H4. exact H5. inversion H1.
	elim (H0 (Npos p0) p N0 r H1). intros. elim H2. intros. elim H3. intros.
	elim H4. intros. split with x. split with x0. simpl in |- *. split. simpl in H4.
	exact H4. exact H5. induction  c as [| p1]. simpl in H1. elim (H (Npos p0) p N0 r H1).
	intros. elim H2. intros. elim H3. intros. elim H4. intros. split with x.
	split with x0. simpl in |- *. split. simpl in H4. exact H4. exact H5. simpl in H1.
	induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]. inversion H1. elim (H (Npos p0) p (Npos p1) r H1). intros.
	elim H2. intros. elim H3. intros. elim H4. intros. split with x. split with x0. simpl in |- *. split. simpl in H4. exact H4. exact H5. inversion H1. induction  c as [| p0].
	simpl in H1. inversion H1. simpl in H. simpl in H1. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ].
	elim (H0 N0 p (Npos p0) r H1). intros. elim H2. intros. elim H3. intros.
	elim H4. intros. split with x. split with x0. simpl in |- *. split. simpl in H4.
	exact H4. exact H5. inversion H1. elim (H0 N0 p N0 r H1). intros.
	elim H2. intros. elim H3. intros. elim H4. intros. split with x. split with x0. simpl in |- *. split. simpl in H4. exact H4.  exact H5.
Qed.

Lemma sproductr_1_3 : forall m : state, sproductr_1_def m.
Proof.
	exact
  (Map_ind prec_list sproductr_1_def sproductr_1_0 sproductr_1_1
     sproductr_1_2).
Qed.

Lemma sproductr_1 :
 forall (s : state) (a : ad) (p : prec_list) (c : ad) (r : prec_list),
 MapGet prec_list (s_produit_r a p s) c = Some r ->
 exists r0 : prec_list,
   (exists r1 : prec_list,
      MapGet prec_list (M1 prec_list a p) c = Some r0 /\
      MapGet prec_list s c = Some r1).
Proof.
	exact
  (Map_ind prec_list sproductr_1_def sproductr_1_0 sproductr_1_1
     sproductr_1_2).
Qed.

Fixpoint s_produit (s0 s1 : state) {struct s1} : state :=
  match s0, s1 with
  | M0, M0 => M0 prec_list
  | M0, M1 a1 p1 => M0 prec_list
  | M0, M2 s10 s11 => M0 prec_list
  | M1 a0 p0, M0 => M0 prec_list
  | M1 a0 p0, M1 a1 p1 => s_produit_l a0 p0 (M1 prec_list a1 p1)
  | M1 a0 p0, M2 s10 s11 => s_produit_l a0 p0 (M2 prec_list s10 s11)
  | M2 s00 s01, M0 => M0 prec_list
  | M2 s00 s01, M1 a1 p1 => s_produit_r a1 p1 (M2 prec_list s00 s01)
  | M2 s00 s01, M2 s10 s11 =>
      M2 prec_list (s_produit s00 s10) (s_produit s01 s11)
  end.

Lemma s_produit_0 :
 forall (s0 s1 : state) (c : ad) (p0 p1 : prec_list),
 MapGet prec_list s0 c = Some p0 ->
 MapGet prec_list s1 c = Some p1 ->
 MapGet prec_list (s_produit s0 s1) c = Some (pl_produit p0 p1).
Proof.
	simple induction s0. intros. inversion H. intros. induction  s1 as [| a1 a2| s1_1 Hrecs1_1 s1_0 Hrecs1_0]. inversion H0.
	unfold s_produit in |- *. exact (sproductl_0 (M1 prec_list a1 a2) a a0 c p0 p1 H H0).
	unfold s_produit in |- *. exact (sproductl_0 (M2 prec_list s1_1 s1_0) a a0 c p0 p1 H H0).
	intros. induction  s1 as [| a a0| s1_1 Hrecs1_1 s1_0 Hrecs1_0]. inversion H2. unfold s_produit in |- *. exact (sproductr_0 (M2 prec_list m m0) a a0 c p1 p0 H2 H1). induction  c as [| p]. simpl in |- *.
	simpl in H1. simpl in H2. exact (H s1_1 N0 p0 p1 H1 H2). induction  p as [p Hrecp| p Hrecp| ].
	simpl in |- *. simpl in H1. simpl in H2. exact (H0 s1_0 (Npos p) p0 p1 H1 H2).
	simpl in H1. simpl in H2. simpl in |- *. exact (H s1_1 (Npos p) p0 p1 H1 H2).
	simpl in |- *. simpl in H1. simpl in H2. exact (H0 s1_0 N0 p0 p1 H1 H2).
Qed.

Lemma s_produit_1 :
 forall (s0 s1 : state) (c : ad) (p : prec_list),
 MapGet prec_list (s_produit s0 s1) c = Some p ->
 exists p0 : prec_list,
   (exists p1 : prec_list,
      MapGet prec_list s0 c = Some p0 /\
      MapGet prec_list s1 c = Some p1).
Proof.
	simple induction s0. simple induction s1. intros. simpl in H. inversion H. intros.
	simpl in H. inversion H. intros. simpl in H1. inversion H1. simple induction s1.
	intros. simpl in H. inversion H. intros. unfold s_produit in H.
	exact (sproductl_1 (M1 prec_list a1 a2) a a0 c p H). intros. simpl in H.
	unfold s_produit in H1. exact (sproductl_1 (M2 prec_list m m0) a a0 c p H1).
	simple induction s1; intros. inversion H1. unfold s_produit in H1. elim (sproductr_1 (M2 prec_list m m0) a a0 c p H1). intros. elim H2. intros. elim H3. intros.
	split with x0. split with x. split. exact H5. exact H4. induction  c as [| p0]. 
	simpl in H3. elim (H m1 N0 p H3). intros. elim H4. intros. elim H5. intros.
	split with x. split with x0. split. simpl in |- *. exact H6. simpl in |- *. exact H7.
	induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. simpl in H3. elim (H0 m2 (Npos p0) p H3). intros. elim H4.
	intros. elim H5. intros. split with x. split with x0. simpl in |- *. split. 
	exact H6. exact H7. simpl in H3. elim (H m1 (Npos p0) p H3). intros.
	elim H4. intros. elim H5. intros. split with x. split with x0. simpl in |- *.
	split. exact H6. exact H7. simpl in H3. elim (H0 m2 N0 p H3). intros.
	elim H4. intros. elim H5. intros. split with x. split with x0. simpl in |- *.
	split. exact H6. exact H7.
Qed.

(* preDTA produit *)

Fixpoint preDTA_produit_l (a : ad) (s : state) (d : preDTA) {struct d} :
 preDTA :=
  match d with
  | M0 => M0 state
  | M1 a' s' => M1 state (iad_conv a a') (s_produit s s')
  | M2 s0 s1 =>
      match a with
      | N0 =>
          M2 state
            (M2 state (preDTA_produit_l N0 s s0)
               (preDTA_produit_l N0 s s1)) (M0 state)
      | Npos p =>
          match p with
          | xH =>
              M2 state (M0 state)
                (M2 state (preDTA_produit_l N0 s s0)
                   (preDTA_produit_l N0 s s1))
          | xO p' =>
              M2 state
                (M2 state (preDTA_produit_l (Npos p') s s0)
                   (preDTA_produit_l (Npos p') s s1)) 
                (M0 state)
          | xI p' =>
              M2 state (M0 state)
                (M2 state (preDTA_produit_l (Npos p') s s0)
                   (preDTA_produit_l (Npos p') s s1))
          end
      end
  end.

Fixpoint preDTA_produit_r (a : ad) (s : state) (d : preDTA) {struct d} :
 preDTA :=
  match d with
  | M0 => M0 state
  | M1 a' s' => M1 state (iad_conv a' a) (s_produit s' s)
  | M2 s0 s1 =>
      match a with
      | N0 =>
          M2 state (M2 state (preDTA_produit_r N0 s s0) (M0 state))
            (M2 state (preDTA_produit_r N0 s s1) (M0 state))
      | Npos p =>
          match p with
          | xH =>
              M2 state (M2 state (M0 state) (preDTA_produit_r N0 s s0))
                (M2 state (M0 state) (preDTA_produit_r N0 s s1))
          | xO p' =>
              M2 state
                (M2 state (preDTA_produit_r (Npos p') s s0) (M0 state))
                (M2 state (preDTA_produit_r (Npos p') s s1) (M0 state))
          | xI p' =>
              M2 state
                (M2 state (M0 state) (preDTA_produit_r (Npos p') s s0))
                (M2 state (M0 state) (preDTA_produit_r (Npos p') s s1))
          end
      end
  end.


Fixpoint preDTA_produit (d0 d1 : preDTA) {struct d1} : preDTA :=
  match d0, d1 with
  | M0, M0 => M0 state
  | M0, M1 a1 s1 => M0 state
  | M0, M2 s10 s11 => M0 state
  | M1 a0 s0, M0 => M0 state
  | M1 a0 s0, M1 a1 s1 => preDTA_produit_l a0 s0 (M1 state a1 s1)
  | M1 a0 s0, M2 s10 s11 => preDTA_produit_l a0 s0 (M2 state s10 s11)
  | M2 s00 s01, M0 => M0 state
  | M2 s00 s01, M1 a1 s1 => preDTA_produit_r a1 s1 (M2 state s00 s01)
  | M2 s00 s01, M2 s10 s11 =>
      M2 state (M2 state (preDTA_produit s00 s10) (preDTA_produit s00 s11))
        (M2 state (preDTA_produit s01 s10) (preDTA_produit s01 s11))
  end.


Definition predta_produit_0d_def (d : preDTA) : Prop :=
  forall (a : ad) (s : state) (a0 a1 : ad) (s0 s1 : state),
  MapGet state (M1 state a s) a0 = Some s0 ->
  MapGet state d a1 = Some s1 ->
  MapGet state (preDTA_produit_l a s d) (iad_conv a0 a1) =
  Some (s_produit s0 s1).

Lemma predta_produit_0_0 : predta_produit_0d_def (M0 state).
Proof.
	unfold predta_produit_0d_def in |- *. intros. inversion H0.
Qed.

Lemma predta_produit_0_1 :
 forall (a : ad) (a0 : state), predta_produit_0d_def (M1 state a a0).
Proof.
	unfold predta_produit_0d_def in |- *. intros. simpl in H. simpl in H0.
	elim (bool_is_true_or_false (Neqb a1 a2)); intro; rewrite H1 in H.
	rewrite (Neqb_complete a1 a2 H1). elim (bool_is_true_or_false (Neqb a a3)); intro; rewrite H2 in H0. rewrite (Neqb_complete a a3 H2). inversion H.
	inversion H0. simpl in |- *. rewrite (Neqb_correct (iad_conv a2 a3)). trivial.
	inversion H0. inversion H.
Qed.

Lemma predta_produit_0_2 :
 forall m : preDTA,
 predta_produit_0d_def m ->
 forall m0 : preDTA,
 predta_produit_0d_def m0 -> predta_produit_0d_def (M2 state m m0).
Proof.
	unfold predta_produit_0d_def in |- *. intros. simpl in H1.
	elim (bool_is_true_or_false (Neqb a a0)); intro; rewrite H3 in H1.
	inversion H1. induction  a1 as [| p]. induction  a0 as [| p]. rewrite (Neqb_complete a N0 H3). simpl in |- *. elim (H N0 s0 N0 N0 s0 s1). simpl in |- *. trivial.
	simpl in |- *. trivial. simpl in H2. exact H2. induction  p as [p Hrecp| p Hrecp| ]. rewrite (Neqb_complete _ _ H3). simpl in |- *. elim (H (Npos p) s0 (Npos p) N0 s0 s1). simpl in |- *. trivial.
	simpl in |- *. rewrite (aux_Neqb_1_0 p). trivial. simpl in H2. assumption.
	rewrite (Neqb_complete _ _ H3). simpl in |- *. elim (H (Npos p) s0 (Npos p) N0 s0 s1). simpl in |- *. trivial. simpl in |- *. rewrite (aux_Neqb_1_0 p). trivial.
	simpl in H2. trivial. rewrite (Neqb_complete _ _ H3). simpl in |- *.
	elim (H N0 s0 N0 N0 s0 s1). simpl in |- *. trivial. simpl in |- *. trivial.
	simpl in H2. trivial. induction  p as [p Hrecp| p Hrecp| ]. rewrite (Neqb_complete _ _ H3).
	induction  a0 as [| p0]. simpl in |- *. elim (H0 N0 s0 N0 (Npos p) s0 s1). simpl in |- *.
	trivial. reflexivity. simpl in H2. exact H2. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. simpl in |- *.
	simpl in H2. elim (H0 (Npos p0) s0 (Npos p0) (Npos p) s0 s1). simpl in |- *.
	trivial. simpl in |- *. rewrite (aux_Neqb_1_0 p0). trivial. exact H2. simpl in |- *.
	elim (H0 (Npos p0) s0 (Npos p0) (Npos p) s0 s1). simpl in |- *. trivial. simpl in |- *.
	rewrite (aux_Neqb_1_0 p0). trivial. simpl in H2. exact H2. simpl in |- *.
	elim (H0 N0 s0 N0 (Npos p) s0 s1). simpl in |- *. reflexivity. reflexivity.
	simpl in H2. exact H2. rewrite (Neqb_complete _ _ H3). induction  a0 as [| p0].
	simpl in |- *. elim (H N0 s0 N0 (Npos p) s0 s1). reflexivity. reflexivity.
	simpl in H2. exact H2. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. simpl in |- *. elim (H (Npos p0) s0 (Npos p0) (Npos p) s0 s1). reflexivity. simpl in |- *. rewrite (aux_Neqb_1_0 p0). reflexivity.
	simpl in H2. exact H2. simpl in |- *. elim (H (Npos p0) s0 (Npos p0) (Npos p) s0 s1).
	reflexivity. simpl in |- *. rewrite (aux_Neqb_1_0 p0). trivial. simpl in H2.
	exact H2. simpl in |- *. elim (H N0 s0 N0 (Npos p) s0 s1). reflexivity.
	reflexivity. simpl in H2. exact H2. rewrite (Neqb_complete _ _ H3).
	induction  a0 as [| p]. simpl in |- *. elim (H0 N0 s0 N0 N0 s0 s1). reflexivity.
	reflexivity. simpl in H2. exact H2. induction  p as [p Hrecp| p Hrecp| ]. simpl in |- *.
	elim (H0 (Npos p) s0 (Npos p) N0 s0 s1). reflexivity. simpl in |- *.
	rewrite (aux_Neqb_1_0 p). trivial. simpl in H2. exact H2. simpl in |- *.
	elim (H0 (Npos p) s0 (Npos p) N0 s0 s1). reflexivity. simpl in |- *. rewrite (aux_Neqb_1_0 p). reflexivity. simpl in H2. exact H2. simpl in |- *.
	elim (H0 N0 s0 N0 N0 s0 s1). reflexivity. reflexivity. simpl in H2.
	exact H2. inversion H1.
Qed.

Lemma predta_produit_0_3 : forall m : preDTA, predta_produit_0d_def m.
Proof.
	exact
  (Map_ind state predta_produit_0d_def predta_produit_0_0 predta_produit_0_1
     predta_produit_0_2).
Qed.

Lemma predta_produit_0 :
 forall (a : ad) (s : state) (d : preDTA) (a0 a1 : ad) (s0 s1 : state),
 MapGet state (M1 state a s) a0 = Some s0 ->
 MapGet state d a1 = Some s1 ->
 MapGet state (preDTA_produit_l a s d) (iad_conv a0 a1) =
 Some (s_produit s0 s1).
Proof.
	intros. exact (predta_produit_0_3 d a s a0 a1 s0 s1 H H0).
Qed.

Definition predta_produit_1_def (d : preDTA) : Prop :=
  forall (a : ad) (s : state) (a0 a1 : ad) (s0 s1 : state),
  MapGet state (M1 state a s) a0 = Some s0 ->
  MapGet state d a1 = Some s1 ->
  MapGet state (preDTA_produit_r a s d) (iad_conv a1 a0) =
  Some (s_produit s1 s0).

Lemma predta_produit_1_0 : predta_produit_1_def (M0 state).
Proof.
	unfold predta_produit_1_def in |- *. intros. inversion H0.
Qed.

Lemma predta_produit_1_1 :
 forall (a : ad) (a0 : state), predta_produit_1_def (M1 state a a0).
Proof.
	unfold predta_produit_1_def in |- *. intros. simpl in H. simpl in H0.
	elim (bool_is_true_or_false (Neqb a1 a2)); intro; rewrite H1 in H.
	elim (bool_is_true_or_false (Neqb a a3)); intro; rewrite H2 in H0.
	inversion H. inversion H0. rewrite (Neqb_complete _ _ H1).
	rewrite (Neqb_complete _ _ H2). simpl in |- *. rewrite (Neqb_correct (iad_conv a3 a2)). trivial. inversion H0. inversion H.
Qed.

Lemma predta_produit_1_2 :
 forall m : preDTA,
 predta_produit_1_def m ->
 forall m0 : preDTA,
 predta_produit_1_def m0 -> predta_produit_1_def (M2 state m m0).
Proof.
	unfold predta_produit_1_def in |- *. intros. simpl in H1. 
	elim (bool_is_true_or_false (Neqb a a0)); intro; rewrite H3 in H1.
	rewrite (Neqb_complete _ _ H3). inversion H1. induction  a0 as [| p]. induction  a1 as [| p].
	simpl in |- *. elim (H N0 s0 N0 N0 s0 s1). reflexivity. reflexivity.
	simpl in H2. exact H2. induction  p as [p Hrecp| p Hrecp| ]. simpl in |- *. elim (H0 N0 s0 N0 (Npos p) s0 s1). reflexivity. reflexivity. simpl in H2. exact H2. simpl in |- *.
	elim (H N0 s0 N0 (Npos p) s0 s1). reflexivity. reflexivity.
	simpl in H2. exact H2. simpl in |- *. elim (H0 N0 s0 N0 N0 s0 s1).
	reflexivity. reflexivity. simpl in H2. exact H2. induction  p as [p Hrecp| p Hrecp| ].
	induction  a1 as [| p0]. simpl in |- *. elim (H (Npos p) s0 (Npos p) N0 s0 s1).
	reflexivity. simpl in |- *. rewrite (aux_Neqb_1_0 p). reflexivity.
	simpl in H2. exact H2. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. simpl in |- *. elim (H0 (Npos p) s0 (Npos p) (Npos p0) s0 s1). reflexivity. simpl in |- *. rewrite (aux_Neqb_1_0 p).
	reflexivity. simpl in H2. exact H2. simpl in |- *. elim (H (Npos p) s0 (Npos p) (Npos p0) s0 s1). reflexivity. simpl in |- *. rewrite (aux_Neqb_1_0 p).
	reflexivity. simpl in H2. exact H2. simpl in |- *. elim (H0 (Npos p) s0 (Npos p) N0 s0 s1). reflexivity. simpl in |- *. rewrite (aux_Neqb_1_0 p). reflexivity.
	simpl in H2. exact H2. induction  a1 as [| p0]. simpl in |- *. elim (H (Npos p) s0 (Npos p) N0 s0 s1). reflexivity. simpl in |- *. rewrite (aux_Neqb_1_0 p). reflexivity.
	simpl in H2. exact H2. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. simpl in |- *. elim (H0 (Npos p) s0 (Npos p) (Npos p0) s0 s1). reflexivity. simpl in |- *. rewrite (aux_Neqb_1_0 p).
	reflexivity. simpl in H2. exact H2. simpl in |- *. elim (H (Npos p) s0 (Npos p) (Npos p0) s0 s1). reflexivity. simpl in |- *. rewrite (aux_Neqb_1_0 p).
	reflexivity. simpl in H2. exact H2. simpl in |- *. elim (H0 (Npos p) s0 (Npos p) N0 s0 s1). reflexivity. simpl in |- *. rewrite (aux_Neqb_1_0 p). reflexivity.
	simpl in H2. exact H2. induction  a1 as [| p]. simpl in |- *. elim (H N0 s0 N0 N0 s0 s1). reflexivity. reflexivity. simpl in H2. exact H2. induction  p as [p Hrecp| p Hrecp| ].
	simpl in |- *. elim (H0 N0 s0 N0 (Npos p) s0 s1). reflexivity. reflexivity.
	simpl in H2. exact H2. simpl in |- *. elim (H N0 s0 N0 (Npos p) s0 s1).
	reflexivity. reflexivity. simpl in H2. exact H2. simpl in |- *.
	elim (H0 N0 s0 N0 N0 s0 s1). reflexivity. reflexivity.
	simpl in H2. exact H2. inversion H1.
Qed.

Lemma predta_produit_1_3 : forall m : preDTA, predta_produit_1_def m.
Proof.
	exact
  (Map_ind state predta_produit_1_def predta_produit_1_0 predta_produit_1_1
     predta_produit_1_2).
Qed.

Lemma predta_produit_1 :
 forall (a : ad) (s : state) (d : preDTA) (a0 a1 : ad) (s0 s1 : state),
 MapGet state (M1 state a s) a0 = Some s0 ->
 MapGet state d a1 = Some s1 ->
 MapGet state (preDTA_produit_r a s d) (iad_conv a1 a0) =
 Some (s_produit s1 s0).
Proof.
	intros. exact (predta_produit_1_3 d a s a0 a1 s0 s1 H H0).
Qed.

Lemma predta_produit_2 :
 forall (d0 d1 : preDTA) (a0 a1 : ad) (s0 s1 : state),
 MapGet state d0 a0 = Some s0 ->
 MapGet state d1 a1 = Some s1 ->
 MapGet state (preDTA_produit d0 d1) (iad_conv a0 a1) =
 Some (s_produit s0 s1).
Proof.
	simple induction d0. intros. inversion H. intros. induction  d1 as [| a3 a4| d1_1 Hrecd1_1 d1_0 Hrecd1_0];
  unfold preDTA_produit in |- *. inversion H0. exact (predta_produit_0 a a0 (M1 state a3 a4) a1 a2 s0 s1 H H0). exact (predta_produit_0 a a0 (M2 state d1_1 d1_0) a1 a2 s0 s1 H H0). intros. induction  d1 as [| a a2| d1_1 Hrecd1_1 d1_0 Hrecd1_0].
	inversion H2. unfold preDTA_produit in |- *. exact (predta_produit_1 a a2 (M2 state m m0) a1 a0 s1 s0 H2 H1). induction  a0 as [| p]. induction  a1 as [| p]. simpl in |- *.
	simpl in H1. simpl in H2. exact (H d1_1 N0 N0 s0 s1 H1 H2).
	induction  p as [p Hrecp| p Hrecp| ]. simpl in |- *. simpl in H1. simpl in H2. exact (H d1_0 N0 (Npos p) s0 s1 H1 H2). simpl in |- *. simpl in H1. simpl in H2. exact (H d1_1 N0 (Npos p) s0 s1 H1 H2). simpl in |- *. exact (H d1_0 N0 N0 s0 s1 H1 H2). simpl in H1.
	induction  p as [p Hrecp| p Hrecp| ]. induction  a1 as [| p0]. simpl in H2. simpl in |- *. exact (H0 d1_1 (Npos p) N0 s0 s1 H1 H2). induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. simpl in |- *. simpl in H2. exact (H0 d1_0 (Npos p) (Npos p0) s0 s1 H1 H2). simpl in |- *. exact (H0 d1_1 (Npos p) (Npos p0) s0 s1 H1 H2).
	simpl in H2. simpl in |- *. exact (H0 d1_0 (Npos p) N0 s0 s1 H1 H2). induction  a1 as [| p0].
	simpl in H2. simpl in |- *. exact (H d1_1 (Npos p) N0 s0 s1 H1 H2). induction  p0 as [p0 Hrecp0| p0 Hrecp0| ].
	simpl in |- *. simpl in H2. simpl in H1. exact (H d1_0 (Npos p) (Npos p0) s0 s1 H1 H2).
	simpl in |- *. simpl in H2. exact (H d1_1 (Npos p) (Npos p0) s0 s1 H1 H2). 
	simpl in H2. simpl in |- *. exact (H d1_0 (Npos p) N0 s0 s1 H1 H2). induction  a1 as [| p].
	simpl in H2. simpl in |- *. exact (H0 d1_1 N0 N0 s0 s1 H1 H2). induction  p as [p Hrecp| p Hrecp| ].
	simpl in H2. simpl in |- *. exact (H0 d1_0 N0 (Npos p) s0 s1 H1 H2). simpl in H2.
	simpl in |- *. exact (H0 d1_1 N0 (Npos p) s0 s1 H1 H2). simpl in H2. simpl in |- *.
	exact (H0 d1_0 N0 N0 s0 s1 H1 H2).
Qed.

Definition predta_produit_3_def (d0 : preDTA) : Prop :=
  forall (a a0 : ad) (s s0 : state),
  MapGet state (preDTA_produit_l a0 s0 d0) a = Some s ->
  exists a1 : ad,
    (exists a2 : ad,
       (exists s1 : state,
          (exists s2 : state,
             a = iad_conv a1 a2 /\
             MapGet state (M1 state a0 s0) a1 = Some s1 /\
             MapGet state d0 a2 = Some s2))).

Lemma predta_produit_3_0 : predta_produit_3_def (M0 state).
Proof.
	unfold predta_produit_3_def in |- *. intros. simpl in H. inversion H.
Qed.

Lemma predta_produit_3_1 :
 forall (a : ad) (a0 : state), predta_produit_3_def (M1 state a a0).
Proof.
	unfold predta_produit_3_def in |- *. intros. simpl in H. split with a2.
	split with a. split with s0. split with a0. elim (bool_is_true_or_false (Neqb (iad_conv a2 a) a1)); intro. rewrite (Neqb_complete _ _ H0).
	split. reflexivity. split. simpl in |- *. rewrite (Neqb_correct a2). reflexivity.
	simpl in |- *. rewrite (Neqb_correct a). reflexivity. rewrite H0 in H.
	inversion H.
Qed.

Lemma predta_produit_3_2 :
 forall m : preDTA,
 predta_produit_3_def m ->
 forall m0 : preDTA,
 predta_produit_3_def m0 -> predta_produit_3_def (M2 state m m0).
Proof.
	unfold predta_produit_3_def in |- *. intros. elim (iad_conv_surj a). intros. elim H2.
	intros. rewrite H3 in H1. rewrite H3. induction  a0 as [| p]. induction  x as [| p]. induction  x0 as [| p].
	simpl in H1. elim (H N0 N0 s s0 H1). intros. elim H4. intros. elim H5.
	intros. elim H6. intros. elim H7. intros. elim H9. intros. split with N0.
	split with N0. split with x1. split with x2. split. reflexivity.
	elim (iad_conv_inj N0 N0 x x0 H8). intros. rewrite <- H12 in H10.
	rewrite <- H13 in H11. split. exact H10. exact H11. induction  p as [p Hrecp| p Hrecp| ]. simpl in H1.
	elim (H0 (Npos (iad_conv_aux_0 p)) N0 s s0 H1). intros. elim H4. intros.
	elim H5. intros. elim H6. intros. elim H7. intros. elim H9. intros.
	split with N0. split with (Npos (xI p)). split with x1. split with x2.
	split. reflexivity. elim (iad_conv_inj N0 (Npos p) x x0 H8). intros.
	intros. rewrite <- H12 in H10. rewrite <- H13 in H11. split. exact H10.
	exact H11. simpl in H1. elim (H (Npos (iad_conv_aux_0 p)) N0 s s0 H1).
	intros. elim H4. intros. elim H5. intros. elim H6. intros. elim H7. intros.
	elim H9. intros. split with N0. split with (Npos (xO p)). split with x1.
	split with x2. elim (iad_conv_inj N0 (Npos p) x x0 H8). intros. split.
	reflexivity. intros. rewrite <- H12 in H10. rewrite <- H13 in H11. split.
	exact H10. exact H11. simpl in H1. elim (H0 N0 N0 s s0 H1). intros.
	elim H4. intros. elim H5. intros. elim H6. intros. elim H7. intros. elim H9.
	intros. split with N0. split with (Npos 1). split with x1. split with x2.
	elim (iad_conv_inj N0 N0 x x0 H8). intros. split. reflexivity. intros.
	rewrite <- H12 in H10. rewrite <- H13 in H11. split. exact H10. exact H11.
	induction  p as [p Hrecp| p Hrecp| ]. induction  x0 as [| p0]. simpl in H1. inversion H1. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ].
	simpl in H1. inversion H1. simpl in H1. inversion H1. simpl in H1. 
	inversion H1. induction  x0 as [| p0]. simpl in H1. elim (H (Npos (iad_conv_aux_1 p)) N0 s s0 H1). intros. elim H4. intros. elim H5. intros. elim H6. intros.
	elim H7. intros. elim H9. intros. split with (Npos (xO p)). split with N0.
	split with x1. split with x2. elim (iad_conv_inj (Npos p) N0 x x0 H8). intros.
	split. reflexivity. intros. rewrite <- H12 in H10. rewrite <- H13 in H11. split.
	exact H10. exact H11. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. clear Hrecp0. clear Hrecp. simpl in H1.
	elim (H0 (Npos (iad_conv_aux_2 p p0)) N0 s s0 H1). intros. elim H4. intros. elim H5.
	intros. elim H6. intros. elim H7. intros. elim H9. intros. split with (Npos (xO p)).
	split with (Npos (xI p0)). split with x1. split with x2. elim (iad_conv_inj (Npos p) (Npos p0) x x0 H8). intros. split. reflexivity. intros. rewrite <- H12 in H10.
	rewrite <- H13 in H11. split. exact H10. exact H11. clear Hrecp0. simpl in H1.
	elim (H (Npos (iad_conv_aux_2 p p0)) N0 s s0 H1). intros. elim H4. intros. elim H5.
	intros. elim H6. intros. elim H7. intros. elim H9. intros. split with (Npos (xO p)).
	split with (Npos (xO p0)). split with x1. split with x2. elim (iad_conv_inj (Npos p) (Npos p0) x x0 H8). intros. split. reflexivity. intros. rewrite <- H12 in H10.
	rewrite <- H13 in H11. split. exact H10. exact H11. simpl in H1. elim (H0 (Npos (iad_conv_aux_1 p)) N0 s s0 H1). intros. elim H4. intros. elim H5. intros. elim H6.
	intros. elim H7. intros. elim H9. intros. split with (Npos (xO p)). split with (Npos 1).
	split with x1. split with x2. elim (iad_conv_inj (Npos p) N0 x x0 H8). intros. split.
	reflexivity.  intros. rewrite <- H12 in H10. rewrite <- H13 in H11. split. exact H10.
	exact H11. induction  x0 as [| p]. simpl in H1. inversion H1. induction  p as [p Hrecp| p Hrecp| ]. simpl in H1.
	inversion H1. simpl in H1. inversion H1. simpl in H1. inversion H1. induction  p as [p Hrecp| p Hrecp| ].
	induction  x as [| p0]. induction  x0 as [| p0]. simpl in H1. inversion H1. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. simpl in H1.
	inversion H1. simpl in H1. inversion H1. simpl in H1. inversion H1. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ].
	induction  x0 as [| p1]. simpl in H1. elim (H (Npos (iad_conv_aux_1 p0)) (Npos p) s s0 H1).
	intros. elim H4. intros. elim H5. intros. elim H6. intros. elim H7. intros. elim H9.
	intros. split with (Npos (xI p0)). split with N0. split with x1. split with x2.
	elim (iad_conv_inj (Npos p0) N0 x x0 H8). intros. split. reflexivity. intros.
	rewrite <- H12 in H10. rewrite <- H13 in H11. split. exact H10. exact H11.
	induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]. clear Hrecp1. clear Hrecp0. simpl in H1. elim (H0 (Npos (iad_conv_aux_2 p0 p1)) (Npos p) s s0 H1). intros. elim H4. intros. elim H5. intros. elim H6. intros.
	elim H7. intros. elim H9. intros. split with (Npos (xI p0)). split with (Npos (xI p1)).
	split with x1. split with x2. elim (iad_conv_inj (Npos p0) (Npos p1) x x0 H8). intros.
	split. reflexivity. intros. rewrite <- H12 in H10. rewrite <- H13 in H11. split.
	exact H10. exact H11. clear Hrecp1. clear Hrecp0. simpl in H1. elim (H (Npos (iad_conv_aux_2 p0 p1)) (Npos p) s s0 H1). intros. elim H4. intros. elim H5. intros.
	elim H6. intros. elim H7. intros. elim H9. intros. split with (Npos (xI p0)).
	split with (Npos (xO p1)). split with x1. split with x2. elim (iad_conv_inj (Npos p0) (Npos p1) x x0 H8). intros. split. reflexivity. intros. rewrite <- H12 in H10.
	rewrite <- H13 in H11. split. exact H10. exact H11. clear Hrecp0. simpl in H1.
	elim (H0 (Npos (iad_conv_aux_1 p0)) (Npos p) s s0 H1). intros. elim H4. intros.
	elim H5. intros. elim H6. intros. elim H7. intros. elim H9. intros.
	split with (Npos (xI p0)). split with (Npos 1). split with x1. split with x2.
	elim (iad_conv_inj (Npos p0) N0 x x0 H8). intros. split. reflexivity. intros.
	rewrite <- H12 in H10. rewrite <- H13 in H11. split. exact H10. exact H11.
	induction  x0 as [| p1]. simpl in H1. inversion H1. induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]. simpl in H1. inversion H1.
	simpl in H1. inversion H1. simpl in H1. inversion H1. induction  x0 as [| p0]. simpl in H1.
	elim (H N0 (Npos p) s s0 H1). intros. elim H4. intros. elim H5. intros. elim H6.
	intros. elim H7. intros. elim H9. intros. split with (Npos 1). split with N0.
	split with x1. split with x2. elim (iad_conv_inj N0 N0 x x0 H8). intros.
	split. reflexivity. intros. rewrite <- H12 in H10. rewrite <- H13 in H11.
	split. exact H10. exact H11. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. simpl in H1. elim (H0 (Npos (iad_conv_aux_0 p0)) (Npos p) s s0 H1). intros. elim H4. intros. elim H5. intros. elim H6. intros.
	elim H7. intros. elim H9. intros. split with (Npos 1). split with (Npos (xI p0)).
	split with x1. split with x2. elim (iad_conv_inj N0 (Npos p0) x x0 H8). intros.
	split. reflexivity. intros. rewrite <- H12 in H10. rewrite <- H13 in H11. split.
	exact H10. exact H11. simpl in H1. elim (H (Npos (iad_conv_aux_0 p0)) (Npos p) s s0 H1).
	intros. elim H4. intros. elim H5. intros. elim H6. intros. elim H7. intros. elim H9.
	intros. split with (Npos 1). split with (Npos (xO p0)). split with x1. split with x2.
	elim (iad_conv_inj N0 (Npos p0) x x0 H8). intros. split. reflexivity. intros.
	rewrite <- H12 in H10. rewrite <- H13 in H11. split. exact H10. exact H11.
	simpl in H1. elim (H0 N0 (Npos p) s s0 H1). intros. elim H4. intros. elim H5.
	intros. elim H6. intros. elim H7. intros. elim H9. intros. split with (Npos 1).
	split with (Npos 1). split with x1. split with x2. elim (iad_conv_inj N0 N0 x x0 H8).
	intros. split. reflexivity. intros. rewrite <- H12 in H10. rewrite <- H13 in H11.
	split. exact H10. exact H11. induction  x as [| p0]. induction  x0 as [| p0]. simpl in H1. 
	elim (H N0 (Npos p) s s0 H1). intros. elim H4. intros. elim H5. intros. elim H6.
	intros. elim H7. intros. elim H9. intros. split with N0. split with N0.
	split with x1. split with x2. elim (iad_conv_inj N0 N0 x x0). intros. split.
	reflexivity. intros. rewrite <- H12 in H10. rewrite <- H13 in H11. split.
	exact H10. exact H11. simpl in |- *. exact H8. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. simpl in H1. elim (H0 (Npos (iad_conv_aux_0 p0)) (Npos p) s s0 H1). intros. elim H4. intros. elim H5. intros.
	elim H6. intros. elim H7. intros. elim H9. intros. split with N0. split with (Npos (xI p0)). split with x1. split with x2. elim (iad_conv_inj N0 (Npos p0) x x0 H8).
	intros. split. reflexivity. intros. rewrite <- H12 in H10. rewrite <- H13 in H11.
	split. exact H10. exact H11. simpl in H1. elim (H (Npos (iad_conv_aux_0 p0)) (Npos p) s s0 H1). intros. elim H4. intros. elim H5. intros. elim H6. intros. elim H7. intros.
	elim H9. intros. split with N0. split with (Npos (xO p0)). split with x1.
	split with x2. elim (iad_conv_inj N0 (Npos p0) x x0 H8). intros. split. reflexivity.
	intros. rewrite <- H12 in H10. rewrite <- H13 in H11. split. exact H10. exact H11.
	simpl in H1. elim (H0 N0 (Npos p) s s0 H1). intros. elim H4. intros. elim H5.
	intros. elim H6. intros. elim H7. intros. elim H9. intros. split with N0.
	split with (Npos 1). split with x1. split with x2. elim (iad_conv_inj N0 N0 x x0 H8).
	intros. split. reflexivity. intros. rewrite <- H12 in H10. rewrite <- H13 in H11. split.
	exact H10. exact H11. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. induction  x0 as [| p1]. simpl in H1. inversion H1.
	induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]. simpl in H1. inversion H1. simpl in H1. inversion H1. simpl in H1.
	inversion H1. induction  x0 as [| p1]. simpl in H1. elim (H (Npos (iad_conv_aux_1 p0)) (Npos p) s s0 H1). intros. elim H4. intros. elim H5. intros. elim H6. intros. elim H7. intros.
	elim H9. intros. split with (Npos (xO p0)). split with N0. split with x1.
	split with x2. elim (iad_conv_inj (Npos p0) N0 x x0 H8). intros. split. reflexivity.
	intros. rewrite <- H12 in H10. rewrite <- H13 in H11. split. exact H10. exact H11.
	induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]. clear Hrecp1. clear Hrecp0. simpl in H1. elim (H0 (Npos (iad_conv_aux_2 p0 p1)) (Npos p) s s0 H1). intros. elim H4. intros. elim H5. intros. elim H6. intros.
	elim H7. intros. elim H9. intros. split with (Npos (xO p0)). split with (Npos (xI p1)).
	split with x1. split with x2. elim (iad_conv_inj (Npos p0) (Npos p1) x x0 H8). intros.
	split. reflexivity. intros. rewrite <- H12 in H10. rewrite <- H13 in H11. split.
	exact H10. exact H11. clear Hrecp1. clear Hrecp0. simpl in H1. elim (H (Npos (iad_conv_aux_2 p0 p1)) (Npos p) s s0 H1). intros. elim H4. intros. elim H5. intros. elim H6. intros.
	elim H7. intros. elim H9. intros. split with (Npos (xO p0)). split with (Npos (xO p1)).
	split with x1. elim (iad_conv_inj (Npos p0) (Npos p1) x x0 H8). intros. intros.
	rewrite <- H12 in H10. split with x2. split. reflexivity. rewrite <- H13 in H11.
	split. simpl in |- *. simpl in H10. exact H10. exact H11. simpl in H1. elim (H0 (Npos (iad_conv_aux_1 p0)) (Npos p) s s0 H1). intros. elim H4. intros. elim H5. intros.
	elim H6. intros. elim H7. intros. elim H9. intros. split with (Npos (xO p0)).
	split with (Npos 1). split with x1. split with x2. elim (iad_conv_inj (Npos p0) N0 x x0 H8). intros. split. reflexivity. intros. rewrite <- H12 in H10. rewrite <- H13 in H11.
	split. exact H10. exact H11. induction  x0 as [| p0]. simpl in H1. inversion H1. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ].
	simpl in H1. inversion H1. simpl in H1. inversion H1. simpl in H1. inversion H1.
	induction  x as [| p]. induction  x0 as [| p]. simpl in H1. inversion H1. induction  p as [p Hrecp| p Hrecp| ]. simpl in H1.
	inversion H1. simpl in H1. inversion H1. simpl in H1. inversion H1. induction  p as [p Hrecp| p Hrecp| ].
	induction  x0 as [| p0]. simpl in H1. elim (H (Npos (iad_conv_aux_1 p)) N0 s s0 H1).
	intros. elim H4. intros. elim H5. intros. elim H6. intros. elim H7. intros. elim H9.
	intros. split with (Npos (xI p)). split with N0. split with x1. split with x2.
	elim (iad_conv_inj (Npos p) N0 x x0 H8). intros. split. reflexivity. intros.
	rewrite <- H12 in H10. rewrite <- H13 in H11. split. exact H10. exact H11.
	induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. simpl in H1. elim (H0 (Npos (iad_conv_aux_2 p p0)) N0 s s0 H1).
	intros. elim H4. intros. elim H5. intros. elim H6. intros. elim H7. intros. elim H9.
	intros. split with (Npos (xI p)). split with (Npos (xI p0)). split with x1. split with x2.
	elim (iad_conv_inj (Npos p) (Npos p0) x x0 H8). intros. split. reflexivity. intros.
	rewrite <- H12 in H10. rewrite <- H13 in H11. split. exact H10. exact H11. simpl in H1.
	elim (H (Npos (iad_conv_aux_2 p p0)) N0 s s0 H1). intros. elim H4. intros. elim H5.
	intros. elim H6. intros. elim H7. intros. elim H9. intros. split with (Npos (xI p)).
	split with (Npos (xO p0)). split with x1. split with x2. elim (iad_conv_inj (Npos p) (Npos p0) x x0 H8). intros. split. reflexivity. intros. rewrite <- H12 in H10. 
	rewrite <- H13 in H11. split. exact H10. exact H11. simpl in H1. elim (H0 (Npos (iad_conv_aux_1 p)) N0 s s0 H1). intros. elim H4. intros. elim H5. intros. elim H6.
	intros. elim H7. intros. elim H9. intros. split with (Npos (xI p)). split with (Npos 1).
	split with x1. split with x2. elim (iad_conv_inj (Npos p) N0 x x0 H8). intros.
	intros. split. reflexivity. intros. rewrite <- H12 in H10. rewrite <- H13 in H11.
	split. exact H10. exact H11. induction  x0 as [| p0]. simpl in H1. inversion H1. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ].
	simpl in H1. inversion H1. simpl in H1. inversion H1. simpl in H1. inversion H1.
	induction  x0 as [| p]. simpl in H1. elim (H N0 N0 s s0 H1). intros. elim H4. intros.
	elim H5. intros. elim H6. intros. elim H7. intros. elim H9. intros. split with (Npos 1). split with N0. split with x1. split with x2. elim (iad_conv_inj N0 N0 x x0 H8). intros. split. reflexivity. intros. rewrite <- H12 in H10.
	rewrite <- H13 in H11. split. exact H10. exact H11. induction  p as [p Hrecp| p Hrecp| ]. simpl in H1.
	elim (H0 (Npos (iad_conv_aux_0 p)) N0 s s0 H1). intros. elim H4. intros. elim H5. 
	intros. elim H6. intros. elim H7. intros. elim H9. intros. split with (Npos 1).
	split with (Npos (xI p)). split with x1. split with x2. elim (iad_conv_inj N0 (Npos p) x x0 H8). intros. split. reflexivity. intros. rewrite <- H12 in H10.
	rewrite <- H13 in H11. split. exact H10. exact H11. simpl in H1. elim (H (Npos (iad_conv_aux_0 p)) N0 s s0 H1). intros. elim H4. intros. elim H5. intros.
	elim H6. intros. elim H7. intros. elim H9. intros. split with (Npos 1). split with (Npos (xO p)). split with x1. split with x2. elim (iad_conv_inj N0 (Npos p) x x0 H8).
	intros. split. reflexivity. intros. rewrite <- H12 in H10. rewrite <- H13 in H11.
	split. exact H10. exact H11. simpl in H1. elim (H0 N0 N0 s s0 H1). intros.
	elim H4. intros. elim H5. intros. elim H6. intros. elim H7. intros. elim H9.
	intros. split with (Npos 1). split with (Npos 1). split with x1. split with x2.
	elim (iad_conv_inj N0 N0 x x0 H8). intros. split. reflexivity. intros. 
	rewrite <- H12 in H10. rewrite <- H13 in H11. split. exact H10. exact H11.
Qed.

Lemma predta_produit_3_3 : forall m : preDTA, predta_produit_3_def m.
Proof.
	exact
  (Map_ind state predta_produit_3_def predta_produit_3_0 predta_produit_3_1
     predta_produit_3_2).
Qed.

Lemma predta_produit_3 :
 forall (d0 : preDTA) (a a0 : ad) (s s0 : state),
 MapGet state (preDTA_produit_l a0 s0 d0) a = Some s ->
 exists a1 : ad,
   (exists a2 : ad,
      (exists s1 : state,
         (exists s2 : state,
            a = iad_conv a1 a2 /\
            MapGet state (M1 state a0 s0) a1 = Some s1 /\
            MapGet state d0 a2 = Some s2))).
Proof.
	exact
  (Map_ind state predta_produit_3_def predta_produit_3_0 predta_produit_3_1
     predta_produit_3_2).
Qed.

Definition predta_produit_4_def (d0 : preDTA) : Prop :=
  forall (a a0 : ad) (s s0 : state),
  MapGet state (preDTA_produit_r a0 s0 d0) a = Some s ->
  exists a1 : ad,
    (exists a2 : ad,
       (exists s1 : state,
          (exists s2 : state,
             a = iad_conv a1 a2 /\
             MapGet state (M1 state a0 s0) a2 = Some s1 /\
             MapGet state d0 a1 = Some s2))).

Lemma predta_produit_4_0 : predta_produit_4_def (M0 state).
Proof.
	unfold predta_produit_4_def in |- *. intros. inversion H.
Qed.

Lemma predta_produit_4_1 :
 forall (a : ad) (a0 : state), predta_produit_4_def (M1 state a a0).
Proof.
	unfold predta_produit_4_def in |- *. intros. simpl in H. elim (bool_is_true_or_false (Neqb (iad_conv a a2) a1)). intro. rewrite H0 in H. inversion H. split with a.
	split with a2. split with s0. split with a0. split. symmetry  in |- *. 
	exact (Neqb_complete _ _ H0). split. simpl in |- *. rewrite (Neqb_correct a2).
	reflexivity. simpl in |- *. rewrite (Neqb_correct a). reflexivity. intro.
	rewrite H0 in H. inversion H.
Qed.

Lemma predta_produit_4_2 :
 forall m : preDTA,
 predta_produit_4_def m ->
 forall m0 : preDTA,
 predta_produit_4_def m0 -> predta_produit_4_def (M2 state m m0).
Proof.
	unfold predta_produit_4_def in |- *. intros. elim (iad_conv_surj a). intros.
	elim H2. intros. rewrite H3 in H1. induction  a0 as [| p]. induction  x as [| p]. induction  x0 as [| p]. simpl in H1. elim (H N0 N0 s s0 H1). intros. elim H4. intros.
	elim H5. intros. elim H6. intros. elim H7. intros. elim H9. intros.
	split with x. split with x0. split with x1. split with x2.
	elim (iad_conv_inj N0 N0 _ _ H8). intros. split. rewrite H3.
	simpl in |- *. assumption. split. assumption. rewrite <- H12. simpl in |- *.
	rewrite <- H12 in H11. assumption. induction  p as [p Hrecp| p Hrecp| ]. simpl in H1.
	inversion H1. simpl in H1. elim (H (Npos (iad_conv_aux_0 p)) N0 s s0 H1). intros. elim H4. intros. elim H5. intros. elim H6. intros.
	elim H7. intros. elim H9. intros. split with N0. split with (Npos (xO p)). split with x1. split with x2. simpl in H3. split.
	simpl in |- *. exact H3. elim (iad_conv_inj N0 (Npos p) _ _ H8). intros.
	rewrite <- H12 in H11. rewrite <- H13 in H10. split; simpl in |- *; assumption.
	simpl in H1. inversion H1. induction  p as [p Hrecp| p Hrecp| ]. induction  x0 as [| p0]. simpl in H1.
	elim (H0 (Npos (iad_conv_aux_1 p)) N0 s s0 H1). intros. elim H4.
	intros. elim H5. intros. elim H6. intros. elim H7. intros. elim H9.
	intros. split with (Npos (xI p)). split with N0. split with x1.
	split with x2. split. assumption. elim (iad_conv_inj (Npos p) N0 _ _ H8). intros. rewrite <- H12 in H11. rewrite <- H13 in H10.
	split; simpl in |- *; assumption. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. simpl in H1. inversion H1.
	simpl in H1. elim (H0 (Npos (iad_conv_aux_2 p p0)) N0 s s0 H1).
	intros. elim H4. intros. elim H5. intros. elim H6. intros. elim H7.
	intros. elim H9. intros. split with (Npos (xI p)). split with (Npos (xO p0)). split with x1. split with x2. split. assumption.
	elim (iad_conv_inj (Npos p) (Npos p0) _ _ H8). intros. rewrite <- H12 in H11. rewrite <- H13 in H10. split; simpl in |- *; assumption.
	simpl in H1. inversion H1. induction  x0 as [| p0]. simpl in H1. elim (H (Npos (iad_conv_aux_1 p)) N0 s s0 H1). intros. elim H4. intros. elim H5. intros. elim H6. intros. elim H7. intros. elim H9. intros.
	split with (Npos (xO p)). split with N0. split with x1. split with x2.
	elim (iad_conv_inj (Npos p) N0 _ _ H8). intros. split. assumption.
	rewrite <- H13 in H10. rewrite <- H12 in H11. split; simpl in |- *; assumption.
	induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. simpl in H1. inversion H1. simpl in H1. elim (H (Npos (iad_conv_aux_2 p p0)) N0 s s0 H1). intros. elim H4. intros. elim H5.
	intros. elim H6. intros. elim H7. intros. elim H9. intros. split with (Npos (xO p)). split with (Npos (xO p0)). split with x1. split with x2.
	elim (iad_conv_inj (Npos p) (Npos p0) _ _ H8). intros. split. 
	assumption. rewrite <- H12 in H11. rewrite <- H13 in H10. split; simpl in |- *; assumption. inversion H1. induction  x0 as [| p]. simpl in H1. elim (H0 N0 N0 s s0 H1). intros. elim H4. intros. elim H5. intros. elim H6. intros.
	elim H7. intros. elim H9. intros. split with (Npos 1). split with N0.
	split with x1. split with x2. elim (iad_conv_inj N0 N0 _ _ H8).
	intros. split. assumption. rewrite <- H13 in H10. rewrite <- H12 in H11.
	split; simpl in |- *; assumption. induction  p as [p Hrecp| p Hrecp| ]. simpl in H1. inversion H1.
	simpl in H1. elim (H0 (Npos (iad_conv_aux_0 p)) N0 s s0 H1). intros.
	elim H4. intros. elim H5. intros. elim H6. intros. elim H7. intros.
	elim H9. intros. split with (Npos 1). split with (Npos (xO p)).
	split with x1. split with x2. elim (iad_conv_inj N0 (Npos p) _ _ H8).
	intros. split. assumption. rewrite <- H13 in H10. rewrite <- H12 in H11.
	split; simpl in |- *; assumption. simpl in H1. inversion H1. induction  p as [p Hrecp| p Hrecp| ].
	clear Hrecp. induction  x as [| p0]. induction  x0 as [| p0]. simpl in H1. inversion H1.
	induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. simpl in H1. elim (H (Npos (iad_conv_aux_0 p0)) (Npos p) s s0 H1). intros. elim H4. intros. elim H5. intros. elim H6.
	intros. elim H7. intros. elim H9. intros. split with N0. split with (Npos (xI p0)). split with x1. split with x2. elim (iad_conv_inj N0 (Npos p0) _ _ H8). intros. split. assumption. rewrite <- H13 in H10. rewrite <- H12 in H11. split; simpl in |- *; assumption. simpl in H1.
	inversion H1. simpl in H1. elim (H N0 (Npos p) s s0 H1). intros.
	elim H4. intros. elim H5. intros. elim H6. intros. elim H7. intros.
	elim H9. intros. split with N0. split with (Npos 1). 
	split with x1. split with x2. elim (iad_conv_inj N0 N0 _ _ H8).
	intros. split. assumption. rewrite <- H13 in H10. rewrite <- H12 in H11. split; simpl in |- *; assumption. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. induction  x0 as [| p1].
	simpl in H1. inversion H1. clear Hrecp0. induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]. simpl in H1.
	elim (H0 (Npos (iad_conv_aux_2 p0 p1)) (Npos p) s s0 H1). intros.
	elim H4. intros. elim H5. intros. elim H6. intros. elim H7. intros.
	elim H9. intros. split with (Npos (xI p0)). split with (Npos (xI p1)). split with x1. split with x2. elim (iad_conv_inj (Npos p0) (Npos p1) _ _ H8). intros. split. assumption. rewrite <- H13 in H10.
	rewrite <- H12 in H11. split; simpl in |- *; assumption. simpl in H1.
	inversion H1. simpl in H1. elim (H0 (Npos (iad_conv_aux_1 p0)) (Npos p) s s0 H1). intros. elim H4. intros. elim H5. intros. elim H6.
	intros. elim H7. intros. elim H9. intros. split with (Npos (xI p0)).
	split with (Npos 1). split with x1. split with x2. elim (iad_conv_inj (Npos p0) N0 _ _ H8). intros. split. assumption.
	rewrite <- H13 in H10. rewrite <- H12 in H11. split; simpl in |- *; assumption. induction  x0 as [| p1]. simpl in H1. inversion H1. clear Hrecp0.
	induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]. simpl in H1. elim (H (Npos (iad_conv_aux_2 p0 p1)) (Npos p) s s0 H1). intros. elim H4. intros. elim H5. intros.
	elim H6. intros. elim H7. intros. elim H9. intros. split with (Npos (xO p0)). split with (Npos (xI p1)). split with x1. split with x2. elim (iad_conv_inj (Npos p0) (Npos p1) _ _ H8). intros.
	split. assumption. rewrite <- H13 in H10. rewrite <- H12 in H11.
	split; simpl in |- *; assumption. simpl in H1. inversion H1. simpl in H1.
	elim (H (Npos (iad_conv_aux_1 p0)) (Npos p) s s0 H1). intros. 
	elim H4. intros. elim H5. intros. elim H6. intros. elim H7. intros.
	elim H9. intros. split with (Npos (xO p0)). split with (Npos 1).
	split with x1. split with x2. elim (iad_conv_inj (Npos p0) N0 _ _ H8).  intros. split. assumption. rewrite <- H13 in H10. rewrite <- H12 in H11. split; simpl in |- *; assumption. induction  x0 as [| p0]. simpl in H1.
	inversion H1. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. simpl in H1. elim (H0 (Npos (iad_conv_aux_0 p0)) (Npos p) s s0 H1). intros. elim H4. intros.
	elim H5. intros. elim H6. intros. elim H7. intros. elim H9. intros.
	split with (Npos 1). split with (Npos (xI p0)). split with x1.
	split with x2. elim (iad_conv_inj N0 (Npos p0) _ _ H8). intros.
	split. assumption. rewrite <- H13 in H10. rewrite <- H12 in H11.
	split; simpl in |- *; assumption. simpl in H1. inversion H1. simpl in H1.
	elim (H0 N0 (Npos p) s s0 H1). intros. elim H4. intros. elim H5.
	intros. elim H6. intros. elim H7. intros. elim H9. intros.
	split with (Npos 1). split with (Npos 1). split with x1. split with x2. elim (iad_conv_inj N0 N0 _ _ H8). intros. split.
	assumption. rewrite <- H13 in H10. rewrite <- H12 in H11.
	split; simpl in |- *; assumption. clear Hrecp. induction  x as [| p0]. induction  x0 as [| p0].
	simpl in H1. elim (H N0 (Npos p) s s0 H1). intros. elim H4.
	intros. elim H5. intros. elim H6. intros. elim H7. intros.
	elim H9. intros. split with N0. split with N0. split with x1.
	split with x2. elim (iad_conv_inj N0 N0 _ _ H8). intros.
	split. assumption. rewrite <- H13 in H10. rewrite <- H12 in H11.
	split; simpl in |- *; assumption. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. simpl in H1. inversion H1.
	simpl in H1. elim (H (Npos (iad_conv_aux_0 p0)) (Npos p) s s0 H1).
	intros. elim H4. intros. elim H5. intros. elim H6. intros. elim H7.
	intros. elim H9. intros. split with N0. split with (Npos (xO p0)).
	split with x1. split with x2. elim (iad_conv_inj N0 (Npos p0) _ _ H8). intros. split. assumption. rewrite <- H13 in H10.
	rewrite <- H12 in H11. split; simpl in |- *; assumption. simpl in H1.
	inversion H1. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. clear Hrecp0. induction  x0 as [| p1].
	simpl in H1. elim (H0 (Npos (iad_conv_aux_1 p0)) (Npos p) s s0 H1).
	intros. elim H4. intros. elim H5. intros. elim H6. intros. elim H7.
	intros. elim H9. intros. split with (Npos (xI p0)). split with N0.
	split with x1. split with x2. elim (iad_conv_inj (Npos p0) N0 _ _ H8). intros. split. assumption. rewrite <- H13 in H10. rewrite <- H12 in H11. split; simpl in |- *; assumption. induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]. simpl in H1.
	inversion H1. simpl in H1. elim (H0 (Npos (iad_conv_aux_2 p0 p1)) (Npos p) s s0 H1). intros. elim H4. intros. elim H5. intros. elim H6.
	intros. elim H7. intros. elim H9. intros. split with (Npos (xI p0)).
	split with (Npos (xO p1)). split with x1. split with x2. elim (iad_conv_inj (Npos p0) (Npos p1) _ _ H8). intros. split. assumption.
	rewrite <- H13 in H10. rewrite <- H12 in H11. split; simpl in |- *; assumption.
	simpl in H1. inversion H1. clear Hrecp0. induction  x0 as [| p1]. simpl in H1.
	elim (H (Npos (iad_conv_aux_1 p0)) (Npos p) s s0 H1). intros. elim H4.
	intros. elim H5. intros. elim H6. intros. elim H7. intros. elim H9.
	intros. split with (Npos (xO p0)). split with N0. split with x1.
	split with x2. elim (iad_conv_inj (Npos p0) N0 _ _ H8). intros.
	split. assumption. rewrite <- H13 in H10. rewrite <- H12 in H11.
	split; simpl in |- *; assumption. induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]. simpl in H1. inversion H1.
	simpl in H1. elim (H (Npos (iad_conv_aux_2 p0 p1)) (Npos p) s s0 H1).
	intros. elim H4. intros. elim H5. intros. elim H6. intros. elim H7.
	intros. elim H9. intros. split with (Npos (xO p0)). split with (Npos (xO p1)). split with x1. split with x2. elim (iad_conv_inj (Npos p0) (Npos p1) _ _ H8). intros. split. assumption. rewrite <- H13 in H10.
	rewrite <- H12 in H11. split; simpl in |- *; assumption. simpl in H1.
	inversion H1. induction  x0 as [| p0]. simpl in H1. elim (H0 N0 (Npos p) s s0 H1). intros. elim H4. intros. elim H5. intros. elim H6. intros.
	elim H7. intros. elim H9. intros. split with (Npos 1). split with N0. split with x1. split with x2. elim (iad_conv_inj N0 N0 _ _ H8). intros. split. assumption. rewrite <- H13 in H10. rewrite <- H12 in H11. split; simpl in |- *; assumption. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. simpl in H1. inversion H1. simpl in H1. elim (H0 (Npos (iad_conv_aux_0 p0)) (Npos p) s s0 H1).
	intros. elim H4. intros. elim H5. intros. elim H6. intros. elim H7.
	intros. elim H9. intros. split with (Npos 1). split with (Npos (xO p0)). split with x1. split with x2. elim (iad_conv_inj N0 (Npos p0) _ _ H8). intros. split. assumption. rewrite <- H13 in H10. rewrite <- H12 in H11. split; simpl in |- *; assumption. simpl in H1. inversion H1.
	induction  x as [| p]. induction  x0 as [| p]. simpl in H1. inversion H1. induction  p as [p Hrecp| p Hrecp| ].
	simpl in H1. elim (H (Npos (iad_conv_aux_0 p)) N0 s s0 H1). 
	intros. elim H4. intros. elim H5. intros. elim H6. intros. elim H7.
	intros. elim H9. intros. split with N0. split with (Npos (xI p)).
	split with x1. split with x2. elim (iad_conv_inj N0 (Npos p) _ _ H8).  intros. split. assumption. rewrite <- H13 in H10. rewrite <- H12 in H11. split; simpl in |- *; assumption. simpl in H1. inversion H1.
	simpl in H1. elim (H N0 N0 s s0 H1). intros. elim H4. intros.
	elim H5. intros. elim H6. intros. elim H7. intros. elim H9. intros.
	split with N0. split with (Npos 1). split with x1. split with x2.
	elim (iad_conv_inj N0 N0 _ _ H8). intros. split. assumption.
	rewrite <- H13 in H10. rewrite <- H12 in H11. split; simpl in |- *; assumption. induction  p as [p Hrecp| p Hrecp| ]. clear Hrecp. induction  x0 as [| p0]. simpl in H1.
	inversion H1. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. simpl in H1. elim (H0 (Npos (iad_conv_aux_2 p p0)) N0 s s0 H1). intros. elim H4. intros.
	elim H5. intros. elim H6. intros. elim H7. intros. elim H9. intros.
	split with (Npos (xI p)). split with (Npos (xI p0)). split with x1.
	split with x2. elim (iad_conv_inj (Npos p) (Npos p0) _ _ H8). intros.
	split. assumption. rewrite <- H13 in H10. rewrite <- H12 in H11.
	split; simpl in |- *; assumption. simpl in H1. inversion H1. simpl in H1.
	elim (H0 (Npos (iad_conv_aux_1 p)) N0 s s0 H1). intros. elim H4.
	intros. elim H5. intros. elim H6. intros. elim H7. intros. elim H9.
	intros. split with (Npos (xI p)). split with (Npos 1). 
	split with x1. split with x2. elim (iad_conv_inj (Npos p) N0 _ _ H8).
	intros. split. assumption. rewrite <- H13 in H10. rewrite <- H12 in H11.
	split; simpl in |- *; assumption. induction  x0 as [| p0]. simpl in H1. inversion H1.
	clear Hrecp. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. simpl in H1. elim (H (Npos (iad_conv_aux_2 p p0)) N0 s s0 H1). intros. elim H4. intros. elim H5. intros. elim H6.
	intros. elim H7. intros. elim H9. intros. split with (Npos (xO p)).
	split with (Npos (xI p0)). split with x1. split with x2. elim (iad_conv_inj (Npos p) (Npos p0) _ _ H8). intros. split. assumption.
	rewrite <- H13 in H10. rewrite <- H12 in H11. split; simpl in |- *; assumption.
	simpl in H1. inversion H1. simpl in H1. elim (H (Npos (iad_conv_aux_1 p)) N0 s s0 H1). intros. elim H4. intros. elim H5. intros. elim H6.
	intros. elim H7. intros. elim H9. intros. split with (Npos (xO p)).
	split with (Npos 1). split with x1. split with x2. elim (iad_conv_inj (Npos p) N0 _ _ H8). intros. split. assumption. rewrite <- H13 in H10.
	rewrite <- H12 in H11. split; simpl in |- *; assumption. induction  x0 as [| p]. 
	simpl in H1. inversion H1. induction  p as [p Hrecp| p Hrecp| ]. simpl in H1. elim (H0 (Npos (iad_conv_aux_0 p)) N0 s s0 H1). intros. elim H4. intros. elim H5.
	intros. elim H6. intros. elim H7. intros. elim H9. intros. split with (Npos 1). split with (Npos (xI p)). split with x1. split with x2.
	elim (iad_conv_inj N0 (Npos p) _ _ H8). intros. split. assumption.
	rewrite <- H13 in H10. rewrite <- H12 in H11. split; simpl in |- *; assumption.
	simpl in H1. inversion H1. simpl in H1. elim (H0 N0 N0 s s0 H1).
	intros. elim H4. intros. elim H5. intros. elim H6. intros. elim H7.
	intros. elim H9. intros. split with (Npos 1). split with (Npos 1).
	split with x1. split with x2. elim (iad_conv_inj N0 N0 _ _ H8).
	intros. split. assumption. rewrite <- H13 in H10. rewrite <- H12 in H11. split; simpl in |- *; assumption.
Qed.

Lemma predta_produit_4_3 : forall m : preDTA, predta_produit_4_def m.
Proof.
	exact
  (Map_ind state predta_produit_4_def predta_produit_4_0 predta_produit_4_1
     predta_produit_4_2).
Qed.

Lemma predta_produit_4 :
 forall (d0 : preDTA) (a a0 : ad) (s s0 : state),
 MapGet state (preDTA_produit_r a0 s0 d0) a = Some s ->
 exists a1 : ad,
   (exists a2 : ad,
      (exists s1 : state,
         (exists s2 : state,
            a = iad_conv a1 a2 /\
            MapGet state (M1 state a0 s0) a2 = Some s1 /\
            MapGet state d0 a1 = Some s2))).
Proof.
	exact
  (Map_ind state predta_produit_4_def predta_produit_4_0 predta_produit_4_1
     predta_produit_4_2).
Qed.

Lemma predta_produit_5 :
 forall (d0 d1 : preDTA) (a : ad) (s : state),
 MapGet state (preDTA_produit d0 d1) a = Some s ->
 exists a0 : ad,
   (exists a1 : ad,
      (exists s0 : state,
         (exists s1 : state,
            a = iad_conv a0 a1 /\
            MapGet state d0 a0 = Some s0 /\
            MapGet state d1 a1 = Some s1))).
Proof.
	simple induction d0. intros. induction  d1 as [| a0 a1| d1_1 Hrecd1_1 d1_0 Hrecd1_0]; inversion H. intros.
	induction  d1 as [| a2 a3| d1_1 Hrecd1_1 d1_0 Hrecd1_0]. simpl in H. inversion H. cut
  (preDTA_produit (M1 state a a0) (M1 state a2 a3) =
   preDTA_produit_l a a0 (M1 state a2 a3)). intro. rewrite H0 in H. exact (predta_produit_3 (M1 state a2 a3) a1 a s a0 H). reflexivity. cut
  (preDTA_produit (M1 state a a0) (M2 state d1_1 d1_0) =
   preDTA_produit_l a a0 (M2 state d1_1 d1_0)).
	intro. rewrite H0 in H. exact (predta_produit_3 (M2 state d1_1 d1_0) a1 a s a0 H). reflexivity. simple induction d1. intros. inversion H1. intros.
	cut
  (preDTA_produit (M2 state m m0) (M1 state a a0) =
   preDTA_produit_r a a0 (M2 state m m0)). intro. rewrite H2 in H1. elim (predta_produit_4 (M2 state m m0) a1 a s a0 H1). intros. elim H3. intros. elim H4. intros.
	elim H5. intros. elim H6. intros. elim H8. intros. split with x.
	split with x0. split with x2. split with x1. split. assumption. split; assumption. reflexivity. intros. clear H1. clear H2. induction  a as [| p]. simpl in H3.
	elim (H m1 N0 s H3). intros. elim H1. intros. elim H2. intros. elim H4.
	intros. elim H5. intros. elim H7. intros. split with N0. split with N0.
	simpl in |- *. split with x1. split with x2. elim (iad_conv_inj N0 N0 _ _ H6); intros. rewrite <- H10 in H8. rewrite <- H11 in H9. split. reflexivity.
	split. exact H8. exact H9. induction  p as [p Hrecp| p Hrecp| ]. clear Hrecp. induction  p as [p Hrecp| p Hrecp| ].
	clear Hrecp. simpl in H3. elim (H0 m2 (Npos p) s H3). intros. elim H1.
	intros. elim H2. intros. elim H4. intros. elim H5. intros. elim H7. intros.
	induction  x as [| p0]. induction  x0 as [| p0]. inversion H6. split with (Npos 1). split with (Npos (xI p0)). split with x1. split with x2. split. simpl in |- *. simpl in H6.
	inversion H6. reflexivity. simpl in |- *. split; assumption. induction  x0 as [| p1].
	split with (Npos (xI p0)). split with (Npos 1). split with x1. split with x2.
	simpl in |- *. split. simpl in H6. inversion H6. reflexivity. split; assumption.
	split with (Npos (xI p0)). split with (Npos (xI p1)). split with x1.
	split with x2. simpl in |- *. simpl in H6. inversion H6. split. reflexivity.
	split; assumption.  clear Hrecp. simpl in H3. elim (H0 m1 (Npos p) s H3).
	intros. elim H1. intros. elim H2. intros. elim H4. intros. elim H5. intros.
	elim H7. intros. induction  x as [| p0]. induction  x0 as [| p0]. inversion H6. split with (Npos 1). split with (Npos (xO p0)). split with x1. split with x2. simpl in H6.
	inversion H6. simpl in |- *. split. reflexivity. split; assumption. induction  x0 as [| p1].
	split with (Npos (xI p0)). split with N0. split with x1. split with x2.
	simpl in H6. inversion H6. simpl in |- *. split. reflexivity. split; assumption.
	split with (Npos (xI p0)). split with (Npos (xO p1)). split with x1.
	split with x2. simpl in H6. inversion H6. split. reflexivity. split; assumption. simpl in H3. elim (H0 m2 N0 s H3). intros. elim H1. intros.
	elim H2. intros. elim H4. intros. elim H5. intros. elim H7. intros. induction  x as [| p]. induction  x0 as [| p]. split with (Npos 1). split with (Npos 1). split with x1.
	split with x2. simpl in |- *. split. reflexivity. split; assumption. simpl in H6.
	inversion H6. induction  x0 as [| p0]; simpl in H6; inversion H6. clear Hrecp.
	induction  p as [p Hrecp| p Hrecp| ]. clear Hrecp. simpl in H3. elim (H m2 (Npos p) s H3). intros.
	elim H1. intros. elim H2. intros. elim H4. intros. elim H5. intros. elim H7.
	intros. induction  x as [| p0]. induction  x0 as [| p0]. simpl in H6. inversion H6. split with N0.
	split with (Npos (xI p0)). split with x1. split with x2. simpl in H6.
	inversion H6. simpl in |- *. split. reflexivity. split; assumption. induction  x0 as [| p1].
	split with (Npos (xO p0)). split with (Npos 1). split with x1. split with x2.
	simpl in H6. inversion H6. simpl in |- *. split. reflexivity. split; assumption.
	split with (Npos (xO p0)). split with (Npos (xI p1)). split with x1.
	split with x2. simpl in H6. inversion H6. simpl in |- *. split. reflexivity.
	split; assumption. clear Hrecp. simpl in H3. elim (H m1 (Npos p) s H3).
	intros. elim H1. intros. elim H2. intros. elim H4. intros. elim H5. intros.
	elim H7. intros. induction  x as [| p0]. induction  x0 as [| p0]. simpl in H6. inversion H6.
	split with N0. split with (Npos (xO p0)). split with x1. split with x2.
	simpl in H6. inversion H6. simpl in |- *. split. reflexivity. split; assumption.
	induction  x0 as [| p1]. simpl in H6. split with (Npos (xO p0)). split with N0.
	split with x1. split with x2. simpl in H6. inversion H6. split. reflexivity.
	split; assumption. split with (Npos (xO p0)). split with (Npos (xO p1)).
	split with x1. split with x2. simpl in H6. inversion H6. simpl in |- *. split.
	reflexivity. split; assumption. simpl in H3. elim (H m2 N0 s H3). intros.
	elim H1. intros. elim H2. intros. elim H4. intros. elim H5. intros. elim H7.
	intros. induction  x as [| p]. induction  x0 as [| p]. split with N0. split with (Npos 1).
	split with x1. split with x2. simpl in |- *. split. reflexivity. split; assumption.
	simpl in H6. inversion H6. induction  x0 as [| p0]. simpl in H6. inversion H6.
	simpl in H6. inversion H6. simpl in H3. elim (H0 m1 N0 s H3). intros.
	elim H1. intros. elim H2. intros. elim H4. intros. elim H5. intros. elim H7.
	intros. split with (Npos 1). split with N0. split with x1. split with x2.
	simpl in |- *. split. reflexivity. elim (iad_conv_inj N0 N0 _ _ H6). intros.
	rewrite <- H10 in H8. rewrite <- H11 in H9. split; assumption.
Qed.

Lemma pl_produit_rec_0 :
 forall tl : term_list,
 (forall u : term,
  term_list_occur u tl ->
  forall (d0 d1 : preDTA) (a0 a1 : ad),
  predta_compatible d0 d1 ->
  reconnaissance d0 a0 u ->
  reconnaissance d1 a1 u ->
  reconnaissance (preDTA_produit d0 d1) (iad_conv a0 a1) u) ->
 forall (d0 d1 : preDTA) (plp0 plp1 : pl_path),
 predta_compatible d0 d1 ->
 pl_path_recon d0 tl plp0 ->
 pl_path_recon d1 tl plp1 ->
 pl_path_recon (preDTA_produit d0 d1) tl (pl_path_product plp0 plp1).
Proof.
	simple induction tl. intros. inversion H1. inversion H2. simpl in |- *. exact (pl_path_rec_nil (preDTA_produit d0 d1)). intros. inversion H2. inversion H3. simpl in |- *. apply
  (pl_path_rec_cons (preDTA_produit d0 d1) (iad_conv a a0) t
     (pl_path_product plp plp2) t0).
	exact (H0 t (tlo_head t t t0 (to_eq t)) d0 d1 a a0 H1 H7 H13). 
	exact
  (H (fun (u : term) (p : term_list_occur u t0) => H0 u (tlo_tail u t t0 p))
     d0 d1 plp plp2 H1 H9 H15).
Qed.

Lemma pl_produit_rec_1 :
 forall (d0 d1 : preDTA) (tl : term_list) (pl0 pl1 : prec_list),
 liste_reconnait d0 pl0 tl ->
 liste_reconnait d1 pl1 tl ->
 pl_tl_length pl0 (lst_length tl) ->
 pl_tl_length pl1 (lst_length tl) ->
 predta_compatible d0 d1 ->
 (forall u : term,
  term_list_occur u tl ->
  forall (d0 d1 : preDTA) (a0 a1 : ad),
  predta_compatible d0 d1 ->
  reconnaissance d0 a0 u ->
  reconnaissance d1 a1 u ->
  reconnaissance (preDTA_produit d0 d1) (iad_conv a0 a1) u) ->
 liste_reconnait (preDTA_produit d0 d1) (pl_produit pl0 pl1) tl.
Proof.
	intros. elim (pl_path_rec_equiv_0 d0 pl0 tl H). elim (pl_path_rec_equiv_0 d1 pl1 tl H0).
	intros. cut (pl_path_incl (pl_path_product x0 x) (pl_produit pl0 pl1)). intro. elim H5.
	intros. elim H6. intros. apply
  (pl_path_rec_equiv_1 (pl_path_product x0 x) (pl_produit pl0 pl1) H7
     (preDTA_produit d0 d1) tl (lst_length tl)). exact (pl_produit_rec_0 tl H4 d0 d1 x0 x H3 H11 H9). apply (pl_tl_length_prod pl0 pl1 (lst_length tl)). exact H1.
	exact H2. elim H5. intros. elim H6. intros. exact (pl_produit_path_incl_2 pl0 pl1 (lst_length tl) x0 x H9 H1 H7 H2).
Qed.

Lemma pl_produit_rec_2 :
 forall tl : term_list,
 (forall u : term,
  term_list_occur u tl ->
  forall (d0 d1 : preDTA) (a0 a1 : ad),
  predta_compatible d0 d1 ->
  reconnaissance (preDTA_produit d0 d1) (iad_conv a0 a1) u ->
  reconnaissance d0 a0 u /\ reconnaissance d1 a1 u) ->
 forall (d0 d1 : preDTA) (plp : pl_path),
 predta_compatible d0 d1 ->
 pl_path_recon (preDTA_produit d0 d1) tl plp ->
 exists plp0 : pl_path,
   (exists plp1 : pl_path,
      plp = pl_path_product plp0 plp1 /\
      pl_path_recon d0 tl plp0 /\ pl_path_recon d1 tl plp1).
Proof.
	simple induction tl. intros. inversion H1. split with pl_path_nil. split with pl_path_nil.
	simpl in |- *. split. reflexivity. split. exact (pl_path_rec_nil d0). exact (pl_path_rec_nil d1). intros. inversion H2. elim
  (H
     (fun (u : term) (pr : term_list_occur u t0) => H0 u (tlo_tail u t t0 pr))
     d0 d1 plp0 H1 H8). intros. elim H9. intros. elim (iad_conv_surj a).
	intros. elim H11. intros. rewrite H12 in H6. elim (H0 t (tlo_head t t t0 (to_eq t)) d0 d1 x1 x2 H1 H6). intros. split with (pl_path_cons x1 x). split with (pl_path_cons x2 x0). simpl in |- *. split. rewrite H12. elim H10. intros. rewrite H15. reflexivity.
	elim H10. intros. elim H16. intros. split. exact (pl_path_rec_cons d0 x1 t x t0 H13 H17). exact (pl_path_rec_cons d1 x2 t x0 t0 H14 H18).
Qed.

Lemma pl_produit_rec_3 :
 forall (d0 d1 : preDTA) (tl : term_list) (pl0 pl1 : prec_list) (n : nat),
 liste_reconnait (preDTA_produit d0 d1) (pl_produit pl0 pl1) tl ->
 predta_compatible d0 d1 ->
 pl_tl_length pl0 n ->
 pl_tl_length pl1 n ->
 (forall u : term,
  term_list_occur u tl ->
  forall (d0 d1 : preDTA) (a0 a1 : ad),
  predta_compatible d0 d1 ->
  reconnaissance (preDTA_produit d0 d1) (iad_conv a0 a1) u ->
  reconnaissance d0 a0 u /\ reconnaissance d1 a1 u) ->
 liste_reconnait d0 pl0 tl /\ liste_reconnait d1 pl1 tl.
Proof.
	intros. elim (pl_path_rec_equiv_0 (preDTA_produit d0 d1) (pl_produit pl0 pl1) tl H). intros. elim H4. intros. elim (pl_produit_rec_2 tl H3 d0 d1 x H0 H6).
	intros. elim H7. intros. elim H8. intros. elim H10. intros. elim (pl_produit_path_incl_4 pl0 pl1 n x H5 H1 H2). intros. elim H13. intros. elim H14. intros. elim H16. intros.
	elim (pl_produit_path_incl_inj x0 x1 x2 x3 n). intros. rewrite <- H19 in H17.
	rewrite <- H20 in H18. split. exact (pl_path_rec_equiv_1 x0 pl0 H17 d0 tl n H11 H1).
	exact (pl_path_rec_equiv_1 x1 pl1 H18 d1 tl n H12 H2). transitivity (lst_length tl).
	exact (pl_path_rec_length x0 tl d0 H11). symmetry  in |- *. exact
  (liste_rec_length (pl_produit pl0 pl1) tl (preDTA_produit d0 d1) n H
     (pl_tl_length_prod pl0 pl1 n H1 H2)).
	transitivity (lst_length tl). exact (pl_path_rec_length x1 tl d1 H12). symmetry  in |- *.
	exact
  (liste_rec_length (pl_produit pl0 pl1) tl (preDTA_produit d0 d1) n H
     (pl_tl_length_prod pl0 pl1 n H1 H2)). exact (pl_path_incl_length x2 pl0 n H17 H1).
	exact (pl_path_incl_length x3 pl1 n H18 H2). transitivity x. symmetry  in |- *. exact H9.
	exact H15.
Qed.

Definition predta_inter_def_0 (t : term) : Prop :=
  forall (d0 d1 : preDTA) (a0 a1 : ad),
  predta_compatible d0 d1 ->
  reconnaissance d0 a0 t ->
  reconnaissance d1 a1 t ->
  reconnaissance (preDTA_produit d0 d1) (iad_conv a0 a1) t.

Definition predta_inter_def_1 (t : term) : Prop :=
  forall (d0 d1 : preDTA) (a0 a1 : ad),
  predta_compatible d0 d1 ->
  reconnaissance (preDTA_produit d0 d1) (iad_conv a0 a1) t ->
  reconnaissance d0 a0 t /\ reconnaissance d1 a1 t.

Lemma predta_inter_0 :
 forall (a : ad) (tl : term_list),
 (forall u : term, term_list_occur u tl -> predta_inter_def_0 u) ->
 predta_inter_def_0 (app a tl).
Proof.
	unfold predta_inter_def_0 in |- *. intros. inversion H1. inversion H2. inversion H4.
	inversion H9. apply
  (rec_dta (preDTA_produit d0 d1) (iad_conv a0 a1) 
     (app a tl) (s_produit ladj ladj0)). exact (predta_produit_2 d0 d1 a0 a1 ladj ladj0 H3 H8).
	apply
  (rec_st (preDTA_produit d0 d1) (s_produit ladj ladj0) a tl
     (pl_produit l l0)).
	exact (s_produit_0 ladj ladj0 a l l0 H17 H23). apply (pl_produit_rec_1 d0 d1 tl l l0 H18 H24). cut (pl_compatible l l0). intro. elim H25. intros. elim H26. intros.
	rewrite <- (liste_rec_length l tl d0 x H18 H27). exact H27. cut (st_compatible ladj ladj0).
	intro. exact (H25 a l l0 H17 H23). apply (H0 ladj ladj0). split with a0. exact H3.
	split with a1. exact H8. cut (pl_compatible l l0). intro. elim H25. intros. elim H26.
	intros. rewrite <- (liste_rec_length l0 tl d1 x H24 H28). exact H28. cut (st_compatible ladj ladj0). intro. exact (H25 a l l0 H17 H23). apply (H0 ladj ladj0). split with a0.
	exact H3. split with a1. exact H8. exact H0. exact H.
Qed.

Lemma predta_inter_1 :
 forall (a : ad) (tl : term_list),
 (forall u : term, term_list_occur u tl -> predta_inter_def_1 u) ->
 predta_inter_def_1 (app a tl).
Proof.
	unfold predta_inter_def_1 in |- *. intros. inversion H1. inversion H3.
	elim (predta_produit_5 d0 d1 (iad_conv a0 a1) ladj H2). intros. elim H13.
	intros. elim H14. intros. elim H15. intros. elim H16. intros. elim H18. intros.
	elim (iad_conv_inj _ _ _ _ H17). intros. rewrite <- H21 in H19. rewrite <- H22 in H20. rewrite (predta_produit_2 d0 d1 a0 a1 x1 x2 H19 H20) in H2. inversion H2.
	rewrite <- H24 in H11. elim (s_produit_1 x1 x2 a l H11). intros. elim H23.
	intros. elim H25. intros. rewrite (s_produit_0 x1 x2 a x3 x4 H26 H27) in H11.
	inversion H11. cut (pl_compatible x3 x4). intros. elim H28. intros. elim H30.
	intros. rewrite <- H29 in H12. elim (pl_produit_rec_3 d0 d1 tl x3 x4 x5 H12 H0 H31 H32 H). intros. split. apply (rec_dta d0 a0 (app a tl) x1 H19). exact (rec_st d0 x1 a tl x3 H26 H33). apply (rec_dta d1 a1 (app a tl) x2 H20).
	exact (rec_st d1 x2 a tl x4 H27 H34). cut (st_compatible x1 x2). intro. exact (H28 a x3 x4 H26 H27). apply (H0 x1 x2). split with a0. exact H19. split with a1.
	exact H20.
Qed.

Lemma predta_inter_direct :
 forall (d0 d1 : preDTA) (a0 a1 : ad) (t : term),
 predta_compatible d0 d1 ->
 reconnaissance d0 a0 t ->
 reconnaissance d1 a1 t ->
 reconnaissance (preDTA_produit d0 d1) (iad_conv a0 a1) t.
Proof.
	intro. intro. intro. intro. intro. exact (indprinciple_term predta_inter_def_0 predta_inter_0 t d0 d1 a0 a1).	
Qed.

Lemma predta_inter_reciproque :
 forall (d0 d1 : preDTA) (a0 a1 : ad) (t : term),
 predta_compatible d0 d1 ->
 reconnaissance (preDTA_produit d0 d1) (iad_conv a0 a1) t ->
 reconnaissance d0 a0 t /\ reconnaissance d1 a1 t.
Proof.
	intro. intro. intro. intro. intro. exact (indprinciple_term predta_inter_def_1 predta_inter_1 t d0 d1 a0 a1).
Qed.

Definition inter (d0 d1 : DTA) : DTA :=
  match d0, d1 with
  | dta p0 a0, dta p1 a1 => dta (preDTA_produit p0 p1) (iad_conv a0 a1)
  end.

Lemma inter_semantics_0 :
 forall (d0 d1 : DTA) (t : term),
 dta_compatible d0 d1 ->
 (reconnait d0 t /\ reconnait d1 t <-> reconnait (inter d0 d1) t).
Proof.
	simple induction d0. simple induction d1. intros. simpl in H. simpl in |- *. split. intros.
	elim H0. intros. exact (predta_inter_direct p p0 a a0 t H H1 H2). intros.
	exact (predta_inter_reciproque p p0 a a0 t H H0).
Qed.

Lemma inter_semantics :
 forall (d0 d1 : DTA) (sigma : signature) (t : term),
 dta_correct_wrt_sign d0 sigma ->
 dta_correct_wrt_sign d1 sigma ->
 (reconnait d0 t /\ reconnait d1 t <-> reconnait (inter d0 d1) t).
Proof.
	exact
  (fun (d0 d1 : DTA) (sigma : signature) (t : term)
     (pr0 : dta_correct_wrt_sign d0 sigma)
     (pr1 : dta_correct_wrt_sign d1 sigma) =>
   inter_semantics_0 d0 d1 t
     (dtas_correct_wrt_sign_compatibles sigma d0 d1 pr0 pr1)).
Qed.