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
Require Import NArith Ndec Ndigits.
Require Import ZArith.
Require Import Classical_Prop.
From IntMap Require Import Allmaps.
Require Import bases.
Require Import defs.
Require Import semantics.
Require Import signature.
Require Import refcorrect.

(* définition des fonctions de modification des adresses *)

Definition uad_conv_0 (a : ad) : ad :=
  match a with
  | N0 => N0
  | Npos p => Npos (xO p)
  end.

Definition uad_conv_1 (a : ad) : ad :=
  match a with
  | N0 => Npos 1
  | Npos p => Npos (xI p)
  end.

Lemma adcnv_inj0 : forall a b : ad, uad_conv_0 a = uad_conv_0 b -> a = b.
Proof.
	simple induction a; simple induction b. intro. trivial. intro. simpl in |- *. intro. 
	inversion H. simpl in |- *. intro. inversion H. simpl in |- *. intros. cut (p = p0).
	simpl in |- *. intro. simpl in |- *. rewrite H0. trivial. inversion H. trivial.
Qed.

Lemma adcnv_inj1 : forall a b : ad, uad_conv_1 a = uad_conv_1 b -> a = b.
Proof.
	simple induction a; simple induction b. intros. trivial. simpl in |- *. intros. 
	inversion H. simpl in |- *. intros. inversion H. simpl in |- *. intros.
	cut (p = p0). intro. rewrite H0. trivial. inversion H. trivial.
Qed.

Lemma adcnv_ok : forall a b : ad, uad_conv_0 a <> uad_conv_1 b.
Proof.
	simple induction a; simple induction b. simpl in |- *. intro. inversion H.
	simpl in |- *. intros. intro. inversion H. simpl in |- *. intro. inversion H.
	simpl in |- *. intros. intro. inversion H.
Qed.

Lemma adcnv_disj :
 forall a : ad, exists b : ad, a = uad_conv_0 b \/ a = uad_conv_1 b.
Proof.
	simple induction a. split with N0. left. simpl in |- *. trivial. simple induction p.
	intros. split with (Npos p0). right. simpl in |- *. trivial. intros.
	split with (Npos p0). left. simpl in |- *. trivial. split with N0.
	right. simpl in |- *. trivial.
Qed.

(* calcul des automates modifiés *)

Fixpoint upl_conv_0 (p : prec_list) : prec_list :=
  match p with
  | prec_empty => prec_empty
  | prec_cons a p0 p1 =>
      prec_cons (uad_conv_0 a) (upl_conv_0 p0) (upl_conv_0 p1)
  end.

Fixpoint upl_conv_1 (p : prec_list) : prec_list :=
  match p with
  | prec_empty => prec_empty
  | prec_cons a p0 p1 =>
      prec_cons (uad_conv_1 a) (upl_conv_1 p0) (upl_conv_1 p1)
  end.

Fixpoint umpl_conv_0 (s : state) : state :=
  match s with
  | M0 => M0 prec_list
  | M1 a p => M1 prec_list a (upl_conv_0 p)
  | M2 p0 p1 => M2 prec_list (umpl_conv_0 p0) (umpl_conv_0 p1)
  end.

Fixpoint umpl_conv_1 (s : state) : state :=
  match s with
  | M0 => M0 prec_list
  | M1 a p => M1 prec_list a (upl_conv_1 p)
  | M2 p0 p1 => M2 prec_list (umpl_conv_1 p0) (umpl_conv_1 p1)
  end.

Fixpoint udta_conv_0_aux (d : preDTA) : preDTA :=
  match d with
  | M0 => M0 state
  | M1 a s => M1 state a (umpl_conv_0 s)
  | M2 s0 s1 => M2 state (udta_conv_0_aux s0) (udta_conv_0_aux s1)
  end.

Fixpoint udta_conv_1_aux (d : preDTA) : preDTA :=
  match d with
  | M0 => M0 state
  | M1 a s => M1 state a (umpl_conv_1 s)
  | M2 s0 s1 => M2 state (udta_conv_1_aux s0) (udta_conv_1_aux s1)
  end.

Definition udta_conv_0 (d : preDTA) : preDTA :=
  M2 state (udta_conv_0_aux d) (M0 state).

Definition udta_conv_1 (d : preDTA) : preDTA :=
  M2 state (M0 state) (udta_conv_1_aux d).

(* lemmes d'injectivité *)

Lemma upl_conv_0_inj :
 forall p0 p1 : prec_list, upl_conv_0 p0 = upl_conv_0 p1 -> p0 = p1.
Proof.
	simple induction p0. intros. induction  p2 as [a0 p2_1 Hrecp2_1 p2_0 Hrecp2_0| ]. simpl in H1. inversion H1. 
	cut (p = p2_1). cut (p1 = p2_0). intros. rewrite H2. rewrite H6. cut (a = a0).
	intro. rewrite H7. trivial. exact (adcnv_inj0 a a0 H3).
	exact (H0 p2_0 H5). exact (H p2_1 H4). simpl in H1. inversion H1.
	simple induction p1. intros. inversion H1. intros. trivial.
Qed.

Lemma upl_conv_1_inj :
 forall p0 p1 : prec_list, upl_conv_1 p0 = upl_conv_1 p1 -> p0 = p1.
Proof.
	simple induction p0. intros. induction  p2 as [a0 p2_1 Hrecp2_1 p2_0 Hrecp2_0| ]. simpl in H1. inversion H1.
	cut (a = a0). cut (p = p2_1). cut (p1 = p2_0). intros. rewrite H2. rewrite H6.
	rewrite H7. trivial. exact (H0 p2_0 H5). exact (H p2_1 H4).
 	exact (adcnv_inj1 a a0 H3). inversion H1. simple induction p1. intros.
	inversion H1. intros. trivial.
Qed.

Lemma umpl_conv_0_inj :
 forall s0 s1 : state, umpl_conv_0 s0 = umpl_conv_0 s1 -> s0 = s1.
Proof.
	simple induction s0. simple induction s1. simpl in |- *. intros. trivial.
	intros. inversion H. intros. simpl in H1. inversion H1. intro.
	intro. simple induction s1. intros. simpl in H. inversion H. intros.
	simpl in H. inversion H. cut (a0 = a2). intro. rewrite H0. trivial.
	exact (upl_conv_0_inj a0 a2 H2). intros. inversion H1. intro.
	intro. intro. intro. simple induction s1. intros. inversion H1.  intros.
	inversion H1. intros. simpl in H3. inversion H3. cut (m = m1).
	cut (m0 = m2). intros. rewrite H4. rewrite <- H7. trivial.  
	exact (H0 m2 H6). exact (H m1 H5).
Qed.

Lemma umpl_conv_1_inj :
 forall s0 s1 : state, umpl_conv_1 s0 = umpl_conv_1 s1 -> s0 = s1.
Proof.
	simple induction s0. simple induction s1. intros. trivial. intros. inversion H.
	intros. inversion H1. intro. intro. simple induction s1. intros.
	inversion H. intros. simpl in H. inversion H. cut (a0 = a2). intro.
	rewrite H0. trivial. exact (upl_conv_1_inj a0 a2 H2). intros.
	inversion H1. intro. intro. intro. intro. simple induction s1. intros.
	inversion H1. intros. inversion H1. intros. simpl in H3.
	inversion H3. cut (m = m1). cut (m0 = m2). intros. rewrite H4. rewrite H7.
	trivial. exact (H0 m2 H6). exact (H m1 H5).
Qed.

(* lemmes sur les images des applications précédentes *)

Lemma upl_conv_0_img :
 forall (p : prec_list) (a : ad) (la ls : prec_list),
 upl_conv_0 p = prec_cons a la ls ->
 exists a0 : ad,
   (exists la0 : prec_list,
      (exists ls0 : prec_list, p = prec_cons a0 la0 ls0)).
Proof.
	simple induction p. intros. split with a. split with p0. split with p1.
	trivial. intros. inversion H.
Qed.

Lemma upl_conv_0_img_0 :
 forall (p : prec_list) (a : ad) (la ls : prec_list),
 upl_conv_0 p = prec_cons a la ls ->
 exists a0 : ad,
   (exists la0 : prec_list,
      (exists ls0 : prec_list,
         p = prec_cons a0 la0 ls0 /\
         a = uad_conv_0 a0 /\ la = upl_conv_0 la0 /\ ls = upl_conv_0 ls0)).
Proof.
	intros. cut
  (exists a0 : ad,
     (exists la0 : prec_list,
        (exists ls0 : prec_list, p = prec_cons a0 la0 ls0))).
	intros. elim H0. intros. elim H1. intros. elim H2. intros.
	rewrite H3 in H. split with x. split with x0. split with x1.
	split. assumption. split. inversion H. trivial. split.
	inversion H; trivial. inversion H. trivial.
	exact (upl_conv_0_img p a la ls H).
Qed.

Lemma upl_conv_0_img_1 :
 forall p : prec_list, upl_conv_0 p = prec_empty -> p = prec_empty.
Proof.
	simple induction p. intros. inversion H1. intros. trivial.
Qed.

Lemma upl_conv_1_img :
 forall (p : prec_list) (a : ad) (la ls : prec_list),
 upl_conv_1 p = prec_cons a la ls ->
 exists a0 : ad,
   (exists la0 : prec_list,
      (exists ls0 : prec_list, p = prec_cons a0 la0 ls0)).
Proof.
	simple induction p. intros. split with a. split with p0. split with p1.
	trivial. intros. inversion H.
Qed.

Lemma upl_conv_1_img_0 :
 forall (p : prec_list) (a : ad) (la ls : prec_list),
 upl_conv_1 p = prec_cons a la ls ->
 exists a0 : ad,
   (exists la0 : prec_list,
      (exists ls0 : prec_list,
         p = prec_cons a0 la0 ls0 /\
         a = uad_conv_1 a0 /\ la = upl_conv_1 la0 /\ ls = upl_conv_1 ls0)).
Proof.
	intros. cut
  (exists a0 : ad,
     (exists la0 : prec_list,
        (exists ls0 : prec_list, p = prec_cons a0 la0 ls0))).
	intros. elim H0. intros. elim H1. intros. elim H2. intros.
	rewrite H3 in H. split with x. split with x0. split with x1.
	split. assumption. split. inversion H. trivial. split.
	inversion H; trivial. inversion H. trivial.
	exact (upl_conv_1_img p a la ls H).
Qed.

Lemma upl_conv_1_img_1 :
 forall p : prec_list, upl_conv_1 p = prec_empty -> p = prec_empty.
Proof.
	simple induction p. intros. inversion H1. intros. trivial.
Qed.

(* invariants sur les MapGet pour conv_0 *)

Lemma u_conv_0_invar_0 :
 forall (d : preDTA) (a : ad) (ladj : state),
 MapGet state d a = Some ladj ->
 MapGet state (udta_conv_0 d) (uad_conv_0 a) = Some (umpl_conv_0 ladj).
Proof.
	simple induction d. intros. simpl in H. inversion H. intros.
	unfold udta_conv_0 in |- *. unfold udta_conv_0_aux in |- *. cut (a = a1).
	intro. rewrite H0. rewrite H0 in H. induction  a1 as [| p]. simpl in |- *.
	simpl in H. inversion H. trivial. simpl in |- *. simpl in H.
	cut (Peqb p p = true). intro. rewrite H1 in H. rewrite H1.
	inversion H. trivial. exact (aux_Neqb_1_0 p). intros. 
	cut (Neqb a a1 = true). intro. exact (Neqb_complete a a1 H0).
	cut (Neqb a a1 = true \/ Neqb a a1 = false). intros. elim H0.
	intros. assumption. intro. 
	cut (MapGet state (M1 state a a0) a1 = None).
	intro. rewrite H2 in H. inversion H.
	exact (M1_semantics_2 state a a1 a0 H1).
	exact (bool_is_true_or_false (Neqb a a1)).
	intro. intro. intro. intro. simple induction a. exact (H N0).
	simple induction p. intros. simpl in |- *. simpl in H2. 
	exact (H0 (Npos p0) ladj H2). intros. simpl in |- *. simpl in H2.
	exact (H (Npos p0) ladj H2). intros. simpl in H1. simpl in |- *.
	exact (H0 N0 ladj H1).
Qed.

Lemma u_conv_0_invar_1 :
 forall (s : state) (c : ad) (p : prec_list),
 MapGet prec_list s c = Some p ->
 MapGet prec_list (umpl_conv_0 s) c = Some (upl_conv_0 p).
Proof.
	simple induction s. intros. simpl in H. inversion H. intros.
	simpl in |- *. simpl in H. cut (Neqb a c = true). intro.
	rewrite H0 in H. rewrite H0. inversion H. trivial.
	cut (Neqb a c = true \/ Neqb a c = false). intro. 
	elim H0; intros. assumption. rewrite H1 in H.
	inversion H. exact (bool_is_true_or_false (Neqb a c)).
	intro. intro. intro. intro. simple induction c. simpl in |- *. intros.
	exact (H N0 p H1). simple induction p. intros. simpl in H2.
	simpl in |- *. exact (H0 (Npos p0) p1 H2). intros. simpl in |- *.
	simpl in H2. exact (H (Npos p0) p1 H2).
	intros. simpl in |- *. simpl in H1. exact (H0 N0 p0 H1).
Qed.

Lemma u_conv_0_invar_2 :
 forall (d : preDTA) (a : ad) (ladj : state),
 MapGet state (udta_conv_0 d) (uad_conv_0 a) = Some (umpl_conv_0 ladj) ->
 MapGet state d a = Some ladj.
Proof.
	simple induction d. simple induction a. intros. inversion H. simple induction p.
	intros. inversion H0. intros. simpl in H0. inversion H0.
	intros. inversion H. simple induction a; intro. simple induction a1. simpl in |- *.
	intros. simpl in H. inversion H. cut (a0 = ladj). intros. rewrite H0.
	trivial. exact (umpl_conv_0_inj a0 ladj H1). simple induction p. intros.
	simpl in H0. inversion H0. intros. inversion H0. intros. inversion H.
	intro. simple induction a1. intros. inversion H. intros. induction  p as [p Hrecp| p Hrecp| ].
	induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. simpl in H. simpl in |- *.
	cut (Peqb p p0 = true \/ Peqb p p0 = false). intro. elim H0; intros.
	rewrite H1. rewrite H1 in H. inversion H. cut (a0 = ladj). intro. rewrite H2.
	trivial.  exact (umpl_conv_0_inj a0 ladj H3). rewrite H1. rewrite H1 in H.
	inversion H. exact (bool_is_true_or_false (Peqb p p0)).
	inversion H. inversion H. simpl in H. simpl in |- *.
	cut (Peqb (xO p) p0 = true \/ Peqb (xO p) p0 = false). intro.
	elim H0; intros. rewrite H1. rewrite H1 in H. inversion H. cut (a0 = ladj).
	intro. rewrite H2. trivial. exact (umpl_conv_0_inj a0 ladj H3).
	rewrite H1 in H. inversion H. 
	exact (bool_is_true_or_false (Peqb (xO p) p0)). simpl in |- *. simpl in H. 
	cut (Peqb 1 p0 = true \/ Peqb 1 p0 = false). intro. elim H0; intros.
	rewrite H1 in H. rewrite H1. inversion H. cut (a0 = ladj). intros. rewrite H2.
	trivial. exact (umpl_conv_0_inj a0 ladj H3). rewrite H1 in H. inversion H.
	exact (bool_is_true_or_false (Peqb 1 p0)). intros. induction  a as [| p].
	simpl in H1. unfold udta_conv_0 in H. simpl in |- *. apply (H N0 ladj).
	simpl in |- *. trivial. induction  p as [p Hrecp| p Hrecp| ]. simpl in |- *. unfold udta_conv_0 in H0.
	apply (H0 (Npos p) ladj). simpl in |- *. simpl in H1. trivial. simpl in |- *. simpl in H1.
	unfold udta_conv_0 in H. exact (H (Npos p) ladj H1). simpl in |- *. simpl in H1.
	unfold udta_conv_0 in H0. exact (H0 N0 ladj H1).
Qed.

Lemma u_conv_0_invar_3 :
 forall (s : state) (c : ad) (p : prec_list),
 MapGet prec_list (umpl_conv_0 s) c = Some (upl_conv_0 p) ->
 MapGet prec_list s c = Some p.
Proof.
	simple induction s. intros. inversion H. simple induction a. intro.
	simple induction c. simpl in |- *. intros. inversion H. cut (a0 = p). intros. rewrite H0.
	trivial. exact (upl_conv_0_inj a0 p H1). simpl in |- *. intros. inversion H.
	intro. intro. simple induction c. simpl in |- *. intros. inversion H. induction  p as [p Hrecp| p Hrecp| ].
	simple induction p0. intros. simpl in H0. 
	cut (Peqb p p1 = true \/ Peqb p p1 = false). intros. elim H1; intros.
	simpl in |- *. rewrite H2. rewrite H2 in H0. inversion H0. cut (a0 = p2). intro.
	rewrite H3. trivial. exact (upl_conv_0_inj a0 p2 H4). simpl in |- *. rewrite H2.
	rewrite H2 in H0. inversion H0. exact (bool_is_true_or_false (Peqb p p1)).
	intros. inversion H0. intros. inversion H. simple induction p0. intros. inversion H0.
	intros. simpl in H0. simpl in |- *. cut (Peqb p p1 = true \/ Peqb p p1 = false).
	intros. elim H1; intros. rewrite H2 in H0. rewrite H2. inversion H0.
	cut (a0 = p2). intro. rewrite H3. trivial. exact (upl_conv_0_inj a0 p2 H4).
	rewrite H2. rewrite H2 in H0. inversion H0.
	exact (bool_is_true_or_false (Peqb p p1)). intros. inversion H.
	simple induction p. intros. inversion H0. intros. inversion H0. intros. simpl in H.
	inversion H. cut (a0 = p0). intro. rewrite H0. trivial.
	exact (upl_conv_0_inj a0 p0 H1). intro. intro. intro. intro. simple induction c.
	simpl in |- *. intros. exact (H N0 p H1). simple induction p. intros. simpl in |- *. simpl in H2.
	exact (H0 (Npos p0) p1 H2). intros; simpl in |- *. simpl in H2. 
	exact (H (Npos p0) p1 H2). intros; simpl in |- *. simpl in H1. exact (H0 N0 p0 H1).
Qed.

Lemma u_conv_0_invar_4 :
 forall (d : preDTA) (a : ad) (ladj : state),
 MapGet state (udta_conv_0 d) (uad_conv_0 a) = Some ladj ->
 exists ladj0 : _, ladj = umpl_conv_0 ladj0.
Proof.
	simple induction d. intros. induction  a as [| p]. simpl in H. inversion H.
	induction  p as [p Hrecp| p Hrecp| ]; simpl in H; inversion H. simple induction a. intro. simple induction a1.
	intros. simpl in H. induction  a0 as [| a0 a2| a0_1 Hreca0_1 a0_0 Hreca0_0]. simpl in H. split with (M0 prec_list).
	simpl in |- *. inversion H. trivial. split with (M1 prec_list a0 a2). inversion H.
	trivial. split with (M2 prec_list a0_1 a0_0). inversion H. trivial. simpl in |- *.
	intros. inversion H. intro. intro. simple induction a1. simpl in |- *. intros. inversion H.
	simpl in |- *. intros. cut (Peqb p p0 = true \/ Peqb p p0 = false). intro.
	elim H0; intros. rewrite H1 in H. inversion H. split with a0. trivial.
	rewrite H1 in H. inversion H. exact (bool_is_true_or_false (Peqb p p0)).
	intro. intro. intro. intro. simple induction a. simpl in |- *. intros. exact (H N0 ladj H1).
	simple induction p. intros. simpl in H2. exact (H0 (Npos p0) ladj H2). intros.
	simpl in H2. exact (H (Npos p0) ladj H2). simpl in |- *. intros. exact (H0 N0 ladj H1).
Qed.

Lemma u_conv_0_invar_5 :
 forall (d : preDTA) (a : ad) (ladj : state),
 MapGet state (udta_conv_0 d) (uad_conv_0 a) = Some ladj ->
 exists ladj0 : _,
   ladj = umpl_conv_0 ladj0 /\ MapGet state d a = Some ladj0.
Proof.
	intros. cut (exists ladj0 : state, ladj = umpl_conv_0 ladj0).
	intros. elim H0. intros. split with x. split. assumption. rewrite H1 in H.
	exact (u_conv_0_invar_2 d a x H). exact (u_conv_0_invar_4 d a ladj H).
Qed.

Lemma u_conv_0_invar_6 :
 forall (s : state) (c : ad) (p : prec_list),
 MapGet prec_list (umpl_conv_0 s) c = Some p ->
 exists p0 : prec_list, p = upl_conv_0 p0.
Proof.
	simple induction s. intros. induction  c as [| p0]. inversion H. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]; inversion H.
	simple induction a. intro. simple induction c. intros. simpl in H. inversion H. split with a0.
	trivial. simpl in |- *. intros. inversion H. simple induction p. intro. intro. simple induction c.
	simpl in |- *. intros. inversion H0. simpl in |- *. simple induction p1. intros. simpl in H1.
	cut (Peqb p0 p2 = true \/ Peqb p0 p2 = false). intro. elim H2. intros. 
	rewrite H3 in H1. inversion H1. split with a0. trivial. intro. rewrite H3 in H1.
	inversion H1. exact (bool_is_true_or_false (Peqb p0 p2)). intros. inversion H1.
	intros. inversion H0. intro. intro. intro. simple induction c. intros. inversion H0.
	simple induction p1. intros. simpl in H1. inversion H1. intros. simpl in H1.
	cut (Peqb p0 p2 = true \/ Peqb p0 p2 = false). intro. elim H2; intro. 
	rewrite H3 in H1. inversion H1. split with a0. trivial. rewrite H3 in H1. inversion H1.
	exact (bool_is_true_or_false (Peqb p0 p2)). intros. inversion H0. intro.
	simple induction c. intros. inversion H. simple induction p0. intros. inversion H0. intros.
	inversion H0. intros. simpl in H. inversion H. split with a0. trivial. intro. intro.
	intro. intro. simple induction c. simpl in |- *. intros. simpl in H1. exact (H N0 p H1). simple induction p.
	intros. simpl in H2. exact (H0 (Npos p0) p1 H2). intros. simpl in H2. 
	exact (H (Npos p0) p1 H2). simpl in |- *. intros. exact (H0 N0 p0 H1).
Qed.

Lemma u_conv_0_invar_7 :
 forall (s : state) (c : ad) (p : prec_list),
 MapGet prec_list (umpl_conv_0 s) c = Some p ->
 exists p0 : prec_list,
   p = upl_conv_0 p0 /\ MapGet prec_list s c = Some p0.
Proof.
	intros. elim (u_conv_0_invar_6 s c p H). intros. split with x.
	intros. split. assumption. rewrite H0 in H. 
	exact (u_conv_0_invar_3 s c x H).
Qed.

Lemma u_conv_0_invar_8 :
 forall (p0 : preDTA) (a0 : ad) (s0 : state),
 MapGet state (udta_conv_0 p0) a0 = Some s0 ->
 exists a1 : ad, a0 = uad_conv_0 a1.
Proof.
	simple induction p0. intros. induction  a0 as [| p]. simpl in H. inversion H.
	induction  p as [p Hrecp| p Hrecp| ]; simpl in H; inversion H.
	unfold udta_conv_0 in |- *. unfold udta_conv_0_aux in |- *. intros.
	induction  a as [| p]. split with N0. unfold uad_conv_0 in |- *. induction  a1 as [| p].
	trivial. simpl in H. induction  p as [p Hrecp| p Hrecp| ]; inversion H.
	split with (Npos p). simpl in |- *. induction  a1 as [| p1]. simpl in H.
	inversion H. induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]. simpl in H. inversion H.
	simpl in H. cut (Peqb p p1 = true). intro. cut (p1 = p).
	intro. rewrite H1. trivial. symmetry  in |- *. 
	exact (aux_Neqb_1_1 p p1 H0).
	cut (Peqb p p1 = true \/ Peqb p p1 = false). intro.
	elim H0; intros. assumption. rewrite H1 in H. inversion H.
	exact (bool_is_true_or_false (Peqb p p1)).
 	simpl in H. inversion H. unfold udta_conv_0 in |- *. intro. intro.
	intro. intro. simple induction a0. intros. split with N0. simpl in |- *.
	trivial. simple induction p. intros. inversion H2. intros.
	split with (Npos p1). simpl in |- *. trivial. intros. inversion H1.
Qed.

(* invariant de reconnaissance sur conv_0 : sens direct *)

Definition u_conv_rec_0 (p : preDTA) (a : ad) (t : term)
  (pr : reconnaissance p a t) :=
  reconnaissance (udta_conv_0 p) (uad_conv_0 a) t.

Definition u_conv_str_0 (p : preDTA) (s : state) (t : term)
  (pr : state_reconnait p s t) :=
  state_reconnait (udta_conv_0 p) (umpl_conv_0 s) t.

Definition u_conv_lr_0 (p : preDTA) (p0 : prec_list) 
  (t : term_list) (pr : liste_reconnait p p0 t) :=
  liste_reconnait (udta_conv_0 p) (upl_conv_0 p0) t.

Lemma u_conv0_0 :
 forall (d : preDTA) (a : ad) (t : term) (ladj : state)
   (e : MapGet state d a = Some ladj) (s : state_reconnait d ladj t),
 u_conv_str_0 d ladj t s -> u_conv_rec_0 d a t (rec_dta d a t ladj e s).
Proof.
	intros. unfold u_conv_rec_0 in |- *. unfold u_conv_str_0 in H.
	cut
  (MapGet state (udta_conv_0 d) (uad_conv_0 a) =
   Some (umpl_conv_0 ladj)). intros.
	exact (rec_dta (udta_conv_0 d) (uad_conv_0 a) t (umpl_conv_0 ladj) H0 H). 
	exact (u_conv_0_invar_0 d a ladj e).
Qed.

Lemma u_conv0_1 :
 forall (d : preDTA) (s : state) (c : ad) (tl : term_list) 
   (l : prec_list) (e : MapGet prec_list s c = Some l)
   (l0 : liste_reconnait d l tl),
 u_conv_lr_0 d l tl l0 ->
 u_conv_str_0 d s (app c tl) (rec_st d s c tl l e l0).
Proof.
	intros. unfold u_conv_str_0 in |- *. unfold u_conv_lr_0 in H.
	cut (MapGet prec_list (umpl_conv_0 s) c = Some (upl_conv_0 l)). intros.
	exact (rec_st (udta_conv_0 d) (umpl_conv_0 s) c tl (upl_conv_0 l) H0 H).
	exact (u_conv_0_invar_1 s c l e).
Qed.

Lemma u_conv0_2 :
 forall d : preDTA, u_conv_lr_0 d prec_empty tnil (rec_empty d).
Proof.
	intros. unfold u_conv_lr_0 in |- *. simpl in |- *.
	exact (rec_empty (udta_conv_0 d)).
Qed.

Lemma u_conv0_3 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list) (r : reconnaissance d a hd),
 u_conv_rec_0 d a hd r ->
 forall l : liste_reconnait d la tl,
 u_conv_lr_0 d la tl l ->
 u_conv_lr_0 d (prec_cons a la ls) (tcons hd tl)
   (rec_consi d a la ls hd tl r l).
Proof.
	intros. unfold u_conv_lr_0 in |- *. unfold u_conv_rec_0 in H. 
	unfold u_conv_lr_0 in H0. simpl in |- *.
	exact
  (rec_consi (udta_conv_0 d) (uad_conv_0 a) (upl_conv_0 la) 
     (upl_conv_0 ls) hd tl H H0).
Qed.

Lemma u_conv0_4 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list) (l : liste_reconnait d ls (tcons hd tl)),
 u_conv_lr_0 d ls (tcons hd tl) l ->
 u_conv_lr_0 d (prec_cons a la ls) (tcons hd tl)
   (rec_consn d a la ls hd tl l).
Proof.
	intros. unfold u_conv_lr_0 in |- *. simpl in |- *. unfold u_conv_lr_0 in H.
	exact
  (rec_consn (udta_conv_0 d) (uad_conv_0 a) (upl_conv_0 la) 
     (upl_conv_0 ls) hd tl H).  
Qed.

Lemma u_conv0_5 :
 forall (p : preDTA) (a : ad) (t : term) (r : reconnaissance p a t),
 u_conv_rec_0 p a t r.
Proof.
	exact
  (mreconnaissance_ind u_conv_rec_0 u_conv_str_0 u_conv_lr_0 u_conv0_0
     u_conv0_1 u_conv0_2 u_conv0_3 u_conv0_4).
Qed.

Lemma u_conv0 :
 forall (p : preDTA) (a : ad) (t : term),
 reconnaissance p a t -> reconnaissance (udta_conv_0 p) (uad_conv_0 a) t.
Proof.
	intros. exact (u_conv0_5 p a t H).
Qed.

(* invariant de reconnaissance sur conv_0 : sens reciproque *)

Definition u_conv_rec_0_r (p0 : preDTA) (a0 : ad) (t : term)
  (pr0 : reconnaissance p0 a0 t) :=
  forall (p : preDTA) (a : ad),
  p0 = udta_conv_0 p -> a0 = uad_conv_0 a -> reconnaissance p a t.

Definition u_conv_str_0_r (p0 : preDTA) (s0 : state) 
  (t : term) (pr : state_reconnait p0 s0 t) :=
  forall (p : preDTA) (s : state),
  p0 = udta_conv_0 p -> s0 = umpl_conv_0 s -> state_reconnait p s t.

Definition u_conv_lr_0_r (p0 : preDTA) (pl0 : prec_list) 
  (t : term_list) (pr : liste_reconnait p0 pl0 t) :=
  forall (p : preDTA) (pl : prec_list),
  p0 = udta_conv_0 p -> pl0 = upl_conv_0 pl -> liste_reconnait p pl t.

Lemma u_conv0_0r :
 forall (d : preDTA) (a : ad) (t : term) (ladj : state)
   (e : MapGet state d a = Some ladj) (s : state_reconnait d ladj t),
 u_conv_str_0_r d ladj t s -> u_conv_rec_0_r d a t (rec_dta d a t ladj e s).
Proof.
	intros. unfold u_conv_str_0_r in H. unfold u_conv_rec_0_r in |- *.
	intros. rewrite H0 in e. rewrite H1 in e. 
	elim (u_conv_0_invar_5 p a0 ladj e). intros. elim H2. intros.
	apply (rec_dta p a0 t x H4). apply (H p x). exact H0. exact H3.
Qed.

Lemma u_conv0_1r :
 forall (d : preDTA) (s : state) (c : ad) (tl : term_list) 
   (l : prec_list) (e : MapGet prec_list s c = Some l)
   (l0 : liste_reconnait d l tl),
 u_conv_lr_0_r d l tl l0 ->
 u_conv_str_0_r d s (app c tl) (rec_st d s c tl l e l0).
Proof.
	intros. unfold u_conv_lr_0_r in H. unfold u_conv_str_0_r in |- *. intros.
	rewrite H1 in e. elim (u_conv_0_invar_7 s0 c l e). intros. elim H2.
	intros. apply (rec_st p s0 c tl x H4). exact (H p x H0 H3).
Qed.

Lemma u_conv0_2r :
 forall d : preDTA, u_conv_lr_0_r d prec_empty tnil (rec_empty d).
Proof.
	intros. unfold u_conv_lr_0_r in |- *. intros. cut (pl = prec_empty). intros.
	rewrite H1. exact (rec_empty p). cut (upl_conv_0 prec_empty = prec_empty).
	intros. rewrite <- H1 in H0. symmetry  in |- *. 
	exact (upl_conv_0_inj prec_empty pl H0). simpl in |- *. trivial.
Qed.

Lemma u_conv0_3r :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list) (r : reconnaissance d a hd),
 u_conv_rec_0_r d a hd r ->
 forall l : liste_reconnait d la tl,
 u_conv_lr_0_r d la tl l ->
 u_conv_lr_0_r d (prec_cons a la ls) (tcons hd tl)
   (rec_consi d a la ls hd tl r l).
Proof.
	intros. unfold u_conv_lr_0_r in |- *. unfold u_conv_rec_0_r in H.
	unfold u_conv_lr_0_r in H0. intros. cut (upl_conv_0 pl = prec_cons a la ls).
	intro. cut
  (exists a0 : ad,
     (exists la0 : prec_list,
        (exists ls0 : prec_list,
           pl = prec_cons a0 la0 ls0 /\
           a = uad_conv_0 a0 /\ la = upl_conv_0 la0 /\ ls = upl_conv_0 ls0))).
	intro. elim H4. intros. elim H5. intros. elim H6. intros. elim H7.
	intros. elim H9. intros. elim H11. intros. rewrite H8. 	
	apply (rec_consi p x x0 x1 hd tl). apply (H p x). exact H1. trivial.
	exact (H0 p x0 H1 H12). exact (upl_conv_0_img_0 pl a la ls H3).
	symmetry  in |- *. trivial.
Qed.

Lemma u_conv0_4r :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list) (l : liste_reconnait d ls (tcons hd tl)),
 u_conv_lr_0_r d ls (tcons hd tl) l ->
 u_conv_lr_0_r d (prec_cons a la ls) (tcons hd tl)
   (rec_consn d a la ls hd tl l).
Proof.
	intros. unfold u_conv_lr_0_r in H. unfold u_conv_lr_0_r in |- *. intros.
	cut (upl_conv_0 pl = prec_cons a la ls). cut
  (exists a0 : ad,
     (exists la0 : prec_list,
        (exists ls0 : prec_list,
           pl = prec_cons a0 la0 ls0 /\
           a = uad_conv_0 a0 /\ la = upl_conv_0 la0 /\ ls = upl_conv_0 ls0))).
	intros. elim H2. intros. elim H4. intros. elim H5. intros. elim H6.
	intros. elim H8. intros. elim H10. intros. rewrite H7.
	exact (rec_consn p x x0 x1 hd tl (H p x1 H0 H12)).
	cut (upl_conv_0 pl = prec_cons a la ls). intro.
	exact (upl_conv_0_img_0 pl a la ls H2). symmetry  in |- *. trivial. symmetry  in |- *.
	trivial.
Qed.

Lemma u_conv0_5r :
 forall (p : preDTA) (a : ad) (t : term) (r : reconnaissance p a t),
 u_conv_rec_0_r p a t r.
Proof.
	exact
  (mreconnaissance_ind u_conv_rec_0_r u_conv_str_0_r u_conv_lr_0_r u_conv0_0r
     u_conv0_1r u_conv0_2r u_conv0_3r u_conv0_4r).
Qed.

Lemma u_conv0_r :
 forall (p : preDTA) (a : ad) (t : term),
 reconnaissance (udta_conv_0 p) (uad_conv_0 a) t -> reconnaissance p a t.
Proof.
	intros. apply (u_conv0_5r (udta_conv_0 p) (uad_conv_0 a) t H p a). trivial. trivial.
Qed.

(* invariants sur les MapGet : conv_1 *)

Lemma u_conv_1_invar_0 :
 forall (d : preDTA) (a : ad) (ladj : state),
 MapGet state d a = Some ladj ->
 MapGet state (udta_conv_1 d) (uad_conv_1 a) = Some (umpl_conv_1 ladj).
Proof.
	simple induction d. intros. simpl in H. inversion H. intros. 
	unfold udta_conv_1 in |- *. cut (a = a1). intro. rewrite H0. rewrite H0 in H.
	induction  a1 as [| p]. simpl in |- *. simpl in H. inversion H. inversion H. trivial.
	simpl in |- *. simpl in H. cut (Peqb p p = true). intro. rewrite H1. simpl in H.
	rewrite H1 in H. inversion H. trivial. exact (aux_Neqb_1_0 p).
 	cut (Neqb a a1 = true \/ Neqb a a1 = false). intros. elim H0. intros.
	exact (Neqb_complete a a1 H1). intro. 
	cut (MapGet state (M1 state a a0) a1 = None).
	intro. rewrite H2 in H. inversion H.
	exact (M1_semantics_2 state a a1 a0 H1).
	exact (bool_is_true_or_false (Neqb a a1)).
	intro. intro. intro. intro. simple induction a. simpl in |- *. intros. 
	exact (H N0 ladj H1). simple induction p. intros. simpl in |- *. simpl in H2.
	exact (H0 (Npos p0) ladj H2). intros. simpl in |- *. simpl in H2.
	exact (H (Npos p0) ladj H2). intros. simpl in |- *. simpl in H1.
	exact (H0 N0 ladj H1).
Qed.

Lemma u_conv_1_invar_1 :
 forall (s : state) (c : ad) (p : prec_list),
 MapGet prec_list s c = Some p ->
 MapGet prec_list (umpl_conv_1 s) c = Some (upl_conv_1 p).
Proof.
	simple induction s. simpl in |- *. intros. inversion H.
	intros. simpl in H. simpl in |- *. cut (Neqb a c = true). intro.
	rewrite H0 in H. rewrite H0. inversion H. trivial.
	cut (Neqb a c = true \/ Neqb a c = false). intros.
	elim H0; intros. assumption. rewrite H1 in H. inversion H.
	exact (bool_is_true_or_false (Neqb a c)).
	intro. intro. intro. intro. simple induction c. simpl in |- *. intros.
	exact (H N0 p H1). simple induction p. intros. simpl in H2.
	simpl in |- *. exact (H0 (Npos p0) p1 H2). intros. simpl in |- *. 
	simpl in H2. exact (H (Npos p0) p1 H2).
	intros. simpl in |- *. simpl in H1. exact (H0 N0 p0 H1).
Qed.

Lemma u_conv_1_invar_2 :
 forall (d : preDTA) (a : ad) (ladj : state),
 MapGet state (udta_conv_1 d) (uad_conv_1 a) = Some (umpl_conv_1 ladj) ->
 MapGet state d a = Some ladj.
Proof.
	simple induction d. intros. induction  a as [| p]. simpl in H. inversion H.
	induction  p as [p Hrecp| p Hrecp| ]; inversion H. simple induction a. intro. simple induction a1. simpl in |- *.
	intros. inversion H. cut (a0 = ladj). intro. rewrite H0. trivial.
	exact (umpl_conv_1_inj a0 ladj H1). simpl in |- *. intros. inversion H.
	simple induction p. intro. intro. intro. simple induction a1. intros. simpl in H0.
	inversion H0. simple induction p1. intros. simpl in H1. simpl in |- *.
	cut (Peqb p0 p2 = true \/ Peqb p0 p2 = false). intros. elim H2; intros.
	rewrite H3 in H1. rewrite H3. inversion H1. cut (a0 = ladj). intro. rewrite H4.
	trivial. exact (umpl_conv_1_inj a0 ladj H5). rewrite H3 in H1. inversion H1.
	exact (bool_is_true_or_false (Peqb p0 p2)). intros. simpl in H1. 
	inversion H1. intros. inversion H0. intros. induction  a1 as [| p1]. simpl in |- *. simpl in H0.
	inversion H0. induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]. inversion H0. simpl in |- *. simpl in H0.
	cut (Peqb p0 p1 = true \/ Peqb p0 p1 = false). intro. elim H1; intros.
	rewrite H2. rewrite H2 in H0. inversion H0. cut (a0 = ladj). intro. rewrite H3.
	trivial. exact (umpl_conv_1_inj a0 ladj H4). rewrite H2 in H0.
	inversion H0. exact (bool_is_true_or_false (Peqb p0 p1)).
	inversion H0. intros. induction  a1 as [| p0]. inversion H. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. inversion H.
	inversion H. simpl in H. inversion H. cut (a0 = ladj). intro. rewrite H0.
	trivial. exact (umpl_conv_1_inj a0 ladj H1). intro. intro. intro. intro.
	simple induction a. simpl in |- *. intros. exact (H N0 ladj H1). simple induction p. intros.
	simpl in |- *. simpl in H2. exact (H0 (Npos p0) ladj H2). intros. simpl in |- *. simpl in H2.
	exact (H (Npos p0) ladj H2). intros. simpl in |- *. simpl in H1. 
	exact (H0 N0 ladj H1).
Qed.

Lemma u_conv_1_invar_3 :
 forall (s : state) (c : ad) (p : prec_list),
 MapGet prec_list (umpl_conv_1 s) c = Some (upl_conv_1 p) ->
 MapGet prec_list s c = Some p.
Proof.
	simple induction s. simpl in |- *. intros. inversion H. simple induction a. intro. simple induction c.
	simpl in |- *. intros; inversion H. cut (a0 = p). intro. rewrite H0. trivial.
	exact (upl_conv_1_inj a0 p H1). simpl in |- *. intros. inversion H. intro. intro.
	simple induction c. simpl in |- *. intros. inversion H. induction  p as [p Hrecp| p Hrecp| ]. simple induction p0. intros.
	simpl in |- *. simpl in H0. cut (Peqb p p1 = true \/ Peqb p p1 = false). intro.
	elim H1; intros. rewrite H2. rewrite H2 in H0. inversion H0. cut (a0 = p2). intro.
	rewrite H3. trivial. exact (upl_conv_1_inj a0 p2 H4). rewrite H2. 
	rewrite H2 in H0. inversion H0. exact (bool_is_true_or_false (Peqb p p1)).
	intros. inversion H0. intros. inversion H. simple induction p0. intros. inversion H0.
	intros. simpl in |- *. simpl in H0. cut (Peqb p p1 = true \/ Peqb p p1 = false).
	intro. elim H1; intros. rewrite H2 in H0. rewrite H2. inversion H0. cut (a0 = p2).
	intro. rewrite H3. trivial. exact (upl_conv_1_inj a0 p2 H4). rewrite H2 in H0.
	inversion H0. exact (bool_is_true_or_false (Peqb p p1)). intros. inversion H.
	intros. induction  p as [p Hrecp| p Hrecp| ]. inversion H. inversion H. simpl in H. inversion H. cut (a0 = p0).
	intro. rewrite H0. trivial. exact (upl_conv_1_inj a0 p0 H1). intro. intro. intro.
	intro. simple induction c. simpl in |- *. intros. exact (H N0 p H1). simple induction p. intros.
	simpl in |- *. simpl in H2. exact (H0 (Npos p0) p1 H2). intros. simpl in |- *. simpl in H2.
	exact (H (Npos p0) p1 H2). intros. simpl in |- *. simpl in H1. exact (H0 N0 p0 H1).
Qed.

Lemma u_conv_1_invar_4 :
 forall (d : preDTA) (a : ad) (ladj : state),
 MapGet state (udta_conv_1 d) (uad_conv_1 a) = Some ladj ->
 exists ladj0 : _, ladj = umpl_conv_1 ladj0.
Proof.
	simple induction d. simple induction a. intros. inversion H. simple induction p; intros. inversion H0.
	inversion H0. inversion H. simple induction a. intro. simple induction a1. intros. simpl in H.
	inversion H. split with a0. trivial. simpl in |- *. intros. inversion H. intro. intro.
	simple induction a1. simpl in |- *. intros. inversion H. induction  p as [p Hrecp| p Hrecp| ]. simple induction p0. intros. 
	simpl in H0. elim (bool_is_true_or_false (Peqb p p1)); intro; rewrite H1 in H0.
	inversion H0. split with a0. trivial. inversion H0. intros. inversion H0. intros.
	inversion H. simple induction p0. intros. inversion H0. intros. simpl in H0.
	elim (bool_is_true_or_false (Peqb p p1)); intros; rewrite H1 in H0. inversion H0.
	split with a0. trivial. inversion H0. intros. inversion H. simple induction p. intros.
	inversion H0. intros. inversion H0. intros. inversion H. split with a0. trivial.
	intro. intro. intro. intro. simple induction a. intros. simpl in H1. exact (H N0 ladj H1).
	simple induction p. intros. simpl in H2. exact (H0 (Npos p0) ladj H2). intros. simpl in H2.
	exact (H (Npos p0) ladj H2). intros. simpl in H1. exact (H0 N0 ladj H1).
Qed.

Lemma u_conv_1_invar_5 :
 forall (d : preDTA) (a : ad) (ladj : state),
 MapGet state (udta_conv_1 d) (uad_conv_1 a) = Some ladj ->
 exists ladj0 : _,
   ladj = umpl_conv_1 ladj0 /\ MapGet state d a = Some ladj0.
Proof.
	intros. cut (exists ladj0 : state, ladj = umpl_conv_1 ladj0).
	intros. elim H0. intros. split with x. split. assumption. rewrite H1 in H.
	exact (u_conv_1_invar_2 d a x H). exact (u_conv_1_invar_4 d a ladj H).
Qed.

Lemma u_conv_1_invar_6 :
 forall (s : state) (c : ad) (p : prec_list),
 MapGet prec_list (umpl_conv_1 s) c = Some p ->
 exists p0 : prec_list, p = upl_conv_1 p0.
Proof.
	simple induction s. simple induction c. intros. inversion H. simple induction p. intros.
	inversion H0. intros. inversion H0. intros. inversion H. simple induction a.
	intro. simple induction c. simpl in |- *. intros. inversion H. split with a0. trivial.
	simpl in |- *. intros. inversion H. intro. intro. simple induction c. simpl in |- *. intros.
	inversion H. induction  p as [p Hrecp| p Hrecp| ]. simple induction p0. intros. simpl in H0.
	elim (bool_is_true_or_false (Peqb p p1)); intro; rewrite H1 in H0.
	inversion H0. split with a0. trivial. inversion H0. intros. inversion H0.
	intros. inversion H. simple induction p0. intros. inversion H0. intros. simpl in H0.
	elim (bool_is_true_or_false (Peqb p p1)); intro; rewrite H1 in H0.
	inversion H0. split with a0. trivial. inversion H0. simpl in |- *. intros. inversion H.
	simple induction p. intros. inversion H0. intros. inversion H0. intros. simpl in H.
	inversion H. split with a0. trivial. intro. intro. intro. intro. simple induction c.
	simpl in |- *. intros. exact (H N0 p H1). simple induction p; intros. simpl in H2.
	exact (H0 (Npos p0) p1 H2). simpl in H2. exact (H (Npos p0) p1 H2).
	simpl in H1. exact (H0 N0 p0 H1).
Qed.

Lemma u_conv_1_invar_7 :
 forall (s : state) (c : ad) (p : prec_list),
 MapGet prec_list (umpl_conv_1 s) c = Some p ->
 exists p0 : prec_list,
   p = upl_conv_1 p0 /\ MapGet prec_list s c = Some p0.
Proof.
	intros. elim (u_conv_1_invar_6 s c p H). intros. split with x.
	intros. split. assumption. rewrite H0 in H. 
	exact (u_conv_1_invar_3 s c x H).
Qed.

Lemma u_conv_1_invar_8 :
 forall (p0 : preDTA) (a0 : ad) (s0 : state),
 MapGet state (udta_conv_1 p0) a0 = Some s0 ->
 exists a1 : ad, a0 = uad_conv_1 a1.
Proof.
	simple induction p0. intros. simpl in H. induction  a0 as [| p]. inversion H.
	induction  p as [p Hrecp| p Hrecp| ]; inversion H. unfold udta_conv_1 in |- *. 
	unfold udta_conv_1_aux in |- *. intro. intro. simple induction a1. intros.
	simpl in H. inversion H. simple induction p. intros.
	split with (Npos p1). simpl in |- *. trivial. intros. simpl in H0.
	inversion H0. intros. simpl in H. split with N0. simpl in |- *.
	trivial.  intro. intro. intro. intro. simple induction a0.
	simpl in |- *. intros. inversion H1. simple induction p. intros.
	split with (Npos p1). simpl in |- *. trivial. intros. simpl in H2.
	inversion H2. intros. split with N0. simpl in |- *. trivial.
Qed.

(* invariant de reconnaissance de conv_1 *)

Definition u_conv_rec_1 (p : preDTA) (a : ad) (t : term)
  (pr : reconnaissance p a t) :=
  reconnaissance (udta_conv_1 p) (uad_conv_1 a) t.

Definition u_conv_str_1 (p : preDTA) (s : state) (t : term)
  (pr : state_reconnait p s t) :=
  state_reconnait (udta_conv_1 p) (umpl_conv_1 s) t.

Definition u_conv_lr_1 (p : preDTA) (p0 : prec_list) 
  (t : term_list) (pr : liste_reconnait p p0 t) :=
  liste_reconnait (udta_conv_1 p) (upl_conv_1 p0) t.

Lemma u_conv1_0 :
 forall (d : preDTA) (a : ad) (t : term) (ladj : state)
   (e : MapGet state d a = Some ladj) (s : state_reconnait d ladj t),
 u_conv_str_1 d ladj t s -> u_conv_rec_1 d a t (rec_dta d a t ladj e s).
Proof.
	intros. unfold u_conv_rec_1 in |- *. unfold u_conv_str_1 in H.
	cut
  (MapGet state (udta_conv_1 d) (uad_conv_1 a) =
   Some (umpl_conv_1 ladj)). intros.
	exact (rec_dta (udta_conv_1 d) (uad_conv_1 a) t (umpl_conv_1 ladj) H0 H).
	exact (u_conv_1_invar_0 d a ladj e).
Qed.

Lemma u_conv1_1 :
 forall (d : preDTA) (s : state) (c : ad) (tl : term_list) 
   (l : prec_list) (e : MapGet prec_list s c = Some l)
   (l0 : liste_reconnait d l tl),
 u_conv_lr_1 d l tl l0 ->
 u_conv_str_1 d s (app c tl) (rec_st d s c tl l e l0).
Proof.
	intros. unfold u_conv_lr_1 in H. unfold u_conv_str_1 in |- *.
	cut (MapGet prec_list (umpl_conv_1 s) c = Some (upl_conv_1 l)). intros.
	exact (rec_st (udta_conv_1 d) (umpl_conv_1 s) c tl (upl_conv_1 l) H0 H).
	exact (u_conv_1_invar_1 s c l e).
Qed.

Lemma u_conv1_2 :
 forall d : preDTA, u_conv_lr_1 d prec_empty tnil (rec_empty d).
Proof.
	intros. unfold u_conv_lr_1 in |- *. simpl in |- *.
	exact (rec_empty (udta_conv_1 d)).
Qed.

Lemma u_conv1_3 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list) (r : reconnaissance d a hd),
 u_conv_rec_1 d a hd r ->
 forall l : liste_reconnait d la tl,
 u_conv_lr_1 d la tl l ->
 u_conv_lr_1 d (prec_cons a la ls) (tcons hd tl)
   (rec_consi d a la ls hd tl r l).
Proof.
	intros. unfold u_conv_lr_1 in |- *. unfold u_conv_lr_1 in H0.
	unfold u_conv_rec_1 in H. simpl in |- *.
	exact
  (rec_consi (udta_conv_1 d) (uad_conv_1 a) (upl_conv_1 la) 
     (upl_conv_1 ls) hd tl H H0).
Qed.

Lemma u_conv1_4 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list) (l : liste_reconnait d ls (tcons hd tl)),
 u_conv_lr_1 d ls (tcons hd tl) l ->
 u_conv_lr_1 d (prec_cons a la ls) (tcons hd tl)
   (rec_consn d a la ls hd tl l).
Proof.
	intros. unfold u_conv_lr_1 in |- *. unfold u_conv_lr_1 in H. simpl in |- *.
	exact
  (rec_consn (udta_conv_1 d) (uad_conv_1 a) (upl_conv_1 la) 
     (upl_conv_1 ls) hd tl H).
Qed.

Lemma u_conv1_5 :
 forall (p : preDTA) (a : ad) (t : term) (r : reconnaissance p a t),
 u_conv_rec_1 p a t r.
Proof.
	exact
  (mreconnaissance_ind u_conv_rec_1 u_conv_str_1 u_conv_lr_1 u_conv1_0
     u_conv1_1 u_conv1_2 u_conv1_3 u_conv1_4).
Qed.

Lemma u_conv1 :
 forall (p : preDTA) (a : ad) (t : term),
 reconnaissance p a t -> reconnaissance (udta_conv_1 p) (uad_conv_1 a) t.
Proof.
	intros. exact (u_conv1_5 p a t H).
Qed.

(* invariant de reconnaissance sur conv_1 : sens reciproque *)

Definition u_conv_rec_1_r (p0 : preDTA) (a0 : ad) (t : term)
  (pr0 : reconnaissance p0 a0 t) :=
  forall (p : preDTA) (a : ad),
  p0 = udta_conv_1 p -> a0 = uad_conv_1 a -> reconnaissance p a t.

Definition u_conv_str_1_r (p0 : preDTA) (s0 : state) 
  (t : term) (pr : state_reconnait p0 s0 t) :=
  forall (p : preDTA) (s : state),
  p0 = udta_conv_1 p -> s0 = umpl_conv_1 s -> state_reconnait p s t.

Definition u_conv_lr_1_r (p0 : preDTA) (pl0 : prec_list) 
  (t : term_list) (pr : liste_reconnait p0 pl0 t) :=
  forall (p : preDTA) (pl : prec_list),
  p0 = udta_conv_1 p -> pl0 = upl_conv_1 pl -> liste_reconnait p pl t.

Lemma u_conv1_0r :
 forall (d : preDTA) (a : ad) (t : term) (ladj : state)
   (e : MapGet state d a = Some ladj) (s : state_reconnait d ladj t),
 u_conv_str_1_r d ladj t s -> u_conv_rec_1_r d a t (rec_dta d a t ladj e s).
Proof.
	intros. unfold u_conv_str_1_r in H. unfold u_conv_rec_1_r in |- *.
	intros. rewrite H0 in e. rewrite H1 in e. 
	elim (u_conv_1_invar_5 p a0 ladj e). intros. elim H2. intros.
	apply (rec_dta p a0 t x H4). apply (H p x). exact H0. exact H3.
Qed.

Lemma u_conv1_1r :
 forall (d : preDTA) (s : state) (c : ad) (tl : term_list) 
   (l : prec_list) (e : MapGet prec_list s c = Some l)
   (l0 : liste_reconnait d l tl),
 u_conv_lr_1_r d l tl l0 ->
 u_conv_str_1_r d s (app c tl) (rec_st d s c tl l e l0).
Proof.
	intros. unfold u_conv_lr_1_r in H. unfold u_conv_str_1_r in |- *. intros.
	rewrite H1 in e. elim (u_conv_1_invar_7 s0 c l e). intros. elim H2.
	intros. apply (rec_st p s0 c tl x H4). exact (H p x H0 H3).
Qed.

Lemma u_conv1_2r :
 forall d : preDTA, u_conv_lr_1_r d prec_empty tnil (rec_empty d).
Proof.
	intros. unfold u_conv_lr_1_r in |- *. intros. cut (pl = prec_empty). intros.
	rewrite H1. exact (rec_empty p). cut (upl_conv_1 prec_empty = prec_empty).
	intros. rewrite <- H1 in H0. symmetry  in |- *. 
	exact (upl_conv_1_inj prec_empty pl H0). simpl in |- *. trivial.
Qed.

Lemma u_conv1_3r :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list) (r : reconnaissance d a hd),
 u_conv_rec_1_r d a hd r ->
 forall l : liste_reconnait d la tl,
 u_conv_lr_1_r d la tl l ->
 u_conv_lr_1_r d (prec_cons a la ls) (tcons hd tl)
   (rec_consi d a la ls hd tl r l).
Proof.
	intros. unfold u_conv_lr_1_r in |- *. unfold u_conv_rec_1_r in H.
	unfold u_conv_lr_1_r in H0. intros. cut (upl_conv_1 pl = prec_cons a la ls).
	intro. cut
  (exists a0 : ad,
     (exists la0 : prec_list,
        (exists ls0 : prec_list,
           pl = prec_cons a0 la0 ls0 /\
           a = uad_conv_1 a0 /\ la = upl_conv_1 la0 /\ ls = upl_conv_1 ls0))).
	intro. elim H4. intros. elim H5. intros. elim H6. intros. elim H7.
	intros. elim H9. intros. elim H11. intros. rewrite H8. 	
	apply (rec_consi p x x0 x1 hd tl). apply (H p x). exact H1. trivial.
	exact (H0 p x0 H1 H12). exact (upl_conv_1_img_0 pl a la ls H3).
	symmetry  in |- *. trivial.
Qed.

Lemma u_conv1_4r :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list) (l : liste_reconnait d ls (tcons hd tl)),
 u_conv_lr_1_r d ls (tcons hd tl) l ->
 u_conv_lr_1_r d (prec_cons a la ls) (tcons hd tl)
   (rec_consn d a la ls hd tl l).
Proof.
	intros. unfold u_conv_lr_1_r in H. unfold u_conv_lr_1_r in |- *. intros.
	cut (upl_conv_1 pl = prec_cons a la ls). cut
  (exists a0 : ad,
     (exists la0 : prec_list,
        (exists ls0 : prec_list,
           pl = prec_cons a0 la0 ls0 /\
           a = uad_conv_1 a0 /\ la = upl_conv_1 la0 /\ ls = upl_conv_1 ls0))).
	intros. elim H2. intros. elim H4. intros. elim H5. intros. elim H6.
	intros. elim H8. intros. elim H10. intros. rewrite H7.
	exact (rec_consn p x x0 x1 hd tl (H p x1 H0 H12)).
	cut (upl_conv_1 pl = prec_cons a la ls). intro.
	exact (upl_conv_1_img_0 pl a la ls H2). symmetry  in |- *. trivial. symmetry  in |- *.
	trivial.
Qed.

Lemma u_conv1_5r :
 forall (p : preDTA) (a : ad) (t : term) (r : reconnaissance p a t),
 u_conv_rec_1_r p a t r.
Proof.
	exact
  (mreconnaissance_ind u_conv_rec_1_r u_conv_str_1_r u_conv_lr_1_r u_conv1_0r
     u_conv1_1r u_conv1_2r u_conv1_3r u_conv1_4r).
Qed.

Lemma u_conv1_r :
 forall (p : preDTA) (a : ad) (t : term),
 reconnaissance (udta_conv_1 p) (uad_conv_1 a) t -> reconnaissance p a t.
Proof.
	intros. apply (u_conv1_5r (udta_conv_1 p) (uad_conv_1 a) t H p a). trivial. trivial.
Qed.

(* udta_conv_0 et udta_conv_1 ont des images disjointes *)

Lemma u_conv_disj :
 forall (p0 p1 : preDTA) (a0 a1 : ad) (s0 s1 : state),
 MapGet state (udta_conv_0 p0) a0 = Some s0 ->
 MapGet state (udta_conv_1 p1) a1 = Some s1 -> a0 <> a1.
Proof.
	intros. intro. cut (exists a2 : _, a0 = uad_conv_0 a2).
	cut (exists a3 : _, a1 = uad_conv_1 a3). intros. elim H2.
	elim H3. intros. rewrite <- H1 in H5. rewrite H4 in H5.
	exact (adcnv_ok x x0 H5). exact (u_conv_1_invar_8 p1 a1 s1 H0).
	exact (u_conv_0_invar_8 p0 a0 s0 H).
Qed.

(* définition de l'union des supports de deux automates *)

Definition u_merge (p0 p1 : preDTA) : preDTA :=
  MapMerge state (udta_conv_0 p0) (udta_conv_1 p1).

(* invariants des MapGet au travers de u_merge *)

Lemma u_merge_0 :
 forall (p0 p1 : preDTA) (a : ad) (s : state),
 MapGet state (udta_conv_0 p0) a = Some s ->
 MapGet state (u_merge p0 p1) a = Some s.
Proof.
	intros. unfold u_merge in |- *. cut
  (eqm state
     (MapGet state (MapMerge state (udta_conv_0 p0) (udta_conv_1 p1)))
     (fun a0 : ad =>
      match MapGet state (udta_conv_1 p1) a0 with
      | None => MapGet state (udta_conv_0 p0) a0
      | Some y' => Some y'
      end)). intros. unfold eqm in H0.
	cut
  (MapGet state (MapMerge state (udta_conv_0 p0) (udta_conv_1 p1)) a =
   match MapGet state (udta_conv_1 p1) a with
   | None => MapGet state (udta_conv_0 p0) a
   | Some y' => Some y'
   end).
	intros. rewrite H1. cut
  (MapGet state (udta_conv_1 p1) a = None \/
   (exists y : state, MapGet state (udta_conv_1 p1) a = Some y)).
	intro. elim H2; intros. rewrite H3. rewrite H. trivial. elim H3.
	intros. rewrite H4. elim (u_conv_disj p0 p1 a a s x H H4 (refl_equal a)).
	elim (MapGet state (udta_conv_1 p1) a). Focus 2. left. trivial. right. split with a0.
	trivial. exact (H0 a).
	exact (MapMerge_semantics state (udta_conv_0 p0) (udta_conv_1 p1)).
Qed.

Lemma u_merge_1 :
 forall (p0 p1 : preDTA) (a : ad) (s : state),
 MapGet state (udta_conv_1 p1) a = Some s ->
 MapGet state (u_merge p0 p1) a = Some s.
Proof.
	intros. unfold u_merge in |- *. cut
  (eqm state
     (MapGet state (MapMerge state (udta_conv_0 p0) (udta_conv_1 p1)))
     (fun a0 : ad =>
      match MapGet state (udta_conv_1 p1) a0 with
      | None => MapGet state (udta_conv_0 p0) a0
      | Some y' => Some y'
      end)).
	intros. unfold eqm in H0.
	cut
  (MapGet state (MapMerge state (udta_conv_0 p0) (udta_conv_1 p1)) a =
   match MapGet state (udta_conv_1 p1) a with
   | None => MapGet state (udta_conv_0 p0) a
   | Some y' => Some y'
   end).
	intros. rewrite H1. rewrite H. trivial. exact (H0 a).
	exact (MapMerge_semantics state (udta_conv_0 p0) (udta_conv_1 p1)).
Qed.

Lemma u_merge_0r :
 forall (p0 p1 : preDTA) (a : ad) (s : state),
 MapGet state (u_merge p0 p1) a = Some s ->
 forall b : ad,
 a = uad_conv_0 b -> MapGet state (udta_conv_0 p0) a = Some s.
Proof.
	intros. cut
  (eqm state
     (MapGet state (MapMerge state (udta_conv_0 p0) (udta_conv_1 p1)))
     (fun a0 : ad =>
      match MapGet state (udta_conv_1 p1) a0 with
      | None => MapGet state (udta_conv_0 p0) a0
      | Some y' => Some y'
      end)). intro. unfold eqm in H1.
	unfold u_merge in H. rewrite H0. rewrite H0 in H.
	cut
  (MapGet state (MapMerge state (udta_conv_0 p0) (udta_conv_1 p1))
     (uad_conv_0 b) =
   match MapGet state (udta_conv_1 p1) (uad_conv_0 b) with
   | None => MapGet state (udta_conv_0 p0) (uad_conv_0 b)
   | Some y' => Some y'
   end). intro. rewrite H2 in H.
	cut
  (MapGet state (udta_conv_1 p1) (uad_conv_0 b) = None \/
   (exists s : state,
      MapGet state (udta_conv_1 p1) (uad_conv_0 b) = Some s)).
	intros. elim H3; intros. rewrite H4 in H. assumption. elim H4. intros.
	elim (u_conv_1_invar_8 p1 (uad_conv_0 b) x). intros. elim (adcnv_ok b x0 H6).
	assumption. generalize (MapGet state (udta_conv_1 p1) (uad_conv_0 b)).
	simple induction o. Focus 2. left. trivial. intro. right. split with a0. trivial.
	exact (H1 (uad_conv_0 b)). 
	exact (MapMerge_semantics state (udta_conv_0 p0) (udta_conv_1 p1)).
Qed.

Lemma u_merge_1r :
 forall (p0 p1 : preDTA) (a : ad) (s : state),
 MapGet state (u_merge p0 p1) a = Some s ->
 forall b : ad,
 a = uad_conv_1 b -> MapGet state (udta_conv_1 p1) a = Some s.
Proof.
	intros. cut
  (eqm state
     (MapGet state (MapMerge state (udta_conv_0 p0) (udta_conv_1 p1)))
     (fun a0 : ad =>
      match MapGet state (udta_conv_1 p1) a0 with
      | None => MapGet state (udta_conv_0 p0) a0
      | Some y' => Some y'
      end)). intro. unfold eqm in H1.
	unfold u_merge in H. rewrite H0. rewrite H0 in H.
	cut
  (MapGet state (MapMerge state (udta_conv_0 p0) (udta_conv_1 p1))
     (uad_conv_1 b) =
   match MapGet state (udta_conv_1 p1) (uad_conv_1 b) with
   | None => MapGet state (udta_conv_0 p0) (uad_conv_1 b)
   | Some y' => Some y'
   end). intros. rewrite H2 in H.
	cut
  (MapGet state (udta_conv_1 p1) (uad_conv_1 b) = None \/
   (exists s : _, MapGet state (udta_conv_1 p1) (uad_conv_1 b) = Some s)). intro.
	elim H3; intros. rewrite H4 in H. elim (u_conv_0_invar_8 p0 (uad_conv_1 b) s H).
	intros. elim (adcnv_ok x b (sym_eq H5)).
	elim H4. intros. rewrite H5 in H. inversion H. rewrite <- H7. exact H5.
	generalize (MapGet state (udta_conv_1 p1) (uad_conv_1 b)). simple induction o. Focus 2.
	left. trivial. intros. right. split with a0. trivial. exact (H1 (uad_conv_1 b)).
	exact (MapMerge_semantics state (udta_conv_0 p0) (udta_conv_1 p1)).
Qed.

(* invariant de reconnaissance pour conv_0 au travers de u_merge *)

Definition u_merge_inv_0_dta (p0 : preDTA) (a : ad) 
  (t : term) (pr : reconnaissance p0 a t) :=
  forall p1 : preDTA, reconnaissance (u_merge p0 p1) (uad_conv_0 a) t.

Definition u_merge_inv_0_st (p0 : preDTA) (s : state) 
  (t : term) (pr : state_reconnait p0 s t) :=
  forall p1 : preDTA, state_reconnait (u_merge p0 p1) (umpl_conv_0 s) t.

Definition u_merge_inv_0_lst (p0 : preDTA) (pl : prec_list) 
  (lt : term_list) (pr : liste_reconnait p0 pl lt) :=
  forall p1 : preDTA, liste_reconnait (u_merge p0 p1) (upl_conv_0 pl) lt.

Lemma u_merge_2_0 :
 forall (d : preDTA) (a : ad) (t : term) (ladj : state)
   (e : MapGet state d a = Some ladj) (s : state_reconnait d ladj t),
 u_merge_inv_0_st d ladj t s ->
 u_merge_inv_0_dta d a t (rec_dta d a t ladj e s).
Proof.
	intros. unfold u_merge_inv_0_st in H. unfold u_merge_inv_0_dta in |- *.
	intro. apply (rec_dta (u_merge d p1) (uad_conv_0 a) t (umpl_conv_0 ladj)).
	apply (u_merge_0 d p1 (uad_conv_0 a) (umpl_conv_0 ladj)).
	exact (u_conv_0_invar_0 d a ladj e). exact (H p1).
Qed.

Lemma u_merge_2_1 :
 forall (d : preDTA) (s : state) (c : ad) (tl : term_list) 
   (l : prec_list) (e : MapGet prec_list s c = Some l)
   (l0 : liste_reconnait d l tl),
 u_merge_inv_0_lst d l tl l0 ->
 u_merge_inv_0_st d s (app c tl) (rec_st d s c tl l e l0).
Proof.
	intros. unfold u_merge_inv_0_lst in H. unfold u_merge_inv_0_st in |- *.
	intros. apply (rec_st (u_merge d p1) (umpl_conv_0 s) c tl (upl_conv_0 l)).
	apply (u_conv_0_invar_1 s c l). assumption. exact (H p1).
Qed.

Lemma u_merge_2_2 :
 forall d : preDTA, u_merge_inv_0_lst d prec_empty tnil (rec_empty d).
Proof.
	unfold u_merge_inv_0_lst in |- *. simpl in |- *. intros. exact (rec_empty (u_merge d p1)).
Qed.

Lemma u_merge_2_3 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list) (r : reconnaissance d a hd),
 u_merge_inv_0_dta d a hd r ->
 forall l : liste_reconnait d la tl,
 u_merge_inv_0_lst d la tl l ->
 u_merge_inv_0_lst d (prec_cons a la ls) (tcons hd tl)
   (rec_consi d a la ls hd tl r l).
Proof.
	intros. unfold u_merge_inv_0_lst in H0. unfold u_merge_inv_0_lst in |- *.
	unfold u_merge_inv_0_dta in |- *. simpl in |- *. unfold u_merge_inv_0_dta in H.
	intros. apply
  (rec_consi (u_merge d p1) (uad_conv_0 a) (upl_conv_0 la) 
     (upl_conv_0 ls) hd tl). exact (H p1). exact (H0 p1).
Qed.

Lemma u_merge_2_4 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list) (l : liste_reconnait d ls (tcons hd tl)),
 u_merge_inv_0_lst d ls (tcons hd tl) l ->
 u_merge_inv_0_lst d (prec_cons a la ls) (tcons hd tl)
   (rec_consn d a la ls hd tl l).
Proof.
	intros. unfold u_merge_inv_0_lst in |- *. unfold u_merge_inv_0_lst in H.
	simpl in |- *. intros. exact
  (rec_consn (u_merge d p1) (uad_conv_0 a) (upl_conv_0 la) 
     (upl_conv_0 ls) hd tl (H p1)).
Qed.

Lemma u_merge_2_5 :
 forall (p : preDTA) (a : ad) (t : term) (r : reconnaissance p a t),
 u_merge_inv_0_dta p a t r.
Proof.
	exact
  (mreconnaissance_ind u_merge_inv_0_dta u_merge_inv_0_st u_merge_inv_0_lst
     u_merge_2_0 u_merge_2_1 u_merge_2_2 u_merge_2_3 u_merge_2_4).
Qed.

Lemma u_merge_2 :
 forall (p0 p1 : preDTA) (a : ad) (t : term),
 reconnaissance p0 a t -> reconnaissance (u_merge p0 p1) (uad_conv_0 a) t.
Proof.
	intros. exact (u_merge_2_5 p0 a t H p1).
Qed.

(* invariant de reconnaissance pour conv_1 au travers de u_merge *)

Definition u_merge_inv_1_dta (p1 : preDTA) (a : ad) 
  (t : term) (pr : reconnaissance p1 a t) :=
  forall p0 : preDTA, reconnaissance (u_merge p0 p1) (uad_conv_1 a) t.

Definition u_merge_inv_1_st (p1 : preDTA) (s : state) 
  (t : term) (pr : state_reconnait p1 s t) :=
  forall p0 : preDTA, state_reconnait (u_merge p0 p1) (umpl_conv_1 s) t.

Definition u_merge_inv_1_lst (p1 : preDTA) (pl : prec_list) 
  (lt : term_list) (pr : liste_reconnait p1 pl lt) :=
  forall p0 : preDTA, liste_reconnait (u_merge p0 p1) (upl_conv_1 pl) lt.

Lemma u_merge_3_0 :
 forall (d : preDTA) (a : ad) (t : term) (ladj : state)
   (e : MapGet state d a = Some ladj) (s : state_reconnait d ladj t),
 u_merge_inv_1_st d ladj t s ->
 u_merge_inv_1_dta d a t (rec_dta d a t ladj e s).
Proof.
	intros. unfold u_merge_inv_1_dta in |- *. unfold u_merge_inv_1_st in H.
	intros. apply (rec_dta (u_merge p0 d) (uad_conv_1 a) t (umpl_conv_1 ladj)).
	apply (u_merge_1 p0 d (uad_conv_1 a) (umpl_conv_1 ladj)).
	exact (u_conv_1_invar_0 d a ladj e). exact (H p0).
Qed.

Lemma u_merge_3_1 :
 forall (d : preDTA) (s : state) (c : ad) (tl : term_list) 
   (l : prec_list) (e : MapGet prec_list s c = Some l)
   (l0 : liste_reconnait d l tl),
 u_merge_inv_1_lst d l tl l0 ->
 u_merge_inv_1_st d s (app c tl) (rec_st d s c tl l e l0).
Proof.
	intros; unfold u_merge_inv_1_st in |- *. unfold u_merge_inv_1_lst in H.
	intros. apply (rec_st (u_merge p0 d) (umpl_conv_1 s) c tl (upl_conv_1 l)).
	exact (u_conv_1_invar_1 s c l e). exact (H p0).
Qed.

Lemma u_merge_3_2 :
 forall d : preDTA, u_merge_inv_1_lst d prec_empty tnil (rec_empty d).
Proof.
	intros. unfold u_merge_inv_1_lst in |- *. simpl in |- *. intros.
	exact (rec_empty (u_merge p0 d)).
Qed.

Lemma u_merge_3_3 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list) (r : reconnaissance d a hd),
 u_merge_inv_1_dta d a hd r ->
 forall l : liste_reconnait d la tl,
 u_merge_inv_1_lst d la tl l ->
 u_merge_inv_1_lst d (prec_cons a la ls) (tcons hd tl)
   (rec_consi d a la ls hd tl r l).
Proof.
	intros. unfold u_merge_inv_1_lst in |- *. unfold u_merge_inv_1_dta in H.
	unfold u_merge_inv_1_lst in H. intros. simpl in |- *. unfold u_merge_inv_1_lst in H0.
	exact
  (rec_consi (u_merge p0 d) (uad_conv_1 a) (upl_conv_1 la) 
     (upl_conv_1 ls) hd tl (H p0) (H0 p0)).
Qed.

Lemma u_merge_3_4 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list) (l : liste_reconnait d ls (tcons hd tl)),
 u_merge_inv_1_lst d ls (tcons hd tl) l ->
 u_merge_inv_1_lst d (prec_cons a la ls) (tcons hd tl)
   (rec_consn d a la ls hd tl l).
Proof.
	intros. unfold u_merge_inv_1_lst in H. unfold u_merge_inv_1_lst in |- *.
	simpl in |- *. intros. exact
  (rec_consn (u_merge p0 d) (uad_conv_1 a) (upl_conv_1 la) 
     (upl_conv_1 ls) hd tl (H p0)).
Qed.

Lemma u_merge_3_5 :
 forall (p : preDTA) (a : ad) (t : term) (r : reconnaissance p a t),
 u_merge_inv_1_dta p a t r.
Proof.
	exact
  (mreconnaissance_ind u_merge_inv_1_dta u_merge_inv_1_st u_merge_inv_1_lst
     u_merge_3_0 u_merge_3_1 u_merge_3_2 u_merge_3_3 u_merge_3_4).
Qed.

Lemma u_merge_3 :
 forall (p0 p1 : preDTA) (a : ad) (t : term),
 reconnaissance p1 a t -> reconnaissance (u_merge p0 p1) (uad_conv_1 a) t.
Proof.
	intros. exact (u_merge_3_5 p1 a t H p0).
Qed.

(* invariant pour u_merge : sens réciproque pour u_conv_0 *)

Definition u_merge_invr_0_dta (p : preDTA) (a : ad) 
  (t : term) (pr : reconnaissance p a t) :=
  forall p0 p1 : preDTA,
  p = u_merge p0 p1 ->
  forall a0 : ad, a = uad_conv_0 a0 -> reconnaissance (udta_conv_0 p0) a t.

Definition u_merge_invr_0_st (p : preDTA) (s : state) 
  (t : term) (pr : state_reconnait p s t) :=
  forall p0 p1 : preDTA,
  p = u_merge p0 p1 ->
  forall s0 : state,
  s = umpl_conv_0 s0 -> state_reconnait (udta_conv_0 p0) s t.

Definition u_merge_invr_0_lst (p : preDTA) (pl : prec_list) 
  (lt : term_list) (pr : liste_reconnait p pl lt) :=
  forall p0 p1 : preDTA,
  p = u_merge p0 p1 ->
  forall pl0 : prec_list,
  pl = upl_conv_0 pl0 -> liste_reconnait (udta_conv_0 p0) pl lt.

Lemma u_merge_4_0 :
 forall (d : preDTA) (a : ad) (t : term) (ladj : state)
   (e : MapGet state d a = Some ladj) (s : state_reconnait d ladj t),
 u_merge_invr_0_st d ladj t s ->
 u_merge_invr_0_dta d a t (rec_dta d a t ladj e s).
Proof.
	intros. unfold u_merge_invr_0_st in H. unfold u_merge_invr_0_dta in |- *.
	intros. rewrite H0 in e. apply (rec_dta (udta_conv_0 p0) a t ladj (u_merge_0r p0 p1 a ladj e a0 H1)). cut
  (exists ladj0 : state,
     ladj = umpl_conv_0 ladj0 /\ MapGet state p0 a0 = Some ladj0).
	intros. elim H2. intros. elim H3. intros. exact (H p0 p1 H0 x H4).
	apply (u_conv_0_invar_5 p0 a0 ladj). rewrite <- H1.
	exact (u_merge_0r p0 p1 a ladj e a0 H1).
Qed.

Lemma u_merge_4_1 :
 forall (d : preDTA) (s : state) (c : ad) (tl : term_list) 
   (l : prec_list) (e : MapGet prec_list s c = Some l)
   (l0 : liste_reconnait d l tl),
 u_merge_invr_0_lst d l tl l0 ->
 u_merge_invr_0_st d s (app c tl) (rec_st d s c tl l e l0).
Proof.
	intros. unfold u_merge_invr_0_st in |- *. intros. unfold u_merge_invr_0_lst in H.
	apply (rec_st (udta_conv_0 p0) s c tl l e). rewrite H1 in e.
	elim (u_conv_0_invar_7 s0 c l e). intros. elim H2. intros.
	exact (H p0 p1 H0 x H3).
Qed.

Lemma u_merge_4_2 :
 forall d : preDTA, u_merge_invr_0_lst d prec_empty tnil (rec_empty d).
Proof.
	intros. unfold u_merge_invr_0_lst in |- *. intros. exact (rec_empty (udta_conv_0 p0)).
Qed.

Lemma u_merge_4_3 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list) (r : reconnaissance d a hd),
 u_merge_invr_0_dta d a hd r ->
 forall l : liste_reconnait d la tl,
 u_merge_invr_0_lst d la tl l ->
 u_merge_invr_0_lst d (prec_cons a la ls) (tcons hd tl)
   (rec_consi d a la ls hd tl r l).
Proof.
	intros. unfold u_merge_invr_0_dta in H. unfold u_merge_invr_0_lst in H0.
	unfold u_merge_invr_0_lst in |- *. intros. elim (upl_conv_0_img_0 pl0 a la ls (sym_eq H2)). intros. 
	elim H3. intros. elim H4. intros. elim H5. intros. elim H7. intros. elim H9. 
	intros. exact
  (rec_consi (udta_conv_0 p0) a la ls hd tl (H p0 p1 H1 x H8)
     (H0 p0 p1 H1 x0 H10)).
Qed.

Lemma u_merge_4_4 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list) (l : liste_reconnait d ls (tcons hd tl)),
 u_merge_invr_0_lst d ls (tcons hd tl) l ->
 u_merge_invr_0_lst d (prec_cons a la ls) (tcons hd tl)
   (rec_consn d a la ls hd tl l).
Proof.
	intros; unfold u_merge_invr_0_lst in H. unfold u_merge_invr_0_lst in |- *. intros.
	elim (upl_conv_0_img_0 pl0 a la ls (sym_eq H1)). intros. elim H2.
	intros. elim H3. intros. elim H4. intros. elim H6. intros. elim H8. intros.
	exact (rec_consn (udta_conv_0 p0) a la ls hd tl (H p0 p1 H0 x1 H10)).
Qed.

Lemma u_merge_4_5 :
 forall (p : preDTA) (a : ad) (t : term) (r : reconnaissance p a t),
 u_merge_invr_0_dta p a t r.
Proof. 
	exact
  (mreconnaissance_ind u_merge_invr_0_dta u_merge_invr_0_st
     u_merge_invr_0_lst u_merge_4_0 u_merge_4_1 u_merge_4_2 u_merge_4_3
     u_merge_4_4).
Qed.

Lemma u_merge_4 :
 forall (p0 p1 : preDTA) (a : ad) (t : term),
 reconnaissance (u_merge p0 p1) (uad_conv_0 a) t -> reconnaissance p0 a t.
Proof.
	intros. apply (u_conv0_r p0 a t). exact
  (u_merge_4_5 (u_merge p0 p1) (uad_conv_0 a) t H p0 p1
     (refl_equal (u_merge p0 p1)) a (refl_equal (uad_conv_0 a))).
Qed.

(* invariant pour u_merge : sens réciproque pour u_conv_1 *)

Definition u_merge_invr_1_dta (p : preDTA) (a : ad) 
  (t : term) (pr : reconnaissance p a t) :=
  forall p0 p1 : preDTA,
  p = u_merge p0 p1 ->
  forall a0 : ad, a = uad_conv_1 a0 -> reconnaissance (udta_conv_1 p1) a t.

Definition u_merge_invr_1_st (p : preDTA) (s : state) 
  (t : term) (pr : state_reconnait p s t) :=
  forall p0 p1 : preDTA,
  p = u_merge p0 p1 ->
  forall s0 : state,
  s = umpl_conv_1 s0 -> state_reconnait (udta_conv_1 p1) s t.

Definition u_merge_invr_1_lst (p : preDTA) (pl : prec_list) 
  (lt : term_list) (pr : liste_reconnait p pl lt) :=
  forall p0 p1 : preDTA,
  p = u_merge p0 p1 ->
  forall pl0 : prec_list,
  pl = upl_conv_1 pl0 -> liste_reconnait (udta_conv_1 p1) pl lt.

Lemma u_merge_5_0 :
 forall (d : preDTA) (a : ad) (t : term) (ladj : state)
   (e : MapGet state d a = Some ladj) (s : state_reconnait d ladj t),
 u_merge_invr_1_st d ladj t s ->
 u_merge_invr_1_dta d a t (rec_dta d a t ladj e s).
Proof.
	intros. unfold u_merge_invr_1_st in H. unfold u_merge_invr_1_dta in |- *.
	intros. rewrite H0 in e. apply (rec_dta (udta_conv_1 p1) a t ladj (u_merge_1r p0 p1 a ladj e a0 H1)). cut
  (exists ladj0 : state,
     ladj = umpl_conv_1 ladj0 /\ MapGet state p1 a0 = Some ladj0).
	intros. elim H2. intros. elim H3. intros. exact (H p0 p1 H0 x H4).
	apply (u_conv_1_invar_5 p1 a0 ladj). rewrite <- H1.
	exact (u_merge_1r p0 p1 a ladj e a0 H1).
Qed.

Lemma u_merge_5_1 :
 forall (d : preDTA) (s : state) (c : ad) (tl : term_list) 
   (l : prec_list) (e : MapGet prec_list s c = Some l)
   (l0 : liste_reconnait d l tl),
 u_merge_invr_1_lst d l tl l0 ->
 u_merge_invr_1_st d s (app c tl) (rec_st d s c tl l e l0).
Proof.
	intros. unfold u_merge_invr_1_st in |- *. intros. unfold u_merge_invr_1_lst in H.
	apply (rec_st (udta_conv_1 p1) s c tl l e). rewrite H1 in e.
	elim (u_conv_1_invar_7 s0 c l e). intros. elim H2. intros. 
	exact (H p0 p1 H0 x H3).
Qed.

Lemma u_merge_5_2 :
 forall d : preDTA, u_merge_invr_1_lst d prec_empty tnil (rec_empty d).
Proof.
	unfold u_merge_invr_1_lst in |- *. intros. exact (rec_empty (udta_conv_1 p1)).
Qed.

Lemma u_merge_5_3 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list) (r : reconnaissance d a hd),
 u_merge_invr_1_dta d a hd r ->
 forall l : liste_reconnait d la tl,
 u_merge_invr_1_lst d la tl l ->
 u_merge_invr_1_lst d (prec_cons a la ls) (tcons hd tl)
   (rec_consi d a la ls hd tl r l).
Proof.
	intros. unfold u_merge_invr_1_dta in H. unfold u_merge_invr_1_lst in H0.
	unfold u_merge_invr_1_lst in |- *. intros. elim (upl_conv_1_img_0 pl0 a la ls (sym_eq H2)). intros.
	elim H3. intros. elim H4. intros; elim H5. intros. elim H7. intros.
	elim H9. intros. apply (rec_consi (udta_conv_1 p1) a la ls hd tl).
	exact (H p0 p1 H1 x H8). exact (H0 p0 p1 H1 x0 H10).
Qed.

Lemma u_merge_5_4 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list) (l : liste_reconnait d ls (tcons hd tl)),
 u_merge_invr_1_lst d ls (tcons hd tl) l ->
 u_merge_invr_1_lst d (prec_cons a la ls) (tcons hd tl)
   (rec_consn d a la ls hd tl l).
Proof.
	intros. unfold u_merge_invr_1_lst in H. unfold u_merge_invr_1_lst in |- *.
	intros. elim (upl_conv_1_img_0 pl0 a la ls (sym_eq H1)).
	intros. elim H2. intros. elim H3. intros. elim H4. intros. elim H6.
	intros. elim H8. intros. 
	exact (rec_consn (udta_conv_1 p1) a la ls hd tl (H p0 p1 H0 x1 H10)).
Qed.

Lemma u_merge_5_5 :
 forall (p : preDTA) (a : ad) (t : term) (r : reconnaissance p a t),
 u_merge_invr_1_dta p a t r.
Proof. 
	exact
  (mreconnaissance_ind u_merge_invr_1_dta u_merge_invr_1_st
     u_merge_invr_1_lst u_merge_5_0 u_merge_5_1 u_merge_5_2 u_merge_5_3
     u_merge_5_4).
Qed.

Lemma u_merge_5 :
 forall (p0 p1 : preDTA) (a : ad) (t : term),
 reconnaissance (u_merge p0 p1) (uad_conv_1 a) t -> reconnaissance p1 a t.
Proof.
	intros. apply (u_conv1_r p1 a t). exact
  (u_merge_5_5 (u_merge p0 p1) (uad_conv_1 a) t H p0 p1
     (refl_equal (u_merge p0 p1)) a (refl_equal (uad_conv_1 a))).
Qed.

(* union de deux états dans un meme preDTA *)

(* définition d'un état *)

Fixpoint union_pl (pl0 : prec_list) : prec_list -> prec_list :=
  fun pl1 : prec_list =>
  match pl0 with
  | prec_empty => pl1
  | prec_cons a pl00 pl01 => prec_cons a pl00 (union_pl pl01 pl1)
  end.

Fixpoint union_mpl_0 (c : ad) (pl : prec_list) (s : state) {struct s} :
 state :=
  match s with
  | M0 => M1 prec_list c pl
  | M1 c0 pl0 =>
      if Neqb c c0
      then M1 prec_list c (union_pl pl pl0)
      else MapMerge prec_list (M1 prec_list c pl) (M1 prec_list c0 pl0)
  | M2 s0 s1 =>
      match c with
      | N0 => M2 prec_list (union_mpl_0 N0 pl s0) s1
      | Npos p =>
          match p with
          | xH => M2 prec_list s0 (union_mpl_0 N0 pl s1)
          | xO p' => M2 prec_list (union_mpl_0 (Npos p') pl s0) s1
          | xI p' => M2 prec_list s0 (union_mpl_0 (Npos p') pl s1)
          end
      end
  end.

Fixpoint union_mpl (s0 : state) : state -> state :=
  fun s1 : state =>
  match s0, s1 with
  | M0, M0 => M0 prec_list
  | M0, M2 s10 s11 => M2 prec_list s10 s11
  | _, M1 c1 pl1 => union_mpl_0 c1 pl1 s0
  | M1 c0 pl0, _ => union_mpl_0 c0 pl0 s1
  | M2 s00 s01, M0 => M2 prec_list s00 s01
  | M2 s00 s01, M2 s10 s11 =>
      M2 prec_list (union_mpl s00 s10) (union_mpl s01 s11)
  end.

Lemma union_pl_0 : forall pl : prec_list, union_pl pl prec_empty = pl.
Proof.
	simple induction pl. intros. simpl in |- *. rewrite H0. trivial. simpl in |- *. trivial.
Qed.

Lemma union_pl_1 : forall pl : prec_list, union_pl prec_empty pl = pl.
Proof.
	simpl in |- *. intros. trivial.
Qed.

Lemma union_pl_2 :
 forall pl0 pl1 : prec_list,
 union_pl pl0 pl1 = prec_empty -> pl0 = prec_empty.
Proof.
	intros. induction  pl0 as [a pl0_1 Hrecpl0_1 pl0_0 Hrecpl0_0| ]. inversion H. trivial.
Qed.

Lemma union_pl_3 :
 forall pl0 pl1 : prec_list,
 pl0 <> prec_empty -> union_pl pl0 pl1 <> prec_empty.
Proof.
	intros. intro. exact (H (union_pl_2 pl0 pl1 H0)).
Qed.

Lemma union_pl_0d_0 :
 forall (d : preDTA) (pl0 : prec_list) (tl : term_list),
 liste_reconnait d pl0 tl -> liste_reconnait d (union_pl pl0 prec_empty) tl.
Proof.
	intros. rewrite (union_pl_0 pl0). trivial.
Qed.

Lemma union_pl_0d_1 :
 forall (d : preDTA) (pl0 : prec_list) (tl : term_list) 
   (a : ad) (la ls : prec_list),
 liste_reconnait d pl0 tl ->
 pl0 <> prec_empty -> liste_reconnait d (union_pl pl0 (prec_cons a la ls)) tl.
Proof.
	intro. simple induction pl0. intros. simpl in |- *. elim (term_list_disj tl). intros.
	rewrite H3 in H1. inversion H1. intros. elim H3. intros. elim H4. intros.
	rewrite H5. rewrite H5 in H1. inversion H1.
	exact (rec_consi d a p (union_pl p0 (prec_cons a0 la ls)) x x0 H9 H13).
	apply (rec_consn d a p (union_pl p0 (prec_cons a0 la ls)) x x0). 
	elim (classic (p0 = prec_empty)). intro. rewrite H13 in H8. 
	elim (sem_listes_1 d x x0 H8). intros. exact (H0 (tcons x x0) a0 la ls H8 H13).
	intros. elim H0. trivial.
Qed.

Lemma union_pl_0d :
 forall (d : preDTA) (pl0 pl1 : prec_list) (tl : term_list),
 pl_compat pl0 pl1 ->
 liste_reconnait d pl0 tl -> liste_reconnait d (union_pl pl0 pl1) tl.
Proof.
	intros. elim H. intros. elim H1. intros. rewrite H3. 
	exact (union_pl_0d_0 d pl0 tl H0). intros. elim H1. intros. induction  pl1 as [a pl1_1 Hrecpl1_1 pl1_0 Hrecpl1_0| ].
	exact (union_pl_0d_1 d pl0 tl a pl1_1 pl1_0 H0 H2). rewrite (union_pl_0 pl0).
	assumption.
Qed.

Lemma union_pl_1d_0 :
 forall (d : preDTA) (pl1 : prec_list) (tl : term_list),
 liste_reconnait d pl1 tl -> liste_reconnait d (union_pl prec_empty pl1) tl.
Proof.
	intros. simpl in |- *. assumption.
Qed.

Lemma union_pl_1d_1 :
 forall (d : preDTA) (pl1 : prec_list) (tl : term_list) pl0,
 liste_reconnait d pl1 tl ->
 pl1 <> prec_empty -> liste_reconnait d (union_pl pl0 pl1) tl.
Proof.
	intros. induction  pl0 as [a pl0_1 Hrecpl0_1 pl0_0 Hrecpl0_0| ]. elim (term_list_disj tl). intros. rewrite H1 in H.
	elim (H0 (sem_listes_2 d pl1 H)). intro. elim H1. intros. elim H2. intros. rewrite H3.
	rewrite H3 in H. simpl in |- *. apply (rec_consn d a pl0_1 (union_pl pl0_0 pl1) x x0).
	rewrite H3 in Hrecpl0_0. trivial. simpl in |- *. assumption.
Qed.

Lemma union_pl_1d :
 forall (d : preDTA) (pl0 pl1 : prec_list) (tl : term_list),
 pl_compat pl0 pl1 ->
 liste_reconnait d pl1 tl -> liste_reconnait d (union_pl pl0 pl1) tl.
Proof.
	intros. elim H. intros. elim H1. intros. rewrite H2. simpl in |- *. assumption.
	intros. elim H1. intros. induction  pl0 as [a pl0_1 Hrecpl0_1 pl0_0 Hrecpl0_0| ]. 
	exact (union_pl_1d_1 d pl1 tl (prec_cons a pl0_1 pl0_0) H0 H3). simpl in |- *.
	assumption.
Qed.

Lemma union_pl_r_0 :
 forall (d : preDTA) (pl0 pl1 : prec_list) (hd : term) (tl : term_list),
 liste_reconnait d (union_pl pl0 pl1) (tcons hd tl) ->
 liste_reconnait d pl0 (tcons hd tl) \/ liste_reconnait d pl1 (tcons hd tl).
Proof.
	intros. induction  pl0 as [a pl0_1 Hrecpl0_1 pl0_0 Hrecpl0_0| ]. simpl in H. inversion H. left.
	exact (rec_consi d a pl0_1 pl0_0 hd tl H3 H7). elim (Hrecpl0_0 H2). intros.
	left. exact (rec_consn d a pl0_1 pl0_0 hd tl H7). intro. right. assumption.
	simpl in H. right. assumption.
Qed.

Lemma union_pl_r_1 :
 forall (d : preDTA) (pl0 pl1 : prec_list),
 pl_compat pl0 pl1 ->
 liste_reconnait d (union_pl pl0 pl1) tnil ->
 liste_reconnait d pl0 tnil \/ liste_reconnait d pl1 tnil.
Proof.
	intros. elim H. intros. elim H1. intros. left. rewrite H2. 
	exact (rec_empty d). intros. elim H1. intros.
	elim (union_pl_3 pl0 pl1 H2 (sem_listes_2 d (union_pl pl0 pl1) H0)).
Qed.

Lemma union_pl_r :
 forall (d : preDTA) (pl0 pl1 : prec_list) (tl : term_list),
 pl_compat pl0 pl1 ->
 liste_reconnait d (union_pl pl0 pl1) tl ->
 liste_reconnait d pl0 tl \/ liste_reconnait d pl1 tl.
Proof.
	intros. induction  tl as [| t tl Hrectl]. exact (union_pl_r_1 d pl0 pl1 H H0).
	exact (union_pl_r_0 d pl0 pl1 t tl H0).
Qed.

(* conservation des relation compat par union d'état *)

Definition mpl_compat_7_def (s : state) : Prop :=
  forall (c : ad) (pl l : prec_list),
  MapGet prec_list s c = Some l ->
  MapGet prec_list (union_mpl_0 c pl s) c = Some (union_pl pl l).

Lemma mpl_compat_7_0 : mpl_compat_7_def (M0 prec_list).
Proof.
	unfold mpl_compat_7_def in |- *. intros. simpl in H. inversion H.
Qed.

Lemma mpl_compat_7_1 :
 forall (a : ad) (a0 : prec_list), mpl_compat_7_def (M1 prec_list a a0).
Proof.
	unfold mpl_compat_7_def in |- *. intros. simpl in H. elim (bool_is_true_or_false (Neqb a c)); intros; rewrite H0 in H;
  inversion H. rewrite (Neqb_complete a c H0). simpl in |- *.
	rewrite (Neqb_correct c). simpl in |- *. rewrite (Neqb_correct c). trivial.
Qed.

Lemma mpl_compat_7_2 :
 forall m : Map prec_list,
 mpl_compat_7_def m ->
 forall m0 : Map prec_list,
 mpl_compat_7_def m0 -> mpl_compat_7_def (M2 prec_list m m0).
Proof.
	unfold mpl_compat_7_def in |- *. intros. induction  c as [| p]. simpl in |- *. apply (H N0 pl l).
	simpl in H1. assumption. induction  p as [p Hrecp| p Hrecp| ]. simpl in |- *. apply (H0 (Npos p) pl l).
	simpl in H1. assumption. simpl in |- *. apply (H (Npos p) pl l). simpl in H1. assumption.
	simpl in H1. simpl in |- *. exact (H0 N0 pl l H1).
Qed.

Lemma mpl_compat_7_3 : forall m : state, mpl_compat_7_def m.
Proof.
	exact
  (Map_ind prec_list mpl_compat_7_def mpl_compat_7_0 mpl_compat_7_1
     mpl_compat_7_2).
Qed.

Lemma mpl_compat_7 :
 forall (s : state) (c : ad) (pl l : prec_list),
 MapGet prec_list s c = Some l ->
 MapGet prec_list (union_mpl_0 c pl s) c = Some (union_pl pl l).
Proof.
	intros. exact (mpl_compat_7_3 s c pl l H).
Qed.

Definition mpl_compat_8_def (s : state) : Prop :=
  forall (a c : ad) (pl l : prec_list),
  MapGet prec_list s c = Some l ->
  a <> c -> MapGet prec_list (union_mpl_0 a pl s) c = Some l.

Lemma mpl_compat_8_0 : mpl_compat_8_def (M0 prec_list).
Proof.
	unfold mpl_compat_8_def in |- *. intros. inversion H.
Qed.

Lemma mpl_compat_8_1 :
 forall (a : ad) (a0 : prec_list), mpl_compat_8_def (M1 prec_list a a0).
Proof.
	unfold mpl_compat_8_def in |- *. intros. simpl in H. elim (bool_is_true_or_false (Neqb a c)); intros; rewrite H1 in H. inversion H. simpl in |- *. elim (bool_is_true_or_false (Neqb a1 a)); intro; rewrite H2. simpl in |- *. elim (bool_is_true_or_false (Neqb a1 c)). intro.
	elim (H0 (Neqb_complete a1 c H4)). intro. rewrite (Neqb_complete a1 a H2) in H4.
	rewrite H1 in H4. inversion H4. elim (Ndiscr (Nxor a a1)). intro y. elim y.
	intros x y0. rewrite y0. rewrite (MapPut1_semantics prec_list x a a1 l pl y0 c).
	rewrite H1. trivial. intro y. rewrite (Neqb_comm a1 a) in H2.
	rewrite (Nxor_eq_true a a1 y) in H2. inversion H2. inversion H.
Qed.

Lemma mpl_compat_8_2 :
 forall m : state,
 mpl_compat_8_def m ->
 forall m0 : state,
 mpl_compat_8_def m0 -> mpl_compat_8_def (M2 prec_list m m0).
Proof.
	unfold mpl_compat_8_def in |- *. intros. induction  a as [| p]; [ induction  c as [| p] | induction  c as [| p0] ]. elim (H2 (refl_equal N0)).
	simpl in |- *. induction  p as [p Hrecp| p Hrecp| ]. simpl in H1. assumption. simpl in H1. apply (H N0 (Npos p) pl l H1).
	intro. inversion H3. simpl in H1. assumption. simpl in |- *. induction  p as [p Hrecp| p Hrecp| ]. simpl in |- *. simpl in H1.
	assumption. simpl in |- *. apply (H (Npos p) N0 pl l H1). intro. inversion H3. simpl in |- *.
	simpl in H1. assumption. simpl in |- *. induction  p as [p Hrecp| p Hrecp| ]. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. simpl in |- *. simpl in H1.
	apply (H0 (Npos p) (Npos p0) pl l H1). intro. inversion H3. elim H2. trivial. rewrite H5.
	trivial. simpl in |- *. simpl in H1. assumption. simpl in |- *. apply (H0 (Npos p) N0 pl l H1).
	intro. inversion H3. simpl in |- *. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. simpl in H1. assumption.
	apply (H (Npos p) (Npos p0) pl l H1). intro. inversion H3. rewrite H5 in H2. elim H2.
	trivial. simpl in H1. assumption. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. simpl in |- *. simpl in H1. simpl in |- *.
	apply (H0 N0 (Npos p0) pl l). assumption. intro. inversion H3. simpl in |- *. simpl in H1.
	assumption. simpl in |- *. elim H2. trivial.
Qed.

Lemma mpl_compat_8_3 : forall m : state, mpl_compat_8_def m.
Proof.
	exact
  (Map_ind prec_list mpl_compat_8_def mpl_compat_8_0 mpl_compat_8_1
     mpl_compat_8_2).
Qed.

Lemma mpl_compat_8 :
 forall (s : state) (a c : ad) (pl l : prec_list),
 MapGet prec_list s c = Some l ->
 a <> c -> MapGet prec_list (union_mpl_0 a pl s) c = Some l.
Proof.
	intro. exact (mpl_compat_8_3 s).
Qed.

(* invariant sur union_mpl_0, sens direct, 0 *)

Lemma union_s0d_0 :
 forall (d : preDTA) (c : ad) (pl : prec_list) (tl : term_list),
 mpl_compat (M1 prec_list c pl) (M0 prec_list) ->
 state_reconnait d (M1 prec_list c pl) (app c tl) ->
 state_reconnait d (union_mpl_0 c pl (M0 prec_list)) (app c tl).
Proof.
	unfold mpl_compat in |- *. intros. inversion H0. simpl in H5. rewrite (Neqb_correct c) in H5.
	inversion H5. apply (rec_st d (union_mpl_0 c l (M0 prec_list)) c tl l). simpl in |- *.
	rewrite (Neqb_correct c). trivial. assumption.
Qed.

Lemma union_s0d_1_0 :
 forall (d : preDTA) (c : ad) (pl pl0 : prec_list) (tl : term_list),
 mpl_compat (M1 prec_list c pl) (M1 prec_list c pl0) ->
 state_reconnait d (M1 prec_list c pl) (app c tl) ->
 state_reconnait d (union_mpl_0 c pl (M1 prec_list c pl0)) (app c tl).
Proof.
	intros. unfold mpl_compat in H. inversion H0. simpl in H5. 
	rewrite (Neqb_correct c) in H5. inversion H5. 
	apply
  (rec_st d (union_mpl_0 c l (M1 prec_list c pl0)) c tl (union_pl l pl0)).
	simpl in |- *. rewrite (Neqb_correct c). simpl in |- *. rewrite (Neqb_correct c). trivial.
	apply (union_pl_0d d l pl0 tl). apply (H c l pl0). simpl in |- *. rewrite (Neqb_correct c).
	trivial. simpl in |- *. rewrite (Neqb_correct c). trivial. assumption.
Qed.

Lemma union_s0d_1_1 :
 forall (d : preDTA) (c : ad) (pl : prec_list) (c0 : ad) 
   (pl0 : prec_list) (tl : term_list),
 mpl_compat (M1 prec_list c pl) (M1 prec_list c0 pl0) ->
 c <> c0 ->
 state_reconnait d (M1 prec_list c pl) (app c tl) ->
 state_reconnait d (union_mpl_0 c pl (M1 prec_list c0 pl0)) (app c tl).
Proof.
	intros. unfold mpl_compat in H. inversion H1. apply (rec_st d (union_mpl_0 c pl (M1 prec_list c0 pl0)) c tl l). simpl in |- *. elim (bool_is_true_or_false (Neqb c c0)); intros; rewrite H8. elim (H0 (Neqb_complete c c0 H8)). elim (Ndiscr (Nxor c0 c)).
	intro y. elim y; intros x y0. rewrite y0. cut
  (MapGet prec_list (MapPut1 prec_list c0 pl0 c pl x) c =
    match Neqb c0 c with
    | true => Some pl0
    | false =>
        match Neqb c c with
        | true => Some pl
        | false => None
        end
    end). intro. rewrite <- (Neqb_comm c c0) in H9.
	rewrite H8 in H9. rewrite (Neqb_correct c) in H9. rewrite H9. simpl in H6.
	rewrite (Neqb_correct c) in H6. inversion H6. trivial. exact (MapPut1_semantics prec_list x c0 c pl0 pl y0 c). intro y. rewrite (Neqb_comm c c0) in H8. rewrite (Nxor_eq_true c0 c y) in H8. inversion H8. assumption.
Qed.

Lemma union_s0d_2_0 :
 forall (d : preDTA) (pl : prec_list) (s0 s1 : state) (tl : term_list),
 mpl_compat (M1 prec_list N0 pl) (M2 prec_list s0 s1) ->
 state_reconnait d (M1 prec_list N0 pl) (app N0 tl) ->
 state_reconnait d (union_mpl_0 N0 pl (M2 prec_list s0 s1)) (app N0 tl).
Proof.
	intro. intro. simple induction s0. intros. simpl in |- *. inversion H0. apply (rec_st d (M2 prec_list (M1 prec_list N0 pl) s1) N0 tl l). simpl in |- *. simpl in H5. inversion H5. trivial.
	assumption. intros. unfold union_mpl_0 in |- *. elim (bool_is_true_or_false (Neqb N0 a)); intros; rewrite H1. apply
  (rec_st d (M2 prec_list (M1 prec_list N0 (union_pl pl a0)) s1) N0 tl
     (union_pl pl a0)). simpl in |- *. trivial. inversion H0. simpl in H6. inversion H6.
	apply (union_pl_0d d l a0 tl). apply (mpl_compat_0 N0 l a0). rewrite <- (Neqb_complete N0 a H1) in H. rewrite H9 in H. apply (mpl_compat_sym (M1 prec_list N0 a0) (M1 prec_list N0 l)). apply (mpl_compat_3 (M1 prec_list N0 a0) s1 l). apply
  (mpl_compat_sym (M1 prec_list N0 l)
     (M2 prec_list (M1 prec_list N0 a0) s1)). assumption. assumption. inversion H0.
	apply
  (rec_st d
     (M2 prec_list
        (MapMerge prec_list (M1 prec_list N0 pl) (M1 prec_list a a0)) s1)
     N0 tl l). cut
  (MapGet prec_list
     (MapMerge prec_list (M1 prec_list N0 pl) (M1 prec_list a a0)) N0 =
   (fun a1 : ad =>
    match MapGet prec_list (M1 prec_list a a0) a1 with
    | None => MapGet prec_list (M1 prec_list N0 pl) a1
    | Some y' => Some y'
    end) N0). intro. cut
  (MapGet prec_list
     (M2 prec_list
        (MapMerge prec_list (M1 prec_list N0 pl) (M1 prec_list a a0)) s1)
     N0 =
   MapGet prec_list
     (MapMerge prec_list (M1 prec_list N0 pl) (M1 prec_list a a0)) N0). intros.
	rewrite H9. rewrite H8. simpl in |- *. rewrite (Neqb_comm N0 a) in H1. rewrite H1. simpl in H6.
	inversion H6. trivial. simpl in |- *. trivial. exact
  (MapMerge_semantics prec_list (M1 prec_list N0 pl) 
     (M1 prec_list a a0) N0). assumption. intros. simpl in |- *. simpl in H. cut
  (state_reconnait d (M2 prec_list (union_mpl_0 N0 pl m) m0) (app N0 tl)). intro. inversion H3. apply
  (rec_st d (M2 prec_list (M2 prec_list (union_mpl_0 N0 pl m) m0) s1) N0
     tl l). simpl in |- *. assumption.
	assumption. apply (H m0 tl). apply (mpl_compat_sym (M2 prec_list m m0) (M1 prec_list N0 pl)).
	apply (mpl_compat_3 (M2 prec_list m m0) s1 pl). exact
  (mpl_compat_sym (M1 prec_list N0 pl)
     (M2 prec_list (M2 prec_list m m0) s1) H1). assumption.
Qed.

Lemma union_s0d_2_1 :
 forall (d : preDTA) (pl : prec_list) (s0 s1 : state) (tl : term_list),
 mpl_compat (M1 prec_list (Npos 1) pl) (M2 prec_list s0 s1) ->
 state_reconnait d (M1 prec_list (Npos 1) pl) (app (Npos 1) tl) ->
 state_reconnait d (union_mpl_0 (Npos 1) pl (M2 prec_list s0 s1))
   (app (Npos 1) tl).
Proof.
	intros. cut (state_reconnait d (union_mpl_0 N0 pl s1) (app N0 tl)). simpl in |- *. intro.
	inversion H1. apply (rec_st d (M2 prec_list s0 (union_mpl_0 N0 pl s1)) (Npos 1) tl l).
	simpl in |- *. assumption. assumption. induction  s1 as [| a a0| s1_1 Hrecs1_1 s1_0 Hrecs1_0]. apply (union_s0d_0 d N0 pl tl). apply (mpl_compat_sym (M0 prec_list) (M1 prec_list N0 pl)). apply (mpl_compat_4 s0 (M0 prec_list) pl). 
	exact
  (mpl_compat_sym (M1 prec_list (Npos 1) pl) (M2 prec_list s0 (M0 prec_list))
     H).
	inversion H0. simpl in H5. apply (rec_st d (M1 prec_list N0 pl) N0 tl pl). simpl in |- *.
	trivial. inversion H5. assumption. elim (classic (N0 = a)). intro. rewrite <- H1. rewrite <- H1 in H. apply (union_s0d_1_0 d N0 pl a0 tl). apply (mpl_compat_sym (M1 prec_list N0 a0) (M1 prec_list N0 pl)). apply (mpl_compat_4 s0 (M1 prec_list N0 a0) pl). exact
  (mpl_compat_sym (M1 prec_list (Npos 1) pl)
     (M2 prec_list s0 (M1 prec_list N0 a0)) H). inversion H0.
	apply (rec_st d (M1 prec_list N0 pl) N0 tl pl). simpl in |- *. trivial. simpl in H6. inversion H6.
	assumption. intro. apply (union_s0d_1_1 d N0 pl a a0 tl). apply (mpl_compat_sym (M1 prec_list a a0) (M1 prec_list N0 pl)). apply (mpl_compat_4 s0 (M1 prec_list a a0) pl). exact
  (mpl_compat_sym (M1 prec_list (Npos 1) pl)
     (M2 prec_list s0 (M1 prec_list a a0)) H). assumption. inversion H0.
	apply (rec_st d (M1 prec_list N0 pl) N0 tl pl). simpl in |- *. trivial. simpl in H6. inversion H6.
	assumption. simpl in |- *. cut (state_reconnait d (union_mpl_0 N0 pl s1_1) (app N0 tl)). intro.
	inversion H1. apply (rec_st d (M2 prec_list (union_mpl_0 N0 pl s1_1) s1_0) N0 tl l).
	simpl in |- *. assumption. assumption. apply Hrecs1_1. cut (mpl_compat (M1 prec_list N0 pl) s1_1).
	intro. unfold mpl_compat in |- *. intros. unfold mpl_compat in H1. unfold MapGet in H2. elim (bool_is_true_or_false (Neqb (Npos 1) c)); intro; rewrite H4 in H2;
  inversion H2.
	apply (H1 N0 p0 p1). simpl in |- *. rewrite H6. trivial. rewrite <- (Neqb_complete (Npos 1) c H4) in H3. simpl in H3. assumption. apply (mpl_compat_sym s1_1 (M1 prec_list N0 pl)).
	apply (mpl_compat_3 s1_1 s1_0 pl). apply (mpl_compat_4 s0 (M2 prec_list s1_1 s1_0) pl).
	exact
  (mpl_compat_sym (M1 prec_list (Npos 1) pl)
     (M2 prec_list s0 (M2 prec_list s1_1 s1_0)) H).
Qed.

Definition union_s_prd0 (s : state) : Prop :=
  forall (d : preDTA) (c : ad) (pl : prec_list) (tl : term_list),
  mpl_compat (M1 prec_list c pl) s ->
  state_reconnait d (M1 prec_list c pl) (app c tl) ->
  state_reconnait d (union_mpl_0 c pl s) (app c tl).

Lemma union_s0d_2 :
 forall m : Map prec_list,
 union_s_prd0 m ->
 forall m0 : Map prec_list,
 union_s_prd0 m0 -> union_s_prd0 (M2 prec_list m m0).
Proof.
	unfold union_s_prd0 in |- *. intros. induction  c as [| p]. exact (union_s0d_2_0 d pl m m0 tl H1 H2).
	induction  p as [p Hrecp| p Hrecp| ]. simpl in |- *. cut (state_reconnait d (union_mpl_0 (Npos p) pl m0) (app (Npos p) tl)). intro. inversion H3. apply
  (rec_st d (M2 prec_list m (union_mpl_0 (Npos p) pl m0)) (Npos (xI p)) tl l). simpl in |- *. assumption. assumption. apply (H0 d (Npos p) pl tl).
	apply (mpl_compat_sym m0 (M1 prec_list (Npos p) pl)). exact
  (mpl_compat_6 m m0 pl p
     (mpl_compat_sym (M1 prec_list (Npos (xI p)) pl) (M2 prec_list m m0) H1)). inversion H2.
	simpl in H7. rewrite (aux_Neqb_1_0 p) in H7. inversion H7. apply (rec_st d (M1 prec_list (Npos p) l) (Npos p) tl l). simpl in |- *. rewrite (aux_Neqb_1_0 p). trivial. assumption.
	simpl in |- *. cut (state_reconnait d (union_mpl_0 (Npos p) pl m) (app (Npos p) tl)). intro.
	inversion H3. apply
  (rec_st d (M2 prec_list (union_mpl_0 (Npos p) pl m) m0) (Npos (xO p)) tl l). simpl in |- *. assumption. assumption. apply (H d (Npos p) pl tl). apply (mpl_compat_sym m (M1 prec_list (Npos p) pl)). exact
  (mpl_compat_5 m m0 pl p
     (mpl_compat_sym (M1 prec_list (Npos (xO p)) pl) (M2 prec_list m m0) H1)). inversion H2. apply (rec_st d (M1 prec_list (Npos p) pl) (Npos p) tl l). simpl in |- *. rewrite (aux_Neqb_1_0 p). simpl in H7. rewrite (aux_Neqb_1_0 p) in H7. inversion H7. trivial. assumption. 
	exact (union_s0d_2_1 d pl m m0 tl H1 H2).
Qed.

Lemma union_s0d_3 : union_s_prd0 (M0 prec_list).
Proof.
	unfold union_s_prd0 in |- *. intros. exact (union_s0d_0 d c pl tl H H0).
Qed.

Lemma union_s0d_1 :
 forall (a : ad) (a0 : prec_list), union_s_prd0 (M1 prec_list a a0).
Proof.
	unfold union_s_prd0 in |- *. intros. elim (classic (a = c)). intro. rewrite H1. rewrite H1 in H.
	exact (union_s0d_1_0 d c pl a0 tl H H0). intro. apply (union_s0d_1_1 d c pl a a0 tl). 
	assumption. intro. exact (H1 (sym_eq H2)). assumption.
Qed.

Lemma union_s_0d : forall m : state, union_s_prd0 m.
Proof.
	exact (Map_ind prec_list union_s_prd0 union_s0d_3 union_s0d_1 union_s0d_2).
Qed.

Lemma union_s0d :
 forall (s : state) (d : preDTA) (c : ad) (pl : prec_list) (tl : term_list),
 mpl_compat (M1 prec_list c pl) s ->
 state_reconnait d (M1 prec_list c pl) (app c tl) ->
 state_reconnait d (union_mpl_0 c pl s) (app c tl).
Proof.
	intro. exact (union_s_0d s).
Qed.

(* invariant sur union_mpl_0, sens direct, 1 *)

Definition union_s_prd1 (s : state) : Prop :=
  forall (d : preDTA) (a : ad) (pl : prec_list) (c : ad) (tl : term_list),
  mpl_compat (M1 prec_list a pl) s ->
  state_reconnait d s (app c tl) ->
  state_reconnait d (union_mpl_0 a pl s) (app c tl).

Lemma union_s1d_0 : union_s_prd1 (M0 prec_list).
Proof.
	unfold union_s_prd1 in |- *. intros. inversion H0. simpl in H5. inversion H5.
Qed.

Lemma union_s1d_1_0 :
 forall (d : preDTA) (a : ad) (pl pl0 : prec_list) (c : ad) (tl : term_list),
 mpl_compat (M1 prec_list a pl) (M1 prec_list c pl0) ->
 a <> c ->
 state_reconnait d (M1 prec_list c pl0) (app c tl) ->
 state_reconnait d (union_mpl_0 a pl (M1 prec_list c pl0)) (app c tl).
Proof.
	intros. simpl in |- *. elim (bool_is_true_or_false (Neqb a c)). intro. 
	elim (H0 (Neqb_complete a c H2)). intro. rewrite H2. 
	elim (Ndiscr (Nxor c a)); intro y. elim y. intros x y0. rewrite y0. inversion H1.
	apply (rec_st d (MapPut1 prec_list c pl0 a pl x) c tl l).
	rewrite (MapPut1_semantics prec_list x c a pl0 pl y0 c). rewrite (Neqb_correct c).
	simpl in H7. rewrite (Neqb_correct c) in H7. inversion H7. trivial. trivial.
	rewrite (Nxor_comm c a) in y. rewrite (Nxor_eq_true a c y) in H2.
	inversion H2.
Qed.

Lemma union_s1d_1_1 :
 forall (d : preDTA) (pl pl0 : prec_list) (c : ad) (tl : term_list),
 mpl_compat (M1 prec_list c pl) (M1 prec_list c pl0) ->
 state_reconnait d (M1 prec_list c pl0) (app c tl) ->
 state_reconnait d (union_mpl_0 c pl (M1 prec_list c pl0)) (app c tl).
Proof.
	intros. simpl in |- *. rewrite (Neqb_correct c). apply (rec_st d (M1 prec_list c (union_pl pl pl0)) c tl (union_pl pl pl0)). simpl in |- *. rewrite (Neqb_correct c). trivial.
	inversion H0. simpl in H5. rewrite (Neqb_correct c) in H5. inversion H5.
	apply (union_pl_1d d pl l tl). rewrite H8 in H. exact (mpl_compat_0 c pl l H).
	assumption.
Qed.

Lemma union_s1d_1 :
 forall (a : ad) (a0 : prec_list), union_s_prd1 (M1 prec_list a a0).
Proof.
	unfold union_s_prd1 in |- *. intros. cut (a = c). intro. rewrite H1 in H. rewrite H1 in H0.
	rewrite H1. elim (classic (a1 = c)). intro. rewrite H2. rewrite H2 in H.
	exact (union_s1d_1_1 d pl a0 c tl H H0). intro. exact (union_s1d_1_0 d a1 pl a0 c tl H H2 H0). inversion H0. simpl in H5. elim (bool_is_true_or_false (Neqb a c)).
	intro. exact (Neqb_complete a c H7). intro. rewrite H7 in H5. inversion H5.
Qed.

Lemma union_s1d_2 :
 forall m : state,
 union_s_prd1 m ->
 forall m0 : state, union_s_prd1 m0 -> union_s_prd1 (M2 prec_list m m0).
Proof.
	unfold union_s_prd1 in |- *. intros. induction  c as [| p]. induction  a as [| p]. simpl in |- *. cut (state_reconnait d (union_mpl_0 N0 pl m) (app N0 tl)). intro. inversion H3. apply (rec_st d (M2 prec_list (union_mpl_0 N0 pl m) m0) N0 tl l). simpl in |- *. assumption. assumption.
	apply (H d N0 pl N0 tl). apply (mpl_compat_sym m (M1 prec_list N0 pl)).
	apply (mpl_compat_3 m m0 pl). exact (mpl_compat_sym (M1 prec_list N0 pl) (M2 prec_list m m0) H1). inversion H2. apply (rec_st d m N0 tl l). simpl in H7.
	assumption. assumption. induction  p as [p Hrecp| p Hrecp| ]. simpl in |- *. inversion H2.
	apply (rec_st d (M2 prec_list m (union_mpl_0 (Npos p) pl m0)) N0 tl l). simpl in |- *.
	simpl in H7. assumption. assumption. simpl in |- *. cut (state_reconnait d (union_mpl_0 (Npos p) pl m) (app N0 tl)). intro. inversion H3. apply (rec_st d (M2 prec_list (union_mpl_0 (Npos p) pl m) m0) N0 tl l). simpl in |- *. assumption. assumption. 
	apply (H d (Npos p) pl N0 tl). apply (mpl_compat_sym m (M1 prec_list (Npos p) pl)).
	apply (mpl_compat_5 m m0 pl p). exact
  (mpl_compat_sym (M1 prec_list (Npos (xO p)) pl) (M2 prec_list m m0) H1). inversion H2. simpl in H7. exact (rec_st d m N0 tl l H7 H8).
	simpl in |- *. inversion H2. apply (rec_st d (M2 prec_list m (union_mpl_0 N0 pl m0)) N0 tl l).
	simpl in |- *. simpl in H7. assumption. assumption. induction  p as [p Hrecp| p Hrecp| ]. induction  a as [| p0]. simpl in |- *. inversion H2.
	apply
  (rec_st d (M2 prec_list (union_mpl_0 N0 pl m) m0) (Npos (xI p)) tl l). simpl in |- *.
	simpl in H7. assumption. assumption. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. simpl in |- *. cut (state_reconnait d (union_mpl_0 (Npos p0) pl m0) (app (Npos p) tl)). intro. inversion H3. apply
  (rec_st d (M2 prec_list m (union_mpl_0 (Npos p0) pl m0)) (Npos (xI p)) tl l). simpl in |- *. assumption. assumption.
	apply (H0 d (Npos p0) pl (Npos p) tl). apply (mpl_compat_sym m0 (M1 prec_list (Npos p0) pl)).
	apply (mpl_compat_6 m m0 pl p0). exact
  (mpl_compat_sym (M1 prec_list (Npos (xI p0)) pl) (M2 prec_list m m0) H1). inversion H2. simpl in H7. exact (rec_st d m0 (Npos p) tl l H7 H8).
	simpl in |- *. inversion H2. apply
  (rec_st d (M2 prec_list (union_mpl_0 (Npos p0) pl m) m0) (Npos (xI p)) tl l). simpl in |- *. simpl in H7. assumption. assumption. simpl in |- *.
	cut (state_reconnait d (union_mpl_0 N0 pl m0) (app (Npos p) tl)). intro. inversion H3.
	apply
  (rec_st d (M2 prec_list m (union_mpl_0 N0 pl m0)) (Npos (xI p)) tl l). simpl in |- *.
	assumption. assumption. apply (H0 d N0 pl (Npos p) tl). apply (mpl_compat_sym m0 (M1 prec_list N0 pl)). apply (mpl_compat_4 m m0 pl). exact (mpl_compat_sym (M1 prec_list (Npos 1) pl) (M2 prec_list m m0) H1). inversion H2. simpl in H7. exact (rec_st d m0 (Npos p) tl l H7 H8). induction  a as [| p0]. simpl in |- *. cut (state_reconnait d (union_mpl_0 N0 pl m) (app (Npos p) tl)).
	intro. inversion H3. apply
  (rec_st d (M2 prec_list (union_mpl_0 N0 pl m) m0) (Npos (xO p)) tl l).
	simpl in |- *. assumption. assumption. apply (H d N0 pl (Npos p) tl). apply (mpl_compat_sym m (M1 prec_list N0 pl)). apply (mpl_compat_3 m m0 pl). exact (mpl_compat_sym (M1 prec_list N0 pl) (M2 prec_list m m0) H1). inversion H2. simpl in H7. exact (rec_st d m (Npos p) tl l H7 H8).
	induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. simpl in |- *. inversion H2. apply
  (rec_st d (M2 prec_list m (union_mpl_0 (Npos p0) pl m0)) (Npos (xO p)) tl l). simpl in |- *. simpl in H7. assumption. assumption. simpl in |- *.
	cut (state_reconnait d (union_mpl_0 (Npos p0) pl m) (app (Npos p) tl)). intro. inversion H3.
	apply
  (rec_st d (M2 prec_list (union_mpl_0 (Npos p0) pl m) m0) (Npos (xO p)) tl l). simpl in |- *.
	simpl in H8. assumption. assumption. apply (H d (Npos p0) pl (Npos p) tl). 
	apply (mpl_compat_sym m (M1 prec_list (Npos p0) pl)). apply (mpl_compat_5 m m0 pl p0). 
	exact
  (mpl_compat_sym (M1 prec_list (Npos (xO p0)) pl) (M2 prec_list m m0) H1). inversion H2. 
	simpl in H7. exact (rec_st d m (Npos p) tl l H7 H8). simpl in |- *. inversion H2. simpl in H7.
	apply
  (rec_st d (M2 prec_list m (union_mpl_0 N0 pl m0)) (Npos (xO p)) tl l). simpl in |- *.
	assumption. assumption. induction  a as [| p]. simpl in |- *. inversion H2. simpl in H7.
	apply (rec_st d (M2 prec_list (union_mpl_0 N0 pl m) m0) (Npos 1) tl l). simpl in |- *. assumption.
	assumption. induction  p as [p Hrecp| p Hrecp| ]. simpl in |- *. cut (state_reconnait d (union_mpl_0 (Npos p) pl m0) (app N0 tl)).
	intro. inversion H3. apply (rec_st d (M2 prec_list m (union_mpl_0 (Npos p) pl m0)) (Npos 1) tl l).
	simpl in |- *. simpl in H8. assumption. assumption. apply (H0 d (Npos p) pl N0 tl).
	apply (mpl_compat_sym m0 (M1 prec_list (Npos p) pl)). apply (mpl_compat_6 m m0 pl p).
	exact
  (mpl_compat_sym (M1 prec_list (Npos (xI p)) pl) (M2 prec_list m m0) H1). inversion H2.
	simpl in H7. exact (rec_st d m0 N0 tl l H7 H8). simpl in |- *. inversion H2. simpl in H7.
	apply (rec_st d (M2 prec_list (union_mpl_0 (Npos p) pl m) m0) (Npos 1) tl l). simpl in |- *.
	assumption. assumption. simpl in |- *. cut (state_reconnait d (union_mpl_0 N0 pl m0) (app N0 tl)).
	intro. inversion H3. apply (rec_st d (M2 prec_list m (union_mpl_0 N0 pl m0)) (Npos 1) tl l).
	simpl in |- *. assumption. assumption. apply (H0 d N0 pl N0 tl). 
	apply (mpl_compat_sym m0 (M1 prec_list N0 pl)). apply (mpl_compat_4 m m0 pl).
	exact (mpl_compat_sym (M1 prec_list (Npos 1) pl) (M2 prec_list m m0) H1).
	inversion H2. simpl in H7. exact (rec_st d m0 N0 tl l H7 H8).
Qed.

Lemma union_s1d_3 : forall m : state, union_s_prd1 m.
Proof.
	exact (Map_ind prec_list union_s_prd1 union_s1d_0 union_s1d_1 union_s1d_2).
Qed.

Lemma union_s1d :
 forall (s : state) (d : preDTA) (a : ad) (pl : prec_list) 
   (c : ad) (tl : term_list),
 mpl_compat (M1 prec_list a pl) s ->
 state_reconnait d s (app c tl) ->
 state_reconnait d (union_mpl_0 a pl s) (app c tl).
Proof.
	intro. exact (union_s1d_3 s).
Qed.

Definition union_std_def (s0 : state) : Prop :=
  forall (s1 : state) (d : preDTA) (c : ad) (tl : term_list),
  mpl_compat s0 s1 ->
  state_reconnait d s0 (app c tl) ->
  state_reconnait d (union_mpl s0 s1) (app c tl) /\
  state_reconnait d (union_mpl s1 s0) (app c tl).

Lemma union_std_0 : union_std_def (M0 prec_list).
Proof.
	unfold union_std_def in |- *. intros. inversion H0. inversion H5.
Qed.

Lemma union_std_1 :
 forall (a : ad) (a0 : prec_list), union_std_def (M1 prec_list a a0).
Proof.
	unfold union_std_def in |- *. intros. split. induction  s1 as [| a1 a2| s1_1 Hrecs1_1 s1_0 Hrecs1_0]. unfold union_mpl in |- *. cut (a = c).
	intro. rewrite H1. rewrite H1 in H. rewrite H1 in H0. exact (union_s0d (M0 prec_list) d c a0 tl H H0). inversion H0. simpl in H5.
	elim (bool_is_true_or_false (Neqb a c)); intro. exact (Neqb_complete a c H7).
	rewrite H7 in H5. inversion H5. unfold union_mpl in |- *.
	exact
  (union_s1d (M1 prec_list a a0) d a1 a2 c tl
     (mpl_compat_sym (M1 prec_list a a0) (M1 prec_list a1 a2) H) H0). unfold union_mpl in |- *. cut (a = c). intro. rewrite H1.
	rewrite H1 in H. rewrite H1 in H0. exact (union_s0d (M2 prec_list s1_1 s1_0) d c a0 tl H H0).
	inversion H0. simpl in H5. elim (bool_is_true_or_false (Neqb a c)). intro.
	exact (Neqb_complete a c H7). intro. rewrite H7 in H5. inversion H5. induction  s1 as [| a1 a2| s1_1 Hrecs1_1 s1_0 Hrecs1_0].
	unfold union_mpl in |- *. cut (a = c). intro. rewrite H1. rewrite H1 in H. rewrite H1 in H0.
	exact (union_s0d (M0 prec_list) d c a0 tl H H0). inversion H0. simpl in H5.
	elim (bool_is_true_or_false (Neqb a c)). intro. exact (Neqb_complete a c H7).
	intro. rewrite H7 in H5. inversion H5. unfold union_mpl in |- *. cut (a = c). intro.
	rewrite H1. rewrite H1 in H. rewrite H1 in H0. exact (union_s0d (M1 prec_list a1 a2) d c a0 tl H H0). inversion H0. simpl in H5. elim (bool_is_true_or_false (Neqb a c)).
	intro. exact (Neqb_complete a c H7). intro. rewrite H7 in H5. inversion H5.
	cut (a = c). intro. rewrite H1 in H. rewrite H1 in H0. rewrite H1.
	exact (union_s0d (M2 prec_list s1_1 s1_0) d c a0 tl H H0). inversion H0.
	elim (bool_is_true_or_false (Neqb a c)). intro. exact (Neqb_complete a c H7).
	intro. simpl in H5. rewrite H7 in H5. inversion H5.
Qed.

Lemma union_std_2 :
 forall m : state,
 union_std_def m ->
 forall m0 : state, union_std_def m0 -> union_std_def (M2 prec_list m m0).
Proof.
	unfold union_std_def in |- *. intros. induction  s1 as [| a a0| s1_1 Hrecs1_1 s1_0 Hrecs1_0]. simpl in |- *. split. assumption.
	assumption. unfold union_mpl in |- *. induction  c as [| p]. induction  a as [| p]. simpl in |- *.
	cut
  (state_reconnait d (M2 prec_list (union_mpl_0 N0 a0 m) m0) (app N0 tl)).
	intro. split. assumption.  assumption. cut (state_reconnait d (union_mpl_0 N0 a0 m) (app N0 tl)). intro. inversion H3. apply (rec_st d (M2 prec_list (union_mpl_0 N0 a0 m) m0) N0 tl l). simpl in |- *. assumption. assumption.
	cut
  (state_reconnait d (union_mpl m (M1 prec_list N0 a0)) (app N0 tl) /\
   state_reconnait d (union_mpl (M1 prec_list N0 a0) m) (app N0 tl)).
	intro. elim H3. intros. unfold union_mpl in H4. induction  m as [| a a1| m1 Hrecm1 m2 Hrecm0]. assumption.
	assumption. assumption. apply (H (M1 prec_list N0 a0) d N0 tl).
	exact (mpl_compat_3 m m0 a0 H1). inversion H2. simpl in H7.
	exact (rec_st d m N0 tl l H7 H8). induction  p as [p Hrecp| p Hrecp| ]. cut
  (state_reconnait d (union_mpl_0 (Npos (xI p)) a0 (M2 prec_list m m0))
     (app N0 tl)). intro.
	split. assumption. assumption. simpl in |- *. inversion H2. simpl in H7.
	apply (rec_st d (M2 prec_list m (union_mpl_0 (Npos p) a0 m0)) N0 tl l).
	simpl in |- *. assumption. assumption. cut
  (state_reconnait d (union_mpl_0 (Npos (xO p)) a0 (M2 prec_list m m0))
     (app N0 tl)). intro. split. assumption. assumption.
	simpl in |- *. cut
  (state_reconnait d (union_mpl m (M1 prec_list (Npos p) a0)) (app N0 tl) /\
   state_reconnait d (union_mpl (M1 prec_list (Npos p) a0) m) (app N0 tl)). intro. elim H3. intros. simpl in |- *. cut (state_reconnait d (union_mpl_0 (Npos p) a0 m) (app N0 tl)). intro. inversion H6.
	apply (rec_st d (M2 prec_list (union_mpl_0 (Npos p) a0 m) m0) N0 tl l).
	simpl in |- *. assumption. assumption. induction  m as [| a a1| m1 Hrecm1 m2 Hrecm0]. assumption. assumption.
	assumption. apply (H (M1 prec_list (Npos p) a0) d N0 tl).
	exact (mpl_compat_5 m m0 a0 p H1). inversion H2. simpl in H7. exact (rec_st d m N0 tl l H7 H8). cut
  (state_reconnait d (union_mpl_0 (Npos 1) a0 (M2 prec_list m m0))
     (app N0 tl)). intros. split. assumption. assumption. inversion H2.
	apply (rec_st d (union_mpl_0 (Npos 1) a0 (M2 prec_list m m0)) N0 tl l).
	simpl in |- *. simpl in H7. assumption. assumption. induction  p as [p Hrecp| p Hrecp| ]. induction  a as [| p0].
	cut
  (state_reconnait d (union_mpl_0 N0 a0 (M2 prec_list m m0))
     (app (Npos (xI p)) tl)).
	intro. split. assumption. assumption. simpl in |- *. inversion H2.
	apply
  (rec_st d (M2 prec_list (union_mpl_0 N0 a0 m) m0) (Npos (xI p)) tl l).
	simpl in |- *. assumption. assumption. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. cut
  (state_reconnait d (union_mpl_0 (Npos (xI p0)) a0 (M2 prec_list m m0))
     (app (Npos (xI p)) tl)).
	intro. split. assumption. assumption. simpl in |- *. cut
  (state_reconnait d (union_mpl m0 (M1 prec_list (Npos p0) a0))
     (app (Npos p) tl) /\
   state_reconnait d (union_mpl (M1 prec_list (Npos p0) a0) m0)
     (app (Npos p) tl)). intros. elim H3. intros.
	cut (state_reconnait d (union_mpl_0 (Npos p0) a0 m0) (app (Npos p) tl)). intro.
	inversion H6. apply
  (rec_st d (M2 prec_list m (union_mpl_0 (Npos p0) a0 m0)) (Npos (xI p)) tl l). simpl in |- *. assumption. assumption. induction  m0 as [| a a1| m0_1 Hrecm0_1 m0_0 Hrecm0_0]; assumption.
	apply (H0 (M1 prec_list (Npos p0) a0) d (Npos p) tl). exact (mpl_compat_6 m m0 a0 p0 H1).
	inversion H2. simpl in H7. exact (rec_st d m0 (Npos p) tl l H7 H8).
	cut
  (state_reconnait d (union_mpl_0 (Npos (xO p0)) a0 (M2 prec_list m m0))
     (app (Npos (xI p)) tl)). intro. split. assumption. assumption. simpl in |- *.
	inversion H2. apply
  (rec_st d (M2 prec_list (union_mpl_0 (Npos p0) a0 m) m0) (Npos (xI p)) tl l). simpl in |- *. simpl in H7. assumption. assumption.
	cut
  (state_reconnait d (union_mpl_0 (Npos 1) a0 (M2 prec_list m m0))
     (app (Npos (xI p)) tl)). intro. split; assumption. simpl in |- *.
	cut
  (state_reconnait d (union_mpl m0 (M1 prec_list N0 a0)) (app (Npos p) tl) /\
   state_reconnait d (union_mpl (M1 prec_list N0 a0) m0) (app (Npos p) tl)).
	intro. elim H3. intros. cut (state_reconnait d (union_mpl_0 N0 a0 m0) (app (Npos p) tl)). intro. inversion H6. apply
  (rec_st d (M2 prec_list m (union_mpl_0 N0 a0 m0)) (Npos (xI p)) tl l). simpl in |- *. assumption. assumption.
	induction  m0 as [| a a1| m0_1 Hrecm0_1 m0_0 Hrecm0_0]; assumption. apply (H0 (M1 prec_list N0 a0) d (Npos p) tl).
	exact (mpl_compat_4 m m0 a0 H1). inversion H2. simpl in H7. exact (rec_st d m0 (Npos p) tl l H7 H8). induction  a as [| p0]. cut
  (state_reconnait d (union_mpl_0 N0 a0 (M2 prec_list m m0))
     (app (Npos (xO p)) tl)). intro. split; assumption. simpl in |- *.
	cut (state_reconnait d (union_mpl_0 N0 a0 m) (app (Npos p) tl)). intro. 
	inversion H3. apply
  (rec_st d (M2 prec_list (union_mpl_0 N0 a0 m) m0) (Npos (xO p)) tl l). simpl in |- *. assumption. assumption. cut
  (state_reconnait d (union_mpl m (M1 prec_list N0 a0)) (app (Npos p) tl) /\
   state_reconnait d (union_mpl (M1 prec_list N0 a0) m) (app (Npos p) tl)). intro. elim H3. intros. induction  m as [| a a1| m1 Hrecm1 m2 Hrecm0]; assumption.
	apply (H (M1 prec_list N0 a0) d (Npos p) tl). exact (mpl_compat_3 m m0 a0 H1).
	inversion H2. simpl in H7. exact (rec_st d m (Npos p) tl l H7 H8). induction  p0 as [p0 Hrecp0| p0 Hrecp0| ].
	cut
  (state_reconnait d (union_mpl_0 (Npos (xI p0)) a0 (M2 prec_list m m0))
     (app (Npos (xO p)) tl)). intro. split; assumption. simpl in |- *. inversion H2.
	apply
  (rec_st d (M2 prec_list m (union_mpl_0 (Npos p0) a0 m0)) (Npos (xO p)) tl l).
	simpl in |- *. assumption. assumption. cut
  (state_reconnait d (union_mpl_0 (Npos (xO p0)) a0 (M2 prec_list m m0))
     (app (Npos (xO p)) tl)). intros. split; assumption. simpl in |- *.
	cut (state_reconnait d (union_mpl_0 (Npos p0) a0 m) (app (Npos p) tl)). intro.
	inversion H3. apply
  (rec_st d (M2 prec_list (union_mpl_0 (Npos p0) a0 m) m0) (Npos (xO p)) tl l). simpl in |- *. simpl in H8. assumption. assumption.
	cut
  (state_reconnait d (union_mpl m (M1 prec_list (Npos p0) a0))
     (app (Npos p) tl) /\
   state_reconnait d (union_mpl (M1 prec_list (Npos p0) a0) m)
     (app (Npos p) tl)).
	intro. elim H3. intros. induction  m as [| a a1| m1 Hrecm1 m2 Hrecm0]; assumption. apply (H (M1 prec_list (Npos p0) a0) d (Npos p) tl). exact (mpl_compat_5 m m0 a0 p0 H1). inversion H2. simpl in H7.
	exact (rec_st d m (Npos p) tl l H7 H8). cut
  (state_reconnait d (union_mpl_0 (Npos 1) a0 (M2 prec_list m m0))
     (app (Npos (xO p)) tl)). intro. split; assumption. simpl in |- *.
	inversion H2. apply
  (rec_st d (M2 prec_list m (union_mpl_0 N0 a0 m0)) (Npos (xO p)) tl l). simpl in H7. simpl in |- *. assumption. assumption. induction  a as [| p]. cut
  (state_reconnait d (union_mpl_0 N0 a0 (M2 prec_list m m0))
     (app (Npos 1) tl)). intro. split; assumption.
	simpl in |- *. inversion H2. apply (rec_st d (M2 prec_list (union_mpl_0 N0 a0 m) m0) (Npos 1) tl l). simpl in |- *. simpl in H7. assumption. assumption. cut
  (state_reconnait d (union_mpl_0 (Npos p) a0 (M2 prec_list m m0))
     (app (Npos 1) tl)). intro. split; assumption.
	induction  p as [p Hrecp| p Hrecp| ]. simpl in |- *. cut (state_reconnait d (union_mpl_0 (Npos p) a0 m0) (app N0 tl)).
	intro. inversion H3. apply (rec_st d (M2 prec_list m (union_mpl_0 (Npos p) a0 m0)) (Npos 1) tl l). simpl in |- *. simpl in H8. assumption. assumption.
	cut
  (state_reconnait d (union_mpl m0 (M1 prec_list (Npos p) a0)) (app N0 tl) /\
   state_reconnait d (union_mpl (M1 prec_list (Npos p) a0) m0) (app N0 tl)).
	intro. elim H3. intros. induction  m0 as [| a a1| m0_1 Hrecm0_1 m0_0 Hrecm0_0]; assumption. apply (H0 (M1 prec_list (Npos p) a0) d N0 tl). exact (mpl_compat_6 m m0 a0 p H1). inversion H2. simpl in H7.
	exact (rec_st d m0 N0 tl l H7 H8). simpl in |- *. inversion H2. apply (rec_st d (M2 prec_list (union_mpl_0 (Npos p) a0 m) m0) (Npos 1) tl l). simpl in |- *. simpl in H7. assumption.
	assumption. simpl in |- *. cut (state_reconnait d (union_mpl_0 N0 a0 m0) (app N0 tl)).
	intro. inversion H3. apply (rec_st d (M2 prec_list m (union_mpl_0 N0 a0 m0)) (Npos 1) tl l). simpl in |- *. simpl in H8. assumption. assumption. cut
  (state_reconnait d (union_mpl m0 (M1 prec_list N0 a0)) (app N0 tl) /\
   state_reconnait d (union_mpl (M1 prec_list N0 a0) m0) (app N0 tl)). intro. elim H3. intros. induction  m0 as [| a a1| m0_1 Hrecm0_1 m0_0 Hrecm0_0]; assumption.
	apply (H0 (M1 prec_list N0 a0) d N0 tl). exact (mpl_compat_4 m m0 a0 H1).
	inversion H2. simpl in H7. exact (rec_st d m0 N0 tl l H7 H8). simpl in |- *. cut (mpl_compat m s1_1).
	cut (mpl_compat m0 s1_0). intros. induction  c as [| p]. cut
  (state_reconnait d (union_mpl m s1_1) (app N0 tl) /\
   state_reconnait d (union_mpl s1_1 m) (app N0 tl)). intro. elim H5.
	intros. split. inversion H6. apply
  (rec_st d (M2 prec_list (union_mpl m s1_1) (union_mpl m0 s1_0)) N0 tl l). simpl in |- *. assumption. assumption. inversion H7. apply
  (rec_st d (M2 prec_list (union_mpl s1_1 m) (union_mpl s1_0 m0)) N0 tl l). simpl in |- *. assumption. assumption.
	apply (H s1_1 d N0 tl H4). inversion H2. simpl in H9. exact (rec_st d m N0 tl l H9 H10).
	induction  p as [p Hrecp| p Hrecp| ]. cut
  (state_reconnait d (union_mpl m0 s1_0) (app (Npos p) tl) /\
   state_reconnait d (union_mpl s1_0 m0) (app (Npos p) tl)). intro. elim H5. intros. 
	split. inversion H6. apply
  (rec_st d (M2 prec_list (union_mpl m s1_1) (union_mpl m0 s1_0))
     (Npos (xI p)) tl l). simpl in |- *. assumption. assumption. inversion H7. apply
  (rec_st d (M2 prec_list (union_mpl s1_1 m) (union_mpl s1_0 m0))
     (Npos (xI p)) tl l). simpl in |- *.
	assumption. assumption. apply (H0 s1_0 d (Npos p) tl H3). inversion H2. simpl in H9.
	exact (rec_st d m0 (Npos p) tl l H9 H10). cut
  (state_reconnait d (union_mpl m s1_1) (app (Npos p) tl) /\
   state_reconnait d (union_mpl s1_1 m) (app (Npos p) tl)). intro.
	elim H5. intros. split. inversion H6. apply
  (rec_st d (M2 prec_list (union_mpl m s1_1) (union_mpl m0 s1_0))
     (Npos (xO p)) tl l). simpl in |- *. assumption. assumption. inversion H7.
	apply
  (rec_st d (M2 prec_list (union_mpl s1_1 m) (union_mpl s1_0 m0))
     (Npos (xO p)) tl l).
	simpl in |- *. assumption. assumption. apply (H s1_1 d (Npos p) tl H4). inversion H2. simpl in H9.
	exact (rec_st d m (Npos p) tl l H9 H10). cut
  (state_reconnait d (union_mpl m0 s1_0) (app N0 tl) /\
   state_reconnait d (union_mpl s1_0 m0) (app N0 tl)). intro. elim H5. intros. split.
	inversion H6. apply
  (rec_st d (M2 prec_list (union_mpl m s1_1) (union_mpl m0 s1_0)) 
     (Npos 1) tl l). simpl in |- *. assumption. assumption. inversion H7. apply
  (rec_st d (M2 prec_list (union_mpl s1_1 m) (union_mpl s1_0 m0)) 
     (Npos 1) tl l). simpl in |- *. assumption. assumption.
	apply (H0 s1_0 d N0 tl H3). inversion H2. simpl in H9. exact (rec_st d m0 N0 tl l H9 H10).
	exact (mpl_compat_2 m m0 s1_1 s1_0 H1). exact (mpl_compat_1 m m0 s1_1 s1_0 H1).
Qed.

Lemma union_std : forall m : state, union_std_def m.
Proof.
	exact (Map_ind prec_list union_std_def union_std_0 union_std_1 union_std_2).
Qed.

Lemma union_sd :
 forall (s0 s1 : state) (d : preDTA) (c : ad) (tl : term_list),
 mpl_compat s0 s1 ->
 state_reconnait d s0 (app c tl) ->
 state_reconnait d (union_mpl s0 s1) (app c tl) /\
 state_reconnait d (union_mpl s1 s0) (app c tl).
Proof.
	intro. exact (union_std s0).
Qed.

Definition union_s_rpl_def (s : state) : Prop :=
  forall (d : preDTA) (a : ad) (pl : prec_list) (c : ad) (tl : term_list),
  mpl_compat (M1 prec_list a pl) s ->
  state_reconnait d (union_mpl_0 a pl s) (app c tl) ->
  state_reconnait d (M1 prec_list a pl) (app c tl) \/
  state_reconnait d s (app c tl).

Lemma union_s_rpl_0 : union_s_rpl_def (M0 prec_list).
Proof.
	unfold union_s_rpl_def in |- *. intros. simpl in H0. left. assumption.
Qed.

Lemma union_s_rpl_1 :
 forall (a : ad) (a0 : prec_list), union_s_rpl_def (M1 prec_list a a0).
Proof.
	unfold union_s_rpl_def in |- *. intros. simpl in H0. elim (bool_is_true_or_false (Neqb a1 a)); intro; rewrite H1 in H0. inversion H0. simpl in H6. elim (bool_is_true_or_false (Neqb a1 c)); intro; rewrite H8 in H6. inversion H6. rewrite <- H10 in H7.
	cut (liste_reconnait d pl tl \/ liste_reconnait d a0 tl). intro. elim H9; intro.
	left. rewrite (Neqb_complete a1 c H8). apply (rec_st d (M1 prec_list c pl) c tl pl).
	simpl in |- *. rewrite (Neqb_correct c). trivial. assumption. right. rewrite <- (Neqb_complete a1 a H1). rewrite (Neqb_complete a1 c H8). apply (rec_st d (M1 prec_list c a0) c tl a0).
	simpl in |- *. rewrite (Neqb_correct c). trivial. trivial. apply (union_pl_r d pl a0 tl).
	apply (H c pl a0). simpl in |- *. rewrite H8. trivial. simpl in |- *. rewrite <- (Neqb_complete a1 a H1). rewrite H8. trivial.  assumption. inversion H6.
	elim (Ndiscr (Nxor a a1)); intro y. elim y. intros x y0. rewrite y0 in H0. inversion H0.
	rewrite (MapPut1_semantics prec_list x a a1 a0 pl y0 c) in H6.
	elim (bool_is_true_or_false (Neqb a c)); intro; rewrite H8 in H6. right. inversion H6.
	apply (rec_st d (M1 prec_list a l) c tl l). simpl in |- *. rewrite H8. trivial. trivial.
	elim (bool_is_true_or_false (Neqb a1 c)); intro; rewrite H9 in H6. inversion H6.
	left. apply (rec_st d (M1 prec_list a1 l) c tl l). simpl in |- *. rewrite H9. trivial.
	trivial. inversion H6. rewrite (Nxor_comm a a1) in y. rewrite (Nxor_eq_true a1 a y) in H1. inversion H1.
Qed.

Lemma union_s_rpl_2 :
 forall m : state,
 union_s_rpl_def m ->
 forall m0 : state, union_s_rpl_def m0 -> union_s_rpl_def (M2 prec_list m m0).
Proof.
	unfold union_s_rpl_def in |- *. intros. induction  a as [| p]. induction  c as [| p]. simpl in H2.
	cut
  (state_reconnait d (M1 prec_list N0 pl) (app N0 tl) \/
   state_reconnait d m (app N0 tl)). intro. elim H3. intro. left. trivial. intro. right. inversion H4.
	apply (rec_st d (M2 prec_list m m0) N0 tl l). simpl in |- *. assumption. assumption.
	apply (H d N0 pl N0 tl). apply (mpl_compat_sym m (M1 prec_list N0 pl)).
	exact
  (mpl_compat_3 m m0 pl
     (mpl_compat_sym (M1 prec_list N0 pl) (M2 prec_list m m0) H1)).
	inversion H2. simpl in H7. exact (rec_st d (union_mpl_0 N0 pl m) N0 tl l H7 H8).
	induction  p as [p Hrecp| p Hrecp| ]. simpl in H2. inversion H2. right. apply (rec_st d (M2 prec_list m m0) (Npos (xI p)) tl l). simpl in |- *. simpl in H7. assumption. assumption. simpl in H2.
	cut
  (state_reconnait d (M1 prec_list N0 pl) (app (Npos p) tl) \/
   state_reconnait d m (app (Npos p) tl)). intro. elim H3. intro. inversion H4. simpl in H9. inversion H9.
	intro. right. inversion H4. apply (rec_st d (M2 prec_list m m0) (Npos (xO p)) tl l).
	simpl in |- *. assumption. assumption. apply (H d N0 pl (Npos p) tl). apply (mpl_compat_sym m (M1 prec_list N0 pl)). exact
  (mpl_compat_3 m m0 pl
     (mpl_compat_sym (M1 prec_list N0 pl) (M2 prec_list m m0) H1)). inversion H2. simpl in H7. exact (rec_st d (union_mpl_0 N0 pl m) (Npos p) tl l H7 H8). simpl in H2. inversion H2. right. simpl in H7.
	apply (rec_st d (M2 prec_list m m0) (Npos 1) tl l). simpl in |- *. assumption. assumption.
	induction  p as [p Hrecp| p Hrecp| ]. induction  c as [| p0]. simpl in H2. inversion H2. right. apply (rec_st d (M2 prec_list m m0) N0 tl l). simpl in |- *. simpl in H7. assumption. assumption.
	simpl in H2. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. cut
  (state_reconnait d (M1 prec_list (Npos p) pl) (app (Npos p0) tl) \/
   state_reconnait d m0 (app (Npos p0) tl)). intro. elim H3; intro.
	inversion H4. left. apply (rec_st d (M1 prec_list (Npos (xI p)) pl) (Npos (xI p0)) tl l).
	simpl in |- *. simpl in H9. assumption. assumption. right. inversion H4. apply (rec_st d (M2 prec_list m m0) (Npos (xI p0)) tl l). simpl in |- *. assumption. assumption.
	apply (H0 d (Npos p) pl (Npos p0) tl). apply (mpl_compat_sym m0 (M1 prec_list (Npos p) pl)).
	apply (mpl_compat_6 m m0 pl p). exact (mpl_compat_sym _ _ H1). inversion H2.
	simpl in H7. simpl in |- *. apply (rec_st d (union_mpl_0 (Npos p) pl m0) (Npos p0) tl l).
	assumption. assumption. inversion H2. simpl in H7. right. apply (rec_st d (M2 prec_list m m0) (Npos (xO p0)) tl l). simpl in |- *. assumption. assumption. simpl in H2.
	cut
  (state_reconnait d (M1 prec_list (Npos p) pl) (app N0 tl) \/
   state_reconnait d m0 (app N0 tl)). intro. elim H3; intro. left. inversion H4. simpl in H9. inversion H9.
	right. inversion H4. apply (rec_st d (M2 prec_list m m0) (Npos 1) tl l). simpl in |- *.
	assumption. assumption. apply (H0 d (Npos p) pl N0 tl). apply (mpl_compat_sym m0 (M1 prec_list (Npos p) pl)). apply (mpl_compat_6 m m0 pl p). exact
  (mpl_compat_sym (M1 prec_list (Npos (xI p)) pl) (M2 prec_list m m0) H1). inversion H2. simpl in H7.
	exact (rec_st d (union_mpl_0 (Npos p) pl m0) N0 tl l H7 H8). induction  c as [| p0]. simpl in H2.
	cut
  (state_reconnait d (M1 prec_list (Npos p) pl) (app N0 tl) \/
   state_reconnait d m (app N0 tl)). intro. elim H3; intros. inversion H4. inversion H9. right. inversion H4.
	apply (rec_st d (M2 prec_list m m0) N0 tl l). simpl in |- *. assumption. assumption.
	apply (H d (Npos p) pl N0 tl). apply (mpl_compat_sym m (M1 prec_list (Npos p) pl)).
	apply (mpl_compat_5 m m0 pl p). exact
  (mpl_compat_sym (M1 prec_list (Npos (xO p)) pl) (M2 prec_list m m0) H1). inversion H2. apply (rec_st d (union_mpl_0 (Npos p) pl m) N0 tl l).
	simpl in |- *. simpl in H7. assumption. assumption. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. simpl in H2. inversion H2. right.
	apply (rec_st d (M2 prec_list m m0) (Npos (xI p0)) tl l). simpl in |- *. simpl in H7. assumption.
	assumption. simpl in H2. cut
  (state_reconnait d (M1 prec_list (Npos p) pl) (app (Npos p0) tl) \/
   state_reconnait d m (app (Npos p0) tl)). intro. elim H3; intro. inversion H4. simpl in H9.
	left. apply (rec_st d (M1 prec_list (Npos (xO p)) pl) (Npos (xO p0)) tl l). simpl in |- *. assumption.
	assumption. right. inversion H4. apply (rec_st d (M2 prec_list m m0) (Npos (xO p0)) tl l).
	simpl in |- *. assumption. assumption. apply (H d (Npos p) pl (Npos p0) tl). apply (mpl_compat_sym m (M1 prec_list (Npos p) pl)). exact (mpl_compat_5 m m0 pl p (mpl_compat_sym _ _ H1)).
	inversion H2. apply (rec_st d (union_mpl_0 (Npos p) pl m) (Npos p0) tl l). simpl in H7.
	assumption. assumption. simpl in H2. inversion H2. right. apply (rec_st d (M2 prec_list m m0) (Npos 1) tl l). simpl in |- *. simpl in H7. assumption. assumption. induction  c as [| p].
	simpl in H2. right. inversion H2. apply (rec_st d (M2 prec_list m m0) N0 tl l).
	simpl in |- *. simpl in H7. assumption. assumption. induction  p as [p Hrecp| p Hrecp| ]. simpl in H2.
	cut
  (state_reconnait d (M1 prec_list N0 pl) (app (Npos p) tl) \/
   state_reconnait d m0 (app (Npos p) tl)). intro. elim H3; intros. left. inversion H4. simpl in H9. inversion H9.
	right. inversion H4. apply (rec_st d (M2 prec_list m m0) (Npos (xI p)) tl l). simpl in |- *.
	assumption. assumption. apply (H0 d N0 pl (Npos p) tl). apply (mpl_compat_sym m0 (M1 prec_list N0 pl)). exact (mpl_compat_4 m m0 pl (mpl_compat_sym _ _ H1)). 
	inversion H2. apply (rec_st d (union_mpl_0 N0 pl m0) (Npos p) tl l). simpl in |- *. simpl in H7.
	assumption. assumption. simpl in H2. inversion H2. right. apply (rec_st d (M2 prec_list m m0) (Npos (xO p)) tl l). simpl in |- *. simpl in H7. assumption. assumption. simpl in H2.
	cut
  (state_reconnait d (M1 prec_list N0 pl) (app N0 tl) \/
   state_reconnait d m0 (app N0 tl)). intro. elim H3; intros. left. inversion H4. apply (rec_st d (M1 prec_list (Npos 1) pl) (Npos 1) tl l). simpl in |- *. assumption. assumption. right.
	inversion H4. apply (rec_st d (M2 prec_list m m0) (Npos 1) tl l). simpl in |- *.
	assumption. assumption. apply (H0 d N0 pl N0 tl). apply (mpl_compat_sym m0 (M1 prec_list N0 pl)). exact (mpl_compat_4 m m0 pl (mpl_compat_sym _ _ H1)).
	inversion H2. simpl in |- *. simpl in H7. apply (rec_st d (union_mpl_0 N0 pl m0) N0 tl l).
	simpl in |- *. assumption. assumption.
Qed.

Lemma union_s_rpl_3 : forall m : state, union_s_rpl_def m.
Proof.
	exact
  (Map_ind prec_list union_s_rpl_def union_s_rpl_0 union_s_rpl_1
     union_s_rpl_2).
Qed.

Lemma union_s_rpl :
 forall (s : state) (d : preDTA) (a : ad) (pl : prec_list) 
   (c : ad) (tl : term_list),
 mpl_compat (M1 prec_list a pl) s ->
 state_reconnait d (union_mpl_0 a pl s) (app c tl) ->
 state_reconnait d (M1 prec_list a pl) (app c tl) \/
 state_reconnait d s (app c tl).
Proof.
	intro. exact (union_s_rpl_3 s).
Qed.

Definition union_str_def (s0 : state) : Prop :=
  forall (s1 : state) (d : preDTA) (c : ad) (tl : term_list),
  mpl_compat s0 s1 ->
  state_reconnait d (union_mpl s0 s1) (app c tl) \/
  state_reconnait d (union_mpl s1 s0) (app c tl) ->
  state_reconnait d s0 (app c tl) \/ state_reconnait d s1 (app c tl).

Lemma union_str_0 : union_str_def (M0 prec_list).
Proof.
	unfold union_str_def in |- *. intros. induction  s1 as [| a a0| s1_1 Hrecs1_1 s1_0 Hrecs1_0]. elim H0; intros.
	inversion H1. inversion H6. inversion H1. inversion H6.
	simpl in H0. right. elim H0; intro; assumption. simpl in H0. right.
	elim H0; intro. assumption. assumption.
Qed.

Lemma union_str_1 :
 forall (a : ad) (a0 : prec_list), union_str_def (M1 prec_list a a0).
Proof.
	unfold union_str_def in |- *. intros. induction  s1 as [| a1 a2| s1_1 Hrecs1_1 s1_0 Hrecs1_0]. simpl in H0. left.
	elim H0; intro; assumption. unfold union_mpl in H0. elim H0; intros.
	elim
  (union_s_rpl (M1 prec_list a a0) d a1 a2 c tl (mpl_compat_sym _ _ H) H1);
  intro. right. assumption. left. assumption. elim (union_s_rpl (M1 prec_list a1 a2) d a a0 c tl H H1); intro. left. trivial. right.
	trivial. elim H0; intros. elim (union_s_rpl (M2 prec_list s1_1 s1_0) d a a0 c tl H H1). intro. left. trivial. right. trivial.
	exact (union_s_rpl (M2 prec_list s1_1 s1_0) d a a0 c tl H H1).
Qed.

Lemma union_str_2 :
 forall m : state,
 union_str_def m ->
 forall m0 : state, union_str_def m0 -> union_str_def (M2 prec_list m m0).
Proof.
	unfold union_str_def in |- *. intros. induction  s1 as [| a a0| s1_1 Hrecs1_1 s1_0 Hrecs1_0]. simpl in H2.
	elim H2; intro; left; assumption. unfold union_mpl in H2. 
	elim H2; intro. elim
  (union_s_rpl (M2 prec_list m m0) d a a0 c tl (mpl_compat_sym _ _ H1) H3);
  intro. right. trivial. left. trivial.
	elim
  (union_s_rpl (M2 prec_list m m0) d a a0 c tl (mpl_compat_sym _ _ H1) H3);
  intro. right. trivial. left. trivial. cut (mpl_compat m s1_1).
	cut (mpl_compat m0 s1_0). intros. induction  c as [| p]. simpl in H2.
	cut
  (state_reconnait d (union_mpl m s1_1) (app N0 tl) \/
   state_reconnait d (union_mpl s1_1 m) (app N0 tl)). intro. elim (H s1_1 d N0 tl H4 H5); intro. inversion H6. left. apply (rec_st d (M2 prec_list m m0) N0 tl l).
	simpl in |- *. assumption. assumption. right. inversion H6. apply (rec_st d (M2 prec_list s1_1 s1_0) N0 tl l). simpl in |- *. assumption. assumption. elim H2.
	intro. inversion H5. left. apply (rec_st d (union_mpl m s1_1) N0 tl l).
	simpl in H10. assumption. assumption. intro. right. inversion H5.
	apply (rec_st d (union_mpl s1_1 m) N0 tl l). simpl in H10. assumption.
	assumption.  induction  p as [p Hrecp| p Hrecp| ]. simpl in H2. clear Hrecp. clear Hrecs1_1. 
	clear Hrecs1_0. cut
  (state_reconnait d (union_mpl m0 s1_0) (app (Npos p) tl) \/
   state_reconnait d (union_mpl s1_0 m0) (app (Npos p) tl)). intro. 
	elim (H0 s1_0 d (Npos p) tl H3 H5). intro. left. inversion H6.
	apply (rec_st d (M2 prec_list m m0) (Npos (xI p)) tl l). simpl in |- *. assumption.
	assumption. intro. inversion H6. right. apply (rec_st d (M2 prec_list s1_1 s1_0) (Npos (xI p)) tl l). simpl in |- *. assumption. assumption. elim H2; intro.
	left. inversion H5. apply (rec_st d (union_mpl m0 s1_0) (Npos p) tl l).
	simpl in H10. assumption. assumption. inversion H5. right.
	apply (rec_st d (union_mpl s1_0 m0) (Npos p) tl l). simpl in H10. simpl in |- *. 
	assumption. assumption. clear Hrecp. clear Hrecs1_1. clear Hrecs1_0.
	simpl in H2. cut
  (state_reconnait d (union_mpl m s1_1) (app (Npos p) tl) \/
   state_reconnait d (union_mpl s1_1 m) (app (Npos p) tl)). intro.
	elim (H s1_1 d (Npos p) tl H4 H5). intro. left. inversion H6.
	apply (rec_st d (M2 prec_list m m0) (Npos (xO p)) tl l). simpl in |- *.
	assumption.  assumption. intro. right. inversion H6.
	apply (rec_st d (M2 prec_list s1_1 s1_0) (Npos (xO p)) tl l). simpl in |- *.
	assumption. assumption. elim H2; intro; inversion H5. left.
	apply (rec_st d (union_mpl m s1_1) (Npos p) tl l). simpl in H10. assumption.
	assumption. right. apply (rec_st d (union_mpl s1_1 m) (Npos p) tl l). 
	simpl in H10. assumption. assumption. simpl in H2. cut
  (state_reconnait d (union_mpl m0 s1_0) (app N0 tl) \/
   state_reconnait d (union_mpl s1_0 m0) (app N0 tl)). intro. elim (H0 s1_0 d N0 tl H3 H5); intro. inversion H6.
	left. apply (rec_st d (M2 prec_list m m0) (Npos 1) tl l). simpl in |- *. assumption.
	assumption. inversion H6. right. apply (rec_st d (M2 prec_list s1_1 s1_0) (Npos 1) tl l). simpl in |- *. assumption. assumption. elim H2; intro; inversion H5.
	left. simpl in H10. apply (rec_st d (union_mpl m0 s1_0) N0 tl l). assumption.
	assumption. right. apply (rec_st d (union_mpl s1_0 m0) N0 tl l). simpl in H10.
	assumption. assumption. exact (mpl_compat_2 m m0 s1_1 s1_0 H1).
	exact (mpl_compat_1 m m0 s1_1 s1_0 H1).
Qed.

Lemma union_str_3 : forall m : state, union_str_def m.
Proof.
	exact (Map_ind prec_list union_str_def union_str_0 union_str_1 union_str_2).
Qed.

Lemma union_str :
 forall (s0 s1 : state) (d : preDTA) (c : ad) (tl : term_list),
 mpl_compat s0 s1 ->
 state_reconnait d (union_mpl s0 s1) (app c tl) \/
 state_reconnait d (union_mpl s1 s0) (app c tl) ->
 state_reconnait d s0 (app c tl) \/ state_reconnait d s1 (app c tl).
Proof.
	intro. exact (union_str_3 s0).
Qed.

Lemma union_state :
 forall (s0 s1 : state) (d : preDTA) (t : term),
 mpl_compat s0 s1 ->
 (state_reconnait d (union_mpl s0 s1) t <->
  state_reconnait d s0 t \/ state_reconnait d s1 t).
Proof.
	intros. split. intro. induction  t as (a, t). apply (union_str s0 s1 d a t H).
	left. trivial. intro. elim H0; intro. induction  t as (a, t).
	elim (union_sd s0 s1 d a t H H1). intros. assumption. induction  t as (a, t).
	elim (union_sd s1 s0 d a t (mpl_compat_sym _ _ H) H1). intros.
	assumption.
Qed.

Definition new_preDTA_ad : preDTA -> ad := ad_alloc_opt state.

(* invariant de reconnaissance lors de l'ajout d'un état, sens direct *)

Definition new_state_insd_def_dta (d : preDTA) (a0 : ad) 
  (t0 : term) (pr : reconnaissance d a0 t0) :=
  forall (a : ad) (s : state),
  MapGet state d a = None -> reconnaissance (MapPut state d a s) a0 t0.

Definition new_state_insd_def_st (d : preDTA) (s0 : state) 
  (t0 : term) (pr : state_reconnait d s0 t0) :=
  forall (a : ad) (s : state),
  MapGet state d a = None -> state_reconnait (MapPut state d a s) s0 t0.

Definition new_state_insd_def_lst (d : preDTA) (pl0 : prec_list)
  (tl0 : term_list) (pr : liste_reconnait d pl0 tl0) :=
  forall (a : ad) (s : state),
  MapGet state d a = None ->
  liste_reconnait (MapPut state d a s) pl0 tl0.

Lemma new_state_insd_0 :
 forall (d : preDTA) (a : ad) (t : term) (ladj : state)
   (e : MapGet state d a = Some ladj) (s : state_reconnait d ladj t),
 new_state_insd_def_st d ladj t s ->
 new_state_insd_def_dta d a t (rec_dta d a t ladj e s).
Proof.
	unfold new_state_insd_def_dta in |- *. unfold new_state_insd_def_st in |- *.
	intros. apply (rec_dta (MapPut state d a0 s0) a t ladj).
	rewrite (MapPut_semantics state d a0 s0 a).
	elim (bool_is_true_or_false (Neqb a0 a)); intros.
	rewrite (Neqb_complete a0 a H1) in H0. rewrite H0 in e.
	inversion e. rewrite H1. assumption. exact (H a0 s0 H0).
Qed.

Lemma new_state_insd_1 :
 forall (d : preDTA) (s : state) (c : ad) (tl : term_list) 
   (l : prec_list) (e : MapGet prec_list s c = Some l)
   (l0 : liste_reconnait d l tl),
 new_state_insd_def_lst d l tl l0 ->
 new_state_insd_def_st d s (app c tl) (rec_st d s c tl l e l0).
Proof.
	unfold new_state_insd_def_lst in |- *. unfold new_state_insd_def_st in |- *.
	intros. apply (rec_st (MapPut state d a s0) s c tl l).
	assumption. exact (H a s0 H0).
Qed.

Lemma new_state_insd_2 :
 forall d : preDTA, new_state_insd_def_lst d prec_empty tnil (rec_empty d).
Proof.
	unfold new_state_insd_def_lst in |- *. intros. exact (rec_empty (MapPut state d a s)).
Qed.

Lemma new_state_insd_3 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list) (r : reconnaissance d a hd),
 new_state_insd_def_dta d a hd r ->
 forall l : liste_reconnait d la tl,
 new_state_insd_def_lst d la tl l ->
 new_state_insd_def_lst d (prec_cons a la ls) (tcons hd tl)
   (rec_consi d a la ls hd tl r l).
Proof.
	unfold new_state_insd_def_lst in |- *. unfold new_state_insd_def_dta in |- *.
	intros. apply (rec_consi (MapPut state d a0 s) a la ls hd tl).
	exact (H a0 s H1). exact (H0 a0 s H1).
Qed.

Lemma new_state_insd_4 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list) (l : liste_reconnait d ls (tcons hd tl)),
 new_state_insd_def_lst d ls (tcons hd tl) l ->
 new_state_insd_def_lst d (prec_cons a la ls) (tcons hd tl)
   (rec_consn d a la ls hd tl l).
Proof.
	unfold new_state_insd_def_lst in |- *. intros.
	exact (rec_consn (MapPut state d a0 s) a la ls hd tl (H a0 s H0)).
Qed.

Lemma new_state_insd_5 :
 forall (p : preDTA) (a : ad) (t : term) (r : reconnaissance p a t),
 new_state_insd_def_dta p a t r.
Proof.
	exact
  (mreconnaissance_ind new_state_insd_def_dta new_state_insd_def_st
     new_state_insd_def_lst new_state_insd_0 new_state_insd_1
     new_state_insd_2 new_state_insd_3 new_state_insd_4).
Qed.

Lemma new_state_ins_d :
 forall (d : preDTA) (a : ad) (s : state) (a0 : ad) (t : term),
 reconnaissance d a0 t ->
 MapGet state d a = None -> reconnaissance (MapPut state d a s) a0 t.
Proof.
	intros. exact (new_state_insd_5 d a0 t H a s H0).
Qed.

(* invariant de reconnaissance lors de l'ajout d'un état, sens réciproque *)

Definition new_state_insr_def_dta (d0 : preDTA) (a0 : ad) 
  (t0 : term) (pr : reconnaissance d0 a0 t0) :=
  forall (d : preDTA) (a : ad) (s : state),
  preDTA_ref_ok d ->
  d0 = MapPut state d a s ->
  MapGet state d a = None -> a <> a0 -> reconnaissance d a0 t0.

Definition new_state_insr_def_st (d0 : preDTA) (s0 : state) 
  (t0 : term) (pr : state_reconnait d0 s0 t0) :=
  forall (d : preDTA) (a : ad) (s : state),
  preDTA_ref_ok d ->
  state_in_dta_diff d0 s0 a ->
  d0 = MapPut state d a s ->
  MapGet state d a = None -> state_reconnait d s0 t0.

Definition new_state_insr_def_lst (d0 : preDTA) (pl0 : prec_list)
  (tl0 : term_list) (pr : liste_reconnait d0 pl0 tl0) :=
  forall (d : preDTA) (a : ad) (s : state),
  preDTA_ref_ok d ->
  d0 = MapPut state d a s ->
  MapGet state d a = None ->
  prec_in_dta_diff_cont d0 pl0 a ->
  liste_reconnait d pl0 tl0 /\ prec_in_dta_diff_cont d pl0 a.

Lemma new_state_insr_0 :
 forall (d : preDTA) (a : ad) (t : term) (ladj : state)
   (e : MapGet state d a = Some ladj) (s : state_reconnait d ladj t),
 new_state_insr_def_st d ladj t s ->
 new_state_insr_def_dta d a t (rec_dta d a t ladj e s).
Proof.
	unfold new_state_insr_def_st in |- *. unfold new_state_insr_def_dta in |- *.
	intros. apply (rec_dta d0 a t ladj). rewrite H1 in e.
	rewrite (MapPut_semantics state d0 a0 s0) in e.
	elim (bool_is_true_or_false (Neqb a0 a)); intro.
	elim (H3 (Neqb_complete _ _ H4)). rewrite H4 in e.
	assumption. apply (H d0 a0 s0). assumption.
	unfold state_in_dta_diff in |- *. split with a. split; assumption.
	assumption. assumption.
Qed.

Lemma new_state_insr_1 :
 forall (d : preDTA) (s : state) (c : ad) (tl : term_list) 
   (l : prec_list) (e : MapGet prec_list s c = Some l)
   (l0 : liste_reconnait d l tl),
 new_state_insr_def_lst d l tl l0 ->
 new_state_insr_def_st d s (app c tl) (rec_st d s c tl l e l0).
Proof.
	unfold new_state_insr_def_lst in |- *. intros. 	unfold new_state_insr_def_st in |- *. 
	intros. cut (prec_in_dta_diff_cont d l a). intro. elim (H d0 a s0 H0 H2 H3 H4). intros. apply (rec_st d0 s c tl l). assumption. assumption.
	unfold prec_in_dta_diff_cont in |- *. split with s. elim H1. intros.
	split with x. elim H4; intros. split with c. split with l. split.
	assumption. split. assumption. split. exact (prec_id _). assumption.
Qed.

Lemma new_state_insr_2 :
 forall d : preDTA, new_state_insr_def_lst d prec_empty tnil (rec_empty d).
Proof.
	intros. unfold new_state_insr_def_lst in |- *. intros. split.
	exact (rec_empty d0). unfold prec_in_dta_diff_cont in |- *.
	unfold prec_in_dta_diff_cont in H1. elim H1. intros.
	elim H2. intros. elim H3. intros. elim H4. intros. elim H5.
	intros. elim H6. intros. elim H8. intros. elim H10. intros.
	split with x. split with x0. split with x1. split with x2.
	split. simpl in H7. rewrite H0 in H7.
	rewrite (MapPut_semantics state d0 a s) in H7.
	elim (bool_is_true_or_false (Neqb a x0)); intro.
	elim (H12 (Neqb_complete _ _ H13)). rewrite H13 in H7.
	assumption. split. assumption. split; assumption.
Qed.

Lemma new_state_insr_3 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list) (r : reconnaissance d a hd),
 new_state_insr_def_dta d a hd r ->
 forall l : liste_reconnait d la tl,
 new_state_insr_def_lst d la tl l ->
 new_state_insr_def_lst d (prec_cons a la ls) (tcons hd tl)
   (rec_consi d a la ls hd tl r l).
Proof.
	unfold new_state_insr_def_lst in |- *. unfold new_state_insr_def_dta in |- *.
	intros. split. apply (rec_consi d0 a la ls hd tl). cut (a0 <> a).
	intro. exact (H d0 a0 s H1 H2 H3 H5). unfold prec_in_dta_diff_cont in H4. unfold preDTA_ref_ok in H1. elim H4. intros. elim H5. intros.
	elim H6. intros. elim H7. intros. elim H8. intros. elim H10. intros.
	cut (MapGet state d0 x0 = Some x). cut (prec_occur x2 a).
	intros. elim (H1 x0 x x1 x2 a H14 H11 H13). intros. elim (classic (a0 = a)). intro. rewrite <- H16 in H15. rewrite H15 in H3. inversion H3.
	intro. assumption. elim H12. intros. exact (prec_occur_1 a la ls x2 H13). rewrite H2 in H9. rewrite (MapPut_semantics state d0 a0 s) in H9. elim (bool_is_true_or_false (Neqb a0 x0)). intro. elim H12.
	intros. elim (H15 (Neqb_complete _ _ H13)). intros. rewrite H13 in H9.
	assumption. unfold prec_in_dta_diff_cont in H4. elim H4. intros. 
	elim H5. intros. elim H6. intros. elim H7. intros. elim H8. intros.
	elim H10. intros. elim H12. intros. cut (prec_in_dta_diff_cont d la a0). intro. elim (H0 d0 a0 s H1 H2 H3 H15). intros. assumption.
	unfold prec_in_dta_diff_cont in |- *. split with x. split with x0. split with x1. split with x2. split. assumption. split. assumption.
	split. exact (prec_contained_0 _ _ _ _ H13). assumption. elim H4.
	intros. elim H5. intros. elim H6. intros. elim H7. intros. elim H8.
	intros. elim H10. intros. elim H12. intros. rewrite H2 in H9.
	rewrite (MapPut_semantics state d0 a0 s) in H9.
	elim (bool_is_true_or_false (Neqb a0 x0)); intro. elim (H14 (Neqb_complete _ _ H15)). rewrite H15 in H9. split with x. 
	split with x0. split with x1. split with x2. split. assumption.
	split. assumption. split; assumption.
Qed.

Lemma new_state_insr_4 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list) (l : liste_reconnait d ls (tcons hd tl)),
 new_state_insr_def_lst d ls (tcons hd tl) l ->
 new_state_insr_def_lst d (prec_cons a la ls) (tcons hd tl)
   (rec_consn d a la ls hd tl l).
Proof.
	unfold new_state_insr_def_lst in |- *. intros. split. apply (rec_consn d0 a la ls hd tl). cut (prec_in_dta_diff_cont d ls a0). intro. elim (H d0 a0 s H0 H1 H2 H4). intros. assumption. elim H3. intros. elim H4.
	intros. elim H5. intros. elim H6. intros. elim H7. intros. elim H9.
	intros. elim H11. intros. split with x. split with x0. split with x1.
	split with x2. split. assumption. split. assumption.  split.
	exact (prec_contained_1 a la ls x2 H12). assumption. elim H3. intros.
	elim H4. intros. elim H5. intros. elim H6. intros. elim H7. intros.
	elim H9. intros. elim H11. intros. split with x. split with x0. 
	split with x1. split with x2. split. rewrite H1 in H8. rewrite (MapPut_semantics state d0 a0 s) in H8. elim (bool_is_true_or_false (Neqb a0 x0)); intro. elim (H13 (Neqb_complete _ _ H14)). 
	rewrite H14 in H8. assumption. split. assumption. split; assumption.
Qed.

Lemma new_state_insr_5 :
 forall (p : preDTA) (a : ad) (t : term) (r : reconnaissance p a t),
 new_state_insr_def_dta p a t r.
Proof.
	exact
  (mreconnaissance_ind new_state_insr_def_dta new_state_insr_def_st
     new_state_insr_def_lst new_state_insr_0 new_state_insr_1
     new_state_insr_2 new_state_insr_3 new_state_insr_4).
Qed.

Lemma new_state_ins_r :
 forall (d0 : preDTA) (a0 : ad) (t0 : term) (d : preDTA) (a : ad) (s : state),
 reconnaissance d0 a0 t0 ->
 preDTA_ref_ok d ->
 d0 = MapPut state d a s ->
 MapGet state d a = None -> a <> a0 -> reconnaissance d a0 t0.
Proof.
	intros. exact (new_state_insr_5 d0 a0 t0 H d a s H0 H1 H2 H3).
Qed.

(* insertion d'un état *)

Definition insert_state (d : preDTA) (a : ad) (s : state) : preDTA :=
  MapPut state d a s.

Definition insert_main_state_0 (d : preDTA) (a : ad) 
  (s : state) : DTA := dta (insert_state d a s) a.

Definition insert_main_state (d : preDTA) (s : state) : DTA :=
  insert_main_state_0 d (new_preDTA_ad d) s.

Definition insert_ostate (d : preDTA) (a : ad) (o : option state) : preDTA :=
  match o with
  | None => d
  | Some s => MapPut state d a s
  end.

Definition insert_main_ostate_0 (d : preDTA) (a : ad) 
  (o : option state) : DTA := dta (insert_ostate d a o) a.

Lemma insert_ostate_0 :
 forall (d : preDTA) (a : ad) (s : state) (a0 : ad) (t : term),
 preDTA_ref_ok d ->
 MapGet state d a = None ->
 a <> a0 ->
 (reconnaissance d a0 t <->
  reconnaissance (insert_ostate d a (Some s)) a0 t).
Proof.
	intros. split. simpl in |- *. intro. exact (new_state_ins_d d a s a0 t H2 H0). simpl in |- *. intro. exact
  (new_state_ins_r (MapPut state d a s) a0 t d a s H2 H (refl_equal _) H0 H1).
Qed.

Lemma insert_ostate_1 :
 forall (d0 d1 : preDTA) (a0 a1 a : ad) (s s0 s1 s0' s1' : state) (t : term),
 MapGet state d0 a0 = Some s0 ->
 MapGet state d1 a1 = Some s1 ->
 MapGet state (u_merge d0 d1) (uad_conv_0 a0) = Some s0' ->
 MapGet state (u_merge d0 d1) (uad_conv_1 a1) = Some s1' ->
 preDTA_ref_ok (u_merge d0 d1) ->
 MapGet state (u_merge d0 d1) a = None ->
 a <> uad_conv_0 a0 ->
 (reconnaissance d0 a0 t <->
  reconnaissance (insert_ostate (u_merge d0 d1) a (Some s))
    (uad_conv_0 a0) t).
Proof.
	intros. cut
  (reconnaissance (u_merge d0 d1) (uad_conv_0 a0) t <->
   reconnaissance (insert_ostate (u_merge d0 d1) a (Some s))
     (uad_conv_0 a0) t). intro. elim H6. intros. split. intros. apply H7.
	exact (u_merge_2 d0 d1 a0 t H9). intro. exact (u_merge_4 d0 d1 a0 t (H8 H9)). 
	exact (insert_ostate_0 (u_merge d0 d1) a s (uad_conv_0 a0) t H3 H4 H5).
Qed.

Lemma insert_ostate_2 :
 forall (d0 d1 : preDTA) (a0 a1 a : ad) (s s0 s1 s0' s1' : state) (t : term),
 MapGet state d0 a0 = Some s0 ->
 MapGet state d1 a1 = Some s1 ->
 MapGet state (u_merge d0 d1) (uad_conv_0 a0) = Some s0' ->
 MapGet state (u_merge d0 d1) (uad_conv_1 a1) = Some s1' ->
 preDTA_ref_ok (u_merge d0 d1) ->
 MapGet state (u_merge d0 d1) a = None ->
 a <> uad_conv_1 a1 ->
 (reconnaissance d1 a1 t <->
  reconnaissance (insert_ostate (u_merge d0 d1) a (Some s))
    (uad_conv_1 a1) t).
Proof.
	intros. cut
  (reconnaissance (u_merge d0 d1) (uad_conv_1 a1) t <->
   reconnaissance (insert_ostate (u_merge d0 d1) a (Some s))
     (uad_conv_1 a1) t). intro. elim H6. intros. split. intros. apply H7.
	exact (u_merge_3 d0 d1 a1 t H9). intro. exact (u_merge_5 d0 d1 a1 t (H8 H9)). 
	exact (insert_ostate_0 (u_merge d0 d1) a s (uad_conv_1 a1) t H3 H4 H5).
Qed.

Lemma insert_ostate_3 :
 forall (d0 d1 : preDTA) (a0 a1 a : ad) (s s0 s1 s0' s1' : state) (t : term),
 MapGet state d0 a0 = Some s0 ->
 MapGet state d1 a1 = Some s1 ->
 MapGet state (u_merge d0 d1) (uad_conv_0 a0) = Some s0' ->
 MapGet state (u_merge d0 d1) (uad_conv_1 a1) = Some s1' ->
 preDTA_ref_ok (u_merge d0 d1) ->
 MapGet state (u_merge d0 d1) a = None ->
 a <> uad_conv_0 a0 ->
 (reconnaissance (insert_ostate (u_merge d0 d1) a (Some s))
    (uad_conv_0 a0) t <->
  state_reconnait (insert_ostate (u_merge d0 d1) a (Some s)) s0' t).
Proof.
	intros. split. intro. inversion H6. unfold insert_ostate in H7.
	rewrite (MapPut_semantics state (u_merge d0 d1) a s) in H7.
	elim (bool_is_true_or_false (Neqb a (uad_conv_0 a0))); intro.
	elim (H5 (Neqb_complete _ _ H12)). rewrite H12 in H7. induction  t as (a3, t).
	inversion H8. apply (rec_st (insert_ostate (u_merge d0 d1) a (Some s)) s0' a3 t l). rewrite H7 in H1. inversion H1.
	rewrite <- H20. assumption. assumption. intro.
	apply
  (rec_dta (insert_ostate (u_merge d0 d1) a (Some s)) 
     (uad_conv_0 a0) t s0'). unfold insert_ostate in |- *.
	rewrite (MapPut_semantics state (u_merge d0 d1) a s).
	elim (bool_is_true_or_false (Neqb a (uad_conv_0 a0))); intro.
	elim (H5 (Neqb_complete _ _ H7)). rewrite H7. assumption.
	assumption.
Qed.

Lemma insert_ostate_4 :
 forall (d0 d1 : preDTA) (a0 a1 a : ad) (s s0 s1 s0' s1' : state) (t : term),
 MapGet state d0 a0 = Some s0 ->
 MapGet state d1 a1 = Some s1 ->
 MapGet state (u_merge d0 d1) (uad_conv_0 a0) = Some s0' ->
 MapGet state (u_merge d0 d1) (uad_conv_1 a1) = Some s1' ->
 preDTA_ref_ok (u_merge d0 d1) ->
 MapGet state (u_merge d0 d1) a = None ->
 a <> uad_conv_1 a1 ->
 (reconnaissance (insert_ostate (u_merge d0 d1) a (Some s))
    (uad_conv_1 a1) t <->
  state_reconnait (insert_ostate (u_merge d0 d1) a (Some s)) s1' t).
Proof.
	intros. split. intro. inversion H6. unfold insert_ostate in H7.
	rewrite (MapPut_semantics state (u_merge d0 d1) a s) in H7.
	elim (bool_is_true_or_false (Neqb a (uad_conv_1 a1))); intro.
	elim (H5 (Neqb_complete _ _ H12)). rewrite H12 in H7. induction  t as (a3, t).
	inversion H8. apply (rec_st (insert_ostate (u_merge d0 d1) a (Some s)) s1' a3 t l). rewrite H7 in H2. inversion H2.
	rewrite <- H20. assumption. assumption. intro.
	apply
  (rec_dta (insert_ostate (u_merge d0 d1) a (Some s)) 
     (uad_conv_1 a1) t s1'). unfold insert_ostate in |- *.
	rewrite (MapPut_semantics state (u_merge d0 d1) a s).
	elim (bool_is_true_or_false (Neqb a (uad_conv_1 a1))); intro.
	elim (H5 (Neqb_complete _ _ H7)). rewrite H7. assumption.
	assumption.
Qed.

Lemma insert_ostate_5 :
 forall (d0 d1 : preDTA) (a0 a1 a : ad) (s0 s1 s0' s1' : state) (t : term),
 mpl_compat s0' s1' ->
 MapGet state d0 a0 = Some s0 ->
 MapGet state d1 a1 = Some s1 ->
 MapGet state (u_merge d0 d1) (uad_conv_0 a0) = Some s0' ->
 MapGet state (u_merge d0 d1) (uad_conv_1 a1) = Some s1' ->
 preDTA_ref_ok (u_merge d0 d1) ->
 MapGet state (u_merge d0 d1) a = None ->
 a <> uad_conv_0 a0 ->
 a <> uad_conv_1 a1 ->
 (state_reconnait
    (insert_ostate (u_merge d0 d1) a (Some (union_mpl s0' s1')))
    (union_mpl s0' s1') t <->
  state_reconnait
    (insert_ostate (u_merge d0 d1) a (Some (union_mpl s0' s1'))) s0' t \/
  state_reconnait
    (insert_ostate (u_merge d0 d1) a (Some (union_mpl s0' s1'))) s1' t).
Proof.
	intros. exact
  (union_state s0' s1'
     (insert_ostate (u_merge d0 d1) a (Some (union_mpl s0' s1'))) t H).
Qed.

Lemma insert_ostate_6 :
 forall (d0 d1 : preDTA) (a0 a1 a : ad) (s0 s1 s0' s1' : state) (t : term),
 mpl_compat s0' s1' ->
 MapGet state d0 a0 = Some s0 ->
 MapGet state d1 a1 = Some s1 ->
 MapGet state (u_merge d0 d1) (uad_conv_0 a0) = Some s0' ->
 MapGet state (u_merge d0 d1) (uad_conv_1 a1) = Some s1' ->
 preDTA_ref_ok (u_merge d0 d1) ->
 MapGet state (u_merge d0 d1) a = None ->
 a <> uad_conv_0 a0 ->
 a <> uad_conv_1 a1 ->
 (state_reconnait
    (insert_ostate (u_merge d0 d1) a (Some (union_mpl s0' s1')))
    (union_mpl s0' s1') t <->
  reconnaissance
    (insert_ostate (u_merge d0 d1) a (Some (union_mpl s0' s1'))) a t).
Proof.
	intros. split. intro. apply
  (rec_dta (insert_ostate (u_merge d0 d1) a (Some (union_mpl s0' s1')))
     a t (union_mpl s0' s1')).
	unfold insert_ostate in |- *. rewrite (MapPut_semantics state (u_merge d0 d1) a (union_mpl s0' s1')). rewrite (Neqb_correct a). trivial. assumption.
	intro. inversion H8. unfold insert_ostate in H9. rewrite (MapPut_semantics state (u_merge d0 d1) a (union_mpl s0' s1')) in H9. rewrite (Neqb_correct a) in H9. inversion H9. rewrite <- H15 in H10. assumption.
Qed.

Lemma insert_ostate_7 :
 forall (d0 d1 : preDTA) (a0 a1 a : ad) (s0 s1 s0' s1' : state) (t : term),
 mpl_compat s0' s1' ->
 MapGet state d0 a0 = Some s0 ->
 MapGet state d1 a1 = Some s1 ->
 MapGet state (u_merge d0 d1) (uad_conv_0 a0) = Some s0' ->
 MapGet state (u_merge d0 d1) (uad_conv_1 a1) = Some s1' ->
 preDTA_ref_ok (u_merge d0 d1) ->
 MapGet state (u_merge d0 d1) a = None ->
 a <> uad_conv_0 a0 ->
 a <> uad_conv_1 a1 ->
 (reconnaissance d0 a0 t \/ reconnaissance d1 a1 t <->
  reconnaissance
    (insert_ostate (u_merge d0 d1) a (Some (union_mpl s0' s1'))) a t).
Proof.
	intros. elim
  (insert_ostate_1 d0 d1 a0 a1 a (union_mpl s0' s1') s0 s1 s0' s1' t H0 H1 H2
     H3 H4 H5 H6). elim
  (insert_ostate_2 d0 d1 a0 a1 a (union_mpl s0' s1') s0 s1 s0' s1' t H0 H1 H2
     H3 H4 H5 H7). intros. elim
  (insert_ostate_3 d0 d1 a0 a1 a (union_mpl s0' s1') s0 s1 s0' s1' t H0 H1 H2
     H3 H4 H5 H6). elim
  (insert_ostate_4 d0 d1 a0 a1 a (union_mpl s0' s1') s0 s1 s0' s1' t H0 H1 H2
     H3 H4 H5 H7). intros. elim
  (insert_ostate_5 d0 d1 a0 a1 a s0 s1 s0' s1' t H H0 H1 H2 H3 H4 H5 H6 H7). elim
  (insert_ostate_6 d0 d1 a0 a1 a s0 s1 s0' s1' t H H0 H1 H2 H3 H4 H5 H6 H7). intros. split. intro.
	apply H16. apply H19. elim H20; intro. left. exact (H14 (H10 H21)).
	right. exact (H12 (H8 H21)). intro. elim (H18 (H17 H20)). intro.
	left. exact (H11 (H15 H21)). intro. right. exact (H9 (H13 H21)).
Qed.

Lemma insert_ostate_8 :
 forall (d0 d1 : preDTA) (a0 a1 a : ad) (s0 s1 s0' s1' : state) (t : term),
 mpl_compat s0' s1' ->
 MapGet state d0 a0 = Some s0 ->
 MapGet state d1 a1 = Some s1 ->
 MapGet state (u_merge d0 d1) (uad_conv_0 a0) = Some s0' ->
 MapGet state (u_merge d0 d1) (uad_conv_1 a1) = Some s1' ->
 preDTA_ref_ok (u_merge d0 d1) ->
 a = new_preDTA_ad (u_merge d0 d1) ->
 (reconnaissance d0 a0 t \/ reconnaissance d1 a1 t <->
  reconnaissance
    (insert_ostate (u_merge d0 d1) a (Some (union_mpl s0' s1'))) a t).
Proof.
	intros. apply (insert_ostate_7 d0 d1 a0 a1 a s0 s1 s0' s1' t H H0 H1 H2 H3 H4). unfold new_preDTA_ad in H5. rewrite H5.
	exact (ad_alloc_opt_allocates_1 state (u_merge d0 d1)). intro.
	rewrite H5 in H6. rewrite <- H6 in H2. unfold new_preDTA_ad in H2.
	rewrite (ad_alloc_opt_allocates_1 state (u_merge d0 d1)) in H2.
	inversion H2. intro. rewrite H5 in H6. rewrite <- H6 in H3.
	unfold new_preDTA_ad in H3. rewrite (ad_alloc_opt_allocates_1 state (u_merge d0 d1)) in H3. inversion H3.
Qed.

Lemma upl_conv_0_occur :
 forall (pl : prec_list) (a : ad),
 prec_occur (upl_conv_0 pl) (uad_conv_0 a) -> prec_occur pl a.
Proof.
	simple induction pl. intros. simpl in H1. inversion H1.
	rewrite (adcnv_inj0 a a0 H6). exact (prec_hd a0 p p0).
	exact (prec_int0 a a0 p p0 (H a0 H6)). exact (prec_int1 a a0 p p0 (H0 a0 H6)). intros. simpl in H. inversion H.
Qed.

Lemma upl_conv_1_occur :
 forall (pl : prec_list) (a : ad),
 prec_occur (upl_conv_1 pl) (uad_conv_1 a) -> prec_occur pl a.
Proof.
	simple induction pl. intros. simpl in H1. inversion H1.
	rewrite (adcnv_inj1 a a0 H6). exact (prec_hd a0 p p0).
	exact (prec_int0 a a0 p p0 (H a0 H6)). exact (prec_int1 a a0 p p0 (H0 a0 H6)). intros. simpl in H. inversion H.
Qed.

Lemma upl_conv_0_occur_in_img :
 forall (pl : prec_list) (a : ad),
 prec_occur (upl_conv_0 pl) a -> exists b : ad, a = uad_conv_0 b.
Proof.
	simple induction pl. intros. simpl in H1. inversion H1. split with a.
	trivial. elim (H a0 H6). intros. split with x. trivial.
	elim (H0 a0 H6). intros. split with x. trivial. intros.
	inversion H.
Qed.

Lemma upl_conv_1_occur_in_img :
 forall (pl : prec_list) (a : ad),
 prec_occur (upl_conv_1 pl) a -> exists b : ad, a = uad_conv_1 b.
Proof.
	simple induction pl. intros. simpl in H1. inversion H1. split with a.
	trivial. elim (H a0 H6). intros. split with x. trivial.
	elim (H0 a0 H6). intros. split with x. trivial. intros.
	inversion H.
Qed.

Lemma u_conv_0_ref_ok :
 forall d : preDTA, preDTA_ref_ok d -> preDTA_ref_ok (udta_conv_0 d).
Proof.
	unfold preDTA_ref_ok in |- *. intros. elim (u_conv_0_invar_8 d a s H0).
	intros. rewrite H3 in H0. elim (u_conv_0_invar_5 d x s H0).
	intros. elim H4. intros. rewrite H5 in H1. elim (u_conv_0_invar_7 x0 c pl H1). intros. elim H7. intros. rewrite H8 in H2. elim (upl_conv_0_occur_in_img x1 b). intros. elim (H x x0 c x1 x2 H6 H9).
	intros. split with (umpl_conv_0 x3). rewrite H10. 
	exact (u_conv_0_invar_0 d x2 x3 H11). rewrite H10 in H2.
	exact (upl_conv_0_occur x1 x2 H2). assumption.
Qed.

Lemma u_conv_1_ref_ok :
 forall d : preDTA, preDTA_ref_ok d -> preDTA_ref_ok (udta_conv_1 d).
Proof.
	unfold preDTA_ref_ok in |- *. intros. elim (u_conv_1_invar_8 d a s H0).
	intros. rewrite H3 in H0. elim (u_conv_1_invar_5 d x s H0).
	intros. elim H4. intros. rewrite H5 in H1. elim (u_conv_1_invar_7 x0 c pl H1). intros. elim H7. intros. rewrite H8 in H2. elim (upl_conv_1_occur_in_img x1 b). intros. elim (H x x0 c x1 x2 H6 H9).
	intros. split with (umpl_conv_1 x3). rewrite H10. 
	exact (u_conv_1_invar_0 d x2 x3 H11). rewrite H10 in H2.
	exact (upl_conv_1_occur x1 x2 H2). assumption.
Qed.

Lemma u_merge_ref_ok :
 forall d0 d1 : preDTA,
 preDTA_ref_ok d0 -> preDTA_ref_ok d1 -> preDTA_ref_ok (u_merge d0 d1).
Proof.
	unfold preDTA_ref_ok in |- *. intros. elim (adcnv_disj a); intro.
	intros. elim H4; intro. elim (u_conv_0_ref_ok d0 H a s c pl b (u_merge_0r d0 d1 a s H1 x H5) H2 H3). intros. split with x0.
	exact (u_merge_0 d0 d1 b x0 H6). elim (u_conv_1_ref_ok d1 H0 a s c pl b (u_merge_1r d0 d1 a s H1 x H5) H2 H3). intros.
	split with x0. exact (u_merge_1 d0 d1 b x0 H6).
Qed.

Lemma upl_conv_compat_0_0 :
 forall p0 p1 : prec_list,
 pl_compat p0 p1 -> pl_compat (upl_conv_0 p0) (upl_conv_0 p1).
Proof.
	simple induction p0. simple induction p2. intros. unfold pl_compat in |- *.
	right. split. intro. inversion H4. intro. inversion H4.
	intro. inversion H1. elim H2. intros. inversion H3.
	elim H2. intros. elim (H4 (refl_equal prec_empty)).
	simple induction p1. intros. unfold pl_compat in H1. elim H1; intros.
	elim H2. intros; intros. inversion H4. elim H2. intros.
	elim (H3 (refl_equal prec_empty)). intros. simpl in |- *.
	unfold pl_compat in |- *. left. split; trivial.
Qed.

Lemma upl_conv_compat_0_1 :
 forall p0 p1 : prec_list,
 pl_compat p0 p1 -> pl_compat (upl_conv_0 p0) (upl_conv_1 p1).
Proof.
	simple induction p0. simple induction p2. intros. unfold pl_compat in |- *.
	right. split. intro. inversion H4. intro. inversion H4.
	intro. inversion H1. elim H2. intros. inversion H3.
	elim H2. intros. elim (H4 (refl_equal prec_empty)).
	simple induction p1. intros. unfold pl_compat in H1. elim H1; intros.
	elim H2. intros; intros. inversion H4. elim H2. intros.
	elim (H3 (refl_equal prec_empty)). intros. simpl in |- *.
	unfold pl_compat in |- *. left. split; trivial.
Qed.

Lemma upl_conv_compat_1_0 :
 forall p0 p1 : prec_list,
 pl_compat p0 p1 -> pl_compat (upl_conv_1 p0) (upl_conv_0 p1).
Proof.
	intros. exact (pl_compat_sym _ _ (upl_conv_compat_0_1 p1 p0 (pl_compat_sym _ _ H))).
Qed.

Lemma upl_conv_compat_1_1 :
 forall p0 p1 : prec_list,
 pl_compat p0 p1 -> pl_compat (upl_conv_1 p0) (upl_conv_1 p1).
Proof.
	simple induction p0. simple induction p2. intros. unfold pl_compat in |- *.
	right. split. intro. inversion H4. intro. inversion H4.
	intro. inversion H1. elim H2. intros. inversion H3.
	elim H2. intros. elim (H4 (refl_equal prec_empty)).
	simple induction p1. intros. unfold pl_compat in H1. elim H1; intros.
	elim H2. intros; intros. inversion H4. elim H2. intros.
	elim (H3 (refl_equal prec_empty)). intros. simpl in |- *.
	unfold pl_compat in |- *. left. split; trivial.
Qed.

Lemma umpl_conv_0_compat :
 forall s0 s1 : state,
 mpl_compat s0 s1 -> mpl_compat (umpl_conv_0 s0) (umpl_conv_0 s1).
Proof.
	unfold mpl_compat in |- *. intros. elim (u_conv_0_invar_7 s0 c p0).
	elim (u_conv_0_invar_7 s1 c p1). intros. elim H2. elim H3.
	intros. rewrite H4. rewrite H6. apply (upl_conv_compat_0_0 x0 x).
	exact (H c x0 x H5 H7). assumption. assumption.
Qed.

Lemma umpl_conv_1_compat :
 forall s0 s1 : state,
 mpl_compat s0 s1 -> mpl_compat (umpl_conv_1 s0) (umpl_conv_1 s1).
Proof.
	unfold mpl_compat in |- *. intros. elim (u_conv_1_invar_7 s0 c p0).
	elim (u_conv_1_invar_7 s1 c p1). intro. intros. elim H2. elim H3. 
	intros. rewrite H4. rewrite H6. apply (upl_conv_compat_1_1 x0 x).
	exact (H c x0 x H5 H7). assumption. assumption.
Qed.

Lemma umpl_conv_0_1_compat :
 forall s0 s1 : state,
 mpl_compat s0 s1 -> mpl_compat (umpl_conv_0 s0) (umpl_conv_1 s1).
Proof.
	unfold mpl_compat in |- *. intros. elim (u_conv_0_invar_7 s0 c p0 H0).
	elim (u_conv_1_invar_7 s1 c p1). intros. elim H2. elim H3. intros.
	rewrite H4. rewrite H6. apply (upl_conv_compat_0_1 x0 x). 
	exact (H c x0 x H5 H7). assumption.
Qed.

Lemma udta_conv_0_compat :
 forall d : preDTA, dta_correct d -> dta_correct (udta_conv_0 d).
Proof.
	unfold dta_correct in |- *. intros. elim (u_conv_0_invar_8 d a0 s0).
	elim (u_conv_0_invar_8 d a1 s1). intros. rewrite H2 in H1.
	rewrite H3 in H0. elim (u_conv_0_invar_5 d x s1 H1).
	elim (u_conv_0_invar_5 d x0 s0 H0). intros. elim H4. elim H5.
	intros. rewrite H6. rewrite H8. exact (umpl_conv_0_compat x1 x2 (H x1 x2 x0 x H9 H7)). assumption. assumption.
Qed.

Lemma udta_conv_1_compat :
 forall d : preDTA, dta_correct d -> dta_correct (udta_conv_1 d).
Proof.
	unfold dta_correct in |- *. intros. elim (u_conv_1_invar_8 d a0 s0).
	elim (u_conv_1_invar_8 d a1 s1). intros. rewrite H2 in H1.
	rewrite H3 in H0. elim (u_conv_1_invar_5 d x s1 H1).
	elim (u_conv_1_invar_5 d x0 s0 H0). intros. elim H4. elim H5.
	intros. rewrite H6. rewrite H8. exact (umpl_conv_1_compat x1 x2 (H x1 x2 x0 x H9 H7)). assumption. assumption.
Qed.

Lemma udta_conv_0_1_compat :
 forall d0 d1 : preDTA,
 dta_compat d0 d1 -> dta_compat (udta_conv_0 d0) (udta_conv_1 d1).
Proof.
	unfold dta_compat in |- *. intros. elim (u_conv_0_invar_8 d0 a0 s0 H0).
	elim (u_conv_1_invar_8 d1 a1 s1 H1). intros. intros. rewrite H3 in H0.
	rewrite H2 in H1. elim (u_conv_0_invar_5 d0 x0 s0 H0). elim (u_conv_1_invar_5 d1 x s1 H1). intros. elim H4. elim H5. intros.
	rewrite H6. rewrite H8. exact (umpl_conv_0_1_compat x2 x1 (H x2 x1 x0 x H7 H9)).
Qed.

Lemma insert_ostate_9 :
 forall (d0 d1 : preDTA) (a0 a1 a : ad) (s0' s1' : state) (t : term),
 preDTA_ref_ok d0 ->
 preDTA_ref_ok d1 ->
 dta_compat d0 d1 ->
 MapGet state (u_merge d0 d1) (uad_conv_0 a0) = Some s0' ->
 MapGet state (u_merge d0 d1) (uad_conv_1 a1) = Some s1' ->
 a = new_preDTA_ad (u_merge d0 d1) ->
 (reconnaissance d0 a0 t \/ reconnaissance d1 a1 t <->
  reconnaissance
    (insert_ostate (u_merge d0 d1) a (Some (union_mpl s0' s1'))) a t).
Proof.
	intros. elim
  (u_conv_0_invar_5 d0 a0 s0'
     (u_merge_0r d0 d1 (uad_conv_0 a0) s0' H2 a0 (refl_equal _))). elim
  (u_conv_1_invar_5 d1 a1 s1'
     (u_merge_1r d0 d1 (uad_conv_1 a1) s1' H3 a1 (refl_equal _))). intros. elim H5. elim H6. intros.
	cut (mpl_compat s0' s1'). intro. exact
  (insert_ostate_8 d0 d1 a0 a1 a x0 x s0' s1' t H11 H8 H10 H2 H3
     (u_merge_ref_ok d0 d1 H H0) H4). apply
  (udta_conv_0_1_compat d0 d1 H1 s0' s1' (uad_conv_0 a0) (uad_conv_1 a1)). exact (u_merge_0r d0 d1 (uad_conv_0 a0) s0' H2 a0 (refl_equal _)). 
	exact (u_merge_1r d0 d1 (uad_conv_1 a1) s1' H3 a1 (refl_equal _)).
Qed.

Definition insert_main_ostate (d : preDTA) (o : option state) : DTA :=
  insert_main_ostate_0 d (new_preDTA_ad d) o.

Definition union_opt_state (o0 o1 : option state) : 
  option state :=
  match o0, o1 with
  | None, None => None
  | None, Some s1 => Some s1
  | Some s0, None => Some s0
  | Some s0, Some s1 => Some (union_mpl s0 s1)
  end.

Definition union_0 (d : preDTA) (a0 a1 : ad) : option state :=
  union_opt_state (MapGet state d (uad_conv_0 a0))
    (MapGet state d (uad_conv_1 a1)).

Definition union_1 (d : preDTA) (a0 a1 : ad) : DTA :=
  insert_main_ostate d (union_0 d a0 a1).

Definition union (dt0 dt1 : DTA) : DTA :=
  match dt0, dt1 with
  | dta d0 a0, dta d1 a1 => union_1 (u_merge d0 d1) a0 a1
  end.

Lemma union_semantics_0 :
 forall (d0 d1 : DTA) (t : term),
 DTA_main_state_correct d0 ->
 DTA_main_state_correct d1 ->
 DTA_ref_ok d0 ->
 DTA_ref_ok d1 ->
 DTA_compat d0 d1 ->
 (reconnait d0 t \/ reconnait d1 t <-> reconnait (union d0 d1) t).
Proof.
	unfold union in |- *. simple induction d0. simple induction d1. intros. unfold union_1 in |- *.
	unfold union_0 in |- *. elim H. elim H0. intros. unfold DTA_ref_ok in H1.
	unfold DTA_ref_ok in H2. unfold DTA_compat in H3. unfold insert_main_ostate in |- *.
	unfold insert_main_ostate_0 in |- *. unfold reconnait in |- *. rewrite
  (u_merge_0 p p0 (uad_conv_0 a) (umpl_conv_0 x0)
     (u_conv_0_invar_0 p a x0 H5)). rewrite
  (u_merge_1 p p0 (uad_conv_1 a0) (umpl_conv_1 x)
     (u_conv_1_invar_0 p0 a0 x H4)).
	unfold union_opt_state in |- *. apply
  (insert_ostate_9 p p0 a a0 (new_preDTA_ad (u_merge p p0)) 
     (umpl_conv_0 x0) (umpl_conv_1 x) t H1 H2 H3). exact
  (u_merge_0 p p0 (uad_conv_0 a) (umpl_conv_0 x0)
     (u_conv_0_invar_0 p a x0 H5)).
	exact
  (u_merge_1 p p0 (uad_conv_1 a0) (umpl_conv_1 x)
     (u_conv_1_invar_0 p0 a0 x H4)).
	trivial.
Qed.

Lemma union_semantics :
 forall (d0 d1 : DTA) (sigma : signature) (t : term),
 DTA_main_state_correct d0 ->
 DTA_main_state_correct d1 ->
 DTA_ref_ok d0 ->
 DTA_ref_ok d1 ->
 dta_correct_wrt_sign d0 sigma ->
 dta_correct_wrt_sign d1 sigma ->
 (reconnait d0 t \/ reconnait d1 t <-> reconnait (union d0 d1) t).
Proof.
	intros. apply (union_semantics_0 d0 d1 t H H0 H1 H2). exact
  (dta_compatible_compat _ _ (dtas_correct_wrt_sign_compatibles _ _ _ H3 H4)).
Qed.