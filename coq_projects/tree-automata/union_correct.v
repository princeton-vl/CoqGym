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
Require Import union.

(* conservation de l'invariant de compatibilité par rapport à une signature pour l'union *)

Lemma upl_conv_0_correct_wrt_sign_invar :
 forall (p : prec_list) (n : nat),
 pl_tl_length p n -> pl_tl_length (upl_conv_0 p) n.
Proof.
	simple induction p; intros. simpl in |- *. inversion H1. simpl in |- *. exact (pl_tl_S (uad_conv_0 a) (upl_conv_0 p0) n0 (H _ H6)).
	exact
  (pl_tl_propag (uad_conv_0 a) (upl_conv_0 p0) (upl_conv_0 p1) n0 
     (H _ H6) (H0 _ H7)). simpl in |- *. inversion H. exact pl_tl_O.
Qed.

Lemma upl_conv_1_correct_wrt_sign_invar :
 forall (p : prec_list) (n : nat),
 pl_tl_length p n -> pl_tl_length (upl_conv_1 p) n.
Proof.
	simple induction p; intros. simpl in |- *. inversion H1. simpl in |- *. exact (pl_tl_S (uad_conv_1 a) (upl_conv_1 p0) n0 (H _ H6)).
	exact
  (pl_tl_propag (uad_conv_1 a) (upl_conv_1 p0) (upl_conv_1 p1) n0 
     (H _ H6) (H0 _ H7)). simpl in |- *. inversion H. exact pl_tl_O.
Qed.

Lemma umpl_conv_0_correct_wrt_sign_invar_0 :
 forall (s : state) (sigma : signature) (pa : pre_ad),
 state_correct_wrt_sign_with_offset s sigma pa ->
 state_correct_wrt_sign_with_offset (umpl_conv_0 s) sigma pa.
Proof.
	simple induction s. intros. simpl in |- *. exact H. intros. simpl in |- *.
	unfold state_correct_wrt_sign_with_offset in H.
	unfold state_correct_wrt_sign_with_offset in |- *. intros.
	simpl in H0. elim (H a a0). intros. split with x. elim (bool_is_true_or_false (Neqb a a1)); intros; rewrite H2 in H0. inversion H0. elim H1. intros. rewrite (Neqb_complete _ _ H2) in H3. split. exact H3. exact (upl_conv_0_correct_wrt_sign_invar _ _ H5). inversion H0. simpl in |- *. rewrite (Neqb_correct a). 
	reflexivity. intros. unfold state_correct_wrt_sign_with_offset in H1.
	unfold state_correct_wrt_sign_with_offset in |- *. intros. unfold state_correct_wrt_sign_with_offset in H. unfold state_correct_wrt_sign_with_offset in H0. induction  a as [| p0]. simpl in H2.
	elim (H sigma (pre_ad_O pa)) with (a := N0) (p := p). intros.
	split with x. simpl in H3. exact H3. intros. elim (H1 (Ndouble a) p0). intros. split with x. simpl in |- *. exact H4. induction  a as [| p1]; simpl in |- *; exact H3. exact H2. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. elim (H0 sigma (pre_ad_I pa)) with (a := Npos p0) (p := p). intros. split with x. simpl in H3. exact H3.
	intros. elim (H1 (Ndouble_plus_one a) p1). intros. split with x.
	induction  a as [| p2]. simpl in H4. simpl in |- *. exact H4. simpl in H4. simpl in |- *.
	exact H4. induction  a as [| p2]; simpl in |- *; exact H3. simpl in H2. exact H2.
	elim (H sigma (pre_ad_O pa)) with (a := Npos p0) (p := p). intros.
	split with x. simpl in H3. exact H3. intros. elim (H1 (Ndouble a) p1). intros. split with x. induction  a as [| p2]; simpl in H4; simpl in |- *; exact H4. induction  a as [| p2]; simpl in |- *; exact H3. simpl in H2. exact H2.
	elim (H0 sigma (pre_ad_I pa)) with (a := N0) (p := p). intros. split with x. simpl in H3. exact H3. intros. elim (H1 (Ndouble_plus_one a) p0). intros. split with x. induction  a as [| p1]; simpl in |- *; simpl in H4; exact H4. induction  a as [| p1]; simpl in |- *; exact H3. simpl in H2. exact H2.
Qed.

Lemma umpl_conv_0_correct_wrt_sign_invar :
 forall (s : state) (sigma : signature),
 state_correct_wrt_sign s sigma ->
 state_correct_wrt_sign (umpl_conv_0 s) sigma.
Proof.
	unfold state_correct_wrt_sign in |- *. intros. elim
  (umpl_conv_0_correct_wrt_sign_invar_0 s sigma pre_ad_empty)
   with (a := a) (p := p). intros. split with x. simpl in H1. exact H1.
	unfold state_correct_wrt_sign_with_offset in |- *. simpl in |- *. exact H.
	exact H0.
Qed.

Lemma umpl_conv_1_correct_wrt_sign_invar_0 :
 forall (s : state) (sigma : signature) (pa : pre_ad),
 state_correct_wrt_sign_with_offset s sigma pa ->
 state_correct_wrt_sign_with_offset (umpl_conv_1 s) sigma pa.
Proof.
	simple induction s. intros. simpl in |- *. exact H. intros. simpl in |- *.
	unfold state_correct_wrt_sign_with_offset in H.
	unfold state_correct_wrt_sign_with_offset in |- *. intros.
	simpl in H0. elim (H a a0). intros. split with x. elim (bool_is_true_or_false (Neqb a a1)); intros; rewrite H2 in H0. inversion H0. elim H1. intros. rewrite (Neqb_complete _ _ H2) in H3. split. exact H3. exact (upl_conv_1_correct_wrt_sign_invar _ _ H5). inversion H0. simpl in |- *. rewrite (Neqb_correct a). 
	reflexivity. intros. unfold state_correct_wrt_sign_with_offset in H1.
	unfold state_correct_wrt_sign_with_offset in |- *. intros. unfold state_correct_wrt_sign_with_offset in H. unfold state_correct_wrt_sign_with_offset in H0. induction  a as [| p0]. simpl in H2.
	elim (H sigma (pre_ad_O pa)) with (a := N0) (p := p). intros.
	split with x. simpl in H3. exact H3. intros. elim (H1 (Ndouble a) p0). intros. split with x. simpl in |- *. exact H4. induction  a as [| p1]; simpl in |- *; exact H3. exact H2. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. elim (H0 sigma (pre_ad_I pa)) with (a := Npos p0) (p := p). intros. split with x. simpl in H3. exact H3.
	intros. elim (H1 (Ndouble_plus_one a) p1). intros. split with x.
	induction  a as [| p2]. simpl in H4. simpl in |- *. exact H4. simpl in H4. simpl in |- *.
	exact H4. induction  a as [| p2]; simpl in |- *; exact H3. simpl in H2. exact H2.
	elim (H sigma (pre_ad_O pa)) with (a := Npos p0) (p := p). intros.
	split with x. simpl in H3. exact H3. intros. elim (H1 (Ndouble a) p1). intros. split with x. induction  a as [| p2]; simpl in H4; simpl in |- *; exact H4. induction  a as [| p2]; simpl in |- *; exact H3. simpl in H2. exact H2.
	elim (H0 sigma (pre_ad_I pa)) with (a := N0) (p := p). intros. split with x. simpl in H3. exact H3. intros. elim (H1 (Ndouble_plus_one a) p0). intros. split with x. induction  a as [| p1]; simpl in |- *; simpl in H4; exact H4. induction  a as [| p1]; simpl in |- *; exact H3. simpl in H2. exact H2.
Qed.

Lemma umpl_conv_1_correct_wrt_sign_invar :
 forall (s : state) (sigma : signature),
 state_correct_wrt_sign s sigma ->
 state_correct_wrt_sign (umpl_conv_1 s) sigma.
Proof.
	unfold state_correct_wrt_sign in |- *. intros. elim
  (umpl_conv_1_correct_wrt_sign_invar_0 s sigma pre_ad_empty)
   with (a := a) (p := p). intros. split with x. simpl in H1. exact H1.
	unfold state_correct_wrt_sign_with_offset in |- *. simpl in |- *. exact H.
	exact H0.
Qed.

Lemma udta_conv_0_correct_wrt_sign_invar_0 :
 forall (d : preDTA) (sigma : signature),
 predta_correct_wrt_sign d sigma ->
 predta_correct_wrt_sign (udta_conv_0_aux d) sigma.
Proof.
	unfold predta_correct_wrt_sign in |- *. simple induction d. intros. inversion H0.
	intros. simpl in H0. elim (bool_is_true_or_false (Neqb a a1)); intros. rewrite H1 in H0. inversion H0. apply (umpl_conv_0_correct_wrt_sign_invar a0 sigma). apply (H a a0).
	simpl in |- *. rewrite (Neqb_correct a). reflexivity. rewrite H1 in H0.
	inversion H0. intros. simpl in H2. induction  a as [| p]. apply (H sigma) with (a := N0) (s := s). intros. apply (H1 (Ndouble a) s0). 
	induction  a as [| p]; simpl in |- *; exact H3. exact H2. induction  p as [p Hrecp| p Hrecp| ]; simpl in H2.
	apply (H0 sigma) with (a := Npos p) (s := s). intros. apply (H1 (Ndouble_plus_one a) s0). induction  a as [| p0]; simpl in |- *; exact H3. exact H2.
	apply (H sigma) with (a := Npos p) (s := s). intros. apply (H1 (Ndouble a) s0). induction  a as [| p0]; simpl in |- *; exact H3. exact H2. apply (H0 sigma) with (a := N0) (s := s). intros. apply (H1 (Ndouble_plus_one a) s0).
	induction  a as [| p]; simpl in |- *; exact H3. exact H2.
Qed.

Lemma udta_conv_0_correct_wrt_sign_invar :
 forall (d : preDTA) (sigma : signature),
 predta_correct_wrt_sign d sigma ->
 predta_correct_wrt_sign (udta_conv_0 d) sigma.
Proof.
	unfold udta_conv_0 in |- *. intros. unfold predta_correct_wrt_sign in |- *. intros.
	induction  a as [| p]. simpl in H0. exact (udta_conv_0_correct_wrt_sign_invar_0 d sigma H N0 s H0). induction  p as [p Hrecp| p Hrecp| ]; simpl in H0. inversion H0.
	exact (udta_conv_0_correct_wrt_sign_invar_0 d sigma H (Npos p) s H0).
	inversion H0.
Qed.

Lemma udta_conv_1_correct_wrt_sign_invar_0 :
 forall (d : preDTA) (sigma : signature),
 predta_correct_wrt_sign d sigma ->
 predta_correct_wrt_sign (udta_conv_1_aux d) sigma.
Proof.
	unfold predta_correct_wrt_sign in |- *. simple induction d. intros. inversion H0.
	intros. simpl in H0. elim (bool_is_true_or_false (Neqb a a1)); intros. rewrite H1 in H0. inversion H0. apply (umpl_conv_1_correct_wrt_sign_invar a0 sigma). apply (H a a0).
	simpl in |- *. rewrite (Neqb_correct a). reflexivity. rewrite H1 in H0.
	inversion H0. intros. simpl in H2. induction  a as [| p]. apply (H sigma) with (a := N0) (s := s). intros. apply (H1 (Ndouble a) s0). 
	induction  a as [| p]; simpl in |- *; exact H3. exact H2. induction  p as [p Hrecp| p Hrecp| ]; simpl in H2.
	apply (H0 sigma) with (a := Npos p) (s := s). intros. apply (H1 (Ndouble_plus_one a) s0). induction  a as [| p0]; simpl in |- *; exact H3. exact H2.
	apply (H sigma) with (a := Npos p) (s := s). intros. apply (H1 (Ndouble a) s0). induction  a as [| p0]; simpl in |- *; exact H3. exact H2. apply (H0 sigma) with (a := N0) (s := s). intros. apply (H1 (Ndouble_plus_one a) s0).
	induction  a as [| p]; simpl in |- *; exact H3. exact H2.
Qed.

Lemma udta_conv_1_correct_wrt_sign_invar :
 forall (d : preDTA) (sigma : signature),
 predta_correct_wrt_sign d sigma ->
 predta_correct_wrt_sign (udta_conv_1 d) sigma.
Proof.
	unfold udta_conv_1 in |- *. intros. unfold predta_correct_wrt_sign in |- *. intros.
	induction  a as [| p]. simpl in H0. inversion H0. induction  p as [p Hrecp| p Hrecp| ]; simpl in H0.
	exact (udta_conv_1_correct_wrt_sign_invar_0 d sigma H (Npos p) s H0).
	inversion H0. exact (udta_conv_1_correct_wrt_sign_invar_0 d sigma H N0 s H0).
Qed.

Lemma umerge_correct_wrt_sign_invar :
 forall (d0 d1 : preDTA) (sigma : signature),
 predta_correct_wrt_sign d0 sigma ->
 predta_correct_wrt_sign d1 sigma ->
 predta_correct_wrt_sign (u_merge d0 d1) sigma.
Proof.
	unfold predta_correct_wrt_sign in |- *. intros. elim (adcnv_disj a).
	intros. elim H2; intros. elim (u_conv_0_invar_5 d0 x s). intros.
	elim H4. intros. apply (udta_conv_0_correct_wrt_sign_invar d0 sigma H a s). exact (u_merge_0r d0 d1 a s H1 x H3). rewrite <- H3.
	exact (u_merge_0r d0 d1 a s H1 x H3). elim (u_conv_1_invar_5 d1 x s).
	intros. elim H4. intros. apply (udta_conv_1_correct_wrt_sign_invar d1 sigma H0 a s). exact (u_merge_1r d0 d1 a s H1 x H3). rewrite <- H3. exact (u_merge_1r d0 d1 a s H1 x H3).
Qed.

Lemma union_pl_correct_wrt_sign_invar :
 forall (p0 p1 : prec_list) (n : nat),
 pl_tl_length p0 n -> pl_tl_length p1 n -> pl_tl_length (union_pl p0 p1) n.
Proof.
	simple induction p0. intros. simpl in |- *. inversion H1. simpl in |- *. rewrite <- H4 in H2. exact (pl_tl_propag a p p2 n0 H7 H2). rewrite <- H5 in H2. exact (pl_tl_propag a p (union_pl p1 p2) n0 H7 (H0 p2 (S n0) H8 H2)). intros. inversion H. rewrite <- H2 in H0. inversion H0. simpl in |- *. exact pl_tl_O.
Qed.

Lemma union_mpl_correct_wrt_sign_invar_0 :
 forall (s : state) (a : ad) (p : prec_list) (pa : pre_ad)
   (sigma : signature),
 state_correct_wrt_sign_with_offset s sigma pa ->
 state_correct_wrt_sign_with_offset (M1 prec_list a p) sigma pa ->
 state_correct_wrt_sign_with_offset (union_mpl_0 a p s) sigma pa.
Proof.
	simple induction s. unfold state_correct_wrt_sign_with_offset in |- *. intros.
	exact (H0 _ _ H1). unfold state_correct_wrt_sign_with_offset in |- *.
	intros. simpl in H1. elim (bool_is_true_or_false (Neqb a1 a)); intros; rewrite H2 in H1. elim (H a a0). intros. elim (H0 a p).
	intros. elim H3. elim H4. intros. simpl in H1. elim (bool_is_true_or_false (Neqb a1 a2)); intros; rewrite H9 in H1;
  inversion H1. rewrite H7 in H5. inversion H5. split with x.
	rewrite <- H12 in H6. split. rewrite <- (Neqb_complete _ _ H9). rewrite (Neqb_complete _ _ H2). exact H7. exact (union_pl_correct_wrt_sign_invar p a0 x H6 H8). simpl in |- *. rewrite H2. reflexivity. simpl in |- *. rewrite (Neqb_correct a). reflexivity. elim (Ndiscr (Nxor a a1)).
	intro y. elim y. intros x y0. rewrite y0 in H1. rewrite (MapPut1_semantics prec_list x a a1 a0 p y0) in H1. elim (bool_is_true_or_false (Neqb a a2)); intros; rewrite H3 in H1. inversion H1. elim (H a a0). intros.
	elim H4. intros. split with x0. rewrite <- (Neqb_complete _ _ H3).
	rewrite <- H5. exact H4. simpl in |- *. rewrite (Neqb_correct a).
	reflexivity. elim (bool_is_true_or_false (Neqb a1 a2)); intros.
	rewrite H4 in H1. inversion H1. elim (H0 a1 p). intros. split with x0. rewrite (Neqb_complete _ _ H4) in H5. rewrite H6 in H5.
	exact H5. simpl in |- *. rewrite (Neqb_correct a1). reflexivity.
	rewrite H4 in H1. inversion H1. intros y. rewrite (Neqb_comm a1 a) in H2. rewrite (Nxor_eq_true _ _ y) in H2. inversion H2.
	intros. unfold state_correct_wrt_sign_with_offset in |- *. intros.
	cut (state_correct_wrt_sign_with_offset m sigma (pre_ad_O pa)).
	cut (state_correct_wrt_sign_with_offset m0 sigma (pre_ad_I pa)).
	intros. induction  a as [| p1]. simpl in H3. cut
  (state_correct_wrt_sign_with_offset (M1 prec_list N0 p) sigma
     (pre_ad_O pa)). intros. induction  a0 as [| p1].
	elim (H _ _ _ _ H5 H6 N0 p0). intros. split with x. simpl in H7.
	exact H7. exact H3. induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]. elim (H4 (Npos p1) p0). intros.
	split with x. simpl in H7. exact H7. exact H3. elim (H _ _ _ _ H5 H6 (Npos p1) p0). intros. split with x. simpl in H7. exact H7.
	exact H3. elim (H4 N0 p0). intros. split with x. simpl in H7.
	exact H7. exact H3. unfold state_correct_wrt_sign_with_offset in |- *.
	intros. elim (H2 (Ndouble a) p1). intros. split with x.
	induction  a as [| p2]; simpl in |- *; simpl in H7; exact H7. simpl in H6. 
	elim (Ndiscr a). intros y. elim y. intros x y0. rewrite y0 in H6.
	inversion H6. intros y. rewrite y in H6. rewrite y. simpl in |- *.
	exact H6. induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]. cut
  (state_correct_wrt_sign_with_offset (M1 prec_list (Npos p1) p) sigma
     (pre_ad_I pa)). intro. induction  a0 as [| p2]. simpl in H3. elim (H5 N0 p0). intros. split with x. simpl in H7. exact H7. exact H3. induction  p2 as [p2 Hrecp2| p2 Hrecp2| ]; simpl in H3. elim (H0 _ _ _ _ H4 H6 (Npos p2) p0). intros. split with x. simpl in H7.
	exact H7. exact H3. elim (H5 (Npos p2) p0). intros. split with x.
	simpl in H7. exact H7. exact H3. elim (H0 _ _ _ _ H4 H6 N0 p0).
	intros. split with x. simpl in H7. exact H7. exact H3. 
	unfold state_correct_wrt_sign_with_offset in |- *. intros. elim (H2 (Ndouble_plus_one a) p2). intros. split with x. induction  a as [| p3]; simpl in |- *; simpl in H7; exact H7. induction  a as [| p3]; simpl in |- *; exact H6. cut
  (state_correct_wrt_sign_with_offset (M1 prec_list (Npos p1) p) sigma
     (pre_ad_O pa)). intros. induction  a0 as [| p2]. simpl in H3.
	elim (H _ _ _ _ H5 H6 N0 p0). intros. split with x. simpl in H7.
	exact H7. exact H3. induction  p2 as [p2 Hrecp2| p2 Hrecp2| ]; simpl in H3. elim (H4 (Npos p2) p0).
	intros. split with x. simpl in H7. exact H7. exact H3. elim (H _ _ _ _ H5 H6 (Npos p2) p0). intros. split with x. simpl in H7.
	exact H7. exact H3. elim (H4 N0 p0). intros. split with x. simpl in H7. exact H7. exact H3. unfold state_correct_wrt_sign_with_offset in |- *.
	intros. elim (H2 (Ndouble a) p2). intros. split with x. 
	induction  a as [| p3]; simpl in |- *; simpl in H7; exact H7. induction  a as [| p3]; simpl in |- *; exact H6. cut
  (state_correct_wrt_sign_with_offset (M1 prec_list N0 p) sigma
     (pre_ad_I pa)). intro. induction  a0 as [| p1]. simpl in H3.
	elim (H5 N0 p0). intros. split with x. simpl in H7. exact H7.
	exact H3. induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]; simpl in H3. elim (H0 _ _ _ _ H4 H6 (Npos p1) p0). intros. split with x. simpl in H7. exact H7.
	exact H3. elim (H5 (Npos p1) p0). intros. split with x. simpl in H7. exact H7. exact H3. elim (H0 _ _ _ _ H4 H6 N0 p0).
	intros. split with x. simpl in H7. exact H7. exact H3. unfold state_correct_wrt_sign_with_offset in |- *. intros. elim (H2 (Ndouble_plus_one a) p1). intros. split with x. induction  a as [| p2]; simpl in |- *; simpl in H7; exact H7. induction  a as [| p2]; simpl in |- *. simpl in H6. exact H6. simpl in H6. inversion H6. unfold state_correct_wrt_sign_with_offset in |- *.
	intros. elim (H1 (Ndouble_plus_one a1) p1). intros. split with x.
	induction  a1 as [| p2]; simpl in H5; simpl in |- *; exact H5. induction  a1 as [| p2]; simpl in |- *; exact H4. unfold state_correct_wrt_sign_with_offset in |- *. intros.
	elim (H1 (Ndouble a1) p1). intros. split with x. induction  a1 as [| p2]; simpl in |- *; simpl in H5; exact H5. induction  a1 as [| p2]; simpl in |- *; exact H4.
Qed.

Lemma union_mpl_correct_wrt_sign_invar_1 :
 forall (s0 s1 : state) (pa : pre_ad) (sigma : signature),
 state_correct_wrt_sign_with_offset s0 sigma pa ->
 state_correct_wrt_sign_with_offset s1 sigma pa ->
 state_correct_wrt_sign_with_offset (union_mpl s0 s1) sigma pa.
Proof.
	simple induction s0. simpl in |- *. simple induction s1; intros. exact H0. exact H0. exact H2.
	simpl in |- *. simple induction s1. intros. exact (union_mpl_correct_wrt_sign_invar_0 (M0 prec_list) a a0 pa sigma H0 H). intros. elim (bool_is_true_or_false (Neqb a1 a)); intros; rewrite H1. unfold state_correct_wrt_sign_with_offset in |- *.
	intros. simpl in H2. elim (bool_is_true_or_false (Neqb a1 a3)); intros; rewrite H3 in H2. inversion H2. elim (H a a0). intros. elim (H0 a1 a2).
	intros. split with x. rewrite (Neqb_complete _ _ H1) in H6. split.
	elim H4. intros. rewrite <- (Neqb_complete _ _ H3). rewrite (Neqb_complete _ _ H1). exact H7. elim H4. elim H6. intros.
	rewrite H9 in H7. inversion H7. rewrite H12 in H10. exact (union_pl_correct_wrt_sign_invar _ _ _ H8 H10). simpl in |- *. rewrite (Neqb_correct a1). reflexivity. simpl in |- *. rewrite (Neqb_correct a).
	reflexivity. inversion H2. elim (Ndiscr (Nxor a a1)); intro y. elim y.
	intros x y0. rewrite y0. unfold state_correct_wrt_sign_with_offset in |- *. intros.
	rewrite (MapPut1_semantics prec_list x a a1 a0 a2) in H2. elim (bool_is_true_or_false (Neqb a a3)); intros. rewrite H3 in H2.
	inversion H2. elim (H a a0). intros. split with x0. rewrite (Neqb_complete _ _ H3) in H4. rewrite H5 in H4. exact H4. simpl in |- *.
	rewrite (Neqb_correct a). reflexivity. rewrite H3 in H2. elim (bool_is_true_or_false (Neqb a1 a3)); intros. rewrite H4 in H2.
	inversion H2. elim (H0 a1 a2). intros. split with x0. rewrite (Neqb_complete _ _ H4) in H5. rewrite H6 in H5. exact H5. simpl in |- *.
	rewrite (Neqb_correct a1). reflexivity. rewrite H4 in H2. inversion H2. exact y0. rewrite (Neqb_comm a1 a) in H1. rewrite (Nxor_eq_true _ _ y) in H1. inversion H1. intros. simpl in |- *. induction  a as [| p]. exact (union_mpl_correct_wrt_sign_invar_0 _ _ _ _ _ H2 H1). induction  p as [p Hrecp| p Hrecp| ].
	clear Hrecp. replace
  (state_correct_wrt_sign_with_offset
     (M2 prec_list m (union_mpl_0 (Npos p) a0 m0)) sigma pa) with
  (state_correct_wrt_sign_with_offset
     (union_mpl_0 (Npos (xI p)) a0 (M2 prec_list m m0)) sigma pa). exact
  (union_mpl_correct_wrt_sign_invar_0 (M2 prec_list m m0) 
     (Npos (xI p)) a0 pa sigma H2 H1). reflexivity.
	clear Hrecp. replace
  (state_correct_wrt_sign_with_offset
     (M2 prec_list (union_mpl_0 (Npos p) a0 m) m0) sigma pa) with
  (state_correct_wrt_sign_with_offset
     (union_mpl_0 (Npos (xO p)) a0 (M2 prec_list m m0)) sigma pa). exact
  (union_mpl_correct_wrt_sign_invar_0 (M2 prec_list m m0) 
     (Npos (xO p)) a0 pa sigma H2 H1). reflexivity.
	replace
  (state_correct_wrt_sign_with_offset
     (M2 prec_list m (union_mpl_0 N0 a0 m0)) sigma pa) with
  (state_correct_wrt_sign_with_offset
     (union_mpl_0 (Npos 1) a0 (M2 prec_list m m0)) sigma pa). exact
  (union_mpl_correct_wrt_sign_invar_0 (M2 prec_list m m0) 
     (Npos 1) a0 pa sigma H2 H1). reflexivity. simple induction s1. intros. simpl in |- *. exact H1.
	intros. simpl in |- *. induction  a as [| p]. replace
  (state_correct_wrt_sign_with_offset
     (M2 prec_list (union_mpl_0 N0 a0 m) m0) sigma pa) with
  (state_correct_wrt_sign_with_offset
     (union_mpl_0 N0 a0 (M2 prec_list m m0)) sigma pa). exact
  (union_mpl_correct_wrt_sign_invar_0 (M2 prec_list m m0) N0 a0 pa sigma H1
     H2). reflexivity. induction  p as [p Hrecp| p Hrecp| ].
	replace
  (state_correct_wrt_sign_with_offset
     (M2 prec_list m (union_mpl_0 (Npos p) a0 m0)) sigma pa) with
  (state_correct_wrt_sign_with_offset
     (union_mpl_0 (Npos (xI p)) a0 (M2 prec_list m m0)) sigma pa). exact
  (union_mpl_correct_wrt_sign_invar_0 (M2 prec_list m m0) 
     (Npos (xI p)) a0 pa sigma H1 H2). reflexivity. replace
  (state_correct_wrt_sign_with_offset
     (M2 prec_list (union_mpl_0 (Npos p) a0 m) m0) sigma pa) with
  (state_correct_wrt_sign_with_offset
     (union_mpl_0 (Npos (xO p)) a0 (M2 prec_list m m0)) sigma pa). exact
  (union_mpl_correct_wrt_sign_invar_0 (M2 prec_list m m0) 
     (Npos (xO p)) a0 pa sigma H1 H2). reflexivity.
	replace
  (state_correct_wrt_sign_with_offset
     (M2 prec_list m (union_mpl_0 N0 a0 m0)) sigma pa) with
  (state_correct_wrt_sign_with_offset
     (union_mpl_0 (Npos 1) a0 (M2 prec_list m m0)) sigma pa). exact
  (union_mpl_correct_wrt_sign_invar_0 (M2 prec_list m m0) 
     (Npos 1) a0 pa sigma H1 H2). reflexivity. intros. simpl in |- *. elim (state_correct_wrt_sign_with_offset_M2 _ _ _ _ H3). elim (state_correct_wrt_sign_with_offset_M2 _ _ _ _ H4). intros. cut
  (state_correct_wrt_sign_with_offset (union_mpl m m1) sigma (pre_ad_O pa)).
	cut
  (state_correct_wrt_sign_with_offset (union_mpl m0 m2) sigma (pre_ad_I pa)). intros. unfold state_correct_wrt_sign_with_offset in |- *. intros.
	induction  a as [| p0]. elim (H10 N0 p). intros. split with x. simpl in H12.
	exact H12. simpl in H11. exact H11. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. elim (H9 (Npos p0) p).
	intros. split with x. simpl in H12. exact H12. simpl in H11.
	exact H11. elim (H10 (Npos p0) p). intros. split with x. simpl in H12. exact H12. simpl in H11. exact H11. elim (H9 N0 p). intros.
	simpl in H12. simpl in H11. split with x. exact H12. exact H11.
	exact (H0 _ _ _ H8 H6). exact (H _ _ _ H7 H5).
Qed.

Lemma union_mpl_correct_wrt_sign_invar :
 forall (s0 s1 : state) (sigma : signature),
 state_correct_wrt_sign s0 sigma ->
 state_correct_wrt_sign s1 sigma ->
 state_correct_wrt_sign (union_mpl s0 s1) sigma.
Proof.
	intros. replace (state_correct_wrt_sign (union_mpl s0 s1) sigma) with
  (state_correct_wrt_sign_with_offset (union_mpl s0 s1) sigma pre_ad_empty). apply (union_mpl_correct_wrt_sign_invar_1 s0 s1 pre_ad_empty sigma). unfold state_correct_wrt_sign_with_offset in |- *.
	simpl in |- *. exact H. unfold state_correct_wrt_sign_with_offset in |- *. simpl in |- *.
	exact H0. unfold state_correct_wrt_sign_with_offset in |- *. reflexivity.
Qed.

Lemma union_0_correct_wrt_sign_invar :
 forall (d : preDTA) (a0 a1 : ad) (s : state) (sigma : signature),
 predta_correct_wrt_sign d sigma ->
 union_0 d a0 a1 = Some s -> state_correct_wrt_sign s sigma.
Proof.
	unfold union_0 in |- *. unfold union_opt_state in |- *. intros. elim (option_sum state (MapGet state d (uad_conv_0 a0))); intros y. elim y. intros x y0.
	rewrite y0 in H0. elim (option_sum state (MapGet state d (uad_conv_1 a1))); intros y1. elim y1. intros x0 y2. rewrite y2 in H0. inversion H0. apply (union_mpl_correct_wrt_sign_invar x x0 sigma). unfold predta_correct_wrt_sign in H. exact (H _ _ y0). unfold predta_correct_wrt_sign in H. exact (H _ _ y2).
	rewrite y1 in H0. inversion H0. rewrite <- H2. exact (H _ _ y0).
	rewrite y in H0. elim (option_sum state (MapGet state d (uad_conv_1 a1))).
	intros y0. elim y0. intros x y1. rewrite y1 in H0. inversion H0. rewrite <- H2.
	exact (H _ _ y1). intros y0. rewrite y0 in H0. inversion H0.
Qed.

Lemma insert_ostate_correct_wrt_sign_invar :
 forall (d : preDTA) (a : ad) (s : state) (sigma : signature),
 predta_correct_wrt_sign d sigma ->
 state_correct_wrt_sign s sigma ->
 predta_correct_wrt_sign (insert_ostate d a (Some s)) sigma.
Proof.
	unfold predta_correct_wrt_sign in |- *. unfold insert_ostate in |- *. intros.
	rewrite (MapPut_semantics state d a s) in H1. elim (bool_is_true_or_false (Neqb a a0)); intros; rewrite H2 in H1.
	inversion H1. rewrite <- H4. exact H0. exact (H a0 s0 H1).
Qed.

Lemma union_correct_wrt_sign_invar :
 forall (d0 d1 : DTA) (sigma : signature),
 dta_correct_wrt_sign d0 sigma ->
 dta_correct_wrt_sign d1 sigma -> dta_correct_wrt_sign (union d0 d1) sigma.
Proof.
	unfold union in |- *. simple induction d0. simple induction d1. unfold union_1 in |- *. unfold insert_main_ostate in |- *. unfold dta_correct_wrt_sign in |- *. intros. unfold insert_main_ostate_0 in |- *. elim (option_sum state (union_0 (u_merge p p0) a a0)).
	intros y. elim y. intros x y0. rewrite y0. exact
  (insert_ostate_correct_wrt_sign_invar (u_merge p p0)
     (new_preDTA_ad (u_merge p p0)) x sigma
     (umerge_correct_wrt_sign_invar _ _ _ H H0)
     (union_0_correct_wrt_sign_invar (u_merge p p0) a a0 x sigma
        (umerge_correct_wrt_sign_invar _ _ _ H H0) y0)).
	intro y. rewrite y. simpl in |- *. exact (umerge_correct_wrt_sign_invar _ _ _ H H0).
Qed.

(* conservation de l'invariant ref_ok pour l'union *)

Lemma upl_conv_0_ref_ok_invar :
 forall (p : prec_list) (a : ad),
 prec_occur (upl_conv_0 p) a ->
 exists b : ad, a = uad_conv_0 b /\ prec_occur p b.
Proof.
	simple induction p. intros. simpl in H1. inversion H1. split with a. split.
	reflexivity. exact (prec_hd a p0 p1). elim (H a0 H6). intros. split with x. elim H7. intros. split. exact H8. exact (prec_int0 a x p0 p1 H9). elim (H0 a0 H6). intros. split with x. elim H7. intros. split.
	exact H8. exact (prec_int1 a x p0 p1 H9). intros. simpl in H.
	inversion H.
Qed.

Lemma upl_conv_1_ref_ok_invar :
 forall (p : prec_list) (a : ad),
 prec_occur (upl_conv_1 p) a ->
 exists b : ad, a = uad_conv_1 b /\ prec_occur p b.
Proof.
	simple induction p. intros. simpl in H1. inversion H1. split with a. split.
	reflexivity. exact (prec_hd a p0 p1). elim (H a0 H6). intros. split with x. elim H7. intros. split. exact H8. exact (prec_int0 a x p0 p1 H9). elim (H0 a0 H6). intros. split with x. elim H7. intros. split.
	exact H8. exact (prec_int1 a x p0 p1 H9). intros. simpl in H.
	inversion H.
Qed.

Lemma udta_conv_0_ref_ok_invar_0 :
 forall (d : preDTA) (a : ad) (s : state) (c : ad) (p : prec_list) (b : ad),
 MapGet state (udta_conv_0 d) (uad_conv_0 a) = Some s ->
 MapGet prec_list s c = Some p ->
 prec_occur p b ->
 exists s' : state,
   (exists p' : prec_list,
      (exists b' : ad,
         MapGet state d a = Some s' /\
         MapGet prec_list s' c = Some p' /\
         p = upl_conv_0 p' /\
         s = umpl_conv_0 s' /\ b = uad_conv_0 b' /\ prec_occur p' b')).
Proof.
	intros. elim (u_conv_0_invar_5 d a s H). intros. split with x. elim H2.
	intros. rewrite H3 in H0. elim (u_conv_0_invar_7 x c p H0). intros. split with x0. elim H5. intros. rewrite H6 in H1. elim (upl_conv_0_ref_ok_invar x0 b H1). intros. split with x1. elim H8. intros. split. exact H4. split.
	exact H7. split. exact H6. split. exact H3. split. exact H9. exact H10.
Qed.

Lemma udta_conv_1_ref_ok_invar_0 :
 forall (d : preDTA) (a : ad) (s : state) (c : ad) (p : prec_list) (b : ad),
 MapGet state (udta_conv_1 d) (uad_conv_1 a) = Some s ->
 MapGet prec_list s c = Some p ->
 prec_occur p b ->
 exists s' : state,
   (exists p' : prec_list,
      (exists b' : ad,
         MapGet state d a = Some s' /\
         MapGet prec_list s' c = Some p' /\
         p = upl_conv_1 p' /\
         s = umpl_conv_1 s' /\ b = uad_conv_1 b' /\ prec_occur p' b')).
Proof.
	intros. elim (u_conv_1_invar_5 d a s H). intros. split with x. elim H2.
	intros. rewrite H3 in H0. elim (u_conv_1_invar_7 x c p H0). intros. split with x0. elim H5. intros. rewrite H6 in H1. elim (upl_conv_1_ref_ok_invar x0 b H1). intros. split with x1. elim H8. intros. split. exact H4. split.
	exact H7. split. exact H6. split. exact H3. split. exact H9. exact H10.
Qed.

Lemma udta_conv_0_ref_ok_invar :
 forall d : preDTA, preDTA_ref_ok d -> preDTA_ref_ok (udta_conv_0 d).
Proof.
	unfold preDTA_ref_ok in |- *. intros. elim (u_conv_0_invar_8 _ _ _ H0). intros.
	rewrite H3 in H0. elim (udta_conv_0_ref_ok_invar_0 _ _ _ _ _ _ H0 H1 H2).
	intros. elim H4. intros. elim H5. intros. decompose [and] H6. elim (H _ _ _ _ _ H7 H9 H13). intros. split with (umpl_conv_0 x3). rewrite H11.
	exact (u_conv_0_invar_0 _ _ _ H12).
Qed.

Lemma udta_conv_1_ref_ok_invar :
 forall d : preDTA, preDTA_ref_ok d -> preDTA_ref_ok (udta_conv_1 d).
Proof.
	unfold preDTA_ref_ok in |- *. intros. elim (u_conv_1_invar_8 _ _ _ H0). intros.
	rewrite H3 in H0. elim (udta_conv_1_ref_ok_invar_0 _ _ _ _ _ _ H0 H1 H2).
	intros. elim H4. intros. elim H5. intros. decompose [and] H6. elim (H _ _ _ _ _ H7 H9 H13). intros. split with (umpl_conv_1 x3). rewrite H11.
	exact (u_conv_1_invar_0 _ _ _ H12).
Qed.

Lemma MapMerge_ref_ok_invar :
 forall d0 d1 : preDTA,
 preDTA_ref_ok d0 -> preDTA_ref_ok d1 -> preDTA_ref_ok (MapMerge state d0 d1).
Proof.
	unfold preDTA_ref_ok in |- *. intros. rewrite (MapMerge_semantics state d0 d1) in H1. rewrite (MapMerge_semantics state d0 d1). elim (option_sum state (MapGet state d1 a)); intros y. elim y. intros x y0. rewrite y0 in H1. inversion H1. rewrite <- H5 in H2. elim (H0 a x c pl b y0 H2 H3). intros. rewrite H4. split with x0. reflexivity. rewrite y in H1. elim (H a s c pl b H1 H2 H3). intros. rewrite H4. elim (option_sum state (MapGet state d1 b)).
	intros y0. elim y0. intros x0 y1. rewrite y1. split with x0. reflexivity. intro y0.
	rewrite y0. split with x. reflexivity.
Qed.

Lemma u_merge_ref_ok_invar :
 forall d0 d1 : preDTA,
 preDTA_ref_ok d0 -> preDTA_ref_ok d1 -> preDTA_ref_ok (u_merge d0 d1).
Proof.
	unfold u_merge in |- *. exact
  (fun (d0 d1 : preDTA) (p0 : preDTA_ref_ok d0) (p1 : preDTA_ref_ok d1) =>
   MapMerge_ref_ok_invar (udta_conv_0 d0) (udta_conv_1 d1)
     (udta_conv_0_ref_ok_invar d0 p0) (udta_conv_1_ref_ok_invar d1 p1)).
Qed.

Lemma union_pl_ref_ok_invar :
 forall (p p' : prec_list) (d : preDTA),
 prec_list_ref_ok p d ->
 prec_list_ref_ok p' d -> prec_list_ref_ok (union_pl p p') d.
Proof.
	simple induction p. simpl in |- *. intros. unfold prec_list_ref_ok in |- *. elim (prec_list_ref_ok_destr a p0 p1 d H1). intros. inversion H5.
	rewrite <- H6. exact (H1 a (prec_hd a p0 p1)). exact (H3 a0 H10).
	exact (H0 p' d H4 H2 a0 H10). intros. unfold prec_list_ref_ok in |- *.
	intros. simpl in H1. exact (H0 a H1).
Qed.

Lemma union_mpl_0_ref_ok_invar :
 forall (s : state) (a : ad) (p : prec_list) (d : preDTA),
 state_ref_ok (M1 prec_list a p) d ->
 state_ref_ok s d -> state_ref_ok (union_mpl_0 a p s) d.
Proof.
	simple induction s. simpl in |- *. intros. exact H. intros. simpl in |- *.  unfold state_ref_ok in |- *.
	intros. elim (bool_is_true_or_false (Neqb a1 a)); intros; rewrite H2 in H1.
	simpl in H1. elim (bool_is_true_or_false (Neqb a1 a2)); intros; rewrite H3 in H1. inversion H1. apply (union_pl_ref_ok_invar p a0 d). apply (H a1).
	simpl in |- *. rewrite (Neqb_correct a1). reflexivity. apply (H0 a). simpl in |- *.
	rewrite (Neqb_correct a). reflexivity. inversion H1. elim (Ndiscr (Nxor a a1)); intros y. elim y. intros x y0. rewrite y0 in H1. rewrite (MapPut1_semantics prec_list x a a1 a0 p) in H1. elim (bool_is_true_or_false (Neqb a a2)); intros; rewrite H3 in H1. inversion H1. rewrite <- H5.
	apply (H0 a). simpl in |- *. rewrite (Neqb_correct a). reflexivity. elim (bool_is_true_or_false (Neqb a1 a2)); intros; rewrite H4 in H1;
  inversion H1. rewrite <- H6. apply (H a1). simpl in |- *. rewrite (Neqb_correct a1). reflexivity. exact y0. rewrite (Neqb_comm a1 a) in H2. rewrite (Nxor_eq_true _ _ y) in H2. inversion H2. intros. simpl in |- *. unfold state_ref_ok in |- *. intros. cut (state_ref_ok m0 d). cut (state_ref_ok m d).
	intros. induction  a as [| p1]. induction  a0 as [| p1]. simpl in H3. exact (H _ _ _ H1 H4 N0 p0 H3). induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]; simpl in H3. exact (H5 _ _ H3). exact (H _ _ _ H1 H4 _ _ H3). exact (H5 _ _ H3). induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]. clear Hrecp1.
	induction  a0 as [| p2]. simpl in H3. exact (H4 _ _ H3). cut (state_ref_ok (M1 prec_list (Npos p1) p) d). intro. induction  p2 as [p2 Hrecp2| p2 Hrecp2| ]; simpl in H3. exact (H0 _ _ _ H6 H5 _ _ H3). exact (H4 _ _ H3). exact (H0 _ _ _ H6 H5 _ _ H3).
	unfold state_ref_ok in |- *. intros. apply (H1 (Ndouble_plus_one a) p3).
	induction  a as [| p4]; simpl in |- *; exact H6. cut (state_ref_ok (M1 prec_list (Npos p1) p) d). intro. induction  a0 as [| p2]. simpl in H3. exact (H _ _ _ H6 H4 _ _ H3).
	induction  p2 as [p2 Hrecp2| p2 Hrecp2| ]; simpl in H3. exact (H5 _ _ H3). exact (H _ _ _ H6 H4 _ _ H3). exact (H5 _ _ H3). unfold state_ref_ok in |- *. intros. apply (H1 (Ndouble a) p2). induction  a as [| p3]; simpl in |- *; exact H6. cut (state_ref_ok (M1 prec_list N0 p) d). intros. induction  a0 as [| p1]. simpl in H3. exact (H4 _ _ H3). induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]; simpl in H3. exact (H0 _ _ _ H6 H5 _ _ H3). exact (H4 _ _ H3). exact (H0 _ _ _ H6 H5 _ _ H3). unfold state_ref_ok in |- *. intros. apply (H1 (Ndouble_plus_one a) p1). induction  a as [| p2]; exact H6. unfold state_ref_ok in |- *. intros. apply (H2 (Ndouble a1) p1).
	induction  a1 as [| p2]; exact H4. unfold state_ref_ok in |- *. intros. apply (H2 (Ndouble_plus_one a1) p1). induction  a1 as [| p2]; exact H4.
Qed.

Lemma union_mpl_correct_ref_ok_invar :
 forall (s0 s1 : state) (d : preDTA),
 state_ref_ok s0 d -> state_ref_ok s1 d -> state_ref_ok (union_mpl s0 s1) d.
Proof.
	simple induction s0. simpl in |- *. intros. induction  s1 as [| a a0| s1_1 Hrecs1_1 s1_0 Hrecs1_0]. exact H. exact H0.
	exact H0. simple induction s1. simpl in |- *. intros. exact H. intros.
	replace (union_mpl (M1 prec_list a a0) (M1 prec_list a1 a2)) with
  (union_mpl_0 a1 a2 (M1 prec_list a a0)). exact (union_mpl_0_ref_ok_invar _ _ _ _ H0 H). reflexivity. intros. replace (union_mpl (M1 prec_list a a0) (M2 prec_list m m0)) with
  (union_mpl_0 a a0 (M2 prec_list m m0)).
	exact (union_mpl_0_ref_ok_invar _ _ _ _ H1 H2). reflexivity.
	simple induction s1. intros. simpl in |- *. exact H1. intros. replace (union_mpl (M2 prec_list m m0) (M1 prec_list a a0)) with
  (union_mpl_0 a a0 (M2 prec_list m m0)). exact (union_mpl_0_ref_ok_invar _ _ _ _ H2 H1). reflexivity. intros. elim (state_ref_ok_M2_destr _ _ _ H3).
	intros. elim (state_ref_ok_M2_destr _ _ _ H4). intros. simpl in |- *.
	unfold state_ref_ok in |- *. intros. induction  a as [| p0]. simpl in H9. exact (H _ _ H5 H7 _ _ H9). induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]; simpl in H9. exact (H0 _ _ H6 H8 _ _ H9). exact (H _ _ H5 H7 _ _ H9). exact (H0 _ _ H6 H8 _ _ H9).
Qed.

Lemma union_ref_ok :
 forall d0 d1 : DTA,
 DTA_ref_ok d0 -> DTA_ref_ok d1 -> DTA_ref_ok (union d0 d1).
Proof.
	simple induction d0. simple induction d1. unfold union in |- *. unfold DTA_ref_ok in |- *.
	unfold union_1 in |- *. unfold insert_main_ostate in |- *. unfold insert_main_ostate_0 in |- *. unfold insert_ostate in |- *. intros. unfold preDTA_ref_ok in |- *. unfold union_0 in |- *. unfold union_opt_state in |- *.
	elim (option_sum state (MapGet state (u_merge p p0) (uad_conv_0 a))). intro y. elim y. intro x. intro y0. rewrite y0. elim (option_sum state (MapGet state (u_merge p p0) (uad_conv_1 a0)));
  intro y1.
	elim y1. intro x0. intro y2. rewrite y2. intros. rewrite
  (MapPut_semantics state (u_merge p p0) (new_preDTA_ad (u_merge p p0))
     (union_mpl x x0)). rewrite
  (MapPut_semantics state (u_merge p p0) (new_preDTA_ad (u_merge p p0))
     (union_mpl x x0)) in H1. elim (bool_is_true_or_false (Neqb (new_preDTA_ad (u_merge p p0)) a1));
  intros; rewrite H4 in H1. inversion H1.
	elim (bool_is_true_or_false (Neqb (new_preDTA_ad (u_merge p p0)) b));
  intros; rewrite H5. split with (union_mpl x x0).
	reflexivity. cut (state_ref_ok (union_mpl x x0) (u_merge p p0)).
	intro. rewrite <- H6 in H2. exact (H7 c pl H2 b H3).
	apply (union_mpl_correct_ref_ok_invar x x0 (u_merge p p0)).
	elim (preDTA_ref_ok_def (u_merge p p0)). intros. exact (H7 (u_merge_ref_ok_invar p p0 H H0) _ _ y0). elim (preDTA_ref_ok_def (u_merge p p0)). intros. exact (H7 (u_merge_ref_ok_invar p p0 H H0) _ _ y2). elim (u_merge_ref_ok_invar p p0 H H0 a1 s c pl b H1 H2 H3). intros. elim (bool_is_true_or_false (Neqb (new_preDTA_ad (u_merge p p0)) b));
  intros; rewrite H6.
	split with (union_mpl x x0). reflexivity. split with x1.
	exact H5. rewrite y1. intros. rewrite
  (MapPut_semantics state (u_merge p p0) (new_preDTA_ad (u_merge p p0)) x)
  . rewrite
  (MapPut_semantics state (u_merge p p0) (new_preDTA_ad (u_merge p p0)) x)
   in H1. elim (bool_is_true_or_false (Neqb (new_preDTA_ad (u_merge p p0)) a1));
  intros; rewrite H4 in H1.
	inversion H1. rewrite <- H6. elim (bool_is_true_or_false (Neqb (new_preDTA_ad (u_merge p p0)) b));
  intros; rewrite H5.
	split with x. reflexivity. elim (preDTA_ref_ok_def (u_merge p p0)).
	intros. rewrite <- H6 in H2. exact (H7 (u_merge_ref_ok_invar _ _ H H0) (uad_conv_0 a) x y0 c pl H2 b H3). elim (bool_is_true_or_false (Neqb (new_preDTA_ad (u_merge p p0)) b));
  intros; rewrite H5. split with x. reflexivity. exact (u_merge_ref_ok_invar _ _ H H0 a1 s c pl b H1 H2 H3).
	intro y. rewrite y. elim (option_sum state (MapGet state (u_merge p p0) (uad_conv_1 a0)));
  intros. elim a1. intros x y1.
	rewrite y1. rewrite y1 in H1. rewrite
  (MapPut_semantics state (u_merge p p0) (new_preDTA_ad (u_merge p p0)) x)
  . rewrite
  (MapPut_semantics state (u_merge p p0) (new_preDTA_ad (u_merge p p0)) x)
   in H1. elim (bool_is_true_or_false (Neqb (new_preDTA_ad (u_merge p p0)) b));
  intros; rewrite H4.
	split with x. reflexivity. elim (bool_is_true_or_false (Neqb (new_preDTA_ad (u_merge p p0)) a2));
  intros; rewrite H5 in H1.
	inversion H1. rewrite <- H7 in H2. exact (u_merge_ref_ok_invar _ _ H H0 _ _ c pl b y1 H2 H3). exact (u_merge_ref_ok _ _ H H0 _ _ _ _ _ H1 H2 H3). rewrite b. rewrite b in H1.
	exact (u_merge_ref_ok _ _ H H0 _ _ _ _ _ H1 H2 H3).
Qed.

(* correction : appartenance de l'état final *)

Lemma union_DTA_main_state_correct_invar :
 forall d0 d1 : DTA,
 DTA_main_state_correct d0 ->
 DTA_main_state_correct d1 -> DTA_main_state_correct (union d0 d1).
Proof.
	simple induction d0. simple induction d1. simpl in |- *. unfold addr_in_preDTA in |- *.
	intros. elim H. elim H0. intros. unfold union_0 in |- *.
	rewrite
  (u_merge_0 p p0 (uad_conv_0 a) (umpl_conv_0 x0)
     (u_conv_0_invar_0 p a x0 H2)). rewrite
  (u_merge_1 p p0 (uad_conv_1 a0) (umpl_conv_1 x)
     (u_conv_1_invar_0 p0 a0 x H1)). unfold insert_ostate in |- *. unfold union_opt_state in |- *.
	split with (union_mpl (umpl_conv_0 x0) (umpl_conv_1 x)).
	rewrite
  (MapPut_semantics state (u_merge p p0)
     (Nmin
        (Ndouble
           (new_preDTA_ad (MapMerge state (udta_conv_0_aux p) (M0 state))))
        (Ndouble_plus_one (new_preDTA_ad (udta_conv_1_aux p0))))
     (union_mpl (umpl_conv_0 x0) (umpl_conv_1 x))). rewrite
  (Neqb_correct
     (Nmin
        (Ndouble
           (new_preDTA_ad (MapMerge state (udta_conv_0_aux p) (M0 state))))
        (Ndouble_plus_one (new_preDTA_ad (udta_conv_1_aux p0)))))
  . reflexivity.
Qed.