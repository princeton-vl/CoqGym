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
From IntMap Require Import Allmaps.
Require Import bases.
Require Import defs.
Require Import semantics.
Require Import signature.
Require Import refcorrect.
Require Import inter.

(* correction de l'invariant de compatibilité par rapport à une signature *)

Lemma pl_produit_correct_wrt_sign_invar :
 forall (p0 p1 : prec_list) (n : nat),
 pl_tl_length p0 n -> pl_tl_length p1 n -> pl_tl_length (pl_produit p0 p1) n.
Proof.
	exact pl_tl_length_prod.
Qed.

Lemma st_produit_l_correct_wrt_sign_invar_with_offset :
 forall (s0 : state) (a : ad) (p : prec_list) (sigma : signature)
   (pa : pre_ad),
 state_correct_wrt_sign_with_offset s0 sigma pa ->
 state_correct_wrt_sign_with_offset (M1 prec_list a p) sigma pa ->
 state_correct_wrt_sign_with_offset (s_produit_l a p s0) sigma pa.
Proof.
	simple induction s0. unfold state_correct_wrt_sign_with_offset in |- *.
	intros. inversion H1. unfold state_correct_wrt_sign_with_offset in |- *.
	intros. simpl in H1. elim (bool_is_true_or_false (Neqb a1 a)); intros; rewrite H2 in H1. simpl in H1. elim (bool_is_true_or_false (Neqb a1 a2)); intros; rewrite H3 in H1. inversion H1. elim (H a a0). elim (H0 a1 p). intros. elim H4. elim H6. intros. rewrite (Neqb_complete _ _ H2) in H9. rewrite H9 in H7. inversion H7.
	split with x. rewrite <- (Neqb_complete _ _ H3). rewrite (Neqb_complete _ _ H2). split. exact H9. rewrite H12 in H7.
	rewrite <- H12 in H8. exact (pl_tl_length_prod p a0 x H10 H8).
	simpl in |- *. rewrite (Neqb_correct a1). reflexivity. simpl in |- *.
	rewrite (Neqb_correct a). reflexivity. inversion H1.
	inversion H1. intros. elim (state_correct_wrt_sign_with_offset_M2 m m0 sigma pa H1). intros. unfold state_correct_wrt_sign_with_offset in |- *.
	intros. unfold state_correct_wrt_sign_with_offset in H.
	unfold state_correct_wrt_sign_with_offset in H0. induction  a as [| p1].
	induction  a0 as [| p1]. simpl in H5. elim (H N0 p sigma (pre_ad_O pa) H3) with (a := N0) (p0 := p0). intros. split with x. elim H6. intros.
	split. induction  pa as [| pa Hrecpa| pa Hrecpa]; simpl in |- *; simpl in H7;
  exact H7.
	exact H8. intros. elim (H2 N0 p). intros. split with x.
	induction  a as [| p2]. simpl in H6. inversion H6. rewrite <- H9. simpl in |- *.
	exact H7. induction  p2 as [p2 Hrecp2| p2 Hrecp2| ]. inversion H6. inversion H6. inversion H6. reflexivity. exact H5. induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]. simpl in H5.
	inversion H5. simpl in H5. elim (H N0 p sigma (pre_ad_O pa) H3) with (a := Npos p1) (p0 := p0). intros. split with x. simpl in H6.
	exact H6. intros. unfold state_correct_wrt_sign_with_offset in H2.
	induction  a as [| p3]. simpl in H6. inversion H6. elim (H2 N0 p). intros.
	split with x. rewrite <- H8. induction  pa as [| pa Hrecpa| pa Hrecpa]; exact H7. reflexivity.
	simpl in H6. inversion H6. exact H5. simpl in H5. inversion H5.
	induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]. clear Hrecp1. induction  a0 as [| p2]. simpl in H5.
	inversion H5. induction  p2 as [p2 Hrecp2| p2 Hrecp2| ]; simpl in H5. elim (H0 (Npos p1) p sigma (pre_ad_I pa) H4) with (a := Npos p2) (p0 := p0).
	intros. split with x. simpl in H6. exact H6. intros.
	unfold state_correct_wrt_sign_with_offset in H2. induction  a as [| p4]. inversion H6. elim (H2 (Npos (xI p4)) p3). intros. split with x. simpl in |- *. exact H7. simpl in |- *. simpl in H6. exact H6.
	exact H5. inversion H5. elim (H0 (Npos p1) p sigma (pre_ad_I pa) H4) with (a := N0) (p0 := p0). intros. split with x. simpl in H6. exact H6. intros. induction  a as [| p3]. inversion H6. elim (H2 (Npos (xI p3)) p2). intros. split with x. simpl in |- *. 
	exact H7. simpl in |- *. simpl in H6. exact H6. exact H5. induction  a0 as [| p2]. simpl in H5. elim (H (Npos p1) p sigma (pre_ad_O pa) H3) with (a := N0) (p0 := p0). intros. split with x. simpl in H6.
	exact H6. intros. induction  a as [| p3]. inversion H6. elim (H2 (Npos (xO p3)) p2). intros. split with x. simpl in |- *. exact H7. simpl in |- *.
	simpl in H6. exact H6. exact H5. induction  p2 as [p2 Hrecp2| p2 Hrecp2| ]; simpl in H5.
	inversion H5. elim (H (Npos p1) p sigma (pre_ad_O pa) H3) with (a := Npos p2) (p0 := p0). intros. split with x. simpl in H6. exact H6. intros. induction  a as [| p4]. inversion H6. elim (H2 (Npos (xO p4)) p3). intros. split with x. simpl in |- *. exact H7.
	simpl in |- *. simpl in H6. exact H6. exact H5. inversion H5.
	induction  a0 as [| p1]. simpl in H5. inversion H5. induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]; simpl in H5. elim (H0 N0 p sigma (pre_ad_I pa) H4) with (a := Npos p1) (p0 := p0). intros. split with x. simpl in H6. exact H6.
	intros. induction  a as [| p3]. elim (H2 (Npos 1) p2). intros.
	split with x. simpl in |- *. exact H7. simpl in |- *. simpl in H6. exact H6. inversion H6. exact H5. inversion H5. elim (H0 N0 p sigma (pre_ad_I pa) H4) with (a := N0) (p0 := p0). intros.
	split with x. simpl in H6. exact H6. intros. induction  a as [| p2].
	elim (H2 (Npos 1) p1). intros. split with x. simpl in |- *.
	exact H7. simpl in |- *. simpl in H6. exact H6. inversion H6.
	exact H5.
Qed.

Lemma st_produit_r_correct_wrt_sign_invar_with_offset :
 forall (s0 : state) (a : ad) (p : prec_list) (sigma : signature)
   (pa : pre_ad),
 state_correct_wrt_sign_with_offset s0 sigma pa ->
 state_correct_wrt_sign_with_offset (M1 prec_list a p) sigma pa ->
 state_correct_wrt_sign_with_offset (s_produit_r a p s0) sigma pa.
Proof.
	simple induction s0. unfold state_correct_wrt_sign_with_offset in |- *.
	intros. inversion H1. unfold state_correct_wrt_sign_with_offset in |- *.
	intros. simpl in H1. elim (bool_is_true_or_false (Neqb a1 a)); intros; rewrite H2 in H1. simpl in H1. elim (bool_is_true_or_false (Neqb a1 a2)); intros; rewrite H3 in H1. inversion H1. elim (H a a0). elim (H0 a1 p). intros.
	elim H4. elim H6. intros. rewrite (Neqb_complete _ _ H2) in H9. rewrite H9 in H7. inversion H7. split with x. 
	rewrite <- (Neqb_complete _ _ H3). rewrite (Neqb_complete _ _ H2). split. exact H9. rewrite H12 in H7. rewrite <- H12 in H8. exact (pl_tl_length_prod a0 p x H8 H10). simpl in |- *.
	rewrite (Neqb_correct a1). reflexivity. simpl in |- *. rewrite (Neqb_correct a). reflexivity. inversion H1. inversion H1.
	intros. elim (state_correct_wrt_sign_with_offset_M2 m m0 sigma pa H1). intros. unfold state_correct_wrt_sign_with_offset in |- *.
	intros. unfold state_correct_wrt_sign_with_offset in H.
	unfold state_correct_wrt_sign_with_offset in H0. induction  a as [| p1]. induction  a0 as [| p1]. simpl in H5. elim (H N0 p sigma (pre_ad_O pa) H3) with (a := N0) (p0 := p0). intros. split with x. simpl in H6. exact H6. intros. elim (H2 N0 p1). intros. split with x. simpl in |- *. induction  a as [| p2]. exact H7. inversion H6.
	induction  a as [| p2]. exact H6. inversion H6. exact H5. induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]; simpl in H5. inversion H5. elim (H N0 p sigma (pre_ad_O pa) H3) with (a := Npos p1) (p0 := p0). intros. split with x. simpl in H6. exact H6. intros. induction  a as [| p3]. elim (H2 N0 p2). intros. split with x. simpl in |- *. exact H7.
	exact H6. inversion H6. exact H5. inversion H5. induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]. induction  a0 as [| p2]. simpl in H5. inversion H5. induction  p2 as [p2 Hrecp2| p2 Hrecp2| ]; simpl in H5. elim (H0 (Npos p1) p sigma (pre_ad_I pa) H4) with (a := Npos p2) (p0 := p0). intros. split with x. simpl in H6. exact H6. intros. induction  a as [| p4]. inversion H6. elim (H2 (Npos (xI p4)) p3). intros. split with x. simpl in |- *.
	exact H7. simpl in |- *. simpl in H6. exact H6. exact H5.
	inversion H5. elim (H0 (Npos p1) p sigma (pre_ad_I pa) H4) with (a := N0) (p0 := p0). intros. split with x. exact H6.
	intros. induction  a as [| p3]. inversion H6. elim (H2 (Npos (xI p3)) p2). intros. split with x. simpl in |- *. exact H7. simpl in |- *. exact H6. exact H5. induction  a0 as [| p2]. simpl in H5. elim (H (Npos p1) p sigma (pre_ad_O pa) H3) with (a := N0) (p0 := p0). intros.
	split with x. simpl in H6. exact H6. intros. induction  a as [| p3].
	inversion H6. elim (H2 (Npos (xO p3)) p2). intros. split with x. simpl in |- *. exact H7. simpl in |- *. simpl in H6. exact H6.
	exact H5. induction  p2 as [p2 Hrecp2| p2 Hrecp2| ]; simpl in H5. inversion H5. elim (H (Npos p1) p sigma (pre_ad_O pa) H3) with (a := Npos p2) (p0 := p0). intros. split with x. simpl in H6. exact H6.
	intros. induction  a as [| p4]. inversion H6. elim (H2 (Npos (xO p4)) p3). intros. split with x. simpl in |- *. exact H7. simpl in |- *. simpl in H6. exact H6. exact H5. inversion H5. induction  a0 as [| p1].
	simpl in H5. inversion H5. induction  p1 as [p1 Hrecp1| p1 Hrecp1| ]; simpl in H5.
	elim (H0 N0 p sigma (pre_ad_I pa) H4) with (a := Npos p1) (p0 := p0). intros. split with x. simpl in H6. exact H6.
	intros. induction  a as [| p3]. elim (H2 (Npos 1) p2). intros.
	split with x. simpl in |- *. exact H7. simpl in |- *. simpl in H6.
	exact H6. inversion H6. exact H5. inversion H5. elim (H0 N0 p sigma (pre_ad_I pa) H4) with (a := N0) (p0 := p0).
	intros. split with x. simpl in H6. exact H6. intros.
	induction  a as [| p2]. elim (H2 (Npos 1) p1). intros. split with x. simpl in |- *. exact H7. simpl in |- *. simpl in H6. exact H6.
	inversion H6. exact H5.
Qed.

Lemma st_produit_correct_wrt_sign_invar_with_offset :
 forall (s0 s1 : state) (sigma : signature) (pa : pre_ad),
 state_correct_wrt_sign_with_offset s0 sigma pa ->
 state_correct_wrt_sign_with_offset s1 sigma pa ->
 state_correct_wrt_sign_with_offset (s_produit s0 s1) sigma pa.
Proof.
	simple induction s0. simple induction s1. intros. simpl in |- *. unfold state_correct_wrt_sign_with_offset in |- *. intros. inversion H1.
	intros. simpl in |- *. unfold state_correct_wrt_sign_with_offset in |- *.
	intros. inversion H1. intros. simpl in |- *. unfold state_correct_wrt_sign_with_offset in |- *. intros. inversion H3.
	simple induction s1. simpl in |- *. intros. unfold state_correct_wrt_sign_with_offset in |- *. intros. inversion H1.
	intros. replace (s_produit (M1 prec_list a a0) (M1 prec_list a1 a2)) with
  (s_produit_l a a0 (M1 prec_list a1 a2)).
	exact
  (st_produit_l_correct_wrt_sign_invar_with_offset 
     (M1 prec_list a1 a2) a a0 sigma pa H0 H). reflexivity. intros.
	replace (s_produit (M1 prec_list a a0) (M2 prec_list m m0)) with
  (s_produit_l a a0 (M2 prec_list m m0)). exact
  (st_produit_l_correct_wrt_sign_invar_with_offset 
     (M2 prec_list m m0) a a0 sigma pa H2 H1). reflexivity. simple induction s1.
	simpl in |- *. intros. exact H2. intros. replace (s_produit (M2 prec_list m m0) (M1 prec_list a a0)) with
  (s_produit_r a a0 (M2 prec_list m m0)). exact
  (st_produit_r_correct_wrt_sign_invar_with_offset 
     (M2 prec_list m m0) a a0 sigma pa H1 H2). reflexivity. intros. unfold state_correct_wrt_sign_with_offset in |- *. simpl in |- *. intros.
	elim (state_correct_wrt_sign_with_offset_M2 _ _ _ _ H3).
	intros. elim (state_correct_wrt_sign_with_offset_M2 _ _ _ _ H4). intros. induction  a as [| p0]. exact (H _ _ _ H6 H8 N0 p H5). induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]. exact (H0 _ _ _ H7 H9 (Npos p0) p H5).
	exact (H _ _ _ H6 H8 _ _ H5). exact (H0 _ _ _ H7 H9 _ _ H5).
Qed.

Lemma st_produit_correct_wrt_sign_invar :
 forall (s0 s1 : state) (sigma : signature),
 state_correct_wrt_sign s0 sigma ->
 state_correct_wrt_sign s1 sigma ->
 state_correct_wrt_sign (s_produit s0 s1) sigma.
Proof.
	intros. replace (state_correct_wrt_sign (s_produit s0 s1) sigma) with
  (state_correct_wrt_sign_with_offset (s_produit s0 s1) sigma pre_ad_empty). apply
  (st_produit_correct_wrt_sign_invar_with_offset s0 s1 sigma pre_ad_empty).
	unfold state_correct_wrt_sign_with_offset in |- *. simpl in |- *. exact H.
	unfold state_correct_wrt_sign_with_offset in |- *. simpl in |- *.
	exact H0. reflexivity.
Qed.

Lemma positive_sum :
 forall p : positive,
 p = 1%positive \/
 (exists q : positive, p = xO q) \/ (exists q : positive, p = xI q).
Proof.
	simple induction p. intros. right. right. split with p0. reflexivity.
	intros. right. left. split with p0. reflexivity. left.
	reflexivity.
Qed.

Lemma preDTA_produit_l_correct_wrt_sign_invar :
 forall (d : preDTA) (a : ad) (s : state) (sigma : signature),
 predta_correct_wrt_sign d sigma ->
 predta_correct_wrt_sign (M1 state a s) sigma ->
 predta_correct_wrt_sign (preDTA_produit_l a s d) sigma.
Proof.
	simple induction d. intros. simpl in |- *. exact H. simpl in |- *. unfold predta_correct_wrt_sign in |- *. intros. simpl in H1. elim (bool_is_true_or_false (Neqb (iad_conv a1 a) a2)); intros;
  rewrite H2 in H1. inversion H1. apply (st_produit_correct_wrt_sign_invar s a0 sigma). apply (H0 a1 s). simpl in |- *. rewrite (Neqb_correct a1).
	reflexivity. apply (H a a0). simpl in |- *. rewrite (Neqb_correct a).
	reflexivity. inversion H1. intros. elim (predta_correct_wrt_sign_M2 m m0 sigma H1). intros. induction  a as [| p]. simpl in |- *. unfold predta_correct_wrt_sign in |- *. intros. induction  a as [| p]. 
	simpl in H5. exact (H N0 s sigma H3 H2 N0 s0 H5).
	elim (positive_sum p); intros. rewrite H6 in H5.
	simpl in H5. inversion H5. elim H6. intros. elim H7.
	intros. rewrite H8 in H5. simpl in H5. elim (positive_sum x). intros. rewrite H9 in H5. exact (H0 N0 s sigma H4 H2 N0 s0 H5). intros. elim H9. intros. elim H10. intros.
	rewrite H11 in H5. exact (H N0 s sigma H3 H2 (Npos x0) s0 H5). intros. elim H10. intros. rewrite H11 in H5.
	exact (H0 N0 s sigma H4 H2 (Npos x0) s0 H5). intros.
	elim H7. intros. rewrite H8 in H5. simpl in H5. inversion H5. induction  p as [p Hrecp| p Hrecp| ]. cut (predta_correct_wrt_sign (M1 state (Npos p) s) sigma). intros. unfold predta_correct_wrt_sign in |- *.
	intros. simpl in H6. induction  a as [| p0]. inversion H6. elim (positive_sum p0); intros. rewrite H7 in H6. exact (H (Npos p) s sigma H3 H5 N0 s0 H6). elim H7; intros; elim H8; intros; rewrite H9 in H6. inversion H6. elim (positive_sum x). intros. rewrite H10 in H6. exact (H0 (Npos p) s _ H4 H5 _ _ H6). intros. elim H10; intros; elim H11; intros; rewrite H12 in H6. exact (H _ _ _ H3 H5 _ _ H6). exact (H0 _ _ _ H4 H5 _ _ H6). unfold predta_correct_wrt_sign in |- *. simple induction a. exact (H2 (Npos 1)). intro. exact (H2 (Npos (xI p0))). cut (predta_correct_wrt_sign (M1 state (Npos p) s) sigma).
	intro. unfold predta_correct_wrt_sign in |- *. intros. simpl in H6. induction  a as [| p0]. exact (H _ _ _ H3 H5 _ _ H6). elim (positive_sum p0); intros. rewrite H7 in H6. inversion H6.
	elim H7; intros; elim H8; intros; rewrite H9 in H6.
	elim (positive_sum x); intros. rewrite H10 in H6. exact (H0 _ _ _ H4 H5 _ _ H6). elim H10; intros; elim H11; intros; rewrite H12 in H6. exact (H _ _ _ H3 H5 _ _ H6).
	exact (H0 _ _ _ H4 H5 _ _ H6). inversion H6. unfold predta_correct_wrt_sign in |- *. simple induction a. exact (H2 N0).
	intro. exact (H2 (Npos (xO p0))). cut (predta_correct_wrt_sign (M1 state N0 s) sigma). intros.
	unfold predta_correct_wrt_sign in |- *. intros. simpl in H6.
	induction  a as [| p]. inversion H6. elim (positive_sum p); intros.
	rewrite H7 in H6. exact (H _ _ _ H3 H5 _ _ H6). elim H7; intros; elim H8; intros; rewrite H9 in H6. inversion H6.
	elim (positive_sum x); intros. rewrite H10 in H6. exact (H0 _ _ _ H4 H5 _ _ H6). elim H10; intros; elim H11; intros; rewrite H12 in H6. exact (H _ _ _ H3 H5 _ _ H6).
	exact (H0 _ _ _ H4 H5 _ _ H6). unfold predta_correct_wrt_sign in |- *.
	simple induction a. exact (H2 (Npos 1)). intro. exact (H2 (Npos (xI p))).
Qed.

Lemma preDTA_produit_r_correct_wrt_sign_invar :
 forall (d : preDTA) (a : ad) (s : state) (sigma : signature),
 predta_correct_wrt_sign d sigma ->
 predta_correct_wrt_sign (M1 state a s) sigma ->
 predta_correct_wrt_sign (preDTA_produit_r a s d) sigma.
Proof.
	simple induction d. intros. simpl in |- *. exact H. unfold predta_correct_wrt_sign in |- *. intros. simpl in H1. elim (bool_is_true_or_false (Neqb (iad_conv a a1) a2)); intros;
  rewrite H2 in H1. inversion H1. apply (st_produit_correct_wrt_sign_invar a0 s sigma). apply (H a a0). simpl in |- *. rewrite (Neqb_correct a).
	reflexivity. apply (H0 a1 s). simpl in |- *. rewrite (Neqb_correct a1). reflexivity. inversion H1.
	intros. elim (predta_correct_wrt_sign_M2 m m0 sigma H1). intros. induction  a as [| p]. simpl in |- *. unfold predta_correct_wrt_sign in |- *. intros. simpl in H5.
	induction  a as [| p]. exact (H _ _ _ H3 H2 _ _ H5). elim (positive_sum p); intros. rewrite H6 in H5. exact (H0 _ _ _ H4 H2 _ _ H5). elim H6; intros; elim H7; intros; rewrite H8 in H5. elim (positive_sum x); intros. rewrite H9 in H5. inversion H5. elim H9; intros; elim H10; intros; rewrite H11 in H5. exact (H _ _ _ H3 H2 _ _ H5). inversion H5. elim (positive_sum x); intros. rewrite H9 in H5. inversion H5. elim H9; intros; elim H10; intros; rewrite H11 in H5. exact (H0 _ _ _ H4 H2 _ _ H5). inversion H5.
	induction  p as [p Hrecp| p Hrecp| ]. cut (predta_correct_wrt_sign (M1 state (Npos p) s) sigma). intros. unfold predta_correct_wrt_sign in |- *.
	intros. simpl in H6. induction  a as [| p0]. inversion H6.
	elim (positive_sum p0); intros. rewrite H7 in H6.
	inversion H6. elim H7; intros; elim H8; intros; rewrite H9 in H6. elim (positive_sum x); intros.
	rewrite H10 in H6. exact (H _ _ _ H3 H5 _ _ H6).
	elim H10; intros; elim H11; intros; rewrite H12 in H6. inversion H6. exact (H _ _ _ H3 H5 _ _ H6).
	elim (positive_sum x); intros. rewrite H10 in H6.
	exact (H0 _ _ _ H4 H5 _ _ H6). elim H10; intros; elim H11; intros; rewrite H12 in H6. inversion H6.
	exact (H0 _ _ _ H4 H5 _ _ H6). unfold predta_correct_wrt_sign in |- *. simple induction a. exact (H2 (Npos 1)). intro. exact (H2 (Npos (xI p0))). cut (predta_correct_wrt_sign (M1 state (Npos p) s) sigma).
	intro. unfold predta_correct_wrt_sign in |- *. intros.
	simpl in H6. induction  a as [| p0]. exact (H _ _ _ H3 H5 _ _ H6).
	elim (positive_sum p0); intros. rewrite H7 in H6.
	exact (H0 _ _ _ H4 H5 _ _ H6). elim H7; intros; elim H8; intros; rewrite H9 in H6. elim (positive_sum x); intros. rewrite H10 in H6. inversion H6. elim H10; intros; elim H11; intros; rewrite H12 in H6. exact (H _ _ _ H3 H5 _ _ H6). inversion H6. elim (positive_sum x); intros. rewrite H10 in H6. inversion H6.
	elim H10; intros; elim H11; intros; rewrite H12 in H6.
	exact (H0 _ _ _ H4 H5 _ _ H6). inversion H6. unfold predta_correct_wrt_sign in |- *. simple induction a. exact (H2 N0).
	intro. exact (H2 (Npos (xO p0))). cut (predta_correct_wrt_sign (M1 state N0 s) sigma).
	intro. unfold predta_correct_wrt_sign in |- *. intros.
	simpl in H6. induction  a as [| p]. inversion H6. elim (positive_sum p); intros. rewrite H7 in H6. inversion H6. elim H7; intros; elim H8; intros; rewrite H9 in H6. elim (positive_sum x); intros. rewrite H10 in H6. exact (H _ _ _ H3 H5 _ _ H6). elim H10; intros; elim H11; intros; rewrite H12 in H6.
	inversion H6. exact (H _ _ _ H3 H5 _ _ H6). elim (positive_sum x); intros. rewrite H10 in H6.
	exact (H0 _ _ _ H4 H5 _ _ H6). elim H10; intros; elim H11; intros; rewrite H12 in H6. inversion H6.
	exact (H0 _ _ _ H4 H5 _ _ H6). unfold predta_correct_wrt_sign in |- *. simple induction a. exact (H2 (Npos 1)). intro. exact (H2 (Npos (xI p))).
Qed.

Lemma preDTA_produit_correct_wrt_sign_invar :
 forall (d0 d1 : preDTA) (sigma : signature),
 predta_correct_wrt_sign d0 sigma ->
 predta_correct_wrt_sign d1 sigma ->
 predta_correct_wrt_sign (preDTA_produit d0 d1) sigma.
Proof.
	simple induction d0. simple induction d1. simpl in |- *. intros. exact H.
	simpl in |- *. intros. exact H. intros. simpl in |- *. exact H1.
	simple induction d1. simpl in |- *. intros. exact H0. intros.
	replace (preDTA_produit (M1 state a a0) (M1 state a1 a2)) with
  (preDTA_produit_l a a0 (M1 state a1 a2)).
	exact
  (preDTA_produit_l_correct_wrt_sign_invar (M1 state a1 a2) a a0 sigma H0 H). reflexivity. intros.
	replace (preDTA_produit (M1 state a a0) (M2 state m m0)) with
  (preDTA_produit_l a a0 (M2 state m m0)). exact
  (preDTA_produit_l_correct_wrt_sign_invar (M2 state m m0) a a0 sigma H2 H1). reflexivity. simple induction d1. simpl in |- *.
	intros. exact H2. intros. replace (preDTA_produit (M2 state m m0) (M1 state a a0)) with
  (preDTA_produit_r a a0 (M2 state m m0)). exact
  (preDTA_produit_r_correct_wrt_sign_invar (M2 state m m0) a a0 sigma H1 H2). reflexivity. intros. simpl in |- *.
	elim (predta_correct_wrt_sign_M2 _ _ _ H3). intros.
	elim (predta_correct_wrt_sign_M2 _ _ _ H4). intros.
	unfold predta_correct_wrt_sign in |- *. intros. simpl in H9.
	induction  a as [| p]. exact (H _ _ H5 H7 N0 s H9). elim (positive_sum p); intros. rewrite H10 in H9.
	exact (H0 _ _ H6 H7 _ _ H9). elim H10; intros; elim H11; intros; rewrite H12 in H9. elim (positive_sum x); intros. rewrite H13 in H9. exact (H _ _ H5 H8 _ _ H9). elim H13; intros; elim H14; intros; rewrite H15 in H9. exact (H _ _ H5 H7 _ _ H9). exact (H _ _ H5 H8 _ _ H9). elim (positive_sum x); intros.
	rewrite H13 in H9. exact (H0 _ _ H6 H8 _ _ H9).
	elim H13; intros; elim H14; intros; rewrite H15 in H9.
	exact (H0 _ _ H6 H7 _ _ H9). exact (H0 _ _ H6 H8 _ _ H9).
Qed.

Lemma inter_correct_wrt_sign_invar :
 forall (d0 d1 : DTA) (sigma : signature),
 dta_correct_wrt_sign d0 sigma ->
 dta_correct_wrt_sign d1 sigma -> dta_correct_wrt_sign (inter d0 d1) sigma.
Proof.
	simple induction d0. simple induction d1. simpl in |- *. intros.
	exact (preDTA_produit_correct_wrt_sign_invar p p0 sigma H H0).
Qed.

Definition pl_produit_ref_ok_0 (la pl : prec_list) : Prop :=
  forall (a b : ad) (l : prec_list) (n : nat),
  prec_occur (pl_produit_0 a la pl n l) b ->
  (exists a0 : ad,
     (exists a1 : ad,
        b = iad_conv a0 a1 /\ prec_occur la a0 /\ prec_occur pl a1)) \/
  (exists a1 : ad, b = iad_conv a a1 /\ prec_occur pl a1) \/ prec_occur l b.

Definition pl_produit_ref_ok_1 (p0 p1 : prec_list) : Prop :=
  forall (b : ad) (n : nat),
  prec_occur (pl_produit_1 p0 n p1) b ->
  exists a0 : ad,
    (exists a1 : ad,
       b = iad_conv a0 a1 /\ prec_occur p0 a0 /\ prec_occur p1 a1).

Lemma pl_produit_ref_ok_lem_0 :
 forall p : prec_list, pl_produit_ref_ok_0 p prec_empty.
Proof.
	unfold pl_produit_ref_ok_0 in |- *. intros. induction  p as [a0 p1 Hrecp1 p0 Hrecp0| ].
	induction  n as [| n Hrecn]. simpl in H. inversion H. simpl in H.
	right. right. exact H. induction  n as [| n Hrecn]. simpl in H.
	inversion H. simpl in H. right. right. exact H.
Qed.

Lemma pl_produit_ref_ok_lem_1 :
 forall p : prec_list, pl_produit_ref_ok_1 p prec_empty.
Proof.
	unfold pl_produit_ref_ok_1 in |- *. intros. induction  n as [| n Hrecn].
	simpl in H. inversion H. simpl in H. induction  p as [a p1 Hrecp1 p0 Hrecp0| ]; inversion H.
Qed.

Lemma pl_produit_ref_ok_lem_2 :
 forall p : prec_list, pl_produit_ref_ok_1 prec_empty p.
Proof.
	unfold pl_produit_ref_ok_1 in |- *. intros. induction  n as [| n Hrecn].
	inversion H. induction  p as [a p1 Hrecp1 p0 Hrecp0| ]; inversion H.
Qed.

Lemma pl_produit_ref_ok_lem_3 :
 forall (a : ad) (la ls p : prec_list),
 pl_produit_ref_ok_0 p ls ->
 pl_produit_ref_ok_1 p la -> pl_produit_ref_ok_0 p (prec_cons a la ls).
Proof.
	unfold pl_produit_ref_ok_0, pl_produit_ref_ok_1 in |- *.
	intros. elim (nat_sum n); intros. rewrite H2 in H1.
	inversion H1. elim H2. intros. rewrite H3 in H1.
	cut
  (pl_produit_0 a0 p (prec_cons a la ls) (S x) l =
   prec_cons (iad_conv a0 a) (pl_produit_1 p x la) (pl_produit_0 a0 p ls x l)). intros. rewrite H4 in H1. inversion H1. right. left. split with a. split.
	reflexivity. exact (prec_hd a la ls). left. elim (H0 b x H9). intros. elim H10. intros. elim H11. intros.
	elim H12. intros. elim H13. intros. split with x0.
	split with x1. split. exact H12. split. exact H14.
	exact (prec_int0 a x1 la ls H15). elim (H _ _ _ _ H9). intros. left. elim H10. intros. elim H11.
	intros. elim H12. intros. elim H14. intros.
	split with x0. split with x1. split. exact H13.
	split. exact H15. exact (prec_int1 a _ la _ H16).
	intros. elim H10. intros. right. left. elim H11.
	intros. elim H12. intros. split with x0. split.
	exact H13. exact (prec_int1 a _ la _ H14). intros.
	right. right. exact H11. reflexivity.
Qed.

Lemma pl_produit_ref_ok_lem_4 :
 forall (a : ad) (la ls p : prec_list),
 pl_produit_ref_ok_0 la p ->
 pl_produit_ref_ok_1 ls p -> pl_produit_ref_ok_1 (prec_cons a la ls) p.
Proof.
	unfold pl_produit_ref_ok_0, pl_produit_ref_ok_1 in |- *.
	intros. elim (nat_sum n); intros. rewrite H2 in H1.
	inversion H1. elim H2. intros. rewrite H3 in H1.
	elim (pl_sum p). intros. rewrite H4 in H1.
	inversion H1. intros. elim H4. intros. elim H5.
	intros. elim H6. intros. rewrite H7 in H1. cut
  (pl_produit_1 (prec_cons a la ls) (S x) (prec_cons x0 x1 x2) =
   pl_produit_0 a la (prec_cons x0 x1 x2) x
     (pl_produit_1 ls x (prec_cons x0 x1 x2))). intro.
	rewrite H8 in H1. rewrite <- H7 in H1. elim (H _ _ _ _ H1). intros. elim H9. intros. elim H10. intros.
	elim H11. intros. elim H13. intros. split with x3.
	split with x4. split. exact H12. split. exact (prec_int0 a x3 la ls H14). exact H15. intros.
	elim H9. intros. elim H10. intros. elim H11.
	intros. split with a. split with x3. split.
	exact H12. split. exact (prec_hd a la ls).
	exact H13. intros. elim (H0 _ _ H10). intros.
	elim H11. intros. elim H12. intros. elim H14.
	intros. split with x3. split with x4. split.
	exact H13. split. exact (prec_int1 a _ la _ H15).
	exact H16. reflexivity.
Qed.

Lemma pl_produit_ref_ok_lem_5 :
 forall p p' : prec_list,
 pl_produit_ref_ok_0 p p' /\ pl_produit_ref_ok_1 p p'.
Proof.
	exact
  (indprinciple_pl pl_produit_ref_ok_0 pl_produit_ref_ok_1
     pl_produit_ref_ok_lem_0 pl_produit_ref_ok_lem_1 pl_produit_ref_ok_lem_2
     pl_produit_ref_ok_lem_3 pl_produit_ref_ok_lem_4).
Qed.

Lemma pl_produit_ref_ok_lem_6 :
 forall (p0 p1 : prec_list) (b : ad),
 prec_occur (pl_produit p0 p1) b ->
 exists a0 : ad,
   (exists a1 : ad,
      b = iad_conv a0 a1 /\ prec_occur p0 a0 /\ prec_occur p1 a1).
Proof.
	unfold pl_produit in |- *. intro. intro. elim (pl_produit_ref_ok_lem_5 p0 p1). intros.
	exact (H0 _ _ H1).
Qed.

Lemma pl_produit_ref_ok :
 forall (p0 p1 : prec_list) (d0 d1 : preDTA),
 prec_list_ref_ok p0 d0 ->
 prec_list_ref_ok p1 d1 ->
 prec_list_ref_ok (pl_produit p0 p1) (preDTA_produit d0 d1).
Proof.
	unfold prec_list_ref_ok in |- *. intros. elim (pl_produit_ref_ok_lem_6 p0 p1 a H1). intros. elim H2.
	intros. elim H3. intros. elim H5. intros. elim (H _ H6).
	elim (H0 _ H7). intros. rewrite H4. split with (s_produit x2 x1). exact (predta_produit_2 d0 d1 x x0 x2 x1 H9 H8). 
Qed.

Lemma s_produit_l_ref_ok :
 forall (s : state) (a : ad) (p : prec_list) (d0 d1 : preDTA),
 state_ref_ok s d1 ->
 state_ref_ok (M1 prec_list a p) d0 ->
 state_ref_ok (s_produit_l a p s) (preDTA_produit d0 d1).
Proof.
	simple induction s. simpl in |- *. unfold state_ref_ok in |- *. intros. inversion H1.
	simpl in |- *. unfold state_ref_ok in |- *. intros. elim (bool_is_true_or_false (Neqb a1 a)); intros. rewrite H2 in H1. simpl in H1. elim (bool_is_true_or_false (Neqb a1 a2)); intros; rewrite H3 in H1;
  inversion H1. apply (pl_produit_ref_ok p a0 d0 d1).
	apply (H0 a1 p). simpl in |- *. rewrite (Neqb_correct a1). reflexivity.
	apply (H a a0). simpl in |- *. rewrite (Neqb_correct a). reflexivity.
	rewrite H2 in H1. inversion H1. intro. intro. intro. intro.
	unfold state_ref_ok in |- *. intros. cut (forall a : ad, state_ref_ok (M1 prec_list a p) d0). intros. elim (state_ref_ok_M2_destr _ _ _ H1). intros. simpl in H3. induction  a as [| p1]. induction  a0 as [| p1]. simpl in H3. exact (H _ _ _ _ H5 (H4 N0) _ _ H3). induction  p1 as [p1 Hrecp1| p1 Hrecp1| ].
	simpl in H3. inversion H3. simpl in H3. exact (H _ _ _ _ H5 (H4 N0) _ _ H3). simpl in H3. inversion H3. elim (positive_sum p1). intros. rewrite H7 in H3. simpl in H3.
	induction  a0 as [| p2]. inversion H3. elim (positive_sum p2); intros.
	rewrite H8 in H3. exact (H0 _ _ _ _ H6 (H4 N0) _ _ H3).
	elim H8; intros; elim H9; intros; rewrite H10 in H3.
	inversion H3. exact (H0 _ _ _ _ H6 (H4 N0) _ _ H3).
	intros. elim H7; intros; elim H8; intros; rewrite H9 in H3.
	simpl in H3. induction  a0 as [| p2]. exact (H _ _ _ _ H5 (H4 (Npos x)) _ _ H3). elim (positive_sum p2); intros. rewrite H10 in H3.
	inversion H3. elim H10; intros; elim H11; intros; rewrite H12 in H3. exact (H _ _ _ _ H5 (H4 (Npos x)) _ _ H3).
	inversion H3. simpl in H3. induction  a0 as [| p2]. inversion H3.
	elim (positive_sum p2); intros. rewrite H10 in H3. exact (H0 _ _ _ _ H6 (H4 (Npos x)) _ _ H3). elim H10; intros; elim H11; intros; rewrite H12 in H3. inversion H3. exact (H0 _ _ _ _ H6 (H4 (Npos x)) _ _ H3). intros. unfold state_ref_ok in |- *. intros. simpl in H4. elim (bool_is_true_or_false (Neqb a1 a2)); intros; rewrite H5 in H4. inversion H4.
	rewrite <- H7. apply (H2 a p). simpl in |- *. rewrite (Neqb_correct a).
	reflexivity. inversion H4.
Qed.

Lemma s_produit_r_ref_ok :
 forall (s : state) (a : ad) (p : prec_list) (d0 d1 : preDTA),
 state_ref_ok s d1 ->
 state_ref_ok (M1 prec_list a p) d0 ->
 state_ref_ok (s_produit_r a p s) (preDTA_produit d1 d0).
Proof.
	simple induction s. simpl in |- *. unfold state_ref_ok in |- *. intros. inversion H1.
	simpl in |- *. unfold state_ref_ok in |- *. intros. elim (bool_is_true_or_false (Neqb a1 a)); intros. rewrite H2 in H1. simpl in H1. elim (bool_is_true_or_false (Neqb a1 a2)); intros; rewrite H3 in H1;
  inversion H1. apply (pl_produit_ref_ok a0 p d1 d0). apply (H a a0). simpl in |- *. rewrite (Neqb_correct a). reflexivity.
	apply (H0 a1 p). simpl in |- *. rewrite (Neqb_correct a1). reflexivity.
	rewrite H2 in H1. inversion H1. intro. intro. intro. intro.
	unfold state_ref_ok in |- *. intros. cut (forall a : ad, state_ref_ok (M1 prec_list a p) d0). intro. elim (state_ref_ok_M2_destr _ _ _ H1). intros. simpl in H3. induction  a as [| p1]. simpl in H3. induction  a0 as [| p1]. exact (H _ _ _ _ H5 (H4 N0) _ _ H3). elim (positive_sum p1). intros. rewrite H7 in H3. inversion H3. intros. elim H7; intros; elim H8; intros; rewrite H9 in H3. exact (H _ _ _ _ H5 (H4 N0) _ _ H3). inversion H3. elim (positive_sum p1); intros. rewrite H7 in H3. simpl in H3. induction  a0 as [| p2]. inversion H3. elim (positive_sum p2); intros. rewrite H8 in H3. exact (H0 _ _ _ _ H6 (H4 N0) _ _ H3). elim H8; intros; elim H9; intros; rewrite H10 in H3. inversion H3. exact (H0 _ _ _ _ H6 (H4 N0) _ _ H3). elim H7; intros; elim H8; intros; rewrite H9 in H3. simpl in H3. induction  a0 as [| p2]. exact (H _ _ _ _ H5 (H4 (Npos x)) _ _ H3). elim (positive_sum p2); intros.
	rewrite H10 in H3. inversion H3. elim H10; intros; elim H11; intros; rewrite H12 in H3. exact (H _ _ _ _ H5 (H4 (Npos x)) _ _ H3). inversion H3. simpl in H3. induction  a0 as [| p2]. inversion H3. elim (positive_sum p2); intros. rewrite H10 in H3. exact (H0 _ _ _ _ H6 (H4 (Npos x)) _ _ H3).
	elim H10; intros; elim H11; intros; rewrite H12 in H3.
	inversion H3. exact (H0 _ _ _ _ H6 (H4 (Npos x)) _ _ H3).
	unfold state_ref_ok in |- *. intros. simpl in H4. elim (bool_is_true_or_false (Neqb a1 a2)); intros; rewrite H5 in H4. inversion H4. rewrite <- H7. apply (H2 a p).
	simpl in |- *. rewrite (Neqb_correct a). reflexivity.
	inversion H4.
Qed.

Lemma st_M0_ref_ok : forall d : preDTA, state_ref_ok (M0 prec_list) d.
Proof.
	unfold state_ref_ok in |- *. intros. inversion H.
Qed.

Lemma s_produit_ref_ok :
 forall (s0 s1 : state) (d0 d1 : preDTA),
 state_ref_ok s0 d0 ->
 state_ref_ok s1 d1 -> state_ref_ok (s_produit s0 s1) (preDTA_produit d0 d1).
Proof.
	simple induction s0. simple induction s1. intros. simpl in |- *. exact (st_M0_ref_ok (preDTA_produit d0 d1)). intros. simpl in |- *.
	exact (st_M0_ref_ok (preDTA_produit d0 d1)). intros.
	simpl in |- *. exact (st_M0_ref_ok (preDTA_produit d0 d1)).
	simple induction s1. intros. simpl in |- *. exact (st_M0_ref_ok (preDTA_produit d0 d1)). intros. replace (s_produit (M1 prec_list a a0) (M1 prec_list a1 a2)) with
  (s_produit_l a a0 (M1 prec_list a1 a2)). exact (s_produit_l_ref_ok _ _ _ _ _ H0 H). reflexivity.
	intros. replace (s_produit (M1 prec_list a a0) (M2 prec_list m m0)) with
  (s_produit_l a a0 (M2 prec_list m m0)). exact (s_produit_l_ref_ok _ _ _ _ _ H2 H1).
	reflexivity. simple induction s1. intros. intros. simpl in |- *.
	exact (st_M0_ref_ok (preDTA_produit d0 d1)). intros.
	replace (s_produit (M2 prec_list m m0) (M1 prec_list a a0)) with
  (s_produit_r a a0 (M2 prec_list m m0)).
	exact (s_produit_r_ref_ok _ _ _ _ _ H1 H2). reflexivity.
	intros. simpl in |- *. elim (state_ref_ok_M2_destr _ _ _ H3).
	intros. elim (state_ref_ok_M2_destr _ _ _ H4). intros.
	unfold state_ref_ok in |- *. intros. induction  a as [| p0]. simpl in H9.
	exact (H _ _ _ H5 H7 N0 p H9). induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]; simpl in H9. exact (H0 _ _ _ H6 H8 (Npos p0) p H9). exact (H _ _ _ H5 H7 _ _ H9). exact (H0 _ _ _ H6 H8 _ _ H9).
Qed.

Lemma preDTA_produit_l_ref_ok :
 forall (d d0 d1 : preDTA) (s : state) (a : ad),
 preDTA_ref_ok_distinct d d1 ->
 preDTA_ref_ok_distinct (M1 state a s) d0 ->
 preDTA_ref_ok_distinct (preDTA_produit_l a s d) (preDTA_produit d0 d1).
Proof.
	unfold preDTA_ref_ok_distinct in |- *. simple induction d. intros.
	inversion H1. intros. simpl in H1. elim (bool_is_true_or_false (Neqb (iad_conv a1 a) a2)); intros;
  rewrite H2 in H1; inversion H1. apply (s_produit_ref_ok s a0 d0 d1). apply (H0 a1 s).
	simpl in |- *. rewrite (Neqb_correct a1). reflexivity.
	apply (H a a0). simpl in |- *; rewrite (Neqb_correct a).
	reflexivity. intros. elim (preDTA_ref_ok_distinct_dest m m0 d1 H1). intros. cut (forall a : ad, preDTA_ref_ok_distinct (M1 state a s) d0). intros. induction  a as [| p]. simpl in H3.
	induction  a0 as [| p]. exact (H _ _ _ _ H4 (H6 N0) _ _ H3).
	induction  p as [p Hrecp| p Hrecp| ]. inversion H3. elim (positive_sum p).
	intros. rewrite H7 in H3. exact (H0 _ _ _ _ H5 (H6 N0) _ _ H3). intros. elim H7; intros; elim H8; intros; rewrite H9 in H3. exact (H _ _ _ _ H4 (H6 N0) _ _ H3). exact (H0 _ _ _ _ H5 (H6 N0) _ _ H3).
	inversion H3. induction  p as [p Hrecp| p Hrecp| ]. induction  a0 as [| p0]. simpl in H3.
	inversion H3. clear Hrecp. induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]; simpl in H3.
	elim (positive_sum p0); intros. rewrite H7 in H3.
	exact (H0 _ _ _ _ H5 (H6 (Npos p)) _ _ H3).
	elim H7; intros; elim H8; intros; rewrite H9 in H3.
	exact (H _ _ _ _ H4 (H6 (Npos p)) _ _ H3). exact (H0 _ _ _ _ H5 (H6 (Npos p)) _ _ H3). inversion H3.
	exact (H _ _ _ _ H4 (H6 (Npos p)) _ _ H3). 
	induction  a0 as [| p0]. simpl in H3. exact (H _ _ _ _ H4 (H6 (Npos p)) _ _ H3). induction  p0 as [p0 Hrecp0| p0 Hrecp0| ]; simpl in H3.
	inversion H3. elim (positive_sum p0); intros.
	rewrite H7 in H3. exact (H0 _ _ _ _ H5 (H6 (Npos p)) _ _ H3). elim H7; intros; elim H8; intros; rewrite H9 in H3. exact (H _ _ _ _ H4 (H6 (Npos p)) _ _ H3). exact (H0 _ _ _ _ H5 (H6 (Npos p)) _ _ H3). inversion H3. induction  a0 as [| p]. simpl in H3.
	inversion H3. induction  p as [p Hrecp| p Hrecp| ]. simpl in H3. elim (positive_sum p); intros. rewrite H7 in H3.
	exact (H0 _ _ _ _ H5 (H6 N0) _ _ H3). elim H7; intros; elim H8; intros; rewrite H9 in H3.
	exact (H _ _ _ _ H4 (H6 N0) _ _ H3). exact (H0 _ _ _ _ H5 (H6 N0) _ _ H3). simpl in H3. 
	inversion H3. simpl in H3. exact (H _ _ _ _ H4 (H6 N0) _ _ H3). unfold preDTA_ref_ok_distinct in |- *.
	intros. simpl in H6. elim (bool_is_true_or_false (Neqb a1 a2)); intros; rewrite H7 in H6;
  inversion H6. rewrite <- H9. apply (H2 a s).
	simpl in |- *. rewrite (Neqb_correct a). reflexivity.
Qed.

Lemma preDTA_produit_r_ref_ok :
 forall (d d0 d1 : preDTA) (s : state) (a : ad),
 preDTA_ref_ok_distinct d d0 ->
 preDTA_ref_ok_distinct (M1 state a s) d1 ->
 preDTA_ref_ok_distinct (preDTA_produit_r a s d) (preDTA_produit d0 d1).
Proof.
	unfold preDTA_ref_ok_distinct in |- *. simple induction d.
	intros. inversion H1. intros. simpl in H1.
	elim (bool_is_true_or_false (Neqb (iad_conv a a1) a2)); intros;
  rewrite H2 in H1; inversion H1.
	apply (s_produit_ref_ok a0 s d0 d1). apply (H a a0). simpl in |- *. rewrite (Neqb_correct a). reflexivity.
	apply (H0 a1 s). simpl in |- *. rewrite (Neqb_correct a1).
	reflexivity. intros. elim (preDTA_ref_ok_distinct_dest _ _ _ H1). intros. cut (forall a : ad, preDTA_ref_ok_distinct (M1 state a s) d1). intro. induction  a as [| p]. simpl in H3.
	induction  a0 as [| p]. exact (H _ _ _ _ H4 (H6 N0) _ _ H3).
	elim (positive_sum p); intros. rewrite H7 in H3.
	exact (H0 _ _ _ _ H5 (H6 N0) _ _ H3).
	elim H7; intros; elim H8; intros; rewrite H9 in H3.
	elim (positive_sum x); intros. rewrite H10 in H3.
	inversion H3. elim H10; intros; elim H11; intros; rewrite H12 in H3. exact (H _ _ _ _ H4 (H6 N0) _ _ H3). inversion H3. elim (positive_sum x); intros.
	rewrite H10 in H3. inversion H3. elim H10; intros; elim H11; intros; rewrite H12 in H3. exact (H0 _ _ _ _ H5 (H6 N0) _ _ H3). inversion H3. induction  p as [p Hrecp| p Hrecp| ]; simpl in H3. induction  a0 as [| p0]. inversion H3. elim (positive_sum p0); intros. rewrite H7 in H3.
	inversion H3. elim H7; intros; elim H8; intros; rewrite H9 in H3. elim (positive_sum p); intros.
	rewrite H10 in H3. elim (positive_sum x); intros.
	rewrite H11 in H3. exact (H _ _ _ _ H4 (H6 (Npos 1)) _ _ H3). elim H11; intros; elim H12; intros; rewrite H13 in H3. inversion H3. exact (H _ _ _ _ H4 (H6 (Npos 1)) _ _ H3). elim H10; intros; elim H11; intros; rewrite H12 in H3. elim (positive_sum x); intros. rewrite H13 in H3. exact (H _ _ _ _ H4 (H6 _) _ _ H3). elim H13; intros; elim H14; intros; rewrite H15 in H3. inversion H3. exact (H _ _ _ _ H4 (H6 _) _ _ H3). elim (positive_sum x); intros. rewrite H13 in H3. exact (H _ _ _ _ H4 (H6 _) _ _ H3). elim H13; intros; elim H14; intros; rewrite H15 in H3. inversion H3.
	exact (H _ _ _ _ H4 (H6 _) _ _ H3). elim (positive_sum x); intros. rewrite H10 in H3.
	exact (H0 _ _ _ _ H5 (H6 _) _ _ H3). elim H10; intros; elim H11; intros; rewrite H12 in H3.
	inversion H3. exact (H0 _ _ _ _ H5 (H6 _) _ _ H3).
	induction  a0 as [| p0]. exact (H _ _ _ _ H4 (H6 _) _ _ H3).
	elim (positive_sum p0); intros. rewrite H7 in H3.
	exact (H0 _ _ _ _ H5 (H6 _) _ _ H3). elim H7; intros; elim H8; intros; rewrite H9 in H3. elim (positive_sum x); intros. rewrite H10 in H3.
	inversion H3. elim H10; intros; elim H11; intros; rewrite H12 in H3. exact (H _ _ _ _ H4 (H6 _) _ _ H3). inversion H3. elim (positive_sum x); intros. rewrite H10 in H3. inversion H3.
	elim H10; intros; elim H11; intros; rewrite H12 in H3. exact (H0 _ _ _ _ H5 (H6 _) _ _ H3).
	inversion H3. induction  a0 as [| p]. inversion H3.
	elim (positive_sum p); intros. rewrite H7 in H3.
	inversion H3. elim H7; intros; elim H8; intros; rewrite H9 in H3. elim (positive_sum x); intros.
	rewrite H10 in H3. exact (H _ _ _ _ H4 (H6 _) _ _ H3). elim H10; intros; elim H11; intros; rewrite H12 in H3. inversion H3. exact (H _ _ _ _ H4 (H6 _) _ _ H3). elim (positive_sum x); intros.
	rewrite H10 in H3. exact (H0 _ _ _ _ H5 (H6 _) _ _ H3). elim H10; intros; elim H11; intros; rewrite H12 in H3. inversion H3. exact (H0 _ _ _ _ H5 (H6 _) _ _ H3). unfold preDTA_ref_ok_distinct in |- *.
	intros. simpl in H6. elim (bool_is_true_or_false (Neqb a1 a2)); intros; rewrite H7 in H6;
  inversion H6. rewrite <- H9. apply (H2 a s). simpl in |- *.
	rewrite (Neqb_correct a). reflexivity.
Qed.

Lemma preDTA_produit_ref_okd :
 forall d0 d1 d0' d1' : preDTA,
 preDTA_ref_ok_distinct d0 d0' ->
 preDTA_ref_ok_distinct d1 d1' ->
 preDTA_ref_ok_distinct (preDTA_produit d0 d1) (preDTA_produit d0' d1').
Proof.
	simple induction d0. simple induction d1. simpl in |- *. intros. unfold preDTA_ref_ok_distinct in |- *. intros. inversion H1. simpl in |- *.
	intros. unfold preDTA_ref_ok_distinct in |- *. intros. 
	inversion H1. intros. simpl in |- *. unfold preDTA_ref_ok_distinct in |- *.
	intros. inversion H3. simple induction d1. simpl in |- *. intros.
	unfold preDTA_ref_ok_distinct in |- *. intros. inversion H1.
	intros. replace (preDTA_produit (M1 state a a0) (M1 state a1 a2)) with
  (preDTA_produit_l a a0 (M1 state a1 a2)). exact (preDTA_produit_l_ref_ok _ _ _ _ _ H0 H). reflexivity. intros. replace (preDTA_produit (M1 state a a0) (M2 state m m0)) with
  (preDTA_produit_l a a0 (M2 state m m0)). exact (preDTA_produit_l_ref_ok _ _ _ _ _ H2 H1). reflexivity.
	simple induction d1. intros. simpl in |- *. unfold preDTA_ref_ok_distinct in |- *.
	intros. inversion H3. intros. replace (preDTA_produit (M2 state m m0) (M1 state a a0)) with
  (preDTA_produit_r a a0 (M2 state m m0)). exact (preDTA_produit_r_ref_ok _ _ _ _ _ H1 H2). reflexivity. intros. elim (preDTA_ref_ok_distinct_dest _ _ _ H3). elim (preDTA_ref_ok_distinct_dest _ _ _ H4). intros.
	simpl in |- *. unfold preDTA_ref_ok_distinct in |- *. intros.
	induction  a as [| p]. simpl in H9. exact (H _ _ _ H7 H5 _ _ H9). induction  p as [p Hrecp| p Hrecp| ]. simpl in H9. elim (positive_sum p); intros. rewrite H10 in H9. exact (H0 _ _ _ H8 H6 _ _ H9). elim H10; intros; elim H11; intros; rewrite H12 in H9. exact (H0 _ _ _ H8 H5 _ _ H9).
	exact (H0 _ _ _ H8 H6 _ _ H9). simpl in H9.
	elim (positive_sum p); intros. rewrite H10 in H9.
	exact (H _ _ _ H7 H6 _ _ H9). elim H10; intros; elim H11; intros; rewrite H12 in H9. exact (H _ _ _ H7 H5 _ _ H9). exact (H _ _ _ H7 H6 _ _ H9).
	simpl in H9. exact (H0 _ _ _ H8 H5 _ _ H9).
Qed.

Lemma preDTA_produit_ref_ok :
 forall d0 d1 : preDTA,
 preDTA_ref_ok d0 -> preDTA_ref_ok d1 -> preDTA_ref_ok (preDTA_produit d0 d1).
Proof.
	intros. cut (preDTA_ref_ok_distinct (preDTA_produit d0 d1) (preDTA_produit d0 d1)).
	intro. unfold preDTA_ref_ok_distinct in H1.
	elim (preDTA_ref_ok_def (preDTA_produit d0 d1)).
	intros. exact (H3 H1). apply (preDTA_produit_ref_okd d0 d1 d0 d1). unfold preDTA_ref_ok_distinct in |- *.
	elim (preDTA_ref_ok_def d0). intros. exact (H1 H _ _ H3). elim (preDTA_ref_ok_def d1); intros.
	exact (H1 H0).
Qed.

Lemma DTA_inter_ref_ok_invar :
 forall d0 d1 : DTA,
 DTA_ref_ok d0 -> DTA_ref_ok d1 -> DTA_ref_ok (inter d0 d1).
Proof.
	simple induction d0. simple induction d1. intros. simpl in H.
	simpl in H0. simpl in |- *. exact (preDTA_produit_ref_ok p p0 H H0).
Qed.

(* correction : appartenance de l'état final *)

Lemma inter_DTA_main_state_correct_invar :
 forall d0 d1 : DTA,
 DTA_main_state_correct d0 ->
 DTA_main_state_correct d1 -> DTA_main_state_correct (inter d0 d1).
Proof.
	simple induction d0. simple induction d1. simpl in |- *. unfold addr_in_preDTA in |- *. intros. elim H. intros.
	elim H0. intros. split with (s_produit x x0).
	exact (predta_produit_2 _ _ _ _ _ _ H1 H2).
Qed.