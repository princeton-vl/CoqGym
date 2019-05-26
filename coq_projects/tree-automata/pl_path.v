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
From IntMap Require Import Allmaps.
Require Import bases.
Require Import defs.
Require Import semantics.
Require Import signature.

(* reconnaissance des listes de termes par chemins dans les prec_list *)

Inductive pl_path : Set :=
  | pl_path_nil : pl_path
  | pl_path_cons : ad -> pl_path -> pl_path.

Inductive pl_path_incl : pl_path -> prec_list -> Prop :=
  | pl_path_incl_nil : pl_path_incl pl_path_nil prec_empty
  | pl_path_incl_cons :
      forall (plp : pl_path) (a : ad) (la ls : prec_list),
      pl_path_incl plp la ->
      pl_path_incl (pl_path_cons a plp) (prec_cons a la ls)
  | pl_path_incl_next :
      forall (plp : pl_path) (a : ad) (la ls : prec_list),
      pl_path_incl plp ls ->
      plp <> pl_path_nil -> pl_path_incl plp (prec_cons a la ls).

Inductive pl_path_recon : preDTA -> term_list -> pl_path -> Prop :=
  | pl_path_rec_nil : forall d : preDTA, pl_path_recon d tnil pl_path_nil
  | pl_path_rec_cons :
      forall (d : preDTA) (a : ad) (t : term) (plp : pl_path)
        (tl : term_list),
      reconnaissance d a t ->
      pl_path_recon d tl plp ->
      pl_path_recon d (tcons t tl) (pl_path_cons a plp).

Definition pl_path_rec_equiv_0_def (d : preDTA) (pl : prec_list)
  (tl : term_list) :=
  liste_reconnait d pl tl ->
  exists plp : pl_path, pl_path_incl plp pl /\ pl_path_recon d tl plp.

Fixpoint pl_path_length (plp : pl_path) : nat :=
  match plp with
  | pl_path_nil => 0
  | pl_path_cons _ p => S (pl_path_length p)
  end.

(* existence de chemins dans les prec_list *)

Lemma pl_path_exists :
 forall pl : prec_list, exists p : pl_path, pl_path_incl p pl.
Proof.
	simple induction pl. intros. elim H. intros. split with (pl_path_cons a x).
	exact (pl_path_incl_cons x a p p0 H1). split with pl_path_nil.
	exact pl_path_incl_nil.
Qed.

Lemma non_empty_pl_path_exists :
 forall pl : prec_list,
 pl <> prec_empty ->
 exists p : pl_path, pl_path_incl p pl /\ 1 <= pl_path_length p.
Proof.
	simple induction pl. intros. elim (pl_path_exists p). intros. split with (pl_path_cons a x).
	split. exact (pl_path_incl_cons x a p p0 H2). simpl in |- *. exact (le_n_S _ _ (le_O_n (pl_path_length x))). intros. elim (H (refl_equal _)).
Qed.

(* CNS de reconnaissance d'une liste de terme par une prec_list *)

Lemma pl_path_rec_equiv_0_0 :
 forall d : preDTA, pl_path_rec_equiv_0_def d prec_empty tnil.
Proof.
	unfold pl_path_rec_equiv_0_def in |- *. intros. inversion H. split with pl_path_nil.
	split. exact pl_path_incl_nil. exact (pl_path_rec_nil d).
Qed.

Lemma pl_path_rec_equiv_0_1 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list),
 reconnaissance d a hd ->
 liste_reconnait d la tl ->
 pl_path_rec_equiv_0_def d la tl ->
 pl_path_rec_equiv_0_def d (prec_cons a la ls) (tcons hd tl).
Proof.
	unfold pl_path_rec_equiv_0_def in |- *. intros. elim (H1 H0). intros. elim H3. intros.
	split with (pl_path_cons a x). split. exact (pl_path_incl_cons x a la ls H4).
	exact (pl_path_rec_cons d a hd x tl H H5).
Qed.

Lemma pl_path_rec_equiv_0_2 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list),
 liste_reconnait d ls (tcons hd tl) ->
 pl_path_rec_equiv_0_def d ls (tcons hd tl) ->
 pl_path_rec_equiv_0_def d (prec_cons a la ls) (tcons hd tl).
Proof.
	unfold pl_path_rec_equiv_0_def in |- *. intros. elim (H0 H). intros. split with x.
	elim H2. intros. split. apply (pl_path_incl_next x a la ls). exact H3.
	intro. rewrite H5 in H4. inversion H4. exact H4.
Qed.

Lemma pl_path_rec_equiv_0_3 :
 forall (p : preDTA) (p0 : prec_list) (t : term_list),
 liste_reconnait p p0 t -> pl_path_rec_equiv_0_def p p0 t.
Proof.
	exact
  (liste_reconnait_ind pl_path_rec_equiv_0_def pl_path_rec_equiv_0_0
     pl_path_rec_equiv_0_1 pl_path_rec_equiv_0_2).
Qed.

Lemma pl_path_rec_equiv_0 :
 forall (d : preDTA) (pl : prec_list) (tl : term_list),
 liste_reconnait d pl tl ->
 exists plp : pl_path, pl_path_incl plp pl /\ pl_path_recon d tl plp.
Proof.
	intros. elim (pl_path_rec_equiv_0_3 d pl tl H H). intros. split with x. exact H0.
Qed.

Definition pl_path_rec_equiv_1_def (plp : pl_path) 
  (pl : prec_list) :=
  pl_path_incl plp pl ->
  forall (d : preDTA) (tl : term_list) (n : nat),
  pl_path_recon d tl plp -> pl_tl_length pl n -> liste_reconnait d pl tl.

Lemma pl_path_rec_equiv_1_0 : pl_path_rec_equiv_1_def pl_path_nil prec_empty.
Proof.
	unfold pl_path_rec_equiv_1_def in |- *. intros. inversion H0. 
	exact (rec_empty d).
Qed.

Lemma pl_path_rec_equiv_1_1 :
 forall (plp : pl_path) (a : ad) (la ls : prec_list),
 pl_path_incl plp la ->
 pl_path_rec_equiv_1_def plp la ->
 pl_path_rec_equiv_1_def (pl_path_cons a plp) (prec_cons a la ls).
Proof.
	unfold pl_path_rec_equiv_1_def in |- *. intros. inversion H2. apply (rec_consi d a la ls t tl0). exact H8. induction  n as [| n Hrecn]. inversion H3. apply (H0 H d tl0 n H9). inversion H3. exact H11. exact H12.
Qed.

Lemma pl_path_rec_equiv_1_2 :
 forall (plp : pl_path) (a : ad) (la ls : prec_list),
 pl_path_incl plp ls ->
 pl_path_rec_equiv_1_def plp ls ->
 plp <> pl_path_nil -> pl_path_rec_equiv_1_def plp (prec_cons a la ls).
Proof.
	unfold pl_path_rec_equiv_1_def in |- *. intros. induction  n as [| n Hrecn].
        inversion_clear H4.
	induction  tl as [| t tl Hrectl]. inversion H3. rewrite <- H7 in H2. inversion_clear H2.
	elim H8; trivial.
        apply (rec_consn d a la ls t tl).
	apply (H0 H d (tcons t tl) (S n) H3). inversion H4. rewrite <- H8 in H.
	inversion H. elim H1; auto.
        exact H10.
Qed.

Lemma pl_path_rec_equiv_1_3 :
 forall (p : pl_path) (p0 : prec_list),
 pl_path_incl p p0 -> pl_path_rec_equiv_1_def p p0.
Proof.
	exact
  (pl_path_incl_ind pl_path_rec_equiv_1_def pl_path_rec_equiv_1_0
     pl_path_rec_equiv_1_1 pl_path_rec_equiv_1_2).
Qed.

Lemma pl_path_rec_equiv_1 :
 forall (plp : pl_path) (pl : prec_list),
 pl_path_incl plp pl ->
 forall (d : preDTA) (tl : term_list) (n : nat),
 pl_path_recon d tl plp -> pl_tl_length pl n -> liste_reconnait d pl tl.
Proof.
	intros. exact (pl_path_rec_equiv_1_3 plp pl H H d tl n H0 H1).
Qed.

Lemma pl_path_rec_length :
 forall (plp : pl_path) (tl : term_list) (d : preDTA),
 pl_path_recon d tl plp -> pl_path_length plp = lst_length tl.
Proof.
	simple induction plp. intros. inversion H. simpl in |- *. reflexivity. intros. inversion H0.
	simpl in |- *. rewrite (H tl0 d). reflexivity. exact H6.
Qed.

Definition liste_rec_length_def (d : preDTA) (pl : prec_list)
  (tl : term_list) : Prop :=
  forall n : nat,
  liste_reconnait d pl tl -> pl_tl_length pl n -> n = lst_length tl.

Lemma liste_rec_length_0 :
 forall d : preDTA, liste_rec_length_def d prec_empty tnil.
Proof.
	unfold liste_rec_length_def in |- *. intros. inversion H0. reflexivity.
Qed.

Lemma liste_rec_length_1 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list),
 reconnaissance d a hd ->
 liste_reconnait d la tl ->
 liste_rec_length_def d la tl ->
 liste_rec_length_def d (prec_cons a la ls) (tcons hd tl).
Proof.
	unfold liste_rec_length_def in |- *. intros. induction  n as [| n Hrecn]. inversion H3. inversion H3.
	simpl in |- *. rewrite <- (H1 n H0 H5). reflexivity. simpl in |- *. rewrite <- (H1 n H0 H6).
	reflexivity.
Qed.

Lemma liste_rec_length_2 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list),
 liste_reconnait d ls (tcons hd tl) ->
 liste_rec_length_def d ls (tcons hd tl) ->
 liste_rec_length_def d (prec_cons a la ls) (tcons hd tl).
Proof.
	unfold liste_rec_length_def in |- *. intros. simpl in |- *. induction  n as [| n Hrecn]. inversion H2.
	simpl in H0. inversion H2. rewrite <- H6 in H. inversion H.
	rewrite <- (H0 (S n) H H8). reflexivity.
Qed.

Lemma liste_rec_length_3 :
 forall (p : preDTA) (p0 : prec_list) (t : term_list),
 liste_reconnait p p0 t -> liste_rec_length_def p p0 t.
Proof.
	exact
  (liste_reconnait_ind liste_rec_length_def liste_rec_length_0
     liste_rec_length_1 liste_rec_length_2).
Qed.

Lemma liste_rec_length :
 forall (pl : prec_list) (tl : term_list) (d : preDTA) (n : nat),
 liste_reconnait d pl tl -> pl_tl_length pl n -> n = lst_length tl.
Proof.
	intros. exact (liste_rec_length_3 d pl tl H n H H0).
Qed.

Definition pl_path_incl_length_def (plp : pl_path) 
  (pl : prec_list) : Prop :=
  forall n : nat,
  pl_path_incl plp pl -> pl_tl_length pl n -> pl_path_length plp = n.

Lemma pl_path_incl_length_0 : pl_path_incl_length_def pl_path_nil prec_empty.
Proof.
	unfold pl_path_incl_length_def in |- *. intros. inversion H0. reflexivity.
Qed.

Lemma pl_path_incl_length_1 :
 forall (plp : pl_path) (a : ad) (la ls : prec_list),
 pl_path_incl plp la ->
 pl_path_incl_length_def plp la ->
 pl_path_incl_length_def (pl_path_cons a plp) (prec_cons a la ls).
Proof.
	unfold pl_path_incl_length_def in |- *. intros. inversion H2. simpl in |- *.
	rewrite (H0 n0 H H7). reflexivity. simpl in |- *. rewrite (H0 n0 H H7).
	reflexivity.
Qed.

Lemma pl_path_incl_length_2 :
 forall (plp : pl_path) (a : ad) (la ls : prec_list),
 pl_path_incl plp ls ->
 pl_path_incl_length_def plp ls ->
 plp <> pl_path_nil -> pl_path_incl_length_def plp (prec_cons a la ls).
Proof.
	unfold pl_path_incl_length_def in |- *. intros. inversion H3. rewrite <- H7 in H.
	inversion H. elim (H1 (sym_eq H9)). exact (H0 (S n0) H H9).
Qed.

Lemma pl_path_incl_length_3 :
 forall (p : pl_path) (p0 : prec_list),
 pl_path_incl p p0 -> pl_path_incl_length_def p p0.
Proof.
	exact
  (pl_path_incl_ind pl_path_incl_length_def pl_path_incl_length_0
     pl_path_incl_length_1 pl_path_incl_length_2).
Qed.

Lemma pl_path_incl_length :
 forall (plp : pl_path) (pl : prec_list) (n : nat),
 pl_path_incl plp pl -> pl_tl_length pl n -> pl_path_length plp = n.
Proof.
	intros. exact
  (pl_path_incl_ind pl_path_incl_length_def pl_path_incl_length_0
     pl_path_incl_length_1 pl_path_incl_length_2 plp pl H n H H0).
Qed.

(* CNS pour la propriété pl_tl_length, partie suffisante *)

Lemma forall_incl_length :
 forall (pl : prec_list) (n : nat),
 (forall p : pl_path, pl_path_incl p pl -> pl_path_length p = n) ->
 pl_tl_length pl n.
Proof.
	simple induction pl. intros. elim (nat_sum n); intros. rewrite H2 in H1.
	elim (non_empty_pl_path_exists (prec_cons a p p0)). intros.
	elim (le_Sn_O 0). elim H3. intros. rewrite (H1 x H4) in H5. exact H5.
	intro. inversion H3. elim H2. intros. rewrite H3. rewrite H3 in H1.
	elim (pl_sum p0); intros. rewrite H4. apply (pl_tl_S a p x). apply (H x). intros. apply (Sn_eq_Sm_n_eq_m (pl_path_length p1) x). replace (S (pl_path_length p1)) with (pl_path_length (pl_path_cons a p1)).
	apply (H1 (pl_path_cons a p1)). exact (pl_path_incl_cons p1 a p p0 H5).
	reflexivity. apply (pl_tl_propag a p p0 x). apply (H x). intros.
	cut (pl_path_length (pl_path_cons a p1) = S x). intros. simpl in H6.
	inversion H6. reflexivity. exact (H1 (pl_path_cons a p1) (pl_path_incl_cons p1 a p p0 H5)). apply (H0 (S x)). intros. apply (H1 p1). apply (pl_path_incl_next p1 a p p0 H5). intro. rewrite H6 in H5. elim H4. intros. elim H7. intros. elim H8. intros.
	rewrite H9 in H5. inversion H5. exact (H15 (refl_equal _)).
	intros. induction  n as [| n Hrecn]. exact pl_tl_O. elim (pl_path_exists prec_empty).
	intros. cut (S n = 0). intros. inversion H1. transitivity (pl_path_length x). symmetry  in |- *. exact (H x H0). inversion H0.
	reflexivity.
Qed.