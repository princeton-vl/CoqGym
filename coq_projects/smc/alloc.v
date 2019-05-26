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
Require Import Sumbool.
Require Import Arith.
Require Import ZArith NArith Nnat Ndec Ndigits.		
From IntMap Require Import Map.
From IntMap Require Import Allmaps.			
Require Import List.
Require Import Wf_nat.
  
Require Import misc.
Require Import bool_fun.
Require Import myMap.
Require Import config.

Section BDD_alloc.

Variable gc : BDDconfig -> list ad -> BDDconfig.
Hypothesis gc_is_OK : gc_OK gc.

(* The arguments for the allocation function *)
Variable cfg : BDDconfig.
Variable x : BDDvar.
Variable l r : ad.
Variable ul : list ad.

(* Conditions on the arguments for the allocation function *)
Hypothesis cfg_OK : BDDconfig_OK cfg.
Hypothesis ul_OK : used_list_OK cfg ul.
Hypothesis l_used' : used_node' cfg ul l.
Hypothesis r_used' : used_node' cfg ul r.
Hypothesis l_neq_r : Neqb l r = false.
Hypothesis
  xl_lt_x :
    forall (xl : BDDvar) (ll rl : ad),
    MapGet _ (bs_of_cfg cfg) l = Some (xl, (ll, rl)) ->
    BDDcompare xl x = Datatypes.Lt.
Hypothesis
  xr_lt_x :
    forall (xr : BDDvar) (lr rr : ad),
    MapGet _ (bs_of_cfg cfg) r = Some (xr, (lr, rr)) ->
    BDDcompare xr x = Datatypes.Lt.
Hypothesis
  no_dup :
    forall (x' : BDDvar) (l' r' a : ad),
    MapGet _ (bs_of_cfg cfg) a = Some (x', (l', r')) ->
    (x, (l, r)) <> (x', (l', r')).

Let new_cfg := gc cfg ul.

Lemma no_dup_new :
 forall (x' : BDDvar) (l' r' a : ad),
 MapGet _ (bs_of_cfg new_cfg) a = Some (x', (l', r')) ->
 (x, (l, r)) <> (x', (l', r')).
Proof.
  intros.  apply no_dup with (a := a).
  apply (proj2 (proj2 (gc_is_OK _ _ cfg_OK ul_OK))).  assumption.
Qed.

Lemma new_cfg_OK : BDDconfig_OK new_cfg.
Proof.
  exact (proj1 (gc_is_OK _ _ cfg_OK ul_OK)).
Qed.

Lemma new_cfg_nodes_preserved : used_nodes_preserved cfg new_cfg ul.
Proof.
  exact (proj1 (proj2 (gc_is_OK _ _ cfg_OK ul_OK))).
Qed.

Lemma new_l_OK : node_OK (bs_of_cfg new_cfg) l.
Proof.
  apply node_preserved_OK_bs with (bs := bs_of_cfg cfg).
  apply used_node'_OK_bs with (ul := ul).  exact (bs_of_cfg_OK _ cfg_OK).  
  assumption.  assumption.
  apply used_nodes_preserved_preserved'_bs with (ul := ul).
  exact (bs_of_cfg_OK _ cfg_OK).  exact new_cfg_nodes_preserved.  assumption.
Qed.

Lemma new_r_OK : node_OK (bs_of_cfg new_cfg) r.
Proof.
  apply node_preserved_OK_bs with (bs := bs_of_cfg cfg).
  apply used_node'_OK_bs with (ul := ul).  exact (bs_of_cfg_OK _ cfg_OK).
  assumption.  assumption.  
  apply used_nodes_preserved_preserved'_bs with (ul := ul).
  exact (bs_of_cfg_OK _ cfg_OK).  exact new_cfg_nodes_preserved.  assumption.
Qed.

Lemma BDD_OK_l : BDD_OK (bs_of_cfg new_cfg) l.
Proof.
  apply node_OK_BDD_OK.  exact (proj1 new_cfg_OK).  exact new_l_OK.
Qed.

Lemma BDD_OK_r : BDD_OK (bs_of_cfg new_cfg) r.
Proof.
  apply node_OK_BDD_OK.  exact (proj1 new_cfg_OK).  exact new_r_OK.
Qed.

Lemma new_xl_lt_x :
 forall (xl : BDDvar) (ll rl : ad),
 MapGet _ (bs_of_cfg new_cfg) l = Some (xl, (ll, rl)) ->
 BDDcompare xl x = Datatypes.Lt.
Proof.
  cut (node_OK (bs_of_cfg cfg) l).  intro H00.  elim H00.  intros.
  rewrite H in H0.  unfold bs_of_cfg in H0.
  rewrite (config_OK_zero _ new_cfg_OK) in H0.  discriminate.  intro.
  elim H; intros.  rewrite H0 in H1.  unfold bs_of_cfg in H1.
  rewrite (config_OK_one _ new_cfg_OK) in H1.  discriminate.
  elim (option_sum _ (MapGet _ (bs_of_cfg cfg) l)).  intro y.  elim y.  intro x0.
  elim x0.  intro y0.  intro y1.  elim y1; intros y2 y3 y4.
  cut (MapGet _ (bs_of_cfg new_cfg) l = Some (y0, (y2, y3))).  intro.
  rewrite H2 in H1.  injection H1.  intros.  rewrite H3 in y4.
  rewrite H4 in y4.  rewrite H5 in y4.  apply xl_lt_x with (ll := ll) (rl := rl).
  assumption.  cut (node_preserved_bs (bs_of_cfg cfg) (bs_of_cfg new_cfg) l).
  intro.  apply H2.  apply nodes_reachable_0.  assumption.  
  apply used_nodes_preserved_preserved'_bs with (ul := ul).
  exact (bs_of_cfg_OK _ cfg_OK).
  exact new_cfg_nodes_preserved.  assumption.  intro y.  unfold in_dom in H0.
  rewrite y in H0.  discriminate.  apply used_node'_OK_bs with (ul := ul).
  exact (bs_of_cfg_OK _ cfg_OK).  assumption.  assumption.
Qed.

Lemma new_xr_lt_x :
 forall (xr : BDDvar) (lr rr : ad),
 MapGet _ (bs_of_cfg new_cfg) r = Some (xr, (lr, rr)) ->
 BDDcompare xr x = Datatypes.Lt.
Proof.
  cut (node_OK (bs_of_cfg cfg) r).  intro H00.  elim H00.  intros.
  rewrite H in H0.  unfold bs_of_cfg in H0.
  rewrite (config_OK_zero _ new_cfg_OK) in H0.  discriminate.  intro.
  elim H; intros.  rewrite H0 in H1.  unfold bs_of_cfg in H1.
  rewrite (config_OK_one _ new_cfg_OK) in H1.  discriminate.
  elim (option_sum _ (MapGet _ (bs_of_cfg cfg) r)).  intro y.  elim y.  intro x0.
  elim x0.  intro y0.  intro y1.  elim y1; intros y2 y3 y4.
  cut (MapGet _ (bs_of_cfg new_cfg) r = Some (y0, (y2, y3))).  intro.
  rewrite H2 in H1.  injection H1.  intros.  rewrite H3 in y4.
  rewrite H4 in y4.  rewrite H5 in y4.  apply xr_lt_x with (lr := lr) (rr := rr).
  assumption.  cut (node_preserved_bs (bs_of_cfg cfg) (bs_of_cfg new_cfg) r).
  intro.  apply H2.  apply nodes_reachable_0.  assumption.
  apply used_nodes_preserved_preserved'_bs with (ul := ul).
  exact (bs_of_cfg_OK _ cfg_OK).
  exact new_cfg_nodes_preserved.  assumption.  intro y.  unfold in_dom in H0.
  rewrite y in H0.  discriminate.  apply used_node'_OK_bs with (ul := ul).
  exact (bs_of_cfg_OK _ cfg_OK).  assumption.  assumption.
Qed.

Definition BDDalloc : BDDconfig * ad :=
  match new_cfg with
  | (bs, (share, (fl, (cnt, (negm, orm))))) =>
      match fl with
      | a :: fl' =>
          (MapPut _ bs a (x, (l, r)),
          (MapPut3 _ share l r x a, (fl', (cnt, (negm, orm)))), a)
      | nil =>
          (MapPut _ bs cnt (x, (l, r)),
          (MapPut3 _ share l r x cnt, (fl, (ad_S cnt, (negm, orm)))), cnt)
      end
  end.
  
Lemma BDDalloc_lemma_1 :
 forall a : ad,
 MapGet _ (fst (fst BDDalloc)) a =
 (if Neqb a (snd BDDalloc)
  then Some (x, (l, r))
  else MapGet _ (fst new_cfg) a).
Proof.
  intro.  unfold BDDalloc in |- *.  rewrite (cfg_comp new_cfg).
  elim (list_sum _ (fl_of_cfg new_cfg)).  intro.  rewrite H.  simpl in |- *.
  rewrite
   (MapPut_semantics (BDDvar * (ad * ad)) (bs_of_cfg new_cfg)
      (cnt_of_cfg new_cfg) (x, (l, r)) a).
  rewrite (Neqb_comm a (cnt_of_cfg new_cfg)).  reflexivity.  intro.
  elim H; clear H.  intros.  elim H; clear H; intros.  rewrite H.  simpl in |- *.
  rewrite
   (MapPut_semantics (BDDvar * (ad * ad)) (bs_of_cfg new_cfg) x0 
      (x, (l, r)) a).
  rewrite (Neqb_comm a x0).  reflexivity.
Qed.

Lemma BDDalloc_lemma_2 :
 In (snd BDDalloc) (fl_of_cfg new_cfg) \/ cnt_of_cfg new_cfg = snd BDDalloc.
Proof.
  intros.  unfold BDDalloc in |- *.  rewrite (cfg_comp new_cfg).
  elim (list_sum _ (fl_of_cfg new_cfg)).  intros.  rewrite H.  simpl in |- *.
  unfold cnt_of_cfg in |- *.  simpl in |- *.  right; reflexivity.  intro.
  elim H; intros.  elim H0; intros.  rewrite H1.  simpl in |- *.  left.  left.
  reflexivity.
Qed.

Lemma BDDalloc_lemma_3 : MapGet _ (bs_of_cfg new_cfg) (snd BDDalloc) = None.
Proof.
  intros.  elim BDDalloc_lemma_2.  intros.  elim new_cfg_OK.  intros.
  elim H1; intros.  elim H3; intros.
  exact (proj2 (proj2 (proj1 (proj2 H4 (snd BDDalloc)) H))).
  intro.  rewrite <- H.
  apply (proj2 (proj1 (proj2 (proj2 (proj2 new_cfg_OK))))).
  apply Nleb_refl.
Qed.

Lemma BDDalloc_lemma_4 :
 fst (fst BDDalloc) = MapPut _ (bs_of_cfg new_cfg) (snd BDDalloc) (x, (l, r)).
Proof.
  intros.  unfold BDDalloc in |- *.  rewrite (cfg_comp new_cfg).  simpl in |- *.
  elim (fl_of_cfg new_cfg).  reflexivity.  intros.  reflexivity.
Qed.

Lemma BDDalloc_lemma_5 :
 fst (snd (fst BDDalloc)) =
 MapPut3 _ (share_of_cfg new_cfg) l r x (snd BDDalloc).
Proof.
  intros.  unfold BDDalloc in |- *.  rewrite (cfg_comp new_cfg).  simpl in |- *.
  elim (fl_of_cfg new_cfg).  reflexivity.  intros.  reflexivity.
Qed.

Lemma BDDalloc_preserves_nodes :
 nodes_preserved_bs (bs_of_cfg new_cfg) (fst (fst BDDalloc)).
Proof.
  intros.  unfold nodes_preserved_bs in |- *.  intros.  rewrite BDDalloc_lemma_1.
  elim (sumbool_of_bool (Neqb node (snd BDDalloc))).  intro y.
  rewrite (Neqb_complete _ _ y) in H.  rewrite BDDalloc_lemma_3 in H.
  discriminate H.  intro y.  rewrite y.  assumption.  
Qed.

Lemma BDDalloc_zero : MapGet _ (fst (fst BDDalloc)) BDDzero = None.
Proof.
  intros.  elim BDDalloc_lemma_2.  intro.  rewrite (BDDalloc_lemma_1 BDDzero).
  elim (sumbool_of_bool (Neqb BDDzero (snd BDDalloc))).  intro y.
  rewrite <- (Neqb_complete _ _ y) in H.
  absurd (Nleb (Npos 2) BDDzero = true).  unfold BDDzero in |- *.  unfold not in |- *.
  intro.  unfold Nleb in H0.  simpl in H0.  discriminate.  
  apply (proj1 (proj1 (proj2 (fl_of_cfg_OK _ new_cfg_OK) BDDzero) H)).
  intro y.  rewrite y.  exact (proj1 (bs_of_cfg_OK _ new_cfg_OK)).  intro.
  rewrite (BDDalloc_lemma_1 BDDzero).  rewrite <- H.
  elim (sumbool_of_bool (Neqb BDDzero (cnt_of_cfg new_cfg))).  intro y.
  cut (Nleb (Npos 2) (cnt_of_cfg new_cfg) = true).
  rewrite <- (Neqb_complete _ _ y).  intro.  unfold Nleb in H0.  simpl in H0.
  discriminate.  exact (proj1 (cnt_of_cfg_OK _ new_cfg_OK)).  intro y.
  rewrite y.  exact (proj1 (bs_of_cfg_OK _ new_cfg_OK)).
Qed.

Lemma BDDalloc_one : MapGet _ (fst (fst BDDalloc)) BDDone = None.
Proof.
  intros.  elim BDDalloc_lemma_2.  intro.  rewrite (BDDalloc_lemma_1 BDDone).
  elim (sumbool_of_bool (Neqb BDDone (snd BDDalloc))).  intro y.
  rewrite <- (Neqb_complete _ _ y) in H.
  absurd (Nleb (Npos 2) BDDone = true).  unfold BDDone in |- *.  unfold not in |- *.
  intro.  unfold Nleb in H0.  simpl in H0.  discriminate.  
  apply (proj1 (proj1 (proj2 (fl_of_cfg_OK _ new_cfg_OK) BDDone) H)).
  intro y.  rewrite y.  exact (proj1 (proj2 (bs_of_cfg_OK _ new_cfg_OK))).
  intro.  rewrite (BDDalloc_lemma_1 BDDone).  rewrite <- H.
  elim (sumbool_of_bool (Neqb BDDone (cnt_of_cfg new_cfg))).  intro y.
  cut (Nleb (Npos 2) (cnt_of_cfg new_cfg) = true).
  rewrite <- (Neqb_complete _ _ y).  intro.  unfold Nleb in H0.  simpl in H0.
  discriminate.  exact (proj1 (cnt_of_cfg_OK _ new_cfg_OK)).  intro y.
  rewrite y.  exact (proj1 (proj2 (bs_of_cfg_OK _ new_cfg_OK))).
Qed.

Lemma BDDalloc_BDD_OK : BDD_OK (fst (fst BDDalloc)) (snd BDDalloc).
Proof.
  intros.  unfold BDD_OK in |- *.  cut
   (MapGet (BDDvar * (ad * ad)) (fst (fst BDDalloc)) (snd BDDalloc) =
    Some (x, (l, r))).
  intro H.  rewrite H.  apply BDDbounded_2 with (x := x) (l := l) (r := r).  assumption.
  apply BDDlt_compare.  rewrite (ad_S_is_S x).  unfold lt in |- *.  apply le_n.
  apply not_true_is_false.  unfold not in |- *; intro H0.  rewrite l_neq_r in H0.
  discriminate.  elim (option_sum _ (MapGet _ (bs_of_cfg new_cfg) l)).  intro y.
  elim y; clear y.  intro x0.  elim x0; clear x0.  intros xl y0.
  elim y0; clear y0.  intros ll rl.  intro y.
  apply nodes_preserved_bounded with (bs := bs_of_cfg new_cfg).
  exact BDDalloc_preserves_nodes.  cut (BDDcompare (ad_S xl) x = Datatypes.Lt \/ ad_S xl = x).
  intro H0.  elim H0; intro H1.  apply increase_bound with (n := ad_S xl).
  cut (BDD_OK (bs_of_cfg new_cfg) l).  unfold BDD_OK in |- *.  rewrite y.
  intro; assumption.  exact BDD_OK_l.  assumption.  rewrite <- H1.
  cut (BDD_OK (bs_of_cfg new_cfg) l).  unfold BDD_OK in |- *.  rewrite y.
  intro; assumption.  exact BDD_OK_l.  apply BDDcompare_1.
  apply (new_xl_lt_x xl ll rl).  assumption.  intro y.
  cut (BDD_OK (bs_of_cfg new_cfg) l).  unfold BDD_OK in |- *.  rewrite y.  intro H0.
  elim H0; intro H1.  rewrite H1.  apply BDDbounded_0.  rewrite H1.
  apply BDDbounded_1.  exact BDD_OK_l.  cut (BDD_OK (bs_of_cfg new_cfg) r).
  intro H0.  unfold BDD_OK in H0.  elim (option_sum _ (MapGet _ (bs_of_cfg new_cfg) r)).
  intro y.  elim y; clear y.  intro x0.  elim x0; clear x0.  intros xr y0.
  elim y0; clear y0.  intros lr rr.  intro y.  apply nodes_preserved_bounded with (bs := bs_of_cfg new_cfg).
  exact BDDalloc_preserves_nodes.  rewrite y in H0.
  cut (BDDcompare (ad_S xr) x = Datatypes.Lt \/ ad_S xr = x).  intro H1.  elim H1; intro H2.
  apply increase_bound with (n := ad_S xr).  assumption.  assumption.
  rewrite <- H2; assumption.  apply BDDcompare_1.  apply (new_xr_lt_x xr lr rr).
  assumption.  intro y.  rewrite y in H0.  elim H0; intro.  rewrite H1.
  apply BDDbounded_0.  rewrite H1.  apply BDDbounded_1.  exact BDD_OK_r.
  rewrite BDDalloc_lemma_1.  rewrite (Neqb_correct (snd BDDalloc)).  reflexivity.
Qed.

Lemma BDDalloc_keeps_state_OK : BDDstate_OK (fst (fst BDDalloc)).
Proof.
  intros.  split.  apply BDDalloc_zero.  split.  apply BDDalloc_one.  
  unfold in_dom in |- *.  intro.  rewrite (BDDalloc_lemma_1 a).
  elim (sumbool_of_bool (Neqb a (snd BDDalloc))).  intro y.  rewrite y.  intro.
  rewrite (Neqb_complete _ _ y).  apply BDDalloc_BDD_OK.  intro y.  rewrite y.
  elim (option_sum _ (MapGet _ (bs_of_cfg new_cfg) a)).  intro y0.
  elim y0; clear y0; intro.  elim x0; clear x0; intros x1 y0.
  elim y0; clear y0; intros l1 r1.  intro y0.  intro H.  unfold BDD_OK in |- *.
  cut
   (MapGet (BDDvar * (ad * ad)) (fst (fst BDDalloc)) a =
    Some (x1, (l1, r1))).
  intro H0.  rewrite H0.  apply nodes_preserved_bounded with (bs := bs_of_cfg new_cfg).
  exact BDDalloc_preserves_nodes.  cut (BDD_OK (bs_of_cfg new_cfg) a).
  unfold BDD_OK in |- *.  rewrite y0.  intro; assumption.
  apply (proj2 (proj2 (bs_of_cfg_OK _ new_cfg_OK))).  unfold in_dom in |- *.
  rewrite y0.  reflexivity.  apply BDDalloc_preserves_nodes.  assumption.  
  intros y0 H.  unfold bs_of_cfg in y0.  rewrite y0 in H.  discriminate.
Qed.

Lemma BDDsharing_OK_1 :
 forall a : ad,
 MapGet _ (bs_of_cfg new_cfg) a = None ->
 BDDsharing_OK (MapPut _ (bs_of_cfg new_cfg) a (x, (l, r)))
   (MapPut3 _ (share_of_cfg new_cfg) l r x a).
Proof.
  intros.  split.  rewrite (MapPut3_semantics ad (share_of_cfg new_cfg) l r x l0 r0 x0 a).
  elim (sumbool_of_bool (Neqb l l0 && (Neqb r r0 && Neqb x x0))).
  intro y.  rewrite y.  intro H0.  injection H0; intro.  rewrite <- H1.
  rewrite
   (MapPut_semantics (BDDvar * (ad * ad)) (bs_of_cfg new_cfg) a (x, (l, r)) a)
   .
  rewrite (Neqb_correct a).  cut (Neqb l l0 = true /\ Neqb r r0 = true /\ Neqb x x0 = true).
  intro.  rewrite (Neqb_complete _ _ (proj1 H2)).
  rewrite (Neqb_complete _ _ (proj1 (proj2 H2))).
  rewrite (Neqb_complete _ _ (proj2 (proj2 H2))).  reflexivity.
  apply andb3_lemma.  assumption.  intro y.  rewrite y.
  rewrite
   (MapPut_semantics (BDDvar * (ad * ad)) (bs_of_cfg new_cfg) a 
      (x, (l, r)) a0).
  elim (sumbool_of_bool (Neqb a a0)).  intro y0.  intro H0.
  rewrite <- (Neqb_complete _ _ y0) in H0.  unfold share_of_cfg in H0.
  unfold bs_of_cfg in H.  rewrite (proj1 (proj1 (proj2 new_cfg_OK) x0 l0 r0 a) H0) in H.
  discriminate.  intros y0 H0.  rewrite y0.  unfold bs_of_cfg in |- *.  unfold share_of_cfg in H0.
  exact (proj1 (proj1 (proj2 new_cfg_OK) x0 l0 r0 a0) H0).  
  rewrite
   (MapPut_semantics (BDDvar * (ad * ad)) (bs_of_cfg new_cfg) a 
      (x, (l, r)) a0).
  intro H0.  elim (sumbool_of_bool (Neqb a a0)).  intro y.  rewrite y in H0.
  injection H0.  intros.  rewrite <- H1.  rewrite <- H2.  rewrite <- H3.
  rewrite (MapPut3_semantics ad (share_of_cfg new_cfg) l r x l r x a).
  rewrite (Neqb_correct l).  rewrite (Neqb_correct r).  rewrite (Neqb_correct x).
  simpl in |- *.  rewrite (Neqb_complete _ _ y).  reflexivity.  intro y.  rewrite y in H0.
  rewrite (MapPut3_semantics ad (share_of_cfg new_cfg) l r x l0 r0 x0 a).
  cut (Neqb l l0 && (Neqb r r0 && Neqb x x0) = false).  intro.
  rewrite H1.  unfold share_of_cfg in |- *.  unfold bs_of_cfg in H0.
  exact (proj2 (proj1 (proj2 new_cfg_OK) x0 l0 r0 a0) H0).
  apply andb3_lemma_1.  cut ((x, (l, r)) <> (x0, (l0, r0))).  intro.  unfold not in |- *; intro.
  apply H1.  injection H2; intros.  rewrite H3.  rewrite H4.  rewrite H5.
  reflexivity.  apply no_dup with (a := a0).
  apply (proj2 (proj2 (gc_is_OK _ _ cfg_OK ul_OK))).  assumption.
Qed.

Lemma BDDalloc_keeps_sharing_OK :
 BDDsharing_OK (fst (fst BDDalloc)) (fst (snd (fst BDDalloc))).
Proof.
  intros.  rewrite BDDalloc_lemma_4.  rewrite BDDalloc_lemma_5.
  apply BDDsharing_OK_1.  apply BDDalloc_lemma_3.
Qed.

Lemma BDDalloc_keeps_cnt_OK :
 cnt_OK (fst (fst BDDalloc)) (fst (snd (snd (snd (fst BDDalloc))))).
Proof.
  unfold BDDalloc, cnt_OK in |- *.  rewrite (cfg_comp new_cfg).
  elim (list_sum _ (fl_of_cfg new_cfg)).  intro.  rewrite H.  simpl in |- *.  split.
  apply Nleb_trans with (b := cnt_of_cfg new_cfg).  unfold cnt_of_cfg in |- *.
  exact (proj1 (proj1 (proj2 (proj2 (proj2 new_cfg_OK))))).
  unfold Nleb in |- *.  apply leb_correct.  rewrite (ad_S_is_S (cnt_of_cfg new_cfg)).
  apply le_S.  apply le_n.  intros.
  rewrite
   (MapPut_semantics (BDDvar * (ad * ad)) (bs_of_cfg new_cfg)
      (cnt_of_cfg new_cfg) (x, (l, r)) a).
  replace (Neqb (cnt_of_cfg new_cfg) a) with false.
  refine (proj2 (proj1 (proj2 (proj2 (proj2 new_cfg_OK)))) a _).
  apply Nleb_trans with (b := ad_S (cnt_of_cfg new_cfg)).  unfold Nleb in |- *.
  apply leb_correct.  rewrite (ad_S_is_S (cnt_of_cfg new_cfg)).
  apply le_S.  apply le_n.  assumption.  symmetry  in |- *.  apply ad_S_le_then_neq.
  assumption.  intro.  elim H; clear H; intros.  elim H; clear H; intros.
  rewrite H.  simpl in |- *.  split.
  exact (proj1 (proj1 (proj2 (proj2 (proj2 new_cfg_OK))))).
  intros.  rewrite
   (MapPut_semantics (BDDvar * (ad * ad)) (bs_of_cfg new_cfg) x0 
      (x, (l, r)) a).
  cut (Neqb x0 a = false).  intro; rewrite H1.
  apply (proj2 (proj1 (proj2 (proj2 (proj2 new_cfg_OK))))).
  exact H0.  apply ad_S_le_then_neq.  apply Nleb_trans with (b := cnt_of_cfg new_cfg).
  unfold cnt_of_cfg in |- *.  refine
   (proj1 (proj2 (proj1 (proj2 (proj1 (proj2 (proj2 new_cfg_OK))) x0) _))).
  unfold fl_of_cfg in H.  rewrite H.  simpl in |- *.  left; reflexivity.  assumption.
Qed.

Lemma BDDalloc_keeps_free_list_OK :
 BDDfree_list_OK (fst (fst BDDalloc)) (fst (snd (snd (fst BDDalloc))))
   (fst (snd (snd (snd (fst BDDalloc))))).
Proof.
  unfold BDDalloc in |- *.  rewrite (cfg_comp new_cfg).  elim (list_sum _ (fl_of_cfg new_cfg)).
  intro.  rewrite H.  simpl in |- *.  unfold BDDfree_list_OK in |- *.  split.  apply no_dup_nil.
  intro.  rewrite
   (MapPut_semantics (BDDvar * (ad * ad)) (bs_of_cfg new_cfg)
      (cnt_of_cfg new_cfg) (x, (l, r)) node).
  split.  simpl in |- *.  tauto.  intro.  elim H0; clear H0; intros.
  elim H1; clear H1; intros.  elim (sumbool_of_bool (Neqb (cnt_of_cfg new_cfg) node)).
  intro y.  rewrite y in H2.  discriminate.  intro y.  rewrite y in H2.
  absurd (In node (fl_of_cfg new_cfg)).  rewrite H.  simpl in |- *.  tauto.  
  apply (proj2 (proj2 (proj1 (proj2 (proj2 new_cfg_OK))) node)).
  split.  assumption.  split.  unfold Nleb in |- *.  apply leb_correct.
  rewrite (ad_S_is_S node).  apply lt_le_S.
  cut (nat_of_N node <= nat_of_N (cnt_of_cfg new_cfg)).  intro.
  elim (le_lt_or_eq _ _ H3).  tauto.  intro.  unfold cnt_of_cfg in y.
  cut (node = fst (snd (snd (snd new_cfg)))).  intro.  rewrite H5 in y.
  rewrite (Neqb_correct (fst (snd (snd (snd new_cfg))))) in y.  discriminate.
  rewrite <- (N_of_nat_of_N node).  rewrite H4.  apply N_of_nat_of_N.  
  apply le_S_n.  rewrite <- (ad_S_is_S node).
  rewrite <- (ad_S_is_S (cnt_of_cfg new_cfg)).  unfold Nleb in H1.
  apply leb_complete.  assumption.  assumption.  intro.
  elim H; clear H; intros.  elim H; clear H; intros.  rewrite H.  simpl in |- *.
  unfold BDDfree_list_OK in |- *.  split.  apply no_dup_cons_no_dup with (a := x0).
  unfold ad in *.
  rewrite <- H.  unfold fl_of_cfg in |- *.  exact (proj1 (proj1 (proj2 (proj2 new_cfg_OK)))).
  cut (~ In x0 x1).  intro.  intro.
  rewrite
   (MapPut_semantics (BDDvar * (ad * ad)) (bs_of_cfg new_cfg) x0 
      (x, (l, r)) node).
  split.  intro.  elim (sumbool_of_bool (Neqb x0 node)).  intro y.
  absurd (In node x1).  rewrite <- (Neqb_complete _ _ y).  assumption.
  assumption.  intro y.
  rewrite y.  apply (proj1 (proj2 (proj1 (proj2 (proj2 new_cfg_OK))) node)).
  unfold fl_of_cfg in H.  rewrite H.  apply in_cons.  assumption.  intros.
  elim (sumbool_of_bool (Neqb x0 node)).  intro y.  rewrite y in H1.
  elim H1; intros.  elim H3; intros.  discriminate.  intro y.
  rewrite y in H1.  unfold bs_of_cfg in H1.  cut (In node (fst (snd (snd new_cfg)))).
  unfold fl_of_cfg in H.  rewrite H.  intro.  elim (in_inv H2).  intro.
  rewrite H3 in y.  rewrite (Neqb_correct node) in y.  discriminate.  tauto.
  apply (proj2 (proj2 (proj1 (proj2 (proj2 new_cfg_OK))) node)).
  assumption.  apply no_dup_cons_no_in.  rewrite <- H.  unfold fl_of_cfg in |- *.
  exact (proj1 (proj1 (proj2 (proj2 new_cfg_OK)))).
Qed.

Lemma BDDalloc_orm_same : orm_of_cfg (fst BDDalloc) = orm_of_cfg new_cfg.
Proof.
  unfold orm_of_cfg, BDDalloc in |- *.  rewrite (cfg_comp new_cfg).  simpl in |- *.
  elim (fl_of_cfg new_cfg).  simpl in |- *.  reflexivity.  simpl in |- *.  reflexivity.
Qed.

Lemma BDDalloc_negm_same : negm_of_cfg (fst BDDalloc) = negm_of_cfg new_cfg.
Proof.
  unfold negm_of_cfg, BDDalloc in |- *.  rewrite (cfg_comp new_cfg).  simpl in |- *.
  elim (fl_of_cfg new_cfg).  simpl in |- *.  reflexivity.  simpl in |- *.  reflexivity.
Qed.

Lemma BDDalloc_um_same : um_of_cfg (fst BDDalloc) = um_of_cfg new_cfg.
Proof.
  unfold um_of_cfg, BDDalloc in |- *.  rewrite (cfg_comp new_cfg).  simpl in |- *.
  elim (fl_of_cfg new_cfg).  simpl in |- *.  reflexivity.  simpl in |- *.  reflexivity.
Qed.

Lemma BDDalloc_keeps_neg_memo_OK :
 BDDneg_memo_OK (bs_of_cfg (fst BDDalloc)) (negm_of_cfg (fst BDDalloc)).
Proof.
  rewrite BDDalloc_negm_same.  apply nodes_preserved_neg_memo_OK with (bs := bs_of_cfg new_cfg).
  exact BDDalloc_preserves_nodes.  exact (bs_of_cfg_OK _ new_cfg_OK).
  exact BDDalloc_keeps_state_OK.  exact (negm_of_cfg_OK _ new_cfg_OK).
Qed.

Lemma BDDalloc_keeps_or_memo_OK :
 BDDor_memo_OK (bs_of_cfg (fst BDDalloc)) (orm_of_cfg (fst BDDalloc)).
Proof.
  rewrite BDDalloc_orm_same.  apply nodes_preserved_or_memo_OK with (bs := bs_of_cfg new_cfg).
  exact BDDalloc_preserves_nodes.  exact (bs_of_cfg_OK _ new_cfg_OK).
  exact BDDalloc_keeps_state_OK.  exact (orm_of_cfg_OK _ new_cfg_OK).
Qed.

Lemma BDDalloc_keeps_univ_memo_OK :
 BDDuniv_memo_OK (bs_of_cfg (fst BDDalloc)) (um_of_cfg (fst BDDalloc)).
Proof.
  rewrite BDDalloc_um_same.  apply nodes_preserved_um_OK with (bs := bs_of_cfg new_cfg).
  exact BDDalloc_preserves_nodes.  exact (bs_of_cfg_OK _ new_cfg_OK).
  exact BDDalloc_keeps_state_OK.  exact (um_of_cfg_OK _ new_cfg_OK).
Qed.

(* The following results are used for BDDmake *)
Lemma BDDalloc_keeps_config_OK : BDDconfig_OK (fst BDDalloc).
Proof.
  unfold BDDconfig_OK in |- *.  split.  apply BDDalloc_keeps_state_OK.  split.
  exact BDDalloc_keeps_sharing_OK.  split.  exact BDDalloc_keeps_free_list_OK.  
  split.  exact BDDalloc_keeps_cnt_OK.  split.
  exact BDDalloc_keeps_neg_memo_OK.  split.  exact BDDalloc_keeps_or_memo_OK.
  exact BDDalloc_keeps_univ_memo_OK.
Qed.
 
Lemma BDDalloc_preserves_used_nodes :
 used_nodes_preserved cfg (fst BDDalloc) ul.
Proof.
  apply used_nodes_preserved_trans with (cfg2 := new_cfg).  assumption.  
  exact new_cfg_nodes_preserved.  apply nodes_preserved_used_nodes_preserved.
  exact BDDalloc_preserves_nodes.
Qed.

Lemma BDDalloc_node_OK : config_node_OK (fst BDDalloc) (snd BDDalloc).
Proof.
  unfold config_node_OK in |- *.  apply BDD_OK_node_OK.  apply BDDalloc_BDD_OK.
Qed.

Lemma BDDallocGet :
 MapGet _ (fst (fst BDDalloc)) (snd BDDalloc) = Some (x, (l, r)).
Proof.
  rewrite (BDDalloc_lemma_1 (snd BDDalloc)).
  rewrite (Neqb_correct (snd BDDalloc)).  reflexivity.
Qed.

End BDD_alloc.