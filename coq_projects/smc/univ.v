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
Require Import alloc.
Require Import make.
Require Import op.

Section BDDuniv_sec.


Variable gc : BDDconfig -> list ad -> BDDconfig.
Hypothesis gc_is_OK : gc_OK gc.

Fixpoint BDDuniv_1 (cfg : BDDconfig) (ul : list ad) 
 (node : ad) (y : BDDvar) (bound : nat) {struct bound} : 
 BDDconfig * ad :=
  match bound with
  | O => (* Error *)  (initBDDconfig, BDDzero)
  | S bound' =>
      match MapGet2 _ (um_of_cfg cfg) node y with
      | Some node' => (cfg, node')
      | None =>
          match MapGet _ (fst cfg) node with
          | None => (cfg, node)
          | Some (x, (l, r)) =>
              match BDDcompare x y with
              | Datatypes.Lt => (cfg, node)
              | Datatypes.Eq => BDDand gc cfg ul l r
              | Datatypes.Gt =>
                  match BDDuniv_1 cfg ul l y bound' with
                  | (cfgl, nodel) =>
                      match BDDuniv_1 cfgl (nodel :: ul) r y bound' with
                      | (cfgr, noder) =>
                          match
                            BDDmake gc cfgr x nodel noder
                              (noder :: nodel :: ul)
                          with
                          | (cfg', node') =>
                              (BDDuniv_memo_put cfg' y node node', node')
                          end
                      end
                  end
              end
          end
      end
  end.

Lemma BDDuniv_1_lemma :
 forall (bound : nat) (cfg : BDDconfig) (ul : list ad) 
   (u : BDDvar) (node : ad),
 nat_of_N (node_height cfg node) < bound ->
 BDDconfig_OK cfg ->
 used_list_OK cfg ul ->
 used_node' cfg ul node ->
 BDDconfig_OK (fst (BDDuniv_1 cfg ul node u bound)) /\
 config_node_OK (fst (BDDuniv_1 cfg ul node u bound))
   (snd (BDDuniv_1 cfg ul node u bound)) /\
 used_nodes_preserved cfg (fst (BDDuniv_1 cfg ul node u bound)) ul /\
 Nleb
   (node_height (fst (BDDuniv_1 cfg ul node u bound))
      (snd (BDDuniv_1 cfg ul node u bound))) (node_height cfg node) = true /\
 bool_fun_eq
   (bool_fun_of_BDD (fst (BDDuniv_1 cfg ul node u bound))
      (snd (BDDuniv_1 cfg ul node u bound)))
   (bool_fun_forall u (bool_fun_of_BDD cfg node)).
Proof.
  simple induction bound.  intros.  absurd (nat_of_N (node_height cfg node) < 0).
  apply lt_n_O.  assumption.  simpl in |- *.  intros.
  elim (option_sum _ (MapGet2 ad (um_of_cfg cfg) node u)).  intro y.
  elim y; clear y; intros node' H4.  rewrite H4.  simpl in |- *.
  elim (um_of_cfg_OK _ H1 u node node' H4).  intros.  split.  assumption.  
  split.  inversion H6.  inversion H8.  assumption.  split.
  apply used_nodes_preserved_refl.  split.  exact (proj1 (proj2 H6)).
  exact (proj2 (proj2 H6)).  intro y.  rewrite y.
  elim (option_sum _ (MapGet (BDDvar * (ad * ad)) (fst cfg) node)).  intro y0.
  elim y0; clear y0.
  intro x; elim x; clear x; intros x x0; elim x0; clear x0; intros l r H4.
  rewrite H4.  cut (used_node' cfg ul l).  cut (used_node' cfg ul r).
  elim (relation_sum (BDDcompare x u)).  intro y0.  elim y0; clear y0.
  intros y0.  rewrite y0.  split.  apply BDDand_config_OK.  assumption.  
  assumption.  assumption.  assumption.  assumption.  split.
  apply BDDand_node_OK.  assumption.  assumption.  assumption.  assumption.  
  assumption.  split.  apply BDDand_used_nodes_preserved.  assumption.
  assumption.  assumption.  assumption.  assumption.  split.
  apply
   Nleb_trans with (b := BDDvar_max (node_height cfg l) (node_height cfg r)).
  apply BDDand_var_le.  assumption.  assumption.  assumption.  assumption.  
  assumption.  unfold Nleb in |- *.
  rewrite (BDDvar_max_max (node_height cfg l) (node_height cfg r)).
  apply leb_correct.  apply lt_le_weak.  apply
   lt_le_trans
    with
      (m := max (nat_of_N (node_height cfg node))
              (nat_of_N (node_height cfg node))).
  apply lt_max_1_2.  apply BDDcompare_lt.  unfold node_height in |- *.
  apply bs_node_height_left with (x := x) (r := r).  exact (proj1 H1).  assumption.
  apply BDDcompare_lt.  unfold node_height in |- *.
  apply bs_node_height_right with (x := x) (l := l).  exact (proj1 H1).  assumption.
  rewrite (max_x_x_eq_x (nat_of_N (node_height cfg node))).  apply le_n.  
  rewrite <- (BDD_EGAL_complete _ _ y0).
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_forall u
                (bool_fun_if x (bool_fun_of_BDD cfg r)
                   (bool_fun_of_BDD cfg l))).
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_and (bool_fun_of_BDD cfg r) (bool_fun_of_BDD cfg l)).
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_and (bool_fun_of_BDD cfg l) (bool_fun_of_BDD cfg r)).
  apply BDDand_is_and.  assumption.  assumption.  assumption.  assumption.  
  assumption.  apply bool_fun_and_comm.  apply bool_fun_eq_sym.
  rewrite (BDD_EGAL_complete _ _ y0).  apply bool_fun_forall_if_egal.
  unfold bool_fun_of_BDD in |- *.  rewrite <- (BDD_EGAL_complete _ _ y0).
  apply BDDvar_independent_high with (x := x) (l := l) (node := node).
  exact (proj1 H1).  assumption.  unfold bool_fun_of_BDD in |- *.
  rewrite <- (BDD_EGAL_complete _ _ y0).
  apply BDDvar_independent_low with (x := x) (r := r) (node := node).  exact (proj1 H1).
  assumption.  rewrite <- (BDD_EGAL_complete _ _ y0).
  apply bool_fun_forall_preserves_eq.  apply bool_fun_eq_sym.
  apply bool_fun_of_BDD_int.  assumption.  assumption.  intros y0.  rewrite y0.
  split.  assumption.  split.  apply used_node'_OK with (ul := ul).  assumption.
  assumption.  assumption.  split.  apply used_nodes_preserved_refl.  split.
  apply Nleb_refl.  simpl in |- *.  apply bool_fun_eq_sym.
  apply bool_fun_forall_independent.  unfold bool_fun_of_BDD in |- *.
  apply BDDvar_independent_bs.  exact (proj1 H1).  
  fold (node_OK (fst cfg) node) in |- *.  fold (config_node_OK cfg node) in |- *.
  apply used_node'_OK with (ul := ul).  assumption.  assumption.  assumption.
  unfold bs_node_height in |- *.  rewrite H4.  unfold Nleb in |- *.  rewrite (ad_S_is_S x).
  apply leb_correct.  fold lt in |- *.  fold (nat_of_N x < nat_of_N u) in |- *.
  apply BDDcompare_lt.  assumption.  intros y0 H5 H6.  rewrite y0.
  elim (prod_sum _ _ (BDDuniv_1 cfg ul l u n)).  intros cfgl H7.
  elim H7; clear H7.  intros nodel H7.  rewrite H7.
  elim (prod_sum _ _ (BDDuniv_1 cfgl (nodel :: ul) r u n)).  intros cfgr H8.
  elim H8; clear H8.  intros noder H8.  rewrite H8.  elim (prod_sum _ _ (BDDmake gc cfgr x nodel noder (noder :: nodel :: ul))).
  intros cfg' H9.  elim H9; clear H9.  intros node' H9.  rewrite H9.  simpl in |- *.  
  cut
   (BDDconfig_OK cfgl /\
    config_node_OK cfgl nodel /\
    used_nodes_preserved cfg cfgl ul /\
    Nleb (node_height cfgl nodel) (node_height cfg l) = true /\
    bool_fun_eq (bool_fun_of_BDD cfgl nodel)
      (bool_fun_forall u (bool_fun_of_BDD cfg l))).
  intro.  elim H10; clear H10; intros.  elim H11; clear H11; intros.
  elim H12; clear H12; intros.  elim H13; clear H13; intros.
  cut (config_node_OK cfg l).  cut (config_node_OK cfg r).  intros.
  cut (used_list_OK cfgl ul).  intro.  cut (used_list_OK cfgl (nodel :: ul)).
  intro.  cut (used_node' cfgl ul r).  intro.
  cut (used_node' cfgl (nodel :: ul) r).  intro.  
  cut
   (BDDconfig_OK cfgr /\
    config_node_OK cfgr noder /\
    used_nodes_preserved cfgl cfgr (nodel :: ul) /\
    Nleb (node_height cfgr noder) (node_height cfgl r) = true /\
    bool_fun_eq (bool_fun_of_BDD cfgr noder)
      (bool_fun_forall u (bool_fun_of_BDD cfgl r))).
  intro.  elim H21; clear H21; intros.  elim H22; clear H22; intros.
  elim H23; clear H23; intros.  elim H24; clear H24; intros.
  cut (used_list_OK cfgr (nodel :: ul)).  intro.
  cut (used_list_OK cfgr (noder :: nodel :: ul)).  intro.
  cut (used_node' cfgr (noder :: nodel :: ul) nodel).
  cut (used_node' cfgr (noder :: nodel :: ul) noder).  intros.
  cut
   (forall (xl : BDDvar) (ll rl : ad),
    MapGet _ (fst cfgr) nodel = Some (xl, (ll, rl)) ->
    BDDcompare xl x = Datatypes.Lt).
  cut
   (forall (xr : BDDvar) (lr rr : ad),
    MapGet _ (fst cfgr) noder = Some (xr, (lr, rr)) ->
    BDDcompare xr x = Datatypes.Lt).
  intros.  cut (BDDconfig_OK cfg').
  cut (used_nodes_preserved cfgr cfg' (noder :: nodel :: ul)).
  cut (config_node_OK cfg' node').

  cut
   (bool_fun_eq (bool_fun_of_BDD cfg' node')
      (bool_fun_if x (bool_fun_of_BDD cfgr noder)
         (bool_fun_of_BDD cfgr nodel))).
  cut (Nleb (node_height cfg' node') (ad_S x) = true).  intros.
  cut (config_node_OK cfg' node).  intro.
  cut (nodes_preserved cfg' (BDDuniv_memo_put cfg' u node node')).  intro.
  cut (BDDconfig_OK (BDDuniv_memo_put cfg' u node node')).  intro.  split.
  assumption.  split.  apply nodes_preserved_config_node_OK with (cfg1 := cfg').
  assumption.  assumption.  split.
  apply used_nodes_preserved_trans with (cfg2 := cfgr).  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfgl).  assumption.  assumption.
  apply used_nodes_preserved_cons with (node := nodel).  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfg').  assumption.
  apply used_nodes_preserved_cons with (node := nodel).
  apply used_nodes_preserved_cons with (node := noder).
  assumption.  apply nodes_preserved_used_nodes_preserved.  assumption.
  rewrite
   (Neqb_complete (node_height (BDDuniv_memo_put cfg' u node node') node')
      (node_height cfg' node')).
  split.  apply Nleb_trans with (b := ad_S x).  assumption.
  unfold node_height in |- *.  unfold bs_node_height in |- *.
  rewrite H4.  apply Nleb_refl.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg' node').
  apply nodes_preserved_bool_fun.  assumption.  assumption.  assumption.
  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_if x (bool_fun_of_BDD cfgr noder)
                (bool_fun_of_BDD cfgr nodel)).
  assumption.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_if x (bool_fun_forall u (bool_fun_of_BDD cfg r))
                (bool_fun_forall u (bool_fun_of_BDD cfg l))).
  apply bool_fun_if_preserves_eq.  apply
   bool_fun_eq_trans with (bf2 := bool_fun_forall u (bool_fun_of_BDD cfgl r)).
  assumption.  apply bool_fun_forall_preserves_eq.
  apply used_nodes_preserved'_bool_fun with (ul := ul).
  assumption.  assumption.  assumption.  assumption.  assumption.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfgl nodel).
  apply used_nodes_preserved'_bool_fun with (ul := nodel :: ul).  assumption.
  assumption.  assumption.  assumption.  apply used_node'_cons_node_ul.
  assumption.  apply bool_fun_eq_sym.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_forall u
                (bool_fun_if x (bool_fun_of_BDD cfg r)
                   (bool_fun_of_BDD cfg l))).
  apply bool_fun_forall_preserves_eq.  apply bool_fun_of_BDD_int.  assumption.
  assumption.  apply bool_fun_forall_orthogonal.  apply not_true_is_false.
  unfold not in |- *; intro.  rewrite (Neqb_complete _ _ H40) in y0.
  rewrite (BDD_EGAL_correct u) in y0.  discriminate y0.  
  apply nodes_preserved_node_height_eq.
  assumption.  assumption.  assumption.  assumption.  apply BDDum_put_OK.
  assumption.  assumption.  assumption.
  rewrite (Neqb_complete (node_height cfg' node) (node_height cfg node)).
  unfold node_height at 2 in |- *.  unfold bs_node_height in |- *.  rewrite H4.  assumption.  
  apply used_nodes_preserved'_node_height_eq with (ul := ul).  assumption.  
  assumption.  apply used_nodes_preserved_trans with (cfg2 := cfgl).  assumption.
  assumption.  apply used_nodes_preserved_cons with (node := nodel).
  apply used_nodes_preserved_trans with (cfg2 := cfgr).  assumption.  assumption.  
  apply used_nodes_preserved_cons with (node := noder).  assumption.  assumption.  
  assumption.  
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_if x (bool_fun_of_BDD cfgr noder)
                (bool_fun_of_BDD cfgr nodel)).
  assumption.
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_forall u (bool_fun_of_BDD cfg node)).
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_if x (bool_fun_forall u (bool_fun_of_BDD cfg r))
                (bool_fun_forall u (bool_fun_of_BDD cfg l))).
  apply bool_fun_if_preserves_eq.
  apply
   bool_fun_eq_trans with (bf2 := bool_fun_forall u (bool_fun_of_BDD cfgl r)).
  assumption.  apply bool_fun_forall_preserves_eq.  
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  assumption.  
  assumption.  assumption.  assumption.  
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfgl nodel).
  apply used_nodes_preserved'_bool_fun with (ul := nodel :: ul).  assumption.  
  assumption.  assumption.  assumption.  apply used_node'_cons_node_ul.  
  assumption. 
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_forall u
                (bool_fun_if x (bool_fun_of_BDD cfg r)
                   (bool_fun_of_BDD cfg l))).
  apply bool_fun_eq_sym.  apply bool_fun_forall_orthogonal.
  apply not_true_is_false.  unfold not in |- *; intro.
  rewrite (Neqb_complete _ _ H39) in y0.  rewrite (BDD_EGAL_correct u) in y0.
  discriminate y0.
  apply bool_fun_forall_preserves_eq.  apply bool_fun_eq_sym.
  apply bool_fun_of_BDD_int.  assumption.  assumption.
  apply bool_fun_forall_preserves_eq.  apply bool_fun_eq_sym.
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfgl).  assumption.  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfgr).  assumption.
  apply used_nodes_preserved_cons with (node := nodel).  assumption.
  apply used_nodes_preserved_cons with (node := nodel).
  apply used_nodes_preserved_cons with (node := noder).  assumption.  assumption.
  assumption.  apply BDDum_put_nodes_preserved.
  apply used_nodes_preserved_node_OK' with (ul := ul) (cfg := cfg).  assumption.
  assumption.  assumption.  apply used_nodes_preserved_trans with (cfg2 := cfgl).
  assumption.  assumption.  apply used_nodes_preserved_trans with (cfg2 := cfgr).
  assumption.  apply used_nodes_preserved_cons with (node := nodel).  assumption.
  apply used_nodes_preserved_cons with (node := nodel).
  apply used_nodes_preserved_cons with (node := noder).  assumption.
  replace cfg' with
   (fst (BDDmake gc cfgr x nodel noder (noder :: nodel :: ul))).
  replace node' with
   (snd (BDDmake gc cfgr x nodel noder (noder :: nodel :: ul))).
  apply BDDmake_node_height_le.  assumption. 
  assumption.  rewrite H9; reflexivity.  rewrite H9; reflexivity.
  replace cfg' with
   (fst (BDDmake gc cfgr x nodel noder (noder :: nodel :: ul))).
  replace node' with
   (snd (BDDmake gc cfgr x nodel noder (noder :: nodel :: ul))).
  apply BDDmake_bool_fun.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  rewrite H9.  reflexivity.  rewrite H9.
reflexivity.
  replace cfg' with
   (fst (BDDmake gc cfgr x nodel noder (noder :: nodel :: ul))).
  replace node' with
   (snd (BDDmake gc cfgr x nodel noder (noder :: nodel :: ul))).
  apply BDDmake_node_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  rewrite H9.  reflexivity.  rewrite H9.
reflexivity.
 replace cfg' with
  (fst (BDDmake gc cfgr x nodel noder (noder :: nodel :: ul))).
  replace node' with
   (snd (BDDmake gc cfgr x nodel noder (noder :: nodel :: ul))).
  apply BDDmake_preserves_used_nodes.  assumption.  assumption.  assumption. 

  rewrite H9.  reflexivity.  rewrite H9.  reflexivity.
  replace cfg' with
   (fst (BDDmake gc cfgr x nodel noder (noder :: nodel :: ul))).
  apply BDDmake_keeps_config_OK.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.   assumption.
  rewrite H9.  reflexivity.
  intros.  rewrite (ad_S_compare xr x).
  replace (ad_S xr) with (node_height cfgr noder).
  replace (ad_S x) with (node_height cfg node).   (* Unfold node_height in H24.*)
  apply BDDlt_compare.  apply le_lt_trans with (m := nat_of_N (node_height cfgl r)).
  apply leb_complete.  assumption.
  rewrite (Neqb_complete (node_height cfgl r) (node_height cfg r)).
  apply BDDcompare_lt.  unfold node_height in |- *.  apply bs_node_height_right with (x := x) (l := l).
  exact (proj1 H1).  assumption.
  apply used_nodes_preserved'_node_height_eq with (ul := ul).  assumption.
  assumption.  assumption.  assumption.  assumption.
  unfold node_height in |- *.  unfold bs_node_height in |- *.  rewrite H4.  reflexivity.
  unfold node_height in |- *.  unfold bs_node_height in |- *.  rewrite H30.  reflexivity.
  intros.  rewrite (ad_S_compare xl x).
  replace (ad_S xl) with (node_height cfgr nodel).
  replace (ad_S x) with (node_height cfg node). (*  Unfold node_height in H24.*)
  rewrite (Neqb_complete (node_height cfgr nodel) (node_height cfgl nodel)).
  apply BDDlt_compare.  apply le_lt_trans with (m := nat_of_N (node_height cfg l)).
  apply leb_complete.  assumption.
  apply BDDcompare_lt.  unfold node_height in |- *.  apply bs_node_height_left with (x := x) (r := r).
  exact (proj1 H1).  assumption.
  apply used_nodes_preserved'_node_height_eq with (ul := nodel :: ul).  assumption.
  assumption.  assumption.  assumption.
  apply used_node'_cons_node_ul.
  unfold node_height in |- *.  unfold bs_node_height in |- *.  rewrite H4.  reflexivity.
  unfold node_height in |- *.  unfold bs_node_height in |- *.  rewrite H30.  reflexivity.
  apply used_node'_cons_node_ul.  apply used_node'_cons_node'_ul.
  apply used_node'_cons_node_ul.  apply node_OK_list_OK.  assumption.
  assumption.  apply used_nodes_preserved_list_OK with (cfg := cfgl).  assumption.
  assumption. 
  replace cfgr with (fst (BDDuniv_1 cfgl (nodel :: ul) r u n)).
  replace noder with (snd (BDDuniv_1 cfgl (nodel :: ul) r u n)).  apply H.
  apply lt_trans_1 with (y := nat_of_N (node_height cfg node)).
  rewrite (Neqb_complete (node_height cfgl r) (node_height cfg r)).  apply BDDcompare_lt.
  unfold node_height in |- *.  apply bs_node_height_right with (x := x) (l := l).  exact (proj1 H1).
  assumption.  apply used_nodes_preserved'_node_height_eq with (ul := ul).  assumption.
  assumption.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  rewrite H8.  reflexivity.
  rewrite H8.  reflexivity.  apply used_node'_cons_node'_ul.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.
  assumption.  apply high_used' with (node := node) (x := x) (l := l).  assumption.
  assumption.  assumption.  
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.
  assumption.  assumption.  apply node_OK_list_OK.  assumption.  assumption.
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.  assumption.
  apply used_node'_OK with (ul := ul).  assumption.  assumption.  assumption.
  apply used_node'_OK with (ul := ul).  assumption.  assumption.  assumption.
  replace cfgl with (fst (BDDuniv_1 cfg ul l u n)).
  replace nodel with (snd (BDDuniv_1 cfg ul l u n)).  apply H.
  apply lt_trans_1 with (y := nat_of_N (node_height cfg node)).
  apply BDDcompare_lt.  unfold node_height in |- *.
  apply bs_node_height_left with (x := x) (r := r).  exact (proj1 H1).
  assumption.  assumption.  assumption.  assumption.  assumption.
  rewrite H7.  reflexivity.  rewrite H7.  reflexivity.  
  apply high_used' with (node := node) (x := x) (l := l).  assumption.  assumption.
  assumption.  apply low_used' with (node := node) (x := x) (r := r).  assumption.
  assumption.  assumption.  intro y0.  rewrite y0.  simpl in |- *.  split.  assumption.
  split.  apply used_node'_OK with (ul := ul).  assumption.  assumption.  
  assumption.  split.  apply used_nodes_preserved_refl.  split.
  apply Nleb_refl.  cut (config_node_OK cfg node).  intro.
  unfold config_node_OK in H4.  elim H4.  intro.  rewrite H5.
  apply bool_fun_eq_trans with bool_fun_zero.  apply bool_fun_of_BDD_zero.
  assumption.  
  apply bool_fun_eq_trans with (bf2 := bool_fun_forall u bool_fun_zero).
  apply bool_fun_eq_sym.  apply bool_fun_forall_zero.  
  apply bool_fun_forall_preserves_eq.  apply bool_fun_eq_sym.
  apply bool_fun_of_BDD_zero.  assumption.  intro.  elim H5.  intro.
  rewrite H6.  apply bool_fun_eq_trans with bool_fun_one.
  apply bool_fun_of_BDD_one.  assumption.  
  apply bool_fun_eq_trans with (bf2 := bool_fun_forall u bool_fun_one).
  apply bool_fun_eq_sym.  apply bool_fun_forall_one.  
  apply bool_fun_forall_preserves_eq.  apply bool_fun_eq_sym.
  apply bool_fun_of_BDD_one.  assumption.  unfold in_dom in |- *.  rewrite y0.
  intro; discriminate.  apply used_node'_OK with (ul := ul).  assumption.  
  assumption.  assumption.  
Qed.

End BDDuniv_sec.
