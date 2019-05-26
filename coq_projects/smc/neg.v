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

Section BDD_neg.

Variable gc : BDDconfig -> list ad -> BDDconfig.
Hypothesis gc_is_OK : gc_OK gc.

Fixpoint BDDneg_1 (cfg : BDDconfig) (ul : list ad) 
 (node : ad) (bound : nat) {struct bound} : BDDconfig * ad :=
  match bound with
  | O => (* Error *)  (initBDDconfig, BDDzero)
  | S bound' =>
      match MapGet _ (negm_of_cfg cfg) node with
      | Some node' => (cfg, node')
      | None =>
          match MapGet _ (fst cfg) node with
          | None =>
              if Neqb node BDDzero
              then (BDDneg_memo_put cfg BDDzero BDDone, BDDone)
              else (BDDneg_memo_put cfg BDDone BDDzero, BDDzero)
          | Some (x, (l, r)) =>
              match BDDneg_1 cfg ul l bound' with
              | (cfgl, nodel) =>
                  match BDDneg_1 cfgl (nodel :: ul) r bound' with
                  | (cfgr, noder) =>
                      match
                        BDDmake gc cfgr x nodel noder (noder :: nodel :: ul)
                      with
                      | (cfg', node') =>
                          (BDDneg_memo_put cfg' node node', node')
                      end
                  end
              end
          end
      end
  end.
  
Lemma BDDneg_1_lemma :
 forall (bound : nat) (cfg : BDDconfig) (ul : list ad) (node : ad),
 nat_of_N (node_height cfg node) < bound ->
 BDDconfig_OK cfg ->
 used_list_OK cfg ul ->
 used_node' cfg ul node ->
 BDDconfig_OK (fst (BDDneg_1 cfg ul node bound)) /\
 config_node_OK (fst (BDDneg_1 cfg ul node bound))
   (snd (BDDneg_1 cfg ul node bound)) /\
 used_nodes_preserved cfg (fst (BDDneg_1 cfg ul node bound)) ul /\
 Neqb
   (node_height (fst (BDDneg_1 cfg ul node bound))
      (snd (BDDneg_1 cfg ul node bound))) (node_height cfg node) = true /\
 bool_fun_eq
   (bool_fun_of_BDD (fst (BDDneg_1 cfg ul node bound))
      (snd (BDDneg_1 cfg ul node bound)))
   (bool_fun_neg (bool_fun_of_BDD cfg node)).
Proof.
  simple induction bound.  intros.  absurd (nat_of_N (node_height cfg node) < 0).
  apply lt_n_O.  assumption.  simpl in |- *.  intros.
  elim (option_sum _ (MapGet _ (negm_of_cfg cfg) node)).  intro y.
  elim y; clear y; intros node' H4.  rewrite H4.  simpl in |- *.
  elim (negm_of_cfg_OK _ H1 node node' H4).  intros.  split.  assumption.
  split.  inversion H6.  inversion H8.  assumption.  split.
  apply used_nodes_preserved_refl.  split.  exact (proj1 (proj2 H6)).
  exact (proj2 (proj2 H6)).  intro y.  rewrite y.
  elim (option_sum _ (MapGet (BDDvar * (ad * ad)) (fst cfg) node)).  intro y0.
  elim y0; clear y0.
  intro x; elim x; clear x; intros x x0; elim x0; clear x0; intros l r H4.
  rewrite H4.  elim (prod_sum _ _ (BDDneg_1 cfg ul l n)).  intros cfgl H5.
  elim H5; clear H5.  intros nodel H5.  rewrite H5.
  elim (prod_sum _ _ (BDDneg_1 cfgl (nodel :: ul) r n)).  intros cfgr H6.
  elim H6; clear H6; intros noder H6.  rewrite H6.
  elim (prod_sum _ _ (BDDmake gc cfgr x nodel noder (noder :: nodel :: ul))).
  intros cfg' H7; elim H7; clear H7; intros node' H7.  rewrite H7.  simpl in |- *.
  cut (nat_of_N (node_height cfg l) < n).  cut (nat_of_N (node_height cfg r) < n).
  intros.  cut (used_node' cfg ul l).  cut (used_node' cfg ul r).  intros.
  cut
   (BDDconfig_OK cfgl /\
    config_node_OK cfgl nodel /\
    used_nodes_preserved cfg cfgl ul /\
    Neqb (node_height cfgl nodel) (node_height cfg l) = true /\
    bool_fun_eq (bool_fun_of_BDD cfgl nodel)
      (bool_fun_neg (bool_fun_of_BDD cfg l))).
  intro.  elim H12; clear H12; intros.  elim H13; clear H13; intros.
  elim H14; clear H14; intros.  elim H15; clear H15; intros.
  cut (config_node_OK cfg l).  cut (config_node_OK cfg r).  intros.
  cut (used_list_OK cfgl ul).  intro.  cut (used_list_OK cfgl (nodel :: ul)).
  intro.  cut (used_node' cfgl ul r).  intro.
  cut (used_node' cfgl (r :: ul) r).  intro.
  cut
   (BDDconfig_OK cfgr /\
    config_node_OK cfgr noder /\
    used_nodes_preserved cfgl cfgr (nodel :: ul) /\
    Neqb (node_height cfgr noder) (node_height cfgl r) = true /\
    bool_fun_eq (bool_fun_of_BDD cfgr noder)
      (bool_fun_neg (bool_fun_of_BDD cfgl r))).
  intros.  elim H23; clear H23; intros.  elim H24; clear H24; intros.
  elim H25; clear H25; intros.  elim H26; clear H26; intros.
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
  cut (Neqb (node_height cfg' node') (ad_S x) = true).  intros.
  cut (config_node_OK cfg' node).  intro.
  cut (nodes_preserved cfg' (BDDneg_memo_put cfg' node node')).  intro.
  cut (BDDconfig_OK (BDDneg_memo_put cfg' node node')).  intro.  split.
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
   (Neqb_complete (node_height (BDDneg_memo_put cfg' node node') node')
      (node_height cfg' node')).
  split.  rewrite (Neqb_complete _ _ H34).  unfold node_height in |- *.  unfold bs_node_height in |- *.
  rewrite H4.  apply Neqb_correct.  
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg' node').
  apply nodes_preserved_bool_fun.  assumption.  assumption.  assumption.  
  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_if x (bool_fun_of_BDD cfgr noder)
                (bool_fun_of_BDD cfgr nodel)).
  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_if x (bool_fun_neg (bool_fun_of_BDD cfg r))
                (bool_fun_neg (bool_fun_of_BDD cfg l))).
  apply bool_fun_if_preserves_eq.  apply bool_fun_eq_trans with (bf2 := bool_fun_neg (bool_fun_of_BDD cfgl r)).
  assumption.  apply bool_fun_neg_preserves_eq.
  apply used_nodes_preserved'_bool_fun with (ul := ul).
  assumption.  assumption.  assumption.  assumption.  assumption.  
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfgl nodel).
  apply used_nodes_preserved'_bool_fun with (ul := nodel :: ul).  assumption.
  assumption.  assumption.  assumption.  apply used_node'_cons_node_ul.
  assumption.  apply bool_fun_eq_sym.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_neg
                (bool_fun_if x (bool_fun_of_BDD cfg r)
                   (bool_fun_of_BDD cfg l))).
  apply bool_fun_neg_preserves_eq.  apply bool_fun_of_BDD_int.  assumption.
  assumption.  apply bool_fun_neg_orthogonal.  apply nodes_preserved_node_height_eq.
  assumption.  assumption.  assumption.  assumption.  apply BDDnegm_put_OK.
  assumption.  assumption.  assumption.  rewrite (Neqb_complete _ _ H34).
  rewrite (Neqb_complete (node_height cfg' node) (node_height cfg node)).  unfold node_height in |- *.
  unfold bs_node_height in |- *.  rewrite H4.  apply Neqb_correct.
  apply used_nodes_preserved'_node_height_eq with (ul := ul).  assumption.  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfgl).  assumption.  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfgr).  assumption.  
  apply used_nodes_preserved_cons with (node := nodel).  assumption.  
  apply used_nodes_preserved_cons with (node := nodel).
  apply used_nodes_preserved_cons with (node := noder).  assumption.  assumption.
  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_if x (bool_fun_of_BDD cfgr noder)
                (bool_fun_of_BDD cfgr nodel)).
  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_if x (bool_fun_neg (bool_fun_of_BDD cfg r))
                (bool_fun_neg (bool_fun_of_BDD cfg l))).
  apply bool_fun_if_preserves_eq.
  apply bool_fun_eq_trans with (bf2 := bool_fun_neg (bool_fun_of_BDD cfgl r)).
  assumption.  apply bool_fun_neg_preserves_eq.
  apply used_nodes_preserved'_bool_fun with (ul := ul).
  assumption.  assumption.  assumption.  assumption.  assumption.  
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfgl nodel).
  apply used_nodes_preserved'_bool_fun with (ul := nodel :: ul).  assumption.
  assumption.  assumption.  assumption.  apply used_node'_cons_node_ul.
  assumption.  apply
   bool_fun_eq_trans with (bf2 := bool_fun_neg (bool_fun_of_BDD cfg node)).
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_neg
                (bool_fun_if x (bool_fun_of_BDD cfg r)
                   (bool_fun_of_BDD cfg l))).
  apply bool_fun_eq_sym.  apply bool_fun_neg_orthogonal.
  apply bool_fun_neg_preserves_eq.  apply bool_fun_eq_sym.
  apply bool_fun_of_BDD_int.  assumption.  assumption.
  apply bool_fun_neg_preserves_eq.  apply bool_fun_eq_sym.
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfgl).  assumption.  assumption.  
  apply used_nodes_preserved_trans with (cfg2 := cfgr).  assumption.  
  apply used_nodes_preserved_cons with (node := nodel).  assumption.  
  apply used_nodes_preserved_cons with (node := nodel).
  apply used_nodes_preserved_cons with (node := noder).  assumption.  assumption.
  assumption.  apply BDDnegm_put_nodes_preserved.  
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
  apply BDDmake_node_height_eq.  assumption.  intros.  apply not_true_is_false.
  unfold not in |- *; intro.  apply eq_true_false_abs with (b := Neqb l r).
  apply BDDunique with (cfg := cfg).  assumption.  assumption.  assumption.  
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfgl r).
  apply bool_fun_eq_neg_eq.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfgl nodel).
  apply bool_fun_eq_sym.  assumption.  
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfgr nodel).
  apply bool_fun_eq_sym.
  apply used_nodes_preserved'_bool_fun with (ul := nodel :: ul).  assumption.
  assumption.  assumption.  assumption.  apply used_node'_cons_node_ul.
  rewrite (Neqb_complete _ _ H34).  assumption.
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  assumption.
  assumption.  assumption.  assumption.
  apply low_high_neq with (cfg := cfg) (node := node) (x := x).  assumption.  assumption.
  rewrite H7.  reflexivity.  rewrite H7.  reflexivity.  
  replace cfg' with
   (fst (BDDmake gc cfgr x nodel noder (noder :: nodel :: ul))).
  replace node' with
   (snd (BDDmake gc cfgr x nodel noder (noder :: nodel :: ul))).
  apply BDDmake_bool_fun.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  rewrite H7.  reflexivity.  rewrite H7.
  reflexivity.  replace cfg' with
   (fst (BDDmake gc cfgr x nodel noder (noder :: nodel :: ul))).
  replace node' with
   (snd (BDDmake gc cfgr x nodel noder (noder :: nodel :: ul))).
  apply BDDmake_node_OK.  assumption.  assumption.  assumption.  assumption.  
  assumption.  assumption.  assumption.  rewrite H7.  reflexivity.  rewrite H7.
  reflexivity.  replace cfg' with
   (fst (BDDmake gc cfgr x nodel noder (noder :: nodel :: ul))).
  replace node' with
   (snd (BDDmake gc cfgr x nodel noder (noder :: nodel :: ul))).
  apply BDDmake_preserves_used_nodes.  assumption.  assumption.  assumption.  
  rewrite H7.  reflexivity.  rewrite H7.  reflexivity.
  replace cfg' with
   (fst (BDDmake gc cfgr x nodel noder (noder :: nodel :: ul))).
  apply BDDmake_keeps_config_OK.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  assumption.  rewrite H7.  reflexivity.
  intros.  rewrite (ad_S_compare xr x).
  replace (ad_S xr) with (bs_node_height (fst cfgr) noder).
  replace (ad_S x) with (bs_node_height (fst cfg) node).  unfold node_height in H26.
  rewrite (Neqb_complete _ _ H26).  cut (Neqb (node_height cfgl r) (node_height cfg r) = true).
  intro.  unfold node_height in H33.  rewrite (Neqb_complete _ _ H33).
  apply bs_node_height_right with (x := x) (l := l).  exact (proj1 H1).  assumption.
  apply used_nodes_preserved'_node_height_eq with (ul := ul).  assumption.  assumption.
  assumption.  assumption.  assumption.  unfold bs_node_height in |- *.  rewrite H4.
  reflexivity.  unfold bs_node_height in |- *.  rewrite H32.  reflexivity.  intros.
  rewrite (ad_S_compare xl x).  replace (ad_S xl) with (bs_node_height (fst cfgr) nodel).
  replace (ad_S x) with (bs_node_height (fst cfg) node).
  cut (Neqb (node_height cfgr nodel) (node_height cfgl nodel) = true).  intro.
  unfold node_height in H33.  rewrite (Neqb_complete _ _ H33).  unfold node_height in H15.
  rewrite (Neqb_complete _ _ H15).  apply bs_node_height_left with (x := x) (r := r).
  exact (proj1 H1).  assumption.  
  apply used_nodes_preserved'_node_height_eq with (ul := nodel :: ul).  assumption.
  assumption.  assumption.  assumption.  apply used_node'_cons_node_ul.  
  unfold bs_node_height in |- *.  rewrite H4.  reflexivity.  unfold bs_node_height in |- *.  rewrite H32.
  reflexivity.  apply used_node'_cons_node_ul.  apply used_node'_cons_node'_ul.
  apply used_node'_cons_node_ul.  apply node_OK_list_OK.  assumption.  
  assumption.  apply used_nodes_preserved_list_OK with (cfg := cfgl).  assumption.  
  assumption.  replace cfgr with (fst (BDDneg_1 cfgl (nodel :: ul) r n)).
  replace noder with (snd (BDDneg_1 cfgl (nodel :: ul) r n)).  apply H.
  apply lt_trans_1 with (y := nat_of_N (node_height cfg node)).
  cut (Neqb (node_height cfgl r) (node_height cfg r) = true).  intro.
  rewrite (Neqb_complete _ _ H23).  apply BDDcompare_lt.  unfold node_height in |- *.
  apply bs_node_height_right with (x := x) (l := l).  exact (proj1 H1).  assumption.
  apply used_nodes_preserved'_node_height_eq with (ul := ul).  assumption.  assumption.
  assumption.  assumption.  assumption.  assumption.  assumption.  assumption.
  apply used_node'_cons_node'_ul.  assumption.  rewrite H6.  reflexivity.  
  rewrite H6.  reflexivity.  apply used_node'_cons_node_ul.  
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.  assumption.
  assumption.  apply node_OK_list_OK.  assumption.  assumption.  
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.  assumption.  
  apply used_node'_OK with (ul := ul).  assumption.  assumption.  assumption.  
  apply used_node'_OK with (ul := ul).  assumption.  assumption.  assumption.  
  replace cfgl with (fst (BDDneg_1 cfg ul l n)).
  replace nodel with (snd (BDDneg_1 cfg ul l n)).  apply H.
  apply lt_trans_1 with (y := nat_of_N (node_height cfg node)).  apply BDDcompare_lt.
  unfold node_height in |- *.  apply bs_node_height_left with (x := x) (r := r).  exact (proj1 H1).
  assumption.  assumption.  assumption.  assumption.  assumption.  rewrite H5.
  reflexivity.  rewrite H5.  reflexivity.  
  apply high_used' with (x := x) (l := l) (node := node).  assumption.  assumption.  
  assumption.  apply low_used' with (x := x) (r := r) (node := node).  assumption.  
  assumption.  assumption.  apply lt_trans_1 with (y := nat_of_N (node_height cfg node)).
  apply BDDcompare_lt.  unfold node_height in |- *.  apply bs_node_height_right with (x := x) (l := l).
  exact (proj1 H1).  assumption.  assumption.
  apply lt_trans_1 with (y := nat_of_N (node_height cfg node)).  apply BDDcompare_lt.
  unfold node_height in |- *.  apply bs_node_height_left with (x := x) (r := r).  exact (proj1 H1).
  assumption.  assumption.  intro y0.  rewrite y0.
  elim (sumbool_of_bool (Neqb node BDDzero)).  intro y1.  rewrite y1.
  rewrite (Neqb_complete _ _ y1).  simpl in |- *.
  cut (BDDconfig_OK (BDDneg_memo_put cfg BDDzero BDDone)).  intro.  split.
  assumption.  cut (nodes_preserved cfg (BDDneg_memo_put cfg BDDzero BDDone)).
  intro.  split.  apply nodes_preserved_config_node_OK with (cfg1 := cfg).
  assumption.  apply one_OK.  split.  apply nodes_preserved_used_nodes_preserved.
  assumption.  split.  rewrite <-
   (Neqb_complete (node_height cfg BDDone) (node_height cfg BDDzero))
   .
  apply nodes_preserved_node_height_eq.  assumption.  assumption.  assumption.
  apply one_OK.  rewrite (Neqb_complete _ _ (node_height_zero _ H1)).
  rewrite (Neqb_complete _ _ (node_height_one _ H1)).  reflexivity.
  apply bool_fun_eq_trans with (bf2 := bool_fun_one).  apply bool_fun_of_BDD_one.
  assumption.  apply bool_fun_eq_trans with (bf2 := bool_fun_neg bool_fun_zero).
  apply bool_fun_eq_sym.  exact bool_fun_neg_zero.
  apply bool_fun_neg_preserves_eq.  apply bool_fun_eq_sym.
  apply bool_fun_of_BDD_zero.  assumption.  apply BDDnegm_put_nodes_preserved.
  apply BDDnegm_put_OK.  assumption.  apply zero_OK.  apply one_OK.  
  rewrite (Neqb_complete _ _ (node_height_zero _ H1)).
  rewrite (Neqb_complete _ _ (node_height_one _ H1)).  reflexivity.  
  apply bool_fun_eq_trans with (bf2 := bool_fun_neg bool_fun_zero).  
  apply bool_fun_of_BDD_one.  assumption.  apply bool_fun_neg_preserves_eq.
  apply bool_fun_eq_sym.  apply bool_fun_of_BDD_zero.  assumption.  intro y1.
  rewrite y1.  simpl in |- *.  cut (BDDconfig_OK (BDDneg_memo_put cfg BDDone BDDzero)).
  intro.  split.  assumption.
  cut (nodes_preserved cfg (BDDneg_memo_put cfg BDDone BDDzero)).  intro.
  split.  apply nodes_preserved_config_node_OK with (cfg1 := cfg).  assumption.
  apply zero_OK.  split.  apply nodes_preserved_used_nodes_preserved.
  assumption.  elim (used_node'_OK cfg ul node H1 H2 H3).  intro.
  rewrite H6 in y1.  simpl in y1.  discriminate.  intro.  elim H6.  intro.
  rewrite H7.  split.  rewrite <-
   (Neqb_complete (node_height cfg BDDzero) (node_height cfg BDDone))
   .
  apply nodes_preserved_node_height_eq.  assumption.  assumption.  assumption.
  apply zero_OK.  rewrite (Neqb_complete _ _ (node_height_zero _ H1)).
  rewrite (Neqb_complete _ _ (node_height_one _ H1)).  reflexivity.  
  apply bool_fun_eq_trans with (bf2 := bool_fun_zero).  apply bool_fun_of_BDD_zero.
  assumption.  apply bool_fun_eq_trans with (bf2 := bool_fun_neg bool_fun_one).
  apply bool_fun_eq_sym.  exact bool_fun_neg_one.
  apply bool_fun_neg_preserves_eq.  apply bool_fun_eq_sym.
  apply bool_fun_of_BDD_one.  assumption.  intro.  unfold in_dom in H7.
  rewrite y0 in H7.  discriminate.  apply BDDnegm_put_nodes_preserved.
  apply BDDnegm_put_OK.  assumption.  apply one_OK.  apply zero_OK.  
  rewrite (Neqb_complete _ _ (node_height_zero _ H1)).
  rewrite (Neqb_complete _ _ (node_height_one _ H1)).  reflexivity.  
  apply bool_fun_eq_trans with (bf2 := bool_fun_neg bool_fun_one).
  apply bool_fun_of_BDD_zero.  assumption.  apply bool_fun_neg_preserves_eq.
  apply bool_fun_eq_sym.  apply bool_fun_of_BDD_one.  assumption.  
Qed.

End BDD_neg.