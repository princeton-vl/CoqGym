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

Section BDD_or.

Variable gc : BDDconfig -> list ad -> BDDconfig.
Hypothesis gc_is_OK : gc_OK gc.

Fixpoint BDDor_1 (cfg : BDDconfig) (ul : list ad) (node1 node2 : ad)
 (bound : nat) {struct bound} : BDDconfig * ad :=
  match bound with
  | O => (* Error *)  (initBDDconfig, BDDzero)
  | S bound' =>
      match MapGet2 _ (orm_of_cfg cfg) node1 node2 with
      | Some node' => (cfg, node')
      | None =>
          match MapGet _ (fst cfg) node1 with
          | None =>
              if Neqb node1 BDDzero
              then (BDDor_memo_put cfg node1 node2 node2, node2)
              else (BDDor_memo_put cfg node1 node2 node1, node1)
          | Some (x1, (l1, r1)) =>
              match MapGet _ (fst cfg) node2 with
              | None =>
                  if Neqb node2 BDDzero
                  then (BDDor_memo_put cfg node1 node2 node1, node1)
                  else (BDDor_memo_put cfg node1 node2 node2, node2)
              | Some (x2, (l2, r2)) =>
                  match BDDcompare x1 x2 with
                  | Datatypes.Eq =>
                      match BDDor_1 cfg ul l1 l2 bound' with
                      | (cfgl, nodel) =>
                          match BDDor_1 cfgl (nodel :: ul) r1 r2 bound' with
                          | (cfgr, noder) =>
                              match
                                BDDmake gc cfgr x1 nodel noder
                                  (noder :: nodel :: ul)
                              with
                              | (cfg', node') =>
                                  (BDDor_memo_put cfg' node1 node2 node',
                                  node')
                              end
                          end
                      end
                  | Datatypes.Gt =>
                      match BDDor_1 cfg ul l1 node2 bound' with
                      | (cfgl, nodel) =>
                          match
                            BDDor_1 cfgl (nodel :: ul) r1 node2 bound'
                          with
                          | (cfgr, noder) =>
                              match
                                BDDmake gc cfgr x1 nodel noder
                                  (noder :: nodel :: ul)
                              with
                              | (cfg', node') =>
                                  (BDDor_memo_put cfg' node1 node2 node',
                                  node')
                              end
                          end
                      end
                  | Datatypes.Lt =>
                      match BDDor_1 cfg ul node1 l2 bound' with
                      | (cfgl, nodel) =>
                          match
                            BDDor_1 cfgl (nodel :: ul) node1 r2 bound'
                          with
                          | (cfgr, noder) =>
                              match
                                BDDmake gc cfgr x2 nodel noder
                                  (noder :: nodel :: ul)
                              with
                              | (cfg', node') =>
                                  (BDDor_memo_put cfg' node1 node2 node',
                                  node')
                              end
                          end
                      end
                  end
              end
          end
      end
  end.

Lemma BDDor_1_lemma :
 forall (bound : nat) (cfg : BDDconfig) (ul : list ad) (node1 node2 : ad),
 max (nat_of_N (node_height cfg node1)) (nat_of_N (node_height cfg node2)) <
 bound ->
 BDDconfig_OK cfg ->
 used_list_OK cfg ul ->
 used_node' cfg ul node1 ->
 used_node' cfg ul node2 ->
 BDDconfig_OK (fst (BDDor_1 cfg ul node1 node2 bound)) /\
 config_node_OK (fst (BDDor_1 cfg ul node1 node2 bound))
   (snd (BDDor_1 cfg ul node1 node2 bound)) /\
 used_nodes_preserved cfg (fst (BDDor_1 cfg ul node1 node2 bound)) ul /\
 Nleb
   (node_height (fst (BDDor_1 cfg ul node1 node2 bound))
      (snd (BDDor_1 cfg ul node1 node2 bound)))
   (BDDvar_max (node_height cfg node1) (node_height cfg node2)) = true /\
 bool_fun_eq
   (bool_fun_of_BDD (fst (BDDor_1 cfg ul node1 node2 bound))
      (snd (BDDor_1 cfg ul node1 node2 bound)))
   (bool_fun_or (bool_fun_of_BDD cfg node1) (bool_fun_of_BDD cfg node2)).
Proof.
  simple induction bound.  intros.
  absurd
   (max (nat_of_N (node_height cfg node1))
      (nat_of_N (node_height cfg node2)) < 0).
  apply lt_n_O.  assumption.  simpl in |- *.  intros.
  elim (option_sum _ (MapGet2 ad (orm_of_cfg cfg) node1 node2)).  intro y.
  elim y; clear y; intros node' H5.  rewrite H5.  simpl in |- *.
  elim (orm_of_cfg_OK _ H1 _ _ _ H5).  intros.  elim H7; intros.
  elim H9; intros.  elim H11; intros.  split.  assumption.  split.
  assumption.  split.  apply used_nodes_preserved_refl.  split.  assumption.
  assumption.  intro y.  rewrite y.
  elim (option_sum _ (MapGet (BDDvar * (ad * ad)) (fst cfg) node1)).  intro y0.
  elim y0; clear y0.
  intro x; elim x; clear x; intros x1 x0; elim x0; clear x0; intros l1 r1 H5.
  rewrite H5.  elim (option_sum _ (MapGet (BDDvar * (ad * ad)) (fst cfg) node2)).
  intro y0.  elim y0; clear y0.
  intro x; elim x; clear x; intros x2 x0; elim x0; clear x0; intros l2 r2 H6.
  rewrite H6.  elim (relation_sum (BDDcompare x1 x2)).  intro y0.
  elim y0; clear y0; intro y0.  rewrite y0.  elim (prod_sum _ _ (BDDor_1 cfg ul l1 l2 n)).
  intros cfgl H7.  elim H7; clear H7.  intros nodel H7.  rewrite H7.
  elim (prod_sum _ _ (BDDor_1 cfgl (nodel :: ul) r1 r2 n)).  intros cfgr H8.
  elim H8; clear H8.  intros noder H8.  rewrite H8.
  elim (prod_sum _ _ (BDDmake gc cfgr x1 nodel noder (noder :: nodel :: ul))).
  intros cfg' H9.  elim H9; clear H9.  intros node' H9.  rewrite H9.  simpl in |- *.
  cut (used_node' cfg ul l1).  cut (used_node' cfg ul r1).
  cut (used_node' cfg ul l2).  cut (used_node' cfg ul r2).  intros.  
  cut
   (BDDconfig_OK cfgl /\
    config_node_OK cfgl nodel /\
    used_nodes_preserved cfg cfgl ul /\
    Nleb (node_height cfgl nodel)
      (BDDvar_max (node_height cfg l1) (node_height cfg l2)) = true /\
    bool_fun_eq (bool_fun_of_BDD cfgl nodel)
      (bool_fun_or (bool_fun_of_BDD cfg l1) (bool_fun_of_BDD cfg l2))).
  intro.  elim H14; clear H14; intros.  elim H15; clear H15; intros.
  elim H16; clear H16; intros.  elim H17; clear H17; intros.
  cut (used_list_OK cfgl ul).  intro.  cut (used_list_OK cfgl (nodel :: ul)).
  intro.  cut (used_node' cfgl ul r1).  cut (used_node' cfgl ul r2).  intros.
  cut (used_node' cfgl (nodel :: ul) r1).  cut (used_node' cfgl (nodel :: ul) r2).
  intros.  cut
   (BDDconfig_OK cfgr /\
    config_node_OK cfgr noder /\
    used_nodes_preserved cfgl cfgr (nodel :: ul) /\
    Nleb (node_height cfgr noder)
      (BDDvar_max (node_height cfgl r1) (node_height cfgl r2)) = true /\
    bool_fun_eq (bool_fun_of_BDD cfgr noder)
      (bool_fun_or (bool_fun_of_BDD cfgl r1) (bool_fun_of_BDD cfgl r2))).


  intro.  elim H25; clear H25; intros.  elim H26; clear H26; intros.
  elim H27; clear H27; intros.  elim H28; clear H28; intros.
  cut (used_list_OK cfgr (nodel :: ul)).  intro.
  cut (used_list_OK cfgr (noder :: nodel :: ul)).  intro.
  cut (used_node' cfgr (noder :: nodel :: ul) nodel).
  cut (used_node' cfgr (noder :: nodel :: ul) noder).  intros.
  cut
   (forall (xl : BDDvar) (ll rl : ad),
    MapGet _ (fst cfgr) nodel = Some (xl, (ll, rl)) ->
    BDDcompare xl x1 = Datatypes.Lt).
  cut
   (forall (xr : BDDvar) (lr rr : ad),
    MapGet _ (fst cfgr) noder = Some (xr, (lr, rr)) ->
    BDDcompare xr x1 = Datatypes.Lt).
  intros.  cut (BDDconfig_OK cfg').
  cut (used_nodes_preserved cfgr cfg' (noder :: nodel :: ul)).
  cut (config_node_OK cfg' node').
  cut
   (bool_fun_eq (bool_fun_of_BDD cfg' node')
      (bool_fun_if x1 (bool_fun_of_BDD cfgr noder)
         (bool_fun_of_BDD cfgr nodel))).
  cut (Nleb (node_height cfg' node') (ad_S x1) = true).  intros.
  cut (config_node_OK cfg' node1).  cut (config_node_OK cfg' node2).  intros.
  cut (nodes_preserved cfg' (BDDor_memo_put cfg' node1 node2 node')).  intro.
  cut (BDDconfig_OK (BDDor_memo_put cfg' node1 node2 node')).  intro.  split.
  assumption.  split.  apply nodes_preserved_config_node_OK with (cfg1 := cfg').
  assumption.  assumption.  split.
  apply used_nodes_preserved_trans with (cfg2 := cfgr).  assumption.  
  apply used_nodes_preserved_trans with (cfg2 := cfgl).  assumption.  assumption.
  apply used_nodes_preserved_cons with (node := nodel).  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfg').  assumption.
  apply used_nodes_preserved_cons with (node := nodel).
  apply used_nodes_preserved_cons with (node := noder).  assumption.
  apply nodes_preserved_used_nodes_preserved.  assumption.  
  rewrite
   (Neqb_complete
      (node_height (BDDor_memo_put cfg' node1 node2 node') node')
      (node_height cfg' node')).
  split.  unfold node_height at 2 3 in |- *.  unfold bs_node_height in |- *.  rewrite H5.  rewrite H6.
  rewrite <- (BDD_EGAL_complete _ _ y0).  apply Nleb_trans with (b := ad_S x1).
  assumption.  apply BDDvar_le_max_1.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg' node').
  apply nodes_preserved_bool_fun.  assumption.  assumption.  assumption.  
  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_if x1 (bool_fun_of_BDD cfgr noder)
                (bool_fun_of_BDD cfgr nodel)).
  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_if x1
                (bool_fun_or (bool_fun_of_BDD cfg r1)
                   (bool_fun_of_BDD cfg r2))
                (bool_fun_or (bool_fun_of_BDD cfg l1)
                   (bool_fun_of_BDD cfg l2))).
  apply bool_fun_if_preserves_eq.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_or (bool_fun_of_BDD cfgl r1) (bool_fun_of_BDD cfgl r2)).
  assumption.  apply bool_fun_or_preserves_eq.
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  assumption.
  assumption.  assumption.  assumption.
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  assumption.
  assumption.  assumption.  assumption.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfgl nodel).
  apply used_nodes_preserved'_bool_fun with (ul := nodel :: ul).  assumption.
  assumption.  assumption.  assumption.  apply used_node'_cons_node_ul.
  assumption.  apply bool_fun_eq_sym.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_or
                (bool_fun_if x1 (bool_fun_of_BDD cfg r1)
                   (bool_fun_of_BDD cfg l1))
                (bool_fun_if x1 (bool_fun_of_BDD cfg r2)
                   (bool_fun_of_BDD cfg l2))).
  apply bool_fun_or_preserves_eq.  apply bool_fun_of_BDD_int.  assumption.
  assumption.  apply bool_fun_of_BDD_int.  assumption.
  rewrite (BDD_EGAL_complete _ _ y0).  assumption.
  apply bool_fun_or_orthogonal.  apply nodes_preserved_node_height_eq.  assumption.
  assumption.  assumption.  assumption.  apply BDDorm_put_OK.  assumption.
  assumption.  assumption.  assumption.  
  rewrite (Neqb_complete (node_height cfg' node1) (node_height cfg node1)).
  rewrite (Neqb_complete (node_height cfg' node2) (node_height cfg node2)).
  unfold node_height at 2 3 in |- *.  unfold bs_node_height in |- *.  rewrite H5.  rewrite H6.
  apply Nleb_trans with (b := ad_S x1).  assumption.
  rewrite (BDD_EGAL_complete _ _ y0).  apply BDDvar_le_max_1.  
  apply used_nodes_preserved'_node_height_eq with (ul := ul).  assumption.  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfgl).  assumption.  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfgr).  assumption.
  apply used_nodes_preserved_cons with (node := nodel).  assumption.
  apply used_nodes_preserved_cons with (node := nodel).
  apply used_nodes_preserved_cons with (node := noder).  assumption.  assumption.
  assumption.  apply used_nodes_preserved'_node_height_eq with (ul := ul).  assumption.
  assumption.  apply used_nodes_preserved_trans with (cfg2 := cfgl).  assumption.
  assumption.  apply used_nodes_preserved_trans with (cfg2 := cfgr).  assumption.
  apply used_nodes_preserved_cons with (node := nodel).  assumption.  
  apply used_nodes_preserved_cons with (node := nodel).
  apply used_nodes_preserved_cons with (node := noder).  assumption.  assumption.
  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_if x1 (bool_fun_of_BDD cfgr noder)
                (bool_fun_of_BDD cfgr nodel)).
  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_if x1
                (bool_fun_or (bool_fun_of_BDD cfg r1)
                   (bool_fun_of_BDD cfg r2))
                (bool_fun_or (bool_fun_of_BDD cfg l1)
                   (bool_fun_of_BDD cfg l2))).
  apply bool_fun_if_preserves_eq.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_or (bool_fun_of_BDD cfgl r1) (bool_fun_of_BDD cfgl r2)).
  assumption.  apply bool_fun_or_preserves_eq.
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  assumption.
  assumption.  assumption.  assumption.  
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  assumption.  
  assumption.  assumption.  assumption.  
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfgl nodel).
  apply used_nodes_preserved'_bool_fun with (ul := nodel :: ul).  assumption.
  assumption.  assumption.  assumption.  apply used_node'_cons_node_ul.  
  assumption.  apply bool_fun_eq_sym.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_or
                (bool_fun_if x1 (bool_fun_of_BDD cfg r1)
                   (bool_fun_of_BDD cfg l1))
                (bool_fun_if x1 (bool_fun_of_BDD cfg r2)
                   (bool_fun_of_BDD cfg l2))).
  apply bool_fun_or_preserves_eq.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg node1).
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfgl).  assumption.  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfgr).  assumption.  
  apply used_nodes_preserved_cons with (node := nodel).  assumption.
  apply used_nodes_preserved_cons with (node := nodel).
  apply used_nodes_preserved_cons with (node := noder).  assumption.  assumption.
  assumption.  apply bool_fun_of_BDD_int.  assumption.  assumption.  
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg node2).
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfgl).  assumption.  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfgr).  assumption.  
  apply used_nodes_preserved_cons with (node := nodel).  assumption.  
  apply used_nodes_preserved_cons with (node := nodel).
  apply used_nodes_preserved_cons with (node := noder).  assumption.  assumption.
  assumption.  apply bool_fun_of_BDD_int.  assumption.
  rewrite (BDD_EGAL_complete _ _ y0).  assumption.
  apply bool_fun_or_orthogonal.  apply BDDorm_put_nodes_preserved.  
  apply used_nodes_preserved_node_OK' with (ul := ul) (cfg := cfg).  assumption.
  assumption.  assumption.  apply used_nodes_preserved_trans with (cfg2 := cfgl).
  assumption.  assumption.  apply used_nodes_preserved_trans with (cfg2 := cfgr).
  assumption.  apply used_nodes_preserved_cons with (node := nodel).  assumption.
  apply used_nodes_preserved_cons with (node := nodel).
  apply used_nodes_preserved_cons with (node := noder).  assumption.
  apply used_nodes_preserved_node_OK' with (ul := ul) (cfg := cfg).  assumption.  
  assumption.  assumption.  apply used_nodes_preserved_trans with (cfg2 := cfgl).
  assumption.  assumption.  apply used_nodes_preserved_trans with (cfg2 := cfgr).
  assumption.  apply used_nodes_preserved_cons with (node := nodel).  assumption.
  apply used_nodes_preserved_cons with (node := nodel).
  apply used_nodes_preserved_cons with (node := noder).  assumption.
  replace cfg' with
   (fst (BDDmake gc cfgr x1 nodel noder (noder :: nodel :: ul))).
  replace node' with
   (snd (BDDmake gc cfgr x1 nodel noder (noder :: nodel :: ul))).
  apply BDDmake_node_height_le.  assumption.  assumption.  rewrite H9.  reflexivity.
  rewrite H9.  reflexivity.
  replace node' with
   (snd (BDDmake gc cfgr x1 nodel noder (noder :: nodel :: ul))).
  replace cfg' with
   (fst (BDDmake gc cfgr x1 nodel noder (noder :: nodel :: ul))).
  apply BDDmake_bool_fun.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  rewrite H9.  reflexivity.  rewrite H9.
  reflexivity.  replace cfg' with
   (fst (BDDmake gc cfgr x1 nodel noder (noder :: nodel :: ul))).
  replace node' with
   (snd (BDDmake gc cfgr x1 nodel noder (noder :: nodel :: ul))).
  apply BDDmake_node_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  rewrite H9.  reflexivity.  rewrite H9.
  reflexivity.  replace cfg' with
   (fst (BDDmake gc cfgr x1 nodel noder (noder :: nodel :: ul))).
  apply BDDmake_preserves_used_nodes.  assumption.  assumption.  assumption.
  rewrite H9.  reflexivity.
  replace cfg' with
   (fst (BDDmake gc cfgr x1 nodel noder (noder :: nodel :: ul))).
  apply BDDmake_keeps_config_OK.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  assumption.  rewrite H9.  reflexivity.
  intros.  rewrite (ad_S_compare xr x1).
  replace (ad_S xr) with (node_height cfgr noder).
  replace (ad_S x1) with (node_height cfg node1).  apply BDDlt_compare.
  apply
   le_lt_trans
    with
      (m := nat_of_N
              (BDDvar_max (node_height cfgl r1) (node_height cfgl r2))).
  apply leb_complete.  assumption.  
  rewrite (Neqb_complete (node_height cfgl r1) (node_height cfg r1)).
  rewrite (Neqb_complete (node_height cfgl r2) (node_height cfg r2)).
  rewrite (BDDvar_max_max (node_height cfg r1) (node_height cfg r2)).
  rewrite <- (max_x_x_eq_x (nat_of_N (node_height cfg node1))).  apply lt_max_1.
  apply BDDcompare_lt.  unfold node_height in |- *.  apply bs_node_height_right with (x := x1) (l := l1).
  exact (proj1 H1).  assumption.  apply BDDcompare_lt.
  replace (node_height cfg node1) with (node_height cfg node2).  unfold node_height in |- *.
  apply bs_node_height_right with (x := x2) (l := l2).  exact (proj1 H1).
  assumption.  unfold node_height in |- *.  unfold bs_node_height in |- *.  rewrite H5.  rewrite H6.
  rewrite (BDD_EGAL_complete _ _ y0).  reflexivity.  
  apply used_nodes_preserved'_node_height_eq with (ul := ul).  assumption.  assumption.
  assumption.  assumption.  assumption.
  apply used_nodes_preserved'_node_height_eq with (ul := ul).  assumption.  assumption.
  assumption.  assumption.  assumption.  unfold node_height in |- *.  unfold bs_node_height in |- *.
  rewrite H5.  reflexivity.  unfold node_height in |- *.  unfold bs_node_height in |- *.  rewrite H34.
  reflexivity.  intros.  rewrite (ad_S_compare xl x1).
  replace (ad_S xl) with (node_height cfgr nodel).
  replace (ad_S x1) with (node_height cfg node1).
  rewrite (Neqb_complete (node_height cfgr nodel) (node_height cfgl nodel)).
  apply BDDlt_compare.
  apply
   le_lt_trans
    with
      (m := nat_of_N (BDDvar_max (node_height cfg l1) (node_height cfg l2))).
  apply leb_complete.  assumption.
  rewrite (BDDvar_max_max (node_height cfg l1) (node_height cfg l2)).
  rewrite <- (max_x_x_eq_x (nat_of_N (node_height cfg node1))).  apply lt_max_1.
  apply BDDcompare_lt.  unfold node_height in |- *.  apply bs_node_height_left with (x := x1) (r := r1).
  exact (proj1 H1).  assumption.  apply BDDcompare_lt.
  replace (node_height cfg node1) with (node_height cfg node2).  unfold node_height in |- *.
  apply bs_node_height_left with (x := x2) (r := r2).  exact (proj1 H1).  assumption.
  unfold node_height in |- *.  unfold bs_node_height in |- *.  rewrite H5.  rewrite H6.
  rewrite (BDD_EGAL_complete _ _ y0).  reflexivity.  
  apply used_nodes_preserved'_node_height_eq with (ul := nodel :: ul).  assumption.
  assumption.  assumption.  assumption.  apply used_node'_cons_node_ul.
  unfold node_height in |- *.  unfold bs_node_height in |- *.  rewrite H5.  reflexivity.  unfold node_height in |- *.
  unfold bs_node_height in |- *.  rewrite H34.  reflexivity.  apply used_node'_cons_node_ul.
  apply used_node'_cons_node'_ul.  apply used_node'_cons_node_ul.
  apply node_OK_list_OK.  assumption.  assumption.
  apply used_nodes_preserved_list_OK with (cfg := cfgl).  assumption.  assumption.
  replace cfgr with (fst (BDDor_1 cfgl (nodel :: ul) r1 r2 n)).
  replace noder with (snd (BDDor_1 cfgl (nodel :: ul) r1 r2 n)).  apply H.
  apply
   lt_trans_1
    with
      (y := max (nat_of_N (node_height cfg node1))
              (nat_of_N (node_height cfg node2))).
  apply lt_max_1.  rewrite (Neqb_complete (node_height cfgl r1) (node_height cfg r1)).
  unfold node_height in |- *.  apply BDDcompare_lt.  apply bs_node_height_right with (x := x1) (l := l1).
  exact (proj1 H1).  assumption.
  apply used_nodes_preserved'_node_height_eq with (ul := ul).  assumption.  assumption.
  assumption.  assumption.  assumption.
  rewrite (Neqb_complete (node_height cfgl r2) (node_height cfg r2)).
  replace (node_height cfg node1) with (node_height cfg node2).  apply BDDcompare_lt.
  unfold node_height in |- *.  apply bs_node_height_right with (x := x2) (l := l2).  exact (proj1 H1).
  assumption.  unfold node_height in |- *.  unfold bs_node_height in |- *.  rewrite H5.  rewrite H6.
  rewrite (BDD_EGAL_complete _ _ y0).  reflexivity.
  apply used_nodes_preserved'_node_height_eq with (ul := ul).  assumption.  assumption.
  assumption.  assumption.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  rewrite H8.  reflexivity.  rewrite H8.  reflexivity.
  apply used_node'_cons_node'_ul.  assumption.  apply used_node'_cons_node'_ul.
  assumption.  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.
  assumption.  apply high_used' with (node := node2) (x := x2) (l := l2).  assumption.
  assumption.  assumption.  apply used_nodes_preserved_used_node' with (cfg := cfg).
  assumption.  assumption.  apply high_used' with (node := node1) (x := x1) (l := l1).
  assumption.  assumption.  assumption.  apply node_OK_list_OK.  assumption.
  assumption.  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.
  assumption.  replace cfgl with (fst (BDDor_1 cfg ul l1 l2 n)).
  replace nodel with (snd (BDDor_1 cfg ul l1 l2 n)).  apply H.
  apply
   lt_trans_1
    with
      (y := max (nat_of_N (node_height cfg node1))
              (nat_of_N (node_height cfg node2))).
  apply lt_max_1.  unfold node_height in |- *.  apply BDDcompare_lt.
  apply bs_node_height_left with (x := x1) (r := r1).  exact (proj1 H1).  assumption.
  replace (node_height cfg node1) with (node_height cfg node2).  apply BDDcompare_lt.
  unfold node_height in |- *.  apply bs_node_height_left with (x := x2) (r := r2).  exact (proj1 H1).
  assumption.  unfold node_height in |- *.  unfold bs_node_height in |- *.  rewrite H5.  rewrite H6.
  rewrite (BDD_EGAL_complete _ _ y0).  reflexivity.  assumption.  assumption.
  assumption.  assumption.  assumption.  rewrite H7.  reflexivity.  rewrite H7.
  reflexivity.  apply high_used' with (node := node2) (x := x2) (l := l2).  assumption.
  assumption.  assumption.  apply low_used' with (node := node2) (x := x2) (r := r2).
  assumption.  assumption.  assumption.
  apply high_used' with (node := node1) (x := x1) (l := l1).  assumption.  assumption.
  assumption.  apply low_used' with (node := node1) (x := x1) (r := r1).  assumption.
  assumption.  assumption.  rewrite y0.
  elim (prod_sum _ _ (BDDor_1 cfg ul node1 l2 n)).  intros cfgl H7.
  elim H7; clear H7.  intros nodel H7.  rewrite H7.
  elim (prod_sum _ _ (BDDor_1 cfgl (nodel :: ul) node1 r2 n)).
  intros cfgr H8.  elim H8; clear H8.  intros noder H8.  rewrite H8.
  elim (prod_sum _ _ (BDDmake gc cfgr x2 nodel noder (noder :: nodel :: ul))).
  intros cfg' H9.  elim H9; clear H9.  intros node' H9.  rewrite H9.  simpl in |- *.
  cut (used_node' cfg ul l2).  cut (used_node' cfg ul r2).  intros.  
  cut
   (BDDconfig_OK cfgl /\
    config_node_OK cfgl nodel /\
    used_nodes_preserved cfg cfgl ul /\
    Nleb (node_height cfgl nodel)
      (BDDvar_max (node_height cfg node1) (node_height cfg l2)) = true /\
    bool_fun_eq (bool_fun_of_BDD cfgl nodel)
      (bool_fun_or (bool_fun_of_BDD cfg node1) (bool_fun_of_BDD cfg l2))).
  intro.  elim H12; clear H12; intros.  elim H13; clear H13; intros.
  elim H14; clear H14; intros.  elim H15; clear H15; intros.
  cut (used_list_OK cfgl ul).  intro.
  cut (used_list_OK cfgl (nodel :: ul)).  intro.
  cut (used_node' cfgl ul node1).  cut (used_node' cfgl ul r2).  intros.
  cut (used_node' cfgl (nodel :: ul) node1).
  cut (used_node' cfgl (nodel :: ul) r2).  intros.
  cut
   (BDDconfig_OK cfgr /\
    config_node_OK cfgr noder /\
    used_nodes_preserved cfgl cfgr (nodel :: ul) /\
    Nleb (node_height cfgr noder)
      (BDDvar_max (node_height cfgl node1) (node_height cfgl r2)) = true /\
    bool_fun_eq (bool_fun_of_BDD cfgr noder)
      (bool_fun_or (bool_fun_of_BDD cfgl node1) (bool_fun_of_BDD cfgl r2))).


  intro.  elim H23; clear H23; intros.  elim H24; clear H24; intros.
  elim H25; clear H25; intros.  elim H26; clear H26; intros.
  cut (used_list_OK cfgr (nodel :: ul)).  intro.
  cut (used_list_OK cfgr (noder :: nodel :: ul)).  intro.
  cut (used_node' cfgr (noder :: nodel :: ul) nodel).
  cut (used_node' cfgr (noder :: nodel :: ul) noder).  intros.
  cut
   (forall (xl : BDDvar) (ll rl : ad),
    MapGet _ (fst cfgr) nodel = Some (xl, (ll, rl)) ->
    BDDcompare xl x2 = Datatypes.Lt).
  cut
   (forall (xr : BDDvar) (lr rr : ad),
    MapGet _ (fst cfgr) noder = Some (xr, (lr, rr)) ->
    BDDcompare xr x2 = Datatypes.Lt).
  intros.  cut (BDDconfig_OK cfg').
  cut (used_nodes_preserved cfgr cfg' (noder :: nodel :: ul)).
  cut (config_node_OK cfg' node').
  cut
   (bool_fun_eq (bool_fun_of_BDD cfg' node')
      (bool_fun_if x2 (bool_fun_of_BDD cfgr noder)
         (bool_fun_of_BDD cfgr nodel))).
  cut (Nleb (node_height cfg' node') (ad_S x2) = true).  intros.
  cut (config_node_OK cfg' node1).  cut (config_node_OK cfg' node2).  intros.
  cut (nodes_preserved cfg' (BDDor_memo_put cfg' node1 node2 node')).  intro.
  cut (BDDconfig_OK (BDDor_memo_put cfg' node1 node2 node')).  intro.  split.
  assumption.  split.  apply nodes_preserved_config_node_OK with (cfg1 := cfg').
  assumption.  assumption.  split.
  apply used_nodes_preserved_trans with (cfg2 := cfgr).  assumption.  
  apply used_nodes_preserved_trans with (cfg2 := cfgl).  assumption.  assumption.
  apply used_nodes_preserved_cons with (node := nodel).  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfg').  assumption.
  apply used_nodes_preserved_cons with (node := nodel).
  apply used_nodes_preserved_cons with (node := noder).  assumption.  
  apply nodes_preserved_used_nodes_preserved.  assumption.  
  rewrite
   (Neqb_complete
      (node_height (BDDor_memo_put cfg' node1 node2 node') node')
      (node_height cfg' node')).
  split.  unfold node_height at 2 3 in |- *.  unfold bs_node_height in |- *.  rewrite H5.  rewrite H6.
  rewrite (BDDvar_max_inf (ad_S x1) (ad_S x2)).  assumption.  
  rewrite <- (ad_S_compare x1 x2).  assumption.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg' node').
  apply nodes_preserved_bool_fun.  assumption.  assumption.  assumption.
  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_if x2 (bool_fun_of_BDD cfgr noder)
                (bool_fun_of_BDD cfgr nodel)).
  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_if x2
                (bool_fun_or (bool_fun_of_BDD cfg node1)
                   (bool_fun_of_BDD cfg r2))
                (bool_fun_or (bool_fun_of_BDD cfg node1)
                   (bool_fun_of_BDD cfg l2))).
  apply bool_fun_if_preserves_eq.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_or (bool_fun_of_BDD cfgl node1)
                (bool_fun_of_BDD cfgl r2)).
  assumption.  apply bool_fun_or_preserves_eq.
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  assumption.
  assumption.  assumption.  assumption.
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  assumption.
  assumption.  assumption.  assumption.  
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfgl nodel).
  apply used_nodes_preserved'_bool_fun with (ul := nodel :: ul).  assumption.
  assumption.  assumption.  assumption.  apply used_node'_cons_node_ul.  
  assumption.  apply bool_fun_eq_sym.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_or (bool_fun_of_BDD cfg node1)
                (bool_fun_if x2 (bool_fun_of_BDD cfg r2)
                   (bool_fun_of_BDD cfg l2))).
  apply bool_fun_or_preserves_eq.  apply bool_fun_eq_refl.
  apply bool_fun_of_BDD_int.  assumption.  assumption.
  apply bool_fun_or_orthogonal_right.  apply nodes_preserved_node_height_eq.
  assumption.  assumption.  assumption.  assumption.  apply BDDorm_put_OK.
  assumption.  assumption.  assumption.  assumption.  
  rewrite (Neqb_complete (node_height cfg' node1) (node_height cfg node1)).
  rewrite (Neqb_complete (node_height cfg' node2) (node_height cfg node2)).
  unfold node_height at 2 3 in |- *.  unfold bs_node_height in |- *.  rewrite H5.  rewrite H6.
  rewrite (BDDvar_max_inf (ad_S x1) (ad_S x2)).  assumption.
  rewrite <- (ad_S_compare x1 x2).  assumption.
  apply used_nodes_preserved'_node_height_eq with (ul := ul).  assumption.  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfgl).  assumption.  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfgr).  assumption.  
  apply used_nodes_preserved_cons with (node := nodel).  assumption.
  apply used_nodes_preserved_cons with (node := nodel).
  apply used_nodes_preserved_cons with (node := noder).  assumption.  assumption.
  assumption.  apply used_nodes_preserved'_node_height_eq with (ul := ul).  assumption.
  assumption.  apply used_nodes_preserved_trans with (cfg2 := cfgl).  assumption.
  assumption.  apply used_nodes_preserved_trans with (cfg2 := cfgr).  assumption.
  apply used_nodes_preserved_cons with (node := nodel).  assumption.  
  apply used_nodes_preserved_cons with (node := nodel).
  apply used_nodes_preserved_cons with (node := noder).  assumption.  assumption.
  assumption.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_if x2 (bool_fun_of_BDD cfgr noder)
                (bool_fun_of_BDD cfgr nodel)).
  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_if x2
                (bool_fun_or (bool_fun_of_BDD cfg node1)
                   (bool_fun_of_BDD cfg r2))
                (bool_fun_or (bool_fun_of_BDD cfg node1)
                   (bool_fun_of_BDD cfg l2))).
  apply bool_fun_if_preserves_eq.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_or (bool_fun_of_BDD cfgl node1)
                (bool_fun_of_BDD cfgl r2)).
  assumption.  apply bool_fun_or_preserves_eq.
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.
  assumption.  assumption.  assumption.  assumption.  
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.
  assumption.  assumption.  assumption.  assumption.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfgl nodel).
  apply used_nodes_preserved'_bool_fun with (ul := nodel :: ul).  assumption.
  assumption.  assumption.  assumption.  apply used_node'_cons_node_ul.  
  assumption.  apply bool_fun_eq_sym.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_or (bool_fun_of_BDD cfg node1)
                (bool_fun_if x2 (bool_fun_of_BDD cfg r2)
                   (bool_fun_of_BDD cfg l2))).
  apply bool_fun_or_preserves_eq.
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfgl).  assumption.  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfgr).  assumption.  
  apply used_nodes_preserved_cons with (node := nodel).  assumption.
  apply used_nodes_preserved_cons with (node := nodel).
  apply used_nodes_preserved_cons with (node := noder).  assumption.  assumption.
  assumption.  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg node2).
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfgl).  assumption.  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfgr).  assumption.
  apply used_nodes_preserved_cons with (node := nodel).  assumption.  
  apply used_nodes_preserved_cons with (node := nodel).
  apply used_nodes_preserved_cons with (node := noder).  assumption.  assumption.
  assumption.  apply bool_fun_of_BDD_int.  assumption.  assumption.  
  apply bool_fun_or_orthogonal_right.  apply BDDorm_put_nodes_preserved.  
  apply used_nodes_preserved_node_OK' with (ul := ul) (cfg := cfg).  assumption.  
  assumption.  assumption.  apply used_nodes_preserved_trans with (cfg2 := cfgl).
  assumption.  assumption.  apply used_nodes_preserved_trans with (cfg2 := cfgr).
  assumption.  apply used_nodes_preserved_cons with (node := nodel).  assumption.
  apply used_nodes_preserved_cons with (node := nodel).
  apply used_nodes_preserved_cons with (node := noder).  assumption.  
  apply used_nodes_preserved_node_OK' with (ul := ul) (cfg := cfg).  assumption.  
  assumption.  assumption.  apply used_nodes_preserved_trans with (cfg2 := cfgl).
  assumption.  assumption.  apply used_nodes_preserved_trans with (cfg2 := cfgr).
  assumption.  apply used_nodes_preserved_cons with (node := nodel).  assumption.
  apply used_nodes_preserved_cons with (node := nodel).
  apply used_nodes_preserved_cons with (node := noder).  assumption.
  replace cfg' with
   (fst (BDDmake gc cfgr x2 nodel noder (noder :: nodel :: ul))).
  replace node' with
   (snd (BDDmake gc cfgr x2 nodel noder (noder :: nodel :: ul))).
  apply BDDmake_node_height_le.  assumption.  assumption.  rewrite H9.  reflexivity.
  rewrite H9.  reflexivity.  replace node' with
   (snd (BDDmake gc cfgr x2 nodel noder (noder :: nodel :: ul))).
  replace cfg' with
   (fst (BDDmake gc cfgr x2 nodel noder (noder :: nodel :: ul))).
  apply BDDmake_bool_fun.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  rewrite H9.  reflexivity.  rewrite H9.
  reflexivity.  replace cfg' with
   (fst (BDDmake gc cfgr x2 nodel noder (noder :: nodel :: ul))).
  replace node' with
   (snd (BDDmake gc cfgr x2 nodel noder (noder :: nodel :: ul))).
  apply BDDmake_node_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  rewrite H9.  reflexivity.  rewrite H9.
  reflexivity.  replace cfg' with
   (fst (BDDmake gc cfgr x2 nodel noder (noder :: nodel :: ul))).
  apply BDDmake_preserves_used_nodes.  assumption.  assumption.  assumption.
  rewrite H9.  reflexivity.
  replace cfg' with
   (fst (BDDmake gc cfgr x2 nodel noder (noder :: nodel :: ul))).
  apply BDDmake_keeps_config_OK.  assumption.  assumption.  assumption.  
  assumption.  assumption.  assumption.  assumption.  rewrite H9.  reflexivity.
  intros.  rewrite (ad_S_compare xr x2).
  replace (ad_S xr) with (node_height cfgr noder).
  replace (ad_S x2) with (node_height cfg node2).  apply BDDlt_compare.
  apply
   le_lt_trans
    with
      (m := nat_of_N
              (BDDvar_max (node_height cfgl node1) (node_height cfgl r2))).
  apply leb_complete.  assumption.
  rewrite (Neqb_complete (node_height cfgl node1) (node_height cfg node1)).
  rewrite (Neqb_complete (node_height cfgl r2) (node_height cfg r2)).
  rewrite (BDDvar_max_max (node_height cfg node1) (node_height cfg r2)).
  rewrite <- (max_x_x_eq_x (nat_of_N (node_height cfg node2))).  apply lt_max_1.
  apply BDDcompare_lt.  unfold node_height in |- *.  unfold bs_node_height in |- *.  rewrite H5.  rewrite H6.
  rewrite <- (ad_S_compare x1 x2).  assumption.  apply BDDcompare_lt.
  unfold node_height in |- *.  apply bs_node_height_right with (x := x2) (l := l2).  exact (proj1 H1).  
  assumption.  apply used_nodes_preserved'_node_height_eq with (ul := ul).
  assumption.  assumption.  assumption.  assumption.  assumption.
  apply used_nodes_preserved'_node_height_eq with (ul := ul).  assumption.  assumption.
  assumption.  assumption.  assumption.  unfold node_height in |- *.  unfold bs_node_height in |- *.
  rewrite H6.  reflexivity.  unfold node_height in |- *.  unfold bs_node_height in |- *.  rewrite H32.
  reflexivity.  intros.  rewrite (ad_S_compare xl x2).
  replace (ad_S xl) with (node_height cfgr nodel).
  replace (ad_S x2) with (node_height cfg node2).
  rewrite (Neqb_complete (node_height cfgr nodel) (node_height cfgl nodel)).
  apply BDDlt_compare.
  apply
   le_lt_trans
    with
      (m := nat_of_N
              (BDDvar_max (node_height cfg node1) (node_height cfg l2))).
  apply leb_complete.  assumption.
  rewrite (BDDvar_max_max (node_height cfg node1) (node_height cfg l2)).
  rewrite <- (max_x_x_eq_x (nat_of_N (node_height cfg node2))).  apply lt_max_1.
  apply BDDcompare_lt.  unfold node_height in |- *.  unfold bs_node_height in |- *.  rewrite H5.  rewrite H6.
  rewrite <- (ad_S_compare x1 x2).  assumption.  apply BDDcompare_lt.
  unfold node_height in |- *.  apply bs_node_height_left with (x := x2) (r := r2).  exact (proj1 H1).
  assumption.  apply used_nodes_preserved'_node_height_eq with (ul := nodel :: ul).
  assumption.  assumption.  assumption.  assumption.
  apply used_node'_cons_node_ul.  unfold node_height in |- *.  unfold bs_node_height in |- *.  rewrite H6.
  reflexivity.  unfold node_height in |- *.  unfold bs_node_height in |- *.  rewrite H32.  reflexivity.
  apply used_node'_cons_node_ul.  apply used_node'_cons_node'_ul.
  apply used_node'_cons_node_ul.  apply node_OK_list_OK.  assumption.
  assumption.  apply used_nodes_preserved_list_OK with (cfg := cfgl).  assumption.
  assumption.  replace cfgr with (fst (BDDor_1 cfgl (nodel :: ul) node1 r2 n)).
  replace noder with (snd (BDDor_1 cfgl (nodel :: ul) node1 r2 n)).  apply H.
  apply
   lt_trans_1
    with
      (y := max (nat_of_N (node_height cfg node1))
              (nat_of_N (node_height cfg node2))).
  rewrite <- (BDDvar_max_max (node_height cfg node1) (node_height cfg node2)).
  rewrite (BDDvar_max_inf (node_height cfg node1) (node_height cfg node2)).
  rewrite <- (max_x_x_eq_x (nat_of_N (node_height cfg node2))).  apply lt_max_1.
  rewrite (Neqb_complete (node_height cfgl node1) (node_height cfg node1)).  unfold node_height in |- *.
  apply BDDcompare_lt.  unfold bs_node_height in |- *.  rewrite H5.  rewrite H6.
  rewrite <- (ad_S_compare x1 x2).  assumption.
  apply used_nodes_preserved'_node_height_eq with (ul := ul).  assumption.  assumption.
  assumption.  assumption.  assumption.
  rewrite (Neqb_complete (node_height cfgl r2) (node_height cfg r2)).  apply BDDcompare_lt.
  unfold node_height in |- *.  apply bs_node_height_right with (x := x2) (l := l2).  exact (proj1 H1).
  assumption.  apply used_nodes_preserved'_node_height_eq with (ul := ul).  assumption.
  assumption.  assumption.  assumption.  assumption.  unfold node_height in |- *.
  unfold bs_node_height in |- *.  rewrite H5.  rewrite H6.  rewrite <- (ad_S_compare x1 x2).
  assumption.  assumption.  assumption.  assumption.  assumption.  assumption.
  rewrite H8.  reflexivity.  rewrite H8.  reflexivity.
  apply used_node'_cons_node'_ul.  assumption.  apply used_node'_cons_node'_ul.
  assumption.  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.
  assumption.  assumption.  apply used_nodes_preserved_used_node' with (cfg := cfg).
  assumption.  assumption.  assumption.  apply node_OK_list_OK.  assumption.
  assumption.  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.
  assumption.  replace cfgl with (fst (BDDor_1 cfg ul node1 l2 n)).
  replace nodel with (snd (BDDor_1 cfg ul node1 l2 n)).  apply H.
  apply
   lt_trans_1
    with
      (y := max (nat_of_N (node_height cfg node1))
              (nat_of_N (node_height cfg node2))).
  rewrite <- (BDDvar_max_max (node_height cfg node1) (node_height cfg node2)).
  rewrite (BDDvar_max_inf (node_height cfg node1) (node_height cfg node2)).
  rewrite <- (max_x_x_eq_x (nat_of_N (node_height cfg node2))).  apply lt_max_1.
  unfold node_height in |- *.  apply BDDcompare_lt.  unfold bs_node_height in |- *.  rewrite H5.  rewrite H6.
  rewrite <- (ad_S_compare x1 x2).  assumption.  apply BDDcompare_lt.
  unfold node_height in |- *.  apply bs_node_height_left with (x := x2) (r := r2).  exact (proj1 H1).
  assumption.  unfold node_height in |- *.  unfold bs_node_height in |- *.  rewrite H5.  rewrite H6.
  rewrite <- (ad_S_compare x1 x2).  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  rewrite H7.  reflexivity.  rewrite H7.
  reflexivity.  apply high_used' with (node := node2) (x := x2) (l := l2).  assumption.
  assumption.  assumption.  apply low_used' with (node := node2) (x := x2) (r := r2).
  assumption.  assumption.  assumption.  intro y0.  rewrite y0.
  cut (BDDcompare x2 x1 = Datatypes.Lt).  intro y00.
  elim (prod_sum _ _ (BDDor_1 cfg ul l1 node2 n)).  intros cfgl H7.
  elim H7; clear H7.  intros nodel H7.  rewrite H7.
  elim (prod_sum _ _ (BDDor_1 cfgl (nodel :: ul) r1 node2 n)).
  intros cfgr H8.  elim H8; clear H8.  intros noder H8.  rewrite H8.
  elim (prod_sum _ _ (BDDmake gc cfgr x1 nodel noder (noder :: nodel :: ul))).
  intros cfg' H9.  elim H9; clear H9.  intros node' H9.  rewrite H9.
  simpl in |- *.  cut (used_node' cfg ul l1).  cut (used_node' cfg ul r1).  intros.
  cut
   (BDDconfig_OK cfgl /\
    config_node_OK cfgl nodel /\
    used_nodes_preserved cfg cfgl ul /\
    Nleb (node_height cfgl nodel)
      (BDDvar_max (node_height cfg l1) (node_height cfg node2)) = true /\
    bool_fun_eq (bool_fun_of_BDD cfgl nodel)
      (bool_fun_or (bool_fun_of_BDD cfg l1) (bool_fun_of_BDD cfg node2))).
  intro.  elim H12; clear H12; intros.  elim H13; clear H13; intros.
  elim H14; clear H14; intros.  elim H15; clear H15; intros.
  cut (used_list_OK cfgl ul).  intro.  cut (used_list_OK cfgl (nodel :: ul)).
  intro.  cut (used_node' cfgl ul node2).  cut (used_node' cfgl ul r1).  intros.
  cut (used_node' cfgl (nodel :: ul) node2).
  cut (used_node' cfgl (nodel :: ul) r1).  intros.
  cut
   (BDDconfig_OK cfgr /\
    config_node_OK cfgr noder /\
    used_nodes_preserved cfgl cfgr (nodel :: ul) /\
    Nleb (node_height cfgr noder)
      (BDDvar_max (node_height cfgl r1) (node_height cfgl node2)) = true /\
    bool_fun_eq (bool_fun_of_BDD cfgr noder)
      (bool_fun_or (bool_fun_of_BDD cfgl r1) (bool_fun_of_BDD cfgl node2))).

  intro.  elim H23; clear H23; intros.  elim H24; clear H24; intros.
  elim H25; clear H25; intros.  elim H26; clear H26; intros.
  cut (used_list_OK cfgr (nodel :: ul)).  intro.
  cut (used_list_OK cfgr (noder :: nodel :: ul)).  intro.
  cut (used_node' cfgr (noder :: nodel :: ul) nodel).
  cut (used_node' cfgr (noder :: nodel :: ul) noder).  intros.
  cut
   (forall (xl : BDDvar) (ll rl : ad),
    MapGet _ (fst cfgr) nodel = Some (xl, (ll, rl)) ->
    BDDcompare xl x1 = Datatypes.Lt).
  cut
   (forall (xr : BDDvar) (lr rr : ad),
    MapGet _ (fst cfgr) noder = Some (xr, (lr, rr)) ->
    BDDcompare xr x1 = Datatypes.Lt).
  intros.  cut (BDDconfig_OK cfg').
  cut (used_nodes_preserved cfgr cfg' (noder :: nodel :: ul)).
  cut (config_node_OK cfg' node').
  cut
   (bool_fun_eq (bool_fun_of_BDD cfg' node')
      (bool_fun_if x1 (bool_fun_of_BDD cfgr noder)
         (bool_fun_of_BDD cfgr nodel))).
  cut (Nleb (node_height cfg' node') (ad_S x1) = true).  intros.
  cut (config_node_OK cfg' node1).  cut (config_node_OK cfg' node2).  intros.
  cut (nodes_preserved cfg' (BDDor_memo_put cfg' node1 node2 node')).  intro.
  cut (BDDconfig_OK (BDDor_memo_put cfg' node1 node2 node')).  intro.  split.
  assumption.  split.  apply nodes_preserved_config_node_OK with (cfg1 := cfg').
  assumption.  assumption.  split.
  apply used_nodes_preserved_trans with (cfg2 := cfgr).  assumption.  
  apply used_nodes_preserved_trans with (cfg2 := cfgl).  assumption.  assumption.
  apply used_nodes_preserved_cons with (node := nodel).  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfg').  assumption.
  apply used_nodes_preserved_cons with (node := nodel).
  apply used_nodes_preserved_cons with (node := noder).  assumption.  
  apply nodes_preserved_used_nodes_preserved.  assumption.  
  rewrite
   (Neqb_complete
      (node_height (BDDor_memo_put cfg' node1 node2 node') node')
      (node_height cfg' node')).
  split.  unfold node_height at 2 3 in |- *.  unfold bs_node_height in |- *.  rewrite H5.  rewrite H6.
  rewrite (BDDvar_max_comm (ad_S x1) (ad_S x2)).
  rewrite (BDDvar_max_inf (ad_S x2) (ad_S x1)).  assumption.
  rewrite <- (ad_S_compare x2 x1).  assumption.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg' node').
  apply nodes_preserved_bool_fun.  assumption.  assumption.  assumption.  
  assumption.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_if x1 (bool_fun_of_BDD cfgr noder)
                (bool_fun_of_BDD cfgr nodel)).
  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_if x1
                (bool_fun_or (bool_fun_of_BDD cfg r1)
                   (bool_fun_of_BDD cfg node2))
                (bool_fun_or (bool_fun_of_BDD cfg l1)
                   (bool_fun_of_BDD cfg node2))).
  apply bool_fun_if_preserves_eq.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_or (bool_fun_of_BDD cfgl r1)
                (bool_fun_of_BDD cfgl node2)).
  assumption.  apply bool_fun_or_preserves_eq.
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  assumption.
  assumption.  assumption.  assumption.
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  assumption.
  assumption.  assumption.  assumption.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfgl nodel).
  apply used_nodes_preserved'_bool_fun with (ul := nodel :: ul).  assumption.  
  assumption.  assumption.  assumption.  apply used_node'_cons_node_ul.  
  assumption.  apply bool_fun_eq_sym.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_or
                (bool_fun_if x1 (bool_fun_of_BDD cfg r1)
                   (bool_fun_of_BDD cfg l1)) (bool_fun_of_BDD cfg node2)).
  apply bool_fun_or_preserves_eq.  apply bool_fun_of_BDD_int.  assumption.  
  assumption.  apply bool_fun_eq_refl.  apply bool_fun_or_orthogonal_left.  
  apply nodes_preserved_node_height_eq.  assumption.  assumption.  assumption.
  assumption.  apply BDDorm_put_OK.  assumption.  assumption.  assumption.
  assumption.  rewrite (Neqb_complete (node_height cfg' node1) (node_height cfg node1)).
  rewrite (Neqb_complete (node_height cfg' node2) (node_height cfg node2)).  unfold node_height at 2 3 in |- *.
  unfold bs_node_height in |- *.  rewrite H5.  rewrite H6.
  rewrite (BDDvar_max_comm (ad_S x1) (ad_S x2)).
  rewrite (BDDvar_max_inf (ad_S x2) (ad_S x1)).  assumption.
  rewrite <- (ad_S_compare x2 x1).  assumption.  
  apply used_nodes_preserved'_node_height_eq with (ul := ul).  assumption.  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfgl).  assumption.  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfgr).  assumption.  
  apply used_nodes_preserved_cons with (node := nodel).  assumption.  
  apply used_nodes_preserved_cons with (node := nodel).
  apply used_nodes_preserved_cons with (node := noder).  assumption.  assumption.
  assumption.  apply used_nodes_preserved'_node_height_eq with (ul := ul).  assumption.
  assumption.  apply used_nodes_preserved_trans with (cfg2 := cfgl).  assumption.
  assumption.  apply used_nodes_preserved_trans with (cfg2 := cfgr).  assumption.
  apply used_nodes_preserved_cons with (node := nodel).  assumption.  
  apply used_nodes_preserved_cons with (node := nodel).
  apply used_nodes_preserved_cons with (node := noder).  assumption.  assumption.
  assumption.  
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_if x1 (bool_fun_of_BDD cfgr noder)
                (bool_fun_of_BDD cfgr nodel)).
  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_if x1
                (bool_fun_or (bool_fun_of_BDD cfg r1)
                   (bool_fun_of_BDD cfg node2))
                (bool_fun_or (bool_fun_of_BDD cfg l1)
                   (bool_fun_of_BDD cfg node2))).
  apply bool_fun_if_preserves_eq.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_or (bool_fun_of_BDD cfgl r1)
                (bool_fun_of_BDD cfgl node2)).
  assumption.  apply bool_fun_or_preserves_eq.
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  assumption.
  assumption.  assumption.  assumption.  
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  assumption.
  assumption.  assumption.  assumption.  
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfgl nodel).
  apply used_nodes_preserved'_bool_fun with (ul := nodel :: ul).  assumption.
  assumption.  assumption.  assumption.  apply used_node'_cons_node_ul.  
  assumption.  apply bool_fun_eq_sym.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_or
                (bool_fun_if x1 (bool_fun_of_BDD cfg r1)
                   (bool_fun_of_BDD cfg l1)) (bool_fun_of_BDD cfg node2)).
  apply bool_fun_or_preserves_eq.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg node1).
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfgl).  assumption.  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfgr).  assumption.  
  apply used_nodes_preserved_cons with (node := nodel).  assumption.  
  apply used_nodes_preserved_cons with (node := nodel).
  apply used_nodes_preserved_cons with (node := noder).  assumption.  assumption.
  assumption.  apply bool_fun_of_BDD_int.  assumption.  assumption.  
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfgl).  assumption.  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfgr).  assumption.  
  apply used_nodes_preserved_cons with (node := nodel).  assumption.
  apply used_nodes_preserved_cons with (node := nodel).
  apply used_nodes_preserved_cons with (node := noder).  assumption.  assumption.
  assumption.  apply bool_fun_or_orthogonal_left.
  apply BDDorm_put_nodes_preserved.
  apply used_nodes_preserved_node_OK' with (ul := ul) (cfg := cfg).  assumption.
  assumption.  assumption.  apply used_nodes_preserved_trans with (cfg2 := cfgl).
  assumption.  assumption.  apply used_nodes_preserved_trans with (cfg2 := cfgr).
  assumption.  apply used_nodes_preserved_cons with (node := nodel).  assumption.
  apply used_nodes_preserved_cons with (node := nodel).
  apply used_nodes_preserved_cons with (node := noder).  assumption.  
  apply used_nodes_preserved_node_OK' with (ul := ul) (cfg := cfg).  assumption.
  assumption.  assumption.  apply used_nodes_preserved_trans with (cfg2 := cfgl).
  assumption.  assumption.  apply used_nodes_preserved_trans with (cfg2 := cfgr).
  assumption.  apply used_nodes_preserved_cons with (node := nodel).  assumption.
  apply used_nodes_preserved_cons with (node := nodel).
  apply used_nodes_preserved_cons with (node := noder).  assumption.
  replace cfg' with
   (fst (BDDmake gc cfgr x1 nodel noder (noder :: nodel :: ul))).
  replace node' with
   (snd (BDDmake gc cfgr x1 nodel noder (noder :: nodel :: ul))).
  apply BDDmake_node_height_le.  assumption.  assumption.  rewrite H9.  reflexivity.
  rewrite H9.  reflexivity.
  replace node' with
   (snd (BDDmake gc cfgr x1 nodel noder (noder :: nodel :: ul))).
  replace cfg' with
   (fst (BDDmake gc cfgr x1 nodel noder (noder :: nodel :: ul))).
  apply BDDmake_bool_fun.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  rewrite H9.  reflexivity.  rewrite H9.
  reflexivity.  replace cfg' with
   (fst (BDDmake gc cfgr x1 nodel noder (noder :: nodel :: ul))).
  replace node' with
   (snd (BDDmake gc cfgr x1 nodel noder (noder :: nodel :: ul))).
  apply BDDmake_node_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  rewrite H9.  reflexivity.  rewrite H9.
  reflexivity.  replace cfg' with
   (fst (BDDmake gc cfgr x1 nodel noder (noder :: nodel :: ul))).
  apply BDDmake_preserves_used_nodes.  assumption.  assumption.  assumption.  
  rewrite H9.  reflexivity.
  replace cfg' with
   (fst (BDDmake gc cfgr x1 nodel noder (noder :: nodel :: ul))).
  apply BDDmake_keeps_config_OK.  assumption.  assumption.  assumption.  
  assumption.  assumption.  assumption.  assumption.  rewrite H9.  reflexivity.
  intros.  rewrite (ad_S_compare xr x1).
  replace (ad_S xr) with (node_height cfgr noder).
  replace (ad_S x1) with (node_height cfg node1).  apply BDDlt_compare.
  apply
   le_lt_trans
    with
      (m := nat_of_N
              (BDDvar_max (node_height cfgl r1) (node_height cfgl node2))).
  apply leb_complete.  assumption.  
  rewrite (Neqb_complete (node_height cfgl r1) (node_height cfg r1)).
  rewrite (Neqb_complete (node_height cfgl node2) (node_height cfg node2)).
  rewrite (BDDvar_max_max (node_height cfg r1) (node_height cfg node2)).
  rewrite <- (max_x_x_eq_x (nat_of_N (node_height cfg node1))).  apply lt_max_1.  
  apply BDDcompare_lt.  unfold node_height in |- *.  apply bs_node_height_right with (x := x1) (l := l1).
  exact (proj1 H1).  assumption.  apply BDDcompare_lt.  unfold node_height in |- *.
  unfold bs_node_height in |- *.  rewrite H5.  rewrite H6.  rewrite <- (ad_S_compare x2 x1).
  assumption.  apply used_nodes_preserved'_node_height_eq with (ul := ul).  assumption.
  assumption.  assumption.  assumption.  assumption.
  apply used_nodes_preserved'_node_height_eq with (ul := ul).  assumption.  assumption.  
  assumption.  assumption.  assumption.  unfold node_height in |- *.  unfold bs_node_height in |- *.
  rewrite H5.  reflexivity.  unfold node_height in |- *.  unfold bs_node_height in |- *.  rewrite H32.
  reflexivity.  intros.  rewrite (ad_S_compare xl x1).
  replace (ad_S xl) with (node_height cfgr nodel).
  replace (ad_S x1) with (node_height cfg node1).
  rewrite (Neqb_complete (node_height cfgr nodel) (node_height cfgl nodel)).
  apply BDDlt_compare.
  apply
   le_lt_trans
    with
      (m := nat_of_N
              (BDDvar_max (node_height cfg l1) (node_height cfg node2))).
  apply leb_complete.  assumption.
  rewrite (BDDvar_max_max (node_height cfg l1) (node_height cfg node2)).
  rewrite <- (max_x_x_eq_x (nat_of_N (node_height cfg node1))).  apply lt_max_1.
  apply BDDcompare_lt.  unfold node_height in |- *.  apply bs_node_height_left with (x := x1) (r := r1).
  exact (proj1 H1).  assumption.  apply BDDcompare_lt.  unfold node_height in |- *.
  unfold bs_node_height in |- *.  rewrite H5.  rewrite H6.  rewrite <- (ad_S_compare x2 x1).
  assumption.  apply used_nodes_preserved'_node_height_eq with (ul := nodel :: ul).
  assumption.  assumption.  assumption.  assumption.
  apply used_node'_cons_node_ul.  unfold node_height in |- *.  unfold bs_node_height in |- *.  rewrite H5.
  reflexivity.  unfold node_height in |- *.  unfold bs_node_height in |- *.  rewrite H32.  reflexivity.
  apply used_node'_cons_node_ul.  apply used_node'_cons_node'_ul.
  apply used_node'_cons_node_ul.  apply node_OK_list_OK.  assumption.
  assumption.  apply used_nodes_preserved_list_OK with (cfg := cfgl).  assumption.
  assumption.  replace cfgr with (fst (BDDor_1 cfgl (nodel :: ul) r1 node2 n)).
  replace noder with (snd (BDDor_1 cfgl (nodel :: ul) r1 node2 n)).  apply H.
  apply
   lt_trans_1
    with
      (y := max (nat_of_N (node_height cfg node1))
              (nat_of_N (node_height cfg node2))).
  rewrite <- (BDDvar_max_max (node_height cfg node1) (node_height cfg node2)).
  rewrite (BDDvar_max_comm (node_height cfg node1) (node_height cfg node2)).
  rewrite (BDDvar_max_inf (node_height cfg node2) (node_height cfg node1)).
  rewrite <- (max_x_x_eq_x (nat_of_N (node_height cfg node1))).  apply lt_max_1.
  rewrite (Neqb_complete (node_height cfgl r1) (node_height cfg r1)).  apply BDDcompare_lt.
  unfold node_height in |- *.  apply bs_node_height_right with (x := x1) (l := l1).  exact (proj1 H1).
  assumption.  apply used_nodes_preserved'_node_height_eq with (ul := ul).  assumption.
  assumption.  assumption.  assumption.  assumption.
  rewrite (Neqb_complete (node_height cfgl node2) (node_height cfg node2)).  unfold node_height in |- *.
  apply BDDcompare_lt.  unfold bs_node_height in |- *.  rewrite H5.  rewrite H6.
  rewrite <- (ad_S_compare x2 x1).  assumption.
  apply used_nodes_preserved'_node_height_eq with (ul := ul).  assumption.  assumption.
  assumption.  assumption.  assumption.  unfold node_height in |- *.  unfold bs_node_height in |- *.
  rewrite H5.  rewrite H6.  rewrite <- (ad_S_compare x2 x1).  assumption.
  assumption.  assumption.  assumption.  assumption.  assumption.  rewrite H8.
  reflexivity.  rewrite H8.  reflexivity.  apply used_node'_cons_node'_ul.
  assumption.  apply used_node'_cons_node'_ul.  assumption.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.
  assumption.  assumption.  apply used_nodes_preserved_used_node' with (cfg := cfg).
  assumption.  assumption.  assumption.  apply node_OK_list_OK.  assumption.  
  assumption.  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.  
  assumption.  replace cfgl with (fst (BDDor_1 cfg ul l1 node2 n)).
  replace nodel with (snd (BDDor_1 cfg ul l1 node2 n)).  apply H.
  apply
   lt_trans_1
    with
      (y := max (nat_of_N (node_height cfg node1))
              (nat_of_N (node_height cfg node2))).
  rewrite <- (BDDvar_max_max (node_height cfg node1) (node_height cfg node2)).
  rewrite (BDDvar_max_comm (node_height cfg node1) (node_height cfg node2)).
  rewrite (BDDvar_max_inf (node_height cfg node2) (node_height cfg node1)).
  rewrite <- (max_x_x_eq_x (nat_of_N (node_height cfg node1))).  apply lt_max_1.
  apply BDDcompare_lt.  unfold node_height in |- *.  apply bs_node_height_left with (x := x1) (r := r1).
  exact (proj1 H1).  assumption.  unfold node_height in |- *.  apply BDDcompare_lt.
  unfold bs_node_height in |- *.  rewrite H5.  rewrite H6.  rewrite <- (ad_S_compare x2 x1).
  assumption.  unfold node_height in |- *.  unfold bs_node_height in |- *.  rewrite H5.  rewrite H6.
  rewrite <- (ad_S_compare x2 x1).  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  rewrite H7.  reflexivity.  rewrite H7.
  reflexivity.  apply high_used' with (node := node1) (x := x1) (l := l1).  assumption.
  assumption.  assumption.  apply low_used' with (node := node1) (x := x1) (r := r1).
  assumption.  assumption.  assumption.  apply BDDcompare_sup_inf.  assumption.
  intro y0.  rewrite y0.  elim (sumbool_of_bool (Neqb node2 BDDzero)).  intro y1.
  rewrite y1.  cut (nodes_preserved cfg (BDDor_memo_put cfg node1 node2 node1)).
  intro.  cut (BDDconfig_OK (BDDor_memo_put cfg node1 node2 node1)).  intro.
  split.  assumption.  split.
  apply nodes_preserved_config_node_OK with (cfg1 := cfg).  assumption.  
  apply used_node'_OK with (ul := ul).  assumption.  assumption.  assumption.
  split.  apply nodes_preserved_used_nodes_preserved.  assumption.  split.
  simpl in |- *.  rewrite (Neqb_complete _ _ y1).
  rewrite (Neqb_complete _ _ (node_height_zero cfg H1)).
  rewrite (BDDvar_max_comm (node_height cfg node1) N0).  unfold BDDvar_max in |- *.  simpl in |- *.
  rewrite
   (Neqb_complete
      (node_height (BDDor_memo_put cfg node1 BDDzero node1) node1)
      (node_height cfg node1)).
  apply Nleb_refl.  apply nodes_preserved_node_height_eq.  assumption.
  rewrite <- (Neqb_complete _ _ y1).  assumption.
  rewrite <- (Neqb_complete _ _ y1).  assumption.
  apply used_node'_OK with (ul := ul).  assumption.  assumption.  assumption.
  simpl in |- *.  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg node1).
  apply nodes_preserved_bool_fun.  assumption.  assumption.  assumption.
  apply used_node'_OK with (ul := ul).  assumption.  assumption.  assumption.
  rewrite (Neqb_complete _ _ y1).
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_or (bool_fun_of_BDD cfg node1) bool_fun_zero).
  apply bool_fun_eq_sym.  apply bool_fun_or_zero.
  apply bool_fun_or_preserves_eq.  apply bool_fun_eq_refl.
  apply bool_fun_eq_sym.  apply bool_fun_of_BDD_zero.  assumption.  
  apply BDDorm_put_OK.  assumption.  apply used_node'_OK with (ul := ul).
  assumption.  assumption.  assumption.  apply used_node'_OK with (ul := ul).
  assumption.  assumption.  assumption.  apply used_node'_OK with (ul := ul).
  assumption.  assumption.  assumption.  apply BDDvar_le_max_1.
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_or (bool_fun_of_BDD cfg node1) bool_fun_zero).
  apply bool_fun_eq_sym.  apply bool_fun_or_zero.
  apply bool_fun_or_preserves_eq.  apply bool_fun_eq_refl.
  apply bool_fun_eq_sym.  rewrite (Neqb_complete _ _ y1).
  apply bool_fun_of_BDD_zero.  assumption.  apply BDDorm_put_nodes_preserved.
  intro y1.  rewrite y1.  cut (Neqb node2 BDDone = true).  intro.
  cut (config_node_OK cfg node1).  cut (config_node_OK cfg node2).  intros.
  cut (nodes_preserved cfg (BDDor_memo_put cfg node1 node2 node2)).  intro.
  cut (BDDconfig_OK (BDDor_memo_put cfg node1 node2 node2)).  intro.  split.
  assumption.  split.  apply nodes_preserved_config_node_OK with (cfg1 := cfg).
  assumption.  assumption.  split.  apply nodes_preserved_used_nodes_preserved.
  assumption.  split.  simpl in |- *.
  rewrite
   (Neqb_complete (node_height (BDDor_memo_put cfg node1 node2 node2) node2)
      (node_height cfg node2)).
  apply BDDvar_le_max_2.  apply nodes_preserved_node_height_eq.  assumption.
  assumption.  assumption.  assumption.  simpl in |- *.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg node2).
  apply nodes_preserved_bool_fun.  assumption.  assumption.  assumption.  
  assumption.  rewrite (Neqb_complete _ _ H6).
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_or (bool_fun_of_BDD cfg node1) bool_fun_one).
  apply bool_fun_eq_sym.  apply bool_fun_eq_trans with (bf2 := bool_fun_one).
  apply bool_fun_or_one.  apply bool_fun_eq_sym.  apply bool_fun_of_BDD_one.
  assumption.  apply bool_fun_or_preserves_eq.  apply bool_fun_eq_refl.  
  apply bool_fun_eq_sym.  apply bool_fun_of_BDD_one.  assumption.
  apply BDDorm_put_OK.  assumption.  assumption.  assumption.  assumption.  
  apply BDDvar_le_max_2.
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_or (bool_fun_of_BDD cfg node1) bool_fun_one).
  apply bool_fun_eq_sym.  rewrite (Neqb_complete _ _ H6).
  apply bool_fun_eq_trans with (bf2 := bool_fun_one).  apply bool_fun_or_one.
  apply bool_fun_eq_sym.  apply bool_fun_of_BDD_one.  assumption.
  apply bool_fun_or_preserves_eq.  apply bool_fun_eq_refl.
  apply bool_fun_eq_sym.  rewrite (Neqb_complete _ _ H6).
  apply bool_fun_of_BDD_one.  assumption.  apply BDDorm_put_nodes_preserved.
  apply used_node'_OK with (ul := ul).  assumption.  assumption.  assumption.
  apply used_node'_OK with (ul := ul).  assumption.  assumption.  assumption.  
  apply not_zero_is_one with (cfg := cfg).  apply used_node'_OK with (ul := ul).
  assumption.  assumption.  assumption.  unfold in_dom in |- *.  rewrite y0.
  reflexivity.  assumption.  intro y0.  rewrite y0.
  cut (config_node_OK cfg node1).  cut (config_node_OK cfg node2).
  intros H00 H01.  elim (sumbool_of_bool (Neqb node1 BDDzero)).  intro y1.
  rewrite y1.  cut (nodes_preserved cfg (BDDor_memo_put cfg node1 node2 node2)).
  intro.  cut (BDDconfig_OK (BDDor_memo_put cfg node1 node2 node2)).  intro.
  split.  assumption.  split.
  apply nodes_preserved_config_node_OK with (cfg1 := cfg).  assumption.  assumption.
  split.  apply nodes_preserved_used_nodes_preserved.  assumption.  split.
  simpl in |- *.  rewrite
   (Neqb_complete (node_height (BDDor_memo_put cfg node1 node2 node2) node2)
      (node_height cfg node2)).
  apply BDDvar_le_max_2.  apply nodes_preserved_node_height_eq.  assumption.  
  assumption.  assumption.  assumption.  simpl in |- *.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg node2).
  apply nodes_preserved_bool_fun.  assumption.  assumption.  assumption.  
  assumption.  rewrite (Neqb_complete _ _ y1).
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_or bool_fun_zero (bool_fun_of_BDD cfg node2)).
  apply bool_fun_eq_sym.
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_or (bool_fun_of_BDD cfg node2) bool_fun_zero).
  apply bool_fun_or_comm.  apply bool_fun_or_zero.
  apply bool_fun_or_preserves_eq.  apply bool_fun_eq_sym.
  apply bool_fun_of_BDD_zero.  assumption.  apply bool_fun_eq_refl.
  apply BDDorm_put_OK.  assumption.  assumption.  assumption.  assumption.
  apply BDDvar_le_max_2.  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_or bool_fun_zero (bool_fun_of_BDD cfg node2)).
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_or (bool_fun_of_BDD cfg node2) bool_fun_zero).
  apply bool_fun_eq_sym.  apply bool_fun_or_zero.  apply bool_fun_or_comm.  
  apply bool_fun_or_preserves_eq.  apply bool_fun_eq_sym.
  rewrite (Neqb_complete _ _ y1).  apply bool_fun_of_BDD_zero.  assumption.
  apply bool_fun_eq_refl.  apply BDDorm_put_nodes_preserved.  intro y1.
  rewrite y1.  cut (Neqb node1 BDDone = true).  intro.
  cut (nodes_preserved cfg (BDDor_memo_put cfg node1 node2 node1)).  intro.
  cut (BDDconfig_OK (BDDor_memo_put cfg node1 node2 node1)).  intro.  split.
  assumption.  split.  apply nodes_preserved_config_node_OK with (cfg1 := cfg).
  assumption.  assumption.  split.  apply nodes_preserved_used_nodes_preserved.
  assumption.  split.  simpl in |- *.  
  rewrite
   (Neqb_complete (node_height (BDDor_memo_put cfg node1 node2 node1) node1)
      (node_height cfg node1)).
  apply BDDvar_le_max_1.  apply nodes_preserved_node_height_eq.  assumption.  
  assumption.  assumption.  assumption.  simpl in |- *.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg node1).
  apply nodes_preserved_bool_fun.  assumption.  assumption.  assumption.  
  assumption.  rewrite (Neqb_complete _ _ H5).
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_or (bool_fun_of_BDD cfg node2) bool_fun_one).
  apply bool_fun_eq_sym.  apply bool_fun_eq_trans with (bf2 := bool_fun_one).
  apply bool_fun_or_one.  apply bool_fun_eq_sym.  apply bool_fun_of_BDD_one.
  assumption.  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_or bool_fun_one (bool_fun_of_BDD cfg node2)).
  apply bool_fun_or_comm.  apply bool_fun_or_preserves_eq.
  apply bool_fun_eq_sym.  apply bool_fun_of_BDD_one.  assumption.  
  apply bool_fun_eq_refl.  apply BDDorm_put_OK.  assumption.  assumption.
  assumption.  assumption.  apply BDDvar_le_max_1.
  rewrite (Neqb_complete _ _ H5).  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_or (bool_fun_of_BDD cfg node2) bool_fun_one).
  apply bool_fun_eq_sym.  apply bool_fun_eq_trans with (bf2 := bool_fun_one).
  apply bool_fun_or_one.  apply bool_fun_eq_sym.  apply bool_fun_of_BDD_one.
  assumption.  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_or bool_fun_one (bool_fun_of_BDD cfg node2)).
  apply bool_fun_or_comm.  apply bool_fun_or_preserves_eq.
  apply bool_fun_eq_sym.  apply bool_fun_of_BDD_one.  assumption.  
  apply bool_fun_eq_refl.  apply BDDorm_put_nodes_preserved.  
  apply not_zero_is_one with (cfg := cfg).  assumption.  unfold in_dom in |- *.
  rewrite y0.  reflexivity.  assumption.  apply used_node'_OK with (ul := ul).
  assumption.  assumption.  assumption.  apply used_node'_OK with (ul := ul).
  assumption.  assumption.  assumption.  
Qed.

End BDD_or.