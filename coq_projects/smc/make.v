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

Section BDD_make.

Variable gc : BDDconfig -> list ad -> BDDconfig.
Hypothesis gc_is_OK : gc_OK gc.

(* The arguments for the make function *)
Variable cfg : BDDconfig.
Variable x : BDDvar.
Variable l r : ad.
Variable ul : list ad.

(* Conditions on the arguments for the make function *)
Hypothesis cfg_OK : BDDconfig_OK cfg.
Hypothesis ul_OK : used_list_OK cfg ul.
Hypothesis l_used' : used_node' cfg ul l.
Hypothesis r_used' : used_node' cfg ul r.
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

Lemma no_dup :
 MapGet3 ad (fst (snd cfg)) l r x = None ->
 forall (x' : BDDvar) (l' r' a : ad),
 MapGet (BDDvar * (ad * ad)) (bs_of_cfg cfg) a =
 Some (x', (l', r')) -> (x, (l, r)) <> (x', (l', r')).
Proof.
  unfold not in |- *.  intros.  injection H1.  intros.  rewrite <- H2 in H0.
  rewrite <- H3 in H0.  rewrite <- H4 in H0.
  rewrite (proj2 (proj1 (proj2 cfg_OK) x l r a) H0) in H.
  discriminate.
Qed.

Definition BDDmake :=
  if Neqb l r
  then (cfg, l)
  else
   match MapGet3 _ (fst (snd cfg)) l r x with
   | Some y => (cfg, y)
   | None => BDDalloc gc cfg x l r ul
   end.

Lemma BDDmake_keeps_config_OK : BDDconfig_OK (fst BDDmake).
Proof.
  unfold BDDmake in |- *.  elim (sumbool_of_bool (Neqb l r)).  intro y.  rewrite y.
  assumption.  intro y.  rewrite y.
  elim (option_sum _ (MapGet3 ad (fst (snd cfg)) l r x)).  intro y0.  elim y0.
  clear y0.  intros node y0.  rewrite y0.  assumption.  intro y0.  rewrite y0.
  apply BDDalloc_keeps_config_OK.  assumption.  assumption.  assumption.  
  assumption.  assumption.  assumption.  assumption.  assumption.  intros.
  apply no_dup with (a := a).  assumption.  assumption.
Qed.

Lemma BDDmake_preserves_used_nodes :
 used_nodes_preserved cfg (fst BDDmake) ul.
Proof.
  unfold BDDmake in |- *.  elim (sumbool_of_bool (Neqb l r)).  intro y.  rewrite y.
  apply used_nodes_preserved_refl.  intro y.  rewrite y.
  elim (option_sum _ (MapGet3 ad (fst (snd cfg)) l r x)).  intro y0.  elim y0.
  clear y0.  intros node y0.  rewrite y0.  apply used_nodes_preserved_refl.  intro y0.
  rewrite y0.  apply BDDalloc_preserves_used_nodes.  assumption.  assumption.
  assumption.
Qed.

Lemma BDDmake_node_OK : config_node_OK (fst BDDmake) (snd BDDmake).
Proof.
  unfold BDDmake in |- *.  elim (sumbool_of_bool (Neqb l r)).  intro y.  rewrite y.
  unfold config_node_OK in |- *.  apply used_node'_OK_bs with (ul := ul).
  exact (proj1 cfg_OK).  assumption.  assumption.  intro y.  rewrite y.
  elim (option_sum _ (MapGet3 ad (fst (snd cfg)) l r x)).  intro y0.  elim y0.
  clear y0.  intros x0 y0.  rewrite y0.  right.  right.  unfold in_dom in |- *.  simpl in |- *.
  rewrite (proj1 (proj1 (proj2 cfg_OK) x l r x0) y0).  reflexivity.
  intro y0.  rewrite y0.  apply BDDalloc_node_OK.  assumption.  assumption.  
  assumption.  assumption.  assumption.  assumption.  assumption.  assumption.
Qed.

Lemma BDDmake_bool_fun :
 bool_fun_eq (bool_fun_of_BDD (fst BDDmake) (snd BDDmake))
   (bool_fun_if x (bool_fun_of_BDD cfg r) (bool_fun_of_BDD cfg l)).
Proof.
  unfold BDDmake in |- *.  elim (sumbool_of_bool (Neqb l r)).  intro y.  rewrite y.
  simpl in |- *.  apply bool_fun_eq_sym.  apply bool_fun_if_eq_2.
  rewrite (Neqb_complete _ _ y).  apply bool_fun_eq_refl.  intro y.  rewrite y.
  elim (option_sum _ (MapGet3 ad (fst (snd cfg)) l r x)).  intro y0.  elim y0.
  clear y0.  intros x0 y0.  rewrite y0.  unfold bool_fun_of_BDD in |- *.  simpl in |- *.
  apply bool_fun_of_BDD_bs_int.  exact (proj1 cfg_OK).  
  exact (proj1 (proj1 (proj2 cfg_OK) x l r x0) y0).  intro y0.
  rewrite y0.  unfold bool_fun_of_BDD in |- *.  simpl in |- *.
  apply
   bool_fun_eq_trans
    with
      (bool_fun_if x
         (bool_fun_of_BDD_bs (fst (fst (BDDalloc gc cfg x l r ul))) r)
         (bool_fun_of_BDD_bs (fst (fst (BDDalloc gc cfg x l r ul))) l)).
  apply bool_fun_of_BDD_bs_int.  apply BDDalloc_keeps_state_OK.  assumption.
  assumption.  assumption.  assumption.  assumption.  assumption.  assumption.
  assumption.  apply BDDallocGet.  apply bool_fun_if_preserves_eq.
  apply used_nodes_preserved'_bs_bool_fun with (ul := ul).  exact (proj1 cfg_OK).
  apply BDDalloc_keeps_state_OK.  assumption.  assumption.  assumption.  
  assumption.  assumption.  assumption.  assumption.  assumption.
  fold (used_nodes_preserved cfg (fst (BDDalloc gc cfg x l r ul)) ul) in |- *.
  apply BDDalloc_preserves_used_nodes.  assumption.  assumption.  assumption.
  assumption.  assumption.  apply used_nodes_preserved'_bs_bool_fun with (ul := ul). 
  exact (proj1 cfg_OK).  apply BDDalloc_keeps_state_OK.  assumption.
  assumption.  assumption.  assumption.  assumption.  assumption.  assumption.  
  assumption.
  fold (used_nodes_preserved cfg (fst (BDDalloc gc cfg x l r ul)) ul) in |- *.
  apply BDDalloc_preserves_used_nodes.  assumption.  assumption.  assumption.
  assumption.  assumption.
Qed.

Lemma BDDmake_node_height_eq :
 Neqb l r = false ->
 Neqb (node_height (fst BDDmake) (snd BDDmake)) (ad_S x) = true.
Proof.
  intro.  unfold BDDmake in |- *.  rewrite H.
  elim (option_sum _ (MapGet3 ad (fst (snd cfg)) l r x)).  intro y.  elim y.
  clear y.  intros x0 y.  rewrite y.  simpl in |- *.  unfold node_height in |- *.  unfold bs_node_height in |- *.
  rewrite (proj1 (proj1 (proj2 cfg_OK) x l r x0) y).
  apply Neqb_correct.  intro y.  rewrite y.  unfold node_height in |- *.  unfold bs_node_height in |- *.
  rewrite (BDDallocGet gc cfg x l r ul).  apply Neqb_correct.
Qed.

Lemma BDDmake_node_height_eq_1 :
 Neqb l r = true ->
 Neqb (node_height (fst BDDmake) (snd BDDmake)) (node_height cfg l) = true.
Proof.
  intro.  unfold BDDmake in |- *.  rewrite H.  apply Neqb_correct.
Qed.

Lemma BDDmake_node_height_le :
 Nleb (node_height (fst BDDmake) (snd BDDmake)) (ad_S x) = true.
Proof.
  elim (sumbool_of_bool (Neqb l r)).  intro y.
  rewrite
   (Neqb_complete (node_height (fst BDDmake) (snd BDDmake))
      (node_height cfg l)).
  unfold node_height in |- *.  unfold bs_node_height in |- *.  elim (option_sum _ (MapGet _ (fst cfg) l)).
  intro y0.  elim y0.  intro x0.  elim x0.  intro y1.  intro y2.  elim y2.  intros y3 y4 y5.
  rewrite y5.  unfold Nleb in |- *.  apply leb_correct.  apply lt_le_weak.
  apply BDDcompare_lt.  rewrite <- (ad_S_compare y1 x).
  apply xl_lt_x with (ll := y3) (rl := y4).  assumption.  intro y0.  rewrite y0.
  reflexivity.  apply BDDmake_node_height_eq_1.  assumption.  intro y.
  rewrite (Neqb_complete _ _ (BDDmake_node_height_eq y)).  apply Nleb_refl.
Qed.

End BDD_make.
