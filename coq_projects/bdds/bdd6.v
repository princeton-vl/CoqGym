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
From IntMap Require Import Allmaps.
Require Import Wf_nat.

Require Import BDDvar_ad_nat.
Require Import bdd1.
Require Import bdd2.
Require Import bdd3.
Require Import bdd4.
Require Import bdd5_1.
Require Import bdd5_2.

Lemma nodes_preserved_trans :
 forall cfg1 cfg2 cfg3 : BDDconfig,
 nodes_preserved cfg1 cfg2 ->
 nodes_preserved cfg2 cfg3 -> nodes_preserved cfg1 cfg3.
Proof.
unfold nodes_preserved in |- *; intros.  apply H0.  apply H.  assumption.
Qed.

Lemma nodes_preserved_var :
 forall (cfg cfg' : BDDconfig) (node : ad),
 nodes_preserved cfg cfg' ->
 is_internal_node cfg node -> var cfg' node = var cfg node.
Proof.
  unfold nodes_preserved, is_internal_node in |- *.  intros.  inversion H0.  inversion H1.
  inversion H2.  unfold var in |- *.  rewrite H3.  rewrite (H x x0 x1 node H3).  reflexivity.
Qed.

Lemma nodes_preserved_var_1 :
 forall (cfg cfg' : BDDconfig) (node : ad),
 BDDconfig_OK cfg ->
 BDDconfig_OK cfg' ->
 nodes_preserved cfg cfg' ->
 config_node_OK cfg node -> var cfg' node = var cfg node.
Proof.
  intros.  unfold var in |- *.  elim H2; intro.  rewrite H3.  rewrite (config_OK_zero cfg H).
  rewrite (config_OK_zero cfg' H0).  reflexivity.  elim H3; intro.  rewrite H4.
  rewrite (config_OK_one cfg H).  rewrite (config_OK_one cfg' H0).  reflexivity.
  cut (is_internal_node cfg node).  intro.  inversion H5.  inversion H6.  inversion H7.
  rewrite H8.  unfold nodes_preserved in H1.  rewrite (H1 x x0 x1 node H8).
  reflexivity.  apply in_dom_is_internal.  assumption.
Qed.

Lemma nodes_preserved_3 :
 forall (cfg cfg' : BDDconfig) (node : ad),
 BDDconfig_OK cfg ->
 BDDconfig_OK cfg' ->
 nodes_preserved cfg cfg' ->
 config_node_OK cfg node ->
 bool_fun_eq (bool_fun_of_BDD cfg' node) (bool_fun_of_BDD cfg node).
Proof.
  intros cfg cfg' node H H0 H1 H2.  apply bool_fun_preservation.  assumption.  assumption.  unfold nodes_preserved in H1.
  intros x l r a H3.  apply H1.  assumption.  assumption.
Qed.

Lemma bool_fun_or_preserves_eq :
 forall bf1 bf2 bf1' bf2' : bool_fun,
 bool_fun_eq bf1 bf1' ->
 bool_fun_eq bf2 bf2' ->
 bool_fun_eq (bool_fun_or bf1 bf2) (bool_fun_or bf1' bf2').
Proof.
  unfold bool_fun_eq in |- *.  intros bf1 bf2 bf1' bf2' H H0 vb.  unfold bool_fun_or in |- *.  unfold bool_fun_eval in |- *.
  unfold bool_fun_eval in H, H0.  rewrite (H vb).  rewrite (H0 vb).  reflexivity.
Qed.

Definition BDDvar_le := Nleb.
Definition BDDvar_max (x y : BDDvar) := if BDDvar_le x y then y else x.

Lemma BDDvar_max_comm : forall x y : BDDvar, BDDvar_max x y = BDDvar_max y x.
Proof.
  unfold BDDvar_max in |- *.  unfold BDDvar_le in |- *.  intros x y.  elim (sumbool_of_bool (Nleb x y)).
  intro y0.  rewrite y0.  elim (sumbool_of_bool (Nleb y x)).  intro y1.  rewrite y1.
  apply Nleb_antisym.  assumption.  assumption.  intro y1.  rewrite y1.  reflexivity.
  intro y0.  rewrite y0.  elim (sumbool_of_bool (Nleb y x)).  intro y1.  rewrite y1.
  reflexivity.  intro y1.  rewrite y1.  apply Nleb_antisym.  apply Nltb_leb_weak.
  assumption.  apply Nltb_leb_weak.  assumption.
Qed.

Lemma BDDvar_max_lemma_1 :
 forall x y z : BDDvar,
 BDDcompare x y = Datatypes.Lt ->
 BDDcompare (BDDvar_max x N0) (BDDvar_max y z) = Datatypes.Lt.
Proof.
  intros x y z.  rewrite (BDDvar_max_comm x N0).  unfold BDDvar_max in |- *.  simpl in |- *.
  intro H.  unfold BDDvar_le in |- *.  unfold Nleb in |- *.  elim (sumbool_of_bool (leb (nat_of_N y) (nat_of_N z))).
  intro y0.  rewrite y0.  apply BDDlt_compare.  apply lt_le_trans with (m := nat_of_N y).
  apply BDDcompare_lt.  assumption.  apply leb_complete.  assumption.  intro y0.
  rewrite y0.  assumption.  
Qed.

Lemma BDDvar_le_z : forall x : BDDvar, BDDvar_le N0 x = true.
Proof.
  intro x.  unfold BDDvar_le in |- *.  unfold Nleb in |- *.  simpl in |- *.  reflexivity.
Qed.

Lemma BDDvar_le_compare :
 forall x y : BDDvar, BDDcompare x y = Datatypes.Lt -> BDDvar_le x y = true.
Proof.
  intros x y H.  unfold BDDvar_le in |- *.  unfold Nleb in |- *.  apply leb_correct.  apply lt_le_weak.
  apply BDDcompare_lt.  assumption.
Qed.

Lemma BDDcompare_max_1_2 :
 forall x1 x2 y1 y2 : BDDvar,
 BDDcompare x1 x2 = Datatypes.Lt ->
 BDDcompare y1 y2 = Datatypes.Lt ->
 BDDcompare (BDDvar_max x1 y1) (BDDvar_max x2 y2) = Datatypes.Lt.
Proof.
  unfold BDDvar_max in |- *.  unfold BDDvar_le in |- *.  unfold Nleb in |- *.  intros x1 x2 y1 y2 H H0.  elim (sumbool_of_bool (leb (nat_of_N x1) (nat_of_N y1))).
  intro y.  rewrite y.  elim (sumbool_of_bool (leb (nat_of_N x2) (nat_of_N y2))).
  intro y0.  rewrite y0.  assumption.  intro y0.  rewrite y0.  apply BDDlt_compare.
  apply lt_trans with (m := nat_of_N y2).  apply BDDcompare_lt.  assumption.
  apply leb_complete_conv.  assumption.  intro y.  rewrite y.  elim (sumbool_of_bool (leb (nat_of_N x2) (nat_of_N y2))).
  intro y0.  rewrite y0.  apply BDDlt_compare.  apply lt_le_trans with (m := nat_of_N x2).
  apply BDDcompare_lt.  assumption.  apply leb_complete.  assumption.
  intro y0.  rewrite y0.  assumption.
Qed.

Lemma BDDcompare_z_nz :
 forall x : BDDvar, x <> N0 -> BDDcompare N0 x = Datatypes.Lt.
Proof.
  simple induction x.  intros H.  absurd (N0 = N0).  assumption.  reflexivity.  simpl in |- *.  reflexivity.
Qed.

Lemma BDDvar_max_x_x : forall x : BDDvar, BDDvar_max x x = x.
Proof.
  unfold BDDvar_max in |- *.  unfold BDDvar_le in |- *.  intro x.  rewrite (Nleb_refl x).  reflexivity.
Qed.

Lemma BDDvar_ordered_high_1 :
 forall (cfg : BDDconfig) (node1 node2 : ad),
 BDDconfig_OK cfg ->
 is_internal_node cfg node1 ->
 is_internal_node cfg node2 ->
 is_internal_node cfg (high cfg node1) \/
 is_internal_node cfg (high cfg node2) ->
 BDDcompare
   (BDDvar_max (var cfg (high cfg node1)) (var cfg (high cfg node2)))
   (BDDvar_max (var cfg node1) (var cfg node2)) = Datatypes.Lt.
Proof.
  intros cfg node1 node2 H H0 H1 H2.  cut (config_node_OK cfg (high cfg node1)).  cut (config_node_OK cfg (high cfg node2)).
  intros H3 H4.  elim H2; intro.  cut (BDDcompare (var cfg (high cfg node1)) (var cfg node1) = Datatypes.Lt).
  intro H6.  elim H3; intro.  rewrite H7.  unfold var at 2 in |- *.  rewrite (config_OK_zero cfg H).
  unfold BDDzero in |- *.  apply BDDvar_max_lemma_1.  assumption.  elim H7; intro.
  rewrite H8.  unfold var at 2 in |- *.  rewrite (config_OK_one cfg H).  unfold BDDzero in |- *.
  apply BDDvar_max_lemma_1.  assumption.  apply BDDcompare_max_1_2.  assumption.
  apply BDDvar_ordered_high.  assumption.  assumption.  apply in_dom_is_internal.
  assumption.  apply BDDvar_ordered_high.  assumption.  assumption.  assumption.
  elim H4; intro.  rewrite H6.  unfold var at 1 in |- *.  rewrite (config_OK_zero cfg H).
  unfold BDDzero in |- *.  rewrite (BDDvar_max_comm N0 (var cfg (high cfg node2))).
  rewrite (BDDvar_max_comm (var cfg node1) (var cfg node2)).  apply BDDvar_max_lemma_1.
  apply BDDvar_ordered_high.  assumption.  assumption.  assumption.  elim H6; intro.
  rewrite H7.  unfold var at 1 in |- *.  rewrite (config_OK_one cfg H).  unfold BDDzero in |- *.
  rewrite (BDDvar_max_comm N0 (var cfg (high cfg node2))).  rewrite (BDDvar_max_comm (var cfg node1) (var cfg node2)).
  apply BDDvar_max_lemma_1.  apply BDDvar_ordered_high.  assumption.  assumption.
  assumption.  apply BDDcompare_max_1_2.  apply BDDvar_ordered_high.  assumption.  
  assumption.  apply in_dom_is_internal; assumption.  apply BDDvar_ordered_high.
  assumption.  assumption.  assumption.  apply high_OK.  assumption.  assumption.
  apply high_OK.  assumption.  assumption.
Qed.

Lemma BDDvar_ordered_low_1 :
 forall (cfg : BDDconfig) (node1 node2 : ad),
 BDDconfig_OK cfg ->
 is_internal_node cfg node1 ->
 is_internal_node cfg node2 ->
 is_internal_node cfg (low cfg node1) \/ is_internal_node cfg (low cfg node2) ->
 BDDcompare (BDDvar_max (var cfg (low cfg node1)) (var cfg (low cfg node2)))
   (BDDvar_max (var cfg node1) (var cfg node2)) = Datatypes.Lt.
Proof.
 intros cfg node1 node2 H H0 H1 H2.  cut (config_node_OK cfg (low cfg node1)).  cut (config_node_OK cfg (low cfg node2)).
  intros H3 H4.  elim H2; intro.  cut (BDDcompare (var cfg (low cfg node1)) (var cfg node1) = Datatypes.Lt).
  intro H6.  elim H3; intro.  rewrite H7.  unfold var at 2 in |- *.  rewrite (config_OK_zero cfg H).
  unfold BDDzero in |- *.  apply BDDvar_max_lemma_1.  assumption.  elim H7; intro.
  rewrite H8.  unfold var at 2 in |- *.  rewrite (config_OK_one cfg H).  unfold BDDzero in |- *.
  apply BDDvar_max_lemma_1.  assumption.  apply BDDcompare_max_1_2.  assumption.
  apply BDDvar_ordered_low.  assumption.  assumption.  apply in_dom_is_internal.
  assumption.  apply BDDvar_ordered_low.  assumption.  assumption.  assumption.
  elim H4; intro.  rewrite H6.  unfold var at 1 in |- *.  rewrite (config_OK_zero cfg H).
  unfold BDDzero in |- *.  rewrite (BDDvar_max_comm N0 (var cfg (low cfg node2))).
  rewrite (BDDvar_max_comm (var cfg node1) (var cfg node2)).  apply BDDvar_max_lemma_1.
  apply BDDvar_ordered_low.  assumption.  assumption.  assumption.  elim H6; intro.
  rewrite H7.  unfold var at 1 in |- *.  rewrite (config_OK_one cfg H).  unfold BDDzero in |- *.
  rewrite (BDDvar_max_comm N0 (var cfg (low cfg node2))).  rewrite (BDDvar_max_comm (var cfg node1) (var cfg node2)).
  apply BDDvar_max_lemma_1.  apply BDDvar_ordered_low.  assumption.  assumption.
  assumption.  apply BDDcompare_max_1_2.  apply BDDvar_ordered_low.  assumption.
  assumption.  apply in_dom_is_internal; assumption.  apply BDDvar_ordered_low.
  assumption.  assumption.  assumption.  apply low_OK.  assumption.  assumption.
  apply low_OK.  assumption.  assumption.
Qed.

Lemma BDDvar_ordered_high_2 :
 forall (cfg : BDDconfig) (node1 node2 : ad),
 BDDconfig_OK cfg ->
 is_internal_node cfg node1 ->
 is_internal_node cfg node2 ->
 BDDcompare (var cfg node1) (var cfg node2) = Datatypes.Lt ->
 BDDcompare (BDDvar_max (var cfg node1) (var cfg (high cfg node2)))
   (var cfg node2) = Datatypes.Lt. 
Proof.
  intros cfg node1 node2 H H0 H1 H2.  cut (var cfg node2 = BDDvar_max (var cfg node2) (var cfg node2)).
  intro H3.  rewrite H3.  apply BDDcompare_max_1_2.  assumption.  cut (config_node_OK cfg (high cfg node2)).
  intro H4.  elim H4; intro.  rewrite H5.  unfold var at 1 in |- *.  rewrite (config_OK_zero cfg H).
  unfold BDDzero in |- *.  apply BDDcompare_z_nz.  apply INFERIEUR_neq_O with (x := var cfg node1).
  assumption.  elim H5; intro.  rewrite H6.  unfold var at 1 in |- *.  rewrite (config_OK_one cfg H).
  unfold BDDzero in |- *.  apply BDDcompare_z_nz.  apply INFERIEUR_neq_O with (x := var cfg node1).
  assumption.  apply BDDvar_ordered_high.  assumption.  assumption.  apply in_dom_is_internal.
  assumption.  apply high_OK.  assumption.  assumption.  rewrite (BDDvar_max_x_x (var cfg node2)).
  reflexivity.
Qed.

Lemma BDDvar_ordered_low_2 :
 forall (cfg : BDDconfig) (node1 node2 : ad),
 BDDconfig_OK cfg ->
 is_internal_node cfg node1 ->
 is_internal_node cfg node2 ->
 BDDcompare (var cfg node1) (var cfg node2) = Datatypes.Lt ->
 BDDcompare (BDDvar_max (var cfg node1) (var cfg (low cfg node2)))
   (var cfg node2) = Datatypes.Lt.
Proof.
  intros cfg node1 node2 H H0 H1 H2.  cut (var cfg node2 = BDDvar_max (var cfg node2) (var cfg node2)).
  intro H3.  rewrite H3.  apply BDDcompare_max_1_2.  assumption.  cut (config_node_OK cfg (low cfg node2)).
  intro H4.  elim H4; intro.  rewrite H5.  unfold var at 1 in |- *.  rewrite (config_OK_zero cfg H).
  unfold BDDzero in |- *.  apply BDDcompare_z_nz.  apply INFERIEUR_neq_O with (x := var cfg node1).
  assumption.  elim H5; intro.  rewrite H6.  unfold var at 1 in |- *.  rewrite (config_OK_one cfg H).
  unfold BDDzero in |- *.  apply BDDcompare_z_nz.  apply INFERIEUR_neq_O with (x := var cfg node1).
  assumption.  apply BDDvar_ordered_low.  assumption.  assumption.  apply in_dom_is_internal.
  assumption.  apply low_OK.  assumption.  assumption.  rewrite (BDDvar_max_x_x (var cfg node2)).
  reflexivity.
Qed.

Lemma BDDvar_ordered_high_3 :
 forall (cfg : BDDconfig) (node1 node2 : ad),
 BDDconfig_OK cfg ->
 is_internal_node cfg node1 ->
 is_internal_node cfg node2 ->
 BDDcompare (var cfg node2) (var cfg node1) = Datatypes.Lt ->
 BDDcompare (BDDvar_max (var cfg (high cfg node1)) (var cfg node2))
   (var cfg node1) = Datatypes.Lt.
Proof.
  intros cfg node1 node2 H H0 H1 H2.  rewrite (BDDvar_max_comm (var cfg (high cfg node1)) (var cfg node2)).
  apply BDDvar_ordered_high_2.  assumption.  assumption.  assumption.  assumption.
Qed.

Lemma BDDvar_ordered_low_3 :
 forall (cfg : BDDconfig) (node1 node2 : ad),
 BDDconfig_OK cfg ->
 is_internal_node cfg node1 ->
 is_internal_node cfg node2 ->
 BDDcompare (var cfg node2) (var cfg node1) = Datatypes.Lt ->
 BDDcompare (BDDvar_max (var cfg (low cfg node1)) (var cfg node2))
   (var cfg node1) = Datatypes.Lt.
Proof.
  intros cfg node1 node2 H H0 H1 H2.  rewrite (BDDvar_max_comm (var cfg (low cfg node1)) (var cfg node2)).
  apply BDDvar_ordered_low_2.  assumption.  assumption.  assumption.  assumption.
Qed.

Lemma lt_max_nat_of_N :
 forall x y z : BDDvar,
 BDDcompare (BDDvar_max x y) z = Datatypes.Lt ->
 max (nat_of_N x) (nat_of_N y) < nat_of_N z.
Proof.
  unfold BDDvar_max in |- *.  unfold BDDvar_le in |- *.  intros x y z.  elim (sumbool_of_bool (Nleb x y)).
  intro y0.  rewrite y0.  intro H.  unfold max in |- *.  elim (sumbool_of_bool (leb (nat_of_N x) (nat_of_N y))).
  intro y1.  rewrite y1.  apply BDDcompare_lt.  assumption.  intro y1.  rewrite y1.
  apply le_lt_trans with (m := nat_of_N y).  apply leb_complete.  exact y0.  
  apply BDDcompare_lt.  assumption.  intro y0.  rewrite y0.  intro H.  unfold max in |- *.
  elim (sumbool_of_bool (leb (nat_of_N x) (nat_of_N y))).  intro y1.  cut (Nleb x y = true).
  intro H0.  rewrite H0 in y0.  discriminate.  exact y1.  intro y1.  rewrite y1.
  apply BDDcompare_lt.  assumption.
Qed.

Lemma le_nat_of_N_max :
 forall x y z : BDDvar,
 BDDvar_le x (BDDvar_max y z) = true ->
 nat_of_N x <= max (nat_of_N y) (nat_of_N z).
Proof.
  unfold BDDvar_max in |- *.  unfold BDDvar_le in |- *.  intros x y z.  elim (sumbool_of_bool (Nleb y z)).
  intro y0.  rewrite y0.  intro H.  unfold max in |- *.  elim (sumbool_of_bool (leb (nat_of_N y) (nat_of_N z))).
  intro y1.  rewrite y1.  apply leb_complete.  assumption.  unfold Nleb in y0.
  rewrite y0.  intro y1.  discriminate.  intro y0.  rewrite y0.  intro H.  unfold max in |- *.
  unfold Nleb in y0, H.  rewrite y0.  apply leb_complete.  assumption.
Qed.

Definition bool_fun_if (x : BDDvar) (bf bf' : bool_fun) : bool_fun :=
  fun vb : var_binding => ifb (vb x) (bf vb) (bf' vb).
  
Lemma nodes_preserved_internal :
 forall (cfg cfg' : BDDconfig) (node : ad),
 BDDconfig_OK cfg ->
 BDDconfig_OK cfg' ->
 config_node_OK cfg node ->
 is_internal_node cfg' node -> is_internal_node cfg node.
Proof.
  intros cfg cfg' node H H0 H1 H2.  inversion H2.  inversion H3.  inversion H4.  elim H1.  intro H6.  rewrite H6 in H5.
  rewrite (config_OK_zero cfg' H0) in H5.  discriminate.  intro H6.  elim H6; intro.
  rewrite H7 in H5.  rewrite (config_OK_one cfg' H0) in H5.  discriminate.
  apply in_dom_is_internal.  assumption.
Qed.

Lemma bool_fun_if_preserves_eq :
 forall (x : BDDvar) (bf1 bf2 bf1' bf2' : bool_fun),
 bool_fun_eq bf1 bf1' ->
 bool_fun_eq bf2 bf2' ->
 bool_fun_eq (bool_fun_if x bf1 bf2) (bool_fun_if x bf1' bf2').
Proof.
  unfold bool_fun_eq, bool_fun_if in |- *.  unfold bool_fun_eval in |- *.  intros x bf1 bf2 bf1' bf2' H H0 vb.  rewrite (H vb).
rewrite (H0 vb).  reflexivity.
Qed.

Lemma BDDmake_var_order :
 forall (cfg : BDDconfig) (l r : ad) (x : BDDvar),
 BDDconfig_OK cfg ->
 config_node_OK cfg l ->
 config_node_OK cfg r ->
 (is_internal_node cfg l -> BDDcompare (var cfg l) x = Datatypes.Lt) ->
 (is_internal_node cfg r -> BDDcompare (var cfg r) x = Datatypes.Lt) ->
 BDDvar_le (var (fst (BDDmake cfg x l r)) (snd (BDDmake cfg x l r))) x = true. 
Proof.
  intros cfg l r x H H0 H1 H2 H3.  cut
   (forall (xl : BDDvar) (ll rl : ad),
    MapGet _ (fst cfg) l = Some (xl, (ll, rl)) ->
    BDDcompare xl x = Datatypes.Lt).
  cut
   (forall (xr : BDDvar) (lr rr : ad),
    MapGet _ (fst cfg) r = Some (xr, (lr, rr)) ->
    BDDcompare xr x = Datatypes.Lt).
  intros H4 H5.  cut (node_OK (fst cfg) l).  cut (node_OK (fst cfg) r).  intros H6 H7.
  cut
   (BDDconfig_OK (fst (BDDmake cfg x l r)) /\
    (Neqb l r = false ->
     MapGet _ (fst (fst (BDDmake cfg x l r))) (snd (BDDmake cfg x l r)) =
     Some (x, (l, r))) /\
    (Neqb l r = true -> snd (BDDmake cfg x l r) = l) /\
    (forall (a l' r' : ad) (x' : BDDvar),
     (MapGet _ (fst (fst (BDDmake cfg x l r))) a = Some (x', (l', r')) ->
      MapGet _ (fst cfg) a = Some (x', (l', r')) \/
      snd (BDDmake cfg x l r) = a) /\
     (MapGet _ (fst cfg) a = Some (x', (l', r')) ->
      MapGet _ (fst (fst (BDDmake cfg x l r))) a = Some (x', (l', r')))) /\
    node_OK (fst (fst (BDDmake cfg x l r))) (snd (BDDmake cfg x l r))).
  intros H8.  elim H8; clear H8; intros.  elim H9; clear H9; intros.  elim H10; clear H10; intros.
  elim H11; clear H11; intros.  elim (sumbool_of_bool (Neqb l r)).  intro y.
  rewrite (H10 y).  unfold var in |- *.  elim (option_sum _ (MapGet _ (fst cfg) l)); intro y0.
  elim y0.  intro x0.  elim x0.  intro y1; intro y2.  elim y2.  intros y3 y4 y5.  rewrite (proj2 (H11 l y3 y4 y1) y5).
  rewrite y5 in H5.  cut (BDDcompare y1 x = Datatypes.Lt).  intro H13.  apply BDDvar_le_compare.
  assumption.  apply H5 with (ll := y3) (rl := y4).  reflexivity.  elim H7; intro.
  rewrite H13.  rewrite H13 in H8.  rewrite (config_OK_zero (fst (BDDmake cfg x BDDzero r)) H8).
  unfold BDDzero in |- *.  apply BDDvar_le_z.  elim H13.  intro H14.  rewrite H14.  rewrite H14 in H8.
  rewrite (config_OK_one (fst (BDDmake cfg x BDDone r)) H8).  unfold BDDzero in |- *.
  apply BDDvar_le_z.  intro H14.  unfold in_dom in H14.  rewrite y0 in H14.  discriminate.
  intro y.  unfold var in |- *.  rewrite (H9 y).  unfold BDDvar_le in |- *.  unfold Nleb in |- *.  apply leb_correct.
  apply le_n.  apply BDDmake_semantics.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  assumption.  intros xr lr rr H4.  unfold is_internal_node in H3.
  unfold var in H3.  rewrite H4 in H3.  apply H3.  split with xr.  split with lr.
  split with rr.  reflexivity.  intros xl ll rl H4.  unfold is_internal_node in H2.  unfold var in H2.
  rewrite H4 in H2.  apply H2.  split with xl.  split with ll.  split with rl.
  reflexivity.
Qed.

Lemma BDDmake_bool_fun :
 forall (cfg : BDDconfig) (l r : ad) (x : BDDvar),
 BDDconfig_OK cfg ->
 config_node_OK cfg l ->
 config_node_OK cfg r ->
 (is_internal_node cfg l -> BDDcompare (var cfg l) x = Datatypes.Lt) ->
 (is_internal_node cfg r -> BDDcompare (var cfg r) x = Datatypes.Lt) ->
 bool_fun_eq
   (bool_fun_of_BDD (fst (BDDmake cfg x l r)) (snd (BDDmake cfg x l r)))
   (bool_fun_if x (bool_fun_of_BDD cfg r) (bool_fun_of_BDD cfg l)).
Proof.
  intros cfg l r x H H0 H1 H2 H3.  cut
   (forall (xl : BDDvar) (ll rl : ad),
    MapGet _ (fst cfg) l = Some (xl, (ll, rl)) ->
    BDDcompare xl x = Datatypes.Lt).
  cut
   (forall (xr : BDDvar) (lr rr : ad),
    MapGet _ (fst cfg) r = Some (xr, (lr, rr)) ->
    BDDcompare xr x = Datatypes.Lt).
  intros H4 H5.  cut (node_OK (fst cfg) l).  cut (node_OK (fst cfg) r).  intros H6 H7.
  cut
   (BDDconfig_OK (fst (BDDmake cfg x l r)) /\
    (Neqb l r = false ->
     MapGet _ (fst (fst (BDDmake cfg x l r))) (snd (BDDmake cfg x l r)) =
     Some (x, (l, r))) /\
    (Neqb l r = true -> snd (BDDmake cfg x l r) = l) /\
    (forall (a l' r' : ad) (x' : BDDvar),
     (MapGet _ (fst (fst (BDDmake cfg x l r))) a = Some (x', (l', r')) ->
      MapGet _ (fst cfg) a = Some (x', (l', r')) \/
      snd (BDDmake cfg x l r) = a) /\
     (MapGet _ (fst cfg) a = Some (x', (l', r')) ->
      MapGet _ (fst (fst (BDDmake cfg x l r))) a = Some (x', (l', r')))) /\
    node_OK (fst (fst (BDDmake cfg x l r))) (snd (BDDmake cfg x l r))).
  intros H8.  elim H8; clear H8; intros.  elim H9; clear H9; intros.  elim H10; clear H10; intros.
  elim H11; clear H11; intros.  elim (sumbool_of_bool (Neqb l r)).  intro y.
  rewrite (H10 y).  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg l).
  apply bool_fun_preservation.  assumption.  assumption.  intros x0 l0 r0 a H13.  exact (proj2 (H11 a l0 r0 x0) H13).
  assumption.  cut (l = r).  intro H13.  rewrite <- H13.  unfold bool_fun_if in |- *.  unfold bool_fun_eq in |- *.
  unfold bool_fun_eval in |- *.  intro vb.  elim (vb x).  simpl in |- *.  reflexivity.  simpl in |- *.  reflexivity.  
  apply Neqb_complete.  assumption.  intro y.  cut (is_internal_node (fst (BDDmake cfg x l r)) (snd (BDDmake cfg x l r))).
  intro H13.  rewrite
   (proj2 (proj2 (bool_fun_of_BDD_semantics (fst (BDDmake cfg x l r)) H8))
      (snd (BDDmake cfg x l r)) H13).
  unfold bool_fun_eq in |- *.  intro vb.  unfold bool_fun_eval in |- *.  unfold var in |- *.  rewrite (H9 y).
  unfold bool_fun_if in |- *.  unfold ifb in |- *.  unfold high, low in |- *.  rewrite (H9 y).
  cut
   (bool_fun_eq (bool_fun_of_BDD (fst (BDDmake cfg x l r)) r)
      (bool_fun_of_BDD cfg r)).
  cut
   (bool_fun_eq (bool_fun_of_BDD (fst (BDDmake cfg x l r)) l)
      (bool_fun_of_BDD cfg l)).
  intros H14 H15.  unfold bool_fun_eq in H14, H15.  unfold bool_fun_eval in H14, H15.  rewrite (H14 vb).
  rewrite (H15 vb).  reflexivity.  apply bool_fun_preservation.  assumption.
  assumption.  intros x0 l0 r0 a H14.  exact (proj2 (H11 a l0 r0 x0) H14).  assumption.
  apply bool_fun_preservation.  assumption.  intros.  assumption.  intros x0 l0 r0 a H14.
  exact (proj2 (H11 a l0 r0 x0) H14).  assumption.  split with x.  split with l.
  split with r.  apply H9.  assumption.  apply BDDmake_semantics.  assumption.  
  assumption.  assumption.  assumption.  assumption.  assumption.  assumption.
  intros xr lr rr H4.  intros.  unfold is_internal_node in H3.  unfold var in H3.  rewrite H4 in H3.
  apply H3.  split with xr.  split with lr.  split with rr.  reflexivity.  intros xl ll rl H4.
  unfold is_internal_node in H2.  unfold var in H2.  rewrite H4 in H2.  apply H2.
  split with xl.  split with ll.  split with rl.  reflexivity.  
Qed.

Lemma bool_fun_or_commute :
 forall bf bf' : bool_fun,
 bool_fun_eq (bool_fun_or bf bf') (bool_fun_or bf' bf).
Proof.
  unfold bool_fun_eq, bool_fun_or in |- *.  unfold bool_fun_eval, bool_fun_or in |- *.  intros bf bf' vb.
  apply orb_comm.
Qed.

Lemma bool_fun_or_zero :
 forall bf : bool_fun, bool_fun_eq (bool_fun_or bf bool_fun_zero) bf.
Proof.
  unfold bool_fun_eq, bool_fun_zero in |- *.  unfold bool_fun_or in |- *.  unfold bool_fun_eval in |- *. 
  intros bf vb.  elim (bf vb).  simpl in |- *.  reflexivity.  simpl in |- *.  reflexivity.
Qed.

Lemma bool_fun_or_one :
 forall bf : bool_fun, bool_fun_eq (bool_fun_or bf bool_fun_one) bool_fun_one.
Proof.
  unfold bool_fun_eq, bool_fun_or, bool_fun_one in |- *.  unfold bool_fun_eval in |- *.  intros bf vb.
  elim (bf vb).  simpl in |- *.  reflexivity.  simpl in |- *.  reflexivity.
Qed.

Lemma bool_fun_if_lemma_1 :
 forall (x : BDDvar) (bfl1 bfl2 bfr1 bfr2 : bool_fun),
 bool_fun_eq (bool_fun_if x (bool_fun_or bfr1 bfr2) (bool_fun_or bfl1 bfl2))
   (bool_fun_or (bool_fun_if x bfr1 bfl1) (bool_fun_if x bfr2 bfl2)).
Proof.
  unfold bool_fun_eq, bool_fun_or, bool_fun_if in |- *.  unfold bool_fun_eval in |- *.  intros x bfl1 bfl2 bfr1 bfr2 vb.
  elim (vb x); simpl in |- *.  reflexivity.  reflexivity.
Qed.

Lemma bool_fun_if_lemma_3 :
 forall (x : BDDvar) (bf1 bfl2 bfr2 : bool_fun),
 bool_fun_eq (bool_fun_if x (bool_fun_or bf1 bfr2) (bool_fun_or bf1 bfl2))
   (bool_fun_or bf1 (bool_fun_if x bfr2 bfl2)).
Proof.
  unfold bool_fun_eq, bool_fun_or, bool_fun_if in |- *.  unfold bool_fun_eval in |- *.  intros x bf1 bfl2 bfr2 vb.
  elim (vb x); simpl in |- *.  reflexivity.  reflexivity.
Qed.

Lemma bool_fun_if_lemma_4 :
 forall (x : BDDvar) (bfl1 bfr1 bf2 : bool_fun),
 bool_fun_eq (bool_fun_if x (bool_fun_or bfr1 bf2) (bool_fun_or bfl1 bf2))
   (bool_fun_or (bool_fun_if x bfr1 bfl1) bf2).
Proof.
  unfold bool_fun_eq, bool_fun_or, bool_fun_if in |- *.  unfold bool_fun_eval in |- *.  intros x bfl1 bfr1 bf2 vb.
  elim (vb x); simpl in |- *.  reflexivity.  reflexivity.
Qed.

Lemma bool_fun_if_lemma_2 :
 forall (cfg : BDDconfig) (node : ad),
 BDDconfig_OK cfg ->
 is_internal_node cfg node ->
 bool_fun_eq (bool_fun_of_BDD cfg node)
   (bool_fun_if (var cfg node) (bool_fun_of_BDD cfg (high cfg node))
      (bool_fun_of_BDD cfg (low cfg node))).
Proof.
  intros cfg node H H0.  rewrite (proj2 (proj2 (bool_fun_of_BDD_semantics cfg H)) node H0).
  unfold bool_fun_eq in |- *.  unfold bool_fun_eval in |- *.  unfold bool_fun_if in |- *.  unfold ifb in |- *.
  reflexivity.
Qed.

(*
Lemma BDD_EGAL_complete : (x,y:BDDvar)
  (BDDcompare x y)=EGAL -> x=y.
Proof.
  Double Induction 1 2.  Reflexivity.  Simpl.  (Intros; Discriminate).  Simpl.
  (Intros; Discriminate).  Simpl.  Intros.  Cut p0=p.  Intro.  (Rewrite H0; Reflexivity).
  Apply compare_convert_EGAL.  Assumption.
Qed.
*)

Lemma BDD_EGAL_correct : forall x y : BDDvar, BDDcompare x x = Datatypes.Eq.
Proof.
  simple induction x.  reflexivity.  simpl in |- *.  intros x0 y.  apply Pcompare_refl.
Qed.

Lemma BDD_EGALsymm :
 forall x y : BDDvar,
 BDDcompare x y = Datatypes.Eq -> BDDcompare y x = Datatypes.Eq.
Proof.
  intros x y H.  cut (x = y).  intros H0.  rewrite H0.  apply BDD_EGAL_correct.  assumption.
  apply BDD_EGAL_complete.  assumption.
Qed.

Lemma BDDcompare_le_INFERIEUR_1 :
 forall x y z : BDDvar,
 BDDvar_le x y = true ->
 BDDcompare y z = Datatypes.Lt -> BDDcompare x z = Datatypes.Lt.
Proof.
  intros x y z H H0.  apply BDDlt_compare.  apply le_lt_trans with (m := nat_of_N y).  unfold BDDvar_le in H.
  unfold Nleb in H.  apply leb_complete; assumption.  apply BDDcompare_lt.
  assumption.
Qed.

Definition BDDor_memo := Map (Map ad).
Definition initBDDor_memo := newMap (Map ad).

Definition BDDor_memo_put (memo : BDDor_memo) (node1 node2 node : ad) :=
  let m1 :=
    match MapGet _ memo node1 with
    | Some y => y
    | None => newMap ad
    end in
  let m1' := MapPut _ m1 node2 node in MapPut _ memo node1 m1'.

Definition BDDor_memo_lookup (memo : BDDor_memo) (node1 node2 : ad) :=
  match MapGet _ memo node1 with
  | None => None
  | Some m1 =>
      match MapGet _ m1 node2 with
      | None => None
      | Some node => Some node
      end
  end. 

Definition BDDor_memo_OK (cfg : BDDconfig) (memo : BDDor_memo) :=
  forall node1 node2 node : ad,
  BDDor_memo_lookup memo node1 node2 = Some node ->
  config_node_OK cfg node1 /\
  config_node_OK cfg node2 /\
  config_node_OK cfg node /\
  BDDvar_le (var cfg node) (BDDvar_max (var cfg node1) (var cfg node2)) =
  true /\
  bool_fun_eq (bool_fun_of_BDD cfg node)
    (bool_fun_or (bool_fun_of_BDD cfg node1) (bool_fun_of_BDD cfg node2)).

Lemma BDDor_memo_lookup_semantics :
 forall (memo : BDDor_memo) (node1 node2 node node1' node2' : ad),
 BDDor_memo_lookup (BDDor_memo_put memo node1 node2 node) node1' node2' =
 (if Neqb node1 node1' && Neqb node2 node2'
  then Some node
  else BDDor_memo_lookup memo node1' node2').
Proof.
  intros memo node1 node2 node node1' node2'.  unfold BDDor_memo_lookup, BDDor_memo_put in |- *.  rewrite
   (MapPut_semantics (Map ad) memo node1
      (MapPut ad
         match MapGet (Map ad) memo node1 with
         | None => newMap ad
         | Some y => y
         end node2 node) node1').
  elim (sumbool_of_bool (Neqb node1 node1')); intro y.  rewrite y.
  rewrite
   (MapPut_semantics ad
      match MapGet (Map ad) memo node1 with
      | None => newMap ad
      | Some y => y
      end node2 node node2').
  elim (sumbool_of_bool (Neqb node2 node2')).  intro y0.  rewrite y0.  simpl in |- *.
  reflexivity.  intro y0.  rewrite y0.  simpl in |- *.  elim (option_sum _ (MapGet (Map ad) memo node1)).
  intro y1.  inversion y1.  rewrite H.  cut (node1 = node1').  intro H0.  rewrite <- H0.
  rewrite H.  reflexivity.  apply Neqb_complete; assumption.  intro y1.  rewrite y1.
  cut (node1 = node1').  intro H.  rewrite <- H.  rewrite y1.  simpl in |- *.  reflexivity.
  apply Neqb_complete; assumption.  rewrite y.  simpl in |- *.  reflexivity.
Qed.