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
Require Import bdd6.
Require Import bdd7.
Require Import BDDdummy_lemma_2.
Require Import BDDdummy_lemma_3.
Require Import BDDdummy_lemma_4.
Require Import bdd8.
Require Import bdd9.

Definition BDDneg (cfg : BDDconfig) (memo : BDDneg_memo) 
  (node : ad) :=
  match BDDneg_1_1 cfg memo node (S (nat_of_N (var cfg node))) with
  | ((cfg', node'), memo') => (cfg', (node', memo'))
  end.

Definition BDDor (cfg : BDDconfig) (memo : BDDor_memo) 
  (node1 node2 : ad) :=
  BDDor_1_1 cfg memo node1 node2
    (S (max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2)))).

Definition BDDand (cfg : BDDconfig) (negm : BDDneg_memo) 
  (orm : BDDor_memo) (node1 node2 : ad) :=
  match BDDneg cfg negm node1 with
  | (cfg', (node1', negm')) =>
      match BDDneg cfg' negm' node2 with
      | (cfg'', (node2', negm'')) =>
          match BDDor cfg'' orm node1' node2' with
          | (cfg''', (node, orm')) =>
              match BDDneg cfg''' negm'' node with
              | (cfg'''', (node', negm''')) =>
                  (cfg'''', (node', (negm''', orm')))
              end
          end
      end
  end.

Lemma nodes_preserved_orm_OK :
 forall (cfg cfg' : BDDconfig) (orm : BDDor_memo),
 BDDconfig_OK cfg ->
 BDDconfig_OK cfg' ->
 nodes_preserved cfg cfg' -> BDDor_memo_OK cfg orm -> BDDor_memo_OK cfg' orm.
Proof.
  intros.  unfold BDDor_memo_OK in |- *.  intros.  unfold BDDor_memo_OK in H2.  cut (config_node_OK cfg node1).
  cut (config_node_OK cfg node2).  cut (config_node_OK cfg node).  intros.
  cut
   (BDDvar_le (var cfg node) (BDDvar_max (var cfg node1) (var cfg node2)) =
    true).
  intro.  cut
   (bool_fun_eq (bool_fun_of_BDD cfg node)
      (bool_fun_or (bool_fun_of_BDD cfg node1) (bool_fun_of_BDD cfg node2))).
  intro.  split.  apply nodes_preserved_2 with (cfg := cfg).  assumption.  assumption.
  split.  apply nodes_preserved_2 with (cfg := cfg).  assumption.  assumption.  split.
  apply nodes_preserved_2 with (cfg := cfg).  assumption.  assumption.  split.
  cut (var cfg' node = var cfg node).  cut (var cfg' node1 = var cfg node1).
  cut (var cfg' node2 = var cfg node2).  intros.  rewrite H9.  rewrite H10.
  rewrite H11.  assumption.  apply nodes_preserved_var_1.  assumption.  assumption.
  assumption.  assumption.  apply nodes_preserved_var_1.  assumption.  assumption.
  assumption.  assumption.  apply nodes_preserved_var_1.  assumption.  assumption.
  assumption.  assumption.  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg node).
  apply nodes_preserved_3.  assumption.  assumption.  assumption.  assumption.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_or (bool_fun_of_BDD cfg node1)
                (bool_fun_of_BDD cfg node2)).
  assumption.  apply bool_fun_eq_symm.  apply bool_fun_or_preserves_eq.  apply nodes_preserved_3.
  assumption.  assumption.  assumption.  assumption.  apply nodes_preserved_3.
  assumption.  assumption.  assumption.  assumption.  exact (proj2 (proj2 (proj2 (proj2 (H2 node1 node2 node H3))))).
  exact (proj1 (proj2 (proj2 (proj2 (H2 node1 node2 node H3))))).  
  exact (proj1 (proj2 (proj2 (H2 node1 node2 node H3)))).  
  exact (proj1 (proj2 (H2 node1 node2 node H3))).
  exact (proj1 (H2 node1 node2 node H3)).
Qed.

Lemma nodes_preserved_negm_OK :
 forall (cfg cfg' : BDDconfig) (negm : BDDneg_memo),
 BDDconfig_OK cfg ->
 BDDconfig_OK cfg' ->
 nodes_preserved cfg cfg' ->
 BDDneg_memo_OK_2 cfg negm -> BDDneg_memo_OK_2 cfg' negm.
Proof.
  intros.  unfold BDDneg_memo_OK_2 in |- *.  unfold BDDneg_memo_OK_2 in H2.  intros.
  cut (is_internal_node cfg node -> nat_of_N (var cfg node) < bound).  intro.
  cut (config_node_OK cfg node).  cut (BDDneg_2 cfg node bound = (cfg, node')).
  intros.  cut (config_node_OK cfg node').  intro.  cut (config_node_OK cfg' node).
  cut (config_node_OK cfg' node').  intros.  split.  assumption.  apply BDDneg_memo_OK_1_lemma_1_1_1.
  assumption.  assumption.  assumption.  assumption.  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg node').
  apply nodes_preserved_3.  assumption.  assumption.  assumption.  assumption.  
  apply
   bool_fun_eq_trans with (bf2 := bool_fun_neg (bool_fun_of_BDD cfg node)).
  replace (bool_fun_of_BDD cfg node') with
   (bool_fun_of_BDD (fst (BDDneg_2 cfg node bound))
      (snd (BDDneg_2 cfg node bound))).
  refine (proj2 (proj2 (proj2 (proj2 (BDDneg_2_lemma _ _ _ _ _ _))))).
  assumption.  assumption.  assumption.  rewrite H6.  reflexivity.  apply bool_fun_eq_symm.
  apply bool_fun_eq_neg_1.  apply nodes_preserved_3.  assumption.  assumption.  
  assumption.  assumption.  apply nodes_preserved_2 with (cfg := cfg).  assumption. 
  assumption.  apply nodes_preserved_2 with (cfg := cfg).  assumption.  assumption.
  replace cfg with (fst (BDDneg_2 cfg node bound)).  replace node' with (snd (BDDneg_2 cfg node bound)).  refine (proj1 (proj2 (proj2 (proj2 (BDDneg_2_lemma _ _ _ _ _ _))))).
  assumption.  assumption.  assumption.  rewrite H6; reflexivity.  rewrite H6; reflexivity.
  exact (proj2 (H2 node node' bound H3 H5)).  exact (proj1 (H2 node node' bound H3 H5)).  
  intro.  cut (var cfg' node = var cfg node).  intro.  rewrite <- H6.  apply H4.
  inversion H5.  inversion H7.  inversion H8.  split with x.  split with x0.
  split with x1.  apply H1.  assumption.  apply nodes_preserved_var.  assumption.
  assumption.
Qed.

Lemma BDDneg_keeps_config_OK :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (node : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 config_node_OK cfg node -> BDDconfig_OK (fst (BDDneg cfg negm node)).
Proof.
  intros.  unfold BDDneg in |- *.  elim
   (prod_sum _ _ (BDDneg_1_1 cfg negm node (S (nat_of_N (var cfg node))))).
  intro.  elim x; clear x.  intros cfg' node'.  intro.  elim H2; clear H2.
  intros negm' H2.  rewrite H2.  simpl in |- *.  rewrite (BDDneg_1_1_eq_1 (S (nat_of_N (var cfg node))) cfg negm node)
    in H2.
  cut
   (is_internal_node cfg node ->
    nat_of_N (var cfg node) < S (nat_of_N (var cfg node))).
  intro.  replace cfg' with
   (fst (fst (BDDneg_1 (cfg, node, negm) (S (nat_of_N (var cfg node)))))).
  rewrite
   (proj1
      (BDDneg_1_lemma' (S (nat_of_N (var cfg node))) 
         (cfg, node, negm) H H1 H0 H3)).
  exact (proj1 (BDDneg_2_lemma _ _ _ H H1 H3)).  rewrite H2.  reflexivity.
  intro.  unfold lt in |- *.  apply le_n.
Qed.

Lemma BDDneg_node_OK :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (node : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 config_node_OK cfg node ->
 config_node_OK (fst (BDDneg cfg negm node))
   (fst (snd (BDDneg cfg negm node))).
Proof.
  intros.  unfold BDDneg in |- *.  elim
   (prod_sum _ _ (BDDneg_1_1 cfg negm node (S (nat_of_N (var cfg node))))).
  intro.  elim x; clear x.  intros cfg' node'.  intro.  elim H2; clear H2.
  intros negm' H2.  rewrite H2.  simpl in |- *.  rewrite (BDDneg_1_1_eq_1 (S (nat_of_N (var cfg node))) cfg negm node)
    in H2.
  cut
   (is_internal_node cfg node ->
    nat_of_N (var cfg node) < S (nat_of_N (var cfg node))).  intro.  replace cfg' with
   (fst (fst (BDDneg_1 (cfg, node, negm) (S (nat_of_N (var cfg node)))))).
  replace node' with
   (snd (fst (BDDneg_1 (cfg, node, negm) (S (nat_of_N (var cfg node)))))).
  rewrite
   (proj1
      (BDDneg_1_lemma' (S (nat_of_N (var cfg node))) 
         (cfg, node, negm) H H1 H0 H3)).
  exact
   (proj1
      (proj2
         (proj2
            (proj2
               (BDDneg_2_lemma (S (nat_of_N (var cfg node))) cfg node H H1
                  H3))))).
  rewrite H2; reflexivity.  rewrite H2; reflexivity.  intro.  unfold lt in |- *.  apply le_n.
Qed.

Lemma BDDneg_preserves_nodes :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (node : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 config_node_OK cfg node -> nodes_preserved cfg (fst (BDDneg cfg negm node)).
Proof.
  intros.  unfold BDDneg in |- *.  elim
   (prod_sum _ _ (BDDneg_1_1 cfg negm node (S (nat_of_N (var cfg node))))).
  intro.  elim x; clear x.  intros cfg' node'.  intro.  elim H2; clear H2.
  intros negm' H2.  rewrite H2.  simpl in |- *.  rewrite (BDDneg_1_1_eq_1 (S (nat_of_N (var cfg node))) cfg negm node)
    in H2.
  cut
   (is_internal_node cfg node ->
    nat_of_N (var cfg node) < S (nat_of_N (var cfg node))).  intro.  replace cfg' with
   (fst (fst (BDDneg_1 (cfg, node, negm) (S (nat_of_N (var cfg node)))))).
  unfold nodes_preserved in |- *.  rewrite
   (proj1
      (BDDneg_1_lemma' (S (nat_of_N (var cfg node))) 
         (cfg, node, negm) H H1 H0 H3)).
  exact (proj1 (proj2 (BDDneg_2_lemma _ _ _ H H1 H3))).  rewrite H2; reflexivity.
  intro.  unfold lt in |- *.  apply le_n.
Qed.

Lemma BDDneg_keeps_neg_memo_OK :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (node : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 config_node_OK cfg node ->
 BDDneg_memo_OK_2 (fst (BDDneg cfg negm node))
   (snd (snd (BDDneg cfg negm node))).
Proof.
  intros.  unfold BDDneg in |- *.  elim
   (prod_sum _ _ (BDDneg_1_1 cfg negm node (S (nat_of_N (var cfg node))))).
  intro.  elim x; clear x.  intros cfg' node'.  intro.  elim H2; clear H2.
  intros negm' H2.  rewrite H2.  simpl in |- *.  rewrite (BDDneg_1_1_eq_1 (S (nat_of_N (var cfg node))) cfg negm node)
    in H2.
  cut
   (is_internal_node cfg node ->
    nat_of_N (var cfg node) < S (nat_of_N (var cfg node))).
  intro.  replace cfg' with
   (fst (fst (BDDneg_1 (cfg, node, negm) (S (nat_of_N (var cfg node)))))).
  replace negm' with
   (snd (BDDneg_1 (cfg, node, negm) (S (nat_of_N (var cfg node))))).
  refine (proj2 (BDDneg_1_lemma' _ _ _ _ _ _)).  assumption.  assumption.
  assumption.  assumption.  rewrite H2; reflexivity.  rewrite H2; reflexivity.
  intro.  unfold lt in |- *.  apply le_n.
Qed.  
Lemma BDDneg_keeps_or_memo_OK :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (orm : BDDor_memo) (node : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 config_node_OK cfg node ->
 BDDor_memo_OK cfg orm -> BDDor_memo_OK (fst (BDDneg cfg negm node)) orm.
Proof.
  intros.  apply nodes_preserved_orm_OK with (cfg := cfg).  assumption.  apply BDDneg_keeps_config_OK.
  assumption.  assumption.  assumption.  apply BDDneg_preserves_nodes.  assumption.
  assumption.  assumption.  assumption.
Qed.

Lemma BDDneg_keeps_node_OK :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (node : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 config_node_OK cfg node ->
 forall node' : ad,
 config_node_OK cfg node' ->
 config_node_OK (fst (BDDneg cfg negm node)) node'.
Proof.
  intros.  apply nodes_preserved_2 with (cfg := cfg).  assumption.  apply BDDneg_preserves_nodes.
  assumption.  assumption.  assumption.
Qed.

Lemma BDDneg_preserves_bool_fun :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (node : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 config_node_OK cfg node ->
 forall node' : ad,
 config_node_OK cfg node' ->
 bool_fun_eq (bool_fun_of_BDD (fst (BDDneg cfg negm node)) node')
   (bool_fun_of_BDD cfg node').
Proof.
  intros.  apply nodes_preserved_3.  assumption.  apply BDDneg_keeps_config_OK.
  assumption.  assumption.  assumption.  apply BDDneg_preserves_nodes.  assumption.
  assumption.  assumption.  assumption.
Qed.

Lemma BDDneg_is_neg :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (node : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 config_node_OK cfg node ->
 bool_fun_eq
   (bool_fun_of_BDD (fst (BDDneg cfg negm node))
      (fst (snd (BDDneg cfg negm node))))
   (bool_fun_neg (bool_fun_of_BDD cfg node)).
Proof.
  intros.  unfold BDDneg in |- *.  elim
   (prod_sum _ _ (BDDneg_1_1 cfg negm node (S (nat_of_N (var cfg node))))).
  intro.  elim x; clear x.  intros cfg' node'.  intro.  elim H2; clear H2.
  intros negm' H2.  rewrite H2.  simpl in |- *.  rewrite (BDDneg_1_1_eq_1 (S (nat_of_N (var cfg node))) cfg negm node)
    in H2.
  cut
   (is_internal_node cfg node ->
    nat_of_N (var cfg node) < S (nat_of_N (var cfg node))).
  intro.  replace cfg' with
   (fst (fst (BDDneg_1 (cfg, node, negm) (S (nat_of_N (var cfg node)))))).
  replace node' with
   (snd (fst (BDDneg_1 (cfg, node, negm) (S (nat_of_N (var cfg node)))))).
  rewrite
   (proj1
      (BDDneg_1_lemma' (S (nat_of_N (var cfg node))) 
         (cfg, node, negm) H H1 H0 H3)).
  exact (proj2 (proj2 (proj2 (proj2 (BDDneg_2_lemma _ _ _ H H1 H3))))).
  rewrite H2; reflexivity.  rewrite H2; reflexivity.  intro.  unfold lt in |- *.  apply le_n.
Qed.

Lemma BDDor_keeps_config_OK :
 forall (cfg : BDDconfig) (orm : BDDor_memo) (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 -> BDDconfig_OK (fst (BDDor cfg orm node1 node2)).
Proof.
  intros.  unfold BDDor in |- *.  rewrite
   (BDDor_1_1_eq_1
      (S (max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2)))) cfg
      orm node1 node2).
  cut
   (is_internal_node cfg node1 ->
    is_internal_node cfg node2 ->
    max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2)) <
    S (max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2)))).
  intros.  refine (proj1 (BDDor_1_lemma _ _ _ _ _ _ _ _ _ _)).  assumption.
  assumption.  assumption.  assumption.  assumption.  intros.  unfold lt in |- *.  apply le_n.
Qed.

Lemma BDDor_node_OK :
 forall (cfg : BDDconfig) (orm : BDDor_memo) (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 config_node_OK (fst (BDDor cfg orm node1 node2))
   (fst (snd (BDDor cfg orm node1 node2))).
Proof.
  intros.  unfold BDDor in |- *.  rewrite
   (BDDor_1_1_eq_1
      (S (max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2)))) cfg
      orm node1 node2).
  cut
   (is_internal_node cfg node1 ->
    is_internal_node cfg node2 ->
    max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2)) <
    S (max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2)))).
  intros.  refine (proj1 (proj2 (proj2 (BDDor_1_lemma _ _ _ _ _ _ _ _ _ _)))).
  assumption.  assumption.  assumption.  assumption.  assumption.  intros.
  unfold lt in |- *.  apply le_n.
Qed.

Lemma BDDor_keeps_or_memo_OK :
 forall (cfg : BDDconfig) (orm : BDDor_memo) (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 BDDor_memo_OK (fst (BDDor cfg orm node1 node2))
   (snd (snd (BDDor cfg orm node1 node2))).
Proof.
  intros.  unfold BDDor in |- *.  rewrite
   (BDDor_1_1_eq_1
      (S (max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2)))) cfg
      orm node1 node2).
  cut
   (is_internal_node cfg node1 ->
    is_internal_node cfg node2 ->
    max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2)) <
    S (max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2)))).
  intros.  refine (proj1 (proj2 (BDDor_1_lemma _ _ _ _ _ _ _ _ _ _))).  
  assumption.  assumption.  assumption.  assumption.  assumption.  intros.
  unfold lt in |- *.  apply le_n.
Qed.

Lemma BDDor_preserves_nodes :
 forall (cfg : BDDconfig) (orm : BDDor_memo) (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 nodes_preserved cfg (fst (BDDor cfg orm node1 node2)).
Proof.
  intros.  unfold BDDor in |- *.  rewrite
   (BDDor_1_1_eq_1
      (S (max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2)))) cfg
      orm node1 node2).
  cut
   (is_internal_node cfg node1 ->
    is_internal_node cfg node2 ->
    max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2)) <
    S (max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2)))).
  intros.  refine (proj1 (proj2 (proj2 (proj2 (BDDor_1_lemma _ _ _ _ _ _ _ _ _ _))))).
  assumption.  assumption.  assumption.  assumption.  assumption.  intros.  unfold lt in |- *.
  apply le_n.
Qed.

Lemma BDDor_keeps_node_OK :
 forall (cfg : BDDconfig) (orm : BDDor_memo) (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 forall node : ad,
 config_node_OK cfg node ->
 config_node_OK (fst (BDDor cfg orm node1 node2)) node.
Proof.
  intros.  apply nodes_preserved_2 with (cfg := cfg).  assumption.  apply BDDor_preserves_nodes.
  assumption.  assumption.  assumption.  assumption.
Qed.

Lemma BDDor_preserves_bool_fun :
 forall (cfg : BDDconfig) (orm : BDDor_memo) (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 forall node : ad,
 config_node_OK cfg node ->
 bool_fun_eq (bool_fun_of_BDD (fst (BDDor cfg orm node1 node2)) node)
   (bool_fun_of_BDD cfg node).
Proof.
  intros.  apply nodes_preserved_3.  assumption.  apply BDDor_keeps_config_OK.
  assumption.  assumption.  assumption.  assumption.  apply BDDor_preserves_nodes.
  assumption.  assumption.  assumption.  assumption.  assumption.
Qed.

Lemma BDDor_keeps_neg_memo_OK :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (orm : BDDor_memo)
   (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 BDDneg_memo_OK_2 cfg negm ->
 BDDneg_memo_OK_2 (fst (BDDor cfg orm node1 node2)) negm.
Proof.
  intros.  apply nodes_preserved_negm_OK with (cfg := cfg).  assumption.  apply BDDor_keeps_config_OK.
  assumption.  assumption.  assumption.  assumption.  apply BDDor_preserves_nodes.
  assumption.  assumption.  assumption.  assumption.  assumption.
Qed.

Lemma BDDor_is_or :
 forall (cfg : BDDconfig) (orm : BDDor_memo) (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 bool_fun_eq
   (bool_fun_of_BDD (fst (BDDor cfg orm node1 node2))
      (fst (snd (BDDor cfg orm node1 node2))))
   (bool_fun_or (bool_fun_of_BDD cfg node1) (bool_fun_of_BDD cfg node2)).
Proof.
  intros.  unfold BDDor in |- *.  rewrite
   (BDDor_1_1_eq_1
      (S (max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2)))) cfg
      orm node1 node2).
  cut
   (is_internal_node cfg node1 ->
    is_internal_node cfg node2 ->
    max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2)) <
    S (max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2)))).
  intros.  refine
   (proj2 (proj2 (proj2 (proj2 (proj2 (BDDor_1_lemma _ _ _ _ _ _ _ _ _ _)))))).
  assumption.  assumption.  assumption.  assumption.  assumption.  intros.  unfold lt in |- *.
  apply le_n.
Qed.

Lemma BDDand_keeps_config_OK :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (orm : BDDor_memo)
   (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 BDDconfig_OK (fst (BDDand cfg negm orm node1 node2)).
Proof.

  intros.  unfold BDDand in |- *.  elim (prod_sum _ _ (BDDneg cfg negm node1)).  intros cfg' H4.
  elim H4; clear H4.  intro.  elim x; clear x.  intros node1' negm' H4.  rewrite H4.
  elim (prod_sum _ _ (BDDneg cfg' negm' node2)).  intros cfg'' H5.  elim H5; clear H5.
  intro.  elim x; clear x.  intros node2' negm'' H5.  rewrite H5.  elim (prod_sum _ _ (BDDor cfg'' orm node1' node2')).
  intros cfg''' H6.  elim H6; clear H6.  intro.  elim x; clear x.  intros node orm' H6.
  rewrite H6.  elim (prod_sum _ _ (BDDneg cfg''' negm'' node)).  intros cfg'''' H7.
  elim H7; clear H7.  intro.  elim x; clear x.  intros node' negm''' H7.  rewrite H7.
  simpl in |- *.  cut (BDDconfig_OK cfg').  cut (config_node_OK cfg' node1').  cut (config_node_OK cfg' node2).
  cut (BDDneg_memo_OK_2 cfg' negm').  cut (BDDor_memo_OK cfg' orm).  intros.
  cut (BDDconfig_OK cfg'').  cut (config_node_OK cfg'' node2').  cut (config_node_OK cfg'' node1').
  cut (BDDneg_memo_OK_2 cfg'' negm'').  cut (BDDor_memo_OK cfg'' orm).  intros.
  cut (BDDconfig_OK cfg''').  cut (config_node_OK cfg''' node).  cut (BDDneg_memo_OK_2 cfg''' negm'').
  cut (BDDor_memo_OK cfg''' orm').  intros.


  replace cfg'''' with (fst (BDDneg cfg''' negm'' node)).
apply BDDneg_keeps_config_OK.
assumption.

assumption.

assumption.

rewrite H7; reflexivity.




  replace cfg''' with (fst (BDDor cfg'' orm node1' node2')).  replace orm' with (snd (snd (BDDor cfg'' orm node1' node2'))).
  apply BDDor_keeps_or_memo_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H6; reflexivity.  rewrite H6; reflexivity.  replace cfg''' with (fst (BDDor cfg'' orm node1' node2')).
  apply BDDor_keeps_neg_memo_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H6; reflexivity.  replace cfg''' with (fst (BDDor cfg'' orm node1' node2')).
  replace node with (fst (snd (BDDor cfg'' orm node1' node2'))).  apply BDDor_node_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H6; reflexivity.
  rewrite H6; reflexivity.  replace cfg''' with (fst (BDDor cfg'' orm node1' node2')).
  apply BDDor_keeps_config_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H6; reflexivity.  replace cfg'' with (fst (BDDneg cfg' negm' node2)).
  apply BDDneg_keeps_or_memo_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDneg cfg' negm' node2)).
  replace negm'' with (snd (snd (BDDneg cfg' negm' node2))).  apply BDDneg_keeps_neg_memo_OK.
  assumption.  assumption.  assumption.  rewrite H5; reflexivity.  rewrite H5; reflexivity.
  replace cfg'' with (fst (BDDneg cfg' negm' node2)).  apply BDDneg_keeps_node_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H5; reflexivity.
  replace cfg'' with (fst (BDDneg cfg' negm' node2)).  replace node2' with (fst (snd (BDDneg cfg' negm' node2))).  apply BDDneg_node_OK.  assumption.  assumption.
  assumption.  rewrite H5; reflexivity.  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDneg cfg' negm' node2)).
  apply BDDneg_keeps_config_OK.  assumption.  assumption.  assumption.  rewrite H5; reflexivity.

  replace cfg' with (fst (BDDneg cfg negm node1)).  apply BDDneg_keeps_or_memo_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  replace negm' with (snd (snd (BDDneg cfg negm node1))).
  apply BDDneg_keeps_neg_memo_OK.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDneg cfg negm node1)).
  apply BDDneg_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDneg cfg negm node1)).
  replace node1' with (fst (snd (BDDneg cfg negm node1))).  apply BDDneg_node_OK.
  assumption.  assumption.  assumption.  rewrite H4; reflexivity.  rewrite H4; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  apply BDDneg_keeps_config_OK.
  assumption.  assumption.  assumption.  rewrite H4; reflexivity.


Qed.

Lemma BDDand_node_OK :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (orm : BDDor_memo)
   (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 config_node_OK (fst (BDDand cfg negm orm node1 node2))
   (fst (snd (BDDand cfg negm orm node1 node2))).
Proof.


  intros.  unfold BDDand in |- *.  elim (prod_sum _ _ (BDDneg cfg negm node1)).  intros cfg' H4.
  elim H4; clear H4.  intro.  elim x; clear x.  intros node1' negm' H4.  rewrite H4.
  elim (prod_sum _ _ (BDDneg cfg' negm' node2)).  intros cfg'' H5.  elim H5; clear H5.
  intro.  elim x; clear x.  intros node2' negm'' H5.  rewrite H5.  elim (prod_sum _ _ (BDDor cfg'' orm node1' node2')).
  intros cfg''' H6.  elim H6; clear H6.  intro.  elim x; clear x.  intros node orm' H6.
  rewrite H6.  elim (prod_sum _ _ (BDDneg cfg''' negm'' node)).  intros cfg'''' H7.
  elim H7; clear H7.  intro.  elim x; clear x.  intros node' negm''' H7.  rewrite H7.
  simpl in |- *.  cut (BDDconfig_OK cfg').  cut (config_node_OK cfg' node1').  cut (config_node_OK cfg' node2).
  cut (BDDneg_memo_OK_2 cfg' negm').  cut (BDDor_memo_OK cfg' orm).  intros.
  cut (BDDconfig_OK cfg'').  cut (config_node_OK cfg'' node2').  cut (config_node_OK cfg'' node1').
  cut (BDDneg_memo_OK_2 cfg'' negm'').  cut (BDDor_memo_OK cfg'' orm).  intros.
  cut (BDDconfig_OK cfg''').  cut (config_node_OK cfg''' node).  cut (BDDneg_memo_OK_2 cfg''' negm'').
  cut (BDDor_memo_OK cfg''' orm').  intros.


replace cfg'''' with (fst (BDDneg cfg''' negm'' node)).
replace node' with (fst (snd (BDDneg cfg''' negm'' node))).
apply BDDneg_node_OK.
assumption.

assumption.

assumption.

rewrite H7; reflexivity.

rewrite H7; reflexivity.



  replace cfg''' with (fst (BDDor cfg'' orm node1' node2')).  replace orm' with (snd (snd (BDDor cfg'' orm node1' node2'))).
  apply BDDor_keeps_or_memo_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H6; reflexivity.  rewrite H6; reflexivity.  replace cfg''' with (fst (BDDor cfg'' orm node1' node2')).
  apply BDDor_keeps_neg_memo_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H6; reflexivity.  replace cfg''' with (fst (BDDor cfg'' orm node1' node2')).
  replace node with (fst (snd (BDDor cfg'' orm node1' node2'))).  apply BDDor_node_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H6; reflexivity.
  rewrite H6; reflexivity.  replace cfg''' with (fst (BDDor cfg'' orm node1' node2')).
  apply BDDor_keeps_config_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H6; reflexivity.  replace cfg'' with (fst (BDDneg cfg' negm' node2)).
  apply BDDneg_keeps_or_memo_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDneg cfg' negm' node2)).
  replace negm'' with (snd (snd (BDDneg cfg' negm' node2))).  apply BDDneg_keeps_neg_memo_OK.
  assumption.  assumption.  assumption.  rewrite H5; reflexivity.  rewrite H5; reflexivity.
  replace cfg'' with (fst (BDDneg cfg' negm' node2)).  apply BDDneg_keeps_node_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H5; reflexivity.
  replace cfg'' with (fst (BDDneg cfg' negm' node2)).  replace node2' with (fst (snd (BDDneg cfg' negm' node2))).  apply BDDneg_node_OK.  assumption.  assumption.
  assumption.  rewrite H5; reflexivity.  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDneg cfg' negm' node2)).
  apply BDDneg_keeps_config_OK.  assumption.  assumption.  assumption.  rewrite H5; reflexivity.

  replace cfg' with (fst (BDDneg cfg negm node1)).  apply BDDneg_keeps_or_memo_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  replace negm' with (snd (snd (BDDneg cfg negm node1))).
  apply BDDneg_keeps_neg_memo_OK.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDneg cfg negm node1)).
  apply BDDneg_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDneg cfg negm node1)).
  replace node1' with (fst (snd (BDDneg cfg negm node1))).  apply BDDneg_node_OK.
  assumption.  assumption.  assumption.  rewrite H4; reflexivity.  rewrite H4; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  apply BDDneg_keeps_config_OK.
  assumption.  assumption.  assumption.  rewrite H4; reflexivity.

Qed.

Lemma BDDand_preserves_nodes :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (orm : BDDor_memo)
   (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 nodes_preserved cfg (fst (BDDand cfg negm orm node1 node2)).
Proof.

  intros.  unfold BDDand in |- *.  elim (prod_sum _ _ (BDDneg cfg negm node1)).  intros cfg' H4.
  elim H4; clear H4.  intro.  elim x; clear x.  intros node1' negm' H4.  rewrite H4.
  elim (prod_sum _ _ (BDDneg cfg' negm' node2)).  intros cfg'' H5.  elim H5; clear H5.
  intro.  elim x; clear x.  intros node2' negm'' H5.  rewrite H5.  elim (prod_sum _ _ (BDDor cfg'' orm node1' node2')).
  intros cfg''' H6.  elim H6; clear H6.  intro.  elim x; clear x.  intros node orm' H6.
  rewrite H6.  elim (prod_sum _ _ (BDDneg cfg''' negm'' node)).  intros cfg'''' H7.
  elim H7; clear H7.  intro.  elim x; clear x.  intros node' negm''' H7.  rewrite H7.
  simpl in |- *.  cut (BDDconfig_OK cfg').  cut (config_node_OK cfg' node1').  cut (config_node_OK cfg' node2).
  cut (BDDneg_memo_OK_2 cfg' negm').  cut (BDDor_memo_OK cfg' orm).  intros.
  cut (BDDconfig_OK cfg'').  cut (config_node_OK cfg'' node2').  cut (config_node_OK cfg'' node1').
  cut (BDDneg_memo_OK_2 cfg'' negm'').  cut (BDDor_memo_OK cfg'' orm).  intros.
  cut (BDDconfig_OK cfg''').  cut (config_node_OK cfg''' node).  cut (BDDneg_memo_OK_2 cfg''' negm'').
  cut (BDDor_memo_OK cfg''' orm').  intros.


apply nodes_preserved_trans with (cfg2 := cfg').
replace cfg' with (fst (BDDneg cfg negm node1)).
apply BDDneg_preserves_nodes.
assumption.

assumption.

assumption.

rewrite H4; reflexivity.

apply nodes_preserved_trans with (cfg2 := cfg'').
replace cfg'' with (fst (BDDneg cfg' negm' node2)).
apply BDDneg_preserves_nodes.
assumption.

assumption.

assumption.

rewrite H5; reflexivity.

apply nodes_preserved_trans with (cfg2 := cfg''').
replace cfg''' with (fst (BDDor cfg'' orm node1' node2')).
apply BDDor_preserves_nodes.
assumption.

assumption.

assumption.

assumption.

rewrite H6; reflexivity.

replace cfg'''' with (fst (BDDneg cfg''' negm'' node)).
apply BDDneg_preserves_nodes.
assumption.

assumption.

assumption.

rewrite H7; reflexivity.


  replace cfg''' with (fst (BDDor cfg'' orm node1' node2')).  replace orm' with (snd (snd (BDDor cfg'' orm node1' node2'))).
  apply BDDor_keeps_or_memo_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H6; reflexivity.  rewrite H6; reflexivity.  replace cfg''' with (fst (BDDor cfg'' orm node1' node2')).
  apply BDDor_keeps_neg_memo_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H6; reflexivity.  replace cfg''' with (fst (BDDor cfg'' orm node1' node2')).
  replace node with (fst (snd (BDDor cfg'' orm node1' node2'))).  apply BDDor_node_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H6; reflexivity.
  rewrite H6; reflexivity.  replace cfg''' with (fst (BDDor cfg'' orm node1' node2')).
  apply BDDor_keeps_config_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H6; reflexivity.  replace cfg'' with (fst (BDDneg cfg' negm' node2)).
  apply BDDneg_keeps_or_memo_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDneg cfg' negm' node2)).
  replace negm'' with (snd (snd (BDDneg cfg' negm' node2))).  apply BDDneg_keeps_neg_memo_OK.
  assumption.  assumption.  assumption.  rewrite H5; reflexivity.  rewrite H5; reflexivity.
  replace cfg'' with (fst (BDDneg cfg' negm' node2)).  apply BDDneg_keeps_node_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H5; reflexivity.
  replace cfg'' with (fst (BDDneg cfg' negm' node2)).  replace node2' with (fst (snd (BDDneg cfg' negm' node2))).  apply BDDneg_node_OK.  assumption.  assumption.
  assumption.  rewrite H5; reflexivity.  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDneg cfg' negm' node2)).
  apply BDDneg_keeps_config_OK.  assumption.  assumption.  assumption.  rewrite H5; reflexivity.

  replace cfg' with (fst (BDDneg cfg negm node1)).  apply BDDneg_keeps_or_memo_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  replace negm' with (snd (snd (BDDneg cfg negm node1))).
  apply BDDneg_keeps_neg_memo_OK.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDneg cfg negm node1)).
  apply BDDneg_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDneg cfg negm node1)).
  replace node1' with (fst (snd (BDDneg cfg negm node1))).  apply BDDneg_node_OK.
  assumption.  assumption.  assumption.  rewrite H4; reflexivity.  rewrite H4; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  apply BDDneg_keeps_config_OK.
  assumption.  assumption.  assumption.  rewrite H4; reflexivity.

Qed.

Lemma BDDand_keeps_node_OK :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (orm : BDDor_memo)
   (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 forall node : ad,
 config_node_OK cfg node ->
 config_node_OK (fst (BDDand cfg negm orm node1 node2)) node.
Proof.
  intros.  apply nodes_preserved_2 with (cfg := cfg).  assumption.  apply BDDand_preserves_nodes.
  assumption.  assumption.  assumption.  assumption.  assumption.
Qed.

Lemma BDDand_preserves_bool_fun :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (orm : BDDor_memo)
   (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 forall node : ad,
 config_node_OK cfg node ->
 bool_fun_eq (bool_fun_of_BDD (fst (BDDand cfg negm orm node1 node2)) node)
   (bool_fun_of_BDD cfg node).
Proof.
  intros.  apply nodes_preserved_3.  assumption.  apply BDDand_keeps_config_OK.
  assumption.  assumption.  assumption.  assumption.  assumption.  apply BDDand_preserves_nodes.
  assumption.  assumption.  assumption.  assumption.  assumption.  assumption.
Qed.

Lemma BDDand_keeps_neg_memo_OK :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (orm : BDDor_memo)
   (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 BDDneg_memo_OK_2 (fst (BDDand cfg negm orm node1 node2))
   (fst (snd (snd (BDDand cfg negm orm node1 node2)))).
Proof.

  intros.  unfold BDDand in |- *.  elim (prod_sum _ _ (BDDneg cfg negm node1)).  intros cfg' H4.
  elim H4; clear H4.  intro.  elim x; clear x.  intros node1' negm' H4.  rewrite H4.
  elim (prod_sum _ _ (BDDneg cfg' negm' node2)).  intros cfg'' H5.  elim H5; clear H5.
  intro.  elim x; clear x.  intros node2' negm'' H5.  rewrite H5.  elim (prod_sum _ _ (BDDor cfg'' orm node1' node2')).
  intros cfg''' H6.  elim H6; clear H6.  intro.  elim x; clear x.  intros node orm' H6.
  rewrite H6.  elim (prod_sum _ _ (BDDneg cfg''' negm'' node)).  intros cfg'''' H7.
  elim H7; clear H7.  intro.  elim x; clear x.  intros node' negm''' H7.  rewrite H7.
  simpl in |- *.  cut (BDDconfig_OK cfg').  cut (config_node_OK cfg' node1').  cut (config_node_OK cfg' node2).
  cut (BDDneg_memo_OK_2 cfg' negm').  cut (BDDor_memo_OK cfg' orm).  intros.
  cut (BDDconfig_OK cfg'').  cut (config_node_OK cfg'' node2').  cut (config_node_OK cfg'' node1').
  cut (BDDneg_memo_OK_2 cfg'' negm'').  cut (BDDor_memo_OK cfg'' orm).  intros.
  cut (BDDconfig_OK cfg''').  cut (config_node_OK cfg''' node).  cut (BDDneg_memo_OK_2 cfg''' negm'').
  cut (BDDor_memo_OK cfg''' orm').  intros.


replace cfg'''' with (fst (BDDneg cfg''' negm'' node)).
replace negm''' with (snd (snd (BDDneg cfg''' negm'' node))).
apply BDDneg_keeps_neg_memo_OK.
assumption.

assumption.

assumption.

rewrite H7; reflexivity.

rewrite H7; reflexivity.



  replace cfg''' with (fst (BDDor cfg'' orm node1' node2')).  replace orm' with (snd (snd (BDDor cfg'' orm node1' node2'))).
  apply BDDor_keeps_or_memo_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H6; reflexivity.  rewrite H6; reflexivity.  replace cfg''' with (fst (BDDor cfg'' orm node1' node2')).
  apply BDDor_keeps_neg_memo_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H6; reflexivity.  replace cfg''' with (fst (BDDor cfg'' orm node1' node2')).
  replace node with (fst (snd (BDDor cfg'' orm node1' node2'))).  apply BDDor_node_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H6; reflexivity.
  rewrite H6; reflexivity.  replace cfg''' with (fst (BDDor cfg'' orm node1' node2')).
  apply BDDor_keeps_config_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H6; reflexivity.  replace cfg'' with (fst (BDDneg cfg' negm' node2)).
  apply BDDneg_keeps_or_memo_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDneg cfg' negm' node2)).
  replace negm'' with (snd (snd (BDDneg cfg' negm' node2))).  apply BDDneg_keeps_neg_memo_OK.
  assumption.  assumption.  assumption.  rewrite H5; reflexivity.  rewrite H5; reflexivity.
  replace cfg'' with (fst (BDDneg cfg' negm' node2)).  apply BDDneg_keeps_node_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H5; reflexivity.
  replace cfg'' with (fst (BDDneg cfg' negm' node2)).  replace node2' with (fst (snd (BDDneg cfg' negm' node2))).  apply BDDneg_node_OK.  assumption.  assumption.
  assumption.  rewrite H5; reflexivity.  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDneg cfg' negm' node2)).
  apply BDDneg_keeps_config_OK.  assumption.  assumption.  assumption.  rewrite H5; reflexivity.

  replace cfg' with (fst (BDDneg cfg negm node1)).  apply BDDneg_keeps_or_memo_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  replace negm' with (snd (snd (BDDneg cfg negm node1))).
  apply BDDneg_keeps_neg_memo_OK.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDneg cfg negm node1)).
  apply BDDneg_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDneg cfg negm node1)).
  replace node1' with (fst (snd (BDDneg cfg negm node1))).  apply BDDneg_node_OK.
  assumption.  assumption.  assumption.  rewrite H4; reflexivity.  rewrite H4; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  apply BDDneg_keeps_config_OK.
  assumption.  assumption.  assumption.  rewrite H4; reflexivity.

Qed.

Lemma BDDand_keeps_or_memo_OK :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (orm : BDDor_memo)
   (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 BDDor_memo_OK (fst (BDDand cfg negm orm node1 node2))
   (snd (snd (snd (BDDand cfg negm orm node1 node2)))).
Proof.

  intros.  unfold BDDand in |- *.  elim (prod_sum _ _ (BDDneg cfg negm node1)).  intros cfg' H4.
  elim H4; clear H4.  intro.  elim x; clear x.  intros node1' negm' H4.  rewrite H4.
  elim (prod_sum _ _ (BDDneg cfg' negm' node2)).  intros cfg'' H5.  elim H5; clear H5.
  intro.  elim x; clear x.  intros node2' negm'' H5.  rewrite H5.  elim (prod_sum _ _ (BDDor cfg'' orm node1' node2')).
  intros cfg''' H6.  elim H6; clear H6.  intro.  elim x; clear x.  intros node orm' H6.
  rewrite H6.  elim (prod_sum _ _ (BDDneg cfg''' negm'' node)).  intros cfg'''' H7.
  elim H7; clear H7.  intro.  elim x; clear x.  intros node' negm''' H7.  rewrite H7.
  simpl in |- *.  cut (BDDconfig_OK cfg').  cut (config_node_OK cfg' node1').  cut (config_node_OK cfg' node2).
  cut (BDDneg_memo_OK_2 cfg' negm').  cut (BDDor_memo_OK cfg' orm).  intros.
  cut (BDDconfig_OK cfg'').  cut (config_node_OK cfg'' node2').  cut (config_node_OK cfg'' node1').
  cut (BDDneg_memo_OK_2 cfg'' negm'').  cut (BDDor_memo_OK cfg'' orm).  intros.
  cut (BDDconfig_OK cfg''').  cut (config_node_OK cfg''' node).  cut (BDDneg_memo_OK_2 cfg''' negm'').
  cut (BDDor_memo_OK cfg''' orm').  intros.


replace cfg'''' with (fst (BDDneg cfg''' negm'' node)).
apply BDDneg_keeps_or_memo_OK.
assumption.

assumption.

assumption.

assumption.

rewrite H7; reflexivity.




  replace cfg''' with (fst (BDDor cfg'' orm node1' node2')).  replace orm' with (snd (snd (BDDor cfg'' orm node1' node2'))).
  apply BDDor_keeps_or_memo_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H6; reflexivity.  rewrite H6; reflexivity.  replace cfg''' with (fst (BDDor cfg'' orm node1' node2')).
  apply BDDor_keeps_neg_memo_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H6; reflexivity.  replace cfg''' with (fst (BDDor cfg'' orm node1' node2')).
  replace node with (fst (snd (BDDor cfg'' orm node1' node2'))).  apply BDDor_node_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H6; reflexivity.
  rewrite H6; reflexivity.  replace cfg''' with (fst (BDDor cfg'' orm node1' node2')).
  apply BDDor_keeps_config_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H6; reflexivity.  replace cfg'' with (fst (BDDneg cfg' negm' node2)).
  apply BDDneg_keeps_or_memo_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDneg cfg' negm' node2)).
  replace negm'' with (snd (snd (BDDneg cfg' negm' node2))).  apply BDDneg_keeps_neg_memo_OK.
  assumption.  assumption.  assumption.  rewrite H5; reflexivity.  rewrite H5; reflexivity.
  replace cfg'' with (fst (BDDneg cfg' negm' node2)).  apply BDDneg_keeps_node_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H5; reflexivity.
  replace cfg'' with (fst (BDDneg cfg' negm' node2)).  replace node2' with (fst (snd (BDDneg cfg' negm' node2))).  apply BDDneg_node_OK.  assumption.  assumption.
  assumption.  rewrite H5; reflexivity.  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDneg cfg' negm' node2)).
  apply BDDneg_keeps_config_OK.  assumption.  assumption.  assumption.  rewrite H5; reflexivity.

  replace cfg' with (fst (BDDneg cfg negm node1)).  apply BDDneg_keeps_or_memo_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  replace negm' with (snd (snd (BDDneg cfg negm node1))).
  apply BDDneg_keeps_neg_memo_OK.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDneg cfg negm node1)).
  apply BDDneg_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDneg cfg negm node1)).
  replace node1' with (fst (snd (BDDneg cfg negm node1))).  apply BDDneg_node_OK.
  assumption.  assumption.  assumption.  rewrite H4; reflexivity.  rewrite H4; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  apply BDDneg_keeps_config_OK.
  assumption.  assumption.  assumption.  rewrite H4; reflexivity.

Qed.

Definition bool_fun_and (bf1 bf2 : bool_fun) : bool_fun :=
  fun vb : var_binding => bf1 vb && bf2 vb.

Lemma bool_fun_and_is_neg_or_neg_neg :
 forall bf1 bf2 : bool_fun,
 bool_fun_eq (bool_fun_and bf1 bf2)
   (bool_fun_neg (bool_fun_or (bool_fun_neg bf1) (bool_fun_neg bf2))).
Proof.
  intros.  unfold bool_fun_eq, bool_fun_neg, bool_fun_or, bool_fun_and in |- *.  unfold bool_fun_eval in |- *.
  intro.  elim (bf1 vb).  elim (bf2 vb).  reflexivity.  reflexivity.  reflexivity.
Qed.

Lemma BDDand_is_and :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (orm : BDDor_memo)
   (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 bool_fun_eq
   (bool_fun_of_BDD (fst (BDDand cfg negm orm node1 node2))
      (fst (snd (BDDand cfg negm orm node1 node2))))
   (bool_fun_and (bool_fun_of_BDD cfg node1) (bool_fun_of_BDD cfg node2)).
Proof.

  intros.  unfold BDDand in |- *.  elim (prod_sum _ _ (BDDneg cfg negm node1)).  intros cfg' H4.
  elim H4; clear H4.  intro.  elim x; clear x.  intros node1' negm' H4.  rewrite H4.
  elim (prod_sum _ _ (BDDneg cfg' negm' node2)).  intros cfg'' H5.  elim H5; clear H5.
  intro.  elim x; clear x.  intros node2' negm'' H5.  rewrite H5.  elim (prod_sum _ _ (BDDor cfg'' orm node1' node2')).
  intros cfg''' H6.  elim H6; clear H6.  intro.  elim x; clear x.  intros node orm' H6.
  rewrite H6.  elim (prod_sum _ _ (BDDneg cfg''' negm'' node)).  intros cfg'''' H7.
  elim H7; clear H7.  intro.  elim x; clear x.  intros node' negm''' H7.  rewrite H7.
  simpl in |- *.  cut (BDDconfig_OK cfg').  cut (config_node_OK cfg' node1').  cut (config_node_OK cfg' node2).
  cut (BDDneg_memo_OK_2 cfg' negm').  cut (BDDor_memo_OK cfg' orm).  intros.
  cut (BDDconfig_OK cfg'').  cut (config_node_OK cfg'' node2').  cut (config_node_OK cfg'' node1').
  cut (BDDneg_memo_OK_2 cfg'' negm'').  cut (BDDor_memo_OK cfg'' orm).  intros.
  cut (BDDconfig_OK cfg''').  cut (config_node_OK cfg''' node).  cut (BDDneg_memo_OK_2 cfg''' negm'').
  cut (BDDor_memo_OK cfg''' orm').  intros.



apply
 bool_fun_eq_trans with (bf2 := bool_fun_neg (bool_fun_of_BDD cfg''' node)).
replace cfg'''' with (fst (BDDneg cfg''' negm'' node)).
replace node' with (fst (snd (BDDneg cfg''' negm'' node))).
apply BDDneg_is_neg.
assumption.

assumption.

assumption.

rewrite H7; reflexivity.

rewrite H7; reflexivity.

apply
 bool_fun_eq_trans
  with
    (bf2 := bool_fun_neg
              (bool_fun_or (bool_fun_of_BDD cfg'' node1')
                 (bool_fun_of_BDD cfg'' node2'))).
apply bool_fun_eq_neg_1.
replace cfg''' with (fst (BDDor cfg'' orm node1' node2')).
replace node with (fst (snd (BDDor cfg'' orm node1' node2'))).
apply BDDor_is_or.
assumption.

assumption.

assumption.

assumption.

rewrite H6; reflexivity.

rewrite H6; reflexivity.

apply
 bool_fun_eq_trans
  with
    (bf2 := bool_fun_neg
              (bool_fun_or (bool_fun_neg (bool_fun_of_BDD cfg node1))
                 (bool_fun_neg (bool_fun_of_BDD cfg node2)))).
apply bool_fun_eq_neg_1.
apply bool_fun_or_preserves_eq.
apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg' node1').
replace cfg'' with (fst (BDDneg cfg' negm' node2)).
apply BDDneg_preserves_bool_fun.
assumption.

assumption.

assumption.

assumption.

rewrite H5; reflexivity.

replace cfg' with (fst (BDDneg cfg negm node1)).
replace node1' with (fst (snd (BDDneg cfg negm node1))).
apply BDDneg_is_neg.
assumption.

assumption.

assumption.

rewrite H4; reflexivity.

rewrite H4; reflexivity.

apply
 bool_fun_eq_trans with (bf2 := bool_fun_neg (bool_fun_of_BDD cfg' node2)).
replace cfg'' with (fst (BDDneg cfg' negm' node2)).
replace node2' with (fst (snd (BDDneg cfg' negm' node2))).
apply BDDneg_is_neg.
assumption.

assumption.

assumption.

rewrite H5; reflexivity.

rewrite H5; reflexivity.

replace cfg' with (fst (BDDneg cfg negm node1)).
apply bool_fun_eq_neg_1.
apply BDDneg_preserves_bool_fun.
assumption.

assumption.

assumption.

assumption.

rewrite H4; reflexivity.

apply bool_fun_eq_symm.
apply bool_fun_and_is_neg_or_neg_neg.


  replace cfg''' with (fst (BDDor cfg'' orm node1' node2')).  replace orm' with (snd (snd (BDDor cfg'' orm node1' node2'))).
  apply BDDor_keeps_or_memo_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H6; reflexivity.  rewrite H6; reflexivity.  replace cfg''' with (fst (BDDor cfg'' orm node1' node2')).
  apply BDDor_keeps_neg_memo_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H6; reflexivity.  replace cfg''' with (fst (BDDor cfg'' orm node1' node2')).
  replace node with (fst (snd (BDDor cfg'' orm node1' node2'))).  apply BDDor_node_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H6; reflexivity.
  rewrite H6; reflexivity.  replace cfg''' with (fst (BDDor cfg'' orm node1' node2')).
  apply BDDor_keeps_config_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H6; reflexivity.  replace cfg'' with (fst (BDDneg cfg' negm' node2)).
  apply BDDneg_keeps_or_memo_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDneg cfg' negm' node2)).
  replace negm'' with (snd (snd (BDDneg cfg' negm' node2))).  apply BDDneg_keeps_neg_memo_OK.
  assumption.  assumption.  assumption.  rewrite H5; reflexivity.  rewrite H5; reflexivity.
  replace cfg'' with (fst (BDDneg cfg' negm' node2)).  apply BDDneg_keeps_node_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H5; reflexivity.
  replace cfg'' with (fst (BDDneg cfg' negm' node2)).  replace node2' with (fst (snd (BDDneg cfg' negm' node2))).  apply BDDneg_node_OK.  assumption.  assumption.
  assumption.  rewrite H5; reflexivity.  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDneg cfg' negm' node2)).
  apply BDDneg_keeps_config_OK.  assumption.  assumption.  assumption.  rewrite H5; reflexivity.

  replace cfg' with (fst (BDDneg cfg negm node1)).  apply BDDneg_keeps_or_memo_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  replace negm' with (snd (snd (BDDneg cfg negm node1))).
  apply BDDneg_keeps_neg_memo_OK.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDneg cfg negm node1)).
  apply BDDneg_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDneg cfg negm node1)).
  replace node1' with (fst (snd (BDDneg cfg negm node1))).  apply BDDneg_node_OK.
  assumption.  assumption.  assumption.  rewrite H4; reflexivity.  rewrite H4; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  apply BDDneg_keeps_config_OK.
  assumption.  assumption.  assumption.  rewrite H4; reflexivity.

Qed.