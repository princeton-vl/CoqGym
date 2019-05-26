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
Require Import neg.
Require Import or.

Section BDDop.

Variable gc : BDDconfig -> list ad -> BDDconfig.
Hypothesis gc_is_OK : gc_OK gc.


                         Section BDDneg_results.

Variable cfg : BDDconfig.
Variable ul : list ad.
Variable node : ad.

Hypothesis cfg_OK : BDDconfig_OK cfg.
Hypothesis ul_OK : used_list_OK cfg ul.
Hypothesis used : used_node' cfg ul node.

Definition BDDneg :=
  BDDneg_1 gc cfg ul node (S (nat_of_N (node_height cfg node))).

Let lt_1 :
  nat_of_N (node_height cfg node) < S (nat_of_N (node_height cfg node)).
Proof.
  unfold lt in |- *.  apply le_n.
Qed.

Lemma BDDneg_config_OK : BDDconfig_OK (fst BDDneg).
Proof.
  unfold BDDneg in |- *.
  exact
   (proj1
      (BDDneg_1_lemma gc gc_is_OK (S (nat_of_N (node_height cfg node))) cfg
         ul node lt_1 cfg_OK ul_OK used)).
Qed.

Lemma BDDneg_node_OK : config_node_OK (fst BDDneg) (snd BDDneg).
Proof.
  unfold BDDneg in |- *.
  exact
   (proj1
      (proj2
         (BDDneg_1_lemma gc gc_is_OK (S (nat_of_N (node_height cfg node)))
            cfg ul node lt_1 cfg_OK ul_OK used))).
Qed.

Lemma BDDneg_used_nodes_preserved : used_nodes_preserved cfg (fst BDDneg) ul.
Proof.
  unfold BDDneg in |- *.
  exact
   (proj1
      (proj2
         (proj2
            (BDDneg_1_lemma gc gc_is_OK
               (S (nat_of_N (node_height cfg node))) cfg ul node lt_1 cfg_OK
               ul_OK used)))).
Qed.

Lemma BDDneg_is_neg :
 bool_fun_eq (bool_fun_of_BDD (fst BDDneg) (snd BDDneg))
   (bool_fun_neg (bool_fun_of_BDD cfg node)).
Proof.
  unfold BDDneg in |- *.
  exact
   (proj2
      (proj2
         (proj2
            (proj2
               (BDDneg_1_lemma gc gc_is_OK
                  (S (nat_of_N (node_height cfg node))) cfg ul node lt_1
                  cfg_OK ul_OK used))))).
Qed.

Lemma BDDneg_list_OK : used_list_OK (fst BDDneg) ul.
Proof.
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.
  exact BDDneg_used_nodes_preserved.  
Qed.

Lemma BDDneg_list_OK_cons : used_list_OK (fst BDDneg) (snd BDDneg :: ul).
Proof.
  apply node_OK_list_OK.  exact BDDneg_node_OK.  exact BDDneg_list_OK.
Qed.

Lemma BDDneg_var_eq :
 Neqb (node_height (fst BDDneg) (snd BDDneg)) (node_height cfg node) = true.
Proof.
  unfold BDDneg in |- *.
  exact
   (proj1
      (proj2
         (proj2
            (proj2
               (BDDneg_1_lemma gc gc_is_OK
                  (S (nat_of_N (node_height cfg node))) cfg ul node lt_1
                  cfg_OK ul_OK used))))).
Qed.

                         End BDDneg_results.


                        Section BDDor_results.


Variable cfg : BDDconfig.
Variable ul : list ad.
Variable node1 node2 : ad.

Hypothesis cfg_OK : BDDconfig_OK cfg.
Hypothesis ul_OK : used_list_OK cfg ul.
Hypothesis used1 : used_node' cfg ul node1.
Hypothesis used2 : used_node' cfg ul node2.

Definition BDDor :=
  BDDor_1 gc cfg ul node1 node2
    (S
       (max (nat_of_N (node_height cfg node1))
          (nat_of_N (node_height cfg node2)))).
Let lt_1 :
  max (nat_of_N (node_height cfg node1)) (nat_of_N (node_height cfg node2)) <
  S
    (max (nat_of_N (node_height cfg node1))
       (nat_of_N (node_height cfg node2))).
Proof.
  unfold lt in |- *.  apply le_n.
Qed.

Lemma BDDor_config_OK : BDDconfig_OK (fst BDDor).
Proof.
  exact
   (proj1 (BDDor_1_lemma _ gc_is_OK _ _ _ _ _ lt_1 cfg_OK ul_OK used1 used2)).
Qed.

Lemma BDDor_node_OK : config_node_OK (fst BDDor) (snd BDDor).
Proof.
  exact
   (proj1
      (proj2
         (BDDor_1_lemma _ gc_is_OK _ _ _ _ _ lt_1 cfg_OK ul_OK used1 used2))).
Qed.

Lemma BDDor_used_nodes_preserved : used_nodes_preserved cfg (fst BDDor) ul.
Proof.
  exact
   (proj1
      (proj2
         (proj2
            (BDDor_1_lemma _ gc_is_OK _ _ _ _ _ lt_1 cfg_OK ul_OK used1 used2)))).
Qed.

Lemma BDDor_is_or :
 bool_fun_eq (bool_fun_of_BDD (fst BDDor) (snd BDDor))
   (bool_fun_or (bool_fun_of_BDD cfg node1) (bool_fun_of_BDD cfg node2)).
Proof.
  exact
   (proj2
      (proj2
         (proj2
            (proj2
               (BDDor_1_lemma _ gc_is_OK _ _ _ _ _ lt_1 cfg_OK ul_OK used1
                  used2))))).
Qed.

Lemma BDDor_list_OK : used_list_OK (fst BDDor) ul.
Proof.
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.
  exact BDDor_used_nodes_preserved.
Qed.

Lemma BDDor_list_OK_cons : used_list_OK (fst BDDor) (snd BDDor :: ul).
Proof.
  apply node_OK_list_OK.  exact BDDor_node_OK.  exact BDDor_list_OK.
Qed.

Lemma BDDor_var_le :
 Nleb (node_height (fst BDDor) (snd BDDor))
   (BDDvar_max (node_height cfg node1) (node_height cfg node2)) = true.
Proof.
  exact
   (proj1
      (proj2
         (proj2
            (proj2
               (BDDor_1_lemma _ gc_is_OK _ _ _ _ _ lt_1 cfg_OK ul_OK used1
                  used2))))).
Qed.

                          End BDDor_results.



                       Section BDDimpl_results.



Variable cfg : BDDconfig.
Variable ul : list ad.
Variable node1 node2 : ad.

Hypothesis cfg_OK : BDDconfig_OK cfg.
Hypothesis ul_OK : used_list_OK cfg ul.
Hypothesis used1 : used_node' cfg ul node1.
Hypothesis used2 : used_node' cfg ul node2.

Definition BDDimpl :=
  match BDDneg cfg ul node1 with
  | (cfg1, node1') => BDDor cfg1 (node1' :: ul) node1' node2
  end.

Lemma BDDimpl_config_OK : BDDconfig_OK (fst BDDimpl).
Proof.
  unfold BDDimpl in |- *.  elim (prod_sum _ _ (BDDneg cfg ul node1)).  intros cfg1 H.
  elim H.  clear H.  intros node1' H.  rewrite H.  apply BDDor_config_OK.
  replace cfg1 with (fst (BDDneg cfg ul node1)).  apply BDDneg_config_OK.
  assumption.  assumption.  assumption.  rewrite H.  reflexivity.  
  replace cfg1 with (fst (BDDneg cfg ul node1)).
  replace node1' with (snd (BDDneg cfg ul node1)).  apply BDDneg_list_OK_cons.
  assumption.  assumption.  assumption.  rewrite H.  reflexivity.  rewrite H.
  reflexivity.  apply used_node'_cons_node_ul.  apply used_node'_cons_node'_ul.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.  
  replace cfg1 with (fst (BDDneg cfg ul node1)).
  apply BDDneg_used_nodes_preserved.  assumption.  assumption.  assumption.  
  rewrite H.  reflexivity.  assumption.  
Qed.

Lemma BDDimpl_node_OK : config_node_OK (fst BDDimpl) (snd BDDimpl).
Proof.
  unfold BDDimpl in |- *.  elim (prod_sum _ _ (BDDneg cfg ul node1)).  intros cfg1 H.
  elim H.  clear H.  intros node1' H.  rewrite H.  apply BDDor_node_OK.
  replace cfg1 with (fst (BDDneg cfg ul node1)).  apply BDDneg_config_OK.
  assumption.  assumption.  assumption.  rewrite H.  reflexivity.  
  replace cfg1 with (fst (BDDneg cfg ul node1)).
  replace node1' with (snd (BDDneg cfg ul node1)).  apply BDDneg_list_OK_cons.
  assumption.  assumption.  assumption.  rewrite H.  reflexivity.  rewrite H.
  reflexivity.  apply used_node'_cons_node_ul.  apply used_node'_cons_node'_ul.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.
  replace cfg1 with (fst (BDDneg cfg ul node1)).
  apply BDDneg_used_nodes_preserved.  assumption.  assumption.  assumption.  
  rewrite H.  reflexivity.  assumption.  
Qed.

Lemma BDDimpl_used_nodes_preserved :
 used_nodes_preserved cfg (fst BDDimpl) ul.
Proof.
  unfold BDDimpl in |- *.  elim (prod_sum _ _ (BDDneg cfg ul node1)).  intros cfg1 H.
  elim H.  clear H.  intros node1' H.  rewrite H.
  apply used_nodes_preserved_trans with (cfg2 := cfg1).  assumption.  
  replace cfg1 with (fst (BDDneg cfg ul node1)).
  apply BDDneg_used_nodes_preserved.  assumption.  assumption.  assumption.
  rewrite H.  reflexivity.  apply used_nodes_preserved_cons with (node := node1').
  apply BDDor_used_nodes_preserved.
  replace cfg1 with (fst (BDDneg cfg ul node1)).  apply BDDneg_config_OK.
  assumption.  assumption.  assumption.  rewrite H.  reflexivity.  
  replace cfg1 with (fst (BDDneg cfg ul node1)).
  replace node1' with (snd (BDDneg cfg ul node1)).  apply BDDneg_list_OK_cons.
  assumption.  assumption.  assumption.  rewrite H.  reflexivity.  rewrite H.
  reflexivity.  apply used_node'_cons_node_ul.  apply used_node'_cons_node'_ul.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.  
  replace cfg1 with (fst (BDDneg cfg ul node1)).
  apply BDDneg_used_nodes_preserved.  assumption.  assumption.  assumption.  
  rewrite H.  reflexivity.  assumption.  
Qed.

Lemma BDDimpl_is_impl :
 bool_fun_eq (bool_fun_of_BDD (fst BDDimpl) (snd BDDimpl))
   (bool_fun_impl (bool_fun_of_BDD cfg node1) (bool_fun_of_BDD cfg node2)).
Proof.
  unfold BDDimpl in |- *.  elim (prod_sum _ _ (BDDneg cfg ul node1)).  intros cfg1 H.
  elim H.  clear H.  intros node1' H.  rewrite H.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_or (bool_fun_of_BDD cfg1 node1')
                (bool_fun_of_BDD cfg1 node2)).
  apply BDDor_is_or.  replace cfg1 with (fst (BDDneg cfg ul node1)).
  apply BDDneg_config_OK.  assumption.  assumption.  assumption.  rewrite H.
  reflexivity.  replace cfg1 with (fst (BDDneg cfg ul node1)).
  replace node1' with (snd (BDDneg cfg ul node1)).  apply BDDneg_list_OK_cons.
  assumption.  assumption.  assumption.  rewrite H.  reflexivity.  rewrite H.
  reflexivity.  apply used_node'_cons_node_ul.  apply used_node'_cons_node'_ul.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.  
  replace cfg1 with (fst (BDDneg cfg ul node1)).
  apply BDDneg_used_nodes_preserved.  assumption.  assumption.  assumption.  
  rewrite H.  reflexivity.  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_or (bool_fun_neg (bool_fun_of_BDD cfg node1))
                (bool_fun_of_BDD cfg node2)).
  replace cfg1 with (fst (BDDneg cfg ul node1)).
  replace node1' with (snd (BDDneg cfg ul node1)).
  apply bool_fun_or_preserves_eq.  apply BDDneg_is_neg.  assumption.
  assumption.  assumption.  apply used_nodes_preserved'_bool_fun with (ul := ul).
  assumption.  apply BDDneg_config_OK.  assumption.  assumption.  assumption.
  apply BDDneg_used_nodes_preserved.  assumption.  assumption.  assumption.
  assumption.  assumption.  rewrite H.  reflexivity.  rewrite H.  reflexivity.
  apply bool_fun_eq_sym.  apply bool_fun_impl_lemma.  
Qed.

Lemma BDDimpl_list_OK : used_list_OK (fst BDDimpl) ul.
Proof.
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.
  exact BDDimpl_used_nodes_preserved.
Qed.

Lemma BDDimpl_list_OK_cons : used_list_OK (fst BDDimpl) (snd BDDimpl :: ul).
Proof.
  apply node_OK_list_OK.  apply BDDimpl_node_OK.  exact BDDimpl_list_OK.  
Qed.


                         End BDDimpl_results.



                        Section BDDand_results.


Variable cfg : BDDconfig.
Variable ul : list ad.
Variable node1 node2 : ad.

Hypothesis cfg_OK : BDDconfig_OK cfg.
Hypothesis ul_OK : used_list_OK cfg ul.
Hypothesis used1 : used_node' cfg ul node1.
Hypothesis used2 : used_node' cfg ul node2.

Definition BDDand :=
  match BDDneg cfg ul node1 with
  | (cfg1, node1') =>
      match BDDneg cfg1 (node1' :: ul) node2 with
      | (cfg2, node2') =>
          match BDDor cfg2 (node2' :: node1' :: ul) node1' node2' with
          | (cfg3, node3) => BDDneg cfg3 (node3 :: ul) node3
          end
      end
  end.

Lemma BDDand_config_OK : BDDconfig_OK (fst BDDand).
Proof.
  unfold BDDand in |- *.  elim (prod_sum _ _ (BDDneg cfg ul node1)).  intros cfg1 H.
  elim H.  clear H.  intros node1' H.  rewrite H.
  elim (prod_sum _ _ (BDDneg cfg1 (node1' :: ul) node2)).  intros cfg2 H0.
  elim H0.  clear H0.  intros node2' H0.  rewrite H0.
  elim (prod_sum _ _ (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  intros cfg3 H1.  elim H1.  clear H1.  intros node3 H1.  rewrite H1.
  cut (BDDconfig_OK cfg1).  cut (used_nodes_preserved cfg cfg1 ul).  intros.
  cut (used_list_OK cfg1 (node1' :: ul)).  intro.
  cut (used_node' cfg1 (node1' :: ul) node2).  intro.
  cut (BDDconfig_OK cfg2).  intro.
  cut (used_nodes_preserved cfg1 cfg2 (node1' :: ul)).  intro.
  cut (used_list_OK cfg2 (node2' :: node1' :: ul)).  intro.
  apply BDDneg_config_OK.
  replace cfg3 with (fst (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  apply BDDor_config_OK.  assumption.  assumption.
  apply used_node'_cons_node'_ul.  apply used_node'_cons_node_ul.
  apply used_node'_cons_node_ul.  rewrite H1.  reflexivity.
  apply node_OK_list_OK.
  replace cfg3 with (fst (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  replace node3 with
   (snd (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  apply BDDor_node_OK.  assumption.  assumption.  apply used_node'_cons_node'_ul.
  apply used_node'_cons_node_ul.  apply used_node'_cons_node_ul.  rewrite H1.
  reflexivity.  rewrite H1.  reflexivity.  apply cons_OK_list_OK with (node := node1').
  apply cons_OK_list_OK with (node := node2').
  replace cfg3 with (fst (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  apply BDDor_list_OK.  assumption.  assumption.  apply used_node'_cons_node'_ul.
  apply used_node'_cons_node_ul.  apply used_node'_cons_node_ul.  rewrite H1.
  reflexivity.  apply used_node'_cons_node_ul.  
  replace cfg2 with (fst (BDDneg cfg1 (node1' :: ul) node2)).
  replace node2' with (snd (BDDneg cfg1 (node1' :: ul) node2)).
  apply BDDneg_list_OK_cons.  assumption.  assumption.  assumption.  rewrite H0.
  reflexivity.  rewrite H0.  reflexivity.  
  replace cfg2 with (fst (BDDneg cfg1 (node1' :: ul) node2)).
  apply BDDneg_used_nodes_preserved.  assumption.  assumption.  assumption.  
  rewrite H0.  reflexivity.
  replace cfg2 with (fst (BDDneg cfg1 (node1' :: ul) node2)).
  apply BDDneg_config_OK.  assumption.  assumption.  assumption.  rewrite H0.
  reflexivity.  apply used_node'_cons_node'_ul.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.  assumption.
  assumption.  replace cfg1 with (fst (BDDneg cfg ul node1)).
  replace node1' with (snd (BDDneg cfg ul node1)).  apply BDDneg_list_OK_cons.
  assumption.  assumption.  assumption.  rewrite H.  reflexivity.  rewrite H.
  reflexivity.  replace cfg1 with (fst (BDDneg cfg ul node1)).
  apply BDDneg_used_nodes_preserved.  assumption.  assumption.  assumption.
  rewrite H.  reflexivity.  replace cfg1 with (fst (BDDneg cfg ul node1)).
  apply BDDneg_config_OK.  assumption.  assumption.  assumption.  rewrite H.
  reflexivity.
Qed.

Lemma BDDand_node_OK : config_node_OK (fst BDDand) (snd BDDand).
Proof.
  unfold BDDand in |- *.  elim (prod_sum _ _ (BDDneg cfg ul node1)).  intros cfg1 H.
  elim H.  clear H.  intros node1' H.  rewrite H.
  elim (prod_sum _ _ (BDDneg cfg1 (node1' :: ul) node2)).  intros cfg2 H0.
  elim H0.  clear H0.  intros node2' H0.  rewrite H0.
  elim (prod_sum _ _ (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  intros cfg3 H1.  elim H1.  clear H1.  intros node3 H1.  rewrite H1.
  cut (BDDconfig_OK cfg1).  cut (used_nodes_preserved cfg cfg1 ul).  intros.
  cut (used_list_OK cfg1 (node1' :: ul)).  intro.
  cut (used_node' cfg1 (node1' :: ul) node2).  intro.
  cut (BDDconfig_OK cfg2).  intro.
  cut (used_nodes_preserved cfg1 cfg2 (node1' :: ul)).  intro.
  cut (used_list_OK cfg2 (node2' :: node1' :: ul)).  intro.


  apply BDDneg_node_OK.


  replace cfg3 with (fst (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  apply BDDor_config_OK.  assumption.  assumption.
  apply used_node'_cons_node'_ul.  apply used_node'_cons_node_ul.
  apply used_node'_cons_node_ul.  rewrite H1.  reflexivity.
  apply node_OK_list_OK.
  replace cfg3 with (fst (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  replace node3 with
   (snd (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  apply BDDor_node_OK.  assumption.  assumption.  apply used_node'_cons_node'_ul.
  apply used_node'_cons_node_ul.  apply used_node'_cons_node_ul.  rewrite H1.
  reflexivity.  rewrite H1.  reflexivity.  apply cons_OK_list_OK with (node := node1').
  apply cons_OK_list_OK with (node := node2').
  replace cfg3 with (fst (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  apply BDDor_list_OK.  assumption.  assumption.  apply used_node'_cons_node'_ul.
  apply used_node'_cons_node_ul.  apply used_node'_cons_node_ul.  rewrite H1.
  reflexivity.  apply used_node'_cons_node_ul.
  replace cfg2 with (fst (BDDneg cfg1 (node1' :: ul) node2)).
  replace node2' with (snd (BDDneg cfg1 (node1' :: ul) node2)).
  apply BDDneg_list_OK_cons.  assumption.  assumption.  assumption.  rewrite H0.
  reflexivity.  rewrite H0.  reflexivity.
  replace cfg2 with (fst (BDDneg cfg1 (node1' :: ul) node2)).
  apply BDDneg_used_nodes_preserved.  assumption.  assumption.  assumption.
  rewrite H0.  reflexivity.
  replace cfg2 with (fst (BDDneg cfg1 (node1' :: ul) node2)).
  apply BDDneg_config_OK.  assumption.  assumption.  assumption.  rewrite H0.
  reflexivity.  apply used_node'_cons_node'_ul.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.  assumption.
  assumption.  replace cfg1 with (fst (BDDneg cfg ul node1)).
  replace node1' with (snd (BDDneg cfg ul node1)).  apply BDDneg_list_OK_cons.
  assumption.  assumption.  assumption.  rewrite H.  reflexivity.  rewrite H.
  reflexivity.  replace cfg1 with (fst (BDDneg cfg ul node1)).
  apply BDDneg_used_nodes_preserved.  assumption.  assumption.  assumption.
  rewrite H.  reflexivity.  replace cfg1 with (fst (BDDneg cfg ul node1)).
  apply BDDneg_config_OK.  assumption.  assumption.  assumption.  rewrite H.
  reflexivity.

Qed.

Lemma BDDand_used_nodes_preserved : used_nodes_preserved cfg (fst BDDand) ul.
Proof.
  unfold BDDand in |- *.  elim (prod_sum _ _ (BDDneg cfg ul node1)).  intros cfg1 H.
  elim H.  clear H.  intros node1' H.  rewrite H.
  elim (prod_sum _ _ (BDDneg cfg1 (node1' :: ul) node2)).  intros cfg2 H0.
  elim H0.  clear H0.  intros node2' H0.  rewrite H0.
  elim (prod_sum _ _ (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  intros cfg3 H1.  elim H1.  clear H1.  intros node3 H1.  rewrite H1.
  cut (BDDconfig_OK cfg1).  cut (used_nodes_preserved cfg cfg1 ul).  intros.
  cut (used_list_OK cfg1 (node1' :: ul)).  intro.
  cut (used_node' cfg1 (node1' :: ul) node2).  intro.
  cut (BDDconfig_OK cfg2).  intro.
  cut (used_nodes_preserved cfg1 cfg2 (node1' :: ul)).  intro.
  cut (used_list_OK cfg2 (node2' :: node1' :: ul)).  intro.


  apply used_nodes_preserved_trans with (cfg2 := cfg3).  assumption.  
  apply used_nodes_preserved_trans with (cfg2 := cfg1).  assumption.  assumption.
  apply used_nodes_preserved_cons with (node := node1').
  apply used_nodes_preserved_trans with (cfg2 := cfg2).  assumption.  assumption.
  apply used_nodes_preserved_cons with (node := node2').
  replace cfg3 with (fst (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  apply BDDor_used_nodes_preserved.  assumption.  assumption.  
  apply used_node'_cons_node'_ul.  apply used_node'_cons_node_ul.  
  apply used_node'_cons_node_ul.  rewrite H1.  reflexivity.  
  apply used_nodes_preserved_cons with (node := node3).
  apply BDDneg_used_nodes_preserved.


  replace cfg3 with (fst (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  apply BDDor_config_OK.  assumption.  assumption.
  apply used_node'_cons_node'_ul.  apply used_node'_cons_node_ul.
  apply used_node'_cons_node_ul.  rewrite H1.  reflexivity.
  apply node_OK_list_OK.
  replace cfg3 with (fst (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  replace node3 with
   (snd (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  apply BDDor_node_OK.  assumption.  assumption.  apply used_node'_cons_node'_ul.
  apply used_node'_cons_node_ul.  apply used_node'_cons_node_ul.  rewrite H1.
  reflexivity.  rewrite H1.  reflexivity.  apply cons_OK_list_OK with (node := node1').
  apply cons_OK_list_OK with (node := node2').
  replace cfg3 with (fst (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  apply BDDor_list_OK.  assumption.  assumption.  apply used_node'_cons_node'_ul.
  apply used_node'_cons_node_ul.  apply used_node'_cons_node_ul.  rewrite H1.
  reflexivity.  apply used_node'_cons_node_ul.
  replace cfg2 with (fst (BDDneg cfg1 (node1' :: ul) node2)).
  replace node2' with (snd (BDDneg cfg1 (node1' :: ul) node2)).
  apply BDDneg_list_OK_cons.  assumption.  assumption.  assumption.  rewrite H0.
  reflexivity.  rewrite H0.  reflexivity.
  replace cfg2 with (fst (BDDneg cfg1 (node1' :: ul) node2)).
  apply BDDneg_used_nodes_preserved.  assumption.  assumption.  assumption.
  rewrite H0.  reflexivity.
  replace cfg2 with (fst (BDDneg cfg1 (node1' :: ul) node2)).
  apply BDDneg_config_OK.  assumption.  assumption.  assumption.  rewrite H0.
  reflexivity.  apply used_node'_cons_node'_ul.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.  assumption.
  assumption.  replace cfg1 with (fst (BDDneg cfg ul node1)).
  replace node1' with (snd (BDDneg cfg ul node1)).  apply BDDneg_list_OK_cons.
  assumption.  assumption.  assumption.  rewrite H.  reflexivity.  rewrite H.
  reflexivity.  replace cfg1 with (fst (BDDneg cfg ul node1)).
  apply BDDneg_used_nodes_preserved.  assumption.  assumption.  assumption.
  rewrite H.  reflexivity.  replace cfg1 with (fst (BDDneg cfg ul node1)).
  apply BDDneg_config_OK.  assumption.  assumption.  assumption.  rewrite H.
  reflexivity.
Qed.

Lemma BDDand_is_and :
 bool_fun_eq (bool_fun_of_BDD (fst BDDand) (snd BDDand))
   (bool_fun_and (bool_fun_of_BDD cfg node1) (bool_fun_of_BDD cfg node2)).
Proof.
  unfold BDDand in |- *.  elim (prod_sum _ _ (BDDneg cfg ul node1)).  intros cfg1 H.
  elim H.  clear H.  intros node1' H.  rewrite H.
  elim (prod_sum _ _ (BDDneg cfg1 (node1' :: ul) node2)).  intros cfg2 H0.
  elim H0.  clear H0.  intros node2' H0.  rewrite H0.
  elim (prod_sum _ _ (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  intros cfg3 H1.  elim H1.  clear H1.  intros node3 H1.  rewrite H1.
  cut (BDDconfig_OK cfg1).  cut (used_nodes_preserved cfg cfg1 ul).  intros.
  cut (used_list_OK cfg1 (node1' :: ul)).  intro.
  cut (used_node' cfg1 (node1' :: ul) node2).  intro.
  cut (BDDconfig_OK cfg2).  intro.
  cut (used_nodes_preserved cfg1 cfg2 (node1' :: ul)).  intro.
  cut (used_list_OK cfg2 (node2' :: node1' :: ul)).  intro.


  cut
   (bool_fun_eq
      (bool_fun_of_BDD (fst (BDDneg cfg3 (node3 :: ul) node3))
         (snd (BDDneg cfg3 (node3 :: ul) node3)))
      (bool_fun_neg (bool_fun_of_BDD cfg3 node3))).  intro.
  apply
   bool_fun_eq_trans with (bf2 := bool_fun_neg (bool_fun_of_BDD cfg3 node3)).
  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_neg
                (bool_fun_or (bool_fun_of_BDD cfg2 node1')
                   (bool_fun_of_BDD cfg2 node2'))).
  apply bool_fun_neg_preserves_eq.  replace cfg3 with (fst (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  replace node3 with
   (snd (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  apply BDDor_is_or.  assumption.  assumption.  apply used_node'_cons_node'_ul.
  apply used_node'_cons_node_ul.  apply used_node'_cons_node_ul.  rewrite H1.
  reflexivity.  rewrite H1.  reflexivity.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_neg
                (bool_fun_or (bool_fun_neg (bool_fun_of_BDD cfg node1))
                   (bool_fun_neg (bool_fun_of_BDD cfg node2)))).
  apply bool_fun_neg_preserves_eq.  apply bool_fun_or_preserves_eq.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg1 node1').
  apply used_nodes_preserved'_bool_fun with (ul := node1' :: ul).  assumption.
  assumption.  assumption.  assumption.  apply used_node'_cons_node_ul.
  replace cfg1 with (fst (BDDneg cfg ul node1)).
  replace node1' with (snd (BDDneg cfg ul node1)).  apply BDDneg_is_neg.
  assumption.  assumption.  assumption.  rewrite H.  reflexivity.  rewrite H.
  reflexivity.  apply
   bool_fun_eq_trans with (bf2 := bool_fun_neg (bool_fun_of_BDD cfg1 node2)).
  replace cfg2 with (fst (BDDneg cfg1 (node1' :: ul) node2)).
  replace node2' with (snd (BDDneg cfg1 (node1' :: ul) node2)).
  apply BDDneg_is_neg.  assumption.  assumption.  assumption.  rewrite H0.
  reflexivity.  rewrite H0.  reflexivity.  apply bool_fun_neg_preserves_eq.
  replace cfg1 with (fst (BDDneg cfg ul node1)).
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  rewrite H.
  assumption.  rewrite H.  assumption.  assumption.  assumption.  rewrite H.
  reflexivity.  apply bool_fun_eq_sym.  apply bool_fun_and_lemma.
  apply BDDneg_is_neg.


  replace cfg3 with (fst (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  apply BDDor_config_OK.  assumption.  assumption.
  apply used_node'_cons_node'_ul.  apply used_node'_cons_node_ul.
  apply used_node'_cons_node_ul.  rewrite H1.  reflexivity.
  apply node_OK_list_OK.
  replace cfg3 with (fst (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  replace node3 with
   (snd (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  apply BDDor_node_OK.  assumption.  assumption.  apply used_node'_cons_node'_ul.
  apply used_node'_cons_node_ul.  apply used_node'_cons_node_ul.  rewrite H1.
  reflexivity.  rewrite H1.  reflexivity.  apply cons_OK_list_OK with (node := node1').
  apply cons_OK_list_OK with (node := node2').
  replace cfg3 with (fst (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  apply BDDor_list_OK.  assumption.  assumption.  apply used_node'_cons_node'_ul.
  apply used_node'_cons_node_ul.  apply used_node'_cons_node_ul.  rewrite H1.
  reflexivity.  apply used_node'_cons_node_ul.
  replace cfg2 with (fst (BDDneg cfg1 (node1' :: ul) node2)).
  replace node2' with (snd (BDDneg cfg1 (node1' :: ul) node2)).
  apply BDDneg_list_OK_cons.  assumption.  assumption.  assumption.  rewrite H0.
  reflexivity.  rewrite H0.  reflexivity.
  replace cfg2 with (fst (BDDneg cfg1 (node1' :: ul) node2)).
  apply BDDneg_used_nodes_preserved.  assumption.  assumption.  assumption.
  rewrite H0.  reflexivity.
  replace cfg2 with (fst (BDDneg cfg1 (node1' :: ul) node2)).
  apply BDDneg_config_OK.  assumption.  assumption.  assumption.  rewrite H0.
  reflexivity.  apply used_node'_cons_node'_ul.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.  assumption.
  assumption.  replace cfg1 with (fst (BDDneg cfg ul node1)).
  replace node1' with (snd (BDDneg cfg ul node1)).  apply BDDneg_list_OK_cons.
  assumption.  assumption.  assumption.  rewrite H.  reflexivity.  rewrite H.
  reflexivity.  replace cfg1 with (fst (BDDneg cfg ul node1)).
  apply BDDneg_used_nodes_preserved.  assumption.  assumption.  assumption.
  rewrite H.  reflexivity.  replace cfg1 with (fst (BDDneg cfg ul node1)).
  apply BDDneg_config_OK.  assumption.  assumption.  assumption.  rewrite H.
  reflexivity.
Qed.

Lemma BDDand_list_OK : used_list_OK (fst BDDand) ul.
Proof.
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.  
  exact BDDand_used_nodes_preserved.
Qed.

Lemma BDDand_list_OK_cons : used_list_OK (fst BDDand) (snd BDDand :: ul).
Proof.
  apply node_OK_list_OK.  apply BDDand_node_OK.  exact BDDand_list_OK.  
Qed.

Lemma BDDand_var_le :
 Nleb (node_height (fst BDDand) (snd BDDand))
   (BDDvar_max (node_height cfg node1) (node_height cfg node2)) = true.
Proof.
  unfold BDDand in |- *.  elim (prod_sum _ _ (BDDneg cfg ul node1)).  intros cfg1 H.
  elim H.  clear H.  intros node1' H.  rewrite H.
  elim (prod_sum _ _ (BDDneg cfg1 (node1' :: ul) node2)).  intros cfg2 H0.
  elim H0.  clear H0.  intros node2' H0.  rewrite H0.
  elim (prod_sum _ _ (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  intros cfg3 H1.  elim H1.  clear H1.  intros node3 H1.  rewrite H1.
  cut (BDDconfig_OK cfg1).  cut (used_nodes_preserved cfg cfg1 ul).  intros.
  cut (used_list_OK cfg1 (node1' :: ul)).  intro.
  cut (used_node' cfg1 (node1' :: ul) node2).  intro.  cut (BDDconfig_OK cfg2).
  intro.  cut (used_nodes_preserved cfg1 cfg2 (node1' :: ul)).  intro.
  cut (used_list_OK cfg2 (node2' :: node1' :: ul)).  intro.
  replace
   (node_height (fst (BDDneg cfg3 (node3 :: ul) node3))
      (snd (BDDneg cfg3 (node3 :: ul) node3))) with 
   (node_height cfg3 node3).
  replace (node_height cfg node1) with (node_height cfg2 node1').
  replace (node_height cfg node2) with (node_height cfg2 node2').
  replace cfg3 with (fst (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  replace node3 with
   (snd (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  apply BDDor_var_le.  assumption.  assumption.  apply used_node'_cons_node'_ul.
  apply used_node'_cons_node_ul.  apply used_node'_cons_node_ul.  rewrite H1.
  reflexivity.  rewrite H1.  reflexivity.  
  transitivity (node_height cfg1 node2).
  replace cfg2 with (fst (BDDneg cfg1 (node1' :: ul) node2)).
  replace node2' with (snd (BDDneg cfg1 (node1' :: ul) node2)).
  apply Neqb_complete.  apply BDDneg_var_eq.  assumption.  assumption.  
  assumption.  rewrite H0.  reflexivity.  rewrite H0.  reflexivity.  
  apply Neqb_complete.  replace cfg1 with (fst (BDDneg cfg ul node1)).
  apply used_nodes_preserved'_node_height_eq with (ul := ul).  assumption.  
  apply BDDneg_config_OK.  assumption.  assumption.  assumption.  
  apply BDDneg_used_nodes_preserved.  assumption.  assumption.  assumption.
  assumption.  assumption.  rewrite H.  reflexivity.  
  transitivity (node_height cfg1 node1').  apply Neqb_complete.
  replace cfg2 with (fst (BDDneg cfg1 (node1' :: ul) node2)).
  apply used_nodes_preserved'_node_height_eq with (ul := node1' :: ul).
  assumption.  apply BDDneg_config_OK.  assumption.  assumption.  assumption.  
  apply BDDneg_used_nodes_preserved.  assumption.  assumption.  assumption.  
  assumption.  apply used_node'_cons_node_ul.  rewrite H0.  reflexivity.  
  replace cfg1 with (fst (BDDneg cfg ul node1)).
  replace node1' with (snd (BDDneg cfg ul node1)).  apply Neqb_complete.
  apply BDDneg_var_eq.  assumption.  assumption.  assumption.  rewrite H.
  reflexivity.  rewrite H.  reflexivity.  symmetry  in |- *.  apply Neqb_complete.
  apply BDDneg_var_eq.
  replace cfg3 with (fst (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  apply BDDor_config_OK.  assumption.  assumption.  apply used_node'_cons_node'_ul.
  apply used_node'_cons_node_ul.  apply used_node'_cons_node_ul.  rewrite H1.
  reflexivity.  apply node_OK_list_OK.
  replace cfg3 with (fst (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  replace node3 with
   (snd (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  apply BDDor_node_OK.  assumption.  assumption.  apply used_node'_cons_node'_ul.
  apply used_node'_cons_node_ul.  apply used_node'_cons_node_ul.  rewrite H1.
  reflexivity.  rewrite H1.  reflexivity.  
  replace cfg3 with (fst (BDDor cfg2 (node2' :: node1' :: ul) node1' node2')).
  apply cons_OK_list_OK with (node := node1').  apply cons_OK_list_OK with (node := node2').
  apply BDDor_list_OK.  assumption.  assumption.  apply used_node'_cons_node'_ul.
  apply used_node'_cons_node_ul.  apply used_node'_cons_node_ul.  rewrite H1.
  reflexivity.  apply used_node'_cons_node_ul.  
  replace cfg2 with (fst (BDDneg cfg1 (node1' :: ul) node2)).
  replace node2' with (snd (BDDneg cfg1 (node1' :: ul) node2)).
  apply BDDneg_list_OK_cons.  assumption.  assumption.  assumption.  rewrite H0.
  reflexivity.  rewrite H0.  reflexivity.
  replace cfg2 with (fst (BDDneg cfg1 (node1' :: ul) node2)).
  apply BDDneg_used_nodes_preserved.  assumption.  assumption.  assumption.
  rewrite H0.  reflexivity.
  replace cfg2 with (fst (BDDneg cfg1 (node1' :: ul) node2)).
  apply BDDneg_config_OK.  assumption.  assumption.  assumption.  rewrite H0.
  reflexivity.  apply used_node'_cons_node'_ul.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.  assumption.
  assumption.  replace cfg1 with (fst (BDDneg cfg ul node1)).
  replace node1' with (snd (BDDneg cfg ul node1)).  apply BDDneg_list_OK_cons.
  assumption.  assumption.  assumption.  rewrite H.  reflexivity.  rewrite H.
  reflexivity.  replace cfg1 with (fst (BDDneg cfg ul node1)).
  apply BDDneg_used_nodes_preserved.  assumption.  assumption.  assumption.
  rewrite H.  reflexivity.  replace cfg1 with (fst (BDDneg cfg ul node1)).
  apply BDDneg_config_OK.  assumption.  assumption.  assumption.  rewrite H.
  reflexivity.
Qed.


                         End BDDand_results.



                       Section BDDiff_results.




Variable cfg : BDDconfig.
Variable ul : list ad.
Variable node1 node2 : ad.

Hypothesis cfg_OK : BDDconfig_OK cfg.
Hypothesis ul_OK : used_list_OK cfg ul.
Hypothesis used1 : used_node' cfg ul node1.
Hypothesis used2 : used_node' cfg ul node2.

Definition BDDiff :=
  match BDDor cfg ul node1 node2 with
  | (cfg1, node3) =>
      match BDDand cfg1 (node3 :: ul) node1 node2 with
      | (cfg2, node4) => BDDimpl cfg2 (node4 :: node3 :: ul) node3 node4
      end
  end.

Lemma BDDiff_config_OK : BDDconfig_OK (fst BDDiff).
Proof.
  unfold BDDiff in |- *.  elim (prod_sum _ _ (BDDor cfg ul node1 node2)).
  intros cfg1 H.  elim H.  clear H.  intros node3 H.  rewrite H.
  elim (prod_sum _ _ (BDDand cfg1 (node3 :: ul) node1 node2)).
  intros cfg2 H0.  elim H0.  clear H0.  intros node4 H0.  rewrite H0.
  cut (BDDconfig_OK cfg1).  intro.  cut (used_nodes_preserved cfg cfg1 ul).
  intro.  cut (used_list_OK cfg1 (node3 :: ul)).  intro.
  cut (used_node' cfg1 (node3 :: ul) node1).
  cut (used_node' cfg1 (node3 :: ul) node2).  intros.
  cut (BDDconfig_OK cfg2).  intro.
  cut (used_nodes_preserved cfg1 cfg2 (node3 :: ul)).  intro.
  cut (used_list_OK cfg2 (node4 :: node3 :: ul)).  intro.
  apply BDDimpl_config_OK.
  replace cfg2 with (fst (BDDand cfg1 (node3 :: ul) node1 node2)).
  apply BDDand_config_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H0.  reflexivity.  assumption.  apply used_node'_cons_node'_ul.
  apply used_node'_cons_node_ul.  apply used_node'_cons_node_ul.  
  apply node_OK_list_OK.
  replace cfg2 with (fst (BDDand cfg1 (node3 :: ul) node1 node2)).
  replace node4 with (snd (BDDand cfg1 (node3 :: ul) node1 node2)).
  apply BDDand_node_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H0.  reflexivity.  rewrite H0.  reflexivity.  
  apply used_nodes_preserved_list_OK with (cfg := cfg1).  assumption.  assumption.
  replace cfg2 with (fst (BDDand cfg1 (node3 :: ul) node1 node2)).
  apply BDDand_used_nodes_preserved.  assumption.  assumption.  assumption.
  assumption.  rewrite H0.  reflexivity.  
  replace cfg2 with (fst (BDDand cfg1 (node3 :: ul) node1 node2)).
  apply BDDand_config_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H0.  reflexivity.  apply used_node'_cons_node'_ul.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.  assumption.
  assumption.  apply used_node'_cons_node'_ul.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.  assumption.
  assumption.  apply node_OK_list_OK.
  replace cfg1 with (fst (BDDor cfg ul node1 node2)).
  replace node3 with (snd (BDDor cfg ul node1 node2)).  apply BDDor_node_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H.  reflexivity.
  rewrite H.  reflexivity.  apply used_nodes_preserved_list_OK with (cfg := cfg).
  assumption.  assumption.  replace cfg1 with (fst (BDDor cfg ul node1 node2)).
  apply BDDor_used_nodes_preserved.  assumption.  assumption.  assumption.  
  assumption.  rewrite H.  reflexivity.
  replace cfg1 with (fst (BDDor cfg ul node1 node2)).  apply BDDor_config_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H.  reflexivity.
Qed.

Lemma BDDiff_node_OK : config_node_OK (fst BDDiff) (snd BDDiff).
Proof.
  unfold BDDiff in |- *.  elim (prod_sum _ _ (BDDor cfg ul node1 node2)).
  intros cfg1 H.  elim H.  clear H.  intros node3 H.  rewrite H.
  elim (prod_sum _ _ (BDDand cfg1 (node3 :: ul) node1 node2)).
  intros cfg2 H0.  elim H0.  clear H0.  intros node4 H0.  rewrite H0.
  cut (BDDconfig_OK cfg1).  intro.  cut (used_nodes_preserved cfg cfg1 ul).
  intro.  cut (used_list_OK cfg1 (node3 :: ul)).  intro.
  cut (used_node' cfg1 (node3 :: ul) node1).
  cut (used_node' cfg1 (node3 :: ul) node2).  intros.
  cut (BDDconfig_OK cfg2).  intro.
  cut (used_nodes_preserved cfg1 cfg2 (node3 :: ul)).  intro.
  cut (used_list_OK cfg2 (node4 :: node3 :: ul)).  intro.
  apply BDDimpl_node_OK.
  replace cfg2 with (fst (BDDand cfg1 (node3 :: ul) node1 node2)).
  apply BDDand_config_OK.  assumption.  assumption.  assumption.  assumption.  
  rewrite H0.  reflexivity.  assumption.  apply used_node'_cons_node'_ul.
  apply used_node'_cons_node_ul.  apply used_node'_cons_node_ul.  
  apply node_OK_list_OK.
  replace cfg2 with (fst (BDDand cfg1 (node3 :: ul) node1 node2)).
  replace node4 with (snd (BDDand cfg1 (node3 :: ul) node1 node2)).
  apply BDDand_node_OK.  assumption.  assumption.  assumption.  assumption.  
  rewrite H0.  reflexivity.  rewrite H0.  reflexivity.  
  apply used_nodes_preserved_list_OK with (cfg := cfg1).  assumption.  assumption.  
  replace cfg2 with (fst (BDDand cfg1 (node3 :: ul) node1 node2)).
  apply BDDand_used_nodes_preserved.  assumption.  assumption.  assumption.
  assumption.  rewrite H0.  reflexivity.  
  replace cfg2 with (fst (BDDand cfg1 (node3 :: ul) node1 node2)).
  apply BDDand_config_OK.  assumption.  assumption.  assumption.  assumption.  
  rewrite H0.  reflexivity.  apply used_node'_cons_node'_ul.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.  assumption.
  assumption.  apply used_node'_cons_node'_ul.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.  assumption.
  assumption.  apply node_OK_list_OK.
  replace cfg1 with (fst (BDDor cfg ul node1 node2)).
  replace node3 with (snd (BDDor cfg ul node1 node2)).  apply BDDor_node_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H.  reflexivity.
  rewrite H.  reflexivity.  apply used_nodes_preserved_list_OK with (cfg := cfg).
  assumption.  assumption.  replace cfg1 with (fst (BDDor cfg ul node1 node2)).
  apply BDDor_used_nodes_preserved.  assumption.  assumption.  assumption.  
  assumption.  rewrite H.  reflexivity.
  replace cfg1 with (fst (BDDor cfg ul node1 node2)).  apply BDDor_config_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H.  reflexivity.
Qed.

Lemma BDDiff_used_nodes_preserved : used_nodes_preserved cfg (fst BDDiff) ul.
Proof.
  unfold BDDiff in |- *.  elim (prod_sum _ _ (BDDor cfg ul node1 node2)).
  intros cfg1 H.  elim H.  clear H.  intros node3 H.  rewrite H.
  elim (prod_sum _ _ (BDDand cfg1 (node3 :: ul) node1 node2)).
  intros cfg2 H0.  elim H0.  clear H0.  intros node4 H0.  rewrite H0.
  cut (BDDconfig_OK cfg1).  intro.  cut (used_nodes_preserved cfg cfg1 ul).
  intro.  cut (used_list_OK cfg1 (node3 :: ul)).  intro.
  cut (used_node' cfg1 (node3 :: ul) node1).
  cut (used_node' cfg1 (node3 :: ul) node2).  intros.
  cut (BDDconfig_OK cfg2).  intro.
  cut (used_nodes_preserved cfg1 cfg2 (node3 :: ul)).  intro.
  cut (used_list_OK cfg2 (node4 :: node3 :: ul)).  intro.
  apply used_nodes_preserved_trans with (cfg2 := cfg1).  assumption.  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfg2).  assumption.  
  apply used_nodes_preserved_cons with (node := node3).  assumption.  
  apply used_nodes_preserved_cons with (node := node3).
  apply used_nodes_preserved_cons with (node := node4).
  apply BDDimpl_used_nodes_preserved.
  replace cfg2 with (fst (BDDand cfg1 (node3 :: ul) node1 node2)).
  apply BDDand_config_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H0.  reflexivity.  assumption.  apply used_node'_cons_node'_ul.
  apply used_node'_cons_node_ul.  apply used_node'_cons_node_ul.
  apply node_OK_list_OK.
  replace cfg2 with (fst (BDDand cfg1 (node3 :: ul) node1 node2)).
  replace node4 with (snd (BDDand cfg1 (node3 :: ul) node1 node2)).
  apply BDDand_node_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H0.  reflexivity.  rewrite H0.  reflexivity.
  apply used_nodes_preserved_list_OK with (cfg := cfg1).  assumption.  assumption.
  replace cfg2 with (fst (BDDand cfg1 (node3 :: ul) node1 node2)).
  apply BDDand_used_nodes_preserved.  assumption.  assumption.  assumption.
  assumption.  rewrite H0.  reflexivity.
  replace cfg2 with (fst (BDDand cfg1 (node3 :: ul) node1 node2)).
  apply BDDand_config_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H0.  reflexivity.  apply used_node'_cons_node'_ul.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.  assumption.
  assumption.  apply used_node'_cons_node'_ul.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.  assumption.
  assumption.  apply node_OK_list_OK.
  replace cfg1 with (fst (BDDor cfg ul node1 node2)).
  replace node3 with (snd (BDDor cfg ul node1 node2)).  apply BDDor_node_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H.  reflexivity.
  rewrite H.  reflexivity.  apply used_nodes_preserved_list_OK with (cfg := cfg).
  assumption.  assumption.  replace cfg1 with (fst (BDDor cfg ul node1 node2)).
  apply BDDor_used_nodes_preserved.  assumption.  assumption.  assumption.
  assumption.  rewrite H.  reflexivity.
  replace cfg1 with (fst (BDDor cfg ul node1 node2)).  apply BDDor_config_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H.  reflexivity.
Qed.

Lemma BDDiff_is_iff :
 bool_fun_eq (bool_fun_of_BDD (fst BDDiff) (snd BDDiff))
   (bool_fun_iff (bool_fun_of_BDD cfg node1) (bool_fun_of_BDD cfg node2)).
Proof.
  unfold BDDiff in |- *.  elim (prod_sum _ _ (BDDor cfg ul node1 node2)).
  intros cfg1 H.  elim H.  clear H.  intros node3 H.  rewrite H.
  elim (prod_sum _ _ (BDDand cfg1 (node3 :: ul) node1 node2)).
  intros cfg2 H0.  elim H0.  clear H0.  intros node4 H0.  rewrite H0.
  cut (BDDconfig_OK cfg1).  intro.  cut (used_nodes_preserved cfg cfg1 ul).
  intro.  cut (used_list_OK cfg1 (node3 :: ul)).  intro.
  cut (used_node' cfg1 (node3 :: ul) node1).
  cut (used_node' cfg1 (node3 :: ul) node2).  intros.
  cut (BDDconfig_OK cfg2).  intro.
  cut (used_nodes_preserved cfg1 cfg2 (node3 :: ul)).  intro.
  cut (used_list_OK cfg2 (node4 :: node3 :: ul)).  intro.
  cut
   (bool_fun_eq
      (bool_fun_of_BDD
         (fst (BDDimpl cfg2 (node4 :: node3 :: ul) node3 node4))
         (snd (BDDimpl cfg2 (node4 :: node3 :: ul) node3 node4)))
      (bool_fun_impl (bool_fun_of_BDD cfg2 node3)
         (bool_fun_of_BDD cfg2 node4))).  intro.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_impl (bool_fun_of_BDD cfg2 node3)
                (bool_fun_of_BDD cfg2 node4)).  assumption.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_impl
                (bool_fun_or (bool_fun_of_BDD cfg node1)
                   (bool_fun_of_BDD cfg node2))
                (bool_fun_and (bool_fun_of_BDD cfg node1)
                   (bool_fun_of_BDD cfg node2))).
  apply bool_fun_impl_preserves_eq.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg1 node3).
  apply used_nodes_preserved'_bool_fun with (ul := node3 :: ul).  assumption.
  assumption.  assumption.  assumption.  apply used_node'_cons_node_ul.  
  replace cfg1 with (fst (BDDor cfg ul node1 node2)).
  replace node3 with (snd (BDDor cfg ul node1 node2)).  apply BDDor_is_or.
  assumption.  assumption.  assumption.  assumption.  rewrite H.  reflexivity.
  rewrite H.  reflexivity.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_and (bool_fun_of_BDD cfg1 node1)
                (bool_fun_of_BDD cfg1 node2)).
  replace cfg2 with (fst (BDDand cfg1 (node3 :: ul) node1 node2)).
  replace node4 with (snd (BDDand cfg1 (node3 :: ul) node1 node2)).
  apply BDDand_is_and.  assumption.  assumption.  assumption.  assumption.  
  rewrite H0.  reflexivity.  rewrite H0.  reflexivity.  
  apply bool_fun_and_preserves_eq.
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  assumption.
  assumption.  assumption.  assumption.
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  assumption.
  assumption.  assumption.  assumption.  apply bool_fun_eq_sym.
  apply bool_fun_iff_lemma.  apply BDDimpl_is_impl.
  replace cfg2 with (fst (BDDand cfg1 (node3 :: ul) node1 node2)).
  apply BDDand_config_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H0.  reflexivity.  assumption.  apply used_node'_cons_node'_ul.
  apply used_node'_cons_node_ul.  apply used_node'_cons_node_ul.
  apply node_OK_list_OK.
  replace cfg2 with (fst (BDDand cfg1 (node3 :: ul) node1 node2)).
  replace node4 with (snd (BDDand cfg1 (node3 :: ul) node1 node2)).
  apply BDDand_node_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H0.  reflexivity.  rewrite H0.  reflexivity.
  apply used_nodes_preserved_list_OK with (cfg := cfg1).  assumption.  assumption.
  replace cfg2 with (fst (BDDand cfg1 (node3 :: ul) node1 node2)).
  apply BDDand_used_nodes_preserved.  assumption.  assumption.  assumption.
  assumption.  rewrite H0.  reflexivity.
  replace cfg2 with (fst (BDDand cfg1 (node3 :: ul) node1 node2)).
  apply BDDand_config_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H0.  reflexivity.  apply used_node'_cons_node'_ul.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.  assumption.
  assumption.  apply used_node'_cons_node'_ul.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.  assumption.
  assumption.  apply node_OK_list_OK.
  replace cfg1 with (fst (BDDor cfg ul node1 node2)).
  replace node3 with (snd (BDDor cfg ul node1 node2)).  apply BDDor_node_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H.  reflexivity.
  rewrite H.  reflexivity.  apply used_nodes_preserved_list_OK with (cfg := cfg).
  assumption.  assumption.  replace cfg1 with (fst (BDDor cfg ul node1 node2)).
  apply BDDor_used_nodes_preserved.  assumption.  assumption.  assumption.
  assumption.  rewrite H.  reflexivity.
  replace cfg1 with (fst (BDDor cfg ul node1 node2)).  apply BDDor_config_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H.  reflexivity.
Qed.

Lemma BDDiff_list_OK : used_list_OK (fst BDDiff) ul.
Proof.
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.
  exact BDDiff_used_nodes_preserved.  
Qed.

Lemma BDDiff_list_OK_cons : used_list_OK (fst BDDiff) (snd BDDiff :: ul).
Proof.
  apply node_OK_list_OK.  apply BDDiff_node_OK.  exact BDDiff_list_OK.  
Qed.



                         End BDDiff_results.




                     Section BDDvar_make_results.


Variable cfg : BDDconfig.
Variable ul : list ad.
Variable x : BDDvar.

Hypothesis cfg_OK : BDDconfig_OK cfg.
Hypothesis ul_OK : used_list_OK cfg ul.

Definition BDDvar_make := BDDmake gc cfg x BDDzero BDDone ul.

Lemma BDDvar_make_config_OK : BDDconfig_OK (fst BDDvar_make).
Proof.
  unfold BDDvar_make in |- *.  apply BDDmake_keeps_config_OK.  assumption.  assumption.
  assumption.  apply used'_zero.  apply used'_one.  unfold bs_of_cfg in |- *.
  rewrite (config_OK_zero _ cfg_OK).  intros.  discriminate.  unfold bs_of_cfg in |- *.
  rewrite (config_OK_one _ cfg_OK).  intros.  discriminate.
Qed.

Lemma BDDvar_make_node_OK :
 config_node_OK (fst BDDvar_make) (snd BDDvar_make).
Proof.
  unfold BDDvar_make in |- *.  apply BDDmake_node_OK.  assumption.  assumption.
  assumption.  apply used'_zero.  apply used'_one.  unfold bs_of_cfg in |- *.
  rewrite (config_OK_zero _ cfg_OK).  intros.  discriminate.  unfold bs_of_cfg in |- *.
  rewrite (config_OK_one _ cfg_OK).  intros.  discriminate.
Qed.

Lemma BDDvar_make_used_nodes_preserved :
 used_nodes_preserved cfg (fst BDDvar_make) ul.
Proof.
  unfold BDDvar_make in |- *.  apply BDDmake_preserves_used_nodes.  assumption.
  assumption.  assumption.
Qed.

Lemma BDDvar_make_list_OK : used_list_OK (fst BDDvar_make) ul.
Proof.
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.
  exact BDDvar_make_used_nodes_preserved.
Qed.

Lemma BDDvar_make_list_OK_cons :
 used_list_OK (fst BDDvar_make) (snd BDDvar_make :: ul).
Proof.
  apply node_OK_list_OK.  exact BDDvar_make_node_OK.  exact BDDvar_make_list_OK.
Qed.

Lemma BDDvar_make_is_var :
 bool_fun_eq (bool_fun_of_BDD (fst BDDvar_make) (snd BDDvar_make))
   (bool_fun_var x).
Proof.
  apply
   bool_fun_eq_trans with (bf2 := bool_fun_if x bool_fun_one bool_fun_zero).
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_if x (bool_fun_of_BDD cfg BDDone)
                (bool_fun_of_BDD cfg BDDzero)).
  unfold BDDvar_make in |- *.  apply BDDmake_bool_fun.  assumption.  assumption.
  assumption.  apply used'_zero.  apply used'_one.  unfold bs_of_cfg in |- *.
  rewrite (config_OK_zero _ cfg_OK).  intros.  discriminate.  unfold bs_of_cfg in |- *.
  rewrite (config_OK_one _ cfg_OK).  intros.  discriminate.
  apply bool_fun_if_preserves_eq.  apply bool_fun_of_BDD_one.  assumption.
  apply bool_fun_of_BDD_zero.  assumption.  apply bool_fun_eq_sym.
  apply bool_fun_var_lemma.
Qed.


                          End BDDvar_make_results.



End BDDop.
