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
Require Import op.

Section tauto.

Variable gc : BDDconfig -> list ad -> BDDconfig.
Hypothesis gc_is_OK : gc_OK gc.

Fixpoint BDDof_bool_expr (cfg : BDDconfig) (ul : list ad) 
 (be : bool_expr) {struct be} : BDDconfig * ad :=
  match be with
  | Zero => (cfg, BDDzero)
  | One => (cfg, BDDone)
  | Var x => BDDvar_make gc cfg ul x
  | Neg be1 =>
      match BDDof_bool_expr cfg ul be1 with
      | (cfg1, node1) => BDDneg gc cfg1 (node1 :: ul) node1
      end
  | Or be1 be2 =>
      match BDDof_bool_expr cfg ul be1 with
      | (cfg1, node1) =>
          match BDDof_bool_expr cfg1 (node1 :: ul) be2 with
          | (cfg2, node2) => BDDor gc cfg2 (node2 :: node1 :: ul) node1 node2
          end
      end
  | ANd be1 be2 =>
      match BDDof_bool_expr cfg ul be1 with
      | (cfg1, node1) =>
          match BDDof_bool_expr cfg1 (node1 :: ul) be2 with
          | (cfg2, node2) =>
              BDDand gc cfg2 (node2 :: node1 :: ul) node1 node2
          end
      end
  | Impl be1 be2 =>
      match BDDof_bool_expr cfg ul be1 with
      | (cfg1, node1) =>
          match BDDof_bool_expr cfg1 (node1 :: ul) be2 with
          | (cfg2, node2) =>
              BDDimpl gc cfg2 (node2 :: node1 :: ul) node1 node2
          end
      end
  | Iff be1 be2 =>
      match BDDof_bool_expr cfg ul be1 with
      | (cfg1, node1) =>
          match BDDof_bool_expr cfg1 (node1 :: ul) be2 with
          | (cfg2, node2) =>
              BDDiff gc cfg2 (node2 :: node1 :: ul) node1 node2
          end
      end
  end.

Lemma BDDof_bool_expr_correct :
 forall (be : bool_expr) (cfg : BDDconfig) (ul : list ad),
 BDDconfig_OK cfg ->
 used_list_OK cfg ul ->
 BDDconfig_OK (fst (BDDof_bool_expr cfg ul be)) /\
 used_nodes_preserved cfg (fst (BDDof_bool_expr cfg ul be)) ul /\
 config_node_OK (fst (BDDof_bool_expr cfg ul be))
   (snd (BDDof_bool_expr cfg ul be)) /\
 bool_fun_eq
   (bool_fun_of_BDD (fst (BDDof_bool_expr cfg ul be))
      (snd (BDDof_bool_expr cfg ul be))) (bool_fun_of_bool_expr be).
Proof.
  simple induction be.  intros.  simpl in |- *.  split.  assumption.  split.
  apply used_nodes_preserved_refl.  split.  apply zero_OK.
  apply bool_fun_of_BDD_zero.  assumption.  intros.  simpl in |- *.  split.  assumption.
  split.  apply used_nodes_preserved_refl.  split.  apply one_OK.
  apply bool_fun_of_BDD_one.  assumption.  intros.  simpl in |- *.  split.
  apply BDDvar_make_config_OK.  assumption.  assumption.  assumption.  split.
  apply BDDvar_make_used_nodes_preserved.  assumption.  assumption.  assumption.
  split.  apply BDDvar_make_node_OK.  assumption.  assumption.  assumption.
  apply BDDvar_make_is_var.  assumption.  assumption.  assumption.  intros.
  simpl in |- *.
  elim (prod_sum _ _ (BDDof_bool_expr cfg ul b)).  intros cfg1 H2.  elim H2.
  clear H2.  intros node1 H2.  rewrite H2.  elim (H cfg ul H0 H1).  clear H.
  rewrite H2.  simpl in |- *.  intros.  elim H3; clear H3; intros.
  elim H4; clear H4; intros.  cut (used_list_OK cfg1 (node1 :: ul)).  intro.
  cut (used_node' cfg1 (node1 :: ul) node1).  intro.  split.
  apply BDDneg_config_OK.  assumption.  assumption.  assumption.  assumption.
  split.  apply used_nodes_preserved_trans with (cfg2 := cfg1).  assumption.
  assumption.  apply used_nodes_preserved_cons with (node := node1).
  apply BDDneg_used_nodes_preserved.  assumption.  assumption.  assumption.  
  assumption.  split.  apply BDDneg_node_OK.  assumption.  assumption.
  assumption.  assumption.  
  apply
   bool_fun_eq_trans with (bf2 := bool_fun_neg (bool_fun_of_BDD cfg1 node1)).
  apply BDDneg_is_neg.  assumption.  assumption.  assumption.  assumption.
  apply bool_fun_neg_preserves_eq.  assumption.  apply used_node'_cons_node_ul.
  apply node_OK_list_OK.  assumption.
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.  assumption.



  intros.  simpl in |- *.  elim (H cfg ul H1 H2).  clear H.
  elim (prod_sum _ _ (BDDof_bool_expr cfg ul b)).  intros cfg1 H3.  elim H3.
  clear H3.  intros node1 H3.  rewrite H3.  simpl in |- *.  intros.
  elim H4; clear H4; intros.  elim H5; clear H5; intros.
  cut (used_list_OK cfg1 ul).  intro.  cut (used_list_OK cfg1 (node1 :: ul)).
  intro.  cut (used_node' cfg1 (node1 :: ul) node1).  intro.
  elim (H0 cfg1 (node1 :: ul) H H8).  clear H0.
  elim (prod_sum _ _ (BDDof_bool_expr cfg1 (node1 :: ul) b0)).
  intros cfg2 H10.  elim H10.  clear H10.  intros node2 H10.  rewrite H10.
  simpl in |- *.  intros.  elim H11; clear H11; intros.
  elim H12; clear H12; intros.  cut (used_list_OK cfg2 (node1 :: ul)).
  intro.  cut (used_list_OK cfg2 (node2 :: node1 :: ul)).  intro.
  cut (used_node' cfg2 (node2 :: node1 :: ul) node2).
  cut (used_node' cfg2 (node2 :: node1 :: ul) node1).  intros.  split.
  apply BDDor_config_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  split.  apply used_nodes_preserved_trans with (cfg2 := cfg1).
  assumption.  assumption.  apply used_nodes_preserved_cons with (node := node1).
  apply used_nodes_preserved_trans with (cfg2 := cfg2).  assumption.  assumption.
  apply used_nodes_preserved_cons with (node := node2).
  apply BDDor_used_nodes_preserved.  assumption.  assumption.  assumption.  
  assumption.  assumption.  split.  apply BDDor_node_OK.  assumption.
  assumption.  assumption.  assumption.  assumption.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_or (bool_fun_of_BDD cfg2 node1)
                (bool_fun_of_BDD cfg2 node2)).
  apply BDDor_is_or.  assumption.  assumption.  assumption.  assumption.
  assumption.  apply bool_fun_or_preserves_eq.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg1 node1).
  apply used_nodes_preserved'_bool_fun with (ul := node1 :: ul).  assumption.
  assumption.  assumption.  assumption.  assumption.  assumption.  assumption.
  apply used_node'_cons_node'_ul.  apply used_node'_cons_node_ul.  
  apply used_node'_cons_node_ul.  apply node_OK_list_OK.  assumption.  
  assumption.  apply used_nodes_preserved_list_OK with (cfg := cfg1).  assumption.
  assumption.  apply used_node'_cons_node_ul.  apply node_OK_list_OK.
  assumption.  assumption.  apply used_nodes_preserved_list_OK with (cfg := cfg).
  assumption.  assumption.  


  intros.  simpl in |- *.  elim (H cfg ul H1 H2).  clear H.
  elim (prod_sum _ _ (BDDof_bool_expr cfg ul b)).  intros cfg1 H3.  elim H3.
  clear H3.  intros node1 H3.  rewrite H3.  simpl in |- *.  intros.
  elim H4; clear H4; intros.  elim H5; clear H5; intros.
  cut (used_list_OK cfg1 ul).  intro.  cut (used_list_OK cfg1 (node1 :: ul)).
  intro.  cut (used_node' cfg1 (node1 :: ul) node1).  intro.
  elim (H0 cfg1 (node1 :: ul) H H8).  clear H0.
  elim (prod_sum _ _ (BDDof_bool_expr cfg1 (node1 :: ul) b0)).
  intros cfg2 H10.  elim H10.  clear H10.  intros node2 H10.  rewrite H10.
  simpl in |- *.  intros.  elim H11; clear H11; intros.
  elim H12; clear H12; intros.  cut (used_list_OK cfg2 (node1 :: ul)).
  intro.  cut (used_list_OK cfg2 (node2 :: node1 :: ul)).  intro.
  cut (used_node' cfg2 (node2 :: node1 :: ul) node2).
  cut (used_node' cfg2 (node2 :: node1 :: ul) node1).  intros.  split.
  apply BDDand_config_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  split.  apply used_nodes_preserved_trans with (cfg2 := cfg1).  
  assumption.  assumption.  apply used_nodes_preserved_cons with (node := node1).
  apply used_nodes_preserved_trans with (cfg2 := cfg2).  assumption.  assumption.
  apply used_nodes_preserved_cons with (node := node2).
  apply BDDand_used_nodes_preserved.  assumption.  assumption.  assumption.
  assumption.  assumption.  split.  apply BDDand_node_OK.  assumption.  
  assumption.  assumption.  assumption.  assumption.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_and (bool_fun_of_BDD cfg2 node1)
                (bool_fun_of_BDD cfg2 node2)).
  apply BDDand_is_and.  assumption.  assumption.  assumption.  assumption.
  assumption.  apply bool_fun_and_preserves_eq.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg1 node1).
  apply used_nodes_preserved'_bool_fun with (ul := node1 :: ul).  assumption.
  assumption.  assumption.  assumption.  assumption.  assumption.  assumption.
  apply used_node'_cons_node'_ul.  apply used_node'_cons_node_ul.
  apply used_node'_cons_node_ul.  apply node_OK_list_OK.  assumption.
  assumption.  apply used_nodes_preserved_list_OK with (cfg := cfg1).  assumption.
  assumption.  apply used_node'_cons_node_ul.  apply node_OK_list_OK.
  assumption.  assumption.  apply used_nodes_preserved_list_OK with (cfg := cfg).
  assumption.  assumption.

  intros.  simpl in |- *.  elim (H cfg ul H1 H2).  clear H.
  elim (prod_sum _ _ (BDDof_bool_expr cfg ul b)).  intros cfg1 H3.  elim H3.
  clear H3.  intros node1 H3.  rewrite H3.  simpl in |- *.  intros.
  elim H4; clear H4; intros.  elim H5; clear H5; intros.
  cut (used_list_OK cfg1 ul).  intro.  cut (used_list_OK cfg1 (node1 :: ul)).
  intro.  cut (used_node' cfg1 (node1 :: ul) node1).  intro.
  elim (H0 cfg1 (node1 :: ul) H H8).  clear H0.
  elim (prod_sum _ _ (BDDof_bool_expr cfg1 (node1 :: ul) b0)).
  intros cfg2 H10.  elim H10.  clear H10.  intros node2 H10.  rewrite H10.
  simpl in |- *.  intros.  elim H11; clear H11; intros.
  elim H12; clear H12; intros.  cut (used_list_OK cfg2 (node1 :: ul)).
  intro.  cut (used_list_OK cfg2 (node2 :: node1 :: ul)).  intro.
  cut (used_node' cfg2 (node2 :: node1 :: ul) node2).
  cut (used_node' cfg2 (node2 :: node1 :: ul) node1).  intros.  split.
  apply BDDimpl_config_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  split.  apply used_nodes_preserved_trans with (cfg2 := cfg1).  
  assumption.  assumption.  apply used_nodes_preserved_cons with (node := node1).
  apply used_nodes_preserved_trans with (cfg2 := cfg2).  assumption.  assumption.
  apply used_nodes_preserved_cons with (node := node2).
  apply BDDimpl_used_nodes_preserved.  assumption.  assumption.  assumption.
  assumption.  assumption.  split.  apply BDDimpl_node_OK.  assumption.  
  assumption.  assumption.  assumption.  assumption.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_impl (bool_fun_of_BDD cfg2 node1)
                (bool_fun_of_BDD cfg2 node2)).
  apply BDDimpl_is_impl.  assumption.  assumption.  assumption.  assumption.
  assumption.  apply bool_fun_impl_preserves_eq.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg1 node1).
  apply used_nodes_preserved'_bool_fun with (ul := node1 :: ul).  assumption.
  assumption.  assumption.  assumption.  assumption.  assumption.  assumption.
  apply used_node'_cons_node'_ul.  apply used_node'_cons_node_ul.
  apply used_node'_cons_node_ul.  apply node_OK_list_OK.  assumption.
  assumption.  apply used_nodes_preserved_list_OK with (cfg := cfg1).  assumption.
  assumption.  apply used_node'_cons_node_ul.  apply node_OK_list_OK.
  assumption.  assumption.  apply used_nodes_preserved_list_OK with (cfg := cfg).
  assumption.  assumption.


  intros.  simpl in |- *.  elim (H cfg ul H1 H2).  clear H.
  elim (prod_sum _ _ (BDDof_bool_expr cfg ul b)).  intros cfg1 H3.  elim H3.
  clear H3.  intros node1 H3.  rewrite H3.  simpl in |- *.  intros.
  elim H4; clear H4; intros.  elim H5; clear H5; intros.
  cut (used_list_OK cfg1 ul).  intro.  cut (used_list_OK cfg1 (node1 :: ul)).
  intro.  cut (used_node' cfg1 (node1 :: ul) node1).  intro.
  elim (H0 cfg1 (node1 :: ul) H H8).  clear H0.
  elim (prod_sum _ _ (BDDof_bool_expr cfg1 (node1 :: ul) b0)).
  intros cfg2 H10.  elim H10.  clear H10.  intros node2 H10.  rewrite H10.
  simpl in |- *.  intros.  elim H11; clear H11; intros.
  elim H12; clear H12; intros.  cut (used_list_OK cfg2 (node1 :: ul)).
  intro.  cut (used_list_OK cfg2 (node2 :: node1 :: ul)).  intro.
  cut (used_node' cfg2 (node2 :: node1 :: ul) node2).
  cut (used_node' cfg2 (node2 :: node1 :: ul) node1).  intros.  split.
  apply BDDiff_config_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  split.  apply used_nodes_preserved_trans with (cfg2 := cfg1).  
  assumption.  assumption.  apply used_nodes_preserved_cons with (node := node1).
  apply used_nodes_preserved_trans with (cfg2 := cfg2).  assumption.  assumption.
  apply used_nodes_preserved_cons with (node := node2).
  apply BDDiff_used_nodes_preserved.  assumption.  assumption.  assumption.
  assumption.  assumption.  split.  apply BDDiff_node_OK.  assumption.  
  assumption.  assumption.  assumption.  assumption.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_iff (bool_fun_of_BDD cfg2 node1)
                (bool_fun_of_BDD cfg2 node2)).
  apply BDDiff_is_iff.  assumption.  assumption.  assumption.  assumption.
  assumption.  apply bool_fun_iff_preserves_eq.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg1 node1).
  apply used_nodes_preserved'_bool_fun with (ul := node1 :: ul).  assumption.
  assumption.  assumption.  assumption.  assumption.  assumption.  assumption.
  apply used_node'_cons_node'_ul.  apply used_node'_cons_node_ul.
  apply used_node'_cons_node_ul.  apply node_OK_list_OK.  assumption.
  assumption.  apply used_nodes_preserved_list_OK with (cfg := cfg1).  assumption.
  assumption.  apply used_node'_cons_node_ul.  apply node_OK_list_OK.
  assumption.  assumption.  apply used_nodes_preserved_list_OK with (cfg := cfg).
  assumption.  assumption.
Qed.

Lemma init_list_OK : forall cfg : BDDconfig, used_list_OK cfg nil.
Proof.
  intro.  unfold used_list_OK in |- *.  unfold used_list_OK_bs in |- *.  simpl in |- *.  tauto.
Qed.

Definition is_tauto (be : bool_expr) :=
  Neqb BDDone (snd (BDDof_bool_expr initBDDconfig nil be)).

Lemma is_tauto_lemma :
 forall be : bool_expr,
 is_tauto be = true <-> bool_fun_eq bool_fun_one (bool_fun_of_bool_expr be).
Proof.
  unfold is_tauto in |- *.  intros.
  cut
   (bool_fun_eq
      (bool_fun_of_BDD (fst (BDDof_bool_expr initBDDconfig nil be))
         (snd (BDDof_bool_expr initBDDconfig nil be)))
      (bool_fun_of_bool_expr be)).
  intro.  split.  intro.  rewrite <- (Neqb_complete _ _ H0) in H.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_of_BDD (fst (BDDof_bool_expr initBDDconfig nil be))
                BDDone).
  apply bool_fun_eq_sym.  apply bool_fun_of_BDD_one.
  refine (proj1 (BDDof_bool_expr_correct _ _ _ _ _)).
  apply initBDDconfig_OK.  apply init_list_OK.  assumption.  intro.
  apply BDDunique with (cfg := fst (BDDof_bool_expr initBDDconfig nil be)).
  refine (proj1 (BDDof_bool_expr_correct _ _ _ _ _)).
  apply initBDDconfig_OK.  apply init_list_OK.  apply one_OK.
  refine (proj1 (proj2 (proj2 (BDDof_bool_expr_correct _ _ _ _ _)))).
  apply initBDDconfig_OK.  apply init_list_OK.  
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_bool_expr be).
  apply bool_fun_eq_trans with (bf2 := bool_fun_one).  apply bool_fun_of_BDD_one.
  refine (proj1 (BDDof_bool_expr_correct _ _ _ _ _)).
  apply initBDDconfig_OK.  apply init_list_OK.  assumption.
  apply bool_fun_eq_sym.  assumption.
  refine (proj2 (proj2 (proj2 (BDDof_bool_expr_correct _ _ _ _ _)))).
  apply initBDDconfig_OK.  apply init_list_OK.  
Qed.

End tauto.