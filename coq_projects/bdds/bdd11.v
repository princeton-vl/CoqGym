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
Require Import bdd10.

Definition BDDimpl (cfg : BDDconfig) (negm : BDDneg_memo) 
  (orm : BDDor_memo) (node1 node2 : ad) :=
  match BDDneg cfg negm node1 with
  | (cfg', (node1', negm')) =>
      match BDDor cfg' orm node1' node2 with
      | (cfg'', (node, orm')) => (cfg'', (node, (negm', orm')))
      end
  end.

Lemma BDDimpl_keeps_config_OK :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (orm : BDDor_memo)
   (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 BDDconfig_OK (fst (BDDimpl cfg negm orm node1 node2)).
Proof.
  intros.  unfold BDDimpl in |- *.  elim (prod_sum _ _ (BDDneg cfg negm node1)).  intros cfg' H4.
  elim H4; clear H4.  intro.  elim x; clear x.  intros node1' negm' H4.
  rewrite H4.  elim (prod_sum _ _ (BDDor cfg' orm node1' node2)).  intros cfg'' H5.
  elim H5; clear H5.  intro.  elim x; clear x.  intros node negm'' H5.  rewrite H5.
  simpl in |- *.  cut (BDDconfig_OK cfg').  cut (config_node_OK cfg' node1').  cut (config_node_OK cfg' node2).
  cut (BDDneg_memo_OK_2 cfg' negm').  cut (BDDor_memo_OK cfg' orm).  intros.
  replace cfg'' with (fst (BDDor cfg' orm node1' node2)).  apply BDDor_keeps_config_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H5; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  apply BDDneg_keeps_or_memo_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  replace negm' with (snd (snd (BDDneg cfg negm node1))).
  apply BDDneg_keeps_neg_memo_OK.  assumption.  assumption.  assumption.  
  rewrite H4; reflexivity.  rewrite H4; reflexivity.  replace cfg' with (fst (BDDneg cfg negm node1)).
  apply BDDneg_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDneg cfg negm node1)).
  replace node1' with (fst (snd (BDDneg cfg negm node1))).  apply BDDneg_node_OK.
  assumption.  assumption.  assumption.  rewrite H4; reflexivity.  rewrite H4; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  apply BDDneg_keeps_config_OK.
  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
Qed.

Lemma BDDimpl_node_OK :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (orm : BDDor_memo)
   (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 config_node_OK (fst (BDDimpl cfg negm orm node1 node2))
   (fst (snd (BDDimpl cfg negm orm node1 node2))).
Proof.

  intros.  unfold BDDimpl in |- *.  elim (prod_sum _ _ (BDDneg cfg negm node1)).  intros cfg' H4.
  elim H4; clear H4.  intro.  elim x; clear x.  intros node1' negm' H4.
  rewrite H4.  elim (prod_sum _ _ (BDDor cfg' orm node1' node2)).  intros cfg'' H5.
  elim H5; clear H5.  intro.  elim x; clear x.  intros node negm'' H5.  rewrite H5.
  simpl in |- *.  cut (BDDconfig_OK cfg').  cut (config_node_OK cfg' node1').  cut (config_node_OK cfg' node2).
  cut (BDDneg_memo_OK_2 cfg' negm').  cut (BDDor_memo_OK cfg' orm).  intros.
  replace cfg'' with (fst (BDDor cfg' orm node1' node2)).  replace node with (fst (snd (BDDor cfg' orm node1' node2))).
  apply BDDor_node_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H5; reflexivity.  rewrite H5; reflexivity.  
  replace cfg' with (fst (BDDneg cfg negm node1)).  apply BDDneg_keeps_or_memo_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  replace negm' with (snd (snd (BDDneg cfg negm node1))).
  apply BDDneg_keeps_neg_memo_OK.  assumption.  assumption.  assumption.
  rewrite H4; reflexivity.  rewrite H4; reflexivity.  replace cfg' with (fst (BDDneg cfg negm node1)).
  apply BDDneg_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDneg cfg negm node1)).
  replace node1' with (fst (snd (BDDneg cfg negm node1))).  apply BDDneg_node_OK.
  assumption.  assumption.  assumption.  rewrite H4; reflexivity.  rewrite H4; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  apply BDDneg_keeps_config_OK.
  assumption.  assumption.  assumption.  rewrite H4; reflexivity.

Qed.

Definition bool_fun_impl (bf1 bf2 : bool_fun) : bool_fun :=
  fun vb : var_binding => implb (bf1 vb) (bf2 vb).

Lemma bool_fun_impl_is_neg_or_bf2 :
 forall bf1 bf2 : bool_fun,
 bool_fun_eq (bool_fun_impl bf1 bf2) (bool_fun_or (bool_fun_neg bf1) bf2).
Proof.
  unfold bool_fun_eq, bool_fun_impl, bool_fun_or, bool_fun_neg in |- *.  unfold bool_fun_eval in |- *.
  intros.  elim (bf1 vb).  elim (bf2 vb).  reflexivity.  reflexivity.  reflexivity.
Qed.

Lemma BDDimpl_is_impl :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (orm : BDDor_memo)
   (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 bool_fun_eq
   (bool_fun_of_BDD (fst (BDDimpl cfg negm orm node1 node2))
      (fst (snd (BDDimpl cfg negm orm node1 node2))))
   (bool_fun_impl (bool_fun_of_BDD cfg node1) (bool_fun_of_BDD cfg node2)).
Proof.
  intros.  unfold BDDimpl in |- *.  elim (prod_sum _ _ (BDDneg cfg negm node1)).  intros cfg' H4.
  elim H4; clear H4.  intro.  elim x; clear x.  intros node1' negm' H4.
  rewrite H4.  elim (prod_sum _ _ (BDDor cfg' orm node1' node2)).  intros cfg'' H5.
  elim H5; clear H5.  intro.  elim x; clear x.  intros node negm'' H5.  rewrite H5.
  simpl in |- *.  cut (BDDconfig_OK cfg').  cut (config_node_OK cfg' node1').  cut (config_node_OK cfg' node2).
  cut (BDDneg_memo_OK_2 cfg' negm').  cut (BDDor_memo_OK cfg' orm).  intros.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_or (bool_fun_of_BDD cfg' node1')
                (bool_fun_of_BDD cfg' node2)).
  replace cfg'' with (fst (BDDor cfg' orm node1' node2)).  replace node with (fst (snd (BDDor cfg' orm node1' node2))).
  apply BDDor_is_or.  assumption.  assumption.  assumption.  assumption.
  rewrite H5; reflexivity.  rewrite H5; reflexivity.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_or (bool_fun_neg (bool_fun_of_BDD cfg node1))
                (bool_fun_of_BDD cfg node2)).
  apply bool_fun_or_preserves_eq.  replace cfg' with (fst (BDDneg cfg negm node1)).
  replace node1' with (fst (snd (BDDneg cfg negm node1))).  apply BDDneg_is_neg.
  assumption.  assumption.  assumption.  rewrite H4; reflexivity.  rewrite H4; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  apply BDDneg_preserves_bool_fun.
  assumption.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  apply bool_fun_eq_symm.  apply bool_fun_impl_is_neg_or_bf2.  
  replace cfg' with (fst (BDDneg cfg negm node1)).  apply BDDneg_keeps_or_memo_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  replace negm' with (snd (snd (BDDneg cfg negm node1))).
  apply BDDneg_keeps_neg_memo_OK.  assumption.  assumption.  assumption.
  rewrite H4; reflexivity.  rewrite H4; reflexivity.  replace cfg' with (fst (BDDneg cfg negm node1)).
  apply BDDneg_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDneg cfg negm node1)).
  replace node1' with (fst (snd (BDDneg cfg negm node1))).  apply BDDneg_node_OK.
  assumption.  assumption.  assumption.  rewrite H4; reflexivity.  rewrite H4; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  apply BDDneg_keeps_config_OK.
  assumption.  assumption.  assumption.  rewrite H4; reflexivity.

Qed.

Lemma BDDimpl_preserves_nodes :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (orm : BDDor_memo)
   (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 nodes_preserved cfg (fst (BDDimpl cfg negm orm node1 node2)).
Proof.
  intros.  unfold BDDimpl in |- *.  elim (prod_sum _ _ (BDDneg cfg negm node1)).  intros cfg' H4.
  elim H4; clear H4.  intro.  elim x; clear x.  intros node1' negm' H4.
  rewrite H4.  elim (prod_sum _ _ (BDDor cfg' orm node1' node2)).  intros cfg'' H5.
  elim H5; clear H5.  intro.  elim x; clear x.  intros node negm'' H5.  rewrite H5.
  simpl in |- *.  cut (BDDconfig_OK cfg').  cut (config_node_OK cfg' node1').  cut (config_node_OK cfg' node2).
  cut (BDDneg_memo_OK_2 cfg' negm').  cut (BDDor_memo_OK cfg' orm).  intros.
  apply nodes_preserved_trans with (cfg2 := cfg').  replace cfg' with (fst (BDDneg cfg negm node1)).
  apply BDDneg_preserves_nodes.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  replace cfg'' with (fst (BDDor cfg' orm node1' node2)).  apply BDDor_preserves_nodes.
  assumption.  assumption.  assumption.  assumption.  rewrite H5; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  apply BDDneg_keeps_or_memo_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  replace negm' with (snd (snd (BDDneg cfg negm node1))).
  apply BDDneg_keeps_neg_memo_OK.  assumption.  assumption.  assumption.
  rewrite H4; reflexivity.  rewrite H4; reflexivity.  replace cfg' with (fst (BDDneg cfg negm node1)).
  apply BDDneg_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDneg cfg negm node1)).
  replace node1' with (fst (snd (BDDneg cfg negm node1))).  apply BDDneg_node_OK.
  assumption.  assumption.  assumption.  rewrite H4; reflexivity.  rewrite H4; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  apply BDDneg_keeps_config_OK.
  assumption.  assumption.  assumption.  rewrite H4; reflexivity.

Qed.

Lemma BDDimpl_keeps_node_OK :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (orm : BDDor_memo)
   (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 forall node : ad,
 config_node_OK cfg node ->
 config_node_OK (fst (BDDimpl cfg negm orm node1 node2)) node.
Proof.
  intros.  apply nodes_preserved_2 with (cfg := cfg).  assumption.  apply BDDimpl_preserves_nodes.
  assumption.  assumption.  assumption.  assumption.  assumption.
Qed.

Lemma BDDimpl_preserves_bool_fun :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (orm : BDDor_memo)
   (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 forall node : ad,
 config_node_OK cfg node ->
 bool_fun_eq (bool_fun_of_BDD (fst (BDDimpl cfg negm orm node1 node2)) node)
   (bool_fun_of_BDD cfg node).
Proof.
  intros.  apply nodes_preserved_3.  assumption.  apply BDDimpl_keeps_config_OK.
  assumption.  assumption.  assumption.  assumption.  assumption.  apply BDDimpl_preserves_nodes.
  assumption.  assumption.  assumption.  assumption.  assumption.  assumption.
Qed.

Lemma BDDimpl_keeps_neg_memo_OK :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (orm : BDDor_memo)
   (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 BDDneg_memo_OK_2 (fst (BDDimpl cfg negm orm node1 node2))
   (fst (snd (snd (BDDimpl cfg negm orm node1 node2)))).
Proof.
  intros.  unfold BDDimpl in |- *.  elim (prod_sum _ _ (BDDneg cfg negm node1)).  intros cfg' H4.
  elim H4; clear H4.  intro.  elim x; clear x.  intros node1' negm' H4.
  rewrite H4.  elim (prod_sum _ _ (BDDor cfg' orm node1' node2)).  intros cfg'' H5.
  elim H5; clear H5.  intro.  elim x; clear x.  intros node negm'' H5.  rewrite H5.
  simpl in |- *.  cut (BDDconfig_OK cfg').  cut (config_node_OK cfg' node1').  cut (config_node_OK cfg' node2).
  cut (BDDneg_memo_OK_2 cfg' negm').  cut (BDDor_memo_OK cfg' orm).  intros.
  replace cfg'' with (fst (BDDor cfg' orm node1' node2)).  apply BDDor_keeps_neg_memo_OK.
  assumption.  assumption.  assumption.  assumption.  assumption.  rewrite H5; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  apply BDDneg_keeps_or_memo_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  replace negm' with (snd (snd (BDDneg cfg negm node1))).
  apply BDDneg_keeps_neg_memo_OK.  assumption.  assumption.  assumption.
  rewrite H4; reflexivity.  rewrite H4; reflexivity.  replace cfg' with (fst (BDDneg cfg negm node1)).
  apply BDDneg_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDneg cfg negm node1)).
  replace node1' with (fst (snd (BDDneg cfg negm node1))).  apply BDDneg_node_OK.
  assumption.  assumption.  assumption.  rewrite H4; reflexivity.  rewrite H4; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  apply BDDneg_keeps_config_OK.
  assumption.  assumption.  assumption.  rewrite H4; reflexivity.

Qed.

Lemma BDDimpl_keeps_or_memo_OK :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (orm : BDDor_memo)
   (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 BDDor_memo_OK (fst (BDDimpl cfg negm orm node1 node2))
   (snd (snd (snd (BDDimpl cfg negm orm node1 node2)))).
Proof.
  intros.  unfold BDDimpl in |- *.  elim (prod_sum _ _ (BDDneg cfg negm node1)).  intros cfg' H4.
  elim H4; clear H4.  intro.  elim x; clear x.  intros node1' negm' H4.
  rewrite H4.  elim (prod_sum _ _ (BDDor cfg' orm node1' node2)).  intros cfg'' H5.
  elim H5; clear H5.  intro.  elim x; clear x.  intros node negm'' H5.  rewrite H5.
  simpl in |- *.  cut (BDDconfig_OK cfg').  cut (config_node_OK cfg' node1').  cut (config_node_OK cfg' node2).
  cut (BDDneg_memo_OK_2 cfg' negm').  cut (BDDor_memo_OK cfg' orm).  intros.
  replace cfg'' with (fst (BDDor cfg' orm node1' node2)).  replace negm'' with (snd (snd (BDDor cfg' orm node1' node2))).
  apply BDDor_keeps_or_memo_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H5; reflexivity.  rewrite H5; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  apply BDDneg_keeps_or_memo_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  replace negm' with (snd (snd (BDDneg cfg negm node1))).
  apply BDDneg_keeps_neg_memo_OK.  assumption.  assumption.  assumption.
  rewrite H4; reflexivity.  rewrite H4; reflexivity.  replace cfg' with (fst (BDDneg cfg negm node1)).
  apply BDDneg_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDneg cfg negm node1)).
  replace node1' with (fst (snd (BDDneg cfg negm node1))).  apply BDDneg_node_OK.
  assumption.  assumption.  assumption.  rewrite H4; reflexivity.  rewrite H4; reflexivity.
  replace cfg' with (fst (BDDneg cfg negm node1)).  apply BDDneg_keeps_config_OK.
  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
Qed.


Definition BDDiff (cfg : BDDconfig) (negm : BDDneg_memo) 
  (orm : BDDor_memo) (node1 node2 : ad) :=
  match BDDimpl cfg negm orm node1 node2 with
  | (cfg', (node1', (negm', orm'))) =>
      match BDDimpl cfg' negm' orm' node2 node1 with
      | (cfg'', (node2', (negm'', orm''))) =>
          BDDand cfg'' negm'' orm'' node1' node2'
      end
  end.

Lemma BDDiff_keeps_config_OK :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (orm : BDDor_memo)
   (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 BDDconfig_OK (fst (BDDiff cfg negm orm node1 node2)).
Proof.
  intros.  unfold BDDiff in |- *.  elim (prod_sum _ _ (BDDimpl cfg negm orm node1 node2)).
  intros cfg' H4.  elim H4; clear H4.  intro.  elim x; clear x.  intros node1' y.
  elim y; clear y.  intros negm' orm' H4.  rewrite H4.  elim (prod_sum _ _ (BDDimpl cfg' negm' orm' node2 node1)).
  intros cfg'' H5.  elim H5; clear H5.  intro.  elim x; clear x.  intros node2' y.
  elim y; clear y.  intros negm'' orm'' H5.  rewrite H5.  cut (BDDconfig_OK cfg').
  cut (config_node_OK cfg' node1').  cut (config_node_OK cfg' node1).  cut (config_node_OK cfg' node2).
  cut (BDDneg_memo_OK_2 cfg' negm').  cut (BDDor_memo_OK cfg' orm').  intros.
  cut (BDDconfig_OK cfg'').  cut (config_node_OK cfg'' node2').  cut (config_node_OK cfg'' node1').
  cut (BDDneg_memo_OK_2 cfg'' negm'').  cut (BDDor_memo_OK cfg'' orm'').  intros.
  apply BDDand_keeps_config_OK.  assumption.  assumption.  assumption.  assumption.  assumption.  
  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).  replace orm'' with (snd (snd (snd (BDDimpl cfg' negm' orm' node2 node1)))).
  apply BDDimpl_keeps_or_memo_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H5; reflexivity.  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).
  replace negm'' with (fst (snd (snd (BDDimpl cfg' negm' orm' node2 node1)))).
  apply BDDimpl_keeps_neg_memo_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H5; reflexivity.  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).
  apply BDDimpl_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).
  replace node2' with (fst (snd (BDDimpl cfg' negm' orm' node2 node1))).  apply BDDimpl_node_OK.
  assumption.  assumption.  assumption.  assumption.  assumption.  rewrite H5; reflexivity.
  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).
  apply BDDimpl_keeps_config_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H5; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  replace orm' with (snd (snd (snd (BDDimpl cfg negm orm node1 node2)))).  apply BDDimpl_keeps_or_memo_OK.
  assumption.  assumption.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  replace negm' with (fst (snd (snd (BDDimpl cfg negm orm node1 node2)))).
  apply BDDimpl_keeps_neg_memo_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H4; reflexivity.  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  apply BDDimpl_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  apply BDDimpl_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  replace node1' with (fst (snd (BDDimpl cfg negm orm node1 node2))).  apply BDDimpl_node_OK.
  assumption.  assumption.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  apply BDDimpl_keeps_config_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H4; reflexivity.
Qed.

Lemma BDDiff_node_OK :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (orm : BDDor_memo)
   (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 config_node_OK (fst (BDDiff cfg negm orm node1 node2))
   (fst (snd (BDDiff cfg negm orm node1 node2))).
Proof.
  intros.  unfold BDDiff in |- *.  elim (prod_sum _ _ (BDDimpl cfg negm orm node1 node2)).
  intros cfg' H4.  elim H4; clear H4.  intro.  elim x; clear x.  intros node1' y.
  elim y; clear y.  intros negm' orm' H4.  rewrite H4.  elim (prod_sum _ _ (BDDimpl cfg' negm' orm' node2 node1)).
  intros cfg'' H5.  elim H5; clear H5.  intro.  elim x; clear x.  intros node2' y.
  elim y; clear y.  intros negm'' orm'' H5.  rewrite H5.  cut (BDDconfig_OK cfg').
  cut (config_node_OK cfg' node1').  cut (config_node_OK cfg' node1).  cut (config_node_OK cfg' node2).
  cut (BDDneg_memo_OK_2 cfg' negm').  cut (BDDor_memo_OK cfg' orm').  intros.
  cut (BDDconfig_OK cfg'').  cut (config_node_OK cfg'' node2').  cut (config_node_OK cfg'' node1').
  cut (BDDneg_memo_OK_2 cfg'' negm'').  cut (BDDor_memo_OK cfg'' orm'').  intros.
  apply BDDand_node_OK.  assumption.  assumption.  assumption.  assumption.  assumption.
  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).  replace orm'' with (snd (snd (snd (BDDimpl cfg' negm' orm' node2 node1)))).
  apply BDDimpl_keeps_or_memo_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H5; reflexivity.  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).
  replace negm'' with (fst (snd (snd (BDDimpl cfg' negm' orm' node2 node1)))).
  apply BDDimpl_keeps_neg_memo_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H5; reflexivity.  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).
  apply BDDimpl_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).
  replace node2' with (fst (snd (BDDimpl cfg' negm' orm' node2 node1))).  apply BDDimpl_node_OK.
  assumption.  assumption.  assumption.  assumption.  assumption.  rewrite H5; reflexivity.
  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).
  apply BDDimpl_keeps_config_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H5; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  replace orm' with (snd (snd (snd (BDDimpl cfg negm orm node1 node2)))).  apply BDDimpl_keeps_or_memo_OK.
  assumption.  assumption.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  replace negm' with (fst (snd (snd (BDDimpl cfg negm orm node1 node2)))).
  apply BDDimpl_keeps_neg_memo_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H4; reflexivity.  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  apply BDDimpl_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  apply BDDimpl_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  replace node1' with (fst (snd (BDDimpl cfg negm orm node1 node2))).  apply BDDimpl_node_OK.
  assumption.  assumption.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  apply BDDimpl_keeps_config_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H4; reflexivity.
Qed.

Lemma BDDiff_preserves_nodes :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (orm : BDDor_memo)
   (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 nodes_preserved cfg (fst (BDDiff cfg negm orm node1 node2)).
Proof.
  intros.  unfold BDDiff in |- *.  elim (prod_sum _ _ (BDDimpl cfg negm orm node1 node2)).
  intros cfg' H4.  elim H4; clear H4.  intro.  elim x; clear x.  intros node1' y.
  elim y; clear y.  intros negm' orm' H4.  rewrite H4.  elim (prod_sum _ _ (BDDimpl cfg' negm' orm' node2 node1)).
  intros cfg'' H5.  elim H5; clear H5.  intro.  elim x; clear x.  intros node2' y.
  elim y; clear y.  intros negm'' orm'' H5.  rewrite H5.  cut (BDDconfig_OK cfg').
  cut (config_node_OK cfg' node1').  cut (config_node_OK cfg' node1).  cut (config_node_OK cfg' node2).
  cut (BDDneg_memo_OK_2 cfg' negm').  cut (BDDor_memo_OK cfg' orm').  intros.
  cut (BDDconfig_OK cfg'').  cut (config_node_OK cfg'' node2').  cut (config_node_OK cfg'' node1').
  cut (BDDneg_memo_OK_2 cfg'' negm'').  cut (BDDor_memo_OK cfg'' orm'').  intros.
  apply nodes_preserved_trans with (cfg2 := cfg').  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  apply BDDimpl_preserves_nodes.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H4; reflexivity.  apply nodes_preserved_trans with (cfg2 := cfg'').
  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).  apply BDDimpl_preserves_nodes.
  assumption.  assumption.  assumption.  assumption.  assumption.  rewrite H5; reflexivity.
  apply BDDand_preserves_nodes.  assumption.  assumption.  assumption.  assumption.
  assumption.
  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).  replace orm'' with (snd (snd (snd (BDDimpl cfg' negm' orm' node2 node1)))).
  apply BDDimpl_keeps_or_memo_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H5; reflexivity.  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).
  replace negm'' with (fst (snd (snd (BDDimpl cfg' negm' orm' node2 node1)))).
  apply BDDimpl_keeps_neg_memo_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H5; reflexivity.  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).
  apply BDDimpl_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).
  replace node2' with (fst (snd (BDDimpl cfg' negm' orm' node2 node1))).  apply BDDimpl_node_OK.
  assumption.  assumption.  assumption.  assumption.  assumption.  rewrite H5; reflexivity.
  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).
  apply BDDimpl_keeps_config_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H5; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  replace orm' with (snd (snd (snd (BDDimpl cfg negm orm node1 node2)))).  apply BDDimpl_keeps_or_memo_OK.
  assumption.  assumption.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  replace negm' with (fst (snd (snd (BDDimpl cfg negm orm node1 node2)))).
  apply BDDimpl_keeps_neg_memo_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H4; reflexivity.  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  apply BDDimpl_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  apply BDDimpl_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  replace node1' with (fst (snd (BDDimpl cfg negm orm node1 node2))).  apply BDDimpl_node_OK.
  assumption.  assumption.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  apply BDDimpl_keeps_config_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H4; reflexivity.
Qed. 

Lemma BDDiff_keeps_neg_memo_OK :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (orm : BDDor_memo)
   (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 BDDneg_memo_OK_2 (fst (BDDiff cfg negm orm node1 node2))
   (fst (snd (snd (BDDiff cfg negm orm node1 node2)))).
Proof.
  intros.  unfold BDDiff in |- *.  elim (prod_sum _ _ (BDDimpl cfg negm orm node1 node2)).
  intros cfg' H4.  elim H4; clear H4.  intro.  elim x; clear x.  intros node1' y.
  elim y; clear y.  intros negm' orm' H4.  rewrite H4.  elim (prod_sum _ _ (BDDimpl cfg' negm' orm' node2 node1)).
  intros cfg'' H5.  elim H5; clear H5.  intro.  elim x; clear x.  intros node2' y.
  elim y; clear y.  intros negm'' orm'' H5.  rewrite H5.  cut (BDDconfig_OK cfg').
  cut (config_node_OK cfg' node1').  cut (config_node_OK cfg' node1).  cut (config_node_OK cfg' node2).
  cut (BDDneg_memo_OK_2 cfg' negm').  cut (BDDor_memo_OK cfg' orm').  intros.
  cut (BDDconfig_OK cfg'').  cut (config_node_OK cfg'' node2').  cut (config_node_OK cfg'' node1').
  cut (BDDneg_memo_OK_2 cfg'' negm'').  cut (BDDor_memo_OK cfg'' orm'').  intros.
  apply BDDand_keeps_neg_memo_OK.  assumption.  assumption.  assumption.  assumption.  assumption.
  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).  replace orm'' with (snd (snd (snd (BDDimpl cfg' negm' orm' node2 node1)))).
  apply BDDimpl_keeps_or_memo_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H5; reflexivity.  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).
  replace negm'' with (fst (snd (snd (BDDimpl cfg' negm' orm' node2 node1)))).
  apply BDDimpl_keeps_neg_memo_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H5; reflexivity.  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).
  apply BDDimpl_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).
  replace node2' with (fst (snd (BDDimpl cfg' negm' orm' node2 node1))).  apply BDDimpl_node_OK.
  assumption.  assumption.  assumption.  assumption.  assumption.  rewrite H5; reflexivity.
  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).
  apply BDDimpl_keeps_config_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H5; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  replace orm' with (snd (snd (snd (BDDimpl cfg negm orm node1 node2)))).  apply BDDimpl_keeps_or_memo_OK.
  assumption.  assumption.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  replace negm' with (fst (snd (snd (BDDimpl cfg negm orm node1 node2)))).
  apply BDDimpl_keeps_neg_memo_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H4; reflexivity.  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  apply BDDimpl_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  apply BDDimpl_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  replace node1' with (fst (snd (BDDimpl cfg negm orm node1 node2))).  apply BDDimpl_node_OK.
  assumption.  assumption.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  apply BDDimpl_keeps_config_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H4; reflexivity.
Qed.

Lemma BDDiff_keeps_or_memo_OK :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (orm : BDDor_memo)
   (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 BDDor_memo_OK (fst (BDDiff cfg negm orm node1 node2))
   (snd (snd (snd (BDDiff cfg negm orm node1 node2)))).
Proof.
  intros.  unfold BDDiff in |- *.  elim (prod_sum _ _ (BDDimpl cfg negm orm node1 node2)).
  intros cfg' H4.  elim H4; clear H4.  intro.  elim x; clear x.  intros node1' y.
  elim y; clear y.  intros negm' orm' H4.  rewrite H4.  elim (prod_sum _ _ (BDDimpl cfg' negm' orm' node2 node1)).
  intros cfg'' H5.  elim H5; clear H5.  intro.  elim x; clear x.  intros node2' y.
  elim y; clear y.  intros negm'' orm'' H5.  rewrite H5.  cut (BDDconfig_OK cfg').
  cut (config_node_OK cfg' node1').  cut (config_node_OK cfg' node1).  cut (config_node_OK cfg' node2).
  cut (BDDneg_memo_OK_2 cfg' negm').  cut (BDDor_memo_OK cfg' orm').  intros.
  cut (BDDconfig_OK cfg'').  cut (config_node_OK cfg'' node2').  cut (config_node_OK cfg'' node1').
  cut (BDDneg_memo_OK_2 cfg'' negm'').  cut (BDDor_memo_OK cfg'' orm'').  intros.
  apply BDDand_keeps_or_memo_OK.  assumption.  assumption.  assumption.  assumption.  assumption.  
  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).  replace orm'' with (snd (snd (snd (BDDimpl cfg' negm' orm' node2 node1)))).
  apply BDDimpl_keeps_or_memo_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H5; reflexivity.  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).
  replace negm'' with (fst (snd (snd (BDDimpl cfg' negm' orm' node2 node1)))).
  apply BDDimpl_keeps_neg_memo_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H5; reflexivity.  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).
  apply BDDimpl_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).
  replace node2' with (fst (snd (BDDimpl cfg' negm' orm' node2 node1))).  apply BDDimpl_node_OK.
  assumption.  assumption.  assumption.  assumption.  assumption.  rewrite H5; reflexivity.
  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).
  apply BDDimpl_keeps_config_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H5; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  replace orm' with (snd (snd (snd (BDDimpl cfg negm orm node1 node2)))).  apply BDDimpl_keeps_or_memo_OK.
  assumption.  assumption.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  replace negm' with (fst (snd (snd (BDDimpl cfg negm orm node1 node2)))).
  apply BDDimpl_keeps_neg_memo_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H4; reflexivity.  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  apply BDDimpl_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  apply BDDimpl_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  replace node1' with (fst (snd (BDDimpl cfg negm orm node1 node2))).  apply BDDimpl_node_OK.
  assumption.  assumption.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  apply BDDimpl_keeps_config_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H4; reflexivity.
Qed.

Definition bool_fun_iff (bf1 bf2 : bool_fun) : bool_fun :=
  fun vb : var_binding => eqb (bf1 vb) (bf2 vb).

Lemma bool_fun_iff_is_and_impl_impl :
 forall bf1 bf2 : bool_fun,
 bool_fun_eq (bool_fun_iff bf1 bf2)
   (bool_fun_and (bool_fun_impl bf1 bf2) (bool_fun_impl bf2 bf1)).
Proof.
  unfold bool_fun_iff, bool_fun_eq, bool_fun_and, bool_fun_impl in |- *.  unfold bool_fun_eval in |- *.
  intros.  elim (bf1 vb).  elim (bf2 vb).  reflexivity.  reflexivity.  reflexivity.
Qed.

Lemma bool_fun_and_preserves_eq :
 forall bf1 bf2 bf1' bf2' : bool_fun,
 bool_fun_eq bf1 bf1' ->
 bool_fun_eq bf2 bf2' ->
 bool_fun_eq (bool_fun_and bf1 bf2) (bool_fun_and bf1' bf2').
Proof.
  intros.  unfold bool_fun_eq in H, H0.  unfold bool_fun_eval in H, H0.
  unfold bool_fun_eq, bool_fun_and in |- *.  unfold bool_fun_eval in |- *.  intro.  rewrite (H vb).
  rewrite (H0 vb).  reflexivity.
Qed.

Lemma bool_fun_impl_preserves_eq :
 forall bf1 bf2 bf1' bf2' : bool_fun,
 bool_fun_eq bf1 bf1' ->
 bool_fun_eq bf2 bf2' ->
 bool_fun_eq (bool_fun_impl bf1 bf2) (bool_fun_impl bf1' bf2').
Proof.
  intros.  unfold bool_fun_eq in H, H0.  unfold bool_fun_eval in H, H0.
  unfold bool_fun_eq, bool_fun_impl in |- *.  unfold bool_fun_eval in |- *.  intro.  rewrite (H vb).
  rewrite (H0 vb).  reflexivity.
Qed.

Lemma bool_fun_iff_preserves_eq :
 forall bf1 bf2 bf1' bf2' : bool_fun,
 bool_fun_eq bf1 bf1' ->
 bool_fun_eq bf2 bf2' ->
 bool_fun_eq (bool_fun_iff bf1 bf2) (bool_fun_iff bf1' bf2').
Proof.
  intros.  unfold bool_fun_eq in H, H0.  unfold bool_fun_eval in H, H0.
  unfold bool_fun_eq, bool_fun_iff in |- *.  unfold bool_fun_eval in |- *.  intro.  rewrite (H vb).
  rewrite (H0 vb).  reflexivity.
Qed.

Lemma BDDiff_is_iff :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (orm : BDDor_memo)
   (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 bool_fun_eq
   (bool_fun_of_BDD (fst (BDDiff cfg negm orm node1 node2))
      (fst (snd (BDDiff cfg negm orm node1 node2))))
   (bool_fun_iff (bool_fun_of_BDD cfg node1) (bool_fun_of_BDD cfg node2)).
Proof.
  intros.  unfold BDDiff in |- *.  elim (prod_sum _ _ (BDDimpl cfg negm orm node1 node2)).
  intros cfg' H4.  elim H4; clear H4.  intro.  elim x; clear x.  intros node1' y.
  elim y; clear y.  intros negm' orm' H4.  rewrite H4.  elim (prod_sum _ _ (BDDimpl cfg' negm' orm' node2 node1)).
  intros cfg'' H5.  elim H5; clear H5.  intro.  elim x; clear x.  intros node2' y.
  elim y; clear y.  intros negm'' orm'' H5.  rewrite H5.  cut (BDDconfig_OK cfg').
  cut (config_node_OK cfg' node1').  cut (config_node_OK cfg' node1).  cut (config_node_OK cfg' node2).
  cut (BDDneg_memo_OK_2 cfg' negm').  cut (BDDor_memo_OK cfg' orm').  intros.
  cut (BDDconfig_OK cfg'').  cut (config_node_OK cfg'' node2').  cut (config_node_OK cfg'' node1').
  cut (BDDneg_memo_OK_2 cfg'' negm'').  cut (BDDor_memo_OK cfg'' orm'').  intros.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_and (bool_fun_of_BDD cfg'' node1')
                (bool_fun_of_BDD cfg'' node2')).
  apply BDDand_is_and.  assumption.  assumption.  assumption.  assumption.  assumption.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_and
                (bool_fun_impl (bool_fun_of_BDD cfg node1)
                   (bool_fun_of_BDD cfg node2))
                (bool_fun_impl (bool_fun_of_BDD cfg node2)
                   (bool_fun_of_BDD cfg node1))).
  apply bool_fun_and_preserves_eq.  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg' node1').
  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).  apply BDDimpl_preserves_bool_fun.
  assumption.  assumption.  assumption.  assumption.  assumption.  assumption.
  rewrite H5; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  replace node1' with (fst (snd (BDDimpl cfg negm orm node1 node2))).  apply BDDimpl_is_impl.
  assumption.  assumption.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  rewrite H4; reflexivity.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_impl (bool_fun_of_BDD cfg' node2)
                (bool_fun_of_BDD cfg' node1)).  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).
  replace node2' with (fst (snd (BDDimpl cfg' negm' orm' node2 node1))).  apply BDDimpl_is_impl.
  assumption.  assumption.  assumption.  assumption.  assumption.  rewrite H5; reflexivity.
  rewrite H5; reflexivity.  apply bool_fun_impl_preserves_eq.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  apply BDDimpl_preserves_bool_fun.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  apply BDDimpl_preserves_bool_fun.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  rewrite H4; reflexivity.  apply bool_fun_eq_symm.
  apply bool_fun_iff_is_and_impl_impl.  
  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).  replace orm'' with (snd (snd (snd (BDDimpl cfg' negm' orm' node2 node1)))).
  apply BDDimpl_keeps_or_memo_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H5; reflexivity.  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).
  replace negm'' with (fst (snd (snd (BDDimpl cfg' negm' orm' node2 node1)))).
  apply BDDimpl_keeps_neg_memo_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H5; reflexivity.  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).
  apply BDDimpl_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).
  replace node2' with (fst (snd (BDDimpl cfg' negm' orm' node2 node1))).  apply BDDimpl_node_OK.
  assumption.  assumption.  assumption.  assumption.  assumption.  rewrite H5; reflexivity.
  rewrite H5; reflexivity.  replace cfg'' with (fst (BDDimpl cfg' negm' orm' node2 node1)).
  apply BDDimpl_keeps_config_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H5; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  replace orm' with (snd (snd (snd (BDDimpl cfg negm orm node1 node2)))).  apply BDDimpl_keeps_or_memo_OK.
  assumption.  assumption.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  replace negm' with (fst (snd (snd (BDDimpl cfg negm orm node1 node2)))).
  apply BDDimpl_keeps_neg_memo_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H4; reflexivity.  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  apply BDDimpl_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  apply BDDimpl_keeps_node_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  replace node1' with (fst (snd (BDDimpl cfg negm orm node1 node2))).  apply BDDimpl_node_OK.
  assumption.  assumption.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  rewrite H4; reflexivity.  replace cfg' with (fst (BDDimpl cfg negm orm node1 node2)).
  apply BDDimpl_keeps_config_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H4; reflexivity.
Qed.

Lemma BDDiff_keeps_node_OK :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (orm : BDDor_memo)
   (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 forall node : ad,
 config_node_OK cfg node ->
 config_node_OK (fst (BDDiff cfg negm orm node1 node2)) node.
Proof.
  intros.  apply nodes_preserved_2 with (cfg := cfg).  assumption.  apply BDDiff_preserves_nodes.
  assumption.  assumption.  assumption.  assumption.  assumption.
Qed.

Lemma BDDiff_preserves_bool_fun :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (orm : BDDor_memo)
   (node1 node2 : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 BDDor_memo_OK cfg orm ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 forall node : ad,
 config_node_OK cfg node ->
 bool_fun_eq (bool_fun_of_BDD (fst (BDDiff cfg negm orm node1 node2)) node)
   (bool_fun_of_BDD cfg node).
Proof.
  intros.  apply nodes_preserved_3.  assumption.  apply BDDiff_keeps_config_OK.
  assumption.  assumption.  assumption.  assumption.  assumption.  apply BDDiff_preserves_nodes.
  assumption.  assumption.  assumption.  assumption.  assumption.  assumption.
Qed.

Definition BDDvar_make (cfg : BDDconfig) (x : BDDvar) :=
  BDDmake cfg x BDDzero BDDone.

Lemma BDDvar_make_keeps_config_OK :
 forall (cfg : BDDconfig) (x : BDDvar),
 BDDconfig_OK cfg -> BDDconfig_OK (fst (BDDvar_make cfg x)).
Proof.
  intros.  refine (proj1 (BDDmake_semantics _ _ _ _ _ _ _ _ _)).  assumption.  
  left; reflexivity.  right; left; reflexivity.  intros.  rewrite (config_OK_zero cfg H) in H0.
  discriminate.  intros.  rewrite (config_OK_one cfg H) in H0.  discriminate.
Qed.

Lemma BDDvar_make_node_OK :
 forall (cfg : BDDconfig) (x : BDDvar),
 BDDconfig_OK cfg ->
 config_node_OK (fst (BDDvar_make cfg x)) (snd (BDDvar_make cfg x)).
Proof.
  intros.  refine
   (proj2 (proj2 (proj2 (proj2 (BDDmake_semantics _ _ _ _ _ _ _ _ _))))).
  assumption.  left; reflexivity.  right; left; reflexivity.  intros.  rewrite (config_OK_zero cfg H) in H0.
  discriminate.  intros.  rewrite (config_OK_one cfg H) in H0.  discriminate.
Qed.

Lemma BDDvar_make_preserves_nodes :
 forall (cfg : BDDconfig) (x : BDDvar),
 BDDconfig_OK cfg -> nodes_preserved cfg (fst (BDDvar_make cfg x)).
Proof.
  intros.  unfold BDDvar_make in |- *.  apply BDDmake_preserves_nodes.  assumption.
Qed.

Lemma BDDvar_make_keeps_neg_memo_OK :
 forall (cfg : BDDconfig) (negm : BDDneg_memo) (x : BDDvar),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm -> BDDneg_memo_OK_2 (fst (BDDvar_make cfg x)) negm.
Proof.
  intros.  apply nodes_preserved_negm_OK with (cfg := cfg).  assumption.  apply BDDvar_make_keeps_config_OK.
  assumption.  apply BDDvar_make_preserves_nodes.  assumption.  assumption.
Qed.

Lemma BDDvar_make_keeps_or_memo_OK :
 forall (cfg : BDDconfig) (orm : BDDor_memo) (x : BDDvar),
 BDDconfig_OK cfg ->
 BDDor_memo_OK cfg orm -> BDDor_memo_OK (fst (BDDvar_make cfg x)) orm.
Proof.
  intros.  apply nodes_preserved_orm_OK with (cfg := cfg).  assumption.  apply BDDvar_make_keeps_config_OK.
  assumption.  apply BDDvar_make_preserves_nodes.  assumption.  assumption.
Qed.

Lemma BDDvar_make_keeps_node_OK :
 forall (cfg : BDDconfig) (x : BDDvar),
 BDDconfig_OK cfg ->
 forall node : ad,
 config_node_OK cfg node -> config_node_OK (fst (BDDvar_make cfg x)) node.
Proof.
  intros.  apply nodes_preserved_2 with (cfg := cfg).  assumption.  apply BDDvar_make_preserves_nodes.  assumption.
Qed.

Lemma BDDvar_make_preserves_bool_fun :
 forall (cfg : BDDconfig) (x : BDDvar),
 BDDconfig_OK cfg ->
 forall node : ad,
 config_node_OK cfg node ->
 bool_fun_eq (bool_fun_of_BDD (fst (BDDvar_make cfg x)) node)
   (bool_fun_of_BDD cfg node).
Proof.
  intros.  apply nodes_preserved_3.  assumption.  apply BDDvar_make_keeps_config_OK.
  assumption.  apply BDDvar_make_preserves_nodes.  assumption.  assumption.
Qed.

Definition bool_fun_var (x : BDDvar) : bool_fun :=
  fun vb : var_binding => vb x.

Lemma BDDvar_make_is_var :
 forall (cfg : BDDconfig) (x : BDDvar),
 BDDconfig_OK cfg ->
 bool_fun_eq
   (bool_fun_of_BDD (fst (BDDvar_make cfg x)) (snd (BDDvar_make cfg x)))
   (bool_fun_var x).
Proof.
  intros.  apply
   bool_fun_eq_trans with (bf2 := bool_fun_if x bool_fun_one bool_fun_zero).
  unfold BDDvar_make in |- *.  apply
   bool_fun_eq_trans
    with
      (bool_fun_if x (bool_fun_of_BDD cfg BDDone)
         (bool_fun_of_BDD cfg BDDzero)).
  apply BDDmake_bool_fun.  assumption.  left; reflexivity.  right; left; reflexivity.  
  intro.  inversion H0.  inversion H1.  inversion H2.  rewrite (config_OK_zero cfg H) in H3; discriminate.
  intro.  inversion H0.  inversion H1.  inversion H2.  rewrite (config_OK_one cfg H) in H3; discriminate.
  apply bool_fun_if_preserves_eq.  apply bool_fun_of_BDDone.  assumption.  
  apply bool_fun_of_BDDzero.  assumption.  unfold bool_fun_eq, bool_fun_one, bool_fun_zero, bool_fun_var, bool_fun_if
   in |- *.
  unfold bool_fun_eval in |- *.  intro.  elim (vb x).  reflexivity.  reflexivity.  
Qed.




Inductive bool_expr : Set :=
  | Zero : bool_expr
  | One : bool_expr
  | Var : BDDvar -> bool_expr
  | Neg : bool_expr -> bool_expr
  | Or : bool_expr -> bool_expr -> bool_expr
  | ANd : bool_expr -> bool_expr -> bool_expr
  | Impl : bool_expr -> bool_expr -> bool_expr
  | Iff : bool_expr -> bool_expr -> bool_expr.

Fixpoint bool_fun_of_bool_expr (be : bool_expr) : bool_fun :=
  match be with
  | Zero => bool_fun_zero
  | One => bool_fun_one
  | Var x => bool_fun_var x
  | Neg be' => bool_fun_neg (bool_fun_of_bool_expr be')
  | Or be1 be2 =>
      bool_fun_or (bool_fun_of_bool_expr be1) (bool_fun_of_bool_expr be2)
  | ANd be1 be2 =>
      bool_fun_and (bool_fun_of_bool_expr be1) (bool_fun_of_bool_expr be2)
  | Impl be1 be2 =>
      bool_fun_impl (bool_fun_of_bool_expr be1) (bool_fun_of_bool_expr be2)
  | Iff be1 be2 =>
      bool_fun_iff (bool_fun_of_bool_expr be1) (bool_fun_of_bool_expr be2)
  end.

Fixpoint BDDof_bool_expr (cfg : BDDconfig) (negm : BDDneg_memo)
 (orm : BDDor_memo) (be : bool_expr) {struct be} :
 BDDconfig * (ad * (BDDneg_memo * BDDor_memo)) :=
  match be with
  | Zero => (cfg, (BDDzero, (negm, orm)))
  | One => (cfg, (BDDone, (negm, orm)))
  | Var x =>
      match BDDvar_make cfg x with
      | (cfg', node) => (cfg', (node, (negm, orm)))
      end
  | Neg be' =>
      match BDDof_bool_expr cfg negm orm be' with
      | (cfg', (node, (negm', orm'))) =>
          match BDDneg cfg' negm' node with
          | (cfg'', (node', negm'')) => (cfg'', (node', (negm'', orm')))
          end
      end
  | Or be1 be2 =>
      match BDDof_bool_expr cfg negm orm be1 with
      | (cfg', (node1, (negm', orm'))) =>
          match BDDof_bool_expr cfg' negm' orm' be2 with
          | (cfg'', (node2, (negm'', orm''))) =>
              match BDDor cfg'' orm'' node1 node2 with
              | (cfg''', (node, orm''')) =>
                  (cfg''', (node, (negm'', orm''')))
              end
          end
      end
  | ANd be1 be2 =>
      match BDDof_bool_expr cfg negm orm be1 with
      | (cfg', (node1, (negm', orm'))) =>
          match BDDof_bool_expr cfg' negm' orm' be2 with
          | (cfg'', (node2, (negm'', orm''))) =>
              BDDand cfg'' negm'' orm'' node1 node2
          end
      end
  | Impl be1 be2 =>
      match BDDof_bool_expr cfg negm orm be1 with
      | (cfg', (node1, (negm', orm'))) =>
          match BDDof_bool_expr cfg' negm' orm' be2 with
          | (cfg'', (node2, (negm'', orm''))) =>
              BDDimpl cfg'' negm'' orm'' node1 node2
          end
      end
  | Iff be1 be2 =>
      match BDDof_bool_expr cfg negm orm be1 with
      | (cfg', (node1, (negm', orm'))) =>
          match BDDof_bool_expr cfg' negm' orm' be2 with
          | (cfg'', (node2, (negm'', orm''))) =>
              BDDiff cfg'' negm'' orm'' node1 node2
          end
      end
  end.

Lemma BDDof_bool_expr_correct :
 forall (be : bool_expr) (cfg : BDDconfig) (negm : BDDneg_memo)
   (orm : BDDor_memo),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg negm ->
 BDDor_memo_OK cfg orm ->
 BDDconfig_OK (fst (BDDof_bool_expr cfg negm orm be)) /\
 config_node_OK (fst (BDDof_bool_expr cfg negm orm be))
   (fst (snd (BDDof_bool_expr cfg negm orm be))) /\
 BDDneg_memo_OK_2 (fst (BDDof_bool_expr cfg negm orm be))
   (fst (snd (snd (BDDof_bool_expr cfg negm orm be)))) /\
 BDDor_memo_OK (fst (BDDof_bool_expr cfg negm orm be))
   (snd (snd (snd (BDDof_bool_expr cfg negm orm be)))) /\
 nodes_preserved cfg (fst (BDDof_bool_expr cfg negm orm be)) /\
 bool_fun_eq
   (bool_fun_of_BDD (fst (BDDof_bool_expr cfg negm orm be))
      (fst (snd (BDDof_bool_expr cfg negm orm be))))
   (bool_fun_of_bool_expr be).
Proof.
  simple induction be.  intros.  simpl in |- *.  split.  assumption.  split.  left; reflexivity.
  split.  assumption.  split.  assumption.  split.  unfold nodes_preserved in |- *.  intros.
  assumption.  apply bool_fun_of_BDDzero.  assumption.  simpl in |- *.  split.  assumption.
  split.  right; left; reflexivity.  split.  assumption.  split.  assumption.
  split.  unfold nodes_preserved in |- *.  intros; assumption.  apply bool_fun_of_BDDone.
  assumption.  simpl in |- *.  intros.  elim (prod_sum _ _ (BDDvar_make cfg b)).  intros cfg' H2.
  elim H2; clear H2.  intros node H2.  rewrite H2.  simpl in |- *.  split.  replace cfg' with (fst (BDDvar_make cfg b)).
  apply BDDvar_make_keeps_config_OK.  assumption.  rewrite H2; reflexivity.  
  split.  replace cfg' with (fst (BDDvar_make cfg b)).  replace node with (snd (BDDvar_make cfg b)).
  apply BDDvar_make_node_OK.  assumption.  rewrite H2; reflexivity.  rewrite H2; reflexivity.
  split.  replace cfg' with (fst (BDDvar_make cfg b)).  apply BDDvar_make_keeps_neg_memo_OK.
  assumption.  assumption.  rewrite H2; reflexivity.  split.  replace cfg' with (fst (BDDvar_make cfg b)).
  apply BDDvar_make_keeps_or_memo_OK.  assumption.  assumption.  rewrite H2; reflexivity.
  split.  replace cfg' with (fst (BDDvar_make cfg b)).  apply BDDvar_make_preserves_nodes.
  assumption.  rewrite H2; reflexivity.  replace cfg' with (fst (BDDvar_make cfg b)).
  replace node with (snd (BDDvar_make cfg b)).  apply BDDvar_make_is_var.  assumption.
  rewrite H2; reflexivity.  rewrite H2; reflexivity.  intros.  simpl in |- *.
  elim (prod_sum _ _ (BDDof_bool_expr cfg negm orm b)).  intros cfg' H3.  elim H3; clear H3.
  intro.  elim x; clear x.  intros node y.  elim y; clear y.  intros negm' orm' H3.
  rewrite H3.  elim (prod_sum _ _ (BDDneg cfg' negm' node)).  intros cfg'' H4.
  elim H4; clear H4.  intro.  elim x; clear x.  intros node' negm''.  intro H4.
  rewrite H4.  simpl in |- *.  cut (BDDconfig_OK cfg').  cut (config_node_OK cfg' node).
  cut (BDDneg_memo_OK_2 cfg' negm').  cut (BDDor_memo_OK cfg' orm').  cut (nodes_preserved cfg cfg').
  cut (bool_fun_eq (bool_fun_of_BDD cfg' node) (bool_fun_of_bool_expr b)).
  intros.  split.  replace cfg'' with (fst (BDDneg cfg' negm' node)).  apply BDDneg_keeps_config_OK.
  assumption.  assumption.  assumption.  rewrite H4; reflexivity.  split.
  replace cfg'' with (fst (BDDneg cfg' negm' node)).  replace node' with (fst (snd (BDDneg cfg' negm' node))).
  apply BDDneg_node_OK.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  rewrite H4; reflexivity.  split.  replace cfg'' with (fst (BDDneg cfg' negm' node)).
  replace negm'' with (snd (snd (BDDneg cfg' negm' node))).  apply BDDneg_keeps_neg_memo_OK.
  assumption.  assumption.  assumption.  rewrite H4; reflexivity.  rewrite H4; reflexivity.
  split.  replace cfg'' with (fst (BDDneg cfg' negm' node)).  apply BDDneg_keeps_or_memo_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.
  split.  apply nodes_preserved_trans with (cfg2 := cfg').  assumption.  replace cfg'' with (fst (BDDneg cfg' negm' node)).
  apply BDDneg_preserves_nodes.  assumption.  assumption.  assumption.  rewrite H4; reflexivity.

apply
 bool_fun_eq_trans with (bf2 := bool_fun_neg (bool_fun_of_BDD cfg' node)).
replace cfg'' with (fst (BDDneg cfg' negm' node)).
replace node' with (fst (snd (BDDneg cfg' negm' node))).
apply BDDneg_is_neg.
assumption.

assumption.

assumption.

rewrite H4; reflexivity.

rewrite H4; reflexivity.

apply bool_fun_eq_neg_1.
assumption.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm b)).
replace node with (fst (snd (BDDof_bool_expr cfg negm orm b))).
refine (proj2 (proj2 (proj2 (proj2 (proj2 (H _ _ _ _ _ _)))))).
assumption.

assumption.

assumption.

rewrite H3; reflexivity.

rewrite H3; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm b)).
refine (proj1 (proj2 (proj2 (proj2 (proj2 (H _ _ _ _ _ _)))))).
assumption.

assumption.

assumption.

rewrite H3; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm b)).
replace orm' with (snd (snd (snd (BDDof_bool_expr cfg negm orm b)))).
refine (proj1 (proj2 (proj2 (proj2 (H _ _ _ _ _ _))))).
assumption.

assumption.

assumption.

rewrite H3; reflexivity.

rewrite H3; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm b)).
replace negm' with (fst (snd (snd (BDDof_bool_expr cfg negm orm b)))).
refine (proj1 (proj2 (proj2 (H _ _ _ _ _ _)))).
assumption.

assumption.

assumption.

rewrite H3; reflexivity.

rewrite H3; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm b)).
replace node with (fst (snd (BDDof_bool_expr cfg negm orm b))).
refine (proj1 (proj2 (H _ _ _ _ _ _))).
assumption.

assumption.

assumption.

rewrite H3; reflexivity.

rewrite H3; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm b)).
refine (proj1 (H _ _ _ _ _ _)).
assumption.

assumption.

assumption.

rewrite H3; reflexivity.

clear be.
intros be1 H.
intros be2 H0.
intros.
simpl in |- *.
elim (prod_sum _ _ (BDDof_bool_expr cfg negm orm be1)).
intros cfg' H4.
elim H4; clear H4.
intro.
elim x; clear x.
intros node1 y.
elim y; clear y; intros negm' orm' H4.
rewrite H4.
elim (prod_sum _ _ (BDDof_bool_expr cfg' negm' orm' be2)).
intros cfg'' H5; elim H5; clear H5; intro; elim x; clear x; intros node2 y;
 elim y; clear y; intros negm'' orm'' H5; rewrite H5.
elim (prod_sum _ _ (BDDor cfg'' orm'' node1 node2)).
intros cfg''' H6.
elim H6; clear H6.
intro.
elim x; clear x.
intros node orm''' H6.
rewrite H6.
simpl in |- *.
cut (BDDconfig_OK cfg').
cut (config_node_OK cfg' node1).
cut (BDDneg_memo_OK_2 cfg' negm').
cut (BDDor_memo_OK cfg' orm').
cut (nodes_preserved cfg cfg').
cut (bool_fun_eq (bool_fun_of_BDD cfg' node1) (bool_fun_of_bool_expr be1)).
intros.
cut (BDDconfig_OK cfg'').
cut (config_node_OK cfg'' node2).
cut (BDDneg_memo_OK_2 cfg'' negm'').
cut (BDDor_memo_OK cfg'' orm'').
cut (nodes_preserved cfg' cfg'').
cut (bool_fun_eq (bool_fun_of_BDD cfg'' node2) (bool_fun_of_bool_expr be2)).
intros.
cut (config_node_OK cfg'' node1).
intros.
split.
replace cfg''' with (fst (BDDor cfg'' orm'' node1 node2)).
apply BDDor_keeps_config_OK.
assumption.

assumption.

assumption.

assumption.

rewrite H6; reflexivity.

split.
replace cfg''' with (fst (BDDor cfg'' orm'' node1 node2)).
replace node with (fst (snd (BDDor cfg'' orm'' node1 node2))).
apply BDDor_node_OK.
assumption.

assumption.

assumption.

assumption.

rewrite H6; reflexivity.

rewrite H6; reflexivity.

split.
replace cfg''' with (fst (BDDor cfg'' orm'' node1 node2)).
apply BDDor_keeps_neg_memo_OK.
assumption.

assumption.

assumption.

assumption.

assumption.

rewrite H6; reflexivity.

split.
replace cfg''' with (fst (BDDor cfg'' orm'' node1 node2)).
replace orm''' with (snd (snd (BDDor cfg'' orm'' node1 node2))).
apply BDDor_keeps_or_memo_OK.
assumption.

assumption.

assumption.

assumption.

rewrite H6; reflexivity.

rewrite H6; reflexivity.

split.
apply nodes_preserved_trans with (cfg2 := cfg').
assumption.

apply nodes_preserved_trans with (cfg2 := cfg'').
assumption.

replace cfg''' with (fst (BDDor cfg'' orm'' node1 node2)).
apply BDDor_preserves_nodes.
assumption.

assumption.

assumption.

assumption.

rewrite H6; reflexivity.

apply
 bool_fun_eq_trans
  with
    (bf2 := bool_fun_or (bool_fun_of_BDD cfg'' node1)
              (bool_fun_of_BDD cfg'' node2)).
replace cfg''' with (fst (BDDor cfg'' orm'' node1 node2)).
replace node with (fst (snd (BDDor cfg'' orm'' node1 node2))).
apply BDDor_is_or.
assumption.

assumption.

assumption.

assumption.

rewrite H6; reflexivity.

rewrite H6; reflexivity.

apply bool_fun_or_preserves_eq.
apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg' node1).
apply nodes_preserved_3.
assumption.

assumption.

assumption.

assumption.

assumption.

assumption.

apply nodes_preserved_2 with (cfg := cfg').
assumption.

assumption.

replace cfg'' with (fst (BDDof_bool_expr cfg' negm' orm' be2)).
replace node2 with (fst (snd (BDDof_bool_expr cfg' negm' orm' be2))).
refine (proj2 (proj2 (proj2 (proj2 (proj2 (H0 _ _ _ _ _ _)))))).
assumption.

assumption.

assumption.

rewrite H5; reflexivity.

rewrite H5; reflexivity.

replace cfg'' with (fst (BDDof_bool_expr cfg' negm' orm' be2)).
refine (proj1 (proj2 (proj2 (proj2 (proj2 (H0 _ _ _ _ _ _)))))).
assumption.

assumption.

assumption.

rewrite H5; reflexivity.

replace cfg'' with (fst (BDDof_bool_expr cfg' negm' orm' be2)).
replace orm'' with (snd (snd (snd (BDDof_bool_expr cfg' negm' orm' be2)))).
refine (proj1 (proj2 (proj2 (proj2 (H0 _ _ _ _ _ _))))).
assumption.

assumption.

assumption.

rewrite H5; reflexivity.

rewrite H5; reflexivity.

replace cfg'' with (fst (BDDof_bool_expr cfg' negm' orm' be2)).
replace negm'' with (fst (snd (snd (BDDof_bool_expr cfg' negm' orm' be2)))).
refine (proj1 (proj2 (proj2 (H0 _ _ _ _ _ _)))).
assumption.

assumption.

assumption.

rewrite H5; reflexivity.

rewrite H5; reflexivity.

replace cfg'' with (fst (BDDof_bool_expr cfg' negm' orm' be2)).
replace node2 with (fst (snd (BDDof_bool_expr cfg' negm' orm' be2))).
refine (proj1 (proj2 (H0 _ _ _ _ _ _))).
assumption.

assumption.

assumption.

rewrite H5; reflexivity.

rewrite H5; reflexivity.

replace cfg'' with (fst (BDDof_bool_expr cfg' negm' orm' be2)).
refine (proj1 (H0 _ _ _ _ _ _)).
assumption.

assumption.

assumption.

rewrite H5; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm be1)).
replace node1 with (fst (snd (BDDof_bool_expr cfg negm orm be1))).
refine (proj2 (proj2 (proj2 (proj2 (proj2 (H _ _ _ _ _ _)))))).
assumption.

assumption.

assumption.

rewrite H4; reflexivity.

rewrite H4; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm be1)).
refine (proj1 (proj2 (proj2 (proj2 (proj2 (H _ _ _ _ _ _)))))).
assumption.

assumption.

assumption.

rewrite H4; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm be1)).
replace orm' with (snd (snd (snd (BDDof_bool_expr cfg negm orm be1)))).
refine (proj1 (proj2 (proj2 (proj2 (H _ _ _ _ _ _))))).
assumption.

assumption.

assumption.

rewrite H4; reflexivity.

rewrite H4; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm be1)).
replace negm' with (fst (snd (snd (BDDof_bool_expr cfg negm orm be1)))).
refine (proj1 (proj2 (proj2 (H _ _ _ _ _ _)))).
assumption.

assumption.

assumption.

rewrite H4; reflexivity.

rewrite H4; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm be1)).
replace node1 with (fst (snd (BDDof_bool_expr cfg negm orm be1))).
refine (proj1 (proj2 (H _ _ _ _ _ _))).
assumption.

assumption.

assumption.

rewrite H4; reflexivity.

rewrite H4; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm be1)).
refine (proj1 (H _ _ _ _ _ _)).
assumption.

assumption.

assumption.

rewrite H4; reflexivity.

clear be.
intros be1 H.
intros be2 H0.
intros.
simpl in |- *.
elim (prod_sum _ _ (BDDof_bool_expr cfg negm orm be1)).
intros cfg' H4.
elim H4; clear H4.
intro.
elim x; clear x.
intros node1 y.
elim y; clear y; intros negm' orm' H4.
rewrite H4.
elim (prod_sum _ _ (BDDof_bool_expr cfg' negm' orm' be2)).
intros cfg'' H5; elim H5; clear H5; intro; elim x; clear x; intros node2 y;
 elim y; clear y; intros negm'' orm'' H5; rewrite H5.
cut (BDDconfig_OK cfg').
cut (config_node_OK cfg' node1).
cut (BDDneg_memo_OK_2 cfg' negm').
cut (BDDor_memo_OK cfg' orm').
cut (nodes_preserved cfg cfg').
cut (bool_fun_eq (bool_fun_of_BDD cfg' node1) (bool_fun_of_bool_expr be1)).
intros.
cut (BDDconfig_OK cfg'').
cut (config_node_OK cfg'' node2).
cut (BDDneg_memo_OK_2 cfg'' negm'').
cut (BDDor_memo_OK cfg'' orm'').
cut (nodes_preserved cfg' cfg'').
cut (bool_fun_eq (bool_fun_of_BDD cfg'' node2) (bool_fun_of_bool_expr be2)).
intros.
cut (config_node_OK cfg'' node1).
intros.
split.
apply BDDand_keeps_config_OK.
assumption.

assumption.

assumption.

assumption.

assumption.

split.
apply BDDand_node_OK.
assumption.

assumption.

assumption.

assumption.

assumption.

split.
apply BDDand_keeps_neg_memo_OK.
assumption.

assumption.

assumption.

assumption.

assumption.

split.
apply BDDand_keeps_or_memo_OK.
assumption.

assumption.

assumption.

assumption.

assumption.

split.
apply nodes_preserved_trans with (cfg2 := cfg').
assumption.

apply nodes_preserved_trans with (cfg2 := cfg'').
assumption.

apply BDDand_preserves_nodes.
assumption.

assumption.

assumption.

assumption.

assumption.

apply
 bool_fun_eq_trans
  with
    (bf2 := bool_fun_and (bool_fun_of_BDD cfg'' node1)
              (bool_fun_of_BDD cfg'' node2)).
apply BDDand_is_and.
assumption.

assumption.

assumption.

assumption.

assumption.

apply bool_fun_and_preserves_eq.
apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg' node1).
apply nodes_preserved_3.
assumption.

assumption.

assumption.

assumption.

assumption.

assumption.

apply nodes_preserved_2 with (cfg := cfg').
assumption.

assumption.

replace cfg'' with (fst (BDDof_bool_expr cfg' negm' orm' be2)).
replace node2 with (fst (snd (BDDof_bool_expr cfg' negm' orm' be2))).
refine (proj2 (proj2 (proj2 (proj2 (proj2 (H0 _ _ _ _ _ _)))))).
assumption.

assumption.

assumption.

rewrite H5; reflexivity.

rewrite H5; reflexivity.

replace cfg'' with (fst (BDDof_bool_expr cfg' negm' orm' be2)).
refine (proj1 (proj2 (proj2 (proj2 (proj2 (H0 _ _ _ _ _ _)))))).
assumption.

assumption.

assumption.

rewrite H5; reflexivity.

replace cfg'' with (fst (BDDof_bool_expr cfg' negm' orm' be2)).
replace orm'' with (snd (snd (snd (BDDof_bool_expr cfg' negm' orm' be2)))).
refine (proj1 (proj2 (proj2 (proj2 (H0 _ _ _ _ _ _))))).
assumption.

assumption.

assumption.

rewrite H5; reflexivity.

rewrite H5; reflexivity.

replace cfg'' with (fst (BDDof_bool_expr cfg' negm' orm' be2)).
replace negm'' with (fst (snd (snd (BDDof_bool_expr cfg' negm' orm' be2)))).
refine (proj1 (proj2 (proj2 (H0 _ _ _ _ _ _)))).
assumption.

assumption.

assumption.

rewrite H5; reflexivity.

rewrite H5; reflexivity.

replace cfg'' with (fst (BDDof_bool_expr cfg' negm' orm' be2)).
replace node2 with (fst (snd (BDDof_bool_expr cfg' negm' orm' be2))).
refine (proj1 (proj2 (H0 _ _ _ _ _ _))).
assumption.

assumption.

assumption.

rewrite H5; reflexivity.

rewrite H5; reflexivity.

replace cfg'' with (fst (BDDof_bool_expr cfg' negm' orm' be2)).
refine (proj1 (H0 _ _ _ _ _ _)).
assumption.

assumption.

assumption.

rewrite H5; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm be1)).
replace node1 with (fst (snd (BDDof_bool_expr cfg negm orm be1))).
refine (proj2 (proj2 (proj2 (proj2 (proj2 (H _ _ _ _ _ _)))))).
assumption.

assumption.

assumption.

rewrite H4; reflexivity.

rewrite H4; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm be1)).
refine (proj1 (proj2 (proj2 (proj2 (proj2 (H _ _ _ _ _ _)))))).
assumption.

assumption.

assumption.

rewrite H4; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm be1)).
replace orm' with (snd (snd (snd (BDDof_bool_expr cfg negm orm be1)))).
refine (proj1 (proj2 (proj2 (proj2 (H _ _ _ _ _ _))))).
assumption.

assumption.

assumption.

rewrite H4; reflexivity.

rewrite H4; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm be1)).
replace negm' with (fst (snd (snd (BDDof_bool_expr cfg negm orm be1)))).
refine (proj1 (proj2 (proj2 (H _ _ _ _ _ _)))).
assumption.

assumption.

assumption.

rewrite H4; reflexivity.

rewrite H4; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm be1)).
replace node1 with (fst (snd (BDDof_bool_expr cfg negm orm be1))).
refine (proj1 (proj2 (H _ _ _ _ _ _))).
assumption.

assumption.

assumption.

rewrite H4; reflexivity.

rewrite H4; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm be1)).
refine (proj1 (H _ _ _ _ _ _)).
assumption.

assumption.

assumption.

rewrite H4; reflexivity.

(************ End of script.v ********)


clear be.
intros be1 H.
intros be2 H0.
intros.
simpl in |- *.
elim (prod_sum _ _ (BDDof_bool_expr cfg negm orm be1)).
intros cfg' H4.
elim H4; clear H4.
intro.
elim x; clear x.
intros node1 y.
elim y; clear y; intros negm' orm' H4.
rewrite H4.
elim (prod_sum _ _ (BDDof_bool_expr cfg' negm' orm' be2)).
intros cfg'' H5; elim H5; clear H5; intro; elim x; clear x; intros node2 y;
 elim y; clear y; intros negm'' orm'' H5; rewrite H5.
cut (BDDconfig_OK cfg').
cut (config_node_OK cfg' node1).
cut (BDDneg_memo_OK_2 cfg' negm').
cut (BDDor_memo_OK cfg' orm').
cut (nodes_preserved cfg cfg').
cut (bool_fun_eq (bool_fun_of_BDD cfg' node1) (bool_fun_of_bool_expr be1)).
intros.
cut (BDDconfig_OK cfg'').
cut (config_node_OK cfg'' node2).
cut (BDDneg_memo_OK_2 cfg'' negm'').
cut (BDDor_memo_OK cfg'' orm'').
cut (nodes_preserved cfg' cfg'').
cut (bool_fun_eq (bool_fun_of_BDD cfg'' node2) (bool_fun_of_bool_expr be2)).
intros.
cut (config_node_OK cfg'' node1).
intros.
split.
apply BDDimpl_keeps_config_OK.
assumption.

assumption.

assumption.

assumption.

assumption.

split.
apply BDDimpl_node_OK.
assumption.

assumption.

assumption.

assumption.

assumption.

split.
apply BDDimpl_keeps_neg_memo_OK.
assumption.

assumption.

assumption.

assumption.

assumption.

split.
apply BDDimpl_keeps_or_memo_OK.
assumption.

assumption.

assumption.

assumption.

assumption.

split.
apply nodes_preserved_trans with (cfg2 := cfg').
assumption.

apply nodes_preserved_trans with (cfg2 := cfg'').
assumption.

apply BDDimpl_preserves_nodes.
assumption.

assumption.

assumption.

assumption.

assumption.

apply
 bool_fun_eq_trans
  with
    (bf2 := bool_fun_impl (bool_fun_of_BDD cfg'' node1)
              (bool_fun_of_BDD cfg'' node2)).
apply BDDimpl_is_impl.
assumption.

assumption.

assumption.

assumption.

assumption.

apply bool_fun_impl_preserves_eq.
apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg' node1).
apply nodes_preserved_3.
assumption.

assumption.

assumption.

assumption.

assumption.

assumption.

apply nodes_preserved_2 with (cfg := cfg').
assumption.

assumption.

replace cfg'' with (fst (BDDof_bool_expr cfg' negm' orm' be2)).
replace node2 with (fst (snd (BDDof_bool_expr cfg' negm' orm' be2))).
refine (proj2 (proj2 (proj2 (proj2 (proj2 (H0 _ _ _ _ _ _)))))).
assumption.

assumption.

assumption.

rewrite H5; reflexivity.

rewrite H5; reflexivity.

replace cfg'' with (fst (BDDof_bool_expr cfg' negm' orm' be2)).
refine (proj1 (proj2 (proj2 (proj2 (proj2 (H0 _ _ _ _ _ _)))))).
assumption.

assumption.

assumption.

rewrite H5; reflexivity.

replace cfg'' with (fst (BDDof_bool_expr cfg' negm' orm' be2)).
replace orm'' with (snd (snd (snd (BDDof_bool_expr cfg' negm' orm' be2)))).
refine (proj1 (proj2 (proj2 (proj2 (H0 _ _ _ _ _ _))))).
assumption.

assumption.

assumption.

rewrite H5; reflexivity.

rewrite H5; reflexivity.

replace cfg'' with (fst (BDDof_bool_expr cfg' negm' orm' be2)).
replace negm'' with (fst (snd (snd (BDDof_bool_expr cfg' negm' orm' be2)))).
refine (proj1 (proj2 (proj2 (H0 _ _ _ _ _ _)))).
assumption.

assumption.

assumption.

rewrite H5; reflexivity.

rewrite H5; reflexivity.

replace cfg'' with (fst (BDDof_bool_expr cfg' negm' orm' be2)).
replace node2 with (fst (snd (BDDof_bool_expr cfg' negm' orm' be2))).
refine (proj1 (proj2 (H0 _ _ _ _ _ _))).
assumption.

assumption.

assumption.

rewrite H5; reflexivity.

rewrite H5; reflexivity.

replace cfg'' with (fst (BDDof_bool_expr cfg' negm' orm' be2)).
refine (proj1 (H0 _ _ _ _ _ _)).
assumption.

assumption.

assumption.

rewrite H5; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm be1)).
replace node1 with (fst (snd (BDDof_bool_expr cfg negm orm be1))).
refine (proj2 (proj2 (proj2 (proj2 (proj2 (H _ _ _ _ _ _)))))).
assumption.

assumption.

assumption.

rewrite H4; reflexivity.

rewrite H4; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm be1)).
refine (proj1 (proj2 (proj2 (proj2 (proj2 (H _ _ _ _ _ _)))))).
assumption.

assumption.

assumption.

rewrite H4; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm be1)).
replace orm' with (snd (snd (snd (BDDof_bool_expr cfg negm orm be1)))).
refine (proj1 (proj2 (proj2 (proj2 (H _ _ _ _ _ _))))).
assumption.

assumption.

assumption.

rewrite H4; reflexivity.

rewrite H4; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm be1)).
replace negm' with (fst (snd (snd (BDDof_bool_expr cfg negm orm be1)))).
refine (proj1 (proj2 (proj2 (H _ _ _ _ _ _)))).
assumption.

assumption.

assumption.

rewrite H4; reflexivity.

rewrite H4; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm be1)).
replace node1 with (fst (snd (BDDof_bool_expr cfg negm orm be1))).
refine (proj1 (proj2 (H _ _ _ _ _ _))).
assumption.

assumption.

assumption.

rewrite H4; reflexivity.

rewrite H4; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm be1)).
refine (proj1 (H _ _ _ _ _ _)).
assumption.

assumption.

assumption.

rewrite H4; reflexivity.
(*********** End of tempimpl.v ***********************)



clear be.
intros be1 H.
intros be2 H0.
intros.
simpl in |- *.
elim (prod_sum _ _ (BDDof_bool_expr cfg negm orm be1)).
intros cfg' H4.
elim H4; clear H4.
intro.
elim x; clear x.
intros node1 y.
elim y; clear y; intros negm' orm' H4.
rewrite H4.
elim (prod_sum _ _ (BDDof_bool_expr cfg' negm' orm' be2)).
intros cfg'' H5; elim H5; clear H5; intro; elim x; clear x; intros node2 y;
 elim y; clear y; intros negm'' orm'' H5; rewrite H5.
cut (BDDconfig_OK cfg').
cut (config_node_OK cfg' node1).
cut (BDDneg_memo_OK_2 cfg' negm').
cut (BDDor_memo_OK cfg' orm').
cut (nodes_preserved cfg cfg').
cut (bool_fun_eq (bool_fun_of_BDD cfg' node1) (bool_fun_of_bool_expr be1)).
intros.
cut (BDDconfig_OK cfg'').
cut (config_node_OK cfg'' node2).
cut (BDDneg_memo_OK_2 cfg'' negm'').
cut (BDDor_memo_OK cfg'' orm'').
cut (nodes_preserved cfg' cfg'').
cut (bool_fun_eq (bool_fun_of_BDD cfg'' node2) (bool_fun_of_bool_expr be2)).
intros.
cut (config_node_OK cfg'' node1).
intros.
split.
apply BDDiff_keeps_config_OK.
assumption.

assumption.

assumption.

assumption.

assumption.

split.
apply BDDiff_node_OK.
assumption.

assumption.

assumption.

assumption.

assumption.

split.
apply BDDiff_keeps_neg_memo_OK.
assumption.

assumption.

assumption.

assumption.

assumption.

split.
apply BDDiff_keeps_or_memo_OK.
assumption.

assumption.

assumption.

assumption.

assumption.

split.
apply nodes_preserved_trans with (cfg2 := cfg').
assumption.

apply nodes_preserved_trans with (cfg2 := cfg'').
assumption.

apply BDDiff_preserves_nodes.
assumption.

assumption.

assumption.

assumption.

assumption.

apply
 bool_fun_eq_trans
  with
    (bf2 := bool_fun_iff (bool_fun_of_BDD cfg'' node1)
              (bool_fun_of_BDD cfg'' node2)).
apply BDDiff_is_iff.
assumption.

assumption.

assumption.

assumption.

assumption.

apply bool_fun_iff_preserves_eq.
apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg' node1).
apply nodes_preserved_3.
assumption.

assumption.

assumption.

assumption.

assumption.

assumption.

apply nodes_preserved_2 with (cfg := cfg').
assumption.

assumption.

replace cfg'' with (fst (BDDof_bool_expr cfg' negm' orm' be2)).
replace node2 with (fst (snd (BDDof_bool_expr cfg' negm' orm' be2))).
refine (proj2 (proj2 (proj2 (proj2 (proj2 (H0 _ _ _ _ _ _)))))).
assumption.

assumption.

assumption.

rewrite H5; reflexivity.

rewrite H5; reflexivity.

replace cfg'' with (fst (BDDof_bool_expr cfg' negm' orm' be2)).
refine (proj1 (proj2 (proj2 (proj2 (proj2 (H0 _ _ _ _ _ _)))))).
assumption.

assumption.

assumption.

rewrite H5; reflexivity.

replace cfg'' with (fst (BDDof_bool_expr cfg' negm' orm' be2)).
replace orm'' with (snd (snd (snd (BDDof_bool_expr cfg' negm' orm' be2)))).
refine (proj1 (proj2 (proj2 (proj2 (H0 _ _ _ _ _ _))))).
assumption.

assumption.

assumption.

rewrite H5; reflexivity.

rewrite H5; reflexivity.

replace cfg'' with (fst (BDDof_bool_expr cfg' negm' orm' be2)).
replace negm'' with (fst (snd (snd (BDDof_bool_expr cfg' negm' orm' be2)))).
refine (proj1 (proj2 (proj2 (H0 _ _ _ _ _ _)))).
assumption.

assumption.

assumption.

rewrite H5; reflexivity.

rewrite H5; reflexivity.

replace cfg'' with (fst (BDDof_bool_expr cfg' negm' orm' be2)).
replace node2 with (fst (snd (BDDof_bool_expr cfg' negm' orm' be2))).
refine (proj1 (proj2 (H0 _ _ _ _ _ _))).
assumption.

assumption.

assumption.

rewrite H5; reflexivity.

rewrite H5; reflexivity.

replace cfg'' with (fst (BDDof_bool_expr cfg' negm' orm' be2)).
refine (proj1 (H0 _ _ _ _ _ _)).
assumption.

assumption.

assumption.

rewrite H5; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm be1)).
replace node1 with (fst (snd (BDDof_bool_expr cfg negm orm be1))).
refine (proj2 (proj2 (proj2 (proj2 (proj2 (H _ _ _ _ _ _)))))).
assumption.

assumption.

assumption.

rewrite H4; reflexivity.

rewrite H4; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm be1)).
refine (proj1 (proj2 (proj2 (proj2 (proj2 (H _ _ _ _ _ _)))))).
assumption.

assumption.

assumption.

rewrite H4; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm be1)).
replace orm' with (snd (snd (snd (BDDof_bool_expr cfg negm orm be1)))).
refine (proj1 (proj2 (proj2 (proj2 (H _ _ _ _ _ _))))).
assumption.

assumption.

assumption.

rewrite H4; reflexivity.

rewrite H4; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm be1)).
replace negm' with (fst (snd (snd (BDDof_bool_expr cfg negm orm be1)))).
refine (proj1 (proj2 (proj2 (H _ _ _ _ _ _)))).
assumption.

assumption.

assumption.

rewrite H4; reflexivity.

rewrite H4; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm be1)).
replace node1 with (fst (snd (BDDof_bool_expr cfg negm orm be1))).
refine (proj1 (proj2 (H _ _ _ _ _ _))).
assumption.

assumption.

assumption.

rewrite H4; reflexivity.

rewrite H4; reflexivity.

replace cfg' with (fst (BDDof_bool_expr cfg negm orm be1)).
refine (proj1 (H _ _ _ _ _ _)).
assumption.

assumption.

assumption.

rewrite H4; reflexivity.

Qed.