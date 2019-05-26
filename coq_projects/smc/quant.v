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
Require Import Compare.
Require Import Peano_dec.

Require Import misc.
Require Import bool_fun.
Require Import myMap.
Require Import config.
Require Import alloc.
Require Import make.
Require Import or.
Require Import op.
Require Import tauto.
Require Import gc.
Require Import univ.

Fixpoint ad_list_neq (l1 l2 : list ad) {struct l2} : bool :=
  match l1, l2 with
  | nil, _ => true
  | _, nil => true
  | a1 :: l1', a2 :: l2' => negb (Neqb a1 a2) && ad_list_neq l1' l2'
  end.

Definition bool_to_be (b : bool) :=
  match b with
  | true => One
  | false => Zero
  end.
Definition bool_to_bf (b : bool) :=
  match b with
  | true => bool_fun_one
  | false => bool_fun_zero
  end.

Definition bool_fun_subst (x : BDDvar) (bfx bf : bool_fun) : bool_fun :=
  fun ve : var_env => bf (augment ve x (bfx ve)).

Definition bool_fun_subst1 (x : BDDvar) (bfx bf : bool_fun) : bool_fun :=
  bool_fun_forall x (bool_fun_impl (bool_fun_iff (bool_fun_var x) bfx) bf).

Definition bool_fun_replace (x y : BDDvar) (bf : bool_fun) :=
  bool_fun_subst x (bool_fun_var y) bf.

Definition bool_fun_restrict1 (x : BDDvar) (b : bool) 
  (bf : bool_fun) := bool_fun_subst x (bool_to_bf b) bf.

Lemma bool_fun_restrict1_eq_restrict :
 forall (bf : bool_fun) (x : BDDvar) (b : bool),
 bool_fun_eq (bool_fun_restrict1 x b bf) (bool_fun_restrict bf x b).
Proof.
  unfold bool_fun_restrict1, bool_fun_restrict in |- *.  unfold bool_fun_subst in |- *.  intros.
  unfold bool_fun_eq in |- *.  intro.  unfold bool_to_bf in |- *.  elim b.  unfold bool_fun_one in |- *.
  reflexivity.  unfold bool_fun_zero in |- *.  reflexivity.  
Qed.

Lemma bool_fun_subst_preserves_eq :
 forall (bf bf' bfx bfx' : bool_fun) (x : BDDvar),
 bool_fun_eq bf bf' ->
 bool_fun_eq bfx bfx' ->
 bool_fun_eq (bool_fun_subst x bfx bf) (bool_fun_subst x bfx' bf').
Proof.
  unfold bool_fun_eq, bool_fun_subst in |- *.  intros.  rewrite (H0 vb).  apply H.  
Qed.

Lemma bool_fun_replace_preserves_eq :
 forall (bf1 bf2 : bool_fun) (x y : BDDvar),
 bool_fun_eq bf1 bf2 ->
 bool_fun_eq (bool_fun_replace x y bf1) (bool_fun_replace x y bf2).
Proof.
  unfold bool_fun_replace in |- *.  intros.  apply bool_fun_subst_preserves_eq.
  assumption.  apply bool_fun_eq_refl.  
Qed.

Fixpoint subst (x : BDDvar) (bex be : bool_expr) {struct be} : bool_expr :=
  match be with
  | Zero => Zero
  | One => One
  | Var y => if Neqb x y then bex else be
  | Neg be1 => Neg (subst x bex be1)
  | Or be1 be2 => Or (subst x bex be1) (subst x bex be2)
  | ANd be1 be2 => ANd (subst x bex be1) (subst x bex be2)
  | Impl be1 be2 => Impl (subst x bex be1) (subst x bex be2)
  | Iff be1 be2 => Iff (subst x bex be1) (subst x bex be2)
  end.

Lemma subst_ok :
 forall (be bex : bool_expr) (x : BDDvar),
 bool_fun_eq (bool_fun_of_bool_expr (subst x bex be))
   (bool_fun_subst x (bool_fun_of_bool_expr bex) (bool_fun_of_bool_expr be)).
Proof.
  simple induction be.  compute in |- *.  reflexivity.  compute in |- *.  reflexivity.  simpl in |- *.
  unfold bool_fun_subst in |- *.  unfold bool_fun_eq in |- *.  unfold augment in |- *.
  unfold bool_fun_var in |- *.  intros.  elim (Neqb x b).  reflexivity.  reflexivity.
  simpl in |- *.  intros.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_neg
                (bool_fun_subst x (bool_fun_of_bool_expr bex)
                   (bool_fun_of_bool_expr b))).
  apply bool_fun_neg_preserves_eq.  apply H.  unfold bool_fun_neg, bool_fun_eq in |- *.
  intro.  unfold bool_fun_subst in |- *.  reflexivity.  simpl in |- *.  intros.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_or
                (bool_fun_subst x (bool_fun_of_bool_expr bex)
                   (bool_fun_of_bool_expr b))
                (bool_fun_subst x (bool_fun_of_bool_expr bex)
                   (bool_fun_of_bool_expr b0))).
  apply bool_fun_or_preserves_eq.  apply H.  apply H0.
  unfold bool_fun_or, bool_fun_eq in |- *.  intro.  unfold bool_fun_subst in |- *.  reflexivity.
  simpl in |- *.  intros.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_and
                (bool_fun_subst x (bool_fun_of_bool_expr bex)
                   (bool_fun_of_bool_expr b))
                (bool_fun_subst x (bool_fun_of_bool_expr bex)
                   (bool_fun_of_bool_expr b0))).
  apply bool_fun_and_preserves_eq.  apply H.  apply H0.
  unfold bool_fun_and, bool_fun_eq in |- *.  intro.  unfold bool_fun_subst in |- *.  reflexivity.
  simpl in |- *.  intros.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_impl
                (bool_fun_subst x (bool_fun_of_bool_expr bex)
                   (bool_fun_of_bool_expr b))
                (bool_fun_subst x (bool_fun_of_bool_expr bex)
                   (bool_fun_of_bool_expr b0))).
  apply bool_fun_impl_preserves_eq.  apply H.  apply H0.
  unfold bool_fun_impl, bool_fun_eq in |- *.  intro.  unfold bool_fun_subst in |- *.
  reflexivity.  simpl in |- *.  intros.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_iff
                (bool_fun_subst x (bool_fun_of_bool_expr bex)
                   (bool_fun_of_bool_expr b))
                (bool_fun_subst x (bool_fun_of_bool_expr bex)
                   (bool_fun_of_bool_expr b0))).
  apply bool_fun_iff_preserves_eq.  apply H.  apply H0.
  unfold bool_fun_iff, bool_fun_eq in |- *.  intro.  unfold bool_fun_subst in |- *.  reflexivity.
Qed.

Fixpoint bool_fun_univl (bf : bool_fun) (la : list ad) {struct la} :
 bool_fun :=
  match la with
  | nil => bf
  | a :: la' => bool_fun_forall a (bool_fun_univl bf la')
  end.

Fixpoint bool_fun_exl (bf : bool_fun) (la : list ad) {struct la} :
 bool_fun :=
  match la with
  | nil => bf
  | a :: la' => bool_fun_ex a (bool_fun_exl bf la')
  end.

Lemma bool_fun_subst1_eq_subst :
 forall (x : BDDvar) bfx (bf : bool_fun),
 bool_fun_independent bfx x ->
 bool_fun_eq (bool_fun_subst1 x bfx bf) (bool_fun_subst x bfx bf).
Proof.
  unfold bool_fun_subst1, bool_fun_subst in |- *.  intros.  unfold bool_fun_eq in |- *.  intro.
  unfold bool_fun_iff in |- *.  unfold bool_fun_forall in |- *.  unfold bool_fun_restrict in |- *.
  unfold bool_fun_and, bool_fun_impl in |- *.  unfold bool_fun_var in |- *.  unfold augment at 1 4 in |- *.
  rewrite (Neqb_correct x).  simpl in |- *.  unfold bool_fun_independent in H.
  unfold bool_fun_restrict in H.  unfold bool_fun_eq in H.
  rewrite (H true vb).  rewrite (H false vb).
  elim (sumbool_of_bool (bfx vb)).  intro y.  rewrite y.  simpl in |- *.
  elim (bf (augment vb x true)); reflexivity.  intro y.  rewrite y.  simpl in |- *.
  reflexivity.
Qed.

Definition restrict (x : BDDvar) (b : bool) (be : bool_expr) :=
  subst x (bool_to_be b) be.

Lemma bool_fun_restrict_eq_subst :
 forall (x : BDDvar) (b : bool) (bf : bool_fun),
 bool_fun_eq (bool_fun_restrict bf x b) (bool_fun_subst x (bool_to_bf b) bf).
Proof.
  unfold bool_fun_restrict in |- *.  unfold bool_fun_subst in |- *.  intros.
  unfold bool_fun_eq in |- *.  intro.  elim b; reflexivity.
Qed.

Lemma bool_to_be_to_bf :
 forall b : bool, bool_fun_of_bool_expr (bool_to_be b) = bool_to_bf b.
Proof.
  intros.  elim b; reflexivity.  
Qed.

Lemma restrict_OK :
 forall (x : BDDvar) (b : bool) (be : bool_expr),
 bool_fun_eq (bool_fun_of_bool_expr (restrict x b be))
   (bool_fun_restrict (bool_fun_of_bool_expr be) x b).
Proof.
  unfold restrict in |- *.  intros.
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_subst x (bool_to_bf b) (bool_fun_of_bool_expr be)).
  rewrite <- (bool_to_be_to_bf b).  apply subst_ok.  apply bool_fun_eq_sym.
  apply bool_fun_restrict_eq_subst.
Qed.

Definition forall_ (x : BDDvar) (be : bool_expr) : bool_expr :=
  ANd (restrict x true be) (restrict x false be).

Definition be_ex (x : BDDvar) (be : bool_expr) : bool_expr :=
  Or (restrict x true be) (restrict x false be).

Lemma forall_OK :
 forall (x : BDDvar) (be : bool_expr),
 bool_fun_eq (bool_fun_of_bool_expr (forall_ x be))
   (bool_fun_forall x (bool_fun_of_bool_expr be)).
Proof.
  unfold forall_, bool_fun_forall in |- *.  intros.  simpl in |- *.
  apply bool_fun_and_preserves_eq.  apply restrict_OK.  apply restrict_OK.  
Qed.
 
Lemma ex_OK :
 forall (x : BDDvar) (be : bool_expr),
 bool_fun_eq (bool_fun_of_bool_expr (be_ex x be))
   (bool_fun_ex x (bool_fun_of_bool_expr be)).
Proof.
  unfold be_ex, bool_fun_ex in |- *.  intros.  simpl in |- *.
  apply bool_fun_or_preserves_eq.  apply restrict_OK.  apply restrict_OK.  
Qed.
 
Fixpoint univl (be : bool_expr) (la : list ad) {struct la} : bool_expr :=
  match la with
  | nil => be
  | a :: la' => forall_ a (univl be la')
  end.

Fixpoint exl (be : bool_expr) (la : list ad) {struct la} : bool_expr :=
  match la with
  | nil => be
  | a :: la' => be_ex a (exl be la')
  end.

Lemma univl_OK :
 forall (la : list ad) (be : bool_expr),
 bool_fun_eq (bool_fun_of_bool_expr (univl be la))
   (bool_fun_univl (bool_fun_of_bool_expr be) la).
Proof.
  simple induction la.  intro.  apply bool_fun_eq_refl.  intros.
  replace (univl be (a :: l)) with (forall_ a (univl be l)).
  unfold bool_fun_univl in |- *.  fold bool_fun_univl in |- *.
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_forall a (bool_fun_of_bool_expr (univl be l))).
  apply forall_OK.  apply bool_fun_forall_preserves_eq.  apply H.  reflexivity.
Qed.

Lemma exl_OK :
 forall (la : list ad) (be : bool_expr),
 bool_fun_eq (bool_fun_of_bool_expr (exl be la))
   (bool_fun_exl (bool_fun_of_bool_expr be) la).
Proof.
  simple induction la.  intro.  apply bool_fun_eq_refl.  intros.
  replace (exl be (a :: l)) with (be_ex a (exl be l)).
  unfold bool_fun_exl in |- *.  fold bool_fun_exl in |- *.
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_ex a (bool_fun_of_bool_expr (exl be l))).
  apply ex_OK.  apply bool_fun_ex_preserves_eq.  apply H.  reflexivity.
Qed.

Definition replace (x y : BDDvar) (be : bool_expr) := subst x (Var y) be.

Lemma replace_OK :
 forall (x y : BDDvar) (be : bool_expr),
 bool_fun_eq (bool_fun_of_bool_expr (replace x y be))
   (bool_fun_replace x y (bool_fun_of_bool_expr be)).
Proof.
  unfold replace, bool_fun_replace in |- *.  intros.  simpl in |- *.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_subst x (bool_fun_of_bool_expr (Var y))
                (bool_fun_of_bool_expr be)).
  apply subst_ok.  apply bool_fun_subst_preserves_eq.  apply bool_fun_eq_refl.  
  simpl in |- *.  apply bool_fun_eq_refl.  
Qed.

Fixpoint replacel (be : bool_expr) (lx ly : list ad) {struct ly} :
 bool_expr :=
  match lx, ly with
  | nil, _ => be
  | _ :: _, nil => (* error *)  be
  | x :: lx', y :: ly' => replace x y (replacel be lx' ly')
  end.

Fixpoint bool_fun_replacel (bf : bool_fun) (lx ly : list ad) {struct ly} :
 bool_fun :=
  match lx, ly with
  | nil, _ => bf
  | _ :: _, nil => (* error *)  bf
  | x :: lx', y :: ly' => bool_fun_replace x y (bool_fun_replacel bf lx' ly')
  end.

Lemma replacel_OK :
 forall (lx ly : list ad) (be : bool_expr),
 bool_fun_eq (bool_fun_of_bool_expr (replacel be lx ly))
   (bool_fun_replacel (bool_fun_of_bool_expr be) lx ly).
Proof.
  simple induction lx.  simpl in |- *.  intros.  elim ly; intros; apply bool_fun_eq_refl.  
  intros a l ly.  intros.  elim ly0.  apply bool_fun_eq_refl.  intros.  simpl in |- *.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_replace a a0
                (bool_fun_of_bool_expr (replacel be l l0))).
  apply replace_OK.  apply bool_fun_replace_preserves_eq.  apply ly.  
Qed.

Section BDDquant.

Variable gc : BDDconfig -> list ad -> BDDconfig.
Hypothesis gc_is_OK : gc_OK gc.

                          Section BDDuniv_results.


Variable cfg : BDDconfig.
Variable ul : list ad.
Variable y : BDDvar.
Variable node : ad.

Hypothesis cfg_OK : BDDconfig_OK cfg.
Hypothesis ul_OK : used_list_OK cfg ul.
Hypothesis used : used_node' cfg ul node.

Definition BDDuniv :=
  BDDuniv_1 gc cfg ul node y (S (nat_of_N (node_height cfg node))).

Let lt_1 :
  nat_of_N (node_height cfg node) < S (nat_of_N (node_height cfg node)).
Proof.
  unfold lt in |- *.  apply le_n.
Qed.

Lemma BDDuniv_config_OK : BDDconfig_OK (fst BDDuniv).
Proof.
exact
 (proj1
    (BDDuniv_1_lemma gc gc_is_OK (S (nat_of_N (node_height cfg node))) cfg
       ul y node lt_1 cfg_OK ul_OK used)).
Qed.

Lemma BDDuniv_node_OK : config_node_OK (fst BDDuniv) (snd BDDuniv).
Proof.
  exact
   (proj1
      (proj2
         (BDDuniv_1_lemma gc gc_is_OK (S (nat_of_N (node_height cfg node)))
            cfg ul y node lt_1 cfg_OK ul_OK used))).
Qed.

Lemma BDDuniv_used_nodes_preserved :
 used_nodes_preserved cfg (fst BDDuniv) ul.
Proof.
  exact
   (proj1
      (proj2
         (proj2
            (BDDuniv_1_lemma gc gc_is_OK
               (S (nat_of_N (node_height cfg node))) cfg ul y node lt_1
               cfg_OK ul_OK used)))).
Qed.

Lemma BDDuniv_is_univ :
 bool_fun_eq (bool_fun_of_BDD (fst BDDuniv) (snd BDDuniv))
   (bool_fun_forall y (bool_fun_of_BDD cfg node)).
Proof.
  exact
   (proj2
      (proj2
         (proj2
            (proj2
               (BDDuniv_1_lemma gc gc_is_OK
                  (S (nat_of_N (node_height cfg node))) cfg ul y node lt_1
                  cfg_OK ul_OK used))))).
Qed.

Lemma BDDuniv_list_OK : used_list_OK (fst BDDuniv) ul.
Proof.
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.
  exact BDDuniv_used_nodes_preserved.
Qed.

Lemma BDDuniv_list_OK_cons : used_list_OK (fst BDDuniv) (snd BDDuniv :: ul).
Proof.
  apply node_OK_list_OK.  exact BDDuniv_node_OK.  exact BDDuniv_list_OK.
Qed.

Lemma BDDuniv_var_le :
 Nleb (node_height (fst BDDuniv) (snd BDDuniv)) (node_height cfg node) =
 true.
Proof.
  exact
   (proj1
      (proj2
         (proj2
            (proj2
               (BDDuniv_1_lemma gc gc_is_OK
                  (S (nat_of_N (node_height cfg node))) cfg ul y node lt_1
                  cfg_OK ul_OK used))))).
Qed.


                          End BDDuniv_results.

                         Section BDDex_results.

Variable cfg : BDDconfig.
Variable ul : list ad.
Variable y : BDDvar.
Variable node : ad.
 
Hypothesis cfg_OK : BDDconfig_OK cfg.
Hypothesis ul_OK : used_list_OK cfg ul.
Hypothesis used : used_node' cfg ul node.

Definition BDDex :=
  match BDDneg gc cfg ul node with
  | (cfg1, node1) =>
      match BDDuniv cfg1 (node1 :: ul) y node1 with
      | (cfg2, node2) => BDDneg gc cfg2 (node2 :: ul) node2
      end
  end.

Lemma BDDex_config_OK : BDDconfig_OK (fst BDDex).
Proof.
  unfold BDDex in |- *.  elim (prod_sum _ _ (BDDneg gc cfg ul node)).  intros cfg1 H.
  elim H.  clear H.  intros node1 H.  rewrite H.
  elim (prod_sum _ _ (BDDuniv cfg1 (node1 :: ul) y node1)).  intros cfg2 H0.
  elim H0.  clear H0.  intros node2 H0.  rewrite H0.  cut (BDDconfig_OK cfg1).
  intro.  cut (used_nodes_preserved cfg cfg1 ul).  intro.
  cut (used_list_OK cfg1 (node1 :: ul)).  intro.  apply BDDneg_config_OK.
  assumption.  replace cfg2 with (fst (BDDuniv cfg1 (node1 :: ul) y node1)).
  apply BDDuniv_config_OK.  assumption.  assumption.  
  apply used_node'_cons_node_ul.  rewrite H0.  reflexivity.
  apply node_OK_list_OK.
  replace cfg2 with (fst (BDDuniv cfg1 (node1 :: ul) y node1)).
  replace node2 with (snd (BDDuniv cfg1 (node1 :: ul) y node1)).
  apply BDDuniv_node_OK.  assumption.  assumption.
  apply used_node'_cons_node_ul.  rewrite H0.  reflexivity.  rewrite H0.
  reflexivity.  replace cfg2 with (fst (BDDuniv cfg1 (node1 :: ul) y node1)).
  apply cons_OK_list_OK with (node := node1).  apply BDDuniv_list_OK.  assumption.
  assumption.  apply used_node'_cons_node_ul.  rewrite H0.  reflexivity.  
  apply used_node'_cons_node_ul.
  replace cfg1 with (fst (BDDneg gc cfg ul node)).
  replace node1 with (snd (BDDneg gc cfg ul node)).  apply BDDneg_list_OK_cons.
  assumption.  assumption.  assumption.  assumption.  rewrite H.  reflexivity.  
  rewrite H.  reflexivity.  replace cfg1 with (fst (BDDneg gc cfg ul node)).
  apply BDDneg_used_nodes_preserved.  assumption.  assumption.  assumption.  
  assumption.  rewrite H.  reflexivity.
  replace cfg1 with (fst (BDDneg gc cfg ul node)).  apply BDDneg_config_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H.  reflexivity.
Qed.

Lemma BDDex_node_OK : config_node_OK (fst BDDex) (snd BDDex).
Proof.
  unfold BDDex in |- *.  elim (prod_sum _ _ (BDDneg gc cfg ul node)).  intros cfg1 H.
  elim H.  clear H.  intros node1 H.  rewrite H.
  elim (prod_sum _ _ (BDDuniv cfg1 (node1 :: ul) y node1)).  intros cfg2 H0.
  elim H0.  clear H0.  intros node2 H0.  rewrite H0.  cut (BDDconfig_OK cfg1).
  intro.  cut (used_nodes_preserved cfg cfg1 ul).  intro.
  cut (used_list_OK cfg1 (node1 :: ul)).  intro.  apply BDDneg_node_OK.
  assumption.  replace cfg2 with (fst (BDDuniv cfg1 (node1 :: ul) y node1)).
  apply BDDuniv_config_OK.  assumption.  assumption.  
  apply used_node'_cons_node_ul.  rewrite H0.  reflexivity.
  apply node_OK_list_OK.
  replace cfg2 with (fst (BDDuniv cfg1 (node1 :: ul) y node1)).
  replace node2 with (snd (BDDuniv cfg1 (node1 :: ul) y node1)).
  apply BDDuniv_node_OK.  assumption.  assumption.
  apply used_node'_cons_node_ul.  rewrite H0.  reflexivity.  rewrite H0.
  reflexivity.  replace cfg2 with (fst (BDDuniv cfg1 (node1 :: ul) y node1)).
  apply cons_OK_list_OK with (node := node1).  apply BDDuniv_list_OK.  assumption.
  assumption.  apply used_node'_cons_node_ul.  rewrite H0.  reflexivity.  
  apply used_node'_cons_node_ul.
  replace cfg1 with (fst (BDDneg gc cfg ul node)).
  replace node1 with (snd (BDDneg gc cfg ul node)).  apply BDDneg_list_OK_cons.
  assumption.  assumption.  assumption.  assumption.  rewrite H.  reflexivity.  
  rewrite H.  reflexivity.  replace cfg1 with (fst (BDDneg gc cfg ul node)).
  apply BDDneg_used_nodes_preserved.  assumption.  assumption.  assumption.  
  assumption.  rewrite H.  reflexivity.
  replace cfg1 with (fst (BDDneg gc cfg ul node)).  apply BDDneg_config_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H.  reflexivity.
Qed.

Lemma BDDex_used_nodes_preserved : used_nodes_preserved cfg (fst BDDex) ul.
Proof.
  unfold BDDex in |- *.  elim (prod_sum _ _ (BDDneg gc cfg ul node)).  intros cfg1 H.
  elim H.  clear H.  intros node1 H.  rewrite H.
  elim (prod_sum _ _ (BDDuniv cfg1 (node1 :: ul) y node1)).  intros cfg2 H0.
  elim H0.  clear H0.  intros node2 H0.  rewrite H0.  cut (BDDconfig_OK cfg1).
  intro.  cut (used_nodes_preserved cfg cfg1 ul).  intro.
  cut (used_list_OK cfg1 (node1 :: ul)).  intro.
  apply used_nodes_preserved_trans with (cfg2 := cfg1).  assumption.  assumption.  
  apply used_nodes_preserved_trans with (cfg2 := cfg2).  assumption.  
  replace cfg2 with (fst (BDDuniv cfg1 (node1 :: ul) y node1)).
  apply used_nodes_preserved_cons with (node := node1).
  apply BDDuniv_used_nodes_preserved.  assumption.  assumption.  
  apply used_node'_cons_node_ul.  rewrite H0.  reflexivity.
  apply used_nodes_preserved_cons with (node := node2).
  apply BDDneg_used_nodes_preserved.
  assumption.  replace cfg2 with (fst (BDDuniv cfg1 (node1 :: ul) y node1)).
  apply BDDuniv_config_OK.  assumption.  assumption.
  apply used_node'_cons_node_ul.  rewrite H0.  reflexivity.
  apply node_OK_list_OK.
  replace cfg2 with (fst (BDDuniv cfg1 (node1 :: ul) y node1)).
  replace node2 with (snd (BDDuniv cfg1 (node1 :: ul) y node1)).
  apply BDDuniv_node_OK.  assumption.  assumption.
  apply used_node'_cons_node_ul.  rewrite H0.  reflexivity.  rewrite H0.
  reflexivity.  replace cfg2 with (fst (BDDuniv cfg1 (node1 :: ul) y node1)).
  apply cons_OK_list_OK with (node := node1).  apply BDDuniv_list_OK.  assumption.
  assumption.  apply used_node'_cons_node_ul.  rewrite H0.  reflexivity.
  apply used_node'_cons_node_ul.
  replace cfg1 with (fst (BDDneg gc cfg ul node)).
  replace node1 with (snd (BDDneg gc cfg ul node)).  apply BDDneg_list_OK_cons.
  assumption.  assumption.  assumption.  assumption.  rewrite H.  reflexivity.
  rewrite H.  reflexivity.  replace cfg1 with (fst (BDDneg gc cfg ul node)).
  apply BDDneg_used_nodes_preserved.  assumption.  assumption.  assumption.
  assumption.  rewrite H.  reflexivity.
  replace cfg1 with (fst (BDDneg gc cfg ul node)).  apply BDDneg_config_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H.  reflexivity.
Qed.

Lemma BDDex_is_ex :
 bool_fun_eq (bool_fun_of_BDD (fst BDDex) (snd BDDex))
   (bool_fun_ex y (bool_fun_of_BDD cfg node)).
Proof.
  unfold BDDex in |- *.  elim (prod_sum _ _ (BDDneg gc cfg ul node)).  intros cfg1 H.
  elim H.  clear H.  intros node1 H.  rewrite H.
  elim (prod_sum _ _ (BDDuniv cfg1 (node1 :: ul) y node1)).  intros cfg2 H0.
  elim H0.  clear H0.  intros node2 H0.  rewrite H0.  cut (BDDconfig_OK cfg1).
  intro.  cut (used_nodes_preserved cfg cfg1 ul).  intro.
  cut (used_list_OK cfg1 (node1 :: ul)).  intro.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_neg
                (bool_fun_forall y (bool_fun_neg (bool_fun_of_BDD cfg node)))).
  apply
   bool_fun_eq_trans with (bf2 := bool_fun_neg (bool_fun_of_BDD cfg2 node2)).
  apply BDDneg_is_neg.  assumption.  
  replace cfg2 with (fst (BDDuniv cfg1 (node1 :: ul) y node1)).
  apply BDDuniv_config_OK.  assumption.  assumption.  
  apply used_node'_cons_node_ul.  rewrite H0.  reflexivity.
  apply node_OK_list_OK.
  replace cfg2 with (fst (BDDuniv cfg1 (node1 :: ul) y node1)).
  replace node2 with (snd (BDDuniv cfg1 (node1 :: ul) y node1)).
  apply BDDuniv_node_OK.  assumption.  assumption.
  apply used_node'_cons_node_ul.  rewrite H0.  reflexivity.  rewrite H0.
  reflexivity.  replace cfg2 with (fst (BDDuniv cfg1 (node1 :: ul) y node1)).
  apply cons_OK_list_OK with (node := node1).  apply BDDuniv_list_OK.  assumption.  
  assumption.  apply used_node'_cons_node_ul.  rewrite H0.  reflexivity.  
  apply used_node'_cons_node_ul.  apply bool_fun_neg_preserves_eq.
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_forall y (bool_fun_of_BDD cfg1 node1)).
  replace cfg2 with (fst (BDDuniv cfg1 (node1 :: ul) y node1)).
  replace node2 with (snd (BDDuniv cfg1 (node1 :: ul) y node1)).
  apply BDDuniv_is_univ.  assumption.  assumption.  
  apply used_node'_cons_node_ul.  rewrite H0.  reflexivity.  rewrite H0.
  reflexivity.  apply bool_fun_forall_preserves_eq.
  replace cfg1 with (fst (BDDneg gc cfg ul node)).
  replace node1 with (snd (BDDneg gc cfg ul node)).  apply BDDneg_is_neg.
  assumption.  assumption.  assumption.  assumption.  rewrite H.  reflexivity.  
  rewrite H.  reflexivity.  apply bool_fun_eq_sym.  apply bool_fun_ex_lemma.
  replace cfg1 with (fst (BDDneg gc cfg ul node)).
  replace node1 with (snd (BDDneg gc cfg ul node)).  apply BDDneg_list_OK_cons.
  assumption.  assumption.  assumption.  assumption.  rewrite H.  reflexivity.  
  rewrite H.  reflexivity.  replace cfg1 with (fst (BDDneg gc cfg ul node)).
  apply BDDneg_used_nodes_preserved.  assumption.  assumption.  assumption.  
  assumption.  rewrite H.  reflexivity.  
  replace cfg1 with (fst (BDDneg gc cfg ul node)).  apply BDDneg_config_OK.
  assumption.  assumption.  assumption.  assumption.  rewrite H.  reflexivity.
Qed.

Lemma BDDex_list_OK : used_list_OK (fst BDDex) ul.
Proof.
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.
  exact BDDex_used_nodes_preserved.
Qed.
 
Lemma BDDex_list_OK_cons : used_list_OK (fst BDDex) (snd BDDex :: ul).
Proof.
  apply node_OK_list_OK.  apply BDDex_node_OK.  exact BDDex_list_OK.
Qed.

(*
Lemma BDDex_var_le : (Nleb (node_height (Fst BDDex) (Snd BDDex)) (node_height cfg node))=true.
Proof.

Qed.
*)

                           End BDDex_results.
                          


Fixpoint BDDunivl (cfg : BDDconfig) (ul : list ad) 
 (node : ad) (ly : list BDDvar) {struct ly} : BDDconfig * ad :=
  match ly with
  | nil => (cfg, node)
  | y :: ly' =>
      match BDDunivl cfg ul node ly' with
      | (cfg1, node1) => BDDuniv cfg1 (node1 :: ul) y node1
      end
  end.

Lemma BDDunivl_lemma :
 forall (ly : list BDDvar) (cfg : BDDconfig) (ul : list ad) (node : ad),
 BDDconfig_OK cfg ->
 used_list_OK cfg ul ->
 used_node' cfg ul node ->
 BDDconfig_OK (fst (BDDunivl cfg ul node ly)) /\
 config_node_OK (fst (BDDunivl cfg ul node ly))
   (snd (BDDunivl cfg ul node ly)) /\
 used_nodes_preserved cfg (fst (BDDunivl cfg ul node ly)) ul /\
 bool_fun_eq
   (bool_fun_of_BDD (fst (BDDunivl cfg ul node ly))
      (snd (BDDunivl cfg ul node ly)))
   (bool_fun_univl (bool_fun_of_BDD cfg node) ly).
Proof.
  simple induction ly.  simpl in |- *.  intros.  split.  assumption.  split.
  apply used_node'_OK with (ul := ul).  assumption.  assumption.  assumption.
  split.  apply used_nodes_preserved_refl.  apply bool_fun_eq_refl.  intros.
  simpl in |- *.
  elim (prod_sum _ _ (BDDunivl cfg ul node l)).  intros cfg1 H3.
  elim H3; clear H3.  intros node1 H3.  rewrite H3.
  elim (H cfg ul node H0 H1 H2).  intros.  elim H5.  intros.
  rewrite H3 in H4.  rewrite H3 in H6.  rewrite H3 in H7.  elim H7.  intros.
  split.  apply BDDuniv_config_OK.
  assumption.  apply node_OK_list_OK.  assumption.  
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.  assumption.
  apply used_node'_cons_node_ul.  split.  apply BDDuniv_node_OK.  assumption.
  apply node_OK_list_OK.  assumption.  
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.  assumption.
  apply used_node'_cons_node_ul.  split.
  apply used_nodes_preserved_trans with (cfg2 := cfg1).  assumption.  assumption.
  apply used_nodes_preserved_cons with (node := node1).
  apply BDDuniv_used_nodes_preserved.  assumption.  apply node_OK_list_OK.
  assumption.  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.
  assumption.  apply used_node'_cons_node_ul.
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_forall a (bool_fun_of_BDD cfg1 node1)).
  apply BDDuniv_is_univ.  assumption.  apply node_OK_list_OK.  assumption.  
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.  assumption.  
  apply used_node'_cons_node_ul.  apply bool_fun_forall_preserves_eq.
  assumption.
Qed.

                          Section BDDunivl_results.


Variable cfg : BDDconfig.
Variable ul : list ad.
Variable node : ad.
Variable ly : list BDDvar.

Hypothesis cfg_OK : BDDconfig_OK cfg.
Hypothesis ul_OK : used_list_OK cfg ul.
Hypothesis used : used_node' cfg ul node.

Lemma BDDunivl_config_OK : BDDconfig_OK (fst (BDDunivl cfg ul node ly)).
Proof.
  exact (proj1 (BDDunivl_lemma ly cfg ul node cfg_OK ul_OK used)).
Qed.

Lemma BDDunivl_node_OK :
 config_node_OK (fst (BDDunivl cfg ul node ly))
   (snd (BDDunivl cfg ul node ly)).
Proof.
  exact (proj1 (proj2 (BDDunivl_lemma ly cfg ul node cfg_OK ul_OK used))).
Qed.

Lemma BDDunivl_used_nodes_preserved :
 used_nodes_preserved cfg (fst (BDDunivl cfg ul node ly)) ul.
Proof.
  exact
   (proj1 (proj2 (proj2 (BDDunivl_lemma ly cfg ul node cfg_OK ul_OK used)))).
Qed.

Lemma BDDunivl_list_OK : used_list_OK (fst (BDDunivl cfg ul node ly)) ul.
Proof.
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.
  exact BDDunivl_used_nodes_preserved.
Qed.

Lemma BDDunivl_list_OK_cons :
 used_list_OK (fst (BDDunivl cfg ul node ly))
   (snd (BDDunivl cfg ul node ly) :: ul).
Proof.
  apply node_OK_list_OK.  exact BDDunivl_node_OK.  exact BDDunivl_list_OK.
Qed.

Lemma BDDunivl_is_univl :
 bool_fun_eq
   (bool_fun_of_BDD (fst (BDDunivl cfg ul node ly))
      (snd (BDDunivl cfg ul node ly)))
   (bool_fun_univl (bool_fun_of_BDD cfg node) ly).
Proof.
  exact
   (proj2 (proj2 (proj2 (BDDunivl_lemma ly cfg ul node cfg_OK ul_OK used)))).
Qed.

                          End BDDunivl_results.

Fixpoint BDDexl (cfg : BDDconfig) (ul : list ad) (node : ad)
 (ly : list BDDvar) {struct ly} : BDDconfig * ad :=
  match ly with
  | nil => (cfg, node)
  | y :: ly' =>
      match BDDexl cfg ul node ly' with
      | (cfg1, node1) => BDDex cfg1 (node1 :: ul) y node1
      end
  end.

Lemma BDDexl_lemma :
 forall (ly : list BDDvar) (cfg : BDDconfig) (ul : list ad) (node : ad),
 BDDconfig_OK cfg ->
 used_list_OK cfg ul ->
 used_node' cfg ul node ->
 BDDconfig_OK (fst (BDDexl cfg ul node ly)) /\
 config_node_OK (fst (BDDexl cfg ul node ly)) (snd (BDDexl cfg ul node ly)) /\
 used_nodes_preserved cfg (fst (BDDexl cfg ul node ly)) ul /\
 bool_fun_eq
   (bool_fun_of_BDD (fst (BDDexl cfg ul node ly))
      (snd (BDDexl cfg ul node ly)))
   (bool_fun_exl (bool_fun_of_BDD cfg node) ly).
Proof.
  simple induction ly.  simpl in |- *.  intros.  split.  assumption.  split.
  apply used_node'_OK with (ul := ul).  assumption.  assumption.  assumption.
  split.  apply used_nodes_preserved_refl.  apply bool_fun_eq_refl.  intros.
  simpl in |- *.
  elim (prod_sum _ _ (BDDexl cfg ul node l)).  intros cfg1 H3.
  elim H3; clear H3.  intros node1 H3.  rewrite H3.
  elim (H cfg ul node H0 H1 H2).  intros.  elim H5.  intros.
  rewrite H3 in H4.  rewrite H3 in H6.  rewrite H3 in H7.  elim H7.  intros.
  split.  apply BDDex_config_OK.
  assumption.  apply node_OK_list_OK.  assumption.  
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.  assumption.
  apply used_node'_cons_node_ul.  split.  apply BDDex_node_OK.  assumption.
  apply node_OK_list_OK.  assumption.  
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.  assumption.
  apply used_node'_cons_node_ul.  split.
  apply used_nodes_preserved_trans with (cfg2 := cfg1).  assumption.  assumption.
  apply used_nodes_preserved_cons with (node := node1).
  apply BDDex_used_nodes_preserved.  assumption.  apply node_OK_list_OK.
  assumption.  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.
  assumption.  apply used_node'_cons_node_ul.
  apply
   bool_fun_eq_trans with (bf2 := bool_fun_ex a (bool_fun_of_BDD cfg1 node1)).
  apply BDDex_is_ex.  assumption.  apply node_OK_list_OK.  assumption.  
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.  assumption.  
  apply used_node'_cons_node_ul.  apply bool_fun_ex_preserves_eq.
  assumption.
Qed.

                          Section BDDexl_results.


Variable cfg : BDDconfig.
Variable ul : list ad.
Variable node : ad.
Variable ly : list BDDvar.

Hypothesis cfg_OK : BDDconfig_OK cfg.
Hypothesis ul_OK : used_list_OK cfg ul.
Hypothesis used : used_node' cfg ul node.

Lemma BDDexl_config_OK : BDDconfig_OK (fst (BDDexl cfg ul node ly)).
Proof.
  exact (proj1 (BDDexl_lemma ly cfg ul node cfg_OK ul_OK used)).
Qed.

Lemma BDDexl_node_OK :
 config_node_OK (fst (BDDexl cfg ul node ly)) (snd (BDDexl cfg ul node ly)).
Proof.
  exact (proj1 (proj2 (BDDexl_lemma ly cfg ul node cfg_OK ul_OK used))).
Qed.

Lemma BDDexl_used_nodes_preserved :
 used_nodes_preserved cfg (fst (BDDexl cfg ul node ly)) ul.
Proof.
  exact
   (proj1 (proj2 (proj2 (BDDexl_lemma ly cfg ul node cfg_OK ul_OK used)))).
Qed.

Lemma BDDexl_list_OK : used_list_OK (fst (BDDexl cfg ul node ly)) ul.
Proof.
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.
  exact BDDexl_used_nodes_preserved.
Qed.

Lemma BDDexl_list_OK_cons :
 used_list_OK (fst (BDDexl cfg ul node ly))
   (snd (BDDexl cfg ul node ly) :: ul).
Proof.
  apply node_OK_list_OK.  exact BDDexl_node_OK.  exact BDDexl_list_OK.
Qed.

Lemma BDDexl_is_exl :
 bool_fun_eq
   (bool_fun_of_BDD (fst (BDDexl cfg ul node ly))
      (snd (BDDexl cfg ul node ly)))
   (bool_fun_exl (bool_fun_of_BDD cfg node) ly).
Proof.
  exact
   (proj2 (proj2 (proj2 (BDDexl_lemma ly cfg ul node cfg_OK ul_OK used)))).
Qed.

                          End BDDexl_results.

Definition BDDsubst (cfg : BDDconfig) (ul : list ad) 
  (node1 : ad) (x : BDDvar) (node2 : ad) :=
  match BDDvar_make gc cfg ul x with
  | (cfg1, nodex) =>
      match BDDiff gc cfg1 (nodex :: ul) nodex node2 with
      | (cfg2, node3) =>
          match BDDimpl gc cfg2 (node3 :: ul) node3 node1 with
          | (cfg3, node4) => BDDuniv cfg3 (node4 :: ul) x node4
          end
      end
  end.

Lemma BDDsubst_lemma :
 forall (cfg : BDDconfig) (ul : list ad) (node1 : ad) 
   (x : BDDvar) (node2 : ad),
 BDDconfig_OK cfg ->
 used_list_OK cfg ul ->
 used_node' cfg ul node1 ->
 used_node' cfg ul node2 ->
 BDDconfig_OK (fst (BDDsubst cfg ul node1 x node2)) /\
 config_node_OK (fst (BDDsubst cfg ul node1 x node2))
   (snd (BDDsubst cfg ul node1 x node2)) /\
 used_nodes_preserved cfg (fst (BDDsubst cfg ul node1 x node2)) ul /\
 bool_fun_eq
   (bool_fun_of_BDD (fst (BDDsubst cfg ul node1 x node2))
      (snd (BDDsubst cfg ul node1 x node2)))
   (bool_fun_subst1 x (bool_fun_of_BDD cfg node2) (bool_fun_of_BDD cfg node1)).
Proof.
  intros.  unfold BDDsubst in |- *.  elim (prod_sum _ _ (BDDvar_make gc cfg ul x)).
  intros cfg1 H3.  elim H3; clear H3.  intros nodex H3.  rewrite H3.
  elim (prod_sum _ _ (BDDiff gc cfg1 (nodex :: ul) nodex node2)).
  intros cfg2 H4.  elim H4; clear H4; intros node3 H4.  rewrite H4.
  elim (prod_sum _ _ (BDDimpl gc cfg2 (node3 :: ul) node3 node1)).
  intros cfg3 H5.  elim H5; clear H5; intros node4 H5.  rewrite H5.
  cut (BDDconfig_OK cfg1).  cut (used_nodes_preserved cfg cfg1 ul).
  cut (config_node_OK cfg1 nodex).
  cut (bool_fun_eq (bool_fun_of_BDD cfg1 nodex) (bool_fun_var x)).  intros.
  cut (used_list_OK cfg1 (nodex :: ul)).
  cut (used_node' cfg1 (nodex :: ul) nodex).
  cut (used_node' cfg1 (nodex :: ul) node2).  intros.
  cut (BDDconfig_OK cfg2).
  cut (used_nodes_preserved cfg1 cfg2 (nodex :: ul)).
  cut (config_node_OK cfg2 node3).
  cut
   (bool_fun_eq (bool_fun_of_BDD cfg2 node3)
      (bool_fun_iff (bool_fun_of_BDD cfg1 nodex) (bool_fun_of_BDD cfg1 node2))).
  intros.  cut (used_list_OK cfg2 (node3 :: ul)).  intro.
  cut (used_node' cfg2 (node3 :: ul) node1).
  cut (used_node' cfg2 (node3 :: ul) node3).  intros.
  cut (BDDconfig_OK cfg3).
  cut (used_nodes_preserved cfg2 cfg3 (node3 :: ul)).
  cut (config_node_OK cfg3 node4).
  cut
   (bool_fun_eq (bool_fun_of_BDD cfg3 node4)
      (bool_fun_impl (bool_fun_of_BDD cfg2 node3)
         (bool_fun_of_BDD cfg2 node1))).
  intros.  cut (used_list_OK cfg3 (node4 :: ul)).  intro.
  cut (used_node' cfg3 (node4 :: ul) node4).  intro.  split.
  apply BDDuniv_config_OK.  assumption.  assumption.  assumption.  split.
  apply BDDuniv_node_OK.  assumption.  assumption.  assumption.  split.
  apply used_nodes_preserved_trans with (cfg2 := cfg1).  assumption.  assumption.  
  apply used_nodes_preserved_trans with (cfg2 := cfg2).  assumption.  
  apply used_nodes_preserved_cons with (node := nodex).  assumption.  
  apply used_nodes_preserved_trans with (cfg2 := cfg3).  assumption.  
  apply used_nodes_preserved_cons with (node := node3).  assumption.  
  apply used_nodes_preserved_cons with (node := node4).
  apply BDDuniv_used_nodes_preserved.  assumption.  assumption.  assumption.  
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_forall x (bool_fun_of_BDD cfg3 node4)).
  apply BDDuniv_is_univ.  assumption.  assumption.  assumption.  
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_forall x
                (bool_fun_impl (bool_fun_of_BDD cfg2 node3)
                   (bool_fun_of_BDD cfg2 node1))).
  apply bool_fun_forall_preserves_eq.  assumption.  unfold bool_fun_subst1 in |- *.
  apply bool_fun_forall_preserves_eq.  apply bool_fun_impl_preserves_eq.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_iff (bool_fun_of_BDD cfg1 nodex)
                (bool_fun_of_BDD cfg1 node2)).
  assumption.  apply bool_fun_iff_preserves_eq.  assumption.  
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  assumption.
  assumption.  assumption.  assumption.
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  assumption.  
  apply used_nodes_preserved_trans with (cfg2 := cfg1).  assumption.  assumption.  
  apply used_nodes_preserved_cons with (node := nodex).  assumption.  assumption.
  assumption.  apply used_node'_cons_node_ul.  apply node_OK_list_OK.
  assumption.  apply used_nodes_preserved_list_OK with (cfg := cfg2).
  apply cons_OK_list_OK with (node := node3).  assumption.  
  apply used_nodes_preserved_cons with (node := node3).  assumption.
  replace cfg3 with (fst (BDDimpl gc cfg2 (node3 :: ul) node3 node1)).
  replace node4 with (snd (BDDimpl gc cfg2 (node3 :: ul) node3 node1)).
  apply BDDimpl_is_impl.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H5.  reflexivity.  rewrite H5.  reflexivity.  
  replace cfg3 with (fst (BDDimpl gc cfg2 (node3 :: ul) node3 node1)).
  replace node4 with (snd (BDDimpl gc cfg2 (node3 :: ul) node3 node1)).
  apply BDDimpl_node_OK.  assumption.  assumption.  assumption.  assumption.  
  assumption.  rewrite H5.  reflexivity.  rewrite H5.  reflexivity.  
  replace cfg3 with (fst (BDDimpl gc cfg2 (node3 :: ul) node3 node1)).
  apply BDDimpl_used_nodes_preserved.  assumption.  assumption.  assumption.
  assumption.  assumption.  rewrite H5.  reflexivity.  
  replace cfg3 with (fst (BDDimpl gc cfg2 (node3 :: ul) node3 node1)).
  apply BDDimpl_config_OK.  assumption.  assumption.  assumption.  assumption.  
  assumption.  rewrite H5.  reflexivity.  apply used_node'_cons_node_ul.  
  apply used_node'_cons_node'_ul.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.
  apply used_nodes_preserved_trans with (cfg2 := cfg1).  assumption.  assumption.  
  apply used_nodes_preserved_cons with (node := nodex).  assumption.  assumption.  
  apply node_OK_list_OK.  assumption.  
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.  
  apply used_nodes_preserved_trans with (cfg2 := cfg1).  assumption.  assumption.  
  apply used_nodes_preserved_cons with (node := nodex).  assumption.  
  replace cfg2 with (fst (BDDiff gc cfg1 (nodex :: ul) nodex node2)).
  replace node3 with (snd (BDDiff gc cfg1 (nodex :: ul) nodex node2)).
  apply BDDiff_is_iff.  assumption.  assumption.  assumption.  assumption.  
  assumption.  rewrite H4; reflexivity.  rewrite H4; reflexivity.  
  replace cfg2 with (fst (BDDiff gc cfg1 (nodex :: ul) nodex node2)).
  replace node3 with (snd (BDDiff gc cfg1 (nodex :: ul) nodex node2)).
  apply BDDiff_node_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  rewrite H4; reflexivity.  rewrite H4; reflexivity.  
  replace cfg2 with (fst (BDDiff gc cfg1 (nodex :: ul) nodex node2)).
  apply BDDiff_used_nodes_preserved.  assumption.  assumption.  assumption.  
  assumption.  assumption.  rewrite H4; reflexivity.  
  replace cfg2 with (fst (BDDiff gc cfg1 (nodex :: ul) nodex node2)).
  apply BDDiff_config_OK.  assumption.  assumption.  assumption.  assumption.  
  assumption.  rewrite H4; reflexivity.  apply used_node'_cons_node'_ul.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.  assumption.
  assumption.  apply used_node'_cons_node_ul.  apply node_OK_list_OK.
  assumption.  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.  
  assumption.  replace cfg1 with (fst (BDDvar_make gc cfg ul x)).
  replace nodex with (snd (BDDvar_make gc cfg ul x)).  apply BDDvar_make_is_var.
  assumption.  assumption.  assumption.  rewrite H3; reflexivity.
  rewrite H3; reflexivity.  replace cfg1 with (fst (BDDvar_make gc cfg ul x)).
  replace nodex with (snd (BDDvar_make gc cfg ul x)).
  apply BDDvar_make_node_OK.  assumption.  assumption.  assumption.  
  rewrite H3; reflexivity.  rewrite H3; reflexivity.  
  replace cfg1 with (fst (BDDvar_make gc cfg ul x)).
  apply BDDvar_make_used_nodes_preserved.  assumption.  assumption.  assumption.
  rewrite H3; reflexivity.  replace cfg1 with (fst (BDDvar_make gc cfg ul x)).
  apply BDDvar_make_config_OK.  assumption.  assumption.  assumption.  
  rewrite H3; reflexivity.
Qed.

Section BDDsubst_results.

Variable cfg : BDDconfig.
Variable ul : list ad.
Variable node1 node2 : ad.
Variable x : ad.

Hypothesis cfg_OK : BDDconfig_OK cfg.
Hypothesis ul_OK : used_list_OK cfg ul.
Hypothesis used1 : used_node' cfg ul node1.
Hypothesis used2 : used_node' cfg ul node2.

Hypothesis node2_ind : bool_fun_independent (bool_fun_of_BDD cfg node2) x.

Lemma BDDsubst_config_OK : BDDconfig_OK (fst (BDDsubst cfg ul node1 x node2)).
Proof.
  exact
   (proj1 (BDDsubst_lemma cfg ul node1 x node2 cfg_OK ul_OK used1 used2)).
Qed.

Lemma BDDsubst_node_OK :
 config_node_OK (fst (BDDsubst cfg ul node1 x node2))
   (snd (BDDsubst cfg ul node1 x node2)).
Proof.
  exact
   (proj1
      (proj2 (BDDsubst_lemma cfg ul node1 x node2 cfg_OK ul_OK used1 used2))).
Qed.

Lemma BDDsubst_used_nodes_preserved :
 used_nodes_preserved cfg (fst (BDDsubst cfg ul node1 x node2)) ul.
Proof.
  exact
   (proj1
      (proj2
         (proj2
            (BDDsubst_lemma cfg ul node1 x node2 cfg_OK ul_OK used1 used2)))).
Qed.

Lemma BDDsubst_list_OK :
 used_list_OK (fst (BDDsubst cfg ul node1 x node2)) ul.
Proof.
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.  
  exact BDDsubst_used_nodes_preserved.
Qed.

Lemma BDDsubst_list_OK_cons :
 used_list_OK (fst (BDDsubst cfg ul node1 x node2))
   (snd (BDDsubst cfg ul node1 x node2) :: ul).
Proof.
  apply node_OK_list_OK.  exact BDDsubst_node_OK.  exact BDDsubst_list_OK.
Qed.

Lemma BDDsubst_is_subst1 :
 bool_fun_eq
   (bool_fun_of_BDD (fst (BDDsubst cfg ul node1 x node2))
      (snd (BDDsubst cfg ul node1 x node2)))
   (bool_fun_subst1 x (bool_fun_of_BDD cfg node2) (bool_fun_of_BDD cfg node1)).
Proof.
  exact
   (proj2
      (proj2
         (proj2
            (BDDsubst_lemma cfg ul node1 x node2 cfg_OK ul_OK used1 used2)))).
Qed.

Lemma BDDsubst_is_subst :
 bool_fun_eq
   (bool_fun_of_BDD (fst (BDDsubst cfg ul node1 x node2))
      (snd (BDDsubst cfg ul node1 x node2)))
   (bool_fun_subst x (bool_fun_of_BDD cfg node2) (bool_fun_of_BDD cfg node1)).
Proof.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_subst1 x (bool_fun_of_BDD cfg node2)
                (bool_fun_of_BDD cfg node1)).
  exact BDDsubst_is_subst1.  apply bool_fun_subst1_eq_subst.  assumption.  
Qed.

End BDDsubst_results.

Section BDDreplace_results.

Variable cfg : BDDconfig.
Variable ul : list ad.
Variable node : ad.
Variable x y : ad.

Hypothesis cfg_OK : BDDconfig_OK cfg.
Hypothesis ul_OK : used_list_OK cfg ul.
Hypothesis used : used_node' cfg ul node.

Hypothesis xy_neq : Neqb x y = false.

Definition BDDreplace :=
  match BDDvar_make gc cfg ul y with
  | (cfg1, nodey) => BDDsubst cfg1 (nodey :: ul) node x nodey
  end.

Lemma BDDreplace_config_OK : BDDconfig_OK (fst BDDreplace).
Proof.
  unfold BDDreplace in |- *.  elim (prod_sum _ _ (BDDvar_make gc cfg ul y)).
  intros cfg1 H.  elim H; clear H.  intros nodey H.  rewrite H.
  replace cfg1 with (fst (BDDvar_make gc cfg ul y)).
  replace nodey with (snd (BDDvar_make gc cfg ul y)).  apply BDDsubst_config_OK.
  apply BDDvar_make_config_OK; assumption.
  apply BDDvar_make_list_OK_cons; assumption.  apply used_node'_cons_node'_ul.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.  
  apply BDDvar_make_used_nodes_preserved; assumption.  assumption.  
  apply used_node'_cons_node_ul.  rewrite H; reflexivity.
  rewrite H; reflexivity.
Qed.

Lemma BDDreplace_node_OK : config_node_OK (fst BDDreplace) (snd BDDreplace).
Proof.
  unfold BDDreplace in |- *.  elim (prod_sum _ _ (BDDvar_make gc cfg ul y)).
  intros cfg1 H.  elim H; clear H.  intros nodey H.  rewrite H.
  replace cfg1 with (fst (BDDvar_make gc cfg ul y)).
  replace nodey with (snd (BDDvar_make gc cfg ul y)).  apply BDDsubst_node_OK.
  apply BDDvar_make_config_OK; assumption.  
  apply BDDvar_make_list_OK_cons; assumption.  apply used_node'_cons_node'_ul.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.
  apply BDDvar_make_used_nodes_preserved; assumption.  assumption.
  apply used_node'_cons_node_ul.  rewrite H; reflexivity.  
  rewrite H; reflexivity.
Qed.

Lemma BDDreplace_used_nodes_preserved :
 used_nodes_preserved cfg (fst BDDreplace) ul.
Proof.
  unfold BDDreplace in |- *.  elim (prod_sum _ _ (BDDvar_make gc cfg ul y)).
  intros cfg1 H.  elim H; clear H.  intros nodey H.  rewrite H.
  replace cfg1 with (fst (BDDvar_make gc cfg ul y)).
  replace nodey with (snd (BDDvar_make gc cfg ul y)). 
  apply
   used_nodes_preserved_trans with (cfg2 := fst (BDDvar_make gc cfg ul y)).
  assumption.  apply BDDvar_make_used_nodes_preserved; assumption.  
  apply
   used_nodes_preserved_cons with (node := snd (BDDvar_make gc cfg ul y)).  
  apply BDDsubst_used_nodes_preserved.  apply BDDvar_make_config_OK; assumption.
  apply BDDvar_make_list_OK_cons; assumption.  apply used_node'_cons_node'_ul.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.
  apply BDDvar_make_used_nodes_preserved; assumption.  assumption.
  apply used_node'_cons_node_ul.  rewrite H; reflexivity.  
  rewrite H; reflexivity.
Qed.

Lemma BDDreplace_list_OK : used_list_OK (fst BDDreplace) ul.
Proof.
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.
  exact BDDreplace_used_nodes_preserved.
Qed.

Lemma BDDreplace_list_OK_cons :
 used_list_OK (fst BDDreplace) (snd BDDreplace :: ul).
Proof.
  apply node_OK_list_OK.  exact BDDreplace_node_OK.  exact BDDreplace_list_OK.
Qed.

Lemma BDDreplace_is_replace :
 bool_fun_eq (bool_fun_of_BDD (fst BDDreplace) (snd BDDreplace))
   (bool_fun_replace x y (bool_fun_of_BDD cfg node)).
Proof.
  unfold BDDreplace in |- *.  elim (prod_sum _ _ (BDDvar_make gc cfg ul y)).
  intros cfg1 H.  elim H; clear H.  intros nodey H.  rewrite H.
  replace cfg1 with (fst (BDDvar_make gc cfg ul y)).
  replace nodey with (snd (BDDvar_make gc cfg ul y)).  unfold bool_fun_replace in |- *.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_subst x
                (bool_fun_of_BDD (fst (BDDvar_make gc cfg ul y))
                   (snd (BDDvar_make gc cfg ul y)))
                (bool_fun_of_BDD (fst (BDDvar_make gc cfg ul y)) node)).
  apply BDDsubst_is_subst.  apply BDDvar_make_config_OK; assumption.  
  apply BDDvar_make_list_OK_cons; assumption.  apply used_node'_cons_node'_ul.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.  
  apply BDDvar_make_used_nodes_preserved; assumption.  assumption.
  apply used_node'_cons_node_ul.  
  apply bool_fun_eq_independent with (bf1 := bool_fun_var y).
  apply bool_fun_eq_sym.  apply BDDvar_make_is_var; assumption.  
  unfold bool_fun_independent, bool_fun_var in |- *.
  unfold bool_fun_restrict, augment, bool_fun_eq in |- *.  intros.  rewrite xy_neq.
  reflexivity.  apply bool_fun_subst_preserves_eq.
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  
  apply BDDvar_make_config_OK; assumption.
  apply BDDvar_make_used_nodes_preserved; assumption.  assumption.  assumption.
  apply BDDvar_make_is_var; assumption.  rewrite H; reflexivity.  
  rewrite H; reflexivity.
Qed.

End BDDreplace_results.

Fixpoint BDDreplacel (cfg : BDDconfig) (ul : list ad) 
 (node : ad) (lx ly : list BDDvar) {struct ly} : BDDconfig * ad :=
  match lx, ly with
  | nil, _ => (cfg, node)
  | _ :: _, nil => (cfg, node)
  | x :: lx', y :: ly' =>
      match BDDreplacel cfg ul node lx' ly' with
      | (cfg1, node1) => BDDreplace cfg1 (node1 :: ul) node1 x y
      end
  end.

Lemma BDDreplacel_lemma :
 forall (lx ly : list ad) (cfg : BDDconfig) (ul : list ad) (node : ad),
 BDDconfig_OK cfg ->
 used_list_OK cfg ul ->
 used_node' cfg ul node ->
 ad_list_neq lx ly = true ->
 BDDconfig_OK (fst (BDDreplacel cfg ul node lx ly)) /\
 config_node_OK (fst (BDDreplacel cfg ul node lx ly))
   (snd (BDDreplacel cfg ul node lx ly)) /\
 used_nodes_preserved cfg (fst (BDDreplacel cfg ul node lx ly)) ul /\
 bool_fun_eq
   (bool_fun_of_BDD (fst (BDDreplacel cfg ul node lx ly))
      (snd (BDDreplacel cfg ul node lx ly)))
   (bool_fun_replacel (bool_fun_of_BDD cfg node) lx ly).
Proof.
  simple induction lx.  simple induction ly.  simpl in |- *.  intros.  split.  assumption.  split.
  apply used_node'_OK with (ul := ul).  assumption.  assumption.  assumption.
  split.  apply used_nodes_preserved_refl.  apply bool_fun_eq_refl.  simpl in |- *.
  intros.  split.  assumption.  split.  apply used_node'_OK with (ul := ul).
  assumption.  assumption.  assumption.  split.
  apply used_nodes_preserved_refl.  apply bool_fun_eq_refl.  simple induction ly.
  simpl in |- *.  intros.  split.  assumption.  split.  apply used_node'_OK with (ul := ul).
  assumption.  assumption.  assumption.  split.
  apply used_nodes_preserved_refl.  apply bool_fun_eq_refl.  simpl in |- *.  intros.
  elim (prod_sum _ _ (BDDreplacel cfg ul node l l0)).  intros cfg1 H5.
  elim H5; clear H5; intros node1 H5.  elim (H l0 cfg ul node H1 H2 H3).
  rewrite H5.  simpl in |- *.  intros.
  elim H7; clear H7; intros H9 H8; elim H8; clear H8; intros H8 H11. 

  cut (used_list_OK cfg1 (node1 :: ul)).  intro.  split.
  apply BDDreplace_config_OK.  assumption.  assumption.
  apply used_node'_cons_node_ul.  split.  apply BDDreplace_node_OK.  assumption.
  assumption.  apply used_node'_cons_node_ul.  split.
  apply used_nodes_preserved_trans with (cfg2 := cfg1).  assumption.  assumption.
  apply used_nodes_preserved_cons with (node := node1).
  apply BDDreplace_used_nodes_preserved.  assumption.  assumption.
  apply used_node'_cons_node_ul.  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_replace a a0 (bool_fun_of_BDD cfg1 node1)).
  apply BDDreplace_is_replace.  assumption.  assumption.
  apply used_node'_cons_node_ul.  apply not_true_is_false.  unfold not in |- *; intro.
  rewrite H10 in H4; discriminate.  apply bool_fun_replace_preserves_eq.
  assumption.  apply node_OK_list_OK.  assumption.  
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.  assumption.  
  elim (andb_prop _ _ H4).  trivial.  
Qed.

Section BDDreplacel_results.

Variable cfg : BDDconfig.
Variable ul : list ad.
Variable node : ad.
Variable lx ly : list BDDvar.

Hypothesis cfg_OK : BDDconfig_OK cfg.
Hypothesis ul_OK : used_list_OK cfg ul.
Hypothesis used : used_node' cfg ul node.

Hypothesis lxy_neq : ad_list_neq lx ly = true.

Lemma BDDreplacel_config_OK :
 BDDconfig_OK (fst (BDDreplacel cfg ul node lx ly)).
Proof.
  exact
   (proj1 (BDDreplacel_lemma lx ly cfg ul node cfg_OK ul_OK used lxy_neq)).
Qed.

Lemma BDDreplacel_node_OK :
 config_node_OK (fst (BDDreplacel cfg ul node lx ly))
   (snd (BDDreplacel cfg ul node lx ly)).
Proof.
  exact
   (proj1
      (proj2 (BDDreplacel_lemma lx ly cfg ul node cfg_OK ul_OK used lxy_neq))).
Qed.

Lemma BDDreplacel_used_nodes_preserved :
 used_nodes_preserved cfg (fst (BDDreplacel cfg ul node lx ly)) ul.
Proof.
  exact
   (proj1
      (proj2
         (proj2
            (BDDreplacel_lemma lx ly cfg ul node cfg_OK ul_OK used lxy_neq)))).
Qed.

Lemma BDDreplacel_list_OK :
 used_list_OK (fst (BDDreplacel cfg ul node lx ly)) ul.
Proof.
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.
  exact BDDreplacel_used_nodes_preserved.
Qed.

Lemma BDDreplacel_list_OK_cons :
 used_list_OK (fst (BDDreplacel cfg ul node lx ly))
   (snd (BDDreplacel cfg ul node lx ly) :: ul).
Proof.
  apply node_OK_list_OK.  exact BDDreplacel_node_OK.  exact BDDreplacel_list_OK.
Qed.

Lemma BDDreplacel_is_replacel :
 bool_fun_eq
   (bool_fun_of_BDD (fst (BDDreplacel cfg ul node lx ly))
      (snd (BDDreplacel cfg ul node lx ly)))
   (bool_fun_replacel (bool_fun_of_BDD cfg node) lx ly).
Proof.
  exact
   (proj2
      (proj2
         (proj2
            (BDDreplacel_lemma lx ly cfg ul node cfg_OK ul_OK used lxy_neq)))).
Qed.

End BDDreplacel_results.

End BDDquant.

Fixpoint be_x_free (x : BDDvar) (be : bool_expr) {struct be} : bool :=
  match be with
  | Zero => false
  | One => false
  | Var y => Neqb x y
  | Neg be1 => be_x_free x be1
  | Or be1 be2 => be_x_free x be1 || be_x_free x be2
  | ANd be1 be2 => be_x_free x be1 || be_x_free x be2
  | Impl be1 be2 => be_x_free x be1 || be_x_free x be2
  | Iff be1 be2 => be_x_free x be1 || be_x_free x be2
  end.

Lemma subst_x_free :
 forall (be bex : bool_expr) (x y : BDDvar),
 be_x_free y (subst x bex be) = true ->
 be_x_free y be = true /\ Neqb x y = false \/ be_x_free y bex = true.
Proof.
  simple induction be.  simpl in |- *.  intros.  discriminate.  simpl in |- *.  intros.  discriminate.
  simpl in |- *.  intros.  elim (sumbool_of_bool (Neqb x b)).  intro y0.  rewrite y0 in H.
  right.  assumption.  intro y0.  rewrite y0 in H.  simpl in H.  left.  split.
  assumption.  rewrite (Neqb_complete _ _ H).  assumption.  simpl in |- *.  intros.
  apply H.  assumption.  simpl in |- *.  intros.  elim (orb_prop _ _ H1).  intro.
  elim (H bex x y H2).  intros.  elim H3.  intros.  rewrite H4.  left.  simpl in |- *.
  split.  reflexivity.  assumption.  intro.  right.  assumption.  intro.
  elim (H0 bex x y H2).  intros.  elim H3.  intros.  rewrite H4.  left.  split.
  elim (be_x_free y b); reflexivity.  assumption.  intro.  right.  assumption.
  simpl in |- *.  intros.  elim (orb_prop _ _ H1).  intro.  elim (H bex x y H2).
  intros.  elim H3.  intros.  rewrite H4.  left.  simpl in |- *.  split.  reflexivity.
  assumption.  intro.  right.  assumption.  intro.  elim (H0 bex x y H2).
  intros.  elim H3.  intros.  rewrite H4.  left.  split.
  elim (be_x_free y b); reflexivity.  assumption.  intro.  right.  assumption.
  simpl in |- *.  intros.  elim (orb_prop _ _ H1).  intro.  elim (H bex x y H2).
  intros.  elim H3.  intros.  rewrite H4.  left.  simpl in |- *.  split.  reflexivity.
  assumption.  intro.  right.  assumption.  intro.  elim (H0 bex x y H2).
  intros.  elim H3.  intros.  rewrite H4.  left.  split.
  elim (be_x_free y b); reflexivity.  assumption.  intro.  right.  assumption.
  simpl in |- *.  intros.  elim (orb_prop _ _ H1).  intro.  elim (H bex x y H2).
  intros.  elim H3.  intros.  rewrite H4.  left.  simpl in |- *.  split.  reflexivity.
  assumption.  intro.  right.  assumption.  intro.  elim (H0 bex x y H2).
  intros.  elim H3.  intros.  rewrite H4.  left.  split.
  elim (be_x_free y b); reflexivity.  assumption.  intro.  right.  assumption.
Qed.

Lemma restrict_x_free :
 forall (be : bool_expr) (x y : BDDvar) (b : bool),
 be_x_free y (restrict x b be) = true ->
 be_x_free y be = true /\ Neqb x y = false.
Proof.
  unfold restrict in |- *.  intros.  elim (subst_x_free be (bool_to_be b) x y H).
  trivial.  elim b.  simpl in |- *.  intro.  discriminate.  simpl in |- *.  intro.
  discriminate.
Qed.


Lemma replace_x_free :
 forall (be : bool_expr) (x y z : BDDvar),
 be_x_free z (replace x y be) = true ->
 be_x_free z be = true /\ Neqb x z = false \/ Neqb y z = true.
Proof.
  unfold replace in |- *.  intros.  elim (subst_x_free be (Var y) x z H).  intros.
  left.  assumption.  simpl in |- *.  intro.  right.  rewrite (Neqb_complete _ _ H0).
  apply Neqb_correct.
Qed.

Lemma replacel_x_free :
 forall (lx ly : list ad) (be : bool_expr) (x : BDDvar),
 length lx = length ly ->
 be_x_free x (replacel be lx ly) = true ->
 be_x_free x be = true /\ ~ In x lx \/ In x ly.
Proof.
  simple induction lx.  intro.  elim ly.  simpl in |- *.  intros.  left.  split.  assumption.
  unfold not in |- *.  trivial.  simpl in |- *.  intros.  left.  split.  assumption.
  unfold not in |- *.  trivial.  intros a l H ly.  elim ly.  simpl in |- *.  intros.
  discriminate.  simpl in |- *.  intros.
  elim (replace_x_free (replacel be l l0) a a0 x H2).  intro.
  elim H3; intros H5 H6.
  elim (H l0 be x).  intro.
  elim H4; intros H8 H9.

  left.
  split.  assumption.  unfold not in |- *; intro.  elim H7; intro.  rewrite H10 in H6.
  rewrite (Neqb_correct x) in H6.  discriminate.  elim (H9 H10).  intro.
  right.  right.  assumption.  apply eq_add_S.  assumption.  assumption.  intro.
  right.  left.  apply Neqb_complete.  assumption.  
Qed.

Lemma impl_x_free :
 forall (be1 be2 : bool_expr) (x : BDDvar),
 be_x_free x (Impl be1 be2) = true ->
 be_x_free x be1 = true \/ be_x_free x be2 = true.
Proof.
  simpl in |- *.  intros.  elim (orb_prop _ _ H); auto.  
Qed.

Lemma and_x_free :
 forall (be1 be2 : bool_expr) (x : BDDvar),
 be_x_free x (ANd be1 be2) = true ->
 be_x_free x be1 = true \/ be_x_free x be2 = true.
Proof.
  simpl in |- *.  intros.  elim (orb_prop _ _ H); auto.  
Qed.

Lemma univ_x_free :
 forall (be : bool_expr) (x y : BDDvar),
 be_x_free y (forall_ x be) = true ->
 be_x_free y be = true /\ Neqb x y = false.
Proof.
  unfold forall_ in |- *.  intros.  elim (and_x_free _ _ _ H).  intro.
  elim (restrict_x_free _ _ _ _ H0).  auto.  intro.
  elim (restrict_x_free _ _ _ _ H0).  auto.  
Qed.

Lemma ex_x_free :
 forall (be : bool_expr) (x y : BDDvar),
 be_x_free y (be_ex x be) = true ->
 be_x_free y be = true /\ Neqb x y = false.
Proof.
  unfold be_ex in |- *.  intros.  elim (and_x_free _ _ _ H).  intro.
  elim (restrict_x_free _ _ _ _ H0).  auto.  intro.
  elim (restrict_x_free _ _ _ _ H0).  auto.  
Qed.

Lemma univl_x_free :
 forall (lx : list ad) (be : bool_expr) (x : BDDvar),
 be_x_free x (univl be lx) = true -> be_x_free x be = true /\ ~ In x lx.
Proof.
  simple induction lx.  simpl in |- *.  auto.  intros.  elim (univ_x_free _ _ _ H0).
  fold (univl be l) in |- *.  intros.  elim (H be x H1).  intros.  split.  assumption.
  simpl in |- *.  unfold not in |- *; intros.  elim H5.  intro.  rewrite H6 in H2.
  rewrite (Neqb_correct x) in H2; discriminate.  intro.  elim (H4 H6).  
Qed.

Lemma exl_x_free :
 forall (lx : list ad) (be : bool_expr) (x : BDDvar),
 be_x_free x (exl be lx) = true -> be_x_free x be = true /\ ~ In x lx.
Proof.
  simple induction lx.  simpl in |- *.  auto.  intros.  elim (ex_x_free _ _ _ H0).
  fold (exl be l) in |- *.  intros.  elim (H be x H1).  intros.  split.  assumption.
  simpl in |- *.  unfold not in |- *; intros.  elim H5.  intro.  rewrite H6 in H2.
  rewrite (Neqb_correct x) in H2; discriminate.  intro.  elim (H4 H6).  
Qed.

Definition var_env' := nat -> bool.
Definition var_env_to_env' (ve : var_env) : var_env' :=
  fun n : nat => ve (N_of_nat n).
Definition var_env'_to_env (ve : var_env') : var_env :=
  fun x : BDDvar => ve (nat_of_N x).
Definition eval_be' (be : bool_expr) (ve : var_env') :=
  bool_fun_of_bool_expr be (var_env'_to_env ve).
Definition var_env'' := Map unit.
Definition var_env''_to_env (ve : var_env'') : var_env :=
  fun x : ad => in_dom _ x ve.
Definition var_env''_to_env' (ve : var_env'') : var_env' :=
  fun n : nat => in_dom _ (N_of_nat n) ve.

Definition be_eq (be1 be2 : bool_expr) :=
  forall ve : var_env', eval_be' be1 ve = eval_be' be2 ve.
Definition be_eq_dec (be1 be2 : bool_expr) :=
  is_tauto (fun x _ => x) (Iff be1 be2).
(* [x,_]x is same as gc_inf *)
Definition be_le (be1 be2 : bool_expr) :=
  forall ve : var_env', eval_be' be1 ve = true -> eval_be' be2 ve = true.

Lemma be_eq_refl : forall be : bool_expr, be_eq be be.
Proof.
  unfold be_eq in |- *.  trivial.
Qed.

Lemma be_eq_sym : forall be1 be2 : bool_expr, be_eq be1 be2 -> be_eq be2 be1.
Proof.
  unfold be_eq in |- *.  intros.  rewrite (H ve).  reflexivity.
Qed.

Lemma be_eq_le : forall be1 be2 : bool_expr, be_eq be1 be2 -> be_le be1 be2.
Proof.
  unfold be_eq, be_le in |- *.  intros.  rewrite <- (H ve).  assumption.
Qed.

Lemma be_eq_dec_correct :
 forall be1 be2 : bool_expr,
 bool_fun_eq (bool_fun_of_bool_expr be1) (bool_fun_of_bool_expr be2) ->
 be_eq_dec be1 be2 = true.
Proof.
  intros.  unfold be_eq_dec in |- *.
  elim (is_tauto_lemma (fun x _ => x) gc_inf_OK (Iff be1 be2)).  intros.  clear H0.
  apply H1.  simpl in |- *.  unfold bool_fun_iff, bool_fun_one in |- *.  unfold bool_fun_eq in |- *.
  intros.  unfold bool_fun_eq in H.  rewrite (H vb).
  elim (bool_fun_of_bool_expr be2 vb).  reflexivity.  reflexivity.
Qed.

Lemma be_eq_dec_complete :
 forall be1 be2 : bool_expr,
 be_eq_dec be1 be2 = true ->
 bool_fun_eq (bool_fun_of_bool_expr be1) (bool_fun_of_bool_expr be2).
Proof.
  unfold be_eq_dec in |- *.  intros.
  elim (is_tauto_lemma (fun x _ => x) gc_inf_OK (Iff be1 be2)).  intros.  clear H1.
  cut (bool_fun_eq bool_fun_one (bool_fun_of_bool_expr (Iff be1 be2))).  simpl in |- *.
  unfold bool_fun_one, bool_fun_eq, bool_fun_iff in |- *.  intros.
  rewrite
   (eqb_prop (bool_fun_of_bool_expr be1 vb) (bool_fun_of_bool_expr be2 vb))
   .
  reflexivity.  symmetry  in |- *.  apply H1.  apply H0.  assumption.
Qed.

Lemma be_eq_dec_eq :
 forall be1 be2 : bool_expr, be_eq_dec be1 be2 = true -> be_eq be1 be2.
Proof.
  intros.  unfold be_eq in |- *.  unfold eval_be' in |- *.  intros.
  cut (bool_fun_eq bool_fun_one (bool_fun_of_bool_expr (Iff be1 be2))).  simpl in |- *.
  unfold bool_fun_one, bool_fun_eq, bool_fun_iff in |- *.  intros.
  rewrite
   (eqb_prop (bool_fun_of_bool_expr be1 (var_env'_to_env ve))
      (bool_fun_of_bool_expr be2 (var_env'_to_env ve)))
   .
  reflexivity.  symmetry  in |- *.  apply H0.
  elim (is_tauto_lemma (fun x _ => x) gc_inf_OK (Iff be1 be2)).  intros.  apply H0.
  exact H.
Qed.

Lemma bool_fun_var_ext : forall x : BDDvar, bool_fun_ext (bool_fun_var x).
Proof.
  unfold bool_fun_ext, bool_fun_var in |- *.  trivial.
Qed.

Lemma bool_fun_neg_ext :
 forall bf1 : bool_fun, bool_fun_ext bf1 -> bool_fun_ext (bool_fun_neg bf1).
Proof.
  unfold bool_fun_neg, bool_fun_ext in |- *.  intros.  rewrite (H vb vb' H0).
  reflexivity.
Qed.

Lemma bool_fun_and_ext :
 forall bf1 bf2 : bool_fun,
 bool_fun_ext bf1 -> bool_fun_ext bf2 -> bool_fun_ext (bool_fun_and bf1 bf2).
Proof.
  unfold bool_fun_ext, bool_fun_and in |- *.  intros.  rewrite (H vb vb' H1).
  rewrite (H0 vb vb' H1).  reflexivity.
Qed.

Lemma bool_fun_or_ext :
 forall bf1 bf2 : bool_fun,
 bool_fun_ext bf1 -> bool_fun_ext bf2 -> bool_fun_ext (bool_fun_or bf1 bf2).
Proof.
  unfold bool_fun_ext, bool_fun_or in |- *.  intros.  rewrite (H vb vb' H1).
  rewrite (H0 vb vb' H1).  reflexivity.
Qed.

Lemma bool_fun_impl_ext :
 forall bf1 bf2 : bool_fun,
 bool_fun_ext bf1 -> bool_fun_ext bf2 -> bool_fun_ext (bool_fun_impl bf1 bf2).
Proof.
  unfold bool_fun_ext, bool_fun_impl in |- *.  intros.  rewrite (H vb vb' H1).
  rewrite (H0 vb vb' H1).  reflexivity.
Qed.

Lemma bool_fun_iff_ext :
 forall bf1 bf2 : bool_fun,
 bool_fun_ext bf1 -> bool_fun_ext bf2 -> bool_fun_ext (bool_fun_iff bf1 bf2).
Proof.
  unfold bool_fun_ext, bool_fun_iff in |- *.  intros.  rewrite (H vb vb' H1).
  rewrite (H0 vb vb' H1).  reflexivity.
Qed.

Lemma bool_fun_of_be_ext :
 forall be : bool_expr, bool_fun_ext (bool_fun_of_bool_expr be).
Proof.
  simple induction be.  simpl in |- *.  exact bool_fun_ext_zero.  exact bool_fun_ext_one.
  exact bool_fun_var_ext.  simpl in |- *.  intros.  apply bool_fun_neg_ext.  assumption.
  simpl in |- *.  intros.  apply bool_fun_or_ext.  assumption.  assumption.  simpl in |- *.
  intros.  apply bool_fun_and_ext.  assumption.  assumption.  simpl in |- *.  intros.
  apply bool_fun_impl_ext.  assumption.  assumption.  simpl in |- *.  intros.
  apply bool_fun_iff_ext.  assumption.  assumption.
Qed.

Lemma be_le_refl : forall be : bool_expr, be_le be be.
Proof.
  unfold be_le in |- *.  auto.
Qed.

Lemma be_le_trans :
 forall be1 be2 be3 : bool_expr,
 be_le be1 be2 -> be_le be2 be3 -> be_le be1 be3.
Proof.
  unfold be_le in |- *; auto.
Qed.

Lemma be_le_antisym :
 forall be1 be2 : bool_expr, be_le be1 be2 -> be_le be2 be1 -> be_eq be1 be2.
Proof.
  unfold be_le in |- *.  unfold be_eq in |- *.  intros.
  elim (sumbool_of_bool (eval_be' be1 ve)).  intro y.  rewrite y.
  rewrite (H ve).  reflexivity.  assumption.  intro y.  rewrite y.  symmetry  in |- *.
  apply not_true_is_false.  unfold not in |- *; intro.  rewrite (H0 ve H1) in y.
  discriminate.
Qed.

Lemma be_eq_trans :
 forall be1 be2 be3 : bool_expr,
 be_eq be1 be2 -> be_eq be2 be3 -> be_eq be1 be3.
Proof.
  unfold be_eq in |- *.  intros.  rewrite (H ve).  apply H0.
Qed.

Lemma be_eq_eq_dec :
 forall be1 be2 : bool_expr, be_eq be1 be2 -> be_eq_dec be1 be2 = true.
Proof.
  intros.  elim (is_tauto_lemma (fun x _ => x) gc_inf_OK (Iff be1 be2)).  intros.
  apply H1.  clear H0 H1.  simpl in |- *.  unfold bool_fun_iff, bool_fun_one, bool_fun_eq in |- *.
  intro.  unfold be_eq in H.  unfold eval_be' in H.
  cut
   (bool_fun_of_bool_expr be1 vb =
    bool_fun_of_bool_expr be1 (var_env'_to_env (var_env_to_env' vb))).
  intro.  cut
   (bool_fun_of_bool_expr be2 vb =
    bool_fun_of_bool_expr be2 (var_env'_to_env (var_env_to_env' vb))).
  intro.  rewrite H0.  rewrite H1.  rewrite (H (var_env_to_env' vb)).  symmetry  in |- *.
  apply eqb_reflx.  apply (bool_fun_of_be_ext be2).
  unfold var_env'_to_env, var_env_to_env' in |- *.  intro.  rewrite (N_of_nat_of_N x).
  reflexivity.  apply (bool_fun_of_be_ext be1).  intro.
  unfold var_env'_to_env, var_env_to_env' in |- *.  rewrite (N_of_nat_of_N x).
  reflexivity.
Qed.

Lemma be_le_not_1 :
 forall be1 be2 : bool_expr, be_le be1 be2 -> be_le (Neg be2) (Neg be1).
Proof.
  unfold be_le in |- *.  intros.  unfold eval_be' in |- *.  simpl in |- *.  unfold eval_be' in H0.
  simpl in H0.  unfold bool_fun_neg in |- *.  unfold bool_fun_neg in H0.
  unfold eval_be' in H.
  elim (sumbool_of_bool (bool_fun_of_bool_expr be1 (var_env'_to_env ve))).
  intro y.  rewrite (H ve y) in H0.  discriminate.  intro y.  rewrite y.
  reflexivity.
Qed.

Lemma and_le :
 forall be1 be2 be1' be2' : bool_expr,
 be_le be1 be1' -> be_le be2 be2' -> be_le (ANd be1 be2) (ANd be1' be2').
Proof.
  unfold be_le in |- *.  unfold eval_be' in |- *.  simpl in |- *.  unfold bool_fun_and in |- *.  intros.
  elim (andb_prop _ _ H1).  intros.  rewrite (H ve H2).  rewrite (H0 ve H3).
  reflexivity.
Qed.

Lemma or_le :
 forall be1 be2 be1' be2' : bool_expr,
 be_le be1 be1' -> be_le be2 be2' -> be_le (Or be1 be2) (Or be1' be2').
Proof.
  unfold be_le in |- *.  unfold eval_be' in |- *.  simpl in |- *.  unfold bool_fun_or in |- *.  intros.
  elim (orb_prop _ _ H1).  intros.  rewrite (H ve H2).  reflexivity.
  intros.  rewrite (H0 ve H2).  auto with bool.
Qed.

Lemma impl_le :
 forall be1 be2 be1' be2' : bool_expr,
 be_le be1' be1 -> be_le be2 be2' -> be_le (Impl be1 be2) (Impl be1' be2').
Proof.
  unfold be_le in |- *.  unfold eval_be' in |- *.  simpl in |- *.  unfold bool_fun_impl in |- *.  intros.
  elim (sumbool_of_bool (bool_fun_of_bool_expr be2' (var_env'_to_env ve))).
  intro y.  rewrite y.
  elim (bool_fun_of_bool_expr be1' (var_env'_to_env ve)); reflexivity.  intro y.
  rewrite y.
  elim (sumbool_of_bool (bool_fun_of_bool_expr be1' (var_env'_to_env ve))).
  intro y0.  rewrite (H ve y0) in H1.  simpl in H1.  rewrite (H0 ve H1) in y.
  discriminate.  intro y0.  rewrite y0.  reflexivity.
Qed.

Lemma and_eq :
 forall be1 be2 be1' be2' : bool_expr,
 be_eq be1 be1' -> be_eq be2 be2' -> be_eq (ANd be1 be2) (ANd be1' be2').
Proof.
  unfold be_eq in |- *.  unfold eval_be' in |- *.  simpl in |- *.  unfold bool_fun_and in |- *.  intros.
  rewrite (H ve).  rewrite (H0 ve).  reflexivity.
Qed.

Lemma or_eq :
 forall be1 be2 be1' be2' : bool_expr,
 be_eq be1 be1' -> be_eq be2 be2' -> be_eq (Or be1 be2) (Or be1' be2').
Proof.
  unfold be_eq in |- *.  unfold eval_be' in |- *.  simpl in |- *.  unfold bool_fun_or in |- *.  intros.
  rewrite (H ve).  rewrite (H0 ve).  reflexivity.
Qed.

Lemma impl_eq :
 forall be1 be2 be1' be2' : bool_expr,
 be_eq be1 be1' -> be_eq be2 be2' -> be_eq (Impl be1 be2) (Impl be1' be2').
Proof.
  unfold be_eq in |- *.  unfold eval_be' in |- *.  simpl in |- *.  unfold bool_fun_impl in |- *.  intros.
  rewrite (H ve).  rewrite (H0 ve).  reflexivity.
Qed.

Lemma iff_eq :
 forall be1 be2 be1' be2' : bool_expr,
 be_eq be1 be1' -> be_eq be2 be2' -> be_eq (Iff be1 be2) (Iff be1' be2').
Proof.
  unfold be_eq in |- *.  unfold eval_be' in |- *.  simpl in |- *.  unfold bool_fun_iff in |- *.  intros.
  rewrite (H ve).  rewrite (H0 ve).  reflexivity.
Qed.

Lemma neg_eq_eq :
 forall be1 be2 : bool_expr, be_eq (Neg be1) (Neg be2) -> be_eq be1 be2.
Proof.
  unfold be_eq in |- *.  unfold eval_be' in |- *.  simpl in |- *.  unfold bool_fun_neg in |- *.  intros.
  rewrite (negb_intro (bool_fun_of_bool_expr be1 (var_env'_to_env ve))).
  rewrite (H ve).
  rewrite (negb_elim (bool_fun_of_bool_expr be2 (var_env'_to_env ve))).
  reflexivity.
Qed.

Lemma eq_neg_eq :
 forall be1 be2 : bool_expr, be_eq be1 be2 -> be_eq (Neg be1) (Neg be2).
Proof.
  unfold be_eq in |- *.  unfold eval_be' in |- *.  simpl in |- *.  intros.  unfold bool_fun_neg in |- *.
  rewrite (H ve).  reflexivity.
Qed.

Section Nsec.

Variable N : nat.

Definition ap (n : nat) := N_of_nat n.
Definition ap' (n : nat) := N_of_nat (N + n).

Fixpoint lx_1 (n : nat) : list ad :=
  match n with
  | O => nil
  | S m => ap m :: lx_1 m
  end.

Fixpoint lx'_1 (n : nat) : list ad :=
  match n with
  | O => nil (A:=ad)
  | S m => ap' m :: lx'_1 m
  end.

Definition lx := lx_1 N.
Definition lx' := lx'_1 N.
Lemma ap_neq_ap' : forall n : nat, n < N -> Neqb (ap n) (ap' n) = false.
Proof.
  simple induction n.  intros.  unfold ap, ap' in |- *.  rewrite <- (plus_n_O N).
  apply not_true_is_false.  unfold not in |- *; intro.  elim (lt_irrefl N).
  replace (N < N) with (0 < N).  assumption.
  replace 0 with (nat_of_N (N_of_nat 0)).  rewrite (Neqb_complete _ _ H0).
  rewrite (nat_of_N_of_nat N).  reflexivity.  reflexivity.  intros.
  unfold ap, ap' in |- *.  rewrite <- (plus_Snm_nSm N n0).  apply not_true_is_false.
  unfold not in |- *; intro.
  cut (nat_of_N (N_of_nat (S n0)) = nat_of_N (N_of_nat (S N + n0))).
  rewrite (nat_of_N_of_nat (S n0)).  rewrite (nat_of_N_of_nat (S N + n0)).
  simpl in |- *.  intro.  unfold ap, ap' in H.  rewrite <- (eq_add_S _ _ H2) in H.
  rewrite (Neqb_correct (N_of_nat n0)) in H.  cut (true = false).  intro.
  discriminate.  apply H.  apply lt_trans with (m := S n0).  apply lt_n_Sn.
  assumption.  rewrite (Neqb_complete _ _ H1).  reflexivity.
Qed.

Lemma lx_1_neg_lx'_1 :
 forall n : nat, n <= N -> ad_list_neq (lx_1 n) (lx'_1 n) = true.
Proof.
  simple induction n.  simpl in |- *.  reflexivity.  simpl in |- *.  intros.  apply andb_true_intro.
  split.  rewrite (ap_neq_ap' n0).  reflexivity.  exact H0.  apply H.
  apply lt_le_weak.  assumption.
Qed.

Lemma lx_neq_lx' : ad_list_neq lx lx' = true.
Proof.
  unfold lx, lx' in |- *.  apply lx_1_neg_lx'_1.  apply le_n.
Qed.

Lemma lt_O_n_lx'_1 : forall n : nat, 0 < n -> In (ap' 0) (lx'_1 n).
Proof.
  simple induction n.  intros.  elim (lt_irrefl _ H).  intros.  simpl in |- *.  unfold lt in H0.
  elim (le_le_S_eq 0 n0).  intros.  right.  apply H.  unfold lt in |- *.  assumption.
  intro.  left.  rewrite H1.  reflexivity.  apply le_S_n.  assumption.  
Qed.

Definition bool_fun_mu_all (bft bfg : bool_fun) : bool_fun :=
  bool_fun_univl (bool_fun_impl bft (bool_fun_replacel bfg lx lx')) lx'.

Definition bool_fun_mu_ex (bft bfg : bool_fun) : bool_fun :=
  bool_fun_exl (bool_fun_and bft (bool_fun_replacel bfg lx lx')) lx'.

Definition mu_all_eval (t be : bool_expr) : bool_expr :=
  univl (Impl t (replacel be lx lx')) lx'.

Definition mu_ex_eval (t be : bool_expr) : bool_expr :=
  exl (ANd t (replacel be lx lx')) lx'.

Definition BDDmu_all (gc : BDDconfig -> list ad -> BDDconfig)
  (cfg : BDDconfig) (ul : list ad) (nodet nodeg : ad) :=
  match BDDreplacel gc cfg ul nodeg lx lx' with
  | (cfgr, noder) =>
      match BDDimpl gc cfgr (noder :: ul) nodet noder with
      | (cfgi, nodei) => BDDunivl gc cfgi (nodei :: ul) nodei lx'
      end
  end.

Definition BDDmu_ex (gc : BDDconfig -> list ad -> BDDconfig)
  (cfg : BDDconfig) (ul : list ad) (nodet nodeg : ad) :=
  match BDDreplacel gc cfg ul nodeg lx lx' with
  | (cfgr, noder) =>
      match BDDand gc cfgr (noder :: ul) nodet noder with
      | (cfga, nodea) => BDDexl gc cfga (nodea :: ul) nodea lx'
      end
  end.

Lemma bool_fun_univl_preserves_eq :
 forall (l : list ad) (bf1 bf2 : bool_fun),
 bool_fun_eq bf1 bf2 ->
 bool_fun_eq (bool_fun_univl bf1 l) (bool_fun_univl bf2 l).
Proof.
  simple induction l.  intros.  simpl in |- *.  assumption.  simpl in |- *.  intros.
  apply bool_fun_forall_preserves_eq.  apply H; assumption.
Qed.

Lemma bool_fun_exl_preserves_eq :
 forall (l : list ad) (bf1 bf2 : bool_fun),
 bool_fun_eq bf1 bf2 -> bool_fun_eq (bool_fun_exl bf1 l) (bool_fun_exl bf2 l).
Proof.
  simple induction l.  intros.  simpl in |- *.  assumption.  simpl in |- *.  intros.
  apply bool_fun_ex_preserves_eq.  apply H; assumption.
Qed.

Lemma mu_all_eval_ok :
 forall t be : bool_expr,
 bool_fun_eq (bool_fun_of_bool_expr (mu_all_eval t be))
   (bool_fun_mu_all (bool_fun_of_bool_expr t) (bool_fun_of_bool_expr be)).
Proof.
  unfold mu_all_eval in |- *.  unfold bool_fun_mu_all in |- *.  intros.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_univl
                (bool_fun_of_bool_expr (Impl t (replacel be lx lx'))) lx').
  apply univl_OK.  apply bool_fun_univl_preserves_eq.  simpl in |- *.
  apply bool_fun_impl_preserves_eq.  apply bool_fun_eq_refl.  apply replacel_OK.
Qed.

 
Lemma mu_ex_eval_ok :
 forall t be : bool_expr,
 bool_fun_eq (bool_fun_of_bool_expr (mu_ex_eval t be))
   (bool_fun_mu_ex (bool_fun_of_bool_expr t) (bool_fun_of_bool_expr be)).
Proof.
  unfold mu_ex_eval in |- *.  unfold bool_fun_mu_ex in |- *.  intros.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_exl
                (bool_fun_of_bool_expr (ANd t (replacel be lx lx'))) lx').
  apply exl_OK.  apply bool_fun_exl_preserves_eq.  simpl in |- *.
  apply bool_fun_and_preserves_eq.  apply bool_fun_eq_refl.  apply replacel_OK.
Qed.

Lemma bool_fun_replacel_preserves_eq :
 forall (lz ly : list ad) (bf1 bf2 : bool_fun),
 bool_fun_eq bf1 bf2 ->
 bool_fun_eq (bool_fun_replacel bf1 lz ly) (bool_fun_replacel bf2 lz ly).
Proof.
  simple induction lz.  intros.  elim ly; intros; assumption.  intros.  elim ly.
  assumption.  intros.  simpl in |- *.  apply bool_fun_replace_preserves_eq.  apply H.
  assumption.
Qed.

Lemma bool_fun_mu_all_preserves_eq :
 forall bft1 bft2 bfg1 bfg2 : bool_fun,
 bool_fun_eq bft1 bft2 ->
 bool_fun_eq bfg1 bfg2 ->
 bool_fun_eq (bool_fun_mu_all bft1 bfg1) (bool_fun_mu_all bft2 bfg2).
Proof.
  unfold bool_fun_mu_all in |- *.  intros.  apply bool_fun_univl_preserves_eq.
  apply bool_fun_impl_preserves_eq.  assumption.
  apply bool_fun_replacel_preserves_eq.  assumption.
Qed.

Lemma bool_fun_mu_ex_preserves_eq :
 forall bft1 bft2 bfg1 bfg2 : bool_fun,
 bool_fun_eq bft1 bft2 ->
 bool_fun_eq bfg1 bfg2 ->
 bool_fun_eq (bool_fun_mu_ex bft1 bfg1) (bool_fun_mu_ex bft2 bfg2).
Proof.
  unfold bool_fun_mu_ex in |- *.  intros.  apply bool_fun_exl_preserves_eq.
  apply bool_fun_and_preserves_eq.  assumption.
  apply bool_fun_replacel_preserves_eq.  assumption.
Qed.

Lemma mu_all_eq :
 forall t be1 be2 : bool_expr,
 be_eq be1 be2 -> be_eq (mu_all_eval t be1) (mu_all_eval t be2).
Proof.
  intros.  apply be_eq_dec_eq.  apply be_eq_dec_correct.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_mu_all (bool_fun_of_bool_expr t)
                (bool_fun_of_bool_expr be1)).
  apply mu_all_eval_ok.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_mu_all (bool_fun_of_bool_expr t)
                (bool_fun_of_bool_expr be2)).
  apply bool_fun_mu_all_preserves_eq.  apply bool_fun_eq_refl.
  apply be_eq_dec_complete.  apply be_eq_eq_dec.  assumption.
  apply bool_fun_eq_sym.  apply mu_all_eval_ok.
Qed.

 
Lemma mu_ex_eq :
 forall t be1 be2 : bool_expr,
 be_eq be1 be2 -> be_eq (mu_ex_eval t be1) (mu_ex_eval t be2).
Proof.
  intros.  apply be_eq_dec_eq.  apply be_eq_dec_correct.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_mu_ex (bool_fun_of_bool_expr t)
                (bool_fun_of_bool_expr be1)).
  apply mu_ex_eval_ok.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_mu_ex (bool_fun_of_bool_expr t)
                (bool_fun_of_bool_expr be2)).
  apply bool_fun_mu_ex_preserves_eq.  apply bool_fun_eq_refl.
  apply be_eq_dec_complete.  apply be_eq_eq_dec.  assumption.
  apply bool_fun_eq_sym.  apply mu_ex_eval_ok.
Qed.

Lemma length_lx_1_eq_lx'_1 :
 forall n : nat, length (lx_1 n) = length (lx'_1 n).
Proof.
  simple induction n.  reflexivity.  intros.  simpl in |- *.  rewrite H.  reflexivity.  
Qed.

Lemma length_lx_eq_lx' : length lx = length lx'.
Proof.
  unfold lx, lx' in |- *.  apply length_lx_1_eq_lx'_1.  
Qed.

Lemma ap'_eq_ap : forall n : nat, ap' n = ap (N + n).
Proof.
  reflexivity.  
Qed.

Lemma in_lx'_1 : forall n m : nat, m < n -> In (ap' m) (lx'_1 n).
Proof.
  simple induction n.  intros.  elim (lt_n_O _ H).  intros.  unfold lt in H0.
  elim (le_le_S_eq m n0).  intros.  right.  apply H.  assumption.  left.
  rewrite H1.  reflexivity.  apply le_S_n.  assumption.  
Qed.

Lemma in_lx' : forall n : nat, N <= n -> S n <= 2 * N -> In (N_of_nat n) lx'.
Proof.
  intros.  replace (N_of_nat n) with (ap' (n - N)).  unfold lx' in |- *.
  apply in_lx'_1.  simpl in H0.  rewrite <- (plus_n_O N) in H0.
  apply plus_lt_reg_l with (p := N).  rewrite <- (le_plus_minus N n H).
  assumption.  unfold ap' in |- *.  rewrite <- (le_plus_minus N n H).  reflexivity.  
Qed.

Lemma in_lx'_1_conv :
 forall n m : nat, In (N_of_nat m) (lx'_1 n) -> N <= m /\ m < N + n.
Proof.
  simple induction n.  simpl in |- *.  intros.  elim H.  simpl in |- *.  intros.  elim H0.  unfold ap' in |- *.
  intros.  replace m with (N + n0).  split.  apply le_plus_l.
  apply plus_lt_compat_l.  unfold lt in |- *.  apply le_n.  rewrite <- (nat_of_N_of_nat m).
  rewrite <- H1.  symmetry  in |- *.  apply nat_of_N_of_nat.  intro.  elim (H _ H1).
  intros.  split.  assumption.  apply lt_trans with (m := N + n0).  assumption.
  apply plus_lt_compat_l.  unfold lt in |- *.  apply le_n.
Qed.

Lemma mu_all_x_free :
 forall (t be : bool_expr) (x : BDDvar),
 be_x_free x (mu_all_eval t be) = true ->
 ~ In x lx' /\ (be_x_free x t = true \/ be_x_free x be = true /\ ~ In x lx).
Proof.
  intros.  unfold mu_all_eval in H.  elim (univl_x_free _ _ _ H).  intros.
  split.  assumption.  elim (impl_x_free _ _ _ H0).  intro.  left.  assumption.
  intro.  right.  elim (replacel_x_free _ _ _ _ length_lx_eq_lx' H2).  trivial.
  intro.  elim (H1 H3).  
Qed.
 
Lemma mu_ex_x_free :
 forall (t be : bool_expr) (x : BDDvar),
 be_x_free x (mu_ex_eval t be) = true ->
 ~ In x lx' /\ (be_x_free x t = true \/ be_x_free x be = true /\ ~ In x lx).
Proof.
  intros.  unfold mu_ex_eval in H.  elim (exl_x_free _ _ _ H).  intros.
  split.  assumption.  elim (and_x_free _ _ _ H0).  intro.  left.  assumption.
  intro.  right.  elim (replacel_x_free _ _ _ _ length_lx_eq_lx' H2).  trivial.
  intro.  elim (H1 H3).
Qed.

Definition be_le2 (be1 be2 : bool_expr) :=
  forall ve : var_env,
  bool_fun_of_bool_expr be1 ve = true -> bool_fun_of_bool_expr be2 ve = true.

Lemma subst_le2 :
 forall (x : BDDvar) (bex be1 be2 : bool_expr),
 be_le2 be1 be2 -> be_le2 (subst x bex be1) (subst x bex be2).
Proof.
  intros.  unfold be_le2 in |- *.  intro.  intro.
  replace (bool_fun_of_bool_expr (subst x bex be2) ve) with
   (bool_fun_subst x (bool_fun_of_bool_expr bex) (bool_fun_of_bool_expr be2)
      ve).
  unfold bool_fun_subst in |- *.  apply H.  rewrite <- H0.  symmetry  in |- *.
  replace
   (bool_fun_of_bool_expr be1 (augment ve x (bool_fun_of_bool_expr bex ve)))
   with
   (bool_fun_subst x (bool_fun_of_bool_expr bex) (bool_fun_of_bool_expr be1)
      ve).
  apply (subst_ok be1 bex x).  unfold bool_fun_subst in |- *.  reflexivity.  symmetry  in |- *.
  apply (subst_ok be2 bex x).
Qed.

Lemma replace_le2 :
 forall (x y : BDDvar) (be1 be2 : bool_expr),
 be_le2 be1 be2 -> be_le2 (replace x y be1) (replace x y be2).
Proof.
  unfold replace in |- *.  intros.  apply subst_le2.  assumption.
Qed.

Lemma replacel_le2 :
 forall (lz ly : list ad) (be1 be2 : bool_expr),
 be_le2 be1 be2 -> be_le2 (replacel be1 lz ly) (replacel be2 lz ly).
Proof.
  simple induction lz.  intros.  elim ly.  assumption.  simpl in |- *.  intros.  assumption.
  intros.  elim ly.  assumption.  simpl in |- *.  intros.  apply replace_le2.  apply H.
  assumption.
Qed.

Lemma impl_le2 :
 forall be be1 be2 : bool_expr,
 be_le2 be1 be2 -> be_le2 (Impl be be1) (Impl be be2).
Proof.
  unfold be_le2 in |- *.  simpl in |- *.  unfold bool_fun_impl in |- *.  intros be be1 be2 H ve.
  elim (bool_fun_of_bool_expr be ve).  simpl in |- *.  intro.  apply H.  assumption.
  simpl in |- *.  reflexivity.
Qed.

Lemma and_le2 :
 forall be1 be2 be1' be2' : bool_expr,
 be_le2 be1 be2 -> be_le2 be1' be2' -> be_le2 (ANd be1 be1') (ANd be2 be2').
Proof.
  unfold be_le2 in |- *.  simpl in |- *.  unfold bool_fun_and in |- *.  intros.
  elim (andb_prop _ _ H1).  intros.  rewrite (H ve H2).  rewrite (H0 ve H3).
  reflexivity.
Qed.

Lemma or_le2 :
 forall be1 be2 be1' be2' : bool_expr,
 be_le2 be1 be2 -> be_le2 be1' be2' -> be_le2 (Or be1 be1') (Or be2 be2').
Proof.
  unfold be_le2 in |- *.  simpl in |- *.  unfold bool_fun_or in |- *.  intros.
  elim (orb_prop _ _ H1).  intros.  rewrite (H ve H2).  reflexivity.
  intros.  rewrite (H0 ve H2).  auto with bool.
Qed.

Lemma univ_le2 :
 forall (x : BDDvar) (be1 be2 : bool_expr),
 be_le2 be1 be2 -> be_le2 (forall_ x be1) (forall_ x be2).
Proof.
  intros.  unfold forall_ in |- *.  apply and_le2.  unfold restrict in |- *.  apply subst_le2.
  assumption.  unfold restrict in |- *.  apply subst_le2.  assumption.
Qed.

Lemma ex_le2 :
 forall (x : BDDvar) (be1 be2 : bool_expr),
 be_le2 be1 be2 -> be_le2 (be_ex x be1) (be_ex x be2).
Proof.
  intros.  unfold be_ex in |- *.  apply or_le2.  unfold restrict in |- *.  apply subst_le2.
  assumption.  unfold restrict in |- *.  apply subst_le2.  assumption.
Qed.

Lemma univl_le2 :
 forall (lz : list ad) (be1 be2 : bool_expr),
 be_le2 be1 be2 -> be_le2 (univl be1 lz) (univl be2 lz).
Proof.
  simple induction lz.  intros.  assumption.  simpl in |- *.  intros.  apply univ_le2.
  apply H.  assumption.
Qed.
 
Lemma exl_le2 :
 forall (lz : list ad) (be1 be2 : bool_expr),
 be_le2 be1 be2 -> be_le2 (exl be1 lz) (exl be2 lz).
Proof.
  simple induction lz.  intros.  assumption.  simpl in |- *.  intros.  apply ex_le2.
  apply H.  assumption.
Qed.

Lemma mu_all_le2 :
 forall t be1 be2 : bool_expr,
 be_le2 be1 be2 -> be_le2 (mu_all_eval t be1) (mu_all_eval t be2).
Proof.
  intros.  unfold mu_all_eval in |- *.  apply univl_le2.  apply impl_le2.
  apply replacel_le2.  assumption.
Qed.
 
Lemma mu_ex_le2 :
 forall t be1 be2 : bool_expr,
 be_le2 be1 be2 -> be_le2 (mu_ex_eval t be1) (mu_ex_eval t be2).
Proof.
  intros.  unfold mu_ex_eval in |- *.  apply exl_le2.  apply and_le2.
  unfold be_le2 in |- *.  auto.  apply replacel_le2.  assumption.
Qed.

Lemma be_le_le2 : forall be1 be2 : bool_expr, be_le be1 be2 -> be_le2 be1 be2.
Proof.
  unfold be_le, be_le2 in |- *.  intros.  unfold eval_be' in H.
  replace (bool_fun_of_bool_expr be2 ve) with
   (bool_fun_of_bool_expr be2 (var_env'_to_env (var_env_to_env' ve))).
  apply H.
  replace (bool_fun_of_bool_expr be1 (var_env'_to_env (var_env_to_env' ve)))
   with (bool_fun_of_bool_expr be1 ve).
  assumption.  apply (bool_fun_of_be_ext be1).
  unfold var_env'_to_env, var_env_to_env' in |- *.  intro.  rewrite (N_of_nat_of_N x).
  reflexivity.  apply (bool_fun_of_be_ext be2).  intro.
  unfold var_env'_to_env, var_env_to_env' in |- *.  rewrite (N_of_nat_of_N x).
  reflexivity.
Qed.

Lemma be_le2_le : forall be1 be2 : bool_expr, be_le2 be1 be2 -> be_le be1 be2.
Proof.
  unfold be_le, be_le2 in |- *.  unfold eval_be' in |- *.  intros.  apply H.  assumption.
Qed.

Lemma mu_all_le :
 forall t be1 be2 : bool_expr,
 be_le be1 be2 -> be_le (mu_all_eval t be1) (mu_all_eval t be2).
Proof.
  intros.  apply be_le2_le.  apply mu_all_le2.  apply be_le_le2.  assumption.
Qed.

Lemma mu_ex_le :
 forall t be1 be2 : bool_expr,
 be_le be1 be2 -> be_le (mu_ex_eval t be1) (mu_ex_eval t be2).
Proof.
  intros.  apply be_le2_le.  apply mu_ex_le2.  apply be_le_le2.  assumption.
Qed.

Lemma BDDmu_all_lemma :
 forall gc : BDDconfig -> list ad -> BDDconfig,
 gc_OK gc ->
 forall (cfg : BDDconfig) (ul : list ad) (nodet nodeg : ad),
 BDDconfig_OK cfg ->
 used_list_OK cfg ul ->
 used_node' cfg ul nodet ->
 used_node' cfg ul nodeg ->
 BDDconfig_OK (fst (BDDmu_all gc cfg ul nodet nodeg)) /\
 config_node_OK (fst (BDDmu_all gc cfg ul nodet nodeg))
   (snd (BDDmu_all gc cfg ul nodet nodeg)) /\
 used_nodes_preserved cfg (fst (BDDmu_all gc cfg ul nodet nodeg)) ul /\
 bool_fun_eq
   (bool_fun_of_BDD (fst (BDDmu_all gc cfg ul nodet nodeg))
      (snd (BDDmu_all gc cfg ul nodet nodeg)))
   (bool_fun_mu_all (bool_fun_of_BDD cfg nodet) (bool_fun_of_BDD cfg nodeg)).
Proof.
  intros.  unfold BDDmu_all in |- *.
  elim (prod_sum _ _ (BDDreplacel gc cfg ul nodeg lx lx')).
  intros cfgr H4; elim H4; clear H4; intros noder H4.  rewrite H4.
  elim (prod_sum _ _ (BDDimpl gc cfgr (noder :: ul) nodet noder)).
  intros cfgi H5; elim H5; clear H5; intros nodei H5.  rewrite H5.
  cut (BDDconfig_OK cfgr).  cut (config_node_OK cfgr noder).
  cut
   (bool_fun_eq (bool_fun_of_BDD cfgr noder)
      (bool_fun_replacel (bool_fun_of_BDD cfg nodeg) lx lx')).
  cut (used_nodes_preserved cfg cfgr ul).  intros.
  cut (used_list_OK cfgr (noder :: ul)).  intro.
  cut (used_node' cfgr (noder :: ul) noder).
  cut (used_node' cfgr (noder :: ul) nodet).  intros.
  cut (BDDconfig_OK cfgi).  cut (config_node_OK cfgi nodei).
  cut (used_nodes_preserved cfgr cfgi (noder :: ul)).
  cut
   (bool_fun_eq (bool_fun_of_BDD cfgi nodei)
      (bool_fun_impl (bool_fun_of_BDD cfgr nodet)
         (bool_fun_of_BDD cfgr noder))).
  intros.  cut (used_list_OK cfgi (nodei :: ul)).  intros.  split.
  apply BDDunivl_config_OK.  assumption.  assumption.  assumption.  
  apply used_node'_cons_node_ul.  split.  apply BDDunivl_node_OK.  assumption.  
  assumption.  assumption.  apply used_node'_cons_node_ul.  split.
  apply used_nodes_preserved_trans with (cfg2 := cfgr).  assumption.  assumption.  
  apply used_nodes_preserved_trans with (cfg2 := cfgi).  assumption.
  apply used_nodes_preserved_cons with (node := noder).  assumption.
  apply used_nodes_preserved_cons with (node := nodei).
  apply BDDunivl_used_nodes_preserved.  assumption.  assumption.  assumption.
  apply used_node'_cons_node_ul.  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_univl (bool_fun_of_BDD cfgi nodei) lx').
  apply BDDunivl_is_univl.  assumption.  assumption.  assumption.
  apply used_node'_cons_node_ul.  unfold bool_fun_mu_all in |- *.
  apply bool_fun_univl_preserves_eq.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_impl (bool_fun_of_BDD cfgr nodet)
                (bool_fun_of_BDD cfgr noder)).
  assumption.  apply bool_fun_impl_preserves_eq.
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  assumption.  
  assumption.  assumption.  assumption.  assumption.  apply node_OK_list_OK.
  assumption.  apply used_nodes_preserved_list_OK with (cfg := cfgr).
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.  assumption.  
  apply used_nodes_preserved_cons with (node := noder).  assumption.  
  replace cfgi with (fst (BDDimpl gc cfgr (noder :: ul) nodet noder)).
  replace nodei with (snd (BDDimpl gc cfgr (noder :: ul) nodet noder)).
  apply BDDimpl_is_impl; assumption.  rewrite H5; reflexivity.
  rewrite H5; reflexivity.  
  replace cfgi with (fst (BDDimpl gc cfgr (noder :: ul) nodet noder)).
  apply BDDimpl_used_nodes_preserved; assumption.  rewrite H5; reflexivity.
  replace cfgi with (fst (BDDimpl gc cfgr (noder :: ul) nodet noder)).
  replace nodei with (snd (BDDimpl gc cfgr (noder :: ul) nodet noder)).
  apply BDDimpl_node_OK; assumption.  rewrite H5; reflexivity.
  rewrite H5; reflexivity.
  replace cfgi with (fst (BDDimpl gc cfgr (noder :: ul) nodet noder)).
  apply BDDimpl_config_OK; assumption.  rewrite H5; reflexivity.  
  apply used_node'_cons_node'_ul.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.  assumption.
  assumption.  apply used_node'_cons_node_ul.  apply node_OK_list_OK.
  assumption.  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.
  assumption.  replace cfgr with (fst (BDDreplacel gc cfg ul nodeg lx lx')).
  apply BDDreplacel_used_nodes_preserved.  assumption.  intros.  assumption.  
  assumption.  assumption.  apply lx_neq_lx'.  rewrite H4; reflexivity.  
  replace cfgr with (fst (BDDreplacel gc cfg ul nodeg lx lx')).
  replace noder with (snd (BDDreplacel gc cfg ul nodeg lx lx')).
  apply BDDreplacel_is_replacel.  assumption.  intros.  assumption.  assumption.
  assumption.  apply lx_neq_lx'.  rewrite H4; reflexivity.
  rewrite H4; reflexivity.  
  replace cfgr with (fst (BDDreplacel gc cfg ul nodeg lx lx')).
  replace noder with (snd (BDDreplacel gc cfg ul nodeg lx lx')).
  apply BDDreplacel_node_OK.  assumption.  intros.  assumption.  assumption.  
  assumption.  apply lx_neq_lx'.  rewrite H4; reflexivity.
  rewrite H4; reflexivity.
  replace cfgr with (fst (BDDreplacel gc cfg ul nodeg lx lx')).
  apply BDDreplacel_config_OK.  assumption.  intros.  assumption.  assumption.  
  assumption.  apply lx_neq_lx'.  rewrite H4; reflexivity.  
Qed.

Section BDDmu_all_results.

Variable gc : BDDconfig -> list ad -> BDDconfig.
Hypothesis gc_is_OK : gc_OK gc.

Variable cfg : BDDconfig.
Variable ul : list ad.
Variable nodet nodeg : ad.

Hypothesis cfg_OK : BDDconfig_OK cfg.
Hypothesis ul_OK : used_list_OK cfg ul.
Hypothesis usedt : used_node' cfg ul nodet.
Hypothesis usedg : used_node' cfg ul nodeg.

Lemma BDDmu_all_config_OK :
 BDDconfig_OK (fst (BDDmu_all gc cfg ul nodet nodeg)).
Proof.
  exact
   (proj1
      (BDDmu_all_lemma gc gc_is_OK cfg ul nodet nodeg cfg_OK ul_OK usedt
         usedg)).
Qed.

Lemma BDDmu_all_node_OK :
 config_node_OK (fst (BDDmu_all gc cfg ul nodet nodeg))
   (snd (BDDmu_all gc cfg ul nodet nodeg)).
Proof.
  exact
   (proj1
      (proj2
         (BDDmu_all_lemma gc gc_is_OK cfg ul nodet nodeg cfg_OK ul_OK usedt
            usedg))).
Qed.

Lemma BDDmu_all_used_nodes_preserved :
 used_nodes_preserved cfg (fst (BDDmu_all gc cfg ul nodet nodeg)) ul.
Proof.
  exact
   (proj1
      (proj2
         (proj2
            (BDDmu_all_lemma gc gc_is_OK cfg ul nodet nodeg cfg_OK ul_OK
               usedt usedg)))).
Qed.

Lemma BDDmu_all_list_OK :
 used_list_OK (fst (BDDmu_all gc cfg ul nodet nodeg)) ul.
Proof.
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.
  exact BDDmu_all_used_nodes_preserved.
Qed.
Lemma BDDmu_all_list_OK_cons :
 used_list_OK (fst (BDDmu_all gc cfg ul nodet nodeg))
   (snd (BDDmu_all gc cfg ul nodet nodeg) :: ul).
Proof.
  apply node_OK_list_OK.  exact BDDmu_all_node_OK.  exact BDDmu_all_list_OK.
Qed.

Lemma BDDmu_all_is_mu_all :
 bool_fun_eq
   (bool_fun_of_BDD (fst (BDDmu_all gc cfg ul nodet nodeg))
      (snd (BDDmu_all gc cfg ul nodet nodeg)))
   (bool_fun_mu_all (bool_fun_of_BDD cfg nodet) (bool_fun_of_BDD cfg nodeg)).
Proof.
  exact
   (proj2
      (proj2
         (proj2
            (BDDmu_all_lemma gc gc_is_OK cfg ul nodet nodeg cfg_OK ul_OK
               usedt usedg)))).
Qed.

End BDDmu_all_results.


Lemma BDDmu_ex_lemma :
 forall gc : BDDconfig -> list ad -> BDDconfig,
 gc_OK gc ->
 forall (cfg : BDDconfig) (ul : list ad) (nodet nodeg : ad),
 BDDconfig_OK cfg ->
 used_list_OK cfg ul ->
 used_node' cfg ul nodet ->
 used_node' cfg ul nodeg ->
 BDDconfig_OK (fst (BDDmu_ex gc cfg ul nodet nodeg)) /\
 config_node_OK (fst (BDDmu_ex gc cfg ul nodet nodeg))
   (snd (BDDmu_ex gc cfg ul nodet nodeg)) /\
 used_nodes_preserved cfg (fst (BDDmu_ex gc cfg ul nodet nodeg)) ul /\
 bool_fun_eq
   (bool_fun_of_BDD (fst (BDDmu_ex gc cfg ul nodet nodeg))
      (snd (BDDmu_ex gc cfg ul nodet nodeg)))
   (bool_fun_mu_ex (bool_fun_of_BDD cfg nodet) (bool_fun_of_BDD cfg nodeg)).
Proof.
  intros.  unfold BDDmu_ex in |- *.
  elim (prod_sum _ _ (BDDreplacel gc cfg ul nodeg lx lx')).
  intros cfgr H4; elim H4; clear H4; intros noder H4.  rewrite H4.
  elim (prod_sum _ _ (BDDand gc cfgr (noder :: ul) nodet noder)).
  intros cfgi H5; elim H5; clear H5; intros nodei H5.  rewrite H5.
  cut (BDDconfig_OK cfgr).  cut (config_node_OK cfgr noder).
  cut
   (bool_fun_eq (bool_fun_of_BDD cfgr noder)
      (bool_fun_replacel (bool_fun_of_BDD cfg nodeg) lx lx')).
  cut (used_nodes_preserved cfg cfgr ul).  intros.
  cut (used_list_OK cfgr (noder :: ul)).  intro.
  cut (used_node' cfgr (noder :: ul) noder).
  cut (used_node' cfgr (noder :: ul) nodet).  intros.
  cut (BDDconfig_OK cfgi).  cut (config_node_OK cfgi nodei).
  cut (used_nodes_preserved cfgr cfgi (noder :: ul)).
  cut
   (bool_fun_eq (bool_fun_of_BDD cfgi nodei)
      (bool_fun_and (bool_fun_of_BDD cfgr nodet) (bool_fun_of_BDD cfgr noder))).
  intros.  cut (used_list_OK cfgi (nodei :: ul)).  intros.  split.
  apply BDDexl_config_OK.  assumption.  assumption.  assumption.  
  apply used_node'_cons_node_ul.  split.  apply BDDexl_node_OK.  assumption.  
  assumption.  assumption.  apply used_node'_cons_node_ul.  split.
  apply used_nodes_preserved_trans with (cfg2 := cfgr).  assumption.  assumption.  
  apply used_nodes_preserved_trans with (cfg2 := cfgi).  assumption.
  apply used_nodes_preserved_cons with (node := noder).  assumption.
  apply used_nodes_preserved_cons with (node := nodei).
  apply BDDexl_used_nodes_preserved.  assumption.  assumption.  assumption.
  apply used_node'_cons_node_ul.  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_exl (bool_fun_of_BDD cfgi nodei) lx').
  apply BDDexl_is_exl.  assumption.  assumption.  assumption.
  apply used_node'_cons_node_ul.  unfold bool_fun_mu_ex in |- *.
  apply bool_fun_exl_preserves_eq.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_and (bool_fun_of_BDD cfgr nodet)
                (bool_fun_of_BDD cfgr noder)).
  assumption.  apply bool_fun_and_preserves_eq.
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  assumption.  
  assumption.  assumption.  assumption.  assumption.  apply node_OK_list_OK.
  assumption.  apply used_nodes_preserved_list_OK with (cfg := cfgr).
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.  assumption.  
  apply used_nodes_preserved_cons with (node := noder).  assumption.  
  replace cfgi with (fst (BDDand gc cfgr (noder :: ul) nodet noder)).
  replace nodei with (snd (BDDand gc cfgr (noder :: ul) nodet noder)).
  apply BDDand_is_and; assumption.  rewrite H5; reflexivity.
  rewrite H5; reflexivity.  
  replace cfgi with (fst (BDDand gc cfgr (noder :: ul) nodet noder)).
  apply BDDand_used_nodes_preserved; assumption.  rewrite H5; reflexivity.
  replace cfgi with (fst (BDDand gc cfgr (noder :: ul) nodet noder)).
  replace nodei with (snd (BDDand gc cfgr (noder :: ul) nodet noder)).
  apply BDDand_node_OK; assumption.  rewrite H5; reflexivity.
  rewrite H5; reflexivity.
  replace cfgi with (fst (BDDand gc cfgr (noder :: ul) nodet noder)).
  apply BDDand_config_OK; assumption.  rewrite H5; reflexivity.  
  apply used_node'_cons_node'_ul.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.  assumption.
  assumption.  apply used_node'_cons_node_ul.  apply node_OK_list_OK.
  assumption.  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.
  assumption.  replace cfgr with (fst (BDDreplacel gc cfg ul nodeg lx lx')).
  apply BDDreplacel_used_nodes_preserved.  assumption.  intros.  assumption.  
  assumption.  assumption.  apply lx_neq_lx'.  rewrite H4; reflexivity.  
  replace cfgr with (fst (BDDreplacel gc cfg ul nodeg lx lx')).
  replace noder with (snd (BDDreplacel gc cfg ul nodeg lx lx')).
  apply BDDreplacel_is_replacel.  assumption.  intros.  assumption.  assumption.
  assumption.  apply lx_neq_lx'.  rewrite H4; reflexivity.
  rewrite H4; reflexivity.  
  replace cfgr with (fst (BDDreplacel gc cfg ul nodeg lx lx')).
  replace noder with (snd (BDDreplacel gc cfg ul nodeg lx lx')).
  apply BDDreplacel_node_OK.  assumption.  intros.  assumption.  assumption.  
  assumption.  apply lx_neq_lx'.  rewrite H4; reflexivity.
  rewrite H4; reflexivity.
  replace cfgr with (fst (BDDreplacel gc cfg ul nodeg lx lx')).
  apply BDDreplacel_config_OK.  assumption.  intros.  assumption.  assumption.  
  assumption.  apply lx_neq_lx'.  rewrite H4; reflexivity.  
Qed.

Section BDDmu_ex_results.

Variable gc : BDDconfig -> list ad -> BDDconfig.
Hypothesis gc_is_OK : gc_OK gc.

Variable cfg : BDDconfig.
Variable ul : list ad.
Variable nodet nodeg : ad.

Hypothesis cfg_OK : BDDconfig_OK cfg.
Hypothesis ul_OK : used_list_OK cfg ul.
Hypothesis usedt : used_node' cfg ul nodet.
Hypothesis usedg : used_node' cfg ul nodeg.

Lemma BDDmu_ex_config_OK :
 BDDconfig_OK (fst (BDDmu_ex gc cfg ul nodet nodeg)).
Proof.
  exact
   (proj1
      (BDDmu_ex_lemma gc gc_is_OK cfg ul nodet nodeg cfg_OK ul_OK usedt usedg)).
Qed.

Lemma BDDmu_ex_node_OK :
 config_node_OK (fst (BDDmu_ex gc cfg ul nodet nodeg))
   (snd (BDDmu_ex gc cfg ul nodet nodeg)).
Proof.
  exact
   (proj1
      (proj2
         (BDDmu_ex_lemma gc gc_is_OK cfg ul nodet nodeg cfg_OK ul_OK usedt
            usedg))).
Qed.

Lemma BDDmu_ex_used_nodes_preserved :
 used_nodes_preserved cfg (fst (BDDmu_ex gc cfg ul nodet nodeg)) ul.
Proof.
  exact
   (proj1
      (proj2
         (proj2
            (BDDmu_ex_lemma gc gc_is_OK cfg ul nodet nodeg cfg_OK ul_OK usedt
               usedg)))).
Qed.

Lemma BDDmu_ex_list_OK :
 used_list_OK (fst (BDDmu_ex gc cfg ul nodet nodeg)) ul.
Proof.
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.
  exact BDDmu_ex_used_nodes_preserved.
Qed.
Lemma BDDmu_ex_list_OK_cons :
 used_list_OK (fst (BDDmu_ex gc cfg ul nodet nodeg))
   (snd (BDDmu_ex gc cfg ul nodet nodeg) :: ul).
Proof.
  apply node_OK_list_OK.  exact BDDmu_ex_node_OK.  exact BDDmu_ex_list_OK.
Qed.

Lemma BDDmu_ex_is_mu_ex :
 bool_fun_eq
   (bool_fun_of_BDD (fst (BDDmu_ex gc cfg ul nodet nodeg))
      (snd (BDDmu_ex gc cfg ul nodet nodeg)))
   (bool_fun_mu_ex (bool_fun_of_BDD cfg nodet) (bool_fun_of_BDD cfg nodeg)).
Proof.
  exact
   (proj2
      (proj2
         (proj2
            (BDDmu_ex_lemma gc gc_is_OK cfg ul nodet nodeg cfg_OK ul_OK usedt
               usedg)))).
Qed.

End BDDmu_ex_results.
End Nsec.

Section Be_ok.

Variable vf : ad -> bool.

Inductive be_ok : bool_expr -> Prop :=
  | zero_ok : be_ok Zero
  | one_ok : be_ok One
  | var_ok : forall x : BDDvar, vf x = true -> be_ok (Var x)
  | neg_ok : forall be : bool_expr, be_ok be -> be_ok (Neg be)
  | or_ok :
      forall be1 be2 : bool_expr,
      be_ok be1 -> be_ok be2 -> be_ok (Or be1 be2)
  | and_ok :
      forall be1 be2 : bool_expr,
      be_ok be1 -> be_ok be2 -> be_ok (ANd be1 be2)
  | impl_ok :
      forall be1 be2 : bool_expr,
      be_ok be1 -> be_ok be2 -> be_ok (Impl be1 be2)
  | iff_ok :
      forall be1 be2 : bool_expr,
      be_ok be1 -> be_ok be2 -> be_ok (Iff be1 be2).

Lemma var_ok_inv : forall x : BDDvar, be_ok (Var x) -> vf x = true.
Proof.
  intros.  inversion H.  assumption.
Qed.

Lemma neg_ok_inv : forall be : bool_expr, be_ok (Neg be) -> be_ok be.
Proof.
  intros.  inversion H.  assumption.
Qed.

Lemma or_ok_inv :
 forall be1 be2 : bool_expr, be_ok (Or be1 be2) -> be_ok be1 /\ be_ok be2.
Proof.
  intros.  inversion H.  auto.
Qed.

Lemma and_ok_inv :
 forall be1 be2 : bool_expr, be_ok (ANd be1 be2) -> be_ok be1 /\ be_ok be2.
Proof.
  intros.  inversion H.  auto.
Qed.
Lemma impl_ok_inv :
 forall be1 be2 : bool_expr, be_ok (Impl be1 be2) -> be_ok be1 /\ be_ok be2.
Proof.
  intros.  inversion H.  auto.
Qed.

Lemma iff_ok_inv :
 forall be1 be2 : bool_expr, be_ok (Iff be1 be2) -> be_ok be1 /\ be_ok be2.
Proof.
  intros.  inversion H.  auto.
Qed.

Lemma be_x_free_be_ok :
 forall be : bool_expr,
 (forall x : BDDvar, be_x_free x be = true -> vf x = true) -> be_ok be.
Proof.
  simple induction be.  intros.  apply zero_ok.  intros.  apply one_ok.  simpl in |- *.
  intros.  apply var_ok.  apply H.  apply Neqb_correct.  simpl in |- *.  intros.
  apply neg_ok.  apply H.  assumption.  simpl in |- *.  intros.  apply or_ok.  apply H.
  intros.  apply H1.  rewrite H2.  reflexivity.  apply H0.  intros.  apply H1.
  rewrite H2.  elim (be_x_free x b); reflexivity.  simpl in |- *.  intros.
  apply and_ok.  apply H.  intros.  apply H1.  rewrite H2.  reflexivity.
  apply H0.  intros.  apply H1.  rewrite H2.  elim (be_x_free x b); reflexivity.
  simpl in |- *.  intros.  apply impl_ok.  apply H.  intros.  apply H1.  rewrite H2.
  reflexivity.  apply H0.  intros.  apply H1.  rewrite H2.
  elim (be_x_free x b); reflexivity.  simpl in |- *.  intros.  apply iff_ok.  apply H.
  intros.  apply H1.  rewrite H2.  reflexivity.  apply H0.  intros.  apply H1.
  rewrite H2.  elim (be_x_free x b); reflexivity.
Qed.

Lemma be_ok_be_x_free :
 forall be : bool_expr,
 be_ok be -> forall x : BDDvar, be_x_free x be = true -> vf x = true.
Proof.
  simple induction be.  simpl in |- *.  intros.  discriminate.  simpl in |- *.  intros.  discriminate.
  simpl in |- *.  intros.  rewrite (Neqb_complete _ _ H0).  inversion H.  assumption.
  simpl in |- *.  intros.  inversion H0.  apply H.  assumption.  assumption.  simpl in |- *.
  intros.  inversion H1.  elim (orb_prop _ _ H2).  intro.  apply H.  assumption.
  assumption.  intro.  apply H0.  assumption.  assumption.  simpl in |- *.  intros.
  inversion H1.  elim (orb_prop _ _ H2).  intro.  apply H.  assumption.
  assumption.  intro.  apply H0.  assumption.  assumption.  simpl in |- *.  intros.
  inversion H1.  elim (orb_prop _ _ H2).  intro.  apply H.  assumption.
  assumption.  intro.  apply H0.  assumption.  assumption.  simpl in |- *.  intros.
  inversion H1.  elim (orb_prop _ _ H2).  intro.  apply H.  assumption.
  assumption.  intro.  apply H0.  assumption.  assumption.
Qed.

End Be_ok.
