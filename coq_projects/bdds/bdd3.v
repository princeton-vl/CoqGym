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

Lemma bool_fun_one_zero_eq : ~ bool_fun_eq bool_fun_one bool_fun_zero.
Proof.
  unfold bool_fun_eq, bool_fun_zero, bool_fun_one in |- *.  unfold not in |- *.  intro H.  unfold bool_fun_eval in H.
  cut (true = false).  intro; discriminate.  apply H.  exact (fun x : BDDvar => true).
Qed.

Lemma bool_fun_zero_one_eq : ~ bool_fun_eq bool_fun_zero bool_fun_one.
Proof.
  unfold bool_fun_eq, bool_fun_zero, bool_fun_one in |- *.  unfold not in |- *.  intro H.  unfold bool_fun_eval in H.
  cut (false = true).  intro; discriminate.  apply H.  exact (fun x : BDDvar => true).
Qed.

Definition augment (vb : var_binding) (x : BDDvar) 
  (b : bool) (y : BDDvar) := if BDDvar_eq x y then b else vb y.

Definition bool_fun_restrict (bf : bool_fun) (x : BDDvar) 
  (b : bool) (vb : var_binding) := bool_fun_eval bf (augment vb x b).

Lemma bool_fun_restrict_zero :
 forall (x : BDDvar) (b : bool),
 bool_fun_eq (bool_fun_restrict bool_fun_zero x b) bool_fun_zero. 
Proof.
  intros x b.  unfold bool_fun_eq, bool_fun_restrict, bool_fun_zero, bool_fun_one in |- *.
  intros vb.  unfold bool_fun_eval, augment in |- *.  reflexivity.
Qed.

Lemma bool_fun_restrict_one :
 forall (x : BDDvar) (b : bool),
 bool_fun_eq (bool_fun_restrict bool_fun_one x b) bool_fun_one.
Proof.
  intros x b.  unfold bool_fun_eq, bool_fun_restrict, bool_fun_zero, bool_fun_one in |- *.
  intros vb.  unfold bool_fun_eval, augment in |- *.  reflexivity.
Qed.

Lemma bool_fun_restrict_eq :
 forall (bf bf' : bool_fun) (x : BDDvar) (b : bool),
 bool_fun_eq bf bf' ->
 bool_fun_eq (bool_fun_restrict bf x b) (bool_fun_restrict bf' x b).
Proof.
  intros bf bf' x b H.  unfold bool_fun_eq in |- *.  unfold bool_fun_restrict in |- *.  unfold bool_fun_eval at 1 3 in |- *.
  intro vb.  apply H.
Qed.

Definition var_binding_eq (vb vb' : var_binding) :=
  forall x : BDDvar, vb x = vb' x.

Definition bool_fun_ext (bf : bool_fun) :=
  forall vb vb' : var_binding,
  var_binding_eq vb vb' -> bool_fun_eval bf vb = bool_fun_eval bf vb'.

Lemma bool_fun_of_BDD_1_ext :
 forall (bound : nat) (cfg : BDDconfig) (node : ad),
 bool_fun_ext (bool_fun_of_BDD_1 cfg node bound). 
Proof.
  simple induction bound.  intro cfg.  elim cfg.  clear cfg.  intros bs y.  elim y.  clear y.
  intros share counter.  intros node.  simpl in |- *.  elim (MapGet (BDDvar * (ad * ad)) bs node). Focus 2.
  elim (Neqb node BDDzero).  unfold bool_fun_ext in |- *.  unfold bool_fun_eval, bool_fun_zero in |- *; reflexivity.
  unfold bool_fun_ext in |- *.  unfold bool_fun_eval, bool_fun_one in |- *; reflexivity.
  unfold bool_fun_ext in |- *.  unfold bool_fun_eval in |- *.  unfold bool_fun_zero in |- *.  intro a.
  intro vb.  intro vb'.  intro H.  elim a.  intros y y0.  elim y0.  reflexivity. intro n.
  intro H.  intro cfg.  elim cfg.  clear cfg.  intros bs y.  elim y.  clear y.  intros share counter.
  intros node.  simpl in |- *.  elim (MapGet (BDDvar * (ad * ad)) bs node).  Focus 2. elim (Neqb node BDDzero).
  unfold bool_fun_ext, bool_fun_zero in |- *.  unfold bool_fun_eval in |- *; reflexivity.  
  unfold bool_fun_ext, bool_fun_one in |- *.  unfold bool_fun_eval in |- *; reflexivity.  intros a.
  elim a.  intros y y0.  elim y0. intros y1 y2.  cut (bool_fun_ext (bool_fun_of_BDD_1 (bs, (share, counter)) y2 n)).
  intro H0.  cut (bool_fun_ext (bool_fun_of_BDD_1 (bs, (share, counter)) y1 n)).  intro H1.
  unfold bool_fun_ext in |- *.  intros vb vb' H2.  unfold bool_fun_eval in |- *.  unfold bool_fun_ext in H0, H1.
  unfold bool_fun_eval in H0, H1.  rewrite (H1 vb vb' H2).  rewrite (H0 vb vb' H2).
  unfold var_binding_eq in H2.  rewrite (H2 y).  reflexivity.  apply H.  apply H.
Qed.

Lemma bool_fun_of_BDD_ext :
 forall (cfg : BDDconfig) (node : ad),
 bool_fun_ext (bool_fun_of_BDD cfg node).
Proof.
  unfold bool_fun_of_BDD in |- *.  intros cfg node.  apply bool_fun_of_BDD_1_ext.
Qed.

Lemma augment_eq :
 forall (vb : var_binding) (x : BDDvar) (b : bool),
 vb x = b -> var_binding_eq (augment vb x b) vb.
Proof.
  unfold var_binding_eq in |- *.  intros vb x b H x0.  unfold augment in |- *.  elim (sumbool_of_bool (BDDvar_eq x x0)).
  intro y.  rewrite y.  cut (x = x0).  intro H0.  rewrite <- H0.  rewrite H; reflexivity.
  apply Neqb_complete.  exact y.  intro y.  rewrite y.  reflexivity.
Qed.

Definition bool_fun_independent (bf : bool_fun) (x : BDDvar) :=
  forall vb : var_binding,
  bool_fun_eval bf (augment vb x true) =
  bool_fun_eval bf (augment vb x false).

Lemma bool_fun_independent_lemma :
 forall (bf : bool_fun) (x : BDDvar) (vb : var_binding) (b : bool),
 bool_fun_ext bf ->
 bool_fun_independent bf x ->
 bool_fun_eval bf (augment vb x b) = bool_fun_eval bf vb. 
Proof.
  intros bf x vb b H H0.  elim (sumbool_of_bool (vb x)).  intro y.  elim b.  cut (var_binding_eq (augment vb x true) vb).
  intro H1.  rewrite (H (augment vb x true) vb H1).  cut (bool_fun_eval bf (augment vb x true) = bool_fun_eval bf vb).
  unfold bool_fun_eval in |- *.  intro H2.  reflexivity.  rewrite (H (augment vb x true) vb H1).
  reflexivity.  apply augment_eq.  assumption.  rewrite <- (H0 vb).  cut (var_binding_eq (augment vb x true) vb).
  intro H1.  rewrite (H (augment vb x true) vb H1).  cut (bool_fun_eval bf (augment vb x true) = bool_fun_eval bf vb).
  unfold bool_fun_eval in |- *.  intro H2.  reflexivity.  rewrite (H (augment vb x true) vb H1).
  reflexivity.  apply augment_eq.  assumption.  intro y.  elim b.  cut (var_binding_eq (augment vb x false) vb).
  intro H1.  cut (bool_fun_eval bf (augment vb x false) = bool_fun_eval bf vb).
  intro H2.  rewrite <- H2.  apply H0.  apply H.  assumption.  apply augment_eq.
  assumption.  cut (var_binding_eq (augment vb x false) vb).  intro H1.  apply H.
  assumption.  apply augment_eq.  assumption.
Qed.

Lemma bool_fun_independent_zero :
 forall (cfg : BDDconfig) (x : BDDvar),
 BDDconfig_OK cfg -> bool_fun_independent (bool_fun_of_BDD cfg BDDzero) x.
Proof.
  intro cfg.  elim cfg; clear cfg; intros bs y.  elim y; clear y; intros share counter.
  intros x H.  rewrite (proj1 (bool_fun_of_BDD_semantics (bs, (share, counter)) H)).
  unfold bool_fun_independent in |- *.  intro vb.  unfold bool_fun_eval, bool_fun_zero in |- *.  reflexivity.
Qed.

Lemma bool_fun_independent_one :
 forall (cfg : BDDconfig) (x : BDDvar),
 BDDconfig_OK cfg -> bool_fun_independent (bool_fun_of_BDD cfg BDDone) x.
Proof.
  intro cfg.  elim cfg; clear cfg; intros bs y.  elim y; clear y; intros share counter.
  intros x H.  rewrite
   (proj1 (proj2 (bool_fun_of_BDD_semantics (bs, (share, counter)) H)))
   .
  unfold bool_fun_independent in |- *.  intro vb.  unfold bool_fun_eval, bool_fun_one in |- *.  reflexivity.
Qed.

Lemma in_dom_is_internal :
 forall (cfg : BDDconfig) (node : ad),
 in_dom _ node (fst cfg) = true -> is_internal_node cfg node.
Proof.
  intro cfg.  elim cfg; clear cfg; intros bs y.  elim y; clear y; intros share counter.
  intros node H.  elim (option_sum _ (MapGet _ (fst (bs, (share, counter))) node)).  intros y.
  elim y. intro x.  elim x. intro y0. intro y1.  elim y1. intros y2 y3 y4.  split with y0; split with y2; split with y3; assumption.
  intro y.  unfold in_dom in H.  rewrite y in H.  discriminate H.
Qed.

Lemma internal_node_lemma :
 forall (cfg : BDDconfig) (node : ad),
 BDDconfig_OK cfg ->
 is_internal_node cfg node ->
 Neqb (low cfg node) (high cfg node) = false /\
 BDDbounded (fst cfg) (low cfg node) (var cfg node) /\
 BDDbounded (fst cfg) (high cfg node) (var cfg node).
Proof.
  intro cfg.  elim cfg; clear cfg; intros bs y.  elim y; clear y; intros share counter.
  intros node H H0.  elim H.  intros H1 H2.  elim H1.  intros H3 H4.  inversion H0.  inversion H5.
  inversion H6.  cut (BDD_OK bs node).  unfold BDD_OK in |- *.  unfold BDDordered in |- *.  simpl in H7; rewrite H7.
  intro H8.  unfold var, high, low in |- *.  simpl in |- *.  rewrite H7.  cut
   (node = BDDzero \/
    node = BDDone \/
    (exists x' : BDDvar,
       (exists l' : BDDvar,
          (exists r' : BDDvar,
             MapGet _ bs node = Some (x', (l', r')) /\
             BDDcompare x' (ad_S x) = Datatypes.Lt /\
             Neqb l' r' = false /\
             BDDbounded bs l' x' /\ BDDbounded bs r' x')))).
  intros H9.  elim H9; intros.  rewrite H10 in H7; rewrite H3 in H7; discriminate.  
  elim H10; intros.  rewrite H11 in H7; rewrite (proj1 H4) in H7; discriminate.
  inversion H11.  inversion H12.  inversion H13.  inversion H14.  rewrite H7 in H15.
  injection H15.  intros H17 H18 H19.  rewrite <- H17 in H16.  rewrite <- H18 in H16.  rewrite <- H19 in H16.
  exact (proj2 H16).  apply BDDbounded_lemma.  assumption.  apply (proj2 H4).
  unfold in_dom in |- *; simpl in H7; rewrite H7; reflexivity.
Qed.

Lemma high_bounded :
 forall (cfg : BDDconfig) (node : ad),
 BDDconfig_OK cfg ->
 is_internal_node cfg node ->
 BDDbounded (fst cfg) (high cfg node) (var cfg node).
Proof.
intros cfg node H H0.  exact (proj2 (proj2 (internal_node_lemma cfg node H H0))).
Qed.

Lemma low_bounded :
 forall (cfg : BDDconfig) (node : ad),
 BDDconfig_OK cfg ->
 is_internal_node cfg node ->
 BDDbounded (fst cfg) (low cfg node) (var cfg node).
Proof.
intros cfg node H H0.  exact (proj1 (proj2 (internal_node_lemma cfg node H H0))).
Qed.

Lemma high_OK :
 forall (cfg : BDDconfig) (node : ad),
 BDDconfig_OK cfg ->
 is_internal_node cfg node -> config_node_OK cfg (high cfg node).
Proof.
  intro cfg.  elim cfg; clear cfg; intros bs y.  elim y; clear y; intros share counter.
  intros node H H0.  inversion H0.  inversion H1.  inversion H2.  unfold high in |- *.  rewrite H3.
  cut
   (BDDbounded (fst (bs, (share, counter)))
      (high (bs, (share, counter)) node) (var (bs, (share, counter)) node)).
  unfold var, high in |- *.  rewrite H3.  intro H4.  unfold config_node_OK in |- *.  apply BDDbounded_node_OK with (n := x).
  assumption.  apply high_bounded.  assumption.  assumption.  
Qed.

Lemma low_OK :
 forall (cfg : BDDconfig) (node : ad),
 BDDconfig_OK cfg ->
 is_internal_node cfg node -> config_node_OK cfg (low cfg node).
Proof.
  intro cfg.  elim cfg; clear cfg; intros bs y.  elim y; clear y; intros share counter.
  intros node H H0.  inversion H0.  inversion H1.  inversion H2.  unfold low in |- *.  rewrite H3.
  cut
   (BDDbounded (fst (bs, (share, counter))) (low (bs, (share, counter)) node)
      (var (bs, (share, counter)) node)).
  unfold var, low in |- *.  rewrite H3.  intro H4.  unfold config_node_OK in |- *.  apply BDDbounded_node_OK with (n := x).
  assumption.  apply low_bounded.  assumption.  assumption.
Qed.

Lemma low_high_neq :
 forall (cfg : BDDconfig) (node : ad),
 BDDconfig_OK cfg ->
 is_internal_node cfg node -> Neqb (low cfg node) (high cfg node) = false.
Proof.
  intros cfg node H H0.  exact (proj1 (internal_node_lemma cfg node H H0)).
Qed.

Lemma BDDvar_independent_1 :
 forall (cfg : BDDconfig) (n : nat) (node : ad) (x : BDDvar),
 BDDconfig_OK cfg ->
 is_internal_node cfg node ->
 n = nat_of_N (var cfg node) ->
 BDDcompare (var cfg node) x = Datatypes.Lt ->
 bool_fun_independent (bool_fun_of_BDD cfg node) x.
Proof.
  intro cfg.  elim cfg; clear cfg; intros bs y.  elim y; clear y; intros share counter.
  intro n.  apply
   lt_wf_ind
    with
      (P := fun n : nat =>
            forall (node : ad) (x : BDDvar),
            BDDconfig_OK (bs, (share, counter)) ->
            is_internal_node (bs, (share, counter)) node ->
            n = nat_of_N (var (bs, (share, counter)) node) ->
            BDDcompare (var (bs, (share, counter)) node) x = Datatypes.Lt ->
            bool_fun_independent
              (bool_fun_of_BDD (bs, (share, counter)) node) x).
  intros n0 H node x H0 H1 H2 H3.  cut
   (bool_fun_independent
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node)) x).
  cut
   (bool_fun_independent
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node)) x).
  intros H4 H5.  rewrite
   (proj2 (proj2 (bool_fun_of_BDD_semantics (bs, (share, counter)) H0)) node
      H1).
  unfold bool_fun_independent in |- *.  unfold bool_fun_eval in |- *.  intro vb.  unfold bool_fun_independent in H4, H5.
  unfold bool_fun_eval in H4, H5.  inversion H1.  inversion H6.  inversion H7.
  unfold var, high, low in |- *.  rewrite H8.  unfold augment at 1 4 in |- *.  cut (BDDvar_eq x x0 = false).
  intro H9.  rewrite H9.  unfold var, high, low in H5, H4.  rewrite H8 in H4.  rewrite H8 in H5.
  rewrite (H4 vb).  rewrite (H5 vb).  reflexivity.  unfold BDDvar_eq in |- *.  cut (Neqb x x0 <> true).
  elim (Neqb x x0).  intro H9.  absurd (true = true).  assumption.  reflexivity.  reflexivity.
  unfold not in |- *.  intro H9.  unfold var in H3.  rewrite H8 in H3.  cut (nat_of_N x0 < nat_of_N x).
  cut (x = x0).  intro H10.  rewrite H10.  exact (lt_irrefl (nat_of_N x0)).  apply Neqb_complete.
  assumption.  apply BDDcompare_lt.  assumption.  cut (node_OK bs (high (bs, (share, counter)) node)).
  intro H4.  elim H4.  intro H5.  rewrite H5.  apply bool_fun_independent_zero.  assumption.
  intro H5.  elim H5; intro H6.  rewrite H6.  apply bool_fun_independent_one.  assumption.
  apply
   H
    with
      (m := nat_of_N
              (var (bs, (share, counter)) (high (bs, (share, counter)) node))).
  rewrite H2.  apply BDDcompare_lt.  apply BDDvar_ordered_high.  assumption.  
  assumption.  unfold is_internal_node in |- *.  elim
   (option_sum _
      (MapGet (BDDvar * (ad * ad)) (fst (bs, (share, counter)))
         (high (bs, (share, counter)) node))).
  intro y.  elim y.  intro x0.  elim x0. intro y0. intro y1.  elim y1. intro y2. intro y3.
  split with y0.  split with y2.  split with y3.  assumption.  intro y.  unfold in_dom in H6.
  simpl in y.  rewrite y in H6.  discriminate H6.  assumption.  apply in_dom_is_internal.
  assumption.  reflexivity.  apply BDDcompare_trans with (y := var (bs, (share, counter)) node).
  apply BDDvar_ordered_high.  assumption.  assumption.  apply in_dom_is_internal.
  assumption.  assumption.  exact (high_OK (bs, (share, counter)) node H0 H1).
  cut (node_OK bs (low (bs, (share, counter)) node)).  intro H4.  elim H4.  intro H5.
  rewrite H5.  apply bool_fun_independent_zero.  assumption.  intro H5.  elim H5; intro H6.
  rewrite H6.  apply bool_fun_independent_one.  assumption.  apply
   H
    with
      (m := nat_of_N
              (var (bs, (share, counter)) (low (bs, (share, counter)) node))).
  rewrite H2.  apply BDDcompare_lt.  apply BDDvar_ordered_low.  assumption.
  assumption.  apply in_dom_is_internal.  assumption.  assumption.  apply in_dom_is_internal.
  assumption.  reflexivity.  apply BDDcompare_trans with (y := var (bs, (share, counter)) node).
  apply BDDvar_ordered_low.  assumption.  assumption.  apply in_dom_is_internal.
  assumption.  assumption.  exact (low_OK (bs, (share, counter)) node H0 H1).
Qed.

Lemma BDDvar_independent_high :
 forall (cfg : BDDconfig) (node : ad),
 BDDconfig_OK cfg ->
 is_internal_node cfg node ->
 bool_fun_independent (bool_fun_of_BDD cfg (high cfg node)) (var cfg node).
Proof.
  intros cfg node H H0.  cut (config_node_OK cfg (high cfg node)).  intros H1.  elim H1.  intro H2.
  rewrite H2.  apply bool_fun_independent_zero.  assumption.  intro H2.  elim H2; intro.
  rewrite H3; apply bool_fun_independent_one; assumption.  cut (is_internal_node cfg (high cfg node)).
  intro H4.  apply BDDvar_independent_1 with (n := nat_of_N (var cfg (high cfg node))).
  assumption.  apply in_dom_is_internal.  assumption.  reflexivity.  apply BDDvar_ordered_high.
  assumption.  assumption.  assumption.  apply in_dom_is_internal.  assumption.
  apply high_OK.  assumption.  assumption.
Qed.

Lemma BDDvar_independent_low :
 forall (cfg : BDDconfig) (node : ad),
 BDDconfig_OK cfg ->
 is_internal_node cfg node ->
 bool_fun_independent (bool_fun_of_BDD cfg (low cfg node)) (var cfg node).
Proof.
  intros cfg node H H0.  cut (config_node_OK cfg (low cfg node)).  intros H1.  elim H1.  intro H2.
  rewrite H2.  apply bool_fun_independent_zero.  assumption.  intro H2.  elim H2; intro.
  rewrite H3; apply bool_fun_independent_one; assumption.  cut (is_internal_node cfg (low cfg node)).
  intro H4.  apply BDDvar_independent_1 with (n := nat_of_N (var cfg (low cfg node))).
  assumption.  apply in_dom_is_internal.  assumption.  reflexivity.  apply BDDvar_ordered_low.
  assumption.  assumption.  assumption.  apply in_dom_is_internal.  assumption.
  apply low_OK.  assumption.  assumption.
Qed.

Lemma bool_fun_of_BDDzero :
 forall cfg : BDDconfig,
 BDDconfig_OK cfg -> bool_fun_eq (bool_fun_of_BDD cfg BDDzero) bool_fun_zero.
Proof.
  intros cfg H.  unfold bool_fun_eq in |- *.  unfold bool_fun_eval in |- *.  intro vb.
  rewrite (proj1 (bool_fun_of_BDD_semantics cfg H)).  reflexivity.
Qed.

Lemma bool_fun_of_BDDone :
 forall cfg : BDDconfig,
 BDDconfig_OK cfg -> bool_fun_eq (bool_fun_of_BDD cfg BDDone) bool_fun_one.
Proof.
  intros cfg H.  unfold bool_fun_eq in |- *.  unfold bool_fun_eval in |- *.  intro vb.
  rewrite (proj1 (proj2 (bool_fun_of_BDD_semantics cfg H))).  reflexivity.
Qed.

Lemma bool_fun_of_BDDhigh :
 forall (cfg : BDDconfig) (node : ad),
 BDDconfig_OK cfg ->
 is_internal_node cfg node ->
 bool_fun_eq (bool_fun_of_BDD cfg (high cfg node))
   (bool_fun_restrict (bool_fun_of_BDD cfg node) (var cfg node) true).
Proof.
  intro cfg.  elim cfg; clear cfg; intros bs y.  elim y; clear y; intros share counter.
  intros node H H0.  rewrite
   (proj2 (proj2 (bool_fun_of_BDD_semantics (bs, (share, counter)) H)) node
      H0).
  unfold bool_fun_restrict in |- *.  unfold bool_fun_eval in |- *.  unfold bool_fun_eq in |- *.  unfold bool_fun_eval in |- *.
  unfold augment at 1 in |- *.  unfold BDDvar_eq in |- *.  cut
   (Neqb (var (bs, (share, counter)) node) (var (bs, (share, counter)) node) =
    true).
  intro H1.  rewrite H1.  intro vb.  cut
   (bool_fun_of_BDD (bs, (share, counter)) (high (bs, (share, counter)) node)
      (augment vb (var (bs, (share, counter)) node) true) =
    bool_fun_of_BDD (bs, (share, counter)) (high (bs, (share, counter)) node)
      vb).
  intro H2.  rewrite H2.  reflexivity.  change
    (bool_fun_eval
       (bool_fun_of_BDD (bs, (share, counter))
          (high (bs, (share, counter)) node))
       (augment vb (var (bs, (share, counter)) node) true) =
     bool_fun_eval
       (bool_fun_of_BDD (bs, (share, counter))
          (high (bs, (share, counter)) node)) vb) in |- *.
  apply bool_fun_independent_lemma.  apply bool_fun_of_BDD_ext.  apply BDDvar_independent_high.
  assumption.  assumption.  apply Neqb_correct.
Qed.

Lemma bool_fun_of_BDDlow :
 forall (cfg : BDDconfig) (node : ad),
 BDDconfig_OK cfg ->
 is_internal_node cfg node ->
 bool_fun_eq (bool_fun_of_BDD cfg (low cfg node))
   (bool_fun_restrict (bool_fun_of_BDD cfg node) (var cfg node) false).
Proof.
  intro cfg.  elim cfg; clear cfg; intros bs y.  elim y; clear y; intros share counter.
  intros node H H0.  rewrite
   (proj2 (proj2 (bool_fun_of_BDD_semantics (bs, (share, counter)) H)) node
      H0).
  unfold bool_fun_restrict in |- *.  unfold bool_fun_eval in |- *.  unfold bool_fun_eq in |- *.  unfold bool_fun_eval in |- *.
  unfold augment at 1 in |- *.  unfold BDDvar_eq in |- *.  cut
   (Neqb (var (bs, (share, counter)) node) (var (bs, (share, counter)) node) =
    true).
  intro H1.  rewrite H1.  intro vb.  cut
   (bool_fun_of_BDD (bs, (share, counter)) (low (bs, (share, counter)) node)
      (augment vb (var (bs, (share, counter)) node) false) =
    bool_fun_of_BDD (bs, (share, counter)) (low (bs, (share, counter)) node)
      vb).
  intro H2.  rewrite H2.  reflexivity.  change
    (bool_fun_eval
       (bool_fun_of_BDD (bs, (share, counter))
          (low (bs, (share, counter)) node))
       (augment vb (var (bs, (share, counter)) node) false) =
     bool_fun_eval
       (bool_fun_of_BDD (bs, (share, counter))
          (low (bs, (share, counter)) node)) vb) in |- *.
  apply bool_fun_independent_lemma.  apply bool_fun_of_BDD_ext.  apply BDDvar_independent_low.
  assumption.  assumption.  apply Neqb_correct.
Qed.

Lemma internal_node_not_constant_1 :
 forall cfg : BDDconfig,
 BDDconfig_OK cfg ->
 forall (n : nat) (node : ad),
 is_internal_node cfg node ->
 n = nat_of_N (var cfg node) ->
 ~ bool_fun_eq (bool_fun_of_BDD cfg node) bool_fun_zero /\
 ~ bool_fun_eq (bool_fun_of_BDD cfg node) bool_fun_one.
Proof.
  intro cfg.  elim cfg; clear cfg; intros bs y.  elim y; clear y; intros share counter.
  intro H.  intro n.  apply
   lt_wf_ind
    with
      (P := fun n : nat =>
            forall node : ad,
            is_internal_node (bs, (share, counter)) node ->
            n = nat_of_N (var (bs, (share, counter)) node) ->
            ~
            bool_fun_eq (bool_fun_of_BDD (bs, (share, counter)) node)
              bool_fun_zero /\
            ~
            bool_fun_eq (bool_fun_of_BDD (bs, (share, counter)) node)
              bool_fun_one).
  intros n0 H0 node H1 H2.  inversion H1.  inversion H3.  inversion H4.  cut
   (config_node_OK (bs, (share, counter)) (high (bs, (share, counter)) node)).
  cut
   (config_node_OK (bs, (share, counter)) (low (bs, (share, counter)) node)).
  intros H6 H7.  elim H6.  intro H8.  elim H7.  intro H9.  cut
   (Neqb (low (bs, (share, counter)) node)
      (high (bs, (share, counter)) node) = true).
rewrite (low_high_neq (bs, (share, counter)) node H H1).
  intro H10.  discriminate H10.  rewrite H8.  rewrite H9.  apply Neqb_correct.  intro H9.
  elim H9; clear H9; intro.  cut
   (bool_fun_of_BDD (bs, (share, counter)) (high (bs, (share, counter)) node) =
    bool_fun_one).
  cut
   (bool_fun_of_BDD (bs, (share, counter)) (low (bs, (share, counter)) node) =
    bool_fun_zero).
  cut
   (bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node))
      (bool_fun_restrict (bool_fun_of_BDD (bs, (share, counter)) node)
         (var (bs, (share, counter)) node) true)).
  intros H10 H11 H12.  cut
   (bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node))
      (bool_fun_restrict (bool_fun_of_BDD (bs, (share, counter)) node)
         (var (bs, (share, counter)) node) false)).
  intros H13.  rewrite H12 in H10.  rewrite H11 in H13.  split; unfold not in |- *; intro.
  cut
   (bool_fun_eq
      (bool_fun_restrict (bool_fun_of_BDD (bs, (share, counter)) node)
         (var (bs, (share, counter)) node) true)
      (bool_fun_restrict bool_fun_zero (var (bs, (share, counter)) node) true)).
  intro H15.  cut
   (bool_fun_eq bool_fun_one
      (bool_fun_restrict bool_fun_zero (var (bs, (share, counter)) node) true)).
  intro H16.  cut (bool_fun_eq bool_fun_one bool_fun_zero).  intro H17.  absurd (bool_fun_eq bool_fun_one bool_fun_zero).
  exact bool_fun_one_zero_eq.  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_restrict bool_fun_zero
                (var (bs, (share, counter)) node) true).
  assumption.  apply bool_fun_restrict_zero.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_restrict (bool_fun_of_BDD (bs, (share, counter)) node)
                (var (bs, (share, counter)) node) true).
  assumption.  assumption.  apply bool_fun_restrict_eq.  assumption.  
  cut
   (bool_fun_eq
      (bool_fun_restrict (bool_fun_of_BDD (bs, (share, counter)) node)
         (var (bs, (share, counter)) node) false)
      (bool_fun_restrict bool_fun_one (var (bs, (share, counter)) node) false)).
  intro H15.  cut
   (bool_fun_eq bool_fun_zero
      (bool_fun_restrict bool_fun_one (var (bs, (share, counter)) node) false)).
  intro H16.  cut (bool_fun_eq bool_fun_zero bool_fun_one).  intro H17.  absurd (bool_fun_eq bool_fun_zero bool_fun_one).
  exact bool_fun_zero_one_eq.  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_restrict bool_fun_one
                (var (bs, (share, counter)) node) false).
  assumption.  apply bool_fun_restrict_one.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_restrict (bool_fun_of_BDD (bs, (share, counter)) node)
                (var (bs, (share, counter)) node) false).
  assumption.  assumption.  apply bool_fun_restrict_eq.  assumption.  apply bool_fun_of_BDDlow.
  assumption.  assumption.  apply bool_fun_of_BDDhigh.  assumption.  assumption.
  rewrite H8.  rewrite (proj1 (bool_fun_of_BDD_semantics (bs, (share, counter)) H)).
  reflexivity.  rewrite H9.  rewrite
   (proj1 (proj2 (bool_fun_of_BDD_semantics (bs, (share, counter)) H)))
   .
  reflexivity.  cut
   (~
    bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node)) bool_fun_zero /\
    ~
    bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node)) bool_fun_one).
  intro H10.  split; unfold not in |- *; intro.  apply (proj1 H10).  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_restrict (bool_fun_of_BDD (bs, (share, counter)) node)
                (var (bs, (share, counter)) node) true).
  apply bool_fun_of_BDDhigh.  assumption.  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_restrict bool_fun_zero
                (var (bs, (share, counter)) node) true).
  apply bool_fun_restrict_eq.  assumption.  apply bool_fun_restrict_zero.  apply (proj2 H10).
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_restrict (bool_fun_of_BDD (bs, (share, counter)) node)
                (var (bs, (share, counter)) node) true).
  apply bool_fun_of_BDDhigh.  assumption.  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_restrict bool_fun_one
                (var (bs, (share, counter)) node) true).
  apply bool_fun_restrict_eq.  assumption.  apply bool_fun_restrict_one.  
  apply
   H0
    with
      (m := nat_of_N
              (var (bs, (share, counter)) (high (bs, (share, counter)) node))).
  rewrite H2.  apply BDDcompare_lt.  apply BDDvar_ordered_high.  assumption.  
  assumption.  apply in_dom_is_internal.  assumption.  apply in_dom_is_internal.
  assumption.  reflexivity.  intro H8.  elim H8; intro.  elim H7; intro.  split; unfold not in |- *; intro.
  apply bool_fun_zero_one_eq.  apply
   bool_fun_eq_trans
    with
      (bool_fun_restrict (bool_fun_of_BDD (bs, (share, counter)) node)
         (var (bs, (share, counter)) node) false).
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_restrict bool_fun_zero
                (var (bs, (share, counter)) node) false).
  apply bool_fun_eq_symm.  apply bool_fun_restrict_zero.  apply bool_fun_restrict_eq.
  apply bool_fun_eq_symm.  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_of_BDD (bs, (share, counter))
                (low (bs, (share, counter)) node)).
  apply bool_fun_eq_symm.  apply bool_fun_of_BDDlow.  assumption.  assumption.
  rewrite H9.  rewrite
   (proj1 (proj2 (bool_fun_of_BDD_semantics (bs, (share, counter)) H)))
   .
  unfold bool_fun_eq, bool_fun_one in |- *.  reflexivity.  apply bool_fun_zero_one_eq.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_of_BDD (bs, (share, counter))
                (high (bs, (share, counter)) node)).
  rewrite H10.  rewrite (proj1 (bool_fun_of_BDD_semantics (bs, (share, counter)) H)).
  unfold bool_fun_eq in |- *; reflexivity.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_restrict (bool_fun_of_BDD (bs, (share, counter)) node)
                (var (bs, (share, counter)) node) true).
  apply bool_fun_of_BDDhigh.  assumption.  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_restrict bool_fun_one
                (var (bs, (share, counter)) node) true).
  apply bool_fun_restrict_eq.  assumption.  apply bool_fun_restrict_one.  elim H10; intro.
  cut
   (Neqb (low (bs, (share, counter)) node)
      (high (bs, (share, counter)) node) = false).
  rewrite H9.  rewrite H11.  rewrite (Neqb_correct BDDone).  intro; discriminate.  
  apply low_high_neq.  assumption.  assumption.  cut
   (~
    bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node)) bool_fun_zero /\
    ~
    bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node)) bool_fun_one).
  intro H12.  split; unfold not in |- *; intro.  apply (proj1 H12).  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_restrict (bool_fun_of_BDD (bs, (share, counter)) node)
                (var (bs, (share, counter)) node) true).
  apply bool_fun_of_BDDhigh.  assumption.  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_restrict bool_fun_zero
                (var (bs, (share, counter)) node) true).
  apply bool_fun_restrict_eq.  assumption.  apply bool_fun_restrict_zero.  apply (proj2 H12).
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_restrict (bool_fun_of_BDD (bs, (share, counter)) node)
                (var (bs, (share, counter)) node) true).
  apply bool_fun_of_BDDhigh.  assumption.  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_restrict bool_fun_one
                (var (bs, (share, counter)) node) true).
  apply bool_fun_restrict_eq.  assumption.  apply bool_fun_restrict_one.  apply
   H0
    with
      (m := nat_of_N
              (var (bs, (share, counter)) (high (bs, (share, counter)) node))).
  rewrite H2.  apply BDDcompare_lt.  apply BDDvar_ordered_high.  assumption.
  assumption.  apply in_dom_is_internal.  assumption.  apply in_dom_is_internal.
  assumption.  reflexivity.  cut
   (~
    bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node)) bool_fun_zero /\
    ~
    bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node)) bool_fun_one).
  intro H10.  split; unfold not in |- *; intro.  apply (proj1 H10).  apply
   bool_fun_eq_trans
    with
      (bool_fun_restrict (bool_fun_of_BDD (bs, (share, counter)) node)
         (var (bs, (share, counter)) node) false).
  apply bool_fun_of_BDDlow.  assumption.  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_restrict bool_fun_zero
                (var (bs, (share, counter)) node) false).
  apply bool_fun_restrict_eq.  assumption.  apply bool_fun_restrict_zero.  apply (proj2 H10).
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_restrict (bool_fun_of_BDD (bs, (share, counter)) node)
                (var (bs, (share, counter)) node) false).
  apply bool_fun_of_BDDlow.  assumption.  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_restrict bool_fun_one
                (var (bs, (share, counter)) node) false).
  apply bool_fun_restrict_eq.  assumption.  apply bool_fun_restrict_one.  apply
   H0
    with
      (m := nat_of_N
              (var (bs, (share, counter)) (low (bs, (share, counter)) node))).
  rewrite H2.  apply BDDcompare_lt.  apply BDDvar_ordered_low.  assumption.
  assumption.  apply in_dom_is_internal.  assumption.  apply in_dom_is_internal.
  assumption.  reflexivity.  apply low_OK.  assumption.  assumption.  apply high_OK.
  assumption.  assumption.  
Qed.

Lemma internal_node_not_constant :
 forall (cfg : BDDconfig) (node : ad),
 BDDconfig_OK cfg ->
 is_internal_node cfg node ->
 ~ bool_fun_eq (bool_fun_of_BDD cfg node) bool_fun_zero /\
 ~ bool_fun_eq (bool_fun_of_BDD cfg node) bool_fun_one.
Proof.
  intros cfg node H H0.  apply internal_node_not_constant_1 with (n := nat_of_N (var cfg node)).
  assumption.  assumption.  reflexivity.
Qed.

Lemma bool_fun_neq_internal_zero :
 forall (cfg : BDDconfig) (node : ad),
 BDDconfig_OK cfg ->
 is_internal_node cfg node ->
 ~ bool_fun_eq (bool_fun_of_BDD cfg node) (bool_fun_of_BDD cfg BDDzero).
Proof.
  intros cfg node H H0.  rewrite (proj1 (bool_fun_of_BDD_semantics cfg H)).
  exact (proj1 (internal_node_not_constant cfg node H H0)).
Qed.
 
Lemma bool_fun_neq_internal_one :
 forall (cfg : BDDconfig) (node : ad),
 BDDconfig_OK cfg ->
 is_internal_node cfg node ->
 ~ bool_fun_eq (bool_fun_of_BDD cfg node) (bool_fun_of_BDD cfg BDDone).
Proof.
  intros cfg node H H0.  rewrite (proj1 (proj2 (bool_fun_of_BDD_semantics cfg H))).
  exact (proj2 (internal_node_not_constant cfg node H H0)).
Qed.

Lemma bool_fun_neq_zero_one :
 forall cfg : BDDconfig,
 BDDconfig_OK cfg ->
 ~ bool_fun_eq (bool_fun_of_BDD cfg BDDzero) (bool_fun_of_BDD cfg BDDone).
Proof.
  intros cfg H.  unfold bool_fun_eq, bool_fun_zero, bool_fun_one in |- *.  unfold bool_fun_eval in |- *.
  rewrite (proj1 (bool_fun_of_BDD_semantics cfg H)).  rewrite (proj1 (proj2 (bool_fun_of_BDD_semantics cfg H))).
  unfold not in |- *; intros.  absurd (true = false).  unfold not in |- *; discriminate.
  unfold bool_fun_zero, bool_fun_one in H0.  rewrite (H0 (fun x : BDDvar => true)).  reflexivity.
Qed.

Lemma bool_fun_neq_one_zero :
 forall cfg : BDDconfig,
 BDDconfig_OK cfg ->
 ~ bool_fun_eq (bool_fun_of_BDD cfg BDDone) (bool_fun_of_BDD cfg BDDzero).
Proof.
  intros cfg H.  unfold bool_fun_eq, bool_fun_zero, bool_fun_one in |- *.  unfold bool_fun_eval in |- *.
  rewrite (proj1 (bool_fun_of_BDD_semantics cfg H)).  rewrite (proj1 (proj2 (bool_fun_of_BDD_semantics cfg H))).
  unfold not in |- *; intros.  absurd (false = true).  unfold not in |- *; discriminate.
  unfold bool_fun_zero, bool_fun_one in H0.  rewrite (H0 (fun x : BDDvar => true)).  reflexivity.
Qed.

Lemma bool_fun_neq_lemma :
 forall bf1 bf2 : bool_fun, ~ bool_fun_eq bf1 bf2 -> ~ bool_fun_eq bf2 bf1.
Proof.
  unfold not in |- *; intros.  apply H.  apply bool_fun_eq_symm.  assumption.
Qed.

Lemma no_duplicate_node :
 forall (cfg : BDDconfig) (node1 node2 : ad),
 BDDconfig_OK cfg ->
 is_internal_node cfg node1 ->
 is_internal_node cfg node2 ->
 var cfg node1 = var cfg node2 ->
 high cfg node1 = high cfg node2 ->
 low cfg node1 = low cfg node2 -> node1 = node2.
Proof.
  intro cfg.  elim cfg; clear cfg; intros bs y.  elim y; clear y; intros share counter.
  intros node1 node2 H H0 H1 H2 H3 H4.  inversion H0.  inversion H5.  inversion H6.  inversion H1.  inversion H8.
  inversion H9.  unfold var in H2; rewrite H7 in H2; rewrite H10 in H2.
  unfold high in H3; rewrite H7 in H3; rewrite H10 in H3.  unfold low in H4; rewrite H7 in H4; rewrite H10 in H4.
  cut (BDDshare_lookup share x x0 x1 = Some node1).  cut (BDDshare_lookup share x2 x3 x4 = Some node2).
  intros H11 H12.  rewrite H2 in H12.  rewrite H3 in H12.  rewrite H4 in H12.  rewrite H11 in H12.
  injection H12.  intro H13.  rewrite H13; reflexivity.  elim H.  intros H11 H12.  apply (proj2 (proj1 H12 x2 x3 x4 node2)).
  assumption.  elim H; intros.  apply (proj2 (proj1 H12 x x0 x1 node1)).
assumption.
Qed.

Lemma BDDunique_1 :
 forall cfg : BDDconfig,
 BDDconfig_OK cfg ->
 forall (n : nat) (node1 node2 : ad),
 n = max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2)) ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 bool_fun_eq (bool_fun_of_BDD cfg node1) (bool_fun_of_BDD cfg node2) ->
 node1 = node2.
Proof.
  intro cfg.  elim cfg; clear cfg; intros bs y.  elim y; clear y; intros share counter.
  intros H n.  apply
   lt_wf_ind
    with
      (P := fun n : nat =>
            forall node1 node2 : ad,
            n =
            max (nat_of_N (var (bs, (share, counter)) node1))
              (nat_of_N (var (bs, (share, counter)) node2)) ->
            config_node_OK (bs, (share, counter)) node1 ->
            config_node_OK (bs, (share, counter)) node2 ->
            bool_fun_eq (bool_fun_of_BDD (bs, (share, counter)) node1)
              (bool_fun_of_BDD (bs, (share, counter)) node2) -> 
            node1 = node2).
  intros n0 H00.  intros node1 node2 H0 H1 H2 H3.  elim H1; intro.  elim H2; intro.  rewrite H4; rewrite H5; reflexivity.
  elim H5; intro.  rewrite H4 in H3.  rewrite H6 in H3.  rewrite (proj1 (bool_fun_of_BDD_semantics (bs, (share, counter)) H)) in H3.
  rewrite
   (proj1 (proj2 (bool_fun_of_BDD_semantics (bs, (share, counter)) H)))
    in H3.
  absurd (bool_fun_eq bool_fun_zero bool_fun_one).  exact bool_fun_zero_one_eq.
  assumption.  absurd
   (bool_fun_eq (bool_fun_of_BDD (bs, (share, counter)) node2) bool_fun_zero).
  cut (is_internal_node (bs, (share, counter)) node2).  intro H7.  exact
   (proj1 (internal_node_not_constant (bs, (share, counter)) node2 H H7)).
  apply in_dom_is_internal.  assumption.  apply bool_fun_eq_trans with (bool_fun_of_BDD (bs, (share, counter)) node1).  apply bool_fun_eq_symm; assumption.
  rewrite H4.  rewrite (proj1 (bool_fun_of_BDD_semantics (bs, (share, counter)) H)).
  unfold bool_fun_eq in |- *; reflexivity.  elim H4; intro.  elim H2; intro.
  rewrite H5 in H3; rewrite H6 in H3.  rewrite (proj1 (bool_fun_of_BDD_semantics (bs, (share, counter)) H)) in H3.
  rewrite
   (proj1 (proj2 (bool_fun_of_BDD_semantics (bs, (share, counter)) H)))
    in H3.
  absurd (bool_fun_eq bool_fun_one bool_fun_zero).  exact bool_fun_one_zero_eq.
  assumption.  elim H6; intro.  rewrite H5; rewrite H7; reflexivity.
  absurd
   (bool_fun_eq (bool_fun_of_BDD (bs, (share, counter)) node2) bool_fun_one).
  cut (is_internal_node (bs, (share, counter)) node2).  intro H8.  exact
   (proj2 (internal_node_not_constant (bs, (share, counter)) node2 H H8)).
  apply in_dom_is_internal.  assumption.  rewrite H5 in H3.  rewrite
   (proj1 (proj2 (bool_fun_of_BDD_semantics (bs, (share, counter)) H)))
    in H3.
  apply bool_fun_eq_symm.  assumption.  elim H2; intro.  absurd
   (bool_fun_eq (bool_fun_of_BDD (bs, (share, counter)) node1) bool_fun_zero).
  cut (is_internal_node (bs, (share, counter)) node1).  intro H7.  exact
   (proj1 (internal_node_not_constant (bs, (share, counter)) node1 H H7)).
  apply in_dom_is_internal; assumption.  rewrite H6 in H3.  rewrite (proj1 (bool_fun_of_BDD_semantics (bs, (share, counter)) H)) in H3.
  assumption.  elim H6; intro.  absurd
   (bool_fun_eq (bool_fun_of_BDD (bs, (share, counter)) node1) bool_fun_one).
  cut (is_internal_node (bs, (share, counter)) node1).  intro H8.  exact
   (proj2 (internal_node_not_constant (bs, (share, counter)) node1 H H8)).
  apply in_dom_is_internal; assumption.  rewrite H7 in H3.  rewrite
   (proj1 (proj2 (bool_fun_of_BDD_semantics (bs, (share, counter)) H)))
    in H3.
  assumption.  cut (is_internal_node (bs, (share, counter)) node1).  cut (is_internal_node (bs, (share, counter)) node2).
  intros H8 H9.  elim
   (relation_sum
      (BDDcompare (var (bs, (share, counter)) node1)
         (var (bs, (share, counter)) node2))); intro y.
  elim y; clear y; intro y0.  cut
   (config_node_OK (bs, (share, counter)) (high (bs, (share, counter)) node1)).
  cut
   (config_node_OK (bs, (share, counter)) (high (bs, (share, counter)) node2)).
  cut
   (config_node_OK (bs, (share, counter)) (low (bs, (share, counter)) node1)).
  cut
   (config_node_OK (bs, (share, counter)) (low (bs, (share, counter)) node2)).
  intros H10 H11 H12 H13.  cut
   (bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node1))
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node2))).
  cut
   (bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node1))
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node2))).
  intros H14 H15.  cut (high (bs, (share, counter)) node1 = high (bs, (share, counter)) node2).
  cut (low (bs, (share, counter)) node1 = low (bs, (share, counter)) node2).  intros H16 H17.
  apply no_duplicate_node with (cfg := (bs, (share, counter))).  assumption.  assumption.
  assumption.  apply BDDcompare_eq; assumption.  assumption.  assumption.
  elim H11; intro.  elim H10; intro.  rewrite H16; rewrite H17; reflexivity.
  elim H17; intro.  absurd
   (bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node1))
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node2))).
  rewrite H16; rewrite H18.  apply bool_fun_neq_zero_one.  assumption.  assumption.
  absurd
   (bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node1))
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node2))).
  apply bool_fun_neq_lemma.  rewrite H16.  apply bool_fun_neq_internal_zero.  assumption.
  apply in_dom_is_internal.  assumption.  assumption.  elim H16; intro.  elim H10; intro.
  absurd
   (bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node1))
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node2))).
  rewrite H17; rewrite H18.  apply bool_fun_neq_one_zero.  assumption.  assumption.
  elim H18; intro.  rewrite H17; rewrite H19; reflexivity.  absurd
   (bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node1))
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node2))).
  rewrite H17.  apply bool_fun_neq_lemma.  apply bool_fun_neq_internal_one.  assumption.
  apply in_dom_is_internal.  assumption.  assumption.  elim H10; intro.  absurd
   (bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node1))
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node2))).
  rewrite H18.  apply bool_fun_neq_internal_zero.  assumption.  apply in_dom_is_internal.
  assumption.  assumption.  elim H18; intro.  absurd
   (bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node1))
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node2))).
  rewrite H19.  apply bool_fun_neq_internal_one.  assumption.  apply in_dom_is_internal.
  assumption.  assumption.  apply
   H00
    with
      (m := max
              (nat_of_N
                 (var (bs, (share, counter))
                    (low (bs, (share, counter)) node1)))
              (nat_of_N
                 (var (bs, (share, counter))
                    (low (bs, (share, counter)) node2)))).
  rewrite H0.  apply lt_max_1_2.  apply BDDcompare_lt.  apply BDDvar_ordered_low.
  assumption.  assumption.  apply in_dom_is_internal; assumption.  apply BDDcompare_lt.
  apply BDDvar_ordered_low.  assumption.  apply in_dom_is_internal; assumption.
  apply in_dom_is_internal; assumption.  reflexivity.  assumption.  assumption.
  assumption.  elim H13; intro.  elim H12; intro.  rewrite H16; rewrite H17; reflexivity.
  elim H17; intro.  absurd
   (bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node1))
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node2))).
  rewrite H16; rewrite H18; apply bool_fun_neq_zero_one.  assumption.  assumption.
  absurd
   (bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node1))
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node2))).
  rewrite H16.  apply bool_fun_neq_lemma.  apply bool_fun_neq_internal_zero.  assumption.
  apply in_dom_is_internal.  assumption.  assumption.  elim H16; intro.  rewrite H17 in H15.
  elim H12; intro.  rewrite H18 in H15.  absurd
   (bool_fun_eq (bool_fun_of_BDD (bs, (share, counter)) BDDone)
      (bool_fun_of_BDD (bs, (share, counter)) BDDzero)).
  apply bool_fun_neq_one_zero.  assumption.  assumption.  elim H18; intro.  rewrite H17; rewrite H19; reflexivity.
  absurd
   (bool_fun_eq (bool_fun_of_BDD (bs, (share, counter)) BDDone)
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node2))).
  apply bool_fun_neq_lemma.  apply bool_fun_neq_internal_one.  assumption.  apply in_dom_is_internal.
  assumption.  assumption.  elim H12; intro.  absurd
   (bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node1))
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node2))).
  rewrite H18.  apply bool_fun_neq_internal_zero.  assumption.  apply in_dom_is_internal.
  assumption.  assumption.  elim H18; intro.  absurd
   (bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node1))
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node2))).
  rewrite H19.  apply bool_fun_neq_internal_one.  assumption.  apply in_dom_is_internal.
  assumption.  assumption.  apply
   H00
    with
      (m := max
              (nat_of_N
                 (var (bs, (share, counter))
                    (high (bs, (share, counter)) node1)))
              (nat_of_N
                 (var (bs, (share, counter))
                    (high (bs, (share, counter)) node2)))).
  rewrite H0.  apply lt_max_1_2.  apply BDDcompare_lt.  apply BDDvar_ordered_high.
  assumption.  assumption.  apply in_dom_is_internal.  assumption.  apply BDDcompare_lt.
  apply BDDvar_ordered_high.  assumption.  apply in_dom_is_internal.  assumption.
  apply in_dom_is_internal.  assumption.  reflexivity.  assumption.  assumption.
  assumption.  apply
   bool_fun_eq_trans
    with
      (bool_fun_restrict (bool_fun_of_BDD (bs, (share, counter)) node1)
         (var (bs, (share, counter)) node1) false).
  apply bool_fun_of_BDDlow.  assumption.  assumption.  apply
   bool_fun_eq_trans
    with
      (bool_fun_restrict (bool_fun_of_BDD (bs, (share, counter)) node2)
         (var (bs, (share, counter)) node2) false).
  cut (var (bs, (share, counter)) node1 = var (bs, (share, counter)) node2).  intro H14.
  rewrite H14.  apply bool_fun_restrict_eq.  assumption.  apply BDDcompare_eq.
  assumption.  apply bool_fun_eq_symm.  apply bool_fun_of_BDDlow.  assumption.
  assumption.  apply
   bool_fun_eq_trans
    with
      (bool_fun_restrict (bool_fun_of_BDD (bs, (share, counter)) node1)
         (var (bs, (share, counter)) node1) true).
  apply bool_fun_of_BDDhigh.  assumption.  assumption.  apply
   bool_fun_eq_trans
    with
      (bool_fun_restrict (bool_fun_of_BDD (bs, (share, counter)) node2)
         (var (bs, (share, counter)) node2) true).
  cut (var (bs, (share, counter)) node1 = var (bs, (share, counter)) node2).  intro H14.
  rewrite H14.  apply bool_fun_restrict_eq.  assumption.  apply BDDcompare_eq.
  assumption.  apply bool_fun_eq_symm.  apply bool_fun_of_BDDhigh.  assumption. 
  assumption.  apply low_OK.  assumption.  assumption.  apply low_OK.  assumption.
  assumption.  apply high_OK.  assumption.  assumption.  apply high_OK.  assumption.
  assumption.  cut
   (config_node_OK (bs, (share, counter)) (high (bs, (share, counter)) node1)).
  cut
   (config_node_OK (bs, (share, counter)) (high (bs, (share, counter)) node2)).  cut
   (config_node_OK (bs, (share, counter)) (low (bs, (share, counter)) node1)).
  cut
   (config_node_OK (bs, (share, counter)) (low (bs, (share, counter)) node2)).  intros H10 H11 H12 H13.
  cut (low (bs, (share, counter)) node2 = high (bs, (share, counter)) node2).  intros H14.
  cut
   (Neqb (low (bs, (share, counter)) node2)
      (high (bs, (share, counter)) node2) = false).
  rewrite H14.  rewrite (Neqb_correct (high (bs, (share, counter)) node2)).  intro H15.
  discriminate H15.  apply low_high_neq.  assumption.  assumption.  cut
   (bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node2))
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node2))).
  intro H14.  elim H10; intro.  elim H12; intro.  rewrite H15; rewrite H16; reflexivity.
  elim H16; intro.  absurd
   (bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node2))
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node2))).
  rewrite H15; rewrite H17.  apply bool_fun_neq_zero_one.  assumption.  assumption.  
  absurd
   (bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node2))
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node2))).
  rewrite H15.  apply bool_fun_neq_lemma.  apply bool_fun_neq_internal_zero.  assumption.
  apply in_dom_is_internal; assumption.  assumption.  elim H15; intro.  elim H12; intro.
  absurd
   (bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node2))
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node2))).
  rewrite H16; rewrite H17.  apply bool_fun_neq_one_zero.  assumption.  assumption.
  elim H17; intro.  rewrite H16; rewrite H18; reflexivity.  absurd
   (bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node2))
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node2))).
  rewrite H16.  apply bool_fun_neq_lemma.  apply bool_fun_neq_internal_one.  assumption.
  apply in_dom_is_internal.  assumption.  assumption.  elim H12; intro.  absurd
   (bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node2))
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node2))).
  rewrite H17.  apply bool_fun_neq_internal_zero.  assumption.  apply in_dom_is_internal.
  assumption.  assumption.  elim H17; intro.  absurd
   (bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node2))
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node2))).
  rewrite H18.  apply bool_fun_neq_internal_one.  assumption.  apply in_dom_is_internal.
  assumption.  assumption.  apply
   H00
    with
      (m := max
              (nat_of_N
                 (var (bs, (share, counter))
                    (low (bs, (share, counter)) node2)))
              (nat_of_N
                 (var (bs, (share, counter))
                    (high (bs, (share, counter)) node2)))).
  rewrite H0.  apply lt_max_2.  apply BDDcompare_lt.  apply BDDvar_ordered_low.
  assumption.  assumption.  apply in_dom_is_internal; assumption.  apply BDDcompare_lt.
  apply BDDvar_ordered_high.  assumption.  apply in_dom_is_internal; assumption.
  apply in_dom_is_internal; assumption.  reflexivity.  assumption.  assumption.
  assumption.  cut
   (bool_fun_eq
      (bool_fun_restrict (bool_fun_of_BDD (bs, (share, counter)) node2)
         (var (bs, (share, counter)) node2) false)
      (bool_fun_restrict (bool_fun_of_BDD (bs, (share, counter)) node2)
         (var (bs, (share, counter)) node2) true)).
  intro H14.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_restrict
                (bool_fun_of_BDD (bs, (share, counter)) node2)
                (var (bs, (share, counter)) node2) false).
  apply bool_fun_of_BDDlow.  assumption.  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_restrict
                (bool_fun_of_BDD (bs, (share, counter)) node2)
                (var (bs, (share, counter)) node2) true).
  assumption.  apply bool_fun_eq_symm.  apply bool_fun_of_BDDhigh.  assumption.
  assumption.  cut
   (bool_fun_eq
      (bool_fun_restrict (bool_fun_of_BDD (bs, (share, counter)) node1)
         (var (bs, (share, counter)) node2) false)
      (bool_fun_restrict (bool_fun_of_BDD (bs, (share, counter)) node1)
         (var (bs, (share, counter)) node2) true)).
  intro H14.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_restrict
                (bool_fun_of_BDD (bs, (share, counter)) node1)
                (var (bs, (share, counter)) node2) false).
  apply bool_fun_restrict_eq.  apply bool_fun_eq_symm.  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_restrict
                (bool_fun_of_BDD (bs, (share, counter)) node1)
                (var (bs, (share, counter)) node2) true).
  assumption.  apply bool_fun_restrict_eq.  assumption.  cut
   (bool_fun_independent (bool_fun_of_BDD (bs, (share, counter)) node1)
      (var (bs, (share, counter)) node2)).
  intro H14.  unfold bool_fun_independent in H14.  unfold bool_fun_eq in |- *.  unfold bool_fun_restrict in |- *.
  unfold bool_fun_eval at 1 3 in |- *.  intro vb.  rewrite (H14 vb); reflexivity.  apply
   BDDvar_independent_1
    with (n := nat_of_N (var (bs, (share, counter)) node1)).
  assumption.  assumption.  reflexivity.  assumption.  apply low_OK.  assumption.
  assumption.  apply low_OK.  assumption.  assumption.  apply high_OK.  assumption.
  assumption.  apply high_OK.  assumption.  assumption.  cut
   (BDDcompare (var (bs, (share, counter)) node2)
      (var (bs, (share, counter)) node1) = Datatypes.Lt).
  clear y; intro y.  cut
   (config_node_OK (bs, (share, counter)) (high (bs, (share, counter)) node1)).
  cut
   (config_node_OK (bs, (share, counter)) (high (bs, (share, counter)) node2)).
  cut
   (config_node_OK (bs, (share, counter)) (low (bs, (share, counter)) node1)).
  cut
   (config_node_OK (bs, (share, counter)) (low (bs, (share, counter)) node2)).
  intros H10 H11 H12 H13.  cut (low (bs, (share, counter)) node1 = high (bs, (share, counter)) node1).
  intros H14.  cut
   (Neqb (low (bs, (share, counter)) node1)
      (high (bs, (share, counter)) node1) = false).
  rewrite H14.  rewrite (Neqb_correct (high (bs, (share, counter)) node1)).  intro H15.
  discriminate H15.  apply low_high_neq.  assumption.  assumption.  cut
   (bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node1))
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node1))).
  intro H14.  elim H11; intro.  elim H13; intro.  rewrite H15; rewrite H16; reflexivity.
  elim H16; intro.  absurd
   (bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node1))
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node1))).
  rewrite H15; rewrite H17.  apply bool_fun_neq_zero_one.  assumption.  assumption.
  absurd
   (bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node1))
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node1))).
  rewrite H15.  apply bool_fun_neq_lemma.  apply bool_fun_neq_internal_zero.  assumption.
  apply in_dom_is_internal; assumption.  assumption.  elim H15; intro.  elim H13; intro.
  absurd
   (bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node1))
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node1))).
  rewrite H16; rewrite H17.  apply bool_fun_neq_one_zero.  assumption.  assumption.
  elim H17; intro.  rewrite H16; rewrite H18; reflexivity.  absurd
   (bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node1))
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node1))).
  rewrite H16.  apply bool_fun_neq_lemma.  apply bool_fun_neq_internal_one.  assumption.
  apply in_dom_is_internal.  assumption.  assumption.  elim H13; intro.  absurd
   (bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node1))
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node1))).
  rewrite H17.  apply bool_fun_neq_internal_zero.  assumption.  apply in_dom_is_internal.
  assumption.  assumption.  elim H17; intro.  absurd
   (bool_fun_eq
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node1))
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node1))).
  rewrite H18.  apply bool_fun_neq_internal_one.  assumption.  apply in_dom_is_internal.
  assumption.  assumption.  apply
   H00
    with
      (m := max
              (nat_of_N
                 (var (bs, (share, counter))
                    (low (bs, (share, counter)) node1)))
              (nat_of_N
                 (var (bs, (share, counter))
                    (high (bs, (share, counter)) node1)))).
  rewrite H0.  apply lt_max_12.  apply BDDcompare_lt.  apply BDDvar_ordered_low.
  assumption.  assumption.  apply in_dom_is_internal; assumption.  apply BDDcompare_lt.
  apply BDDvar_ordered_high.  assumption.  apply in_dom_is_internal; assumption.
  apply in_dom_is_internal; assumption.  reflexivity.  assumption.  assumption.
  assumption.  cut
   (bool_fun_eq
      (bool_fun_restrict (bool_fun_of_BDD (bs, (share, counter)) node1)
         (var (bs, (share, counter)) node1) false)
      (bool_fun_restrict (bool_fun_of_BDD (bs, (share, counter)) node1)
         (var (bs, (share, counter)) node1) true)).
  intro H14.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_restrict
                (bool_fun_of_BDD (bs, (share, counter)) node1)
                (var (bs, (share, counter)) node1) false).
  apply bool_fun_of_BDDlow.  assumption.  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_restrict
                (bool_fun_of_BDD (bs, (share, counter)) node1)
                (var (bs, (share, counter)) node1) true).
  assumption.  apply bool_fun_eq_symm.  apply bool_fun_of_BDDhigh.  assumption.
  assumption.  cut
   (bool_fun_eq
      (bool_fun_restrict (bool_fun_of_BDD (bs, (share, counter)) node2)
         (var (bs, (share, counter)) node1) false)
      (bool_fun_restrict (bool_fun_of_BDD (bs, (share, counter)) node2)
         (var (bs, (share, counter)) node1) true)).
  intro H14.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_restrict
                (bool_fun_of_BDD (bs, (share, counter)) node2)
                (var (bs, (share, counter)) node1) false).
  apply bool_fun_restrict_eq.  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_restrict
                (bool_fun_of_BDD (bs, (share, counter)) node2)
                (var (bs, (share, counter)) node1) true).
  assumption.  apply bool_fun_restrict_eq.  apply bool_fun_eq_symm.  assumption.
  cut
   (bool_fun_independent (bool_fun_of_BDD (bs, (share, counter)) node2)
      (var (bs, (share, counter)) node1)).
  intro H14.  unfold bool_fun_independent in H14.  unfold bool_fun_eq in |- *.  unfold bool_fun_restrict in |- *.
  unfold bool_fun_eval at 1 3 in |- *.  intro vb.  rewrite (H14 vb); reflexivity.  apply
   BDDvar_independent_1
    with (n := nat_of_N (var (bs, (share, counter)) node2)).
  assumption.  assumption.  reflexivity.  assumption.  apply low_OK.  assumption.
  assumption.  apply low_OK.  assumption.  assumption.  apply high_OK.  assumption.
  assumption.  apply high_OK.  assumption.  assumption.  apply BDDcompare_sup_inf.
  assumption.  apply in_dom_is_internal.  assumption.  apply in_dom_is_internal.
  assumption.
Qed.

Lemma BDDunique :
 forall cfg : BDDconfig,
 BDDconfig_OK cfg ->
 forall node1 node2 : ad,
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 bool_fun_eq (bool_fun_of_BDD cfg node1) (bool_fun_of_BDD cfg node2) ->
 node1 = node2.
Proof.
  intros cfg H node1 node2 H0 H1 H2.  apply
   BDDunique_1
    with
      (cfg := cfg)
      (n := max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2))).
  assumption.  reflexivity.  assumption.  assumption.  assumption.
Qed.

Lemma bool_fun_eq_lemma :
 forall (bf1 bf2 : bool_fun) (x : BDDvar),
 bool_fun_ext bf1 ->
 bool_fun_ext bf2 ->
 bool_fun_eq (bool_fun_restrict bf1 x true) (bool_fun_restrict bf2 x true) ->
 bool_fun_eq (bool_fun_restrict bf1 x false) (bool_fun_restrict bf2 x false) ->
 bool_fun_eq bf1 bf2.
Proof.
  intros bf1 bf2 x H H0 H1 H2.  unfold bool_fun_eq in |- *.  intro vb.  elim (sumbool_of_bool (vb x)); intro.
  cut (var_binding_eq (augment vb x true) vb).  intro H3.  cut (bool_fun_eval bf2 (augment vb x true) = bool_fun_eval bf2 vb).
  cut (bool_fun_eval bf1 (augment vb x true) = bool_fun_eval bf1 vb).  intros H4 H5.
  rewrite <- H4.  rewrite <- H5.  unfold bool_fun_eq, bool_fun_restrict in H1.
  unfold bool_fun_eval at 1 3 in H1.  apply H1.  apply H.  assumption.  apply H0.
  assumption.  apply augment_eq.  assumption.  cut (var_binding_eq (augment vb x false) vb).
  intro H3.  cut (bool_fun_eval bf2 (augment vb x false) = bool_fun_eval bf2 vb).
  cut (bool_fun_eval bf1 (augment vb x false) = bool_fun_eval bf1 vb).  intros H4 H5.
  rewrite <- H4.  rewrite <- H5.  unfold bool_fun_eq, bool_fun_restrict in H2.
  unfold bool_fun_eval at 1 3 in H2.  apply H2.  apply H.  assumption.  apply H0.
  assumption.  apply augment_eq.  assumption.  
Qed.
  
Lemma bool_fun_preservation_1 :
 forall cfg cfg' : BDDconfig,
 BDDconfig_OK cfg ->
 BDDconfig_OK cfg' ->
 (forall (x : BDDvar) (l r a : ad),
  MapGet _ (fst cfg) a = Some (x, (l, r)) ->
  MapGet _ (fst cfg') a = Some (x, (l, r))) ->
 forall (n : nat) (node : ad),
 n = nat_of_N (var cfg node) ->
 config_node_OK cfg node ->
 bool_fun_eq (bool_fun_of_BDD cfg' node) (bool_fun_of_BDD cfg node).
Proof.
  intro cfg.  elim cfg; clear cfg; intros bs y.  elim y; clear y; intros share counter.
  intro cfg'.  elim cfg'; clear cfg'; intros bs' y'.  elim y'; clear y'; intros share' counter'.
  intros H H0 H1 n.  apply
   lt_wf_ind
    with
      (P := fun n : nat =>
            forall node : ad,
            n = nat_of_N (var (bs, (share, counter)) node) ->
            config_node_OK (bs, (share, counter)) node ->
            bool_fun_eq (bool_fun_of_BDD (bs', (share', counter')) node)
              (bool_fun_of_BDD (bs, (share, counter)) node)).
  intros n0 H2 node H3 H4.  cut (config_node_OK (bs', (share', counter')) node).  intro H5.  elim H4; intro.
  rewrite H6.  rewrite (proj1 (bool_fun_of_BDD_semantics (bs, (share, counter)) H)).
  rewrite (proj1 (bool_fun_of_BDD_semantics (bs', (share', counter')) H0)).
  unfold bool_fun_eq in |- *; reflexivity.  elim H6; intro.  rewrite H7.  rewrite
   (proj1 (proj2 (bool_fun_of_BDD_semantics (bs', (share', counter')) H0)))
   .
  rewrite
   (proj1 (proj2 (bool_fun_of_BDD_semantics (bs, (share, counter)) H)))
   .
  unfold bool_fun_eq in |- *; reflexivity.  cut (is_internal_node (bs, (share, counter)) node).
  cut (is_internal_node (bs', (share', counter')) node).  intros H8 H9.  cut
   (bool_fun_eq
      (bool_fun_of_BDD (bs', (share', counter'))
         (low (bs', (share', counter')) node))
      (bool_fun_of_BDD (bs, (share, counter))
         (low (bs, (share, counter)) node))).
  cut
   (bool_fun_eq
      (bool_fun_of_BDD (bs', (share', counter'))
         (high (bs', (share', counter')) node))
      (bool_fun_of_BDD (bs, (share, counter))
         (high (bs, (share, counter)) node))).
  intros H10 H11.  cut (var (bs, (share, counter)) node = var (bs', (share', counter')) node).
  intro H12.  apply bool_fun_eq_lemma with (x := var (bs, (share, counter)) node).  apply bool_fun_of_BDD_ext.
  apply bool_fun_of_BDD_ext.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_of_BDD (bs', (share', counter'))
                (high (bs', (share', counter')) node)).
  apply bool_fun_eq_symm.  rewrite H12.  apply bool_fun_of_BDDhigh.  assumption.
  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_of_BDD (bs, (share, counter))
                (high (bs, (share, counter)) node)).
  assumption.  apply bool_fun_of_BDDhigh.  assumption.  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_of_BDD (bs', (share', counter'))
                (low (bs', (share', counter')) node)).
  rewrite H12.  apply bool_fun_eq_symm; apply bool_fun_of_BDDlow; assumption; assumption.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_of_BDD (bs, (share, counter))
                (low (bs, (share, counter)) node)).
  assumption.  apply bool_fun_of_BDDlow; assumption; assumption.  unfold var in |- *.
  inversion H9.  inversion H12.  inversion H13.  rewrite H14.  rewrite (H1 x x0 x1 node H14).
  reflexivity.  cut
   (config_node_OK (bs, (share, counter)) (high (bs, (share, counter)) node)).  cut
   (config_node_OK (bs', (share', counter'))
      (high (bs', (share', counter')) node)).
  intros H10 H11.  inversion H9.  inversion H12.  inversion H13.  cut
   (high (bs', (share', counter')) node = high (bs, (share, counter)) node).
  cut (low (bs', (share', counter')) node = low (bs, (share, counter)) node).  intros H15 H16.
  elim H11; intro.  rewrite H16; rewrite H17.  rewrite (proj1 (bool_fun_of_BDD_semantics (bs, (share, counter)) H)).
  rewrite (proj1 (bool_fun_of_BDD_semantics (bs', (share', counter')) H0)).
  unfold bool_fun_eq in |- *; reflexivity.  elim H17; intro.  rewrite H16; rewrite H18.
  rewrite
   (proj1 (proj2 (bool_fun_of_BDD_semantics (bs', (share', counter')) H0)))
   .
  rewrite
   (proj1 (proj2 (bool_fun_of_BDD_semantics (bs, (share, counter)) H)))
   .
  unfold bool_fun_eq in |- *; reflexivity.  rewrite H16.  apply
   H2
    with
      (m := nat_of_N
              (var (bs, (share, counter)) (high (bs, (share, counter)) node))).
  rewrite H3.  apply BDDcompare_lt.  apply BDDvar_ordered_high.  assumption.
  assumption.  apply in_dom_is_internal.  assumption.  reflexivity.  assumption.
  unfold low in |- *.  rewrite H14.  rewrite (H1 x x0 x1 node H14).  reflexivity.  unfold high in |- *.
  rewrite H14.  rewrite (H1 x x0 x1 node H14).  reflexivity.  apply high_OK.  assumption.
  assumption.  apply high_OK.  assumption.  assumption.  cut (low (bs', (share', counter')) node = low (bs, (share, counter)) node).
  intro H10.  rewrite H10.  cut
   (config_node_OK (bs, (share, counter)) (low (bs, (share, counter)) node)).
  intro H11.  elim H11.  intro H12.  rewrite H12.  rewrite (proj1 (bool_fun_of_BDD_semantics (bs, (share, counter)) H)).
  rewrite (proj1 (bool_fun_of_BDD_semantics (bs', (share', counter')) H0)).
  unfold bool_fun_eq in |- *; reflexivity.  intro H12.  elim H12; intro.  rewrite H13.
  rewrite
   (proj1 (proj2 (bool_fun_of_BDD_semantics (bs, (share, counter)) H)))
   .
  rewrite
   (proj1 (proj2 (bool_fun_of_BDD_semantics (bs', (share', counter')) H0)))
   .
  unfold bool_fun_eq in |- *; reflexivity.  apply
   H2
    with
      (m := nat_of_N
              (var (bs, (share, counter)) (low (bs, (share, counter)) node))).
  rewrite H3.  apply BDDcompare_lt.  apply BDDvar_ordered_low.  assumption.
  assumption.  apply in_dom_is_internal.  assumption.  reflexivity.  apply low_OK.
  assumption.  assumption.  apply low_OK.  assumption.  assumption.  unfold low in |- *.
  inversion H9.  inversion H10.  inversion H11.  rewrite H12.  rewrite (H1 x x0 x1 node H12).
  reflexivity.  apply in_dom_is_internal.  elim (option_sum _ (MapGet _ (fst (bs, (share, counter))) node)).
  intro y.  elim y; intro x.  elim x; intros x0 x1.  elim x1; intros y0 y1 y2.  unfold in_dom in |- *.
  rewrite (H1 x0 y0 y1 node y2).  reflexivity.  intro y.  unfold in_dom in H7.
  rewrite y in H7; discriminate.  apply in_dom_is_internal.  assumption.  elim H4; intro.
  rewrite H5.  left; reflexivity.  elim H5; intro.  rewrite H6; right; left; reflexivity.
  right; right.  elim (option_sum _ (MapGet _ (fst (bs, (share, counter))) node)).
  intro y.  elim y; intro x.  elim x; intro y0.  intro y1.  elim y1; intros y2 y3 y4.  unfold in_dom in |- *; rewrite (H1 y0 y2 y3 node y4); reflexivity.
  intro y.  unfold in_dom in H6; rewrite y in H6; discriminate.
Qed.

Lemma bool_fun_preservation :
 forall (cfg cfg' : BDDconfig) (node : ad),
 BDDconfig_OK cfg ->
 BDDconfig_OK cfg' ->
 (forall (x : BDDvar) (l r a : ad),
  MapGet _ (fst cfg) a = Some (x, (l, r)) ->
  MapGet _ (fst cfg') a = Some (x, (l, r))) ->
 config_node_OK cfg node ->
 bool_fun_eq (bool_fun_of_BDD cfg' node) (bool_fun_of_BDD cfg node).
Proof.
  intros cfg cfg' node H H0 H1 H2.  apply bool_fun_preservation_1 with (n := nat_of_N (var cfg node)).  assumption.
  assumption.  assumption.  reflexivity.  assumption.
Qed.