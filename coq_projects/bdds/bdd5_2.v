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

Lemma BDDneg_memo_OK_1_lemma_2_1' :
 forall (cfg : BDDconfig) (memo : BDDneg_memo),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg memo ->
 BDDneg_memo_OK_2 cfg (BDDneg_memo_put memo BDDzero BDDone).
Proof.
  intro cfg.  elim cfg; clear cfg; intros bs y; elim y; clear y; intros share counter.
  intros memo H H0.  unfold BDDneg_memo_OK_2 in |- *.  intros node node' bound H1 H2.  unfold BDDneg_memo_put, BDDneg_memo_lookup in H1.
  rewrite (MapPut_semantics ad memo BDDzero BDDone node) in H1.  elim (sumbool_of_bool (Neqb BDDzero node)).
  intro y.  cut (BDDzero = node).  intro H3.  rewrite y in H1.  injection H1.  intros H4.
  rewrite <- H3.  rewrite <- H4.  split.  left; reflexivity.  elim bound.
  simpl in |- *.  elim H.  intros H5 H6.  elim H5; intros.  rewrite H7.  reflexivity.  
  intros n H5.  simpl in |- *.  elim H.  intros H6 H7.  elim H6; intros.  simpl in H9.  rewrite H8.
  reflexivity.  apply Neqb_complete.  assumption.  intro y.  rewrite y in H1.
  unfold BDDneg_memo_OK_2 in H0.  apply H0.  assumption.  assumption.
Qed.

Lemma BDDneg_memo_OK_1_lemma_3_1' :
 forall (cfg : BDDconfig) (memo : BDDneg_memo),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg memo ->
 BDDneg_memo_OK_2 cfg (BDDneg_memo_put memo BDDone BDDzero).
Proof.
  intro cfg.  elim cfg; clear cfg; intros bs y; elim y; clear y; intros share counter.
  intros memo H H0.  unfold BDDneg_memo_OK_2 in |- *.  intros node node' bound H1 H2.  unfold BDDneg_memo_put, BDDneg_memo_lookup in H1.
  rewrite (MapPut_semantics ad memo BDDone BDDzero node) in H1.  elim (sumbool_of_bool (Neqb BDDone node)).
  intro y.  cut (BDDone = node).  intro H3.  rewrite y in H1.  injection H1.  intros H4.
  rewrite <- H3.  rewrite <- H4.  split.  right; left; reflexivity.  elim bound.
  simpl in |- *.  elim H.  intros H5 H6.  elim H5; intros.  rewrite (proj1 H8).  reflexivity.
  intros n H5.  simpl in |- *.  elim H.  intros H6 H7.  elim H6; intros.  rewrite (proj1 H9).
  reflexivity.  apply Neqb_complete.  assumption.  intro y.  rewrite y in H1.  unfold BDDneg_memo_OK_2 in H0.
  apply H0.  assumption.  assumption.
Qed.

Lemma BDDneg_memo_OK_1_lemma_1_2' :
 forall (cfg : BDDconfig) (x : BDDvar) (l r node : ad) 
   (n m : nat) (memo : BDDneg_memo),
 BDDconfig_OK cfg ->
 MapGet _ (fst cfg) node = Some (x, (l, r)) ->
 nat_of_N (var cfg node) < n ->
 n = S m ->
 BDDneg_memo_OK_2 (fst (BDDneg_2 (fst (BDDneg_2 cfg l m)) r m)) memo ->
 BDDneg_memo_OK_2 (fst (BDDneg_2 cfg node n))
   (BDDneg_memo_put memo node (snd (BDDneg_2 cfg node n))).
Proof.
  intro cfg.  elim cfg; clear cfg; intros bs y; elim y; clear y; intros share counter.
  intros x l r node n m memo H H0 H1.  intro H3.  intros H2.  unfold BDDneg_memo_OK_2 in |- *.
  intros node0 node' bound H4 H5.  unfold BDDneg_memo_put, BDDneg_memo_lookup in H4.  rewrite
   (MapPut_semantics ad memo node
      (snd (BDDneg_2 (bs, (share, counter)) node n)) node0)
    in H4.
  elim (sumbool_of_bool (Neqb node node0)).  intro y.  rewrite y in H4.  injection H4; intros.
  cut (node = node0).  intro H7.  rewrite <- H7.  rewrite <- H7 in H5.  split.
  apply nodes_preserved_2 with (cfg := (bs, (share, counter))).  right; right.  unfold in_dom in |- *.
  rewrite H0.  reflexivity.  unfold nodes_preserved in |- *.  cut (config_node_OK (bs, (share, counter)) node).
  cut
   (is_internal_node (bs, (share, counter)) node ->
    nat_of_N (var (bs, (share, counter)) node) < n).
  intros H8 H9.  exact
   (proj1 (proj2 (BDDneg_2_lemma n (bs, (share, counter)) node H H9 H8))).
  intro; assumption.  right; right.  unfold in_dom in |- *.  rewrite H0; reflexivity.
  apply BDDneg_memo_OK_1_lemma_1_1_1.  cut (config_node_OK (bs, (share, counter)) node).
  intro H8.  cut
   (is_internal_node (bs, (share, counter)) node ->
    nat_of_N (var (bs, (share, counter)) node) < n).
  intros H9.  exact (proj1 (BDDneg_2_lemma n (bs, (share, counter)) node H H8 H9)).
  intro H9.  assumption.  right.  right.  unfold in_dom in |- *.  rewrite H0.  reflexivity.
  apply nodes_preserved_2 with (cfg := (bs, (share, counter))).  right; right.  unfold in_dom in |- *.
  rewrite H0.  reflexivity.  unfold nodes_preserved in |- *.  cut (config_node_OK (bs, (share, counter)) node).
  cut
   (is_internal_node (bs, (share, counter)) node ->
    nat_of_N (var (bs, (share, counter)) node) < n).
  intros H8 H9.  exact
   (proj1 (proj2 (BDDneg_2_lemma n (bs, (share, counter)) node H H9 H8))).
  intro; assumption.  right; right.  unfold in_dom in |- *.  rewrite H0; reflexivity.
  rewrite <- H6.  cut (config_node_OK (bs, (share, counter)) node).  intro H8.
  cut
   (is_internal_node (bs, (share, counter)) node ->
    nat_of_N (var (bs, (share, counter)) node) < n).
  intros H9.  exact
   (proj1
      (proj2
         (proj2
            (proj2 (BDDneg_2_lemma n (bs, (share, counter)) node H H8 H9))))).  
  intro; assumption.  right; right.  unfold in_dom in |- *.  rewrite H0; reflexivity.
  assumption.  rewrite <- H6.  cut (config_node_OK (bs, (share, counter)) node).
  intro H8.  cut
   (is_internal_node (bs, (share, counter)) node ->
    nat_of_N (var (bs, (share, counter)) node) < n).
  intro H9.  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_neg (bool_fun_of_BDD (bs, (share, counter)) node)).
  exact
   (proj2
      (proj2
         (proj2
            (proj2 (BDDneg_2_lemma n (bs, (share, counter)) node H H8 H9))))).
  apply bool_fun_eq_neg_1.  apply bool_fun_eq_symm.  apply bool_fun_preservation.
  assumption.  exact (proj1 (BDDneg_2_lemma n (bs, (share, counter)) node H H8 H9)).
  exact
   (proj1 (proj2 (BDDneg_2_lemma n (bs, (share, counter)) node H H8 H9))).
  assumption.  intro; assumption.  right; right.  unfold in_dom in |- *.  rewrite H0.
  reflexivity.  apply Neqb_complete.  assumption.  intro y.  rewrite y in H4.
  unfold BDDneg_memo_OK_2 in H2.  split.  apply
   nodes_preserved_2
    with
      (cfg := fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r m)).
  cut
   (is_internal_node
      (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r m)) node0 ->
    nat_of_N
      (var (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r m))
         node0) <
    S
      (nat_of_N
         (var
            (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r m))
            node0))).
  intro H6.  exact
   (proj1
      (H2 node0 node'
         (S
            (nat_of_N
               (var
                  (fst
                     (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r
                        m)) node0))) H4 H6)).
  intro H6.  unfold lt in |- *.  apply le_n.  apply nodes_preserved_1 with (n := n) (x := x).
  assumption.  assumption.  assumption.  assumption.  apply BDDneg_memo_OK_1_lemma_1_1_1.
  cut (config_node_OK (bs, (share, counter)) node).  intro H6.  cut
   (is_internal_node (bs, (share, counter)) node ->
    nat_of_N (var (bs, (share, counter)) node) < n).
  intro H7.  exact (proj1 (BDDneg_2_lemma n (bs, (share, counter)) node H H6 H7)).
  intro H7.  assumption.  right.  right.  unfold in_dom in |- *.  rewrite H0.  reflexivity.
  apply
   nodes_preserved_2
    with
      (cfg := fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r m)).
  cut
   (is_internal_node
      (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r m)) node0 ->
    nat_of_N
      (var (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r m))
         node0) <
    S
      (nat_of_N
         (var
            (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r m))
            node0))).
  intro H6.  exact
   (proj1
      (H2 node0 node'
         (S
            (nat_of_N
               (var
                  (fst
                     (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r
                        m)) node0))) H4 H6)).
  intro H6.  unfold lt in |- *.  apply le_n.  apply nodes_preserved_1 with (n := n) (x := x).  assumption.
  assumption.  assumption.  assumption.  cut
   (config_node_OK
      (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r m)) node').
  intro H6.  cut
   (nodes_preserved
      (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r m))
      (fst (BDDneg_2 (bs, (share, counter)) node n))).
  intro H7.  apply
   nodes_preserved_2
    with
      (cfg := fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r m)).
  assumption.  assumption.  apply nodes_preserved_1 with (x := x).  assumption.  
  assumption.  assumption.  assumption.  apply BDDneg_memo_OK_lemma_1_4' with (memo := memo) (node := node0).
  apply BDDneg_2_config_OK_lemma_2 with (n := n) (x := x) (node := node).  assumption.  assumption.
  assumption.  assumption.  assumption.  cut
   (is_internal_node
      (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r m)) node0 ->
    nat_of_N
      (var (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r m))
         node0) <
    S
      (nat_of_N
         (var
            (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r m))
            node0))).
  intro H6.  exact
   (proj1
      (H2 node0 node'
         (S
            (nat_of_N
               (var
                  (fst
                     (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r
                        m)) node0))) H4 H6)).
  intro H6.  unfold lt in |- *.  apply le_n.  assumption.  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_of_BDD
                (fst
                   (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r m))
                node').
  apply bool_fun_preservation.  apply BDDneg_2_config_OK_lemma_2 with (node := node) (x := x) (n := n).
  assumption.  assumption.  assumption.  assumption.  cut (config_node_OK (bs, (share, counter)) node).
  intro H6.  cut
   (is_internal_node (bs, (share, counter)) node ->
    nat_of_N (var (bs, (share, counter)) node) < n).
  intro H7.  exact (proj1 (BDDneg_2_lemma n (bs, (share, counter)) node H H6 H7)).  
  intro; assumption.  right; right.  unfold in_dom in |- *.  rewrite H0.  reflexivity.
  cut
   (nodes_preserved
      (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r m))
      (fst (BDDneg_2 (bs, (share, counter)) node n))).
  unfold nodes_preserved in |- *.  intro H6.  assumption.  apply nodes_preserved_1 with (x := x).
  assumption.  assumption.  assumption.  assumption.  apply BDDneg_memo_OK_lemma_1_4' with (memo := memo) (node := node0).
  apply BDDneg_2_config_OK_lemma_2 with (node := node) (x := x) (n := n).  assumption.  assumption.
  assumption.  assumption.  assumption.  cut
   (is_internal_node
      (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r m)) node0 ->
    nat_of_N
      (var (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r m))
         node0) <
    S
      (nat_of_N
         (var
            (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r m))
            node0))).
  intro H6.  exact
   (proj1
      (H2 node0 node'
         (S
            (nat_of_N
               (var
                  (fst
                     (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r
                        m)) node0))) H4 H6)).
  intro H6.  unfold lt in |- *.  apply le_n.  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_neg
                (bool_fun_of_BDD
                   (fst
                      (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r
                         m)) node0)).
  apply BDDneg_memo_OK_bool_fun_1' with (memo := memo).  apply BDDneg_2_config_OK_lemma_2 with (node := node) (x := x) (n := n).
  assumption.  assumption.  assumption.  assumption.  assumption.  cut
   (is_internal_node
      (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r m)) node0 ->
    nat_of_N
      (var (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r m))
         node0) <
    S
      (nat_of_N
         (var
            (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r m))
            node0))).
  intro H6.  exact
   (proj1
      (H2 node0 node'
         (S
            (nat_of_N
               (var
                  (fst
                     (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r
                        m)) node0))) H4 H6)).
  intro H6.  unfold lt in |- *.  apply le_n.  assumption.  apply bool_fun_eq_neg_1.  apply bool_fun_eq_symm.
  apply bool_fun_preservation.  apply BDDneg_2_config_OK_lemma_2 with (n := n) (x := x) (node := node).
  assumption.  assumption.  assumption.  assumption.  cut (config_node_OK (bs, (share, counter)) node).
  intro H6.  cut
   (is_internal_node (bs, (share, counter)) node ->
    nat_of_N (var (bs, (share, counter)) node) < n).
  intro H7.  exact (proj1 (BDDneg_2_lemma n (bs, (share, counter)) node H H6 H7)).
  intro; assumption.  right; right.  unfold in_dom in |- *.  rewrite H0.  reflexivity.
  cut
   (nodes_preserved
      (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r m))
      (fst (BDDneg_2 (bs, (share, counter)) node n))).
  unfold nodes_preserved in |- *.  intro H6.  assumption.  apply nodes_preserved_1 with (x := x).
  assumption.  assumption.  assumption.  assumption.  cut
   (is_internal_node
      (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r m)) node0 ->
    nat_of_N
      (var (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r m))
         node0) <
    S
      (nat_of_N
         (var
            (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r m))
            node0))).
  intro H6.  exact
   (proj1
      (H2 node0 node'
         (S
            (nat_of_N
               (var
                  (fst
                     (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l m)) r
                        m)) node0))) H4 H6)).
  intro H6.  unfold lt in |- *.  apply le_n.
Qed.

Lemma BDDneg_1_lemma' :
 forall (bound : nat) (arg : BDDconfig * ad * BDDneg_memo),
 BDDconfig_OK (fst (fst arg)) ->
 config_node_OK (fst (fst arg)) (snd (fst arg)) ->
 BDDneg_memo_OK_2 (fst (fst arg)) (snd arg) ->
 (is_internal_node (fst (fst arg)) (snd (fst arg)) ->
  nat_of_N (var (fst (fst arg)) (snd (fst arg))) < bound) ->
 fst (BDDneg_1 arg bound) = BDDneg_2 (fst (fst arg)) (snd (fst arg)) bound /\
 BDDneg_memo_OK_2 (fst (fst (BDDneg_1 arg bound))) (snd (BDDneg_1 arg bound)).
Proof.
  intro bound.  apply
   lt_wf_ind
    with
      (P := fun bound : nat =>
            forall arg : BDDconfig * ad * BDDneg_memo,
            BDDconfig_OK (fst (fst arg)) ->
            config_node_OK (fst (fst arg)) (snd (fst arg)) ->
            BDDneg_memo_OK_2 (fst (fst arg)) (snd arg) ->
            (is_internal_node (fst (fst arg)) (snd (fst arg)) ->
             nat_of_N (var (fst (fst arg)) (snd (fst arg))) < bound) ->
            fst (BDDneg_1 arg bound) =
            BDDneg_2 (fst (fst arg)) (snd (fst arg)) bound /\
            BDDneg_memo_OK_2 (fst (fst (BDDneg_1 arg bound)))
              (snd (BDDneg_1 arg bound))).
  intros n H arg.  elim arg; clear arg; intro y.  elim y; clear y.  intros cfg node memo.
  intros H0 H1 H2 H3.  elim
   (option_sum _
      (BDDneg_memo_lookup (snd (cfg, node, memo))
         (snd (fst (cfg, node, memo))))).
  intro y.  elim y; clear y; intros node' H4.  rewrite (BDDneg_1_lemma_1 (cfg, node, memo) node' n H4).
  simpl in |- *.  split.  simpl in H2.  unfold BDDneg_memo_OK_2 in H2.  rewrite (proj2 (H2 node node' n H4 H3)).
  reflexivity.  assumption.  intro y.  elim
   (option_sum _
      (MapGet _ (fst (fst (fst (cfg, node, memo))))
         (snd (fst (cfg, node, memo))))).
  intro y0.  elim y0; clear y0.  intro x.  elim x; clear x.  intros x y0.  elim y0; clear y0; intros l r H4.
  elim (nat_sum n).  intros y0.  elim y0; clear y0.  intros m H5.  rewrite (BDDneg_1_lemma_4 (cfg, node, memo) x l r n m H5 y H4).





  simpl in |- *.  cut
   (fst (BDDneg_1 (cfg, l, memo) m) =
    BDDneg_2 (fst (fst (cfg, l, memo))) (snd (fst (cfg, l, memo))) m /\
    BDDneg_memo_OK_2 (fst (fst (BDDneg_1 (cfg, l, memo) m)))
      (snd (BDDneg_1 (cfg, l, memo) m))).
  intro H6.  cut
   (fst
      (BDDneg_1
         (fst
            (fst
               (BDDneg_1
                  (fst (fst (cfg, node, memo)), l, snd (cfg, node, memo)) m)),
         r,
         snd
           (BDDneg_1 (fst (fst (cfg, node, memo)), l, snd (cfg, node, memo))
              m)) m) =
    BDDneg_2
      (fst
         (fst
            (fst
               (fst
                  (BDDneg_1
                     (fst (fst (cfg, node, memo)), l, snd (cfg, node, memo))
                     m)), r,
            snd
              (BDDneg_1
                 (fst (fst (cfg, node, memo)), l, snd (cfg, node, memo)) m))))
      (snd
         (fst
            (fst
               (fst
                  (BDDneg_1
                     (fst (fst (cfg, node, memo)), l, snd (cfg, node, memo))
                     m)), r,
            snd
              (BDDneg_1
                 (fst (fst (cfg, node, memo)), l, snd (cfg, node, memo)) m))))
      m /\
    BDDneg_memo_OK_2
      (fst
         (fst
            (BDDneg_1
               (fst
                  (fst
                     (BDDneg_1
                        (fst (fst (cfg, node, memo)), l,
                        snd (cfg, node, memo)) m)), r,
               snd
                 (BDDneg_1
                    (fst (fst (cfg, node, memo)), l, snd (cfg, node, memo)) m))
               m)))
      (snd
         (BDDneg_1
            (fst
               (fst
                  (BDDneg_1
                     (fst (fst (cfg, node, memo)), l, snd (cfg, node, memo))
                     m)), r,
            snd
              (BDDneg_1
                 (fst (fst (cfg, node, memo)), l, snd (cfg, node, memo)) m))
            m))).  intro H7.  simpl in H6, H7. 
  rewrite (proj1 H7).  rewrite (proj1 H6).  cut
   (BDDmake (fst (BDDneg_2 (fst (BDDneg_2 cfg l m)) r m)) x
      (snd (BDDneg_2 cfg l m)) (snd (BDDneg_2 (fst (BDDneg_2 cfg l m)) r m)) =
    BDDneg_2 cfg node n).

  intro H8.  split.  assumption.  rewrite (proj1 H6) in H7.
  elim H7; intros. rewrite H9 in H7. clear H9 H10. (* instead of Rewrite (proj1 ? ? H7) in H7. which does not work in 6.3. *)
  rewrite H8.  apply BDDneg_memo_OK_1_lemma_1_2' with (x := x) (l := l) (r := r) (m := m).  assumption.
  assumption.  apply H3.  split with x; split with l; split with r; assumption.
  assumption.  exact (proj2 H7).  rewrite H5.  simpl in |- *.  simpl in H4.  rewrite H4.
  reflexivity.  apply H.  rewrite H5.  unfold lt in |- *.  apply le_n.  simpl in |- *.  rewrite (proj1 H6).
  simpl in |- *.  cut (config_node_OK cfg l).  intro.  cut (is_internal_node cfg l -> nat_of_N (var cfg l) < m).
  intros H8.  exact (proj1 (BDDneg_2_lemma m cfg l H0 H7 H8)).  intro H8.  apply lt_trans_1 with (y := nat_of_N (var cfg node)).
  cut (l = low cfg node).  intro H9.  rewrite H9.  apply BDDcompare_lt.  apply BDDvar_ordered_low.





  assumption.  split with x; split with l; split with r.  assumption.  rewrite <- H9; assumption.
  unfold low in |- *.  simpl in H4.  rewrite H4.  reflexivity.  rewrite <- H5.  apply H3.
  simpl in |- *.  split with x; split with l; split with r; assumption.  cut (l = low cfg node); intros.
  rewrite H7.  apply low_OK.  assumption.  split with x; split with l; split with r; assumption.
  unfold low in |- *; simpl in H4; rewrite H4; reflexivity.  simpl in |- *.  rewrite (proj1 H6).
  simpl in |- *.  cut (config_node_OK cfg l).  intro H7.  cut (is_internal_node cfg l -> nat_of_N (var cfg l) < m).
  intro H8.  cut (config_node_OK cfg r).  intro H9.  elim H9; intro.  rewrite H10.
  left; reflexivity.  elim H10; intro.  rewrite H11; right; left; reflexivity.
  right; right.  unfold in_dom in |- *.  cut (is_internal_node cfg r).  intro H12.  inversion H12.
  inversion H13.  inversion H14.  simpl in H0.  simpl in |- *.  cut
   (MapGet (BDDvar * (ad * ad)) (fst (fst (BDDneg_2 cfg l m))) r =
    Some (x0, (x1, x2))).
  intro H16.  rewrite H16.  reflexivity.  exact (proj1 (proj2 (BDDneg_2_lemma m cfg l H0 H7 H8)) x0 x1 x2 r H15).
  apply in_dom_is_internal.  assumption.  cut (r = high cfg node).  intro H9.  rewrite H9.
  apply high_OK.  assumption.  split with x; split with l; split with r; assumption.  
  unfold high in |- *.  simpl in H4; rewrite H4; reflexivity.  intro H8.  apply lt_trans_1 with (y := nat_of_N (var cfg node)).
  apply BDDcompare_lt.  cut (l = low cfg node).  intro; rewrite H9.  apply BDDvar_ordered_low.
  assumption.  split with x; split with l; split with r; assumption.  rewrite <- H9; assumption.
  unfold low in |- *; simpl in H4; rewrite H4; reflexivity.  rewrite <- H5; apply H3.
  simpl in |- *.  split with x; split with l; split with r; assumption.  cut (l = low cfg node).
  intro H7.  rewrite H7.  apply low_OK.  assumption.  split with x; split with l; split with r; assumption.
  unfold low in |- *; simpl in H4; rewrite H4; reflexivity.  simpl in |- *.  exact (proj2 H6).





  simpl in |- *.  rewrite (proj1 H6).  simpl in |- *.  intro H7.  cut (var (fst (BDDneg_2 cfg l m)) r = var cfg r).
  intro H8.  rewrite H8.  apply lt_trans_1 with (y := nat_of_N (var cfg node)).  apply BDDcompare_lt.
  cut (r = high cfg node).  intro H9.  rewrite H9.  apply BDDvar_ordered_high.  assumption.
  split with x; split with l; split with r; assumption.  cut (config_node_OK cfg (high cfg node)).
  intro H10.  elim H10; intro.  inversion H7.  inversion H12.  inversion H13.
  rewrite H9 in H14; rewrite H11 in H14.  cut (BDDconfig_OK (fst (BDDneg_2 cfg l m))).
  intro H15.  rewrite (config_OK_zero (fst (BDDneg_2 cfg l m)) H15) in H14.  discriminate H14.
  cut (config_node_OK cfg l).  intro H15.  cut (is_internal_node cfg l -> nat_of_N (var cfg l) < m).
  intro H16.  exact (proj1 (BDDneg_2_lemma m cfg l H0 H15 H16)).  intro H16.  apply lt_trans_1 with (y := nat_of_N (var cfg node)).
  cut (l = low cfg node).  intro H17.  rewrite H17.  apply BDDcompare_lt.  apply BDDvar_ordered_low.
  assumption.  split with x; split with l; split with r; assumption.  rewrite <- H17; assumption.
  unfold low in |- *; simpl in H4; rewrite H4.  reflexivity.  rewrite <- H5; apply H3.
  simpl in |- *.  split with x; split with l; split with r; assumption.  cut (l = low cfg node).
  intro H15.  rewrite H15.  apply low_OK.  assumption.  split with x; split with l; split with r; assumption.
  unfold low in |- *; simpl in H4; rewrite H4; reflexivity.  elim H11; intro.  rewrite H9 in H7.
  rewrite H12 in H7.  inversion H7.  inversion H13.  inversion H14.  cut (BDDconfig_OK (fst (BDDneg_2 cfg l m))).
  intro H16.  rewrite (config_OK_one (fst (BDDneg_2 cfg l m)) H16) in H15.  discriminate H15.
  cut (config_node_OK cfg l).  intro H16.  cut (is_internal_node cfg l -> nat_of_N (var cfg l) < m).





  intros H17.  exact (proj1 (BDDneg_2_lemma m cfg l H0 H16 H17)).  intro H17.
  apply lt_trans_1 with (y := nat_of_N (var cfg node)).  cut (l = low cfg node).  
  intro H18.  rewrite H18.  apply BDDcompare_lt.  apply BDDvar_ordered_low.  assumption.
  split with x; split with l; split with r.  assumption.  rewrite <- H18; assumption.
  unfold low in |- *.  simpl in H4.  rewrite H4.  reflexivity.  rewrite <- H5.  apply H3.
  simpl in |- *.  split with x; split with l; split with r; assumption.  cut (l = low cfg node); intros.
  rewrite H16.  apply low_OK.  assumption.  split with x; split with l; split with r; assumption.
  unfold low in |- *; simpl in H4; rewrite H4; reflexivity.  apply in_dom_is_internal.
  assumption.  apply high_OK.  assumption.  split with x; split with l; split with r; assumption.
  unfold high in |- *.  simpl in H4; rewrite H4; reflexivity.  rewrite <- H5; apply H3.
  simpl in |- *.  split with x; split with l; split with r; assumption.  inversion H7.
  inversion H8.  inversion H9.  unfold var in |- *.  rewrite H10.  cut (l = low cfg node).
  cut (r = high cfg node).  intros H11 H12.  cut (config_node_OK cfg l).  cut (config_node_OK cfg r).
  intros H13 H14.  cut (BDDconfig_OK (fst (BDDneg_2 cfg l m))).  intro H15.  elim H13; intro.







  rewrite H16 in H10.  rewrite (config_OK_zero (fst (BDDneg_2 cfg l m)) H15) in H10; discriminate.
  elim H16; intro.  rewrite H17 in H10.  rewrite (config_OK_one (fst (BDDneg_2 cfg l m)) H15) in H10; discriminate.
  elim (option_sum _ (MapGet (BDDvar * (ad * ad)) (fst cfg) r)).  intro y0.  elim y0; intro x3.
  elim x3; intro y1; intro y2.  elim y2; intros y3 y4 y5.  rewrite y5.  cut (is_internal_node cfg l -> nat_of_N (var cfg l) < m).
  intro H18.  cut
   (MapGet (BDDvar * (ad * ad)) (fst (fst (BDDneg_2 cfg l m))) r =
    Some (y1, (y3, y4))).
  intro H19.  rewrite H19 in H10.  injection H10.  intros H20 H21 H22.  rewrite H22; reflexivity.
  exact (proj1 (proj2 (BDDneg_2_lemma m cfg l H0 H14 H18)) y1 y3 y4 r y5).
  intro H18.  apply lt_trans_1 with (y := nat_of_N (var cfg node)).  apply BDDcompare_lt.
  rewrite H12.  apply BDDvar_ordered_low.  assumption.  split with x; split with l; split with r; assumption.
  rewrite <- H12.  assumption.  rewrite <- H5.  apply H3.  simpl in |- *.  split with x; split with l; split with r; assumption.
  intro y0.  unfold in_dom in H17.  rewrite y0 in H17.  discriminate.  cut (is_internal_node cfg l -> nat_of_N (var cfg l) < m).
  intro H15.  exact (proj1 (BDDneg_2_lemma m cfg l H0 H14 H15)).  intro H15.  apply lt_trans_1 with (y := nat_of_N (var cfg node)).






  apply BDDcompare_lt.  rewrite H12.  apply BDDvar_ordered_low.  assumption.  
 split with x; split with l; split with r; assumption.  rewrite <- H12; assumption.
  rewrite <- H5; apply H3.  simpl in |- *.  split with x; split with l; split with r; assumption.
  rewrite H11.  apply high_OK.  assumption.  split with x; split with l; split with r; assumption.
  rewrite H12.  apply low_OK.  assumption.  split with x; split with l; split with r; assumption.
  unfold high in |- *; simpl in H4; rewrite H4; reflexivity.  unfold low in |- *; simpl in H4; rewrite H4; reflexivity.  
  apply H.  rewrite H5.  unfold lt in |- *.  apply le_n.  simpl in |- *.  assumption.  simpl in |- *.
  cut (l = low cfg node).  intro; rewrite H6.  apply low_OK.  assumption.  
  split with x; split with l; split with r; assumption.  unfold low in |- *; simpl in H4; rewrite H4; reflexivity.
  simpl in |- *.  assumption.  simpl in |- *.  intro H6.  apply lt_trans_1 with (y := nat_of_N (var cfg node)).
  apply BDDcompare_lt.  cut (l = low cfg node).  intro H7.  rewrite H7.  apply BDDvar_ordered_low.
  assumption.  split with x; split with l; split with r; assumption.  rewrite <- H7; assumption.
  unfold low in |- *; simpl in H4; rewrite H4; reflexivity.  rewrite <- H5; apply H3.
  simpl in |- *.  split with x; split with l; split with r; assumption.  intro y0.  rewrite y0.
  rewrite (BDDneg_1_lemma_3 (cfg, node, memo) x l r y H4).  simpl in |- *.  simpl in H4.
  rewrite H4.  split.  reflexivity.  unfold BDDneg_memo_OK_2 in |- *.  intros node0 node' bound0 H5 H6.  unfold BDDneg_memo_lookup in H5.
  rewrite (newMap_semantics ad node0) in H5.  discriminate.  simpl in |- *.  intro y0.  rewrite (BDDneg_1_lemma_2 (cfg, node, memo) n y y0).
  simpl in |- *.  unfold BDDneg_2 in |- *.  elim n; rewrite y0.  elim (Neqb node BDDzero).











  simpl in |- *.  split.  reflexivity.  apply BDDneg_memo_OK_1_lemma_2_1'.  assumption.
  assumption.  simpl in |- *.  split.  reflexivity.  apply BDDneg_memo_OK_1_lemma_3_1'.
  assumption. assumption.
  fold BDDneg_2 in |- *.  intro n0.  intro H4.  elim (Neqb node BDDzero).  simpl in |- *.  split.
  reflexivity.  apply BDDneg_memo_OK_1_lemma_2_1'.  assumption.  assumption.
  simpl in |- *.  split.
  reflexivity.  apply BDDneg_memo_OK_1_lemma_3_1'.  assumption.  assumption.
Qed.