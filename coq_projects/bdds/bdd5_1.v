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

Definition BDDneg_memo_OK_1 (cfg : BDDconfig) (memo : BDDneg_memo) :=
  forall (node node' : ad) (bound : nat),
  config_node_OK cfg node ->
  BDDneg_memo_lookup memo node = Some node' ->
  (is_internal_node cfg node -> nat_of_N (var cfg node) < bound) ->
  BDDneg_2 cfg node bound = (cfg, node').

Definition BDDneg_memo_OK_2 (cfg : BDDconfig) (memo : BDDneg_memo) :=
  forall (node node' : ad) (bound : nat),
  BDDneg_memo_lookup memo node = Some node' ->
  (is_internal_node cfg node -> nat_of_N (var cfg node) < bound) ->
  config_node_OK cfg node /\ BDDneg_2 cfg node bound = (cfg, node').

Fixpoint BDDneg_1 (arg : BDDconfig * ad * BDDneg_memo) 
 (bound : nat) {struct bound} : BDDconfig * ad * BDDneg_memo :=
  match BDDneg_memo_lookup (snd arg) (snd (fst arg)) with
  | Some node => (fst (fst arg), node, snd arg)
  | None =>
      match MapGet _ (fst (fst (fst arg))) (snd (fst arg)) with
      | None =>
          if Neqb (snd (fst arg)) BDDzero
          then
           (fst (fst arg), BDDone, BDDneg_memo_put (snd arg) BDDzero BDDone)
          else
           (fst (fst arg), BDDzero, BDDneg_memo_put (snd arg) BDDone BDDzero)
      | Some (x, (l, r)) =>
          match bound with
          | O => (initBDDconfig, BDDzero, newMap ad)
          | S bound' =>
              (BDDmake
                 (fst
                    (fst
                       (BDDneg_1
                          (fst
                             (fst
                                (BDDneg_1 (fst (fst arg), l, snd arg) bound')),
                          r,
                          snd (BDDneg_1 (fst (fst arg), l, snd arg) bound'))
                          bound'))) x
                 (snd (fst (BDDneg_1 (fst (fst arg), l, snd arg) bound')))
                 (snd
                    (fst
                       (BDDneg_1
                          (fst
                             (fst
                                (BDDneg_1 (fst (fst arg), l, snd arg) bound')),
                          r,
                          snd (BDDneg_1 (fst (fst arg), l, snd arg) bound'))
                          bound'))),
              BDDneg_memo_put
                (snd
                   (BDDneg_1
                      (fst
                         (fst (BDDneg_1 (fst (fst arg), l, snd arg) bound')),
                      r, snd (BDDneg_1 (fst (fst arg), l, snd arg) bound'))
                      bound')) (snd (fst arg))
                (snd
                   (BDDmake
                      (fst
                         (fst
                            (BDDneg_1
                               (fst
                                  (fst
                                     (BDDneg_1 (fst (fst arg), l, snd arg)
                                        bound')), r,
                               snd
                                 (BDDneg_1 (fst (fst arg), l, snd arg) bound'))
                               bound'))) x
                      (snd
                         (fst (BDDneg_1 (fst (fst arg), l, snd arg) bound')))
                      (snd
                         (fst
                            (BDDneg_1
                               (fst
                                  (fst
                                     (BDDneg_1 (fst (fst arg), l, snd arg)
                                        bound')), r,
                               snd
                                 (BDDneg_1 (fst (fst arg), l, snd arg) bound'))
                               bound'))))))
          end
      end
  end.

Lemma BDDneg_1_lemma_1 :
 forall (arg : BDDconfig * ad * BDDneg_memo) (node : ad) (bound : nat),
 BDDneg_memo_lookup (snd arg) (snd (fst arg)) = Some node ->
 BDDneg_1 arg bound = (fst (fst arg), node, snd arg).
Proof.
  intro arg.  elim arg.  clear arg. intro y.  elim y; clear y.  intros cfg node memo node' bound.
  intros H.  unfold BDDneg_1 in |- *.  simpl in |- *.  elim bound; rewrite H; simpl in |- *.  reflexivity.
reflexivity.
Qed.

Lemma BDDneg_1_lemma_2 :
 forall (arg : BDDconfig * ad * BDDneg_memo) (bound : nat),
 BDDneg_memo_lookup (snd arg) (snd (fst arg)) = None ->
 MapGet _ (fst (fst (fst arg))) (snd (fst arg)) = None ->
 BDDneg_1 arg bound =
 (if Neqb (snd (fst arg)) BDDzero
  then (fst (fst arg), BDDone, BDDneg_memo_put (snd arg) BDDzero BDDone)
  else (fst (fst arg), BDDzero, BDDneg_memo_put (snd arg) BDDone BDDzero)).
Proof.
  intro arg.  elim arg.  clear arg; intro y.  elim y; clear y.  intros cfg node memo bound.
  intros H H0.  unfold BDDneg_1 in |- *.  simpl in |- *.  elim bound; rewrite H; simpl in |- *.  simpl in H0.
  rewrite H0; reflexivity.  fold BDDneg_1 in |- *.  simpl in H0.  rewrite H0.  reflexivity.
Qed.

Lemma BDDneg_1_lemma_3 :
 forall (arg : BDDconfig * ad * BDDneg_memo) (x : BDDvar) (l r : ad),
 BDDneg_memo_lookup (snd arg) (snd (fst arg)) = None ->
 MapGet _ (fst (fst (fst arg))) (snd (fst arg)) = Some (x, (l, r)) ->
 BDDneg_1 arg 0 = (initBDDconfig, BDDzero, newMap ad).
Proof.
  intro arg.  elim arg.  clear arg; intro y.  elim y; clear y.  intros cfg node memo x l r.
  intros H H0.  simpl in |- *.  simpl in H, H0.  rewrite H.  rewrite H0.  reflexivity.
Qed.

Lemma nat_sum : forall n : nat, {m : nat | n = S m} + {n = 0}.
Proof.
  intro n.  elim n.  right.  reflexivity.  intros n0 H.  left.  split with n0.  reflexivity.
Qed.

Lemma BDDneg_1_lemma_4 :
 forall (arg : BDDconfig * ad * BDDneg_memo) (x : BDDvar) 
   (l r : ad) (bound bound' : nat),
 bound = S bound' ->
 BDDneg_memo_lookup (snd arg) (snd (fst arg)) = None ->
 MapGet _ (fst (fst (fst arg))) (snd (fst arg)) = Some (x, (l, r)) ->
 BDDneg_1 arg bound =
 (BDDmake
    (fst
       (fst
          (BDDneg_1
             (fst (fst (BDDneg_1 (fst (fst arg), l, snd arg) bound')), r,
             snd (BDDneg_1 (fst (fst arg), l, snd arg) bound')) bound'))) x
    (snd (fst (BDDneg_1 (fst (fst arg), l, snd arg) bound')))
    (snd
       (fst
          (BDDneg_1
             (fst (fst (BDDneg_1 (fst (fst arg), l, snd arg) bound')), r,
             snd (BDDneg_1 (fst (fst arg), l, snd arg) bound')) bound'))),
 BDDneg_memo_put
   (snd
      (BDDneg_1
         (fst (fst (BDDneg_1 (fst (fst arg), l, snd arg) bound')), r,
         snd (BDDneg_1 (fst (fst arg), l, snd arg) bound')) bound'))
   (snd (fst arg))
   (snd
      (BDDmake
         (fst
            (fst
               (BDDneg_1
                  (fst (fst (BDDneg_1 (fst (fst arg), l, snd arg) bound')),
                  r, snd (BDDneg_1 (fst (fst arg), l, snd arg) bound'))
                  bound'))) x
         (snd (fst (BDDneg_1 (fst (fst arg), l, snd arg) bound')))
         (snd
            (fst
               (BDDneg_1
                  (fst (fst (BDDneg_1 (fst (fst arg), l, snd arg) bound')),
                  r, snd (BDDneg_1 (fst (fst arg), l, snd arg) bound'))
                  bound')))))).
Proof.
  intro arg.  elim arg.  clear arg; intro y.  elim y; clear y.  intros cfg node memo x l r.
  intros bound bound' H H0 H1.  elim (nat_sum bound).  intro y.  elim y; clear y; intros x0 y.  rewrite H in y.
  injection y; intro.  rewrite H.  simpl in |- *.  simpl in H0, H1.  rewrite H0; rewrite H1.
  reflexivity.  intro y.  rewrite H in y; discriminate.
Qed.

Lemma bool_fun_restrict_neg_1 :
 forall (bf : bool_fun) (x : BDDvar) (b : bool),
 bool_fun_ext bf ->
 bool_fun_eq (bool_fun_restrict (bool_fun_neg bf) x b)
   (bool_fun_neg (bool_fun_restrict bf x b)).
Proof.
  intros bf x b H.  unfold bool_fun_eq in |- *.  unfold bool_fun_restrict in |- *.  unfold bool_fun_eval at 2 in |- *.
  intro vb.  unfold bool_fun_neg in |- *.  unfold bool_fun_eval at 3 in |- *.  reflexivity.
Qed.

Lemma bool_fun_neg_eq_var_2 :
 forall (cfg : BDDconfig) (node node' : ad),
 BDDconfig_OK cfg ->
 is_internal_node cfg node ->
 is_internal_node cfg node' ->
 bool_fun_eq (bool_fun_of_BDD cfg node')
   (bool_fun_neg (bool_fun_of_BDD cfg node)) -> var cfg node = var cfg node'.
Proof.
  intro cfg.  elim cfg; clear cfg; intros bs y; elim y; clear y; intros share counter.
  intros node node' H H0 H1 H2.  cut
   (BDDconfig_OK
      (fst
         (BDDneg_2 (bs, (share, counter)) node
            (S (nat_of_N (var (bs, (share, counter)) node))))) /\
    (forall (x : BDDvar) (l r a : ad),
     MapGet _ (fst (bs, (share, counter))) a = Some (x, (l, r)) ->
     MapGet _
       (fst
          (fst
             (BDDneg_2 (bs, (share, counter)) node
                (S (nat_of_N (var (bs, (share, counter)) node)))))) a =
     Some (x, (l, r))) /\
    (is_internal_node (bs, (share, counter)) node ->
     is_internal_node
       (fst
          (BDDneg_2 (bs, (share, counter)) node
             (S (nat_of_N (var (bs, (share, counter)) node)))))
       (snd
          (BDDneg_2 (bs, (share, counter)) node
             (S (nat_of_N (var (bs, (share, counter)) node))))) /\
     var (bs, (share, counter)) node =
     var
       (fst
          (BDDneg_2 (bs, (share, counter)) node
             (S (nat_of_N (var (bs, (share, counter)) node)))))
       (snd
          (BDDneg_2 (bs, (share, counter)) node
             (S (nat_of_N (var (bs, (share, counter)) node)))))) /\
    config_node_OK
      (fst
         (BDDneg_2 (bs, (share, counter)) node
            (S (nat_of_N (var (bs, (share, counter)) node)))))
      (snd
         (BDDneg_2 (bs, (share, counter)) node
            (S (nat_of_N (var (bs, (share, counter)) node))))) /\
    bool_fun_eq
      (bool_fun_of_BDD
         (fst
            (BDDneg_2 (bs, (share, counter)) node
               (S (nat_of_N (var (bs, (share, counter)) node)))))
         (snd
            (BDDneg_2 (bs, (share, counter)) node
               (S (nat_of_N (var (bs, (share, counter)) node))))))
      (bool_fun_neg (bool_fun_of_BDD (bs, (share, counter)) node))).
  intro H3.  cut
   (var (bs, (share, counter)) node' =
    var
      (fst
         (BDDneg_2 (bs, (share, counter)) node
            (S (nat_of_N (var (bs, (share, counter)) node))))) node').
  intro H4.  cut
   (var (bs, (share, counter)) node =
    var
      (fst
         (BDDneg_2 (bs, (share, counter)) node
            (S (nat_of_N (var (bs, (share, counter)) node)))))
      (snd
         (BDDneg_2 (bs, (share, counter)) node
            (S (nat_of_N (var (bs, (share, counter)) node)))))).
  intro H5.  rewrite H5.  rewrite H4.  cut
   (snd
      (BDDneg_2 (bs, (share, counter)) node
         (S (nat_of_N (var (bs, (share, counter)) node)))) = node').
  intro H6.  rewrite H6.  reflexivity.  apply
   BDDunique
    with
      (cfg := fst
                (BDDneg_2 (bs, (share, counter)) node
                   (S (nat_of_N (var (bs, (share, counter)) node))))).
  exact (proj1 H3).  exact (proj1 (proj2 (proj2 (proj2 H3)))).  
  inversion H1.  inversion H6.  inversion H7.  right.  right.  unfold in_dom in |- *.
  rewrite (proj1 (proj2 H3) x x0 x1 node' H8).  reflexivity.  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_neg (bool_fun_of_BDD (bs, (share, counter)) node)).
  exact (proj2 (proj2 (proj2 (proj2 H3)))).  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_of_BDD (bs, (share, counter)) node').
  apply bool_fun_eq_symm; assumption.  apply bool_fun_eq_symm.  apply bool_fun_preservation.
  assumption.  exact (proj1 H3).  exact (proj1 (proj2 H3)).  right.
  right.  unfold in_dom in |- *.  inversion H1.  inversion H6.  inversion H7.  rewrite H8; reflexivity.
  exact (proj2 (proj1 (proj2 (proj2 H3)) H0)).  inversion H1.  inversion H4.
  inversion H5.  unfold var at 1 2 in |- *.  rewrite (proj1 (proj2 H3) x x0 x1 node' H6).
  rewrite H6.  reflexivity.  apply BDDneg_2_lemma.  assumption.  right.  right.
  inversion H0.  inversion H3.  inversion H4.  unfold in_dom in |- *; rewrite H5; reflexivity.
  intro H3.  unfold lt in |- *.  apply le_n.  
Qed.

Lemma BDDneg_memo_OK_1_lemma_1_1_1 :
 forall (bound : nat) (cfg : BDDconfig) (node node' : ad),
 BDDconfig_OK cfg ->
 config_node_OK cfg node ->
 config_node_OK cfg node' ->
 (is_internal_node cfg node -> nat_of_N (var cfg node) < bound) ->
 bool_fun_eq (bool_fun_of_BDD cfg node')
   (bool_fun_neg (bool_fun_of_BDD cfg node)) ->
 BDDneg_2 cfg node bound = (cfg, node').
Proof.
  intro bound.  apply
   lt_wf_ind
    with
      (P := fun bound : nat =>
            forall (cfg : BDDconfig) (node node' : ad),
            BDDconfig_OK cfg ->
            config_node_OK cfg node ->
            config_node_OK cfg node' ->
            (is_internal_node cfg node -> nat_of_N (var cfg node) < bound) ->
            bool_fun_eq (bool_fun_of_BDD cfg node')
              (bool_fun_neg (bool_fun_of_BDD cfg node)) ->
            BDDneg_2 cfg node bound = (cfg, node')).
  intros n H.  intro cfg.  elim cfg; clear cfg; intros bs y; elim y; clear y; intros share counter.
  intros node node' H0 H1 H2 H3 H4.  elim H1; intro.  cut (node' = BDDone).  intro H6.  rewrite H5.  rewrite H6.
  elim n.  unfold BDDneg_2 in |- *.  rewrite (config_OK_zero (bs, (share, counter)) H0).  
  cut (Neqb BDDzero BDDzero = true).  intro H7.  rewrite H7.  reflexivity.  apply Neqb_correct.
  intros n0 H7.  unfold BDDneg_2 in |- *.  fold BDDneg_2 in |- *.  rewrite (config_OK_zero (bs, (share, counter)) H0).
  cut (Neqb BDDzero BDDzero = true).  intro H8.  rewrite H8.  reflexivity.  apply Neqb_correct.
  rewrite H5 in H4.  rewrite (proj1 (bool_fun_of_BDD_semantics (bs, (share, counter)) H0)) in H4.
  rewrite bool_fun_neg_zero in H4.  rewrite <-
   (proj1 (proj2 (bool_fun_of_BDD_semantics (bs, (share, counter)) H0)))
    in H4.
  apply BDDunique with (cfg := (bs, (share, counter))).  assumption.  assumption.  right; left; reflexivity.
  assumption.  elim H5; clear H5; intro.  cut (node' = BDDzero).  intro H6.  rewrite H5.
  rewrite H6.  elim n.  unfold BDDneg_2 in |- *.  rewrite (config_OK_one (bs, (share, counter)) H0).
  cut (Neqb BDDone BDDzero = false).  intro H7.  rewrite H7.  reflexivity.  simpl in |- *.
  reflexivity.  intros n0 H7.  unfold BDDneg_2 in |- *.  fold BDDneg_2 in |- *.  rewrite (config_OK_one (bs, (share, counter)) H0).
  cut (Neqb BDDone BDDzero = false).  intro H8.  rewrite H8.  reflexivity.  reflexivity.
  rewrite H5 in H4.  rewrite
   (proj1 (proj2 (bool_fun_of_BDD_semantics (bs, (share, counter)) H0)))
    in H4.
  rewrite bool_fun_neg_one in H4.  rewrite <- (proj1 (bool_fun_of_BDD_semantics (bs, (share, counter)) H0))
    in H4.
  apply BDDunique with (cfg := (bs, (share, counter))).  assumption.  assumption.  left; reflexivity.
  assumption.  elim (nat_sum n); intro y.  elim y; clear y.  intros m H6.  rewrite H6.
  simpl in |- *.  cut (is_internal_node (bs, (share, counter)) node).  intro H7.  inversion H7.
  inversion H8.  inversion H9.  simpl in H10.  rewrite H10.  cut (is_internal_node (bs, (share, counter)) node').
  intro H11.  inversion H11.  inversion H12.  inversion H13.  clear H8 H9 H12 H13.
  cut (BDDneg_2 (bs, (share, counter)) x0 m = (bs, (share, counter), x3)).  intro H8.  rewrite H8.
  simpl in |- *.  cut (BDDneg_2 (bs, (share, counter)) x1 m = (bs, (share, counter), x4)).  intro H9.
  rewrite H9.  simpl in |- *.  unfold BDDmake in |- *.  simpl in |- *.  cut (Neqb x3 x4 = false).  intro H12.
  rewrite H12.  elim H0.  intros H13 H15.  unfold BDDsharing_OK in H15.  cut (x = x2).  intro H16.
  rewrite H16.  rewrite (proj2 (proj1 H15 x2 x3 x4 node') H14).  reflexivity.
  cut (x = var (bs, (share, counter)) node).  cut (x2 = var (bs, (share, counter)) node').
  intros H16 H17.  rewrite H16.  rewrite H17.  apply bool_fun_neg_eq_var_2 with (cfg := (bs, (share, counter))).
  assumption.  assumption.  assumption.  assumption.  unfold var in |- *.  rewrite H14.
  reflexivity.  unfold var in |- *.  simpl in |- *; rewrite H10; reflexivity.  cut (x3 = low (bs, (share, counter)) node').
  cut (x4 = high (bs, (share, counter)) node').  intros H12 H13.  rewrite H13.  rewrite H12.
  apply low_high_neq.  assumption.  assumption.  unfold high in |- *; rewrite H14; reflexivity.
  unfold low in |- *; rewrite H14; reflexivity.  cut (x1 = high (bs, (share, counter)) node).
  cut (x4 = high (bs, (share, counter)) node').  intros H9 H12.  rewrite H9; rewrite H12.
  apply H.  rewrite H6.  unfold lt in |- *.  apply le_n.  assumption.  apply high_OK.  assumption.
  assumption.  apply high_OK.  assumption.  assumption.  intro H13.  apply lt_trans_1 with (y := nat_of_N (var (bs, (share, counter)) node)).
  apply BDDcompare_lt.  apply BDDvar_ordered_high.  assumption.  assumption.
  assumption.  rewrite <- H6; apply H3.  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_restrict
                (bool_fun_of_BDD (bs, (share, counter)) node')
                (var (bs, (share, counter)) node') true).
  apply bool_fun_of_BDDhigh.  assumption.  assumption.  apply
   bool_fun_eq_trans
    with
      (bool_fun_restrict
         (bool_fun_neg (bool_fun_of_BDD (bs, (share, counter)) node))
         (var (bs, (share, counter)) node') true).
  apply bool_fun_restrict_eq.  assumption.  cut (var (bs, (share, counter)) node = var (bs, (share, counter)) node').
  intro H13.  rewrite <- H13.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_neg
                (bool_fun_restrict
                   (bool_fun_of_BDD (bs, (share, counter)) node)
                   (var (bs, (share, counter)) node) true)).
  apply bool_fun_restrict_neg_1.  apply bool_fun_of_BDD_ext.  apply bool_fun_eq_neg_1.  apply bool_fun_eq_symm.
  apply bool_fun_of_BDDhigh.  assumption.  assumption.  apply bool_fun_neg_eq_var_2.
  assumption.  assumption.  assumption.  assumption.  unfold high in |- *; rewrite H14; reflexivity.
  unfold high in |- *; simpl in |- *; rewrite H10; reflexivity.  cut (x0 = low (bs, (share, counter)) node).
  cut (x3 = low (bs, (share, counter)) node').  intros H8 H9.  rewrite H8; rewrite H9.
  apply H.  rewrite H6.  unfold lt in |- *.  apply le_n.  assumption.  apply low_OK.
  assumption.  assumption.  apply low_OK.  assumption.  assumption.  intros H12.
  apply lt_trans_1 with (y := nat_of_N (var (bs, (share, counter)) node)).  apply BDDcompare_lt.
  apply BDDvar_ordered_low.  assumption.  assumption.  assumption.  rewrite <- H6; apply H3.
  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_restrict
                (bool_fun_of_BDD (bs, (share, counter)) node')
                (var (bs, (share, counter)) node') false).
  apply bool_fun_of_BDDlow.  assumption.  assumption.  apply
   bool_fun_eq_trans
    with
      (bool_fun_restrict
         (bool_fun_neg (bool_fun_of_BDD (bs, (share, counter)) node))
         (var (bs, (share, counter)) node') false).
  apply bool_fun_restrict_eq.  assumption.  cut (var (bs, (share, counter)) node = var (bs, (share, counter)) node').
  intro H12.  rewrite <- H12.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_neg
                (bool_fun_restrict
                   (bool_fun_of_BDD (bs, (share, counter)) node)
                   (var (bs, (share, counter)) node) false)).
  apply bool_fun_restrict_neg_1.  apply bool_fun_of_BDD_ext. apply bool_fun_eq_neg_1.  apply bool_fun_eq_symm.
  apply bool_fun_of_BDDlow.  assumption.  assumption.  apply bool_fun_neg_eq_var_2.
  assumption.  assumption.  assumption.  assumption.  unfold low in |- *; rewrite H14; reflexivity.
  unfold low in |- *; simpl in |- *; rewrite H10; reflexivity.  elim H2; intro.  rewrite H11 in H4.
  rewrite (proj1 (bool_fun_of_BDD_semantics (bs, (share, counter)) H0)) in H4.
  rewrite <- bool_fun_neg_one in H4.  absurd
   (bool_fun_eq bool_fun_one (bool_fun_of_BDD (bs, (share, counter)) node)).
  apply bool_fun_neq_lemma.  exact
   (proj2 (internal_node_not_constant (bs, (share, counter)) node H0 H7)).
  apply bool_fun_eq_neg.  assumption.  elim H11; clear H11; intro.  rewrite H11 in H4.
  rewrite
   (proj1 (proj2 (bool_fun_of_BDD_semantics (bs, (share, counter)) H0)))
    in H4.
  rewrite <- bool_fun_neg_zero in H4.  absurd
   (bool_fun_eq bool_fun_zero (bool_fun_of_BDD (bs, (share, counter)) node)).
  apply bool_fun_neq_lemma.  exact
   (proj1 (internal_node_not_constant (bs, (share, counter)) node H0 H7)).
  apply bool_fun_eq_neg.  assumption.  apply in_dom_is_internal.  assumption.
  apply in_dom_is_internal.  assumption.  absurd (nat_of_N (var (bs, (share, counter)) node) < n).
  rewrite y.  apply lt_n_O.  apply H3.  apply in_dom_is_internal.  assumption.
Qed.

Lemma BDDneg_memo_OK_1_2 :
 forall (cfg : BDDconfig) (memo : BDDneg_memo),
 BDDneg_memo_OK_2 cfg memo -> BDDneg_memo_OK_1 cfg memo.
Proof.
  unfold BDDneg_memo_OK_1 in |- *.  unfold BDDneg_memo_OK_2 in |- *.  intros cfg memo H node node' bound H0 H1 H2.  exact (proj2 (H node node' bound H1 H2)).
Qed.

Lemma BDDneg_memo_OK_bool_fun_1 :
 forall (cfg : BDDconfig) (memo : BDDneg_memo) (node node' : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_1 cfg memo ->
 config_node_OK cfg node ->
 BDDneg_memo_lookup memo node = Some node' ->
 bool_fun_eq (bool_fun_of_BDD cfg node')
   (bool_fun_neg (bool_fun_of_BDD cfg node)).
Proof.
  intro cfg.  elim cfg; clear cfg.  intros bs y.  elim y; clear y; intros share counter.
  intros memo node node' H H0 H1 H2.  unfold BDDneg_memo_OK_1 in H0.  cut
   (BDDneg_2 (bs, (share, counter)) node
      (S (nat_of_N (var (bs, (share, counter)) node))) =
    (bs, (share, counter), node')).
  intro H3.  cut
   (is_internal_node (bs, (share, counter)) node ->
    nat_of_N (var (bs, (share, counter)) node) <
    S (nat_of_N (var (bs, (share, counter)) node))).
  intro H4.  cut
   (bool_fun_of_BDD (bs, (share, counter)) node' =
    bool_fun_of_BDD
      (fst
         (BDDneg_2 (bs, (share, counter)) node
            (S (nat_of_N (var (bs, (share, counter)) node)))))
      (snd
         (BDDneg_2 (bs, (share, counter)) node
            (S (nat_of_N (var (bs, (share, counter)) node)))))).
  intro H5.  rewrite H5.  exact
   (proj2
      (proj2
         (proj2
            (proj2
               (BDDneg_2_lemma
                  (S (nat_of_N (var (bs, (share, counter)) node)))
                  (bs, (share, counter)) node H H1 H4))))).
  rewrite H3.  simpl in |- *.  reflexivity.  intro H4.  unfold lt in |- *; apply le_n.  apply H0.
  assumption.  assumption.  intro H3.  unfold lt in |- *; apply le_n.
Qed.

Lemma BDDneg_memo_OK_bool_fun_1' :
 forall (cfg : BDDconfig) (memo : BDDneg_memo) (node node' : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg memo ->
 config_node_OK cfg node ->
 BDDneg_memo_lookup memo node = Some node' ->
 bool_fun_eq (bool_fun_of_BDD cfg node')
   (bool_fun_neg (bool_fun_of_BDD cfg node)).
Proof.
  intros cfg memo node node' H H0 H1 H2.  apply BDDneg_memo_OK_bool_fun_1 with (memo := memo).  assumption.  
  apply BDDneg_memo_OK_1_2.  assumption.  assumption.  assumption.
Qed.

Definition nodes_preserved (cfg cfg' : BDDconfig) :=
  forall (x : BDDvar) (l r node : ad),
  MapGet _ (fst cfg) node = Some (x, (l, r)) ->
  MapGet _ (fst cfg') node = Some (x, (l, r)).

Lemma BDDmake_preserves_nodes :
 forall (cfg : BDDconfig) (x : BDDvar) (l r : ad),
 BDDconfig_OK cfg -> nodes_preserved cfg (fst (BDDmake cfg x l r)).
Proof.
  intro cfg.  elim cfg; clear cfg.  intros bs y.  elim y; clear y; intros share counter.
  intros x l r H00.  unfold nodes_preserved in |- *.  unfold BDDmake in |- *.  elim (sumbool_of_bool (Neqb l r)).
  intro y.  rewrite y.  simpl in |- *.  intros; assumption.  intro y.  rewrite y.  simpl in |- *.
  elim (option_sum _ (BDDshare_lookup share x l r)).  intro y0.  inversion y0.  rewrite H.
  simpl in |- *.  intros x1 l0 r0 node H0.  assumption.  intro y0.  rewrite y0.  simpl in |- *.  elim H00.  intros H H0 x0 l0 r0 node H1.
  rewrite (MapPut_semantics (BDDvar * (ad * ad)) bs counter (x, (l, r)) node).  elim (sumbool_of_bool (Neqb counter node)).  intro y1.  absurd (counter = node).  unfold not in |- *; intro.  cut (MapGet (BDDvar * (ad * ad)) bs node = None).
  intro H3.  rewrite H1 in H3; discriminate.  apply (proj1 (proj2 H0)).
  rewrite H2.  unfold Nleb in |- *.  apply leb_correct.  apply le_n.  apply Neqb_complete.
  assumption.  intro y1.  rewrite y1.  assumption.  
Qed.

Lemma nodes_preserved_2 :
 forall (cfg cfg' : BDDconfig) (node : ad),
 config_node_OK cfg node ->
 nodes_preserved cfg cfg' -> config_node_OK cfg' node.
Proof.
  intros cfg cfg' node H H0.  elim H; intro.  rewrite H1.  left; reflexivity.  elim H1; intro.
  rewrite H2; right; left; reflexivity.  right; right.  unfold in_dom in H2.
  elim (option_sum _ (MapGet (BDDvar * (ad * ad)) (fst cfg) node)).  intro y.  elim y.
  intros x.  elim x.  intro y0.  intro y1.  elim y1.  intros y2 y3 y4.  unfold nodes_preserved in H0.
  unfold in_dom in |- *.  rewrite (H0 y0 y2 y3 node y4).  reflexivity.  intro y.  rewrite y in H2.
  discriminate.
Qed.

Lemma BDDneg_2_config_OK_lemma_2 :
 forall (cfg : BDDconfig) (node : ad) (x : BDDvar) (l r : ad) (n m : nat),
 BDDconfig_OK cfg ->
 MapGet _ (fst cfg) node = Some (x, (l, r)) ->
 nat_of_N (var cfg node) < n ->
 n = S m -> BDDconfig_OK (fst (BDDneg_2 (fst (BDDneg_2 cfg l m)) r m)).
Proof.
  intro cfg.  elim cfg; clear cfg.  intros bs y.  elim y; clear y; intros share counter.
  intros node x l r n m H H0 H1 H2.  cut
   (is_internal_node (bs, (share, counter)) node ->
    nat_of_N (var (bs, (share, counter)) node) < n).
  intro H3.  cut
   (BDDconfig_OK (fst (BDDneg_2 (bs, (share, counter)) l m)) /\
    (forall (x0 : BDDvar) (l0 r0 a : ad),
     MapGet _ (fst (bs, (share, counter))) a = Some (x0, (l0, r0)) ->
     MapGet _ (fst (fst (BDDneg_2 (bs, (share, counter)) l m))) a =
     Some (x0, (l0, r0))) /\
    (is_internal_node (bs, (share, counter)) l ->
     is_internal_node (fst (BDDneg_2 (bs, (share, counter)) l m))
       (snd (BDDneg_2 (bs, (share, counter)) l m)) /\
     var (bs, (share, counter)) l =
     var (fst (BDDneg_2 (bs, (share, counter)) l m))
       (snd (BDDneg_2 (bs, (share, counter)) l m))) /\
    config_node_OK (fst (BDDneg_2 (bs, (share, counter)) l m))
      (snd (BDDneg_2 (bs, (share, counter)) l m)) /\
    bool_fun_eq
      (bool_fun_of_BDD (fst (BDDneg_2 (bs, (share, counter)) l m))
         (snd (BDDneg_2 (bs, (share, counter)) l m)))
      (bool_fun_neg (bool_fun_of_BDD (bs, (share, counter)) l))).
  intro H4.  elim H4; clear H4; intros.  elim H5; clear H5; intros.  elim H6; clear H6; intros.
  elim H7; clear H7; intros.  cut
   (is_internal_node (fst (BDDneg_2 (bs, (share, counter)) l m)) r ->
    nat_of_N (var (fst (BDDneg_2 (bs, (share, counter)) l m)) r) < m).
  intro H9.  cut (config_node_OK (fst (BDDneg_2 (bs, (share, counter)) l m)) r).
  intro H10.  exact
   (proj1
      (BDDneg_2_lemma m (fst (BDDneg_2 (bs, (share, counter)) l m)) r H4 H10
         H9)).
  apply nodes_preserved_2 with (cfg := (bs, (share, counter))).  cut (r = high (bs, (share, counter)) node).
  intro H10.  rewrite H10.  apply high_OK.  assumption.  split with x; split with l; split with r; assumption.
  unfold high in |- *.  rewrite H0.  reflexivity.  unfold nodes_preserved in |- *.  assumption.
  intro H9.  cut
   (config_node_OK (bs, (share, counter)) (high (bs, (share, counter)) node)).
  intro H10.  unfold high in H10.  rewrite H0 in H10.  elim H10.  intro H11.  inversion H9.
  inversion H12.  inversion H13.  rewrite H11 in H14.  rewrite (config_OK_zero (fst (BDDneg_2 (bs, (share, counter)) l m)) H4)
    in H14; discriminate.
  intro H11.  elim H11; intro.  inversion H9.  inversion H13.  inversion H14.  rewrite H12 in H15.
  rewrite (config_OK_one (fst (BDDneg_2 (bs, (share, counter)) l m)) H4)
    in H15; discriminate.
  elim (option_sum _ (MapGet _ (fst (bs, (share, counter))) r)).  intro y.  elim y.
  intro x0.  elim x0.  intro y0.  intro y1.  elim y1.  intros y2 y3 y4.  cut
   (var (fst (BDDneg_2 (bs, (share, counter)) l m)) r =
    var (bs, (share, counter)) r).
  intro H13.  rewrite H13.  apply lt_trans_1 with (y := nat_of_N (var (bs, (share, counter)) node)).
  replace r with (high (bs, (share, counter)) node).  apply BDDcompare_lt.  apply BDDvar_ordered_high.
  assumption.  split with x; split with l; split with r; assumption.  unfold high in |- *.
  rewrite H0.  split with y0; split with y2; split with y3; assumption.  unfold high in |- *; rewrite H0; reflexivity.
  rewrite <- H2; assumption.  unfold var in |- *.  rewrite y4.  rewrite (H5 y0 y2 y3 r y4).
  reflexivity.  intro y.  unfold in_dom in H12.  rewrite y in H12; discriminate.
  apply high_OK.  assumption.  split with x; split with l; split with r; assumption.
  apply BDDneg_2_lemma.  assumption.  replace l with (low (bs, (share, counter)) node).
  apply low_OK.  assumption.  split with x; split with l; split with r; assumption.
  unfold low in |- *; rewrite H0; reflexivity.  intro H4.  apply lt_trans_1 with (y := nat_of_N (var (bs, (share, counter)) node)).
  apply BDDcompare_lt.  replace l with (low (bs, (share, counter)) node).  apply BDDvar_ordered_low.
  assumption.  split with x.  split with l.  split with r.  assumption.  unfold low in |- *.
  rewrite H0.  assumption.  unfold low in |- *; rewrite H0; reflexivity.  rewrite <- H2; assumption.
  intro; assumption. 
Qed.

Lemma nodes_preserved_1 :
 forall (cfg : BDDconfig) (node : ad) (n m : nat) (x : BDDvar) (l r : ad),
 BDDconfig_OK cfg ->
 MapGet _ (fst cfg) node = Some (x, (l, r)) ->
 n = S m ->
 nat_of_N (var cfg node) < n ->
 nodes_preserved (fst (BDDneg_2 (fst (BDDneg_2 cfg l m)) r m))
   (fst (BDDneg_2 cfg node n)).
Proof.
  intro cfg.  elim cfg; clear cfg.  intros bs y.  elim y; clear y; intros share counter.
  intros node n m x l r H H0 H1 H2.  rewrite H1.  simpl in |- *.  simpl in H0.  rewrite H0.  apply BDDmake_preserves_nodes.
  apply BDDneg_2_config_OK_lemma_2 with (node := node) (x := x) (n := n).  assumption.  assumption.
  assumption.  assumption.  
Qed.

Lemma BDDneg_memo_OK_lemma_1_4' :
 forall (cfg : BDDconfig) (memo : BDDneg_memo) (node node' : ad),
 BDDconfig_OK cfg ->
 BDDneg_memo_OK_2 cfg memo ->
 config_node_OK cfg node ->
 BDDneg_memo_lookup memo node = Some node' -> config_node_OK cfg node'.
Proof.
  intro cfg.  elim cfg; clear cfg; intros bs y; elim y; clear y; intros share counter.
  intros memo node node' H H0 H1 H2.  unfold BDDneg_memo_OK_2 in H0.  cut
   (config_node_OK (bs, (share, counter)) node /\
    BDDneg_2 (bs, (share, counter)) node
      (S (nat_of_N (var (bs, (share, counter)) node))) =
    (bs, (share, counter), node')).
  intro H3.  cut
   (config_node_OK
      (fst
         (BDDneg_2 (bs, (share, counter)) node
            (S (nat_of_N (var (bs, (share, counter)) node)))))
      (snd
         (BDDneg_2 (bs, (share, counter)) node
            (S (nat_of_N (var (bs, (share, counter)) node)))))).
  intro H4.  rewrite (proj2 H3) in H4.  exact H4.  cut
   (is_internal_node (bs, (share, counter)) node ->
    nat_of_N (var (bs, (share, counter)) node) <
    S (nat_of_N (var (bs, (share, counter)) node))).
  intro H4.  exact
   (proj1
      (proj2
         (proj2
            (proj2
               (BDDneg_2_lemma
                  (S (nat_of_N (var (bs, (share, counter)) node)))
                  (bs, (share, counter)) node H H1 H4))))).
  intro H4.  unfold lt in |- *.  apply le_n.  apply H0.  assumption.  unfold lt in |- *.  intro H3.  apply le_n.
Qed.