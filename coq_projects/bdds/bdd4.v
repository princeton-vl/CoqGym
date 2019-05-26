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

Lemma BDDneg_2_lemma :
 forall (bound : nat) (cfg : BDDconfig) (node : ad),
 BDDconfig_OK cfg ->
 config_node_OK cfg node ->
 (is_internal_node cfg node -> nat_of_N (var cfg node) < bound) ->
 BDDconfig_OK (fst (BDDneg_2 cfg node bound)) /\
 (forall (x : BDDvar) (l r a : ad),
  MapGet _ (fst cfg) a = Some (x, (l, r)) ->
  MapGet _ (fst (fst (BDDneg_2 cfg node bound))) a = Some (x, (l, r))) /\
 (is_internal_node cfg node ->
  is_internal_node (fst (BDDneg_2 cfg node bound))
    (snd (BDDneg_2 cfg node bound)) /\
  var cfg node =
  var (fst (BDDneg_2 cfg node bound)) (snd (BDDneg_2 cfg node bound))) /\
 config_node_OK (fst (BDDneg_2 cfg node bound))
   (snd (BDDneg_2 cfg node bound)) /\
 bool_fun_eq
   (bool_fun_of_BDD (fst (BDDneg_2 cfg node bound))
      (snd (BDDneg_2 cfg node bound)))
   (bool_fun_neg (bool_fun_of_BDD cfg node)).
Proof.
  intro bound.
  apply
   lt_wf_ind
    with
      (P := fun bound : nat =>
            forall (cfg : BDDconfig) (node : ad),
            BDDconfig_OK cfg ->
            config_node_OK cfg node ->
            (is_internal_node cfg node -> nat_of_N (var cfg node) < bound) ->
            BDDconfig_OK (fst (BDDneg_2 cfg node bound)) /\
            (forall (x : BDDvar) (l r a : ad),
             MapGet _ (fst cfg) a = Some (x, (l, r)) ->
             MapGet _ (fst (fst (BDDneg_2 cfg node bound))) a =
             Some (x, (l, r))) /\
            (is_internal_node cfg node ->
             is_internal_node (fst (BDDneg_2 cfg node bound))
               (snd (BDDneg_2 cfg node bound)) /\
             var cfg node =
             var (fst (BDDneg_2 cfg node bound))
               (snd (BDDneg_2 cfg node bound))) /\
            config_node_OK (fst (BDDneg_2 cfg node bound))
              (snd (BDDneg_2 cfg node bound)) /\
            bool_fun_eq
              (bool_fun_of_BDD (fst (BDDneg_2 cfg node bound))
                 (snd (BDDneg_2 cfg node bound)))
              (bool_fun_neg (bool_fun_of_BDD cfg node))).
  intro n.  elim n.  intro H.  intro cfg.  elim cfg.  clear cfg.  intros bs y.  elim y.   clear y.  
  intros share counter.  intros node H0 H1 H2.  unfold BDDneg_2 in |- *.
  elim
   (option_sum _
      (MapGet (BDDvar * (ad * ad)) (fst (bs, (share, counter))) node)).  intros y.
  elim y.  clear y.  intro y.  elim y.  clear y.  intros x y.  elim y.  clear y.
  intros l r.  intro y.  cut False.  tauto.  cut (~ nat_of_N (var (bs, (share, counter)) node) < 0).
  unfold not in |- *.  intro H3.  apply H3.  apply H2.  unfold is_internal_node in |- *.  split with x.
  split with l.  split with r.  assumption.  apply lt_n_O.  intro y.  rewrite y.
  elim H1.  intro H3.  rewrite H3.  simpl in |- *.  split.  exact H0.  split.  intros x l r a H4.
  assumption.  split.  split.  unfold is_internal_node in H4.  elim H4.  intros x H5.
  elim H5.  intros x0 H6.  elim H6.  intros x1 H7.  rewrite H3 in y.  rewrite y in H7.
  discriminate H7.  unfold is_internal_node in H4.  elim H4.  intros x H5.  elim H5. 
  intros x0 H6.  elim H6.  intros x1 H7.  rewrite H3 in y.  rewrite y in H7.
  discriminate H7.  split.  right.  left.  reflexivity.
  rewrite (proj1 (bool_fun_of_BDD_semantics (bs, (share, counter)) H0)).
  rewrite
   (proj1 (proj2 (bool_fun_of_BDD_semantics (bs, (share, counter)) H0)))
   .
  unfold bool_fun_eq in |- *.  unfold bool_fun_eval in |- *.  unfold bool_fun_one, bool_fun_zero, bool_fun_neg in |- *.
  simpl in |- *.  reflexivity.  intro H3.  elim H3.  clear H3.  intro H3.  rewrite H3.  simpl in |- *.
  split.  exact H0.  split.  intros x l r a H4.  assumption.  split.  split.  unfold is_internal_node in H4.  elim H4.
  intros x H5.  elim H5.  intros x0 H6.  elim H6.  intros x1 H7.  rewrite H3 in y.  rewrite y in H7.
  discriminate H7.  unfold is_internal_node in H4.  elim H4.  intros x H5.  elim H5.
  intros x0 H6.  elim H6.  intros x1 H7.  rewrite H3 in y.  rewrite y in H7.  discriminate H7.
  split.  left.  reflexivity.  rewrite (proj1 (bool_fun_of_BDD_semantics (bs, (share, counter)) H0)).
  rewrite
   (proj1 (proj2 (bool_fun_of_BDD_semantics (bs, (share, counter)) H0)))
   .
  unfold bool_fun_eq in |- *.  unfold bool_fun_eval, bool_fun_zero, bool_fun_one, bool_fun_neg in |- *.
  reflexivity.  clear H3.  intro H3.  unfold in_dom in H3.  rewrite y in H3.
  discriminate H3.  intro n0.  intro H.  intro H0.  intro cfg.  elim cfg.  clear cfg.
  intros bs y.  elim y.  clear y.  intros share counter.  intros node H1 H2 H3.  elim H2.
  intro H4.  rewrite H4.  unfold BDDneg_2 in |- *.  simpl in |- *; rewrite (proj1 (proj1 H1)).
  split.  exact H1.  split.  intros x l r a H5.  exact H5.  split.  intros H5.
  unfold is_internal_node in H5.  elim H5; intros; elim H6; intros; elim H7; intros.
  simpl in H8.  rewrite (proj1 (proj1 H1)) in H8.  discriminate H8.  
  split.  simpl in |- *.  right.  left.  reflexivity.  rewrite (proj1 (bool_fun_of_BDD_semantics (bs, (share, counter)) H1)).
  simpl in |- *.  rewrite
   (proj1 (proj2 (bool_fun_of_BDD_semantics (bs, (share, counter)) H1)))
   .
  unfold bool_fun_eq in |- *.  reflexivity.  intro; elim H4; clear H4; intro.  rewrite H4.
  simpl in |- *; rewrite (proj1 (proj2 (proj1 H1))).  split.
  unfold BDDneg_2 in |- *.  exact H1.  split.  intros x l r a H5.  exact H5.  split.  intro H5.
  unfold is_internal_node in H5.  elim H5; intros.  elim H6; intros; elim H7; intros.
  simpl in H8; rewrite (proj1 (proj2 (proj1 H1))) in H8; discriminate H8.
  split.  simpl in |- *.  left; reflexivity.  simpl in |- *;
   rewrite (proj1 (bool_fun_of_BDD_semantics (bs, (share, counter)) H1));
   rewrite
    (proj1 (proj2 (bool_fun_of_BDD_semantics (bs, (share, counter)) H1)))
    .
  unfold bool_fun_eq in |- *.  reflexivity.  elim (option_sum _ (MapGet _ (fst (bs, (share, counter))) node)).
  intros y. elim y; clear y; intro y; elim y; clear y; intros x y; elim y; clear y;
  intros l r.
  intro y.  cut (config_node_OK (bs, (share, counter)) l).  cut (config_node_OK (bs, (share, counter)) r).
  intros H5 H6.  simpl in y.  unfold BDDneg_2 in |- *; simpl in |- *; rewrite y; fold BDDneg_2 in |- *.
  cut
   (is_internal_node (bs, (share, counter)) l ->
    nat_of_N (var (bs, (share, counter)) l) < n0).
  cut
   (BDDconfig_OK (fst (BDDneg_2 (bs, (share, counter)) l n0)) /\
    (forall (x0 : BDDvar) (l0 r0 a : ad),
     MapGet _ (fst (bs, (share, counter))) a = Some (x0, (l0, r0)) ->
     MapGet _ (fst (fst (BDDneg_2 (bs, (share, counter)) l n0))) a =
     Some (x0, (l0, r0))) /\
    (is_internal_node (bs, (share, counter)) l ->
     is_internal_node (fst (BDDneg_2 (bs, (share, counter)) l n0))
       (snd (BDDneg_2 (bs, (share, counter)) l n0)) /\
     var (bs, (share, counter)) l =
     var (fst (BDDneg_2 (bs, (share, counter)) l n0))
       (snd (BDDneg_2 (bs, (share, counter)) l n0))) /\
    config_node_OK (fst (BDDneg_2 (bs, (share, counter)) l n0))
      (snd (BDDneg_2 (bs, (share, counter)) l n0)) /\
    bool_fun_eq
      (bool_fun_of_BDD (fst (BDDneg_2 (bs, (share, counter)) l n0))
         (snd (BDDneg_2 (bs, (share, counter)) l n0)))
      (bool_fun_neg (bool_fun_of_BDD (bs, (share, counter)) l))).
  intros H7 H8.  elim H7; clear H7; intros.  elim H9; clear H9; intros.  elim H10; clear H10; intros.
  elim H11; clear H11; intros.  cut (config_node_OK (fst (BDDneg_2 (bs, (share, counter)) l n0)) r).
  cut
   (is_internal_node (fst (BDDneg_2 (bs, (share, counter)) l n0)) r ->
    nat_of_N (var (fst (BDDneg_2 (bs, (share, counter)) l n0)) r) < n0).
  intros H13 H14.  cut
   (BDDconfig_OK
      (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)) /\
    (forall (x0 : BDDvar) (l0 r0 a : ad),
     MapGet _ (fst (fst (BDDneg_2 (bs, (share, counter)) l n0))) a =
     Some (x0, (l0, r0)) ->
     MapGet _
       (fst
          (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)))
       a = Some (x0, (l0, r0))) /\
    (is_internal_node (fst (BDDneg_2 (bs, (share, counter)) l n0)) r ->
     is_internal_node
       (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))
       (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)) /\
     var (fst (BDDneg_2 (bs, (share, counter)) l n0)) r =
     var (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))
       (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))) /\
    config_node_OK
      (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))
      (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)) /\
    bool_fun_eq
      (bool_fun_of_BDD
         (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))
         (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)))
      (bool_fun_neg
         (bool_fun_of_BDD (fst (BDDneg_2 (bs, (share, counter)) l n0)) r))).
  intros H15.  elim H15; clear H15; intros; elim H16; clear H16; intros; elim H17;
   clear H17; intros.
  elim H18.  clear H18.  intros H18 H19.  cut
   (node_OK
      (fst (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)))
      (snd (BDDneg_2 (bs, (share, counter)) l n0))).
  cut
   (node_OK
      (fst (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)))
      (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))).
  cut
   (forall (xl : BDDvar) (ll rl : ad),
    MapGet _
      (fst (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)))
      (snd (BDDneg_2 (bs, (share, counter)) l n0)) = 
    Some (xl, (ll, rl)) -> BDDcompare xl x = Datatypes.Lt).
  cut
   (forall (xr : BDDvar) (lr rr : ad),
    MapGet _
      (fst (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)))
      (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)) =
    Some (xr, (lr, rr)) -> BDDcompare xr x = Datatypes.Lt).
  intros H20 H21 H22 H23.
  cut
   (BDDconfig_OK
      (fst
         (BDDmake
            (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))
            x (snd (BDDneg_2 (bs, (share, counter)) l n0))
            (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)))) /\
    (Neqb (snd (BDDneg_2 (bs, (share, counter)) l n0))
       (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)) =
     false ->
     MapGet _
       (fst
          (fst
             (BDDmake
                (fst
                   (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r
                      n0)) x (snd (BDDneg_2 (bs, (share, counter)) l n0))
                (snd
                   (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r
                      n0)))))
       (snd
          (BDDmake
             (fst
                (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))
             x (snd (BDDneg_2 (bs, (share, counter)) l n0))
             (snd
                (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)))) =
     Some
       (x,
       (snd (BDDneg_2 (bs, (share, counter)) l n0),
       snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)))) /\
    (Neqb (snd (BDDneg_2 (bs, (share, counter)) l n0))
       (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)) =
     true ->
     snd
       (BDDmake
          (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))
          x (snd (BDDneg_2 (bs, (share, counter)) l n0))
          (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))) =
     snd (BDDneg_2 (bs, (share, counter)) l n0)) /\
    (forall (a l' r' : ad) (x' : BDDvar),
     (MapGet _
        (fst
           (fst
              (BDDmake
                 (fst
                    (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r
                       n0)) x (snd (BDDneg_2 (bs, (share, counter)) l n0))
                 (snd
                    (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r
                       n0))))) a = Some (x', (l', r')) ->
      MapGet _
        (fst
           (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)))
        a = Some (x', (l', r')) \/
      snd
        (BDDmake
           (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))
           x (snd (BDDneg_2 (bs, (share, counter)) l n0))
           (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))) =
      a) /\
     (MapGet _
        (fst
           (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)))
        a = Some (x', (l', r')) ->
      MapGet _
        (fst
           (fst
              (BDDmake
                 (fst
                    (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r
                       n0)) x (snd (BDDneg_2 (bs, (share, counter)) l n0))
                 (snd
                    (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r
                       n0))))) a = Some (x', (l', r')))) /\
    node_OK
      (fst
         (fst
            (BDDmake
               (fst
                  (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))
               x (snd (BDDneg_2 (bs, (share, counter)) l n0))
               (snd
                  (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)))))
      (snd
         (BDDmake
            (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))
            x (snd (BDDneg_2 (bs, (share, counter)) l n0))
            (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))))).
  intros H24.  elim H24; clear H24; intros; elim H25; clear H25; intros; elim H26;
   clear H26; intros.  elim H27; clear H27; intros.  split.
  assumption.  cut
   (forall (x0 : BDDvar) (l0 r0 a : ad),
    MapGet (BDDvar * (ad * ad)) bs a =
    Some (x0, (l0, r0)) ->
    MapGet (BDDvar * (ad * ad))
      (fst
         (fst
            (BDDmake
               (fst
                  (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))
               x (snd (BDDneg_2 (bs, (share, counter)) l n0))
               (snd
                  (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)))))
      a = Some (x0, (l0, r0))).
  intros H29.  split.  assumption.  cut
   (is_internal_node (bs, (share, counter)) node ->
    is_internal_node
      (fst
         (BDDmake
            (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))
            x (snd (BDDneg_2 (bs, (share, counter)) l n0))
            (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))))
      (snd
         (BDDmake
            (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))
            x (snd (BDDneg_2 (bs, (share, counter)) l n0))
            (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)))) /\
    var (bs, (share, counter)) node =
    var
      (fst
         (BDDmake
            (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))
            x (snd (BDDneg_2 (bs, (share, counter)) l n0))
            (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))))
      (snd
         (BDDmake
            (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))
            x (snd (BDDneg_2 (bs, (share, counter)) l n0))
            (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))))).
  intros H30.  split.  assumption.  cut
   (config_node_OK
      (fst
         (BDDmake
            (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))
            x (snd (BDDneg_2 (bs, (share, counter)) l n0))
            (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))))
      (snd
         (BDDmake
            (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))
            x (snd (BDDneg_2 (bs, (share, counter)) l n0))
            (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))))).
  intros H31.  split.  assumption.  cut
   (bool_fun_eq
      (bool_fun_of_BDD
         (fst
            (BDDmake
               (fst
                  (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))
               x (snd (BDDneg_2 (bs, (share, counter)) l n0))
               (snd
                  (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))))
         (snd (BDDneg_2 (bs, (share, counter)) l n0)))
      (bool_fun_neg (bool_fun_of_BDD (bs, (share, counter)) l))).
  intro H32.  cut
   (bool_fun_eq
      (bool_fun_of_BDD
         (fst
            (BDDmake
               (fst
                  (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))
               x (snd (BDDneg_2 (bs, (share, counter)) l n0))
               (snd
                  (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))))
         (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)))
      (bool_fun_neg (bool_fun_of_BDD (bs, (share, counter)) r))).
  intro H33.  cut
   (Neqb (snd (BDDneg_2 (bs, (share, counter)) l n0))
      (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)) =
    false).
  intro H34.  cut
   (MapGet (BDDvar * (ad * ad))
      (fst
         (fst
            (BDDmake
               (fst
                  (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))
               x (snd (BDDneg_2 (bs, (share, counter)) l n0))
               (snd
                  (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)))))
      (snd
         (BDDmake
            (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))
            x (snd (BDDneg_2 (bs, (share, counter)) l n0))
            (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)))) =
    Some
      (x,
      (snd (BDDneg_2 (bs, (share, counter)) l n0),
      snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)))).
  intro H35.  cut
   (is_internal_node
      (fst
         (BDDmake
            (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))
            x (snd (BDDneg_2 (bs, (share, counter)) l n0))
            (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))))
      (snd
         (BDDmake
            (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))
            x (snd (BDDneg_2 (bs, (share, counter)) l n0))
            (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))))).
  intro H36.  rewrite (proj2 (proj2 (bool_fun_of_BDD_semantics _ H24)) _ H36).
  cut (is_internal_node (bs, (share, counter)) node).  intro H37.  rewrite (proj2 (proj2 (bool_fun_of_BDD_semantics _ H1)) _ H37).
  unfold var, high, low in |- *.  rewrite H35.  simpl in |- *.  rewrite y.  unfold bool_fun_eq in H32.
  unfold bool_fun_eval in H32.  unfold bool_fun_eq in |- *.  unfold bool_fun_eval in |- *.  unfold bool_fun_neg in |- *.
  intro vb.  rewrite (H32 vb).  unfold bool_fun_eq in H33.  unfold bool_fun_eval in H33.
  rewrite (H33 vb).  elim (vb x); reflexivity.  unfold is_internal_node in |- *.
  split with x.  split with l.  split with r.  assumption.  unfold is_internal_node in |- *.
  split with x.  split with (snd (BDDneg_2 (bs, (share, counter)) l n0)).
  split
   with (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)). 
  assumption.  apply H25.  assumption.  cut
   (Neqb (snd (BDDneg_2 (bs, (share, counter)) l n0))
      (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)) <>
    true).
  elim
   (Neqb (snd (BDDneg_2 (bs, (share, counter)) l n0))
      (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))).
  unfold not in |- *.  intro H34.  cut False.  tauto.  apply H34.  reflexivity.  
  intro H34.  reflexivity.  unfold not in |- *.  intro H34.  cut
   (snd (BDDneg_2 (bs, (share, counter)) l n0) =
    snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)). 
  intro H35.  rewrite <- H35 in H33.  cut
   (bool_fun_eq (bool_fun_neg (bool_fun_of_BDD (bs, (share, counter)) r))
      (bool_fun_neg (bool_fun_of_BDD (bs, (share, counter)) l))).
  intro H36.  cut
   (bool_fun_eq (bool_fun_of_BDD (bs, (share, counter)) r)
      (bool_fun_of_BDD (bs, (share, counter)) l)).
  intro H37.  cut (r = l).  intro H38.  cut (Neqb l r = true).  intro H39.  elim H1.  intros H40 H41.
  elim H40.  intros H42 H43.  elim H43.  intros H44 H45.  cut (BDD_OK bs node).  unfold BDD_OK in |- *. 
  unfold BDDordered in |- *.  rewrite y.  intro H46.  cut
   (node = BDDzero \/
    node = BDDone \/
    (exists x0 : BDDvar,
       (exists l0 : BDDvar,
          (exists r0 : BDDvar,
             MapGet _ bs node = Some (x0, (l0, r0)) /\
             BDDcompare x0 (ad_S x) = Datatypes.Lt /\
             Neqb l0 r0 = false /\
             BDDbounded bs l0 x0 /\ BDDbounded bs r0 x0)))).
  intro H47.  elim H47.  intro H48.  rewrite H48 in y.  rewrite y in H42.
  discriminate H42.  clear H47; intro.  elim H47.  clear H47.  intro H47.
  rewrite H47 in y; rewrite y in H44; discriminate.  intro H48.  elim H48.
  intros x0 H49.  elim H49; intros; elim H50; intros.  elim H51.  intros H52 H53.  rewrite y in H52.
  injection H52.  intros H54 H55 H56.  rewrite <- H54 in H53.  rewrite <- H55 in H53.
  rewrite H39 in H53.  elim H53; intros.  elim H58; intros.  discriminate H59.
  apply BDDbounded_lemma.  assumption.  apply H45.  unfold in_dom in |- *.  rewrite y.  
  reflexivity.  rewrite H38.  apply Neqb_correct.  apply BDDunique with (cfg := (bs, (share, counter))).
  assumption.  assumption.  assumption.  assumption.  apply bool_fun_eq_neg.
  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_of_BDD
                (fst
                   (BDDmake
                      (fst
                         (BDDneg_2
                            (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))
                      x (snd (BDDneg_2 (bs, (share, counter)) l n0))
                      (snd (BDDneg_2 (bs, (share, counter)) l n0))))
                (snd (BDDneg_2 (bs, (share, counter)) l n0))).
  apply bool_fun_eq_symm.  assumption.  rewrite H35.  rewrite H35 in H32.
  assumption.  apply Neqb_complete.  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_of_BDD
                (fst
                   (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r
                      n0))
                (snd
                   (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r
                      n0))).
  apply bool_fun_preservation.  assumption.  assumption.  intros x0 l0 r0 a H33.  apply (proj2 (H27 a l0 r0 x0)).
  assumption.  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_neg
                (bool_fun_of_BDD (fst (BDDneg_2 (bs, (share, counter)) l n0))
                   r)).
  assumption.  apply bool_fun_eq_neg_1.  apply bool_fun_preservation.  assumption.  
  assumption.  assumption.  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_of_BDD
                (fst
                   (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r
                      n0)) (snd (BDDneg_2 (bs, (share, counter)) l n0))).
  apply bool_fun_preservation.  assumption.  assumption.  intros x0 l0 r0 a H32.  apply (proj2 (H27 a l0 r0 x0)).
  assumption.  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_of_BDD (fst (BDDneg_2 (bs, (share, counter)) l n0))
                (snd (BDDneg_2 (bs, (share, counter)) l n0))).
  apply bool_fun_preservation.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  intro H30.  elim
   (sumbool_of_bool
      (Neqb (snd (BDDneg_2 (bs, (share, counter)) l n0))
         (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)))).
  intro y0.  cut
   (snd (BDDneg_2 (bs, (share, counter)) l n0) =
    snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)).
  intro H31.  rewrite <- H31 in H19.  cut
   (bool_fun_eq
      (bool_fun_of_BDD (fst (BDDneg_2 (bs, (share, counter)) l n0))
         (snd (BDDneg_2 (bs, (share, counter)) l n0)))
      (bool_fun_neg
         (bool_fun_of_BDD (fst (BDDneg_2 (bs, (share, counter)) l n0)) r))).
  intro H32.  cut
   (bool_fun_eq
      (bool_fun_of_BDD (fst (BDDneg_2 (bs, (share, counter)) l n0))
         (snd (BDDneg_2 (bs, (share, counter)) l n0)))
      (bool_fun_neg (bool_fun_of_BDD (bs, (share, counter)) r))).
  intro H33.  cut (Neqb l r = true).  intro H34.  elim H1.  intros H35 H36.  elim H35; intros. 
  elim H38; intros.  cut (BDD_OK bs node).  unfold BDD_OK in |- *.  unfold BDDordered in |- *.
  rewrite y.  intro H41.  cut
   (node = BDDzero \/
    node = BDDone \/
    (exists x0 : BDDvar,
       (exists l0 : BDDvar,
          (exists r0 : BDDvar,
             MapGet _ bs node = Some (x0, (l0, r0)) /\
             BDDcompare x0 (ad_S x) = Datatypes.Lt /\
             Neqb l0 r0 = false /\
             BDDbounded bs l0 x0 /\ BDDbounded bs r0 x0)))).
  intro H42.  elim H42; intros.  rewrite H43 in y; rewrite y in H37; discriminate.
  elim H43.  intro H44.  rewrite H44 in y; rewrite y in H39; discriminate.  intro H44.
  elim H44; intros; elim H45; intros; elim H46; intros.  elim H47; intros; elim H48; intros; elim H49; intros.  elim H51; intros.  rewrite y in H48; injection H48.  intros H54 H55 H56.  rewrite <- H54 in H52.  rewrite <- H55 in H52.
  rewrite H34 in H52.  discriminate H52.  apply BDDbounded_lemma.  assumption.
  apply H40.  assumption.  cut (l = r).  intro H34.  rewrite H34; apply Neqb_correct.
  apply BDDunique with (cfg := (bs, (share, counter))).  assumption.  assumption.
  assumption.  apply bool_fun_eq_neg.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_of_BDD (fst (BDDneg_2 (bs, (share, counter)) l n0))
                (snd (BDDneg_2 (bs, (share, counter)) l n0))).
  apply bool_fun_eq_symm.  assumption.  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_neg
                (bool_fun_of_BDD (fst (BDDneg_2 (bs, (share, counter)) l n0))
                   r)).
  assumption.  apply bool_fun_eq_neg_1.  apply bool_fun_preservation.  assumption.
  assumption.  assumption.  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_of_BDD
                (fst
                   (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r
                      n0))
                (snd
                   (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r
                      n0))).
  rewrite <- H31.  apply bool_fun_eq_symm.  apply bool_fun_preservation.  assumption.  
  assumption.  intros x0 l0 r0 a H32.  apply H16.  assumption.  assumption.  rewrite <- H31.
  assumption.  apply Neqb_complete.  assumption.  intro y0.  unfold is_internal_node, var in |- *.
  rewrite (H25 y0).  simpl in |- *.  rewrite y.  split.  split with x.
  split with (snd (BDDneg_2 (bs, (share, counter)) l n0)).  split
   with (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)).
  reflexivity.  reflexivity.  intros x0 l0 r0 a H29.  apply (proj2 (H27 a l0 r0 x0)).
  apply H16.  apply H9.  exact H29.  apply BDDmake_semantics.  assumption.
  assumption.  assumption.  assumption.  assumption.  intros xr lr rr H20.  elim H5.  intro H21.
  rewrite H21 in H19.  rewrite
   (proj1
      (bool_fun_of_BDD_semantics (fst (BDDneg_2 (bs, (share, counter)) l n0))
         H7)) in H19.
  rewrite bool_fun_neg_zero in H19.  rewrite H21 in H15.  rewrite <-
   (proj1
      (proj2
         (bool_fun_of_BDD_semantics
            (fst
               (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) BDDzero
                  n0)) H15))) in H19.
  cut
   (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) BDDzero n0) =
    BDDone).
  intro H22.  rewrite H21 in H20.  rewrite H22 in H20.  rewrite
   (config_OK_one
      (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) BDDzero n0))
      H15) in H20. 
  discriminate H20.  apply
   BDDunique
    with
      (cfg := fst
                (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0))
                   BDDzero n0)).
  assumption.  rewrite H21 in H18.  assumption.  right.  left.  reflexivity.
  assumption.  intro H21.  elim H21.  clear H21; intro.  rewrite H21 in H19.
  rewrite
   (proj1
      (proj2
         (bool_fun_of_BDD_semantics
            (fst (BDDneg_2 (bs, (share, counter)) l n0)) H7)))
    in H19.
  rewrite bool_fun_neg_one in H19.  rewrite H21 in H15.  rewrite <-
   (proj1
      (bool_fun_of_BDD_semantics
         (fst
            (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) BDDone n0))
         H15)) in H19.
  cut
   (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) BDDone n0) =
    BDDzero).
  intro H22.  rewrite H21 in H20.  rewrite H22 in H20.  rewrite
   (config_OK_zero
      (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) BDDone n0))
      H15) in H20.  
  discriminate H20.  apply
   BDDunique
    with
      (cfg := fst
                (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) BDDone
                   n0)).
  assumption.  rewrite H21 in H18.  assumption.  left; reflexivity.
  assumption.  intro H22.  unfold in_dom in H22.  elim
   (option_sum _ (MapGet (BDDvar * (ad * ad)) (fst (bs, (share, counter))) r)).
  intro y0.  elim y0; clear y0; intro x0.  elim x0; clear x0; intro y0; intro y1.
  elim y1; clear y1; intros y1 y2 y3.  cut (is_internal_node (fst (BDDneg_2 (bs, (share, counter)) l n0)) r).
  intro H23.  cut
   (var (fst (BDDneg_2 (bs, (share, counter)) l n0)) r =
    var (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))
      (snd (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0))).
  intro H24.  cut
   (var (bs, (share, counter)) r =
    var (fst (BDDneg_2 (bs, (share, counter)) l n0)) r).
  intro H25.  rewrite <- H25 in H24.  cut
   (BDDcompare
      (var (bs, (share, counter)) (high (bs, (share, counter)) node))
      (var (bs, (share, counter)) node) = Datatypes.Lt).
  unfold var, high, low in |- *.  simpl in |- *.  rewrite y.  simpl in y3.  rewrite y3.  unfold var in H24.
  simpl in H24.  rewrite y3 in H24.  rewrite H20 in H24.  rewrite H24.  trivial.
  apply BDDvar_ordered_high.  assumption.  unfold is_internal_node in |- *.
  split with x; split with l; split with r; assumption.  unfold high in |- *.  simpl in |- *; rewrite y.  split with y0; split with y1; split with y2; assumption.
  unfold var in |- *.  rewrite y3.  cut
   (MapGet (BDDvar * (ad * ad))
      (fst (fst (BDDneg_2 (bs, (share, counter)) l n0))) r =
    Some (y0, (y1, y2))).
  intro H25.  rewrite H25.  reflexivity.  apply H9.  assumption.  exact (proj2 (H17 H23)).
  unfold is_internal_node in |- *.  split with y0.  split with y1.  split with y2.  rewrite (H9 y0 y1 y2 r).
  reflexivity.  assumption.  intro y0.  rewrite y0 in H22; discriminate.  intros xl ll rl H20.
  elim (option_sum _ (MapGet _ (fst (bs, (share, counter))) l)).  intros y0.
  elim y0.  clear y0.  intro x0.  elim x0; clear x0; intro y0; intro y1.  elim y1; clear y1; intros y1 y2 y3.
  cut
   (is_internal_node (fst (BDDneg_2 (bs, (share, counter)) l n0))
      (snd (BDDneg_2 (bs, (share, counter)) l n0)) /\
    var (bs, (share, counter)) l =
    var (fst (BDDneg_2 (bs, (share, counter)) l n0))
      (snd (BDDneg_2 (bs, (share, counter)) l n0))).
  intros H21.  elim H21; clear H21; intros.  elim
   (option_sum _
      (MapGet _ (fst (fst (BDDneg_2 (bs, (share, counter)) l n0)))
         (snd (BDDneg_2 (bs, (share, counter)) l n0)))).
  intros y4.  elim y4; clear y4; intro x0.  elim x0; clear x0; intro y4; intro y5.  elim y5; clear y5; intros y5 y6 y7.
  unfold var in H22.  rewrite y3 in H22.  rewrite y7 in H22.
  cut
   (MapGet (BDDvar * (ad * ad))
      (fst (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)))
      (snd (BDDneg_2 (bs, (share, counter)) l n0)) =
    Some (y4, (y5, y6))).
  intros H23.  rewrite H20 in H23.  injection H23.  intros H24 H25 H26.  rewrite H26.  rewrite <- H22.
  cut
   (BDDcompare (var (bs, (share, counter)) (low (bs, (share, counter)) node))
      (var (bs, (share, counter)) node) = Datatypes.Lt).
  unfold var, high, low in |- *.  simpl in |- *.  rewrite y.  simpl in y3.  rewrite y3.  trivial. 
  apply BDDvar_ordered_low.  assumption.  unfold is_internal_node in |- *.  split with x; split with l; split with r.
  assumption.  unfold low, is_internal_node in |- *.  simpl in |- *.  rewrite y.  split with y0; split with y1; split with y2.
  exact y3.  apply H16.  assumption.  intro y4.  unfold is_internal_node in H21.
  rewrite y4 in H21.  inversion H21.  inversion H23.  inversion H24.  discriminate H25.
  apply H10.  unfold is_internal_node in |- *.  split with y0; split with y1; split with y2; assumption.
  intro y0.  elim H6.  intro H21.  cut (snd (BDDneg_2 (bs, (share, counter)) l n0) = BDDone).
  intro H22.  rewrite H22 in H20.  unfold BDDconfig_OK in H15.  cut
   (MapGet _
      (fst (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)))
      BDDone = None).
  intros H23.  rewrite H23 in H20.  discriminate H20.  apply config_OK_one.  assumption.
  apply BDDunique with (cfg := fst (BDDneg_2 (bs, (share, counter)) l n0)).  assumption.
  assumption.  right; left; reflexivity.  rewrite
   (proj1
      (proj2
         (bool_fun_of_BDD_semantics
            (fst (BDDneg_2 (bs, (share, counter)) l n0)) H7)))
   .
  rewrite <- bool_fun_neg_zero.  rewrite <- (proj1 (bool_fun_of_BDD_semantics (bs, (share, counter)) H1)).
  rewrite <- H21; exact H12.  intro H21.  elim H21; clear H21.  intro H21.
  cut (snd (BDDneg_2 (bs, (share, counter)) l n0) = BDDzero).  intro H22.  rewrite H22 in H20.
  unfold BDDconfig_OK in H15.  cut
   (MapGet _
      (fst (fst (BDDneg_2 (fst (BDDneg_2 (bs, (share, counter)) l n0)) r n0)))
      BDDzero = None).
  intros H23.  rewrite H23 in H20.  discriminate H20.  apply config_OK_zero.  assumption.
  apply BDDunique with (cfg := fst (BDDneg_2 (bs, (share, counter)) l n0)).  assumption.
  assumption.  left; reflexivity.  rewrite
   (proj1
      (bool_fun_of_BDD_semantics (fst (BDDneg_2 (bs, (share, counter)) l n0))
         H7)).
  rewrite <- bool_fun_neg_one.  rewrite <-
   (proj1 (proj2 (bool_fun_of_BDD_semantics (bs, (share, counter)) H1)))
   .
  rewrite <- H21; exact H12.  unfold in_dom in |- *.  rewrite y0.  intro; discriminate.
  assumption.  elim H11.  intro H20.  rewrite H20.  left; reflexivity.  intro H20.
  elim H20; intro.  rewrite H21; right; left; reflexivity. 
  elim
   (option_sum _
      (MapGet _ (fst (fst (BDDneg_2 (bs, (share, counter)) l n0)))
         (snd (BDDneg_2 (bs, (share, counter)) l n0)))).
  intro y0.  elim y0; clear y0; intro x0.  elim x0; clear x0; intro y0; intro y1.  elim y1; clear y1; intros y1 y2 y3.
  right.  right.  unfold in_dom in |- *.  rewrite (H16 y0 y1 y2 (snd (BDDneg_2 (bs, (share, counter)) l n0))).
  reflexivity.  assumption.  intro y0.  unfold in_dom in H21.  rewrite y0 in H21; discriminate.
  apply H0.  unfold lt in |- *.  apply le_n.  assumption.  assumption.  assumption.  intro H13.
  apply lt_trans_1 with (y := nat_of_N (var (bs, (share, counter)) node)).
  apply BDDcompare_lt.  cut
   (BDDcompare
      (var (bs, (share, counter)) (high (bs, (share, counter)) node))
      (var (bs, (share, counter)) node) = Datatypes.Lt).
  cut
   (var (bs, (share, counter)) r =
    var (fst (BDDneg_2 (bs, (share, counter)) l n0)) r).
  intro H14.  unfold high in |- *.  simpl in |- *.  rewrite y.  rewrite H14.  trivial.  unfold is_internal_node in H13.
  inversion H13.  inversion H14.  inversion H15.  elim H5.  intro H17.  rewrite H17 in H16.
  rewrite (config_OK_zero (fst (BDDneg_2 (bs, (share, counter)) l n0)))
    in H16.  discriminate H16.
  assumption.  intro H17.  elim H17; intro.  rewrite H18 in H16.  rewrite (config_OK_one (fst (BDDneg_2 (bs, (share, counter)) l n0))) in H16.
  discriminate H16.  assumption.  elim (option_sum _ (MapGet _ (fst (bs, (share, counter))) r)).
  intro y0.  elim y0; clear y0; intro x3.  elim x3; clear x3; intro y0.  intro y1.
  elim y1; clear y1; intros y1 y2 y3.  unfold var in |- *.  rewrite y3.  rewrite (H9 y0 y1 y2 r).
  reflexivity.  assumption.  intro y0.  unfold in_dom in H18.  rewrite y0 in H18; discriminate.
  apply BDDvar_ordered_high.  assumption.  unfold is_internal_node in |- *.  split with x; split with l; split with r; assumption.
  unfold high in |- *.  simpl in |- *.  rewrite y.  unfold is_internal_node in H13.  inversion H13; inversion H14; inversion H15.
  elim H5; intro.  rewrite H17 in H16.  rewrite (config_OK_zero (fst (BDDneg_2 (bs, (share, counter)) l n0)))
    in H16.
  discriminate H16.  assumption.  elim H17; intro.  rewrite H18 in H16.  rewrite (config_OK_one (fst (BDDneg_2 (bs, (share, counter)) l n0))) in H16.
  discriminate H16.  assumption.  unfold in_dom in H18.  unfold is_internal_node in |- *.
  elim
   (option_sum _ (MapGet (BDDvar * (ad * ad)) (fst (bs, (share, counter))) r)).  intros y0.
  elim y0; intro x3.  elim x3; intro y1; intro y2.  elim y2; intros y3 y4 y5.  split with y1; split with y3; split with y4; assumption.
  intro y0.  rewrite y0 in H18; discriminate.  apply H3.  unfold is_internal_node in |- *.
  split with x; split with l; split with r; exact y.  elim H5; intro.  rewrite H13; left; reflexivity.
  elim H13; intro.  rewrite H14; right; left; reflexivity.  unfold in_dom in H14.
  elim
   (option_sum _ (MapGet (BDDvar * (ad * ad)) (fst (bs, (share, counter))) r)).  intro y0.
  elim y0; intro x0.  elim x0; intro y1; intro y2.  elim y2; intros y3 y4 y5.  right; right.
  unfold in_dom in |- *.  rewrite (H9 y1 y3 y4 r y5).  reflexivity.  intro y0.  rewrite y0 in H14; discriminate.
  apply H0.  unfold lt in |- *.  apply le_n.  assumption.  assumption.  intro H7.  apply lt_trans_1 with (y := nat_of_N (var (bs, (share, counter)) node)).
  cut
   (nat_of_N (var (bs, (share, counter)) (low (bs, (share, counter)) node)) <
    nat_of_N (var (bs, (share, counter)) node)).
  unfold low in |- *.  simpl in |- *.  rewrite y.  trivial.  apply BDDcompare_lt.  apply BDDvar_ordered_low.
  assumption.  unfold is_internal_node in |- *.  split with x; split with l; split with r; exact y.
  unfold low in |- *.  simpl in |- *; rewrite y; assumption.  apply H3.  unfold is_internal_node in |- *.
  split with x; split with l; split with r; assumption.  intro H7.  apply lt_trans_1 with (y := nat_of_N (var (bs, (share, counter)) node)).
  cut
   (nat_of_N (var (bs, (share, counter)) (low (bs, (share, counter)) node)) <
    nat_of_N (var (bs, (share, counter)) node)).
  unfold low in |- *.  simpl in |- *.  rewrite y.  trivial.  apply BDDcompare_lt.  apply BDDvar_ordered_low.
  assumption.  unfold is_internal_node in |- *.  split with x; split with l; split with r; exact y.
  unfold low in |- *.  simpl in |- *; rewrite y; assumption.  apply H3.  unfold is_internal_node in |- *.
  split with x; split with l; split with r; assumption.  elim H1.  intros H5 H6.  elim H5.
  intros H7 H8.  cut (BDD_OK bs node).  unfold BDD_OK in |- *.  unfold BDDordered in |- *.  simpl in y.  rewrite y.
  intro H9.  cut
   (node = BDDzero \/
    node = BDDone \/
    (exists x0 : BDDvar,
       (exists l0 : BDDvar,
          (exists r0 : BDDvar,
             MapGet _ bs node = Some (x0, (l0, r0)) /\
             BDDcompare x0 (ad_S x) = Datatypes.Lt /\
             Neqb l0 r0 = false /\
             BDDbounded bs l0 x0 /\ BDDbounded bs r0 x0)))).
  intro H10.  elim H10; intro.  rewrite H11 in y; rewrite y in H7; discriminate.
  elim H11; intro.  rewrite H12 in y; rewrite (proj1 H8) in y; discriminate.  
  inversion H12.  inversion H13.  inversion H14.  inversion H15.  rewrite y in H16.
  injection H16.  intros H18 H19 H20.  rewrite <- H18 in H17.  rewrite <- H19 in H17.  unfold config_node_OK in |- *.  apply BDDbounded_node_OK with (n := x0).
  exact (proj2 (proj2 (proj2 H17))).  apply BDDbounded_lemma.  assumption.
  apply (proj2 H8).  unfold in_dom in |- *.  simpl in y.  rewrite y.  reflexivity.  elim H1.  intros H5 H6.
  elim H5.  intros H7 H8.  cut (BDD_OK bs node).  unfold BDD_OK in |- *.  unfold BDDordered in |- *.
  simpl in y.  rewrite y.  intro H9.  cut
   (node = BDDzero \/
    node = BDDone \/
    (exists x0 : BDDvar,
       (exists l0 : BDDvar,
          (exists r0 : BDDvar,
             MapGet _ bs node = Some (x0, (l0, r0)) /\
             BDDcompare x0 (ad_S x) = Datatypes.Lt /\
             Neqb l0 r0 = false /\
             BDDbounded bs l0 x0 /\ BDDbounded bs r0 x0)))).
  intro H10.  elim H10; intro.  rewrite H11 in y; rewrite y in H7; discriminate.
  elim H11; intro.  rewrite H12 in y; rewrite (proj1 H8) in y; discriminate.  
  inversion H12.  inversion H13.  inversion H14.  inversion H15.  rewrite y in H16.
  injection H16.  intros H18 H19 H20.  rewrite <- H18 in H17.  rewrite <- H19 in H17.  unfold config_node_OK in |- *.
  apply BDDbounded_node_OK with (n := x0).  exact (proj1 (proj2 (proj2 H17))).
  apply BDDbounded_lemma.  assumption.  apply (proj2 H8).  unfold in_dom in |- *.
  simpl in y.  rewrite y.  reflexivity.  intro y.  unfold in_dom in H4.  rewrite y in H4.
  discriminate H4.
Qed.
