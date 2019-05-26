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

Lemma BDDdummy_lemma_3 :
 forall bound : nat,
 (forall m : nat,
  m < bound ->
  forall (cfg : BDDconfig) (node1 node2 : ad) (memo : BDDor_memo),
  BDDconfig_OK cfg ->
  BDDor_memo_OK cfg memo ->
  config_node_OK cfg node1 ->
  config_node_OK cfg node2 ->
  (is_internal_node cfg node1 ->
   is_internal_node cfg node2 ->
   max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2)) < m) ->
  BDDconfig_OK (fst (BDDor_1 cfg memo node1 node2 m)) /\
  BDDor_memo_OK (fst (BDDor_1 cfg memo node1 node2 m))
    (snd (snd (BDDor_1 cfg memo node1 node2 m))) /\
  config_node_OK (fst (BDDor_1 cfg memo node1 node2 m))
    (fst (snd (BDDor_1 cfg memo node1 node2 m))) /\
  nodes_preserved cfg (fst (BDDor_1 cfg memo node1 node2 m)) /\
  BDDvar_le
    (var (fst (BDDor_1 cfg memo node1 node2 m))
       (fst (snd (BDDor_1 cfg memo node1 node2 m))))
    (BDDvar_max (var cfg node1) (var cfg node2)) = true /\
  bool_fun_eq
    (bool_fun_of_BDD (fst (BDDor_1 cfg memo node1 node2 m))
       (fst (snd (BDDor_1 cfg memo node1 node2 m))))
    (bool_fun_or (bool_fun_of_BDD cfg node1) (bool_fun_of_BDD cfg node2))) ->
 forall (cfg : BDDconfig) (node1 node2 : ad) (memo : BDDor_memo),
 BDDconfig_OK cfg ->
 BDDor_memo_OK cfg memo ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 (is_internal_node cfg node1 ->
  is_internal_node cfg node2 ->
  max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2)) < bound) ->
 BDDor_memo_lookup memo node1 node2 = None ->
 in_dom (BDDvar * (ad * ad)) node1 (fst cfg) = true ->
 node2 = BDDone \/ in_dom (BDDvar * (ad * ad)) node2 (fst cfg) = true ->
 is_internal_node cfg node1 ->
 in_dom (BDDvar * (ad * ad)) node2 (fst cfg) = true ->
 is_internal_node cfg node2 ->
 forall bound' : nat,
 bound = S bound' ->
 max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2)) < bound ->
 BDDcompare (var cfg node1) (var cfg node2) = Datatypes.Lt ->
 BDDconfig_OK (fst (BDDor_1 cfg memo node1 node2 bound)) /\
 BDDor_memo_OK (fst (BDDor_1 cfg memo node1 node2 bound))
   (snd (snd (BDDor_1 cfg memo node1 node2 bound))) /\
 config_node_OK (fst (BDDor_1 cfg memo node1 node2 bound))
   (fst (snd (BDDor_1 cfg memo node1 node2 bound))) /\
 nodes_preserved cfg (fst (BDDor_1 cfg memo node1 node2 bound)) /\
 BDDvar_le
   (var (fst (BDDor_1 cfg memo node1 node2 bound))
      (fst (snd (BDDor_1 cfg memo node1 node2 bound))))
   (BDDvar_max (var cfg node1) (var cfg node2)) = true /\
 bool_fun_eq
   (bool_fun_of_BDD (fst (BDDor_1 cfg memo node1 node2 bound))
      (fst (snd (BDDor_1 cfg memo node1 node2 bound))))
   (bool_fun_or (bool_fun_of_BDD cfg node1) (bool_fun_of_BDD cfg node2)).
Proof.
  intros bound H cfg node1 node2 memo H0 H1 H2 H3 H4 y H5 H6 H8 H9 H7 bound'
   y0 H10 y1.
cut (config_node_OK cfg (low cfg node1)).
cut (config_node_OK cfg (low cfg node2)).
cut (config_node_OK cfg (high cfg node1)).
cut (config_node_OK cfg (high cfg node2)).
intros H11 H12 H13 H14.
cut
 (is_internal_node cfg node1 ->
  is_internal_node cfg (low cfg node2) ->
  max (nat_of_N (var cfg node1)) (nat_of_N (var cfg (low cfg node2))) <
  bound').
intro H15.
cut
 (BDDconfig_OK (fst (BDDor_1 cfg memo node1 (low cfg node2) bound')) /\
  BDDor_memo_OK (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
    (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound'))) /\
  config_node_OK (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
    (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound'))) /\
  nodes_preserved cfg (fst (BDDor_1 cfg memo node1 (low cfg node2) bound')) /\
  BDDvar_le
    (var (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
       (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound'))))
    (BDDvar_max (var cfg node1) (var cfg (low cfg node2))) = true /\
  bool_fun_eq
    (bool_fun_of_BDD (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
       (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound'))))
    (bool_fun_or (bool_fun_of_BDD cfg node1)
       (bool_fun_of_BDD cfg (low cfg node2)))).
intro H16.
elim H16; clear H16; intros.
elim H17; clear H17; intros.
elim H18; clear H18; intros.
elim H19; clear H19; intros.
elim H20; clear H20; intros.
cut
 (config_node_OK (fst (BDDor_1 cfg memo node1 (low cfg node2) bound')) node1).
intro H22.




cut
 (config_node_OK (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
    (high cfg node2)).
intro H23.
cut
 (is_internal_node (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
    node1 ->
  is_internal_node (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
    (high cfg node2) ->
  max
    (nat_of_N
       (var (fst (BDDor_1 cfg memo node1 (low cfg node2) bound')) node1))
    (nat_of_N
       (var (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
          (high cfg node2))) < bound').
intro H24.
cut
 (BDDconfig_OK
    (fst
       (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
          (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound'))) node1
          (high cfg node2) bound')) /\
  BDDor_memo_OK
    (fst
       (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
          (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound'))) node1
          (high cfg node2) bound'))
    (snd
       (snd
          (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
             (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
             node1 (high cfg node2) bound'))) /\
  config_node_OK
    (fst
       (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
          (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound'))) node1
          (high cfg node2) bound'))
    (fst
       (snd
          (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
             (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
             node1 (high cfg node2) bound'))) /\
  nodes_preserved (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
    (fst
       (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
          (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound'))) node1
          (high cfg node2) bound')) /\
  BDDvar_le
    (var
       (fst
          (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
             (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
             node1 (high cfg node2) bound'))
       (fst
          (snd
             (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                node1 (high cfg node2) bound'))))
    (BDDvar_max
       (var (fst (BDDor_1 cfg memo node1 (low cfg node2) bound')) node1)
       (var (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
          (high cfg node2))) = true /\
  bool_fun_eq
    (bool_fun_of_BDD
       (fst
          (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
             (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
             node1 (high cfg node2) bound'))
       (fst
          (snd
             (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                node1 (high cfg node2) bound'))))
    (bool_fun_or
       (bool_fun_of_BDD (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
          node1)
       (bool_fun_of_BDD (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
          (high cfg node2)))).
intro H25.
elim H25; clear H25; intros.
elim H26; clear H26; intros.
elim H27; clear H27; intros.
elim H28; clear H28; intros.
elim H29; clear H29; intros.
cut
 (config_node_OK
    (fst
       (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
          (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound'))) node1
          (high cfg node2) bound'))
    (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))).
intro H31.







cut
 (is_internal_node
    (fst
       (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
          (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound'))) node1
          (high cfg node2) bound'))
    (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound'))) ->
  BDDcompare
    (var
       (fst
          (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
             (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
             node1 (high cfg node2) bound'))
       (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound'))))
    (var cfg node2) = Datatypes.Lt).











intro H32. 


cut
 (is_internal_node
    (fst
       (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
          (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound'))) node1
          (high cfg node2) bound'))
    (fst
       (snd
          (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
             (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
             node1 (high cfg node2) bound'))) ->
  BDDcompare
    (var
       (fst
          (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
             (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
             node1 (high cfg node2) bound'))
       (fst
          (snd
             (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                node1 (high cfg node2) bound')))) (var cfg node2) =
  Datatypes.Lt).












intro H33.




cut
 (BDDconfig_OK
    (fst
       (BDDmake
          (fst
             (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                node1 (high cfg node2) bound')) (var cfg node2)
          (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
          (fst
             (snd
                (BDDor_1
                   (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                   (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                   node1 (high cfg node2) bound'))))) /\
  (Neqb (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
     (fst
        (snd
           (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
              (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
              node1 (high cfg node2) bound'))) = false ->
   MapGet _
     (fst
        (fst
           (BDDmake
              (fst
                 (BDDor_1
                    (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                    (snd
                       (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                    node1 (high cfg node2) bound')) 
              (var cfg node2)
              (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
              (fst
                 (snd
                    (BDDor_1
                       (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                       (snd
                          (snd
                             (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                       node1 (high cfg node2) bound'))))))
     (snd
        (BDDmake
           (fst
              (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                 (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                 node1 (high cfg node2) bound')) (var cfg node2)
           (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
           (fst
              (snd
                 (BDDor_1
                    (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                    (snd
                       (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                    node1 (high cfg node2) bound'))))) =
   Some
     (var cfg node2,
     (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')),
     fst
       (snd
          (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
             (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
             node1 (high cfg node2) bound'))))) /\
  (Neqb (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
     (fst
        (snd
           (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
              (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
              node1 (high cfg node2) bound'))) = true ->
   snd
     (BDDmake
        (fst
           (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
              (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
              node1 (high cfg node2) bound')) (var cfg node2)
        (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
        (fst
           (snd
              (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                 (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                 node1 (high cfg node2) bound')))) =
   fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound'))) /\
  (forall (a l' r' : ad) (x' : BDDvar),
   (MapGet _
      (fst
         (fst
            (BDDmake
               (fst
                  (BDDor_1
                     (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                     (snd
                        (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                     node1 (high cfg node2) bound')) 
               (var cfg node2)
               (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
               (fst
                  (snd
                     (BDDor_1
                        (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                        (snd
                           (snd
                              (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                        node1 (high cfg node2) bound')))))) a =
    Some (x', (l', r')) ->
    MapGet _
      (fst
         (fst
            (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
               (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
               node1 (high cfg node2) bound'))) a = 
    Some (x', (l', r')) \/
    snd
      (BDDmake
         (fst
            (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
               (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
               node1 (high cfg node2) bound')) (var cfg node2)
         (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
         (fst
            (snd
               (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                  (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                  node1 (high cfg node2) bound')))) = a) /\
   (MapGet _
      (fst
         (fst
            (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
               (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
               node1 (high cfg node2) bound'))) a = 
    Some (x', (l', r')) ->
    MapGet _
      (fst
         (fst
            (BDDmake
               (fst
                  (BDDor_1
                     (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                     (snd
                        (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                     node1 (high cfg node2) bound')) 
               (var cfg node2)
               (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
               (fst
                  (snd
                     (BDDor_1
                        (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                        (snd
                           (snd
                              (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                        node1 (high cfg node2) bound')))))) a =
    Some (x', (l', r')))) /\
  node_OK
    (fst
       (fst
          (BDDmake
             (fst
                (BDDor_1
                   (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                   (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                   node1 (high cfg node2) bound')) 
             (var cfg node2)
             (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
             (fst
                (snd
                   (BDDor_1
                      (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                      (snd
                         (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                      node1 (high cfg node2) bound'))))))
    (snd
       (BDDmake
          (fst
             (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                node1 (high cfg node2) bound')) (var cfg node2)
          (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
          (fst
             (snd
                (BDDor_1
                   (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                   (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                   node1 (high cfg node2) bound')))))).
intro H34.
elim H34; clear H34; intros.
elim H35; clear H35; intros.
elim H36; clear H36; intros.
elim H37; clear H37; intros.
cut (BDDconfig_OK (fst (BDDor_1 cfg memo node1 node2 bound))).
intro H39.
cut
 (config_node_OK (fst (BDDor_1 cfg memo node1 node2 bound))
    (fst (snd (BDDor_1 cfg memo node1 node2 bound)))).
intro H40.
cut (nodes_preserved cfg (fst (BDDor_1 cfg memo node1 node2 bound))).
intro H41.
cut
 (BDDvar_le
    (var (fst (BDDor_1 cfg memo node1 node2 bound))
       (fst (snd (BDDor_1 cfg memo node1 node2 bound))))
    (BDDvar_max (var cfg node1) (var cfg node2)) = true).
intro H42.
cut
 (bool_fun_eq
    (bool_fun_of_BDD (fst (BDDor_1 cfg memo node1 node2 bound))
       (fst (snd (BDDor_1 cfg memo node1 node2 bound))))
    (bool_fun_or (bool_fun_of_BDD cfg node1) (bool_fun_of_BDD cfg node2))).
intro H43.
cut
 (BDDor_memo_OK (fst (BDDor_1 cfg memo node1 node2 bound))
    (snd (snd (BDDor_1 cfg memo node1 node2 bound)))).
intro H44.
split.
assumption.

split.
assumption.

split.
assumption.

split.
assumption.

split.
assumption.

assumption.

unfold BDDor_memo_OK in |- *.
intros node1' node2' node.
rewrite
 (BDDor_1_lemma_internal_2 cfg memo node1 node2 bound bound' y H0 H8 H7 H10
    y0 y1).
simpl in |- *.
rewrite
 (BDDor_memo_lookup_semantics
    (snd
       (snd
          (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
             (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
             node1 (high cfg node2) bound'))) node1 node2
    (snd
       (BDDmake
          (fst
             (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                node1 (high cfg node2) bound')) (var cfg node2)
          (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
          (fst
             (snd
                (BDDor_1
                   (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                   (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                   node1 (high cfg node2) bound'))))) node1' node2')
 .
elim (sumbool_of_bool (Neqb node1 node1' && Neqb node2 node2')); intro y2.
rewrite y2.
cut (node1 = node1').
cut (node2 = node2').
intro H44.
intro H45.
intro H46.





injection H46.
clear H46; intros.






cut
 (config_node_OK
    (fst
       (BDDmake
          (fst
             (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                node1 (high cfg node2) bound')) (var cfg node2)
          (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
          (fst
             (snd
                (BDDor_1
                   (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                   (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                   node1 (high cfg node2) bound'))))) node1').
intro H47.
cut
 (config_node_OK
    (fst
       (BDDmake
          (fst
             (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                node1 (high cfg node2) bound')) (var cfg node2)
          (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
          (fst
             (snd
                (BDDor_1
                   (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                   (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                   node1 (high cfg node2) bound'))))) node2').
intro H48.
cut
 (config_node_OK
    (fst
       (BDDmake
          (fst
             (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                node1 (high cfg node2) bound')) (var cfg node2)
          (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
          (fst
             (snd
                (BDDor_1
                   (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                   (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                   node1 (high cfg node2) bound'))))) node).




intro H49.
split.
assumption.

split.
assumption.

split.
assumption.

split.




rewrite <- H44; rewrite <- H45.






cut
 (var
    (fst
       (BDDmake
          (fst
             (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                node1 (high cfg node2) bound')) (var cfg node2)
          (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
          (fst
             (snd
                (BDDor_1
                   (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                   (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                   node1 (high cfg node2) bound'))))) node1 = 
  var cfg node1).
intro H50.
rewrite H50.






cut
 (var
    (fst
       (BDDmake
          (fst
             (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                node1 (high cfg node2) bound')) (var cfg node2)
          (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
          (fst
             (snd
                (BDDor_1
                   (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                   (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                   node1 (high cfg node2) bound'))))) node2 = 
  var cfg node2).
intro H51.




rewrite H51.
rewrite <- H46.
rewrite
 (BDDor_1_lemma_internal_2 cfg memo node1 node2 bound bound' y H0 H8 H7 H10
    y0 y1) in H42.
simpl in H42.
exact H42.
rewrite
 (BDDor_1_lemma_internal_2 cfg memo node1 node2 bound bound' y H0 H8 H7 H10
    y0 y1) in H41.
apply nodes_preserved_var.
exact H41.

assumption.

apply nodes_preserved_var.
rewrite
 (BDDor_1_lemma_internal_2 cfg memo node1 node2 bound bound' y H0 H8 H7 H10
    y0 y1) in H41.
simpl in H39; exact H41.

assumption.





rewrite <- H44; rewrite <- H45.
rewrite <- H46.
apply
 bool_fun_eq_trans
  with
    (bf2 := bool_fun_or (bool_fun_of_BDD cfg node1)
              (bool_fun_of_BDD cfg node2)).
rewrite
 (BDDor_1_lemma_internal_2 cfg memo node1 node2 bound bound' y H0 H8 H7 H10
    y0 y1) in H43.
simpl in H43; exact H43.

apply bool_fun_or_preserves_eq.
apply bool_fun_eq_symm.
apply nodes_preserved_3.
assumption.

assumption.

rewrite
 (BDDor_1_lemma_internal_2 cfg memo node1 node2 bound bound' y H0 H8 H7 H10
    y0 y1) in H41.
exact H41.

assumption.

apply bool_fun_eq_symm.
apply nodes_preserved_3.
assumption.

assumption.

rewrite
 (BDDor_1_lemma_internal_2 cfg memo node1 node2 bound bound' y H0 H8 H7 H10
    y0 y1) in H41.
exact H41.

assumption.

rewrite <- H46.
exact H38.





rewrite <- H44.
apply
 nodes_preserved_2
  with
    (cfg := fst
              (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                 (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                 node1 (high cfg node2) bound')).
apply
 nodes_preserved_2
  with (cfg := fst (BDDor_1 cfg memo node1 (low cfg node2) bound')).
apply nodes_preserved_2 with (cfg := cfg).
assumption.

assumption.

assumption.

apply BDDmake_preserves_nodes.
assumption.

rewrite <- H45.
apply nodes_preserved_2 with (cfg := cfg).
assumption.

rewrite
 (BDDor_1_lemma_internal_2 cfg memo node1 node2 bound bound' y H0 H8 H7 H10
    y0 y1) in H41.
exact H41.

apply Neqb_complete.
exact (proj2 (andb_prop (Neqb node1 node1') (Neqb node2 node2') y2)).

apply Neqb_complete.
exact (proj1 (andb_prop (Neqb node1 node1') (Neqb node2 node2') y2)).

rewrite y2.
intros H44.
split.
apply
 nodes_preserved_2
  with
    (cfg := fst
              (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                 (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                 node1 (high cfg node2) bound')).
unfold BDDor_memo_OK in H26.
exact (proj1 (H26 node1' node2' node H44)).

apply BDDmake_preserves_nodes.
assumption.

split.
apply
 nodes_preserved_2
  with
    (cfg := fst
              (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                 (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                 node1 (high cfg node2) bound')).
unfold BDDor_memo_OK in H26.
exact (proj1 (proj2 (H26 node1' node2' node H44))).

apply BDDmake_preserves_nodes.
assumption.

split.
apply
 nodes_preserved_2
  with
    (cfg := fst
              (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                 (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                 node1 (high cfg node2) bound')).
unfold BDDor_memo_OK in H26.
exact (proj1 (proj2 (proj2 (H26 node1' node2' node H44)))).

apply BDDmake_preserves_nodes.
assumption.

split.
cut
 (var
    (fst
       (BDDmake
          (fst
             (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                node1 (high cfg node2) bound')) (var cfg node2)
          (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
          (fst
             (snd
                (BDDor_1
                   (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                   (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                   node1 (high cfg node2) bound'))))) node =
  var
    (fst
       (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
          (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound'))) node1
          (high cfg node2) bound')) node).
intro H45.
rewrite H45.
cut
 (var
    (fst
       (BDDmake
          (fst
             (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                node1 (high cfg node2) bound')) (var cfg node2)
          (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
          (fst
             (snd
                (BDDor_1
                   (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                   (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                   node1 (high cfg node2) bound'))))) node1' =
  var
    (fst
       (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
          (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound'))) node1
          (high cfg node2) bound')) node1').
intro H46.
rewrite H46.
cut
 (var
    (fst
       (BDDmake
          (fst
             (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                node1 (high cfg node2) bound')) (var cfg node2)
          (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
          (fst
             (snd
                (BDDor_1
                   (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                   (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                   node1 (high cfg node2) bound'))))) node2' =
  var
    (fst
       (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
          (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound'))) node1
          (high cfg node2) bound')) node2').
intro H47.
rewrite H47.
unfold BDDor_memo_OK in H26.
exact (proj1 (proj2 (proj2 (proj2 (H26 node1' node2' node H44))))).

apply nodes_preserved_var_1.
assumption.

assumption.

apply BDDmake_preserves_nodes.
assumption.

unfold BDDor_memo_OK in H26.
exact (proj1 (proj2 (H26 node1' node2' node H44))).

apply nodes_preserved_var_1.
assumption.

assumption.

apply BDDmake_preserves_nodes; assumption.

unfold BDDor_memo_OK in H26.
exact (proj1 (H26 node1' node2' node H44)).

apply
 nodes_preserved_var_1
  with
    (cfg := fst
              (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                 (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                 node1 (high cfg node2) bound')).
assumption.

assumption.

apply BDDmake_preserves_nodes.
assumption.

exact (proj1 (proj2 (proj2 (H26 node1' node2' node H44)))).

apply
 bool_fun_eq_trans
  with
    (bf2 := bool_fun_of_BDD
              (fst
                 (BDDor_1
                    (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                    (snd
                       (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                    node1 (high cfg node2) bound')) node).
apply nodes_preserved_3.
assumption.

assumption.

apply BDDmake_preserves_nodes.
assumption.

exact (proj1 (proj2 (proj2 (H26 node1' node2' node H44)))).

apply
 bool_fun_eq_trans
  with
    (bf2 := bool_fun_or
              (bool_fun_of_BDD
                 (fst
                    (BDDor_1
                       (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                       (snd
                          (snd
                             (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                       node1 (high cfg node2) bound')) node1')
              (bool_fun_of_BDD
                 (fst
                    (BDDor_1
                       (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                       (snd
                          (snd
                             (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                       node1 (high cfg node2) bound')) node2')).
exact (proj2 (proj2 (proj2 (proj2 (H26 node1' node2' node H44))))).

apply bool_fun_eq_symm.
apply bool_fun_or_preserves_eq.
apply nodes_preserved_3.
assumption.

assumption.

apply BDDmake_preserves_nodes.
assumption.

exact (proj1 (H26 node1' node2' node H44)).

apply nodes_preserved_3.
assumption.

assumption.

apply BDDmake_preserves_nodes.
assumption.

exact (proj1 (proj2 (H26 node1' node2' node H44))).

apply
 bool_fun_eq_trans
  with
    (bf2 := bool_fun_if (var cfg node2)
              (bool_fun_or (bool_fun_of_BDD cfg node1)
                 (bool_fun_of_BDD cfg (high cfg node2)))
              (bool_fun_or (bool_fun_of_BDD cfg node1)
                 (bool_fun_of_BDD cfg (low cfg node2)))).
rewrite
 (BDDor_1_lemma_internal_2 cfg memo node1 node2 bound bound' y H0 H8 H7 H10
    y0 y1).
simpl in |- *.
apply
 bool_fun_eq_trans
  with
    (bf2 := bool_fun_if (var cfg node2)
              (bool_fun_of_BDD
                 (fst
                    (BDDor_1
                       (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                       (snd
                          (snd
                             (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                       node1 (high cfg node2) bound'))
                 (fst
                    (snd
                       (BDDor_1
                          (fst
                             (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                          (snd
                             (snd
                                (BDDor_1 cfg memo node1 
                                   (low cfg node2) bound'))) node1
                          (high cfg node2) bound'))))
              (bool_fun_of_BDD
                 (fst
                    (BDDor_1
                       (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                       (snd
                          (snd
                             (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                       node1 (high cfg node2) bound'))
                 (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound'))))).
apply BDDmake_bool_fun.
assumption.

assumption.

assumption.

assumption.

assumption.

apply bool_fun_if_preserves_eq.
apply
 bool_fun_eq_trans
  with
    (bf2 := bool_fun_or
              (bool_fun_of_BDD
                 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound')) node1)
              (bool_fun_of_BDD
                 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                 (high cfg node2))).
assumption.

apply bool_fun_or_preserves_eq.
apply nodes_preserved_3.
assumption.

assumption.

assumption.

assumption.

apply nodes_preserved_3.
assumption.

assumption.

assumption.


assumption.

apply
 bool_fun_eq_trans
  with
    (bf2 := bool_fun_of_BDD
              (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
              (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))).
apply nodes_preserved_3.
assumption.

assumption.

assumption.

assumption.

assumption.

apply
 bool_fun_eq_trans
  with
    (bf2 := bool_fun_or (bool_fun_of_BDD cfg node1)
              (bool_fun_if (var cfg node2)
                 (bool_fun_of_BDD cfg (high cfg node2))
                 (bool_fun_of_BDD cfg (low cfg node2)))).
apply bool_fun_if_lemma_3.

apply bool_fun_or_preserves_eq.
unfold bool_fun_eq in |- *.
reflexivity.

apply bool_fun_eq_symm.
apply bool_fun_if_lemma_2.
assumption.

assumption.

unfold BDDvar_le in |- *.
apply Nleb_trans with (b := var cfg node2).
fold BDDvar_le in |- *.
rewrite
 (BDDor_1_lemma_internal_2 cfg memo node1 node2 bound bound' y H0 H8 H7 H10
    y0 y1).
simpl in |- *.
apply BDDmake_var_order.
assumption.

assumption.

assumption.

assumption.

assumption.

fold BDDvar_le in |- *.
apply BDDvar_le_max_2.

apply
 nodes_preserved_trans
  with (cfg2 := fst (BDDor_1 cfg memo node1 (low cfg node2) bound')).
assumption.

apply
 nodes_preserved_trans
  with
    (cfg2 := fst
               (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                  (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                  node1 (high cfg node2) bound')).
assumption.

rewrite
 (BDDor_1_lemma_internal_2 cfg memo node1 node2 bound bound' y H0 H8 H7 H10
    y0 y1).
simpl in |- *.
apply BDDmake_preserves_nodes.
assumption.

rewrite
 (BDDor_1_lemma_internal_2 cfg memo node1 node2 bound bound' y H0 H8 H7 H10
    y0 y1).
simpl in |- *.
exact H38.

rewrite
 (BDDor_1_lemma_internal_2 cfg memo node1 node2 bound bound' y H0 H8 H7 H10
    y0 y1).
simpl in |- *.
exact H34.

apply BDDmake_semantics.
assumption.

assumption.

assumption.

intros xl ll rl H34.
cut
 (xl =
  var
    (fst
       (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
          (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound'))) node1
          (high cfg node2) bound'))
    (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))).
intro H35.
rewrite H35.
apply H32.
split with xl.
split with ll.
split with rl.
assumption.

unfold var in |- *.
rewrite H34.
reflexivity.

intros xr lr rr H34.
cut
 (xr =
  var
    (fst
       (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
          (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound'))) node1
          (high cfg node2) bound'))
    (fst
       (snd
          (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
             (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
             node1 (high cfg node2) bound')))).
intro H35.
rewrite H35.
apply H33.
split with xr.
split with lr.
split with rr.
assumption.

unfold var in |- *; rewrite H34; reflexivity.

intro H33.
apply
 BDDcompare_le_INFERIEUR_1
  with
    (y := BDDvar_max
            (var (fst (BDDor_1 cfg memo node1 (low cfg node2) bound')) node1)
            (var (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
               (high cfg node2))).
assumption.

cut
 (var (fst (BDDor_1 cfg memo node1 (low cfg node2) bound')) node1 =
  var cfg node1).
intro H34.
rewrite H34.
cut
 (var (fst (BDDor_1 cfg memo node1 (low cfg node2) bound')) (high cfg node2) =
  var cfg (high cfg node2)).
intro; rewrite H35.
apply BDDvar_ordered_high_2.
assumption.

assumption.

assumption.

assumption.

apply nodes_preserved_var_1.
assumption.

assumption.

assumption.

assumption.

apply nodes_preserved_var_1.
assumption.

assumption.

assumption.

assumption.

intro H32.
cut
 (var
    (fst
       (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
          (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound'))) node1
          (high cfg node2) bound'))
    (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound'))) =
  var (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
    (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))).
intro H33.
rewrite H33.
apply
 BDDcompare_le_INFERIEUR_1
  with (y := BDDvar_max (var cfg node1) (var cfg (low cfg node2))).
assumption.

apply BDDvar_ordered_low_2.
assumption.

assumption.

assumption.

assumption.

apply nodes_preserved_var_1.
assumption.

assumption.

assumption.

assumption.

apply
 nodes_preserved_2
  with (cfg := fst (BDDor_1 cfg memo node1 (low cfg node2) bound')).
assumption.

assumption.

apply H.
rewrite y0; unfold lt in |- *; apply le_n.

assumption.

assumption.

assumption.

assumption.

assumption.

intros H24 H25.
cut
 (var (fst (BDDor_1 cfg memo node1 (low cfg node2) bound')) node1 =
  var cfg node1).
intro; rewrite H26.
cut
 (var (fst (BDDor_1 cfg memo node1 (low cfg node2) bound')) (high cfg node2) =
  var cfg (high cfg node2)).
intro; rewrite H27.
apply lt_trans_1 with (y := nat_of_N (var cfg node2)).
apply lt_max_nat_of_N.
apply BDDvar_ordered_high_2.
assumption.

assumption.

assumption.

assumption.

rewrite <- y0.
apply
 le_lt_trans
  with (m := max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2))).
apply le_nat_of_N_max.
apply BDDvar_le_max_2.

assumption.

apply nodes_preserved_var_1.
assumption.

assumption.

assumption.

assumption.

apply nodes_preserved_var_1.
assumption.

assumption.

assumption.

assumption.

apply nodes_preserved_2 with (cfg := cfg).

assumption.

assumption.

apply nodes_preserved_2 with (cfg := cfg).
assumption.

assumption.

apply H.
rewrite y0; unfold lt in |- *; apply le_n.

assumption.

assumption.

assumption.

assumption.

assumption.

intros H15 H16.
apply lt_trans_1 with (y := nat_of_N (var cfg node2)).
apply lt_max_nat_of_N.
apply BDDvar_ordered_low_2.
assumption.

assumption.

assumption.

assumption.

rewrite <- y0.
apply
 le_lt_trans
  with (m := max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2))).
apply le_nat_of_N_max.
apply BDDvar_le_max_2.

assumption.

apply high_OK.
assumption.

assumption.

apply high_OK.
assumption.

assumption.

apply low_OK.
assumption.

assumption.

apply low_OK.
assumption.

assumption.
Qed.