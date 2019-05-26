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

Lemma BDDor_1_lemma :
 forall (bound : nat) (cfg : BDDconfig) (node1 node2 : ad)
   (memo : BDDor_memo),
 BDDconfig_OK cfg ->
 BDDor_memo_OK cfg memo ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 (is_internal_node cfg node1 ->
  is_internal_node cfg node2 ->
  max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2)) < bound) ->
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
intro bound.
apply
 lt_wf_ind
  with
    (P := fun bound : nat =>
          forall (cfg : BDDconfig) (node1 node2 : ad) (memo : BDDor_memo),
          BDDconfig_OK cfg ->
          BDDor_memo_OK cfg memo ->
          config_node_OK cfg node1 ->
          config_node_OK cfg node2 ->
          (is_internal_node cfg node1 ->
           is_internal_node cfg node2 ->
           max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2)) <
           bound) ->
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
            (bool_fun_or (bool_fun_of_BDD cfg node1)
               (bool_fun_of_BDD cfg node2))).




clear bound.
intro bound.
intro H.
intros cfg node1 node2 memo H0 H1 H2 H3 H4.
elim (option_sum _ (BDDor_memo_lookup memo node1 node2)); intro y.
elim y; clear y.
intros node H5.
rewrite (BDDor_1_lemma_1 cfg memo node1 node2 node bound H5).
simpl in |- *.
unfold BDDor_memo_OK in H1.
split.
assumption.

split.
assumption.

split.
exact (proj1 (proj2 (proj2 (H1 node1 node2 node H5)))).

split.
unfold nodes_preserved in |- *.
intros x l r node0 H6.
assumption.

split.
exact (proj1 (proj2 (proj2 (proj2 (H1 node1 node2 node H5))))).

exact (proj2 (proj2 (proj2 (proj2 (H1 node1 node2 node H5))))).

elim H2; intro.
rewrite H5.





rewrite (BDDor_1_lemma_zero_2 cfg memo node2 bound).
simpl in |- *.
cut
 (bool_fun_eq (bool_fun_of_BDD cfg node2)
    (bool_fun_or (bool_fun_of_BDD cfg BDDzero) (bool_fun_of_BDD cfg node2))).
intro H6.
split.
assumption.

split.
unfold BDDor_memo_OK in |- *.
intros node1' node2' node.
intros H7.
rewrite (BDDor_memo_lookup_semantics memo BDDzero node2 node2 node1' node2')
  in H7.
elim (sumbool_of_bool (Neqb BDDzero node1' && Neqb node2 node2')); intro y0.
cut (BDDzero = node1').
cut (node2 = node2').
intros H8 H9.
split.
rewrite <- H9.
left; reflexivity.

split.
rewrite <- H8; assumption.

split.
rewrite y0 in H7.
injection H7.
intro H10.
rewrite <- H10.
assumption.

split.
rewrite y0 in H7.
injection H7; intro.
rewrite <- H10.
rewrite <- H8.
apply BDDvar_le_max_2.

rewrite y0 in H7; injection H7; intro.
rewrite <- H10.
rewrite <- H9.
rewrite <- H8.
assumption.



apply Neqb_complete.
exact (proj2 (andb_prop (Neqb BDDzero node1') (Neqb node2 node2') y0)).

apply Neqb_complete.
exact (proj1 (andb_prop (Neqb BDDzero node1') (Neqb node2 node2') y0)).

rewrite y0 in H7.
unfold BDDor_memo_OK in H1.
split.
exact (proj1 (H1 node1' node2' node H7)).

split.
exact (proj1 (proj2 (H1 node1' node2' node H7))).

split.
exact (proj1 (proj2 (proj2 (H1 node1' node2' node H7)))).

split.
exact (proj1 (proj2 (proj2 (proj2 (H1 node1' node2' node H7))))).

exact (proj2 (proj2 (proj2 (proj2 (H1 node1' node2' node H7))))).

split.
assumption.

split.
unfold nodes_preserved in |- *; intro.
intros l r node H7.
assumption.

split.
apply BDDvar_le_max_2.

assumption.

rewrite (proj1 (bool_fun_of_BDD_semantics cfg H0)).
apply bool_fun_eq_symm.
apply
 bool_fun_eq_trans
  with (bool_fun_or (bool_fun_of_BDD cfg node2) bool_fun_zero).
apply bool_fun_or_commute.

apply bool_fun_or_zero.



rewrite <- H5; assumption.

elim H5; clear H5; intro.
rewrite H5.
rewrite (BDDor_1_lemma_one_2 cfg memo node2 bound).
simpl in |- *.
cut
 (bool_fun_eq (bool_fun_of_BDD cfg BDDone)
    (bool_fun_or (bool_fun_of_BDD cfg BDDone) (bool_fun_of_BDD cfg node2))).
intro H6.
split.
assumption.

split.
unfold BDDor_memo_OK in |- *.
intros node1' node2' node.
intros H7.
rewrite (BDDor_memo_lookup_semantics memo BDDone node2 BDDone node1' node2')
  in H7.
elim (sumbool_of_bool (Neqb BDDone node1' && Neqb node2 node2')); intro y0.
cut (BDDone = node1').
cut (node2 = node2').
intros H8 H9.
split.
rewrite <- H9.
right; left; reflexivity.

split.
rewrite <- H8; assumption.

split.
rewrite y0 in H7.
injection H7.
intro H10.
rewrite <- H10.
right; left; reflexivity.

split.
rewrite y0 in H7.
injection H7; intro.
rewrite <- H10.
rewrite <- H8.
unfold var at 1 in |- *.
rewrite (config_OK_one cfg H0).




unfold BDDzero in |- *.
apply BDDvar_le_z.

rewrite y0 in H7; injection H7; intro.
rewrite <- H10.
rewrite <- H9.
rewrite <- H8.
assumption.

apply Neqb_complete.
exact (proj2 (andb_prop (Neqb BDDone node1') (Neqb node2 node2') y0)).

apply Neqb_complete.
exact (proj1 (andb_prop (Neqb BDDone node1') (Neqb node2 node2') y0)).

rewrite y0 in H7.
unfold BDDor_memo_OK in H1.
split.
exact (proj1 (H1 node1' node2' node H7)).

split.
exact (proj1 (proj2 (H1 node1' node2' node H7))).

split.
exact (proj1 (proj2 (proj2 (H1 node1' node2' node H7)))).

split.
exact (proj1 (proj2 (proj2 (proj2 (H1 node1' node2' node H7))))).

exact (proj2 (proj2 (proj2 (proj2 (H1 node1' node2' node H7))))).

split.
right; left; reflexivity.

split.
unfold nodes_preserved in |- *; intro.
intros l r node H7.
assumption.





split.
apply BDDvar_le_max_1.

assumption.

rewrite (proj1 (proj2 (bool_fun_of_BDD_semantics cfg H0))).
apply
 bool_fun_eq_trans
  with (bf2 := bool_fun_or (bool_fun_of_BDD cfg node2) bool_fun_one).
apply bool_fun_eq_symm.
apply bool_fun_or_one.

apply bool_fun_or_commute.

rewrite <- H5; assumption.

elim H3; intro.
rewrite H6.
rewrite (BDDor_1_lemma_zero_1 cfg memo node1 bound).
simpl in |- *.
cut
 (bool_fun_eq (bool_fun_of_BDD cfg node1)
    (bool_fun_or (bool_fun_of_BDD cfg node1) (bool_fun_of_BDD cfg BDDzero))).
intro H7.
split.
assumption.

split.
unfold BDDor_memo_OK in |- *.
intros node1' node2' node.
intros H8.
rewrite (BDDor_memo_lookup_semantics memo node1 BDDzero node1 node1' node2')
  in H8.
elim (sumbool_of_bool (Neqb node1 node1' && Neqb BDDzero node2')); intro y0.
cut (node1 = node1').
cut (BDDzero = node2').
intros H9 H10.
split.
rewrite <- H10; assumption.

split.
rewrite <- H9; left; reflexivity.

split.
rewrite y0 in H8.
injection H8; intro.








rewrite <- H11; assumption.

split.
rewrite y0 in H8.
injection H8; intro.
rewrite <- H10.
rewrite <- H11.
apply BDDvar_le_max_1.

rewrite <- H9.
rewrite <- H10.
rewrite y0 in H8; injection H8; intro.
rewrite <- H11.
assumption.

apply Neqb_complete.
exact (proj2 (andb_prop (Neqb node1 node1') (Neqb BDDzero node2') y0)).

apply Neqb_complete.
exact (proj1 (andb_prop (Neqb node1 node1') (Neqb BDDzero node2') y0)).

rewrite y0 in H8.
unfold BDDor_memo_OK in H1.
split.
exact (proj1 (H1 node1' node2' node H8)).

split.
exact (proj1 (proj2 (H1 node1' node2' node H8))).

split.
exact (proj1 (proj2 (proj2 (H1 node1' node2' node H8)))).

split.
exact (proj1 (proj2 (proj2 (proj2 (H1 node1' node2' node H8))))).

exact (proj2 (proj2 (proj2 (proj2 (H1 node1' node2' node H8))))).

split.






assumption.

split.
unfold nodes_preserved in |- *; intro.
intros l r node H8.
assumption.

split.
apply BDDvar_le_max_1.

assumption.

rewrite (proj1 (bool_fun_of_BDD_semantics cfg H0)).
apply bool_fun_eq_symm.
apply bool_fun_or_zero.

rewrite <- H6; assumption.

elim H6.
clear H5 H6.
intro H5.
rewrite H5.
rewrite (BDDor_1_lemma_one_1 cfg memo node1 bound).
simpl in |- *.
cut
 (bool_fun_eq (bool_fun_of_BDD cfg BDDone)
    (bool_fun_or (bool_fun_of_BDD cfg node1) (bool_fun_of_BDD cfg BDDone))).
intro H6.
split.
assumption.

split.
unfold BDDor_memo_OK in |- *.
intros node1' node2' node.
intros H7.
rewrite (BDDor_memo_lookup_semantics memo node1 BDDone BDDone node1' node2')
  in H7.
elim (sumbool_of_bool (Neqb node1 node1' && Neqb BDDone node2')); intro y0.
cut (node1 = node1').
cut (BDDone = node2').
intros H8 H9.
intros.








split.
rewrite <- H9; assumption.

split.
rewrite <- H8; right; left; reflexivity.

split.
rewrite y0 in H7.
injection H7.
intro H10.
rewrite <- H10.
right; left; reflexivity.

split.
rewrite y0 in H7.
injection H7; intro.
rewrite <- H10.
rewrite <- H9.
rewrite <- H8.
apply BDDvar_le_max_2.

rewrite y0 in H7; injection H7; intro.
rewrite <- H10.
rewrite <- H9.
rewrite <- H8.
assumption.

apply Neqb_complete.
exact (proj2 (andb_prop (Neqb node1 node1') (Neqb BDDone node2') y0)).

apply Neqb_complete.
exact (proj1 (andb_prop (Neqb node1 node1') (Neqb BDDone node2') y0)).

rewrite y0 in H7.
unfold BDDor_memo_OK in H1.
split.
exact (proj1 (H1 node1' node2' node H7)).






split.
exact (proj1 (proj2 (H1 node1' node2' node H7))).

split.
exact (proj1 (proj2 (proj2 (H1 node1' node2' node H7)))).

split.
exact (proj1 (proj2 (proj2 (proj2 (H1 node1' node2' node H7))))).

exact (proj2 (proj2 (proj2 (proj2 (H1 node1' node2' node H7))))).

split.
right; left; reflexivity.

split.
unfold nodes_preserved in |- *; intro.
intros l r node H7.
assumption.

split.
apply BDDvar_le_max_2.

assumption.

rewrite (proj1 (proj2 (bool_fun_of_BDD_semantics cfg H0))).
apply bool_fun_eq_symm.
apply bool_fun_or_one.

rewrite <- H5; assumption.

cut (is_internal_node cfg node1).



intros H8 H9.
cut (is_internal_node cfg node2).
intro H7.
elim (nat_sum bound).
intro y0.
elim y0; clear y0.
intro bound'.
intro y0.
cut (max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2)) < bound).
intro H10.
elim (relation_sum (BDDcompare (var cfg node1) (var cfg node2))); intro y1.
elim y1; clear y1; intro.
apply BDDdummy_lemma_2 with (bound' := bound').
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
apply BDDdummy_lemma_3 with (bound' := bound').
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
cut (BDDcompare (var cfg node2) (var cfg node1) = Datatypes.Lt).
intro y11.
apply BDDdummy_lemma_4 with (bound' := bound').
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
apply BDDcompare_sup_inf.
assumption.
apply H4.
assumption.

assumption.

intro y0.
rewrite y0 in H4.
absurd (max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2)) < 0).
apply lt_n_O.

apply H4.
assumption.

assumption.

apply in_dom_is_internal.
assumption.

apply in_dom_is_internal.
assumption.
Qed.