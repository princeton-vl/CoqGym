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
Require Import bdd11.

Definition is_tauto (be : bool_expr) :=
  Neqb BDDone
    (fst
       (snd (BDDof_bool_expr initBDDconfig initBDDneg_memo initBDDor_memo be))).

Definition is_valid (be : bool_expr) :=
  forall vb : var_binding, bool_fun_of_bool_expr be vb = true.

Lemma initBDDor_memo_OK : BDDor_memo_OK initBDDconfig initBDDor_memo.
Proof.
  unfold BDDor_memo_OK in |- *. intros. discriminate H.
Qed.

Lemma initBDDneg_memo_OK : BDDneg_memo_OK initBDDconfig initBDDneg_memo.
Proof.
  unfold BDDneg_memo_OK in |- *. intros. discriminate H.
Qed.

Lemma initBDDneg_memo_OK_2 : BDDneg_memo_OK_2 initBDDconfig initBDDneg_memo.
Proof.
  unfold BDDneg_memo_OK_2 in |- *. intros. discriminate H.
Qed.

Lemma is_tauto_is_correct :
 forall be : bool_expr, is_tauto be = true -> is_valid be.
Proof.
  unfold is_tauto, is_valid in |- *. intros.
  elim
   (BDDof_bool_expr_correct be initBDDconfig initBDDneg_memo initBDDor_memo
      initBDDconfig_OK initBDDneg_memo_OK_2 initBDDor_memo_OK).
  intros. elim H1. intros. elim H3. intros. elim H5. intros. elim H7. intros.
  rewrite <- (Neqb_complete _ _ H) in H9.
  exact
   (bool_fun_eq_trans _ _ _ (bool_fun_eq_symm _ _ H9)
      (bool_fun_of_BDDone _ H0) vb).
Qed.

Lemma is_tauto_is_complete :
 forall be : bool_expr, is_valid be -> is_tauto be = true.
Proof.
  unfold is_tauto, is_valid in |- *. intros.
  elim
   (BDDof_bool_expr_correct be initBDDconfig initBDDneg_memo initBDDor_memo
      initBDDconfig_OK initBDDneg_memo_OK_2 initBDDor_memo_OK).
  intros. elim H1. intros. elim H3. intros. elim H5. intros. elim H7. intros.
  rewrite <-
   (BDDunique
      (fst (BDDof_bool_expr initBDDconfig initBDDneg_memo initBDDor_memo be))
      H0 BDDone
      (fst
         (snd
            (BDDof_bool_expr initBDDconfig initBDDneg_memo initBDDor_memo be))))
   .
  reflexivity.
  unfold config_node_OK in |- *. unfold node_OK in |- *. right. left. reflexivity.
  exact H2.
  apply bool_fun_eq_symm.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_bool_expr be). exact H9.
  apply bool_fun_eq_trans with (bf2 := bool_fun_one). exact H.
  apply bool_fun_eq_symm. exact (bool_fun_of_BDDone _ H0).
Qed.