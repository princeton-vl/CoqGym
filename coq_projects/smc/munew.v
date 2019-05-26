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
Require Import Wf_nat.
Require Import EqNat.
Require Import Peano_dec.
Require Import Ensembles.
Require Import Finite_sets.
Require Import Finite_sets_facts.
Require Import Image.
Require Import List.
Require Import Compare.
 
Require Import misc.
Require Import bool_fun.
Require Import myMap.
Require Import config.
Require Import alloc.
Require Import make.
Require Import neg.
Require Import or.
Require Import univ.
Require Import op.
Require Import tauto.
Require Import quant.
Require Import gc.
Require Import mu.

Section New.

Variable N : nat.

Definition var_env'_dash (ve : var_env') (n : nat) :=
  if leb N n then ve (n - N) else false.

Definition var_env''_dash (ve : var_env'') :=
  var_env'_to_env'' N (2 * N) (var_env'_dash (var_env''_to_env' ve)).
 
Fixpoint be_dash (be : bool_expr) : bool_expr :=
  match be with
  | Zero => Zero
  | One => One
  | Var x => Var (N_of_nat (N + nat_of_N x))
  | Neg be' => Neg (be_dash be')
  | Or be1 be2 => Or (be_dash be1) (be_dash be2)
  | ANd be1 be2 => ANd (be_dash be1) (be_dash be2)
  | Impl be1 be2 => Impl (be_dash be1) (be_dash be2)
  | Iff be1 be2 => Iff (be_dash be1) (be_dash be2)
  end.
 
Fixpoint renamef (f : ad -> ad) (be : bool_expr) {struct be} : bool_expr :=
  match be with
  | Zero => Zero
  | One => One
  | Var x => Var (f x)
  | Neg be' => Neg (renamef f be')
  | Or be1 be2 => Or (renamef f be1) (renamef f be2)
  | ANd be1 be2 => ANd (renamef f be1) (renamef f be2)
  | Impl be1 be2 => Impl (renamef f be1) (renamef f be2)
  | Iff be1 be2 => Iff (renamef f be1) (renamef f be2)
  end.

Definition renfnat (n m : nat) := if leb n m then m else m + N.

Definition renfnad (n : nat) (x : ad) := N_of_nat (renfnat n (nat_of_N x)). 

Lemma dash_renf :
 forall be : bool_expr,
 be_ok (var_lu 0 N) be -> be_dash be = renamef (renfnad N) be.
Proof.
  simple induction be.  reflexivity.  reflexivity.  unfold renamef in |- *.  simpl in |- *.
  unfold renfnad in |- *.  unfold renfnat in |- *.  intros.  elim (var_ok_inv _ _ H).
  cut (var_lu 0 N b = true).  intro.  unfold var_lu in H0.
  elim (andb_prop _ _ H0).  intros.
  replace (leb N (nat_of_N b)) with false.
  rewrite (plus_comm N (nat_of_N b)).  reflexivity.  symmetry  in |- *.
  apply leb_correct_conv.  unfold lt in |- *.  apply leb_complete.  assumption.  
  apply var_ok_inv.  assumption.  intros.  simpl in |- *.  rewrite H.  reflexivity.  
  apply neg_ok_inv.  assumption.  intros.  simpl in |- *.  rewrite H.  rewrite H0.
  reflexivity.  exact (proj2 (or_ok_inv _ _ _ H1)).  
  exact (proj1 (or_ok_inv _ _ _ H1)).  intros.  simpl in |- *.  rewrite H.
  rewrite H0.  reflexivity.  exact (proj2 (and_ok_inv _ _ _ H1)).  
  exact (proj1 (and_ok_inv _ _ _ H1)).  intros.  simpl in |- *.  rewrite H.
  rewrite H0.  reflexivity.  exact (proj2 (impl_ok_inv _ _ _ H1)).  
  exact (proj1 (impl_ok_inv _ _ _ H1)).  intros.  simpl in |- *.  rewrite H.
  rewrite H0.  reflexivity.  exact (proj2 (iff_ok_inv _ _ _ H1)).  
  exact (proj1 (iff_ok_inv _ _ _ H1)).
Qed.

Lemma dash_be_ok :
 forall be : bool_expr,
 be_ok (var_lu 0 N) be -> be_ok (var_lu N (2 * N)) (be_dash be).
Proof.
  simple induction be.  intro.  apply zero_ok.  intro.  apply one_ok.  intros.  simpl in |- *.
  apply var_ok.  inversion H.  unfold var_lu in H1.  elim (andb_prop _ _ H1).
  intros.  unfold var_lu in |- *.  apply andb_true_intro.  split.
  rewrite (nat_of_N_of_nat (N + nat_of_N b)).  apply leb_correct.
  apply le_plus_l.  rewrite (nat_of_N_of_nat (N + nat_of_N b)).
  replace (S (N + nat_of_N b)) with (S N + nat_of_N b).
  rewrite (plus_Snm_nSm N (nat_of_N b)).  apply leb_correct.
  apply plus_le_compat.  apply le_n.  rewrite <- (plus_n_O N).
  apply leb_complete.  assumption.  simpl in |- *.  reflexivity.  simpl in |- *.  intros.
  inversion H0.  apply neg_ok.  apply H.  assumption.  simpl in |- *.  intros.
  inversion H1.  apply or_ok; [ apply H; assumption | apply H0; assumption ].
  simpl in |- *.  intros.  inversion H1.
  apply and_ok; [ apply H; assumption | apply H0; assumption ].  simpl in |- *.  intros.
  inversion H1.  apply impl_ok; [ apply H; assumption | apply H0; assumption ].
  simpl in |- *.  intros.  inversion H1.
  apply iff_ok; [ apply H; assumption | apply H0; assumption ].
Qed.

Lemma eval_dash_lemma1 :
 forall (be : bool_expr) (ve : var_env'),
 eval_be' be ve = eval_be' (be_dash be) (var_env'_dash ve).
Proof.
  simple induction be.  unfold eval_be' in |- *.  simpl in |- *.  unfold bool_fun_zero in |- *.  reflexivity.
  unfold eval_be' in |- *.  simpl in |- *.  unfold bool_fun_one in |- *.  reflexivity.  simpl in |- *.
  unfold eval_be' in |- *.  simpl in |- *.  unfold bool_fun_var in |- *.  unfold var_env'_dash in |- *.
  unfold var_env'_to_env in |- *.  intros.
  rewrite (nat_of_N_of_nat (N + nat_of_N b)).
  elim (sumbool_of_bool (leb N (N + nat_of_N b))).  intro y.  rewrite y.
  rewrite (minus_plus N (nat_of_N b)).  reflexivity.
  replace (leb N (N + nat_of_N b)) with true.  intro.  discriminate.  
  symmetry  in |- *.  apply leb_correct.  apply le_plus_l.  intros.  simpl in |- *.
  unfold eval_be' in |- *.  unfold eval_be' in H.  simpl in |- *.  unfold bool_fun_neg in |- *.
  rewrite (H ve).  reflexivity.  unfold eval_be' in |- *.  simpl in |- *.  unfold bool_fun_or in |- *.
  intros.  rewrite (H ve).  rewrite (H0 ve).  reflexivity.  unfold eval_be' in |- *.
  simpl in |- *.  unfold bool_fun_and in |- *.  intros.  rewrite (H ve).  rewrite (H0 ve).
  reflexivity.  unfold eval_be' in |- *.  simpl in |- *.  unfold bool_fun_impl in |- *.  intros.
  rewrite (H ve).  rewrite (H0 ve).  reflexivity.  unfold eval_be' in |- *.  simpl in |- *.
  unfold bool_fun_iff in |- *.  intros.  rewrite (H ve).  rewrite (H0 ve).  reflexivity.
Qed.
 
Definition var_env_or (ve1 ve2 : var_env) (x : ad) := ve1 x || ve2 x.
Definition var_env'_or (ve1 ve2 : var_env') (x : nat) := ve1 x || ve2 x.
 
Lemma forall_lemma1 :
 forall (be : bool_expr) (ve : var_env) (a : ad),
 bool_fun_of_bool_expr (forall_ a be) ve = true ->
 bool_fun_of_bool_expr be ve = true.
Proof.
  intros.  rewrite (forall_OK a be ve) in H.  unfold bool_fun_forall in H.
  unfold bool_fun_and in H.  elim (andb_prop _ _ H).  intros.
  elim (sumbool_of_bool (ve a)).  intro y.  rewrite <- H0.
  unfold bool_fun_restrict in |- *.  apply (bool_fun_of_be_ext be).  intros.
  unfold augment in |- *.  elim (sumbool_of_bool (Neqb a x)).  intro y0.  rewrite y0.
  rewrite (Neqb_complete _ _ y0) in y.  assumption.  intro y0.  rewrite y0.
  reflexivity.  intro y.  rewrite <- H1.  unfold bool_fun_restrict in |- *.
  apply (bool_fun_of_be_ext be).  intros.  unfold augment in |- *.
  elim (sumbool_of_bool (Neqb a x)).  intro y0.  rewrite y0.
  rewrite (Neqb_complete _ _ y0) in y.  assumption.  intro y0.  rewrite y0.
  reflexivity.
Qed.

Lemma renamef_ext :
 forall (be : bool_expr) (f g : ad -> ad),
 (forall x : ad, f x = g x) -> renamef f be = renamef g be.
Proof.
  simple induction be.  reflexivity.  reflexivity.  simpl in |- *.  intros.  rewrite (H b).
  reflexivity.  intros.  simpl in |- *.  rewrite (H _ _ H0).  reflexivity.  intros.
  simpl in |- *.  rewrite (H _ _ H1).  rewrite (H0 _ _ H1).  reflexivity.  intros.
  simpl in |- *.  rewrite (H _ _ H1).  rewrite (H0 _ _ H1).  reflexivity.  intros.
  simpl in |- *.  rewrite (H _ _ H1).  rewrite (H0 _ _ H1).  reflexivity.  intros.
  simpl in |- *.  rewrite (H _ _ H1).  rewrite (H0 _ _ H1).  reflexivity.
Qed.

Lemma renamef_id : forall be : bool_expr, renamef (fun x => x) be = be.
Proof.
  simple induction be.  reflexivity.  reflexivity.  reflexivity.  intros.  simpl in |- *.
  rewrite H.  reflexivity.  intros.  simpl in |- *.  rewrite H.  rewrite H0.
  reflexivity.  intros.  simpl in |- *.  rewrite H.  rewrite H0.  reflexivity.  intros.
  simpl in |- *.  rewrite H.  rewrite H0.  reflexivity.  intros.  simpl in |- *.  rewrite H.
  rewrite H0.  reflexivity.
Qed.

Lemma renamefS :
 forall (be : bool_expr) (n : nat),
 n < N ->
 renamef (renfnad (S n)) be =
 subst (ap n) (Var (ap' N n)) (renamef (renfnad n) be).
Proof.
  simple induction be.  simpl in |- *.  reflexivity.  reflexivity.  intros.  simpl in |- *.
  unfold renfnad at 2 in |- *.  unfold renfnat in |- *.
  elim (sumbool_of_bool (leb n (nat_of_N b))).  intro y.  rewrite y.
  rewrite (N_of_nat_of_N b).  unfold ap in |- *.
  elim (sumbool_of_bool (Neqb (N_of_nat n) b)).  intro y0.  rewrite y0.
  unfold renfnad, ap' in |- *.  unfold renfnat in |- *.  rewrite <- (Neqb_complete _ _ y0).
  rewrite (nat_of_N_of_nat n).  replace (leb (S n) n) with false.
  rewrite (plus_comm n N).  reflexivity.  symmetry  in |- *.  apply leb_correct_conv.
  auto.  intro y0.  rewrite y0.  unfold renfnad in |- *.  unfold renfnat in |- *.  rewrite y.
  rewrite (N_of_nat_of_N b).  replace (leb (S n) (nat_of_N b)) with true.
  rewrite (N_of_nat_of_N b).  reflexivity.  symmetry  in |- *.
  elim (le_le_S_eq _ _ (leb_complete _ _ y)).  intro.  apply leb_correct.
  assumption.  intro.  rewrite H0 in y0.  rewrite (N_of_nat_of_N b) in y0.
  rewrite (Neqb_correct b) in y0.  discriminate.  intro y.  rewrite y.
  unfold renfnad at 1 in |- *.  unfold renfnat at 1 in |- *.
  replace (leb (S n) (nat_of_N b)) with false.
  replace (Neqb (ap n) (N_of_nat (nat_of_N b + N))) with false.
  unfold renfnad in |- *.  unfold renfnat in |- *.  rewrite y.  reflexivity.  symmetry  in |- *.
  apply not_true_is_false.  unfold not in |- *; intro.  unfold ap in H0.
  rewrite <- (nat_of_N_of_nat n) in H.
  rewrite (Neqb_complete _ _ H0) in H.
  rewrite (nat_of_N_of_nat (nat_of_N b + N)) in H.  apply (lt_irrefl N).
  apply le_lt_trans with (m := nat_of_N b + N).  apply le_plus_r.
  assumption.  symmetry  in |- *.  apply not_true_is_false.  unfold not in |- *; intro.
  cut (leb n (nat_of_N b) = true).  intro.  rewrite H1 in y.  discriminate.
  apply leb_correct.  apply le_trans with (m := S n).  apply le_S.  apply le_n.  apply leb_complete.  assumption.  intros.  simpl in |- *.  rewrite (H n H0).
  reflexivity.  intros.  simpl in |- *.  rewrite (H n H1).  rewrite (H0 n H1).
  reflexivity.  intros.  simpl in |- *.  rewrite (H n H1).  rewrite (H0 n H1).
  reflexivity.  intros.  simpl in |- *.  rewrite (H n H1).  rewrite (H0 n H1).
  reflexivity.  intros.  simpl in |- *.  rewrite (H n H1).  rewrite (H0 n H1).
  reflexivity.
Qed.

Lemma replacel_lemma :
 forall (n : nat) (be : bool_expr),
 n <= N -> replacel be (lx_1 n) (lx'_1 N n) = renamef (renfnad n) be.
Proof.
  simple induction n.  simpl in |- *.  unfold renfnad in |- *.  unfold renfnat in |- *.  intro.  intro.
  replace
   (renamef
      (fun x : ad =>
       N_of_nat
         match leb 0 (nat_of_N x) with
         | true => nat_of_N x
         | false => nat_of_N x + N
         end) be) with (renamef (fun x => x) be).
  symmetry  in |- *.  apply renamef_id.  apply renamef_ext.  intro.
  rewrite (leb_correct 0 (nat_of_N x) (le_O_n _)).  symmetry  in |- *.
  apply N_of_nat_of_N.  simpl in |- *.  intros.  rewrite (H be).  unfold replace in |- *.
  symmetry  in |- *.  unfold replace in |- *.  apply renamefS.  assumption.
  apply le_trans with (m := S n0).  apply le_S.  apply le_n.  assumption.
Qed.

Lemma replacel_lemma2 :
 forall be : bool_expr,
 be_ok (var_lu 0 N) be -> replacel be (lx N) (lx' N) = be_dash be.
Proof.
  intros.  unfold lx, lx' in |- *.  rewrite (replacel_lemma N be (le_n _)).  symmetry  in |- *.
  apply dash_renf.  assumption.
Qed.

Lemma exl_semantics :
 forall (lx : list ad) (be : bool_expr) (ve : var_env'),
 (forall n : nat, ve n = true -> ~ In (N_of_nat n) lx) ->
 no_dup_list _ lx ->
 (eval_be' (exl be lx) ve = true <->
  (exists ve' : var_env',
     (forall n : nat, ve' n = true -> In (N_of_nat n) lx) /\
     eval_be' be (var_env'_or ve ve') = true)).
Proof.
  simple induction lx.  simpl in |- *.  intros be ve H H00.  split.  intro.
  split with (fun n : nat => false).  split.  intros.  discriminate.  unfold var_env'_or in |- *.
  rewrite <- H0.  unfold eval_be' in |- *.  apply (bool_fun_of_be_ext be).
  unfold var_env'_to_env in |- *.  intro.  elim (ve (nat_of_N x)); reflexivity.  
  intros.  elim H0; clear H0.  intros ve' H0.  inversion H0.  clear H0.
  rewrite <- H2.  unfold eval_be' in |- *.  apply (bool_fun_of_be_ext be).
  unfold var_env'_to_env in |- *.  unfold var_env'_or in |- *.  intro.
  replace (ve' (nat_of_N x)) with false.  elim (ve (nat_of_N x)); reflexivity.
  symmetry  in |- *.  apply not_true_is_false.  unfold not in |- *; intro.  exact (H1 _ H0).  
  intros a l H be ve H0 H00.  split.  intros.  simpl in H1.
  unfold eval_be' in H1.
  rewrite (ex_OK a (exl be l) (var_env'_to_env ve)) in H1.
  unfold bool_fun_ex in H1.  unfold bool_fun_or in H1.
  unfold bool_fun_restrict in H1.  elim (orb_prop _ _ H1); clear H1; intros.
  elim
   (H be
      (fun n : nat =>
       match Neqb (N_of_nat n) a with
       | true => true
       | false => ve n
       end)).
  intros.  clear H3.  elim H2.  intros ve' H3.  inversion H3.  clear H3.
  split
   with
     (fun n : nat =>
      match Neqb (N_of_nat n) a with
      | true => true
      | false => ve' n
      end).
  split.  intros.  elim (sumbool_of_bool (Neqb (N_of_nat n) a)).  intro y.
  rewrite <- (Neqb_complete _ _ y).  left.  reflexivity.  intro y.
  rewrite y in H3.  right.  apply H4; assumption.  
  replace
   (eval_be' be
      (var_env'_or ve
         (fun n : nat =>
          match Neqb (N_of_nat n) a with
          | true => true
          | false => ve' n
          end))) with
   (eval_be' be
      (var_env'_or
         (fun n : nat =>
          match Neqb (N_of_nat n) a with
          | true => true
          | false => ve n
          end) ve')).
  assumption.  unfold eval_be', var_env'_or in |- *.  apply (bool_fun_of_be_ext be).
  unfold var_env'_to_env in |- *.  intro.  rewrite (N_of_nat_of_N x).
  elim (Neqb x a).  auto with bool.  auto with bool.  unfold eval_be' in |- *.
  replace
   (bool_fun_of_bool_expr (exl be l)
      (var_env'_to_env
         (fun n : nat =>
          match Neqb (N_of_nat n) a with
          | true => true
          | false => ve n
          end))) with
   (bool_fun_of_bool_expr (exl be l) (augment (var_env'_to_env ve) a true)).
  assumption.  apply (bool_fun_of_be_ext (exl be l)).
  unfold augment, var_env'_to_env in |- *.  intro.  rewrite (N_of_nat_of_N x).
  rewrite (Neqb_comm a x).  reflexivity.  intros.
  elim (sumbool_of_bool (Neqb (N_of_nat n) a)).  intro y.
  rewrite (Neqb_complete _ _ y).  apply no_dup_cons_no_in.  assumption.  intro y.
  rewrite y in H2.  simpl in H0.  exact (fun x => H0 _ H2 (or_intror _ x)).  
  apply no_dup_cons_no_dup with (a := a).  assumption.  
  elim
   (H be
      (fun n : nat =>
       match Neqb (N_of_nat n) a with
       | true => false
       | false => ve n
       end)).
  intros.  clear H3 H.  elim H2.  intros ve' H.  inversion H.  clear H.
  clear H2.  split with ve'.  split.  intros.  right.  apply H3.  assumption.
  rewrite <- H4.  unfold eval_be' in |- *.  apply (bool_fun_of_be_ext be).
  unfold var_env'_to_env, var_env'_or in |- *.  intro.  rewrite (N_of_nat_of_N x).
  elim (sumbool_of_bool (Neqb x a)).  intro y.  rewrite y.  simpl in |- *.
  rewrite (Neqb_complete _ _ y).  elim (sumbool_of_bool (ve (nat_of_N a))).
  intro y0.  elim (H0 _ y0).  rewrite (N_of_nat_of_N a).  left.  reflexivity.  
  intro y0.  rewrite y0.  reflexivity.  intro y.  rewrite y.  reflexivity.  
  rewrite <- H1.  unfold eval_be' in |- *.  apply (bool_fun_of_be_ext (exl be l)).
  unfold var_env'_to_env, augment in |- *.  intro.  rewrite (N_of_nat_of_N x).
  rewrite (Neqb_comm a x).  reflexivity.  intros.
  elim (sumbool_of_bool (Neqb (N_of_nat n) a)).  intro y.
  rewrite (Neqb_complete _ _ y).  apply no_dup_cons_no_in.  assumption.  intro y.
  rewrite y in H2.  exact (fun x => H0 _ H2 (or_intror _ x)).  
  apply no_dup_cons_no_dup with (a := a).  assumption.  intros.  elim H1; clear H1.
  intros ve' H1.  inversion H1.  clear H1.  simpl in |- *.  unfold eval_be' in |- *.
  rewrite (ex_OK a (exl be l) (var_env'_to_env ve)).  unfold bool_fun_ex in |- *.
  unfold bool_fun_or in |- *.  unfold bool_fun_restrict in |- *.
  elim (sumbool_of_bool (ve' (nat_of_N a))).  intro y.
  elim
   (H be
      (fun n : nat =>
       match Neqb (N_of_nat n) a with
       | true => true
       | false => ve n
       end)).
  intros.  clear H1 H.  apply orb_true_intro.  left.
  replace
   (bool_fun_of_bool_expr (exl be l) (augment (var_env'_to_env ve) a true))
   with
   (eval_be' (exl be l)
      (fun n : nat =>
       match Neqb (N_of_nat n) a with
       | true => true
       | false => ve n
       end)).
  apply H4.  split
   with
     (fun n : nat =>
      match Neqb (N_of_nat n) a with
      | true => false
      | false => ve' n
      end).
  split.  intros.  elim (sumbool_of_bool (Neqb (N_of_nat n) a)).  intro y0.
  rewrite y0 in H.  discriminate.  intro y0.  rewrite y0 in H.  elim (H2 _ H).
  intro.  rewrite <- H1 in y0.  rewrite (Neqb_correct a) in y0.  discriminate.
  auto.  replace
   (eval_be' be
      (var_env'_or
         (fun n : nat =>
          match Neqb (N_of_nat n) a with
          | true => true
          | false => ve n
          end)
         (fun n : nat =>
          match Neqb (N_of_nat n) a with
          | true => false
          | false => ve' n
          end))) with (eval_be' be (var_env'_or ve ve')).
  assumption.  unfold eval_be' in |- *.  apply (bool_fun_of_be_ext be).  intro x.
  unfold var_env'_to_env, var_env'_or in |- *.  rewrite (N_of_nat_of_N x).
  elim (sumbool_of_bool (Neqb x a)).  intro y0.  rewrite y0.
  rewrite (Neqb_complete _ _ y0).  rewrite y.  auto with bool.  intro y0.
  rewrite y0.  reflexivity.  unfold eval_be' in |- *.
  apply (bool_fun_of_be_ext (exl be l)).  unfold var_env'_to_env, augment in |- *.
  intros.  rewrite (N_of_nat_of_N x).  rewrite (Neqb_comm a x).  reflexivity.
  intros.  elim (sumbool_of_bool (Neqb (N_of_nat n) a)).  intro y0.
  rewrite (Neqb_complete _ _ y0).  apply no_dup_cons_no_in.  assumption.
  intro y0.  rewrite y0 in H1.  exact (fun x => H0 _ H1 (or_intror _ x)).  
  apply no_dup_cons_no_dup with (a := a).  assumption.  intro y.  elim (H be ve).
  intros.  clear H H1.  apply orb_true_intro.  right.  rewrite <- H4.
  unfold eval_be' in |- *.  apply (bool_fun_of_be_ext (exl be l)).
  unfold augment, var_env'_to_env in |- *.  intro.  elim (sumbool_of_bool (Neqb a x)).
  intro y0.  rewrite y0.  symmetry  in |- *.  rewrite <- (Neqb_complete _ _ y0).
  apply not_true_is_false.  unfold not in |- *; intro.  apply (H0 _ H).  left.
  symmetry  in |- *.  apply N_of_nat_of_N.  intro y0.  rewrite y0.  reflexivity.
  split with ve'.  split.  intros.  elim (H2 _ H).  intro.  rewrite H1 in y.
  rewrite (nat_of_N_of_nat n) in y.  rewrite H in y.  discriminate.  auto.  
  assumption.  intros.  exact (fun x => H0 _ H1 (or_intror _ x)).  
  apply no_dup_cons_no_dup with (a := a).  assumption.  
Qed.

Lemma univl_semantics :
 forall (lx : list ad) (be : bool_expr) (ve : var_env'),
 (forall n : nat, ve n = true -> ~ In (N_of_nat n) lx) ->
 no_dup_list _ lx ->
 (eval_be' (univl be lx) ve = true <->
  (forall ve' : var_env',
   (forall n : nat, ve' n = true -> In (N_of_nat n) lx) ->
   eval_be' be (var_env'_or ve ve') = true)).
Proof.
  simple induction lx.  simpl in |- *.  intros be ve H H00.  intros.  split.  intro.  intros.
  unfold eval_be' in |- *.
  replace (bool_fun_of_bool_expr be (var_env'_to_env (var_env'_or ve ve')))
   with (bool_fun_of_bool_expr be (var_env'_to_env ve)).
  assumption.  apply (bool_fun_of_be_ext be).  intros.  unfold var_env'_or in |- *.
  unfold var_env'_to_env in |- *.  replace (ve' (nat_of_N x)) with false.
  elim (ve (nat_of_N x)); reflexivity.  symmetry  in |- *.  apply not_true_is_false.
  unfold not in |- *; intro.  exact (H1 _ H2).  intros.
  replace (eval_be' be ve) with
   (eval_be' be (var_env'_or ve (fun n => false))).
  apply H0.  intros.  discriminate.  unfold eval_be' in |- *.
  apply (bool_fun_of_be_ext be).  intro.  unfold var_env'_to_env in |- *.
  unfold var_env'_or in |- *.  elim (ve (nat_of_N x)); reflexivity.  simpl in |- *.
  intros a l H be ve H0 H00.  intros.  split.  intros.  unfold eval_be' in H1.
  elim (sumbool_of_bool (ve' (nat_of_N a))).  intro y.
  rewrite (forall_OK a (univl be l) (var_env'_to_env ve)) in H1.
  unfold bool_fun_forall in H1.  unfold bool_fun_and in H1.
  elim (andb_prop _ _ H1).  intros.  clear H1.  clear H4.
  unfold bool_fun_restrict in H3.
  replace (eval_be' be (var_env'_or ve ve')) with
   (eval_be' be
      (var_env'_or
         (fun n : nat =>
          match Neqb (N_of_nat n) a with
          | true => true
          | false => ve n
          end)
         (fun n : nat =>
          match Neqb (N_of_nat n) a with
          | true => false
          | false => ve' n
          end))).
  elim
   (H be
      (fun n : nat =>
       match Neqb (N_of_nat n) a with
       | true => true
       | false => ve n
       end)).
  intros.  clear H4.  apply H1.  unfold augment in H3.  unfold eval_be' in |- *.
  replace
   (bool_fun_of_bool_expr (univl be l)
      (var_env'_to_env
         (fun n : nat =>
          match Neqb (N_of_nat n) a with
          | true => true
          | false => ve n
          end))) with
   (bool_fun_of_bool_expr (univl be l)
      (fun y : BDDvar =>
       match Neqb a y with
       | true => true
       | false => var_env'_to_env ve y
       end)).
  assumption.  apply (bool_fun_of_be_ext (univl be l)).  intros.
  unfold var_env'_to_env in |- *.  rewrite (N_of_nat_of_N x).
  rewrite (Neqb_comm a x).  reflexivity.  intros.
  elim (sumbool_of_bool (Neqb (N_of_nat n) a)).  intro y0.  rewrite y0 in H4.
  discriminate.  intro y0.  rewrite y0 in H4.  elim (H2 _ H4).  intro.
  rewrite <- H5 in y0.  rewrite (Neqb_correct a) in y0.  discriminate.
  trivial.  intros.  elim (sumbool_of_bool (Neqb (N_of_nat n) a)).  intro y0.
  apply no_dup_cons_no_in.  rewrite (Neqb_complete _ _ y0).  assumption.  
  intro y0.  rewrite y0 in H1.  unfold not in |- *; intro.  apply (H0 _ H1).  auto.  
  apply no_dup_cons_no_dup with (a := a).  assumption.  unfold eval_be' in |- *.
  apply (bool_fun_of_be_ext be).  intros.  unfold var_env'_to_env, var_env'_or in |- *.
  rewrite (N_of_nat_of_N x).  elim (sumbool_of_bool (Neqb x a)).  intro y0.
  rewrite y0.  simpl in |- *.  rewrite (Neqb_complete _ _ y0).  rewrite y.
  auto with bool.  intro y0.  rewrite y0.  reflexivity.  intro y.  elim (H be ve).
  intros.  clear H4.  apply H3.  unfold eval_be' in |- *.
  apply forall_lemma1 with (a := a).  assumption.  intros.  elim (H2 _ H4).  intro.
  rewrite H5 in y.  rewrite (nat_of_N_of_nat n) in y.  rewrite y in H4.
  discriminate.  auto.  intros.  unfold not in |- *; intro.  apply (H0 _ H3).  auto.
  apply no_dup_cons_no_dup with (a := a).  assumption.  intros.  unfold eval_be' in |- *.
  rewrite (forall_OK a (univl be l) (var_env'_to_env ve)).
  unfold bool_fun_forall in |- *.  unfold bool_fun_and in |- *.  apply andb_true_intro.  split.
  unfold bool_fun_restrict in |- *.
  elim
   (H be
      (fun n : nat =>
       match Neqb (N_of_nat n) a with
       | true => true
       | false => ve n
       end)).
  intros.  clear H2.
  replace
   (bool_fun_of_bool_expr (univl be l) (augment (var_env'_to_env ve) a true))
   with
   (eval_be' (univl be l)
      (fun n : nat =>
       match Neqb (N_of_nat n) a with
       | true => true
       | false => ve n
       end)).
  apply H3.  intros.
  replace
   (eval_be' be
      (var_env'_or
         (fun n : nat =>
          match Neqb (N_of_nat n) a with
          | true => true
          | false => ve n
          end) ve')) with
   (eval_be' be
      (var_env'_or ve
         (fun n : nat =>
          match Neqb (N_of_nat n) a with
          | true => true
          | false => ve' n
          end))).
  apply H1.  intros.  elim (sumbool_of_bool (Neqb (N_of_nat n) a)).  intro y.
  left.  rewrite (Neqb_complete _ _ y).  reflexivity.  intro y.
  rewrite y in H4.  right.  apply H2.  assumption.  unfold eval_be' in |- *.
  apply (bool_fun_of_be_ext be).  intros.  unfold var_env'_to_env, var_env'_or in |- *.
  rewrite (N_of_nat_of_N x).  elim (sumbool_of_bool (Neqb x a)).  intro y.
  rewrite y.  auto with bool.  intro y.  rewrite y.  reflexivity.
  unfold eval_be' in |- *.  unfold var_env'_to_env in |- *.
  apply (bool_fun_of_be_ext (univl be l)).  intro.  rewrite (N_of_nat_of_N x).
  unfold augment in |- *.  rewrite (Neqb_comm a x).  reflexivity.  intros.
  elim (sumbool_of_bool (Neqb (N_of_nat n) a)).  intro y.
  apply no_dup_cons_no_in.  rewrite (Neqb_complete _ _ y).  assumption.  
  intro y.  rewrite y in H2.  exact (fun x => H0 _ H2 (or_intror _ x)).  
  apply no_dup_cons_no_dup with (a := a).  assumption.  unfold bool_fun_restrict in |- *.
  elim (H be ve).  intros.  clear H2.
  replace
   (bool_fun_of_bool_expr (univl be l) (augment (var_env'_to_env ve) a false))
   with (eval_be' (univl be l) ve).
  apply H3.  intros.  apply H1.  intros.  auto.  unfold eval_be' in |- *.
  apply (bool_fun_of_be_ext (univl be l)).  intro.
  unfold var_env'_to_env, augment in |- *.  elim (sumbool_of_bool (Neqb a x)).  intro y.
  rewrite y.  rewrite <- (Neqb_complete _ _ y).  apply not_true_is_false.
  unfold not in |- *.  intro.  elim (H0 (nat_of_N a)).  assumption.  left.
  rewrite (N_of_nat_of_N a).  reflexivity.  intro y.  rewrite y.  reflexivity.
  intros.  exact (fun x => H0 _ H2 (or_intror _ x)).
  apply no_dup_cons_no_dup with (a := a).  assumption.
Qed.

Lemma bool_fun_of_be_ext1 :
 forall (be : bool_expr) (ve ve' : var_env'),
 (forall x : ad,
  be_x_free x be = true -> ve (nat_of_N x) = ve' (nat_of_N x)) ->
 eval_be' be ve = eval_be' be ve'.
Proof.
  simple induction be.  reflexivity.  reflexivity.  intros.  simpl in H.
  unfold eval_be' in |- *.  simpl in |- *.  unfold bool_fun_var in |- *.  unfold var_env'_to_env in |- *.
  rewrite (H b).  reflexivity.  apply Neqb_correct.  simpl in |- *.  intros.
  unfold eval_be' in |- *.  simpl in |- *.  unfold eval_be' in H.  unfold bool_fun_neg in |- *.
  rewrite (H ve ve' H0).  reflexivity.  unfold eval_be' in |- *.  simpl in |- *.
  unfold bool_fun_or in |- *.  intros.  rewrite (H ve ve').  rewrite (H0 ve ve').
  reflexivity.  intros.  apply H1.  rewrite H2.  auto with bool.  intros.
  apply H1.  rewrite H2.  auto with bool.  unfold eval_be' in |- *.  simpl in |- *.
  unfold bool_fun_and in |- *.  simpl in |- *.  intros.  rewrite (H ve ve').
  rewrite (H0 ve ve').  reflexivity.  intros.  apply H1.  rewrite H2.
  auto with bool.  intros.  apply H1.  rewrite H2.  auto with bool.  
  unfold eval_be' in |- *.  simpl in |- *.  unfold bool_fun_impl in |- *.  intros.  rewrite (H ve ve').
  rewrite (H0 ve ve').  reflexivity.  intros.  apply H1.  rewrite H2.
  auto with bool.  intros.  apply H1.  rewrite H2.  auto with bool.  
  unfold eval_be' in |- *.  simpl in |- *.  unfold bool_fun_iff in |- *.  intros.  rewrite (H ve ve').
  rewrite (H0 ve ve').  reflexivity.  intros.  apply H1.  rewrite H2.
  auto with bool.  intros.  apply H1.  rewrite H2.  auto with bool.
Qed.


Lemma no_dup_lx'_1 : forall n : nat, no_dup_list _ (lx'_1 N n).
Proof.
  simple induction n.  simpl in |- *.  apply no_dup_nil.  simpl in |- *.  intros.  apply no_dup_cons.
  unfold not in |- *; intro.  elim (in_lx'_1_conv _ _ _ H0).  intros.
  elim (lt_irrefl _ H2).  assumption.
Qed.

Lemma mu_all_eval_semantics1 :
 forall t be : bool_expr,
 be_ok (var_lu 0 N) be ->
 forall ve : var_env',
 (forall n : nat, ve n = true -> var_lu 0 N (N_of_nat n) = true) ->
 eval_be' (mu_all_eval N t be) ve = true ->
 forall ve' : var_env',
 (forall n : nat, ve' n = true -> var_lu 0 N (N_of_nat n) = true) ->
 eval_be' t (var_env'_or ve (var_env'_dash ve')) = true ->
 eval_be' be ve' = true.
Proof.
  intros.  unfold mu_all_eval in H1.  rewrite (replacel_lemma2 be H) in H1.
  rewrite (eval_dash_lemma1 be ve').
  elim (univl_semantics (lx' N) (Impl t (be_dash be)) ve).  intros.  clear H5.
  cut
   (eval_be' (Impl t (be_dash be)) (var_env'_or ve (var_env'_dash ve')) =
    true).
  intro.  cut (eval_be' (be_dash be) (var_env'_or ve (var_env'_dash ve')) = true).
  intro.  rewrite <- H6.  apply bool_fun_of_be_ext1.  intros.
  unfold var_env'_or in |- *.  replace (ve (nat_of_N x)) with false.  reflexivity.
  symmetry  in |- *.  apply not_true_is_false.  unfold not in |- *; intro.
  cut (var_lu 0 N x = true).  cut (var_lu N (2 * N) x = true).  intros.
  unfold var_lu in H9, H10.  elim (andb_prop _ _ H9).
  elim (andb_prop _ _ H10).  intros.  apply (lt_irrefl N).
  apply le_lt_trans with (m := nat_of_N x).  apply leb_complete; assumption.
  unfold lt in |- *.  apply leb_complete; assumption.  
  apply (be_ok_be_x_free (var_lu N (2 * N)) (be_dash be)).
  apply dash_be_ok.  assumption.  assumption.  rewrite <- (N_of_nat_of_N x).
  apply H0.  assumption.  unfold eval_be' in |- *.  unfold eval_be' in H5.  simpl in H5.
  unfold bool_fun_impl in H5.  unfold eval_be' in H3.  rewrite H3 in H5.
  simpl in H5.  assumption.  apply H4.  assumption.  intros.
  unfold var_env'_dash in H5.  elim (sumbool_of_bool (leb N n)).  intro y.
  rewrite y in H5.  apply in_lx'.  apply leb_complete; assumption.  
  cut (var_lu 0 N (N_of_nat (n - N)) = true).  unfold var_lu in |- *.  intro.
  elim (andb_prop _ _ H6).  intros.
  rewrite (nat_of_N_of_nat (n - N)) in H8.  simpl in |- *.
  rewrite <- (plus_n_O N).  replace n with (n - N + N).
  replace (S (n - N + N)) with (S (n - N) + N).
  apply plus_le_compat.  apply leb_complete; assumption.  apply le_n.
  reflexivity.  rewrite (plus_comm (n - N) N).  symmetry  in |- *.
  apply le_plus_minus.  apply leb_complete; assumption.  apply H2.
  assumption.  intro y.  rewrite y in H5.  discriminate.  intros.
  unfold not in |- *; intro.  unfold lx' in H5.  elim (in_lx'_1_conv N N n H5).  intro.
  intro.  unfold var_lu in H0.  elim (andb_prop _ _ (H0 n H4)).  intros.
  apply (lt_irrefl N).  apply le_lt_trans with (m := n).  assumption.  unfold lt in |- *.
  rewrite (nat_of_N_of_nat n) in H9.  apply leb_complete; assumption.
  unfold lx' in |- *.  apply no_dup_lx'_1.
Qed.

Lemma mu_ex_eval_semantics1 :
 forall t be : bool_expr,
 be_ok (var_lu 0 N) be ->
 forall ve : var_env',
 (forall n : nat, ve n = true -> var_lu 0 N (N_of_nat n) = true) ->
 eval_be' (mu_ex_eval N t be) ve = true ->
 exists ve' : var_env',
   (forall n : nat, ve' n = true -> var_lu 0 N (N_of_nat n) = true) /\
   eval_be' t (var_env'_or ve (var_env'_dash ve')) = true /\
   eval_be' be ve' = true.
Proof.
  intros.  unfold mu_ex_eval in H1.  rewrite (replacel_lemma2 be H) in H1.
  elim (exl_semantics (lx' N) (ANd t (be_dash be)) ve).  intros.  clear H3.
  elim (H2 H1).  intros ve' H3.  inversion H3.  clear H2 H3.
  split with (fun n : nat => ve' (N + n)).  split.  intros.  unfold var_lu in |- *.
  apply andb_true_intro.  rewrite (nat_of_N_of_nat n).  split.
  apply leb_correct.  apply le_O_n.  elim (in_lx'_1_conv _ _ _ (H4 _ H2)).
  intros.  apply leb_correct.  unfold lt in H6.
  rewrite (Splus_nm N n) in H6.  rewrite (plus_Snm_nSm N n) in H6.
  apply (fun p n m : nat => plus_le_reg_l n m p) with (p := N).  assumption.  unfold eval_be' in H5.
  simpl in H5.  unfold bool_fun_and in H5.  elim (andb_prop _ _ H5).  intros.
  split.  rewrite <- H2.  unfold eval_be' in |- *.  apply (bool_fun_of_be_ext t).
  unfold var_env'_to_env, var_env'_or, var_env'_dash in |- *.  intros.
  elim (sumbool_of_bool (leb N (nat_of_N x))).  intro y.  rewrite y.
  rewrite <- (le_plus_minus N (nat_of_N x)).  reflexivity.
  apply leb_complete; assumption.  intro y.  rewrite y.
  replace (ve' (nat_of_N x)) with false.  reflexivity.  symmetry  in |- *.
  apply not_true_is_false.  unfold not in |- *; intro.  unfold lx' in H4.
  elim (in_lx'_1_conv _ _ _ (H4 _ H6)).  intros.
  rewrite (leb_correct _ _ H7) in y; discriminate.
  rewrite (eval_dash_lemma1 be (fun n : nat => ve' (N + n))).  rewrite <- H3.
  fold (eval_be' (be_dash be) (var_env'_or ve ve')) in |- *.  apply bool_fun_of_be_ext1.
  intros.  unfold var_env'_or in |- *.  unfold var_env'_dash in |- *.
  cut (var_lu N (2 * N) x = true).  unfold var_lu in |- *.  intro.
  elim (andb_prop _ _ H7).  intros.  rewrite H8.
  replace (ve (nat_of_N x)) with false.  simpl in |- *.
  rewrite <- (le_plus_minus N (nat_of_N x)).  reflexivity.
  apply leb_complete.  assumption.  symmetry  in |- *.  apply not_true_is_false.
  unfold not in |- *; intro.  unfold var_lu in H0.  elim (andb_prop _ _ (H0 _ H10)).
  intros.  rewrite (N_of_nat_of_N x) in H12.  apply (lt_irrefl N).
  apply le_lt_trans with (m := nat_of_N x).  apply leb_complete; assumption.    unfold lt in |- *.  apply leb_complete; assumption.  
  apply be_ok_be_x_free with (be := be_dash be).  apply dash_be_ok.  assumption.  
  assumption.  intros.  unfold lx' in |- *.  unfold not in |- *; intro.
  elim (in_lx'_1_conv _ _ _ H3).  intros.  unfold var_lu in H0.
  elim (andb_prop _ _ (H0 _ H2)).  rewrite (nat_of_N_of_nat n).  intros.
  apply (lt_irrefl N).  apply le_lt_trans with (m := n).  assumption.  unfold lt in |- *.
  apply leb_complete.  assumption.  unfold lx' in |- *.  apply no_dup_lx'_1.
Qed.

Lemma mu_ex_eval_semantics2 :
 forall t be : bool_expr,
 be_ok (var_lu 0 N) be ->
 forall ve : var_env',
 (forall n : nat, ve n = true -> var_lu 0 N (N_of_nat n) = true) ->
 (exists ve' : var_env',
    (forall n : nat, ve' n = true -> var_lu 0 N (N_of_nat n) = true) /\
    eval_be' t (var_env'_or ve (var_env'_dash ve')) = true /\
    eval_be' be ve' = true) -> eval_be' (mu_ex_eval N t be) ve = true.
Proof.
  unfold mu_ex_eval in |- *.  intros.  rewrite (replacel_lemma2 be H).  elim H1.
  clear H1.  intros ve' H1.  inversion H1.  inversion H3.  clear H3 H1.
  elim (exl_semantics (lx' N) (ANd t (be_dash be)) ve).  intros.  clear H1.
  apply H3.  clear H3.  split with (var_env'_dash ve').  split.
  unfold var_env'_dash in |- *.  intros.  elim (sumbool_of_bool (leb N n)).  intros y.
  apply in_lx'.  apply leb_complete.  assumption.  rewrite y in H1.
  unfold var_lu in H2.  elim (andb_prop _ _ (H2 _ H1)).
  rewrite (nat_of_N_of_nat (n - N)).  intros.  simpl in |- *.
  rewrite <- (plus_n_O N).  replace n with (n - N + N).
  replace (S (n - N + N)) with (S (n - N) + N).
  apply plus_le_compat.  apply leb_complete; assumption.  apply le_n.  
  reflexivity.  rewrite (plus_comm (n - N) N).  symmetry  in |- *.
  apply le_plus_minus.  apply leb_complete; assumption.  intro y.
  rewrite y in H1.  discriminate.  unfold eval_be' in |- *.  simpl in |- *.
  unfold bool_fun_and in |- *.  apply andb_true_intro.  split.  exact H4.  
  fold (eval_be' (be_dash be) (var_env'_or ve (var_env'_dash ve'))) in |- *.
  rewrite (eval_dash_lemma1 be ve') in H5.  rewrite <- H5.
  apply (bool_fun_of_be_ext1 (be_dash be)).  intros.  unfold var_env'_or in |- *.
  replace (ve (nat_of_N x)) with false.  reflexivity.  symmetry  in |- *.
  apply not_true_is_false.  unfold not in |- *; intro.  unfold var_lu in H0.
  elim (andb_prop _ _ (H0 _ H3)).  rewrite (N_of_nat_of_N x).  intros.
  elim (andb_prop _ _ (be_ok_be_x_free _ _ (dash_be_ok _ H) _ H1)).  intros.
  apply (lt_irrefl N).  apply le_lt_trans with (m := nat_of_N x).
  apply leb_complete; assumption.  unfold lt in |- *.
  apply leb_complete; assumption.  unfold not in |- *; intros.  unfold lx' in H3.
  elim (in_lx'_1_conv _ _ _ H3).  intros.  unfold var_lu in H0.
  elim (andb_prop _ _ (H0 _ H1)).  rewrite (nat_of_N_of_nat n).  intros.
  apply (lt_irrefl N).  apply le_lt_trans with (m := n).  assumption.  unfold lt in |- *.
  apply leb_complete.  assumption.  unfold lx' in |- *.  apply no_dup_lx'_1.
Qed.

Lemma mu_all_eval_semantics2 :
 forall t be : bool_expr,
 be_ok (var_lu 0 N) be ->
 forall ve : var_env',
 (forall n : nat, ve n = true -> var_lu 0 N (N_of_nat n) = true) ->
 (forall ve' : var_env',
  (forall n : nat, ve' n = true -> var_lu 0 N (N_of_nat n) = true) ->
  eval_be' t (var_env'_or ve (var_env'_dash ve')) = true ->
  eval_be' be ve' = true) -> eval_be' (mu_all_eval N t be) ve = true.
Proof.
  unfold mu_all_eval in |- *.  intros.  rewrite (replacel_lemma2 be H).
  elim (univl_semantics (lx' N) (Impl t (be_dash be)) ve).  intros.  clear H2.
  apply H3.  intros.  clear H3.  unfold eval_be' in |- *.  simpl in |- *.  unfold bool_fun_impl in |- *.
  elim
   (sumbool_of_bool
      (bool_fun_of_bool_expr t (var_env'_to_env (var_env'_or ve ve')))).
  intro y.  rewrite y.  simpl in |- *.  unfold eval_be' in H1.
  rewrite <- (H1 (fun n : nat => ve' (N + n))).
  fold (eval_be' be (fun n : nat => ve' (N + n))) in |- *.
  rewrite (eval_dash_lemma1 be (fun n : nat => ve' (N + n))).
  fold (eval_be' (be_dash be) (var_env'_or ve ve')) in |- *.  apply bool_fun_of_be_ext1.
  intros.  intros.  unfold var_env'_or in |- *.  unfold var_env'_dash in |- *.
  cut (var_lu N (2 * N) x = true).  unfold var_lu in |- *.  intro.
  elim (andb_prop _ _ H4).  intros.  rewrite H5.
  replace (ve (nat_of_N x)) with false.  simpl in |- *.
  rewrite <- (le_plus_minus N (nat_of_N x)).  reflexivity.  
  apply leb_complete.  assumption.  symmetry  in |- *.  apply not_true_is_false.
  unfold not in |- *; intro.  unfold var_lu in H0.  elim (andb_prop _ _ (H0 _ H7)).
  intros.  rewrite (N_of_nat_of_N x) in H9.  apply (lt_irrefl N).
  apply le_lt_trans with (m := nat_of_N x).  apply leb_complete; assumption.  
  unfold lt in |- *.  apply leb_complete; assumption.  
  apply be_ok_be_x_free with (be := be_dash be).  apply dash_be_ok.  assumption.  
  assumption.  intros.  unfold var_lu in |- *.  apply andb_true_intro.  split.
  apply leb_correct.  apply le_O_n.  rewrite (nat_of_N_of_nat n).
  unfold lx' in H2.  elim (in_lx'_1_conv _ _ _ (H2 _ H3)).  intros.
  unfold lt in H5.  rewrite (plus_comm N n) in H5.  rewrite (Splus_nm n N) in H5.
  apply leb_correct.  apply (fun p n m : nat => plus_le_reg_l n m p) with (p := N).
  rewrite (plus_comm N (S n)).  assumption.  rewrite <- y.
  fold
   (eval_be' t (var_env'_or ve (var_env'_dash (fun n : nat => ve' (N + n)))))
   in |- *.
  fold (eval_be' t (var_env'_or ve ve')) in |- *.  apply bool_fun_of_be_ext1.  intros.
  unfold var_env'_or in |- *.
  replace (var_env'_dash (fun n : nat => ve' (N + n)) (nat_of_N x)) with
   (ve' (nat_of_N x)).
  reflexivity.  unfold var_env'_dash in |- *.
  elim (sumbool_of_bool (leb N (nat_of_N x))).  intro y0.  rewrite y0.
  rewrite <- (le_plus_minus N (nat_of_N x)).  reflexivity.
  apply leb_complete; assumption.  intro y0.  rewrite y0.
  apply not_true_is_false.  unfold not in |- *; intro.  unfold lx' in H2.
  elim (in_lx'_1_conv _ _ _ (H2 _ H4)).  intros.
  rewrite (leb_correct _ _ H5) in y0; discriminate.  intro y.  rewrite y.
  reflexivity.  intros.  unfold not in |- *; intro.  unfold lx' in H3.
  elim (in_lx'_1_conv N N n H3).  intro.  intro.  unfold var_lu in H0.
  elim (andb_prop _ _ (H0 n H2)).  intros.  apply (lt_irrefl N).
  apply le_lt_trans with (m := n).  assumption.  unfold lt in |- *.
  rewrite (nat_of_N_of_nat n) in H7.  apply leb_complete; assumption.
  unfold lx' in |- *.  apply no_dup_lx'_1.
Qed.

End New.