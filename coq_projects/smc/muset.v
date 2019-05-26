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
Require Import List.
Require Import Ensembles.
Require Import Finite_sets.
Require Import Finite_sets_facts.
Require Import Image.
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
Require Import munew.

Lemma relfreeeven :
 forall (f : mu_form) (P : ad) (b : bool),
 mu_rel_free P f = false -> f_P_even P f b.
Proof.
  simple induction f.  intros.  elim b; [ apply mu_0_even | apply mu_0_odd ].  intros.
  elim b; [ apply mu_1_even | apply mu_1_odd ].  intros.
  elim b; [ apply mu_ap_even | apply mu_ap_odd ].  intros.
  simpl in H.  elim b.  apply mu_rel_var_even.  apply mu_rel_var_odd.
  assumption.  intros.  simpl in H0.  elim b.  apply mu_neg_even.  apply H.
  assumption.  apply mu_neg_odd.  apply H.  assumption.  intros.  simpl in H1.
  elim (orb_false_elim _ _ H1); intros.  elim b.  apply mu_and_even.  apply H.
  assumption.  apply H0.  assumption.  apply mu_and_odd.  apply H.  assumption.
  apply H0.  assumption.  intros.  simpl in H1.
  elim (orb_false_elim _ _ H1); intros.  elim b.  apply mu_or_even.  apply H.
  assumption.  apply H0.  assumption.  apply mu_or_odd.  apply H.  assumption.
  apply H0.  assumption.  intros.  simpl in H1.
  elim (orb_false_elim _ _ H1); intros.  elim b.  apply mu_impl_even.  apply H.
  assumption.  apply H0.  assumption.  apply mu_impl_odd.  apply H.  assumption.
  apply H0.  assumption.  intros.  simpl in H1.
  elim (orb_false_elim _ _ H1); intros.  elim b.  apply mu_iff_even.  apply H.
  assumption.  apply H0.  assumption.  apply H.  assumption.  apply H0.
  assumption.  apply mu_iff_odd.  apply H.  assumption.  apply H0.  assumption.
  apply H.  assumption.  apply H0.  assumption.  intros.  simpl in H0.  elim b.
  apply mu_all_even.  apply H.  assumption.  apply mu_all_odd.  apply H.
  assumption.  intros.  simpl in H0.  elim b.  apply mu_ex_even.  apply H.
  assumption.  apply mu_ex_odd.  apply H.  assumption.  intros.  simpl in H0.
  elim (sumbool_of_bool (Neqb P a)).  intro y.
  rewrite <- (Neqb_complete _ _ y).  elim b.  apply mu_mu_P_even.
  apply mu_mu_P_odd.  intro y.  rewrite y in H0.  simpl in H0.  elim b.
  apply mu_mu_Q_even.  assumption.  apply H.  assumption.  apply mu_mu_Q_odd.
  assumption.  apply H.  assumption.
Qed.

Section mu2set.

Variable N : nat.

Definition set_1 := Evar_env'' 0 N.
Definition rel_1 (s t : var_env'') := In _ set_1 s /\ In _ set_1 t.

Definition t_to_rel1 (t : bool_expr) (ve1 ve2 : var_env') :=
  eval_be' t (var_env'_or ve1 (var_env'_dash N ve2)).
Definition t_to_rel (t : bool_expr) (ve1 ve2 : var_env'') :=
  t_to_rel1 t (var_env''_to_env' ve1) (var_env''_to_env' ve2).
Definition new_t_to_rel (t : bool_expr) (ve1 ve2 : var_env'') :=
  t_to_rel t ve1 ve2 = true /\ rel_1 ve1 ve2.

Definition state_set (S : Ensemble var_env'') := Included _ S set_1.
Definition state_rel (R : Relation var_env'') :=
  forall s t : var_env'', R s t -> rel_1 s t.  (* (In ? set_1 s) /\ (In ? set_1 t).*)

Definition set_0 := Empty_set var_env''.
Definition set_ap (x : ad) (s : var_env'') :=
  In _ set_1 s /\ in_dom _ x s = true.
Definition set_or := Union var_env''.
Definition set_and := Intersection var_env''.
Definition set_neg := Setminus _ set_1.
Definition set_impl (S1 S2 : Ensemble var_env'') := set_or (set_neg S1) S2.
Definition set_iff (S1 S2 : Ensemble var_env'') :=
  set_and (set_impl S1 S2) (set_impl S2 S1).
Inductive set_ex (R : Relation var_env'') (S : Ensemble var_env'') :
Ensemble var_env'' :=
    setex_intro :
      forall s t : var_env'',
      In _ set_1 s -> R s t -> In _ S t -> In _ (set_ex R S) s.
Definition set_all (R : Relation var_env'') (S : Ensemble var_env'')
  (s : var_env'') :=
  In _ set_1 s /\ (forall t : var_env'', R s t -> In _ S t).
Definition set_mu (f : Ensemble var_env'' -> Ensemble var_env'')
  (s : var_env'') :=
  forall X : Ensemble var_env'',
  state_set X -> Included _ (f X) X -> In _ X s.

Definition set_renv := ad -> Ensemble var_env''.
Definition set_tenv := ad -> Relation var_env''.
Definition sre_put (sre : set_renv) (P : ad) (S : Ensemble var_env'')
  (Q : ad) := if Neqb P Q then S else sre Q.
Definition te_ste_ok (te : trans_env) (ste : set_tenv) :=
  forall (a : ad) (ve1 ve2 : var_env''),
  new_t_to_rel (te a) ve1 ve2 <-> ste a ve1 ve2.
Definition re_sre_ok (re : rel_env) (sre : set_renv) :=
  forall P : ad, bool_expr_to_var_env'' 0 N (re P) = sre P.

Fixpoint mu_form2set (ste : set_tenv) (f : mu_form) {struct f} :
 set_renv -> Ensemble var_env'' :=
  fun sre =>
  match f with
  | mu_0 => set_0
  | mu_1 => set_1
  | mu_ap p => set_ap p
  | mu_rel_var P => sre P
  | mu_neg g => set_neg (mu_form2set ste g sre)
  | mu_and g1 g2 => set_and (mu_form2set ste g1 sre) (mu_form2set ste g2 sre)
  | mu_or g1 g2 => set_or (mu_form2set ste g1 sre) (mu_form2set ste g2 sre)
  | mu_impl g1 g2 =>
      set_impl (mu_form2set ste g1 sre) (mu_form2set ste g2 sre)
  | mu_iff g1 g2 => set_iff (mu_form2set ste g1 sre) (mu_form2set ste g2 sre)
  | mu_all t g => set_all (ste t) (mu_form2set ste g sre)
  | mu_ex t g => set_ex (ste t) (mu_form2set ste g sre)
  | mu_mu P g => set_mu (fun S => mu_form2set ste g (sre_put sre P S))
  end.

Lemma set_ap_state_set : forall x : ad, state_set (set_ap x).
Proof.
  unfold state_set, set_ap in |- *.  unfold Included in |- *.  unfold In in |- *.  tauto.
Qed.

Lemma var_env'_to_env''_to_env' :
 forall (L U : nat) (ve : var_env') (x : ad),
 var_lu L U x = true ->
 var_env''_to_env' (var_env'_to_env'' L U ve) (nat_of_N x) =
 ve (nat_of_N x).
Proof.
  intros.  unfold var_env''_to_env', var_env'_to_env'' in |- *.
  elim (var_env'_to_var_env''_lemma2 (U - L) L U ve (refl_equal (U - L))).
  intros x0 y.  rewrite (N_of_nat_of_N x).  apply (proj2 y).  assumption.
Qed.

Lemma le_minus_le1 : forall m n p : nat, m <= n -> m - p <= n - p.
Proof.
  simple induction 1.  auto with arith.  intros.  apply le_trans with (m := m0 - p).
  assumption.  generalize p.  generalize m0.  simple induction m1.  simpl in |- *.
  auto with arith.  intros.  elim p0.  auto with arith.  intros.
  replace (S n0 - S n1) with (n0 - n1).
  replace (S (S n0) - S n1) with (S n0 - n1).  apply H2.  
  reflexivity.  reflexivity.
Qed.

Fixpoint ve''_to_be (ve : var_env'') (n : nat) {struct n} : bool_expr :=
  match n with
  | O => One
  | S m =>
      match in_dom _ (N_of_nat m) ve with
      | true => ANd (ve''_to_be ve m) (Var (N_of_nat m))
      | false => ANd (ve''_to_be ve m) (Neg (Var (N_of_nat m)))
      end
  end.

Lemma ve''_to_be_ok :
 forall (n : nat) (ve ve' : var_env''),
 bool_fun_of_bool_expr (ve''_to_be ve n) (var_env''_to_env ve') = true ->
 forall m : nat,
 m < n -> MapGet _ ve (N_of_nat m) = MapGet _ ve' (N_of_nat m).
Proof.
  simple induction n.  intros.  elim (lt_n_O _ H0).  intros.  simpl in H0.
  elim (option_sum _ (MapGet unit ve (N_of_nat n0))).  intro y.  elim y.  intro x.
  elim x.  intros y0.  unfold in_dom in H0.  clear y.  rewrite y0 in H0.
  simpl in H0.  unfold bool_fun_and in H0.  elim (andb_prop _ _ H0).  clear H0.
  intros.  unfold bool_fun_var in H2.  unfold var_env''_to_env in H2.
  unfold lt in H1.  elim (le_lt_eq_dec m n0).  intros y.
  rewrite (H ve ve' H0 m y).  reflexivity.  intro y.  rewrite y.  rewrite y0.
  unfold in_dom in H2.  elim (option_sum _ (MapGet unit ve' (N_of_nat n0))).
  intro y1.  inversion y1.  rewrite H3.  elim x0.  reflexivity.  intro y1.
  rewrite y1 in H2.  discriminate.  apply le_S_n.  assumption.  intro y.
  unfold in_dom in H0.  rewrite y in H0.  simpl in H0.
  unfold bool_fun_and in H0.  elim (andb_prop _ _ H0).  intros.
  unfold bool_fun_neg, bool_fun_var, var_env''_to_env in H3.  unfold in_dom in H3.
  unfold lt in H1.  elim (le_lt_eq_dec m n0).  intro y0.  apply (H ve ve').
  assumption.  assumption.  intro y0.  rewrite y0.  rewrite y.
  elim (option_sum _ (MapGet unit ve' (N_of_nat n0))).  intro y1.  inversion y1.
  rewrite H4 in H3.  simpl in H3.  discriminate.  intro y1.  rewrite y1.
  reflexivity.  apply le_S_n.  assumption.
Qed.

Lemma ve''_to_be_ok1 :
 forall (n : nat) (ve ve' : var_env''),
 Evar_env'' 0 n ve ->
 bool_expr_to_var_env'' 0 n (ve''_to_be ve n) ve' -> ve = ve'.
Proof.
  intros.  unfold Evar_env'' in H.  unfold bool_expr_to_var_env'' in H0.
  elim H; clear H; intros H2 H3.  elim H0; clear H0; intros H4 H5.

  apply (mapcanon_unique unit).  assumption.  unfold Evar_env'' in H5.
  unfold In in H5.  exact (proj1 H5).  unfold Evar_env'' in H5.
  unfold In in H5.
  elim H5; intros H0 H1.
  unfold var_lu in H1, H3.  unfold eqmap in |- *.
  unfold eqm in |- *.  intro.  elim (le_lt_dec n (nat_of_N a)).
  unfold in_dom in H3, H1.  intro.  lapply (H3 a).  lapply (H1 a).
  elim (MapGet unit ve' a).  Focus 2. elim (MapGet unit ve a);  try reflexivity.  intros.
  discriminate.  intros.  discriminate.
  replace (leb (S (nat_of_N a)) n) with false.  simpl in |- *.  reflexivity.
  symmetry  in |- *.  apply not_true_is_false.  unfold not in |- *; intro.  elim (le_Sn_n n).
  apply le_trans with (m := S (nat_of_N a)).  apply le_n_S.  assumption.  
  apply leb_complete.  assumption.  
  replace (leb (S (nat_of_N a)) n) with false.  simpl in |- *.  reflexivity.  
  symmetry  in |- *.  apply not_true_is_false.  unfold not in |- *; intro.  elim (le_Sn_n n).
  apply le_trans with (m := S (nat_of_N a)).  apply le_n_S.  assumption.  
  apply leb_complete.  assumption.  intro.  rewrite <- (N_of_nat_of_N a).
  apply (ve''_to_be_ok n ve ve').  unfold eval_be' in H4.  rewrite <- H4.
  apply (bool_fun_of_be_ext (ve''_to_be ve n)).
  unfold var_env''_to_env, var_env'_to_env, var_env''_to_env' in |- *.  intros.
  rewrite (N_of_nat_of_N x).  reflexivity.  assumption.  
Qed.

Lemma ve''_to_be_ok2 :
 forall (n : nat) (ve : var_env''),
 eval_be' (ve''_to_be ve n) (var_env''_to_env' ve) = true.
Proof.
  simple induction n.  simpl in |- *.  unfold eval_be' in |- *.  simpl in |- *.  unfold bool_fun_one in |- *.
  reflexivity.  simpl in |- *.  intros.  unfold in_dom in |- *.
  elim (option_sum _ (MapGet unit ve (N_of_nat n0))).  intro y.  elim y; clear y.
  intro x.  elim x.  clear x.  intros y.  rewrite y.  unfold eval_be' in |- *.  simpl in |- *.
  unfold eval_be' in H.  unfold bool_fun_and in |- *.  apply andb_true_intro.  split.
  apply H.  unfold bool_fun_var, var_env'_to_env, var_env''_to_env' in |- *.
  rewrite (nat_of_N_of_nat n0).  unfold in_dom in |- *.  rewrite y.  reflexivity.  
  intro y.  rewrite y.  unfold eval_be' in |- *.  simpl in |- *.  unfold eval_be' in H.
  unfold bool_fun_and in |- *.  apply andb_true_intro.  split.  apply H.  
  unfold bool_fun_var, var_env'_to_env, var_env''_to_env', bool_fun_neg
   in |- *.
  rewrite (nat_of_N_of_nat n0).  unfold in_dom in |- *.  rewrite y.  reflexivity.
Qed.

Lemma ve''_to_be_ok3 :
 forall (n : nat) (ve : var_env''),
 n <= N -> be_ok (var_lu 0 N) (ve''_to_be ve n).
Proof.
  simple induction n.  intros.  simpl in |- *.  apply one_ok.  simpl in |- *.  intros.
  elim (in_dom unit (N_of_nat n0) ve).  apply and_ok.  apply H.
  apply lt_le_weak.  assumption.  apply var_ok.  unfold var_lu in |- *.
  apply andb_true_intro.  split.  auto with arith.  
  rewrite (nat_of_N_of_nat n0).  apply leb_correct.  assumption.  
  apply and_ok.  apply H.  apply lt_le_weak.  assumption.  apply neg_ok.
  apply var_ok.  unfold var_lu in |- *.  apply andb_true_intro.  split.
  auto with arith.  rewrite (nat_of_N_of_nat n0).  apply leb_correct.
  assumption. 
Qed.

Lemma env_to_be_lemma :
 forall S : Ensemble var_env'',
 Finite _ S ->
 Included _ S (Evar_env'' 0 N) ->
 exists be : bool_expr,
   bool_expr_to_var_env'' 0 N be = S /\ be_ok (var_lu 0 N) be.
Proof.
  intro.  simple induction 1.
  unfold Included, bool_expr_to_var_env'', Evar_env'' in |- *.  unfold In in |- *.  intros.
  split with Zero. split.
  apply Extensionality_Ensembles.  split.  unfold Included in |- *.
  intros.  unfold In in H1.  unfold eval_be' in H1.  simpl in H1.
  unfold bool_fun_zero in H1.  decompose [and] H1.  discriminate.  
  unfold Included in |- *.  unfold In in |- *.  intros.  elim H1.  apply zero_ok.
  intros.  elim H1.  clear H1.
  intros.  split with (Or x0 (ve''_to_be x N)).  unfold bool_expr_to_var_env'' in |- *.
  split.  elim H1.  clear H1.  intros y H00.
  apply Extensionality_Ensembles.  split.  unfold Included in |- *.  unfold In in |- *.
  unfold Evar_env'', eval_be' in |- *.  unfold bool_expr_to_var_env'' in y.
  unfold eval_be', In, Evar_env'' in y.  intros.  simpl in H1.
  elim H1; clear H1; intros H5 H4; elim H4; clear H4; intros H4 H7.
  unfold bool_fun_or in H5.
  elim (orb_prop _ _ H5).  clear H5.  intro.  unfold Add in |- *.
  apply (Union_introl _ A (Singleton var_env'' x) x1).  rewrite <- y.
  unfold In in |- *.  split.  assumption.  split.  assumption.  assumption.  intro.
  clear H5.  unfold Add in |- *.  apply (Union_intror _ A (Singleton var_env'' x) x1).
  replace x with x1.  apply In_singleton.  symmetry  in |- *.
  apply (ve''_to_be_ok1 N x x1).  unfold Included in H3.  unfold In at 2 in H3.
  apply H3.  unfold Add in |- *.  apply Union_intror.  apply In_singleton.  
  unfold bool_expr_to_var_env'' in |- *.  unfold eval_be' in |- *.  split.  assumption.  split.
  assumption.  assumption.  unfold Included in |- *.  intros.  unfold Add in H1.
  elim H1.  intros.  split.  unfold eval_be' in |- *.  simpl in |- *.  unfold bool_fun_or in |- *.
  apply orb_true_intro.  left.  unfold bool_expr_to_var_env'' in y.
  rewrite <- y in H4.  unfold In in H4.  unfold eval_be' in H4.
  exact (proj1 H4).  rewrite <- y in H4.
  unfold bool_expr_to_var_env'' in H4.  unfold In in H4.  unfold In in |- *.
  exact (proj2 H4).  intros.  elim H4.  unfold In in |- *.  split.  unfold eval_be' in |- *.
  simpl in |- *.  unfold bool_fun_or in |- *.  apply orb_true_intro.  right.
  apply (ve''_to_be_ok2 N x).  unfold Included in H3.  unfold In in H3.
  apply H3.  unfold Add in |- *.  apply (Union_intror _ A (Singleton var_env'' x) x).
  apply In_singleton.  apply or_ok.  exact (proj2 H1).  apply ve''_to_be_ok3.
  apply le_n.  unfold Included in |- *.  intros.  apply H3.  unfold Add in |- *.
  apply Union_introl.  assumption.
Qed.

Lemma env_to_be_lemma1 :
 forall S : Ensemble var_env'',
 Included _ S (Evar_env'' 0 N) ->
 exists be : bool_expr,
   bool_expr_to_var_env'' 0 N be = S /\ be_ok (var_lu 0 N) be.
Proof.
  intros.  apply env_to_be_lemma. 
  apply Finite_downward_closed with (A := Evar_env'' 0 N).
  apply Eenv''_var''finite.  assumption.  assumption.
Qed.

Lemma muevaleqset :
 forall (te : trans_env) (ste : set_tenv),
 ad_to_be_ok (var_lu 0 (2 * N)) te ->
 te_ste_ok te ste ->
 forall (f : mu_form) (re : rel_env) (sre : set_renv),
 f_ok f ->
 mu_form_ap_ok (var_lu 0 N) f ->
 ad_to_be_ok (var_lu 0 N) re ->
 re_sre_ok re sre ->
 mu_form2set ste f sre = bool_expr_to_var_env'' 0 N (mu_eval N te f re).
Proof.
  intro.  intro.  intro te_ok.  intro.  simple induction f.  simpl in |- *.
  unfold set_0, bool_expr_to_var_env'' in |- *.  intros.  apply Extensionality_Ensembles.
  split.  auto with sets.  unfold Included in |- *.  unfold eval_be' in |- *.  simpl in |- *.
  unfold In, bool_fun_zero in |- *.  intros.  decompose [and] H4.  discriminate.  simpl in |- *.
  intros.  apply Extensionality_Ensembles.  unfold set_1 in |- *.  simpl in |- *.  split.
  unfold Included in |- *.  unfold Evar_env'', bool_expr_to_var_env'' in |- *.  unfold In in |- *.
  unfold eval_be' in |- *.  simpl in |- *.  unfold Evar_env'' in |- *.  tauto.  
  unfold bool_expr_to_var_env'', Evar_env'' in |- *.  unfold Included in |- *.  unfold eval_be' in |- *.
  simpl in |- *.  unfold In in |- *.  tauto.  simpl in |- *.  unfold set_ap in |- *.
  unfold bool_expr_to_var_env'' in |- *.  unfold eval_be' in |- *.  simpl in |- *.  unfold bool_fun_var in |- *.
  unfold In in |- *.  unfold Evar_env'' in |- *.  unfold set_1 in |- *.  unfold Evar_env'' in |- *.  intros.
  apply Extensionality_Ensembles.  split.  unfold Included in |- *.  unfold In in |- *.  intros.
  elim H4; intros H5 H7; elim H5; clear H5; intros H5 H8.

  split.  unfold var_env'_to_env, var_env''_to_env' in |- *.
  rewrite (N_of_nat_of_N a).  assumption.  split.  assumption.  assumption.
  unfold var_env'_to_env, var_env''_to_env' in |- *.  rewrite (N_of_nat_of_N a).
  unfold Included in |- *.  unfold In in |- *.  tauto.
  simpl in |- *.  unfold re_sre_ok in |- *.  intros.  symmetry  in |- *.  apply H3.  
  intros.  simpl in |- *.  inversion H2.  rewrite (H0 re sre).
  unfold set_neg, bool_expr_to_var_env'' in |- *.  unfold Setminus in |- *.  unfold eval_be' in |- *.
  simpl in |- *.  apply Extensionality_Ensembles.  unfold Same_set in |- *.  unfold Included in |- *.
  unfold In in |- *.  unfold var_env'_to_env, var_env''_to_env' in |- *.  unfold set_1 in |- *.
  unfold Evar_env'' in |- *.  split.  intros.
  elim H7; intros H8 H10; elim H8; clear H8; intros H8 H11.

  unfold bool_fun_neg in |- *.
  split.  elim
   (sumbool_of_bool
      (bool_fun_of_bool_expr (mu_eval N te m re)
         (fun x0 : BDDvar => in_dom unit (N_of_nat (nat_of_N x0)) x))).
  intro y.  rewrite y in H10.  elim H10.  tauto.  intro y.  rewrite y.  reflexivity.
  split.  assumption.  assumption.  unfold bool_fun_neg in |- *.  intros.
  elim H7; intros H9 H8; elim H8; clear H8; intros H8 H11.
  split.  split.  assumption.  assumption.  
  unfold not in |- *; intro.
  elim H10; intros H13 H12; elim H12; clear H12; intros H12 H15.

  rewrite H13 in H9.  discriminate.
  inversion H1.  assumption.  assumption.  assumption.  assumption.  
  simpl in |- *.  intros.  inversion H3.  rewrite (H0 re sre).  rewrite (H1 re sre).
  unfold set_and, bool_expr_to_var_env'' in |- *.  unfold eval_be' in |- *.
  unfold var_env'_to_env, var_env''_to_env' in |- *.  apply Extensionality_Ensembles.
  unfold Same_set in |- *.  unfold Included in |- *.  split.  intros.  inversion H10.
  simpl in |- *.  unfold bool_fun_and in |- *.  unfold In in H11, H12.  unfold In in |- *.
  rewrite (proj1 H11).  rewrite (proj1 H12).  split.  reflexivity.  
  exact (proj2 H12).  intros.  simpl in H10.  unfold bool_fun_and in H10.
  unfold In in H10.
  elim H10; clear H10; intros H12 H13.

  elim (andb_prop _ _ H12).
  intros.  apply Intersection_intro.  unfold In in |- *.  rewrite H10.
  split; [ reflexivity | assumption ].  unfold In in |- *.  rewrite H11.
  split; [ reflexivity | assumption ].  inversion H2.  assumption.  assumption.
  assumption.  assumption.  inversion H2.  assumption.  assumption.  assumption.
  assumption.
  simpl in |- *.  intros.  rewrite (H0 re sre).  rewrite (H1 re sre).
  unfold set_or, bool_expr_to_var_env'' in |- *.  unfold eval_be' in |- *.
  unfold var_env'_to_env, var_env''_to_env' in |- *.  apply Extensionality_Ensembles.
  unfold Same_set in |- *.  unfold Included in |- *.  split.  intros.  inversion H6.  unfold In in |- *.
  simpl in |- *.  unfold bool_fun_or in |- *.  unfold In in H7.
  elim H7; intros H10 H11.

  rewrite H10.  auto with bool.  unfold In in |- *.  unfold In in H7.  simpl in |- *.
  unfold bool_fun_or in |- *.
  elim H7; intros H10 H11.
  rewrite H10.  auto with bool.  
  intros.  simpl in H6.  unfold In in H6.  unfold bool_fun_or in H6.
  elim H6; clear H6; intros H8 H9.

  elim (orb_true_elim _ _ H8).  intros y.
  apply Union_introl.  unfold In in |- *.  rewrite y.  auto with bool.  intro y.
  apply Union_intror.  unfold In in |- *.  rewrite y.  auto with bool.  inversion H2.
  assumption.  inversion H3.  assumption.  assumption.  assumption.  
  inversion H2.  assumption.  inversion H3.  assumption.  assumption.  
  assumption.
  simpl in |- *.  intros.  rewrite (H0 re sre).  rewrite (H1 re sre).
  unfold set_impl, bool_expr_to_var_env'' in |- *.  unfold eval_be' in |- *.
  unfold var_env'_to_env, var_env''_to_env' in |- *.  apply Extensionality_Ensembles.
  unfold Same_set in |- *.  unfold Included in |- *.  split.  intros.  unfold In in |- *.  simpl in |- *.
  unfold bool_fun_impl in |- *.  inversion H6.  unfold set_neg in H7.
  unfold Setminus in H7.  unfold In in H7.
  elim H7; intros H10 H11.
  unfold implb in |- *.
  unfold ifb in |- *.  elim
   (sumbool_of_bool
      (bool_fun_of_bool_expr (mu_eval N te m re)
         (fun x1 : BDDvar => in_dom unit (N_of_nat (nat_of_N x1)) x))).
  intro y.  rewrite y in H11.  unfold set_1 in H10.  elim H11.  auto with bool.  
  intro y.  rewrite y.  auto with bool.  unfold In in H7.
  elim H7; intros H10 H11.

  rewrite H10.  unfold implb in |- *.  unfold ifb in |- *.
  elim
   (bool_fun_of_bool_expr (mu_eval N te m re)
      (fun x1 : BDDvar => in_dom unit (N_of_nat (nat_of_N x1)) x));
   auto with bool.  unfold set_or, set_neg in |- *.  unfold Setminus in |- *.  simpl in |- *.
  unfold bool_fun_impl in |- *.  unfold set_1 in |- *.  intros.  unfold In in H6.
  elim H6; clear H6; intros H8 H9.

  unfold implb in H8.  unfold ifb in H8.
  elim
   (sumbool_of_bool
      (bool_fun_of_bool_expr (mu_eval N te m re)
         (fun x0 : BDDvar => in_dom unit (N_of_nat (nat_of_N x0)) x))).
  intro y.  rewrite y in H8.  apply Union_intror.  unfold In in |- *.  rewrite H8.
  auto with bool.  intro y.  apply Union_introl.  unfold In in |- *.  split.  assumption.
  unfold not in |- *; intro.
  elim H6; intros H10 H11.

  rewrite y in H10.  discriminate.  
  inversion H2.  assumption.  inversion H3.  assumption.  assumption.  
  assumption.  inversion H2.  assumption.  inversion H3.  assumption.  
  assumption.  assumption.  
  simpl in |- *.  intros.  rewrite (H0 re sre).  rewrite (H1 re sre).
  unfold set_iff, bool_expr_to_var_env'' in |- *.  unfold eval_be' in |- *.
  unfold var_env'_to_env, var_env''_to_env' in |- *.  unfold set_and, set_impl in |- *.
  apply Extensionality_Ensembles.  split.  unfold Included in |- *.  intros.  unfold In in |- *.
  simpl in |- *.  unfold bool_fun_iff in |- *.  inversion H6.  clear H6.
  unfold set_or, set_neg in H7.  unfold Setminus in H7.
  unfold set_or, set_neg in H8.  unfold Setminus in H8.  unfold set_1 in H7.
  unfold set_1 in H8.  inversion H7.  unfold In in H6.  clear H7.
  elim H6; clear H6; intros H11 H12.

  split.  inversion H8.  clear H8.
  unfold In in H6.
  elim H6; clear H6; intros H13 H14.

  replace
   (bool_fun_of_bool_expr (mu_eval N te m re)
      (fun x0 : BDDvar => in_dom unit (N_of_nat (nat_of_N x0)) x)) with
   false.
  replace
   (bool_fun_of_bool_expr (mu_eval N te m0 re)
      (fun x0 : BDDvar => in_dom unit (N_of_nat (nat_of_N x0)) x)) with
   false.
  reflexivity.  symmetry  in |- *.  apply not_true_is_false.
  exact (fun x => H14 (conj x H13)).  symmetry  in |- *.  apply not_true_is_false.
  exact (fun x => H12 (conj x H13)).  unfold In in H6.
  elim H6; intros H14 H15.
  rewrite H14 in H12.  elim H12; auto with bool.  assumption.  unfold In in H6.
  elim H6; clear H6; intros H12 H13.
  inversion H8.  clear H8.  unfold In in H6.
  elim H6; clear H6; intros H14 H15.
  rewrite H12 in H15.  elim H15; auto with bool.
  unfold In in H6.
  elim H6; intros H15 H16.

  rewrite H12.  rewrite H15.  split.
  reflexivity.  assumption.  unfold Included in |- *.  intros.  unfold In in H6.
  simpl in H6.  unfold bool_fun_iff in H6.
  elim H6; intros H8 H9.
  elim
   (sumbool_of_bool
      (bool_fun_of_bool_expr (mu_eval N te m re)
         (fun x0 : BDDvar => in_dom unit (N_of_nat (nat_of_N x0)) x))).
  intro y.  apply Intersection_intro.  unfold set_or, set_neg in |- *.  unfold Setminus in |- *.
  apply Union_intror.  unfold In in |- *.  rewrite (eqb_prop _ _ H8) in y.  rewrite y.
  auto with bool.  unfold set_or, set_neg in |- *.  apply Union_intror.  unfold In in |- *.
  rewrite y.  auto with bool.  intro y.  apply Intersection_intro.
  unfold set_or, set_neg in |- *.  apply Union_introl.  unfold Setminus, In in |- *.  rewrite y.
  unfold set_1 in |- *.  split.  assumption.  unfold not in |- *; intros.  decompose [and] H7.
  discriminate.  unfold set_or, set_neg in |- *.  apply Union_introl.
  unfold Setminus, In in |- *.  unfold set_1 in |- *.  split.  assumption.  
  rewrite <- (eqb_prop _ _ H8).  rewrite y.  unfold not in |- *; intro.
  decompose [and] H7.  discriminate.  inversion H2.  assumption.  inversion H3.
  assumption.  assumption.  assumption.  inversion H2.  assumption.  
  inversion H3.  assumption.  assumption.  assumption.  
  intros.  simpl in |- *.  unfold set_all in |- *.  inversion H1.  inversion H2.
  rewrite (H0 re sre).  apply Extensionality_Ensembles.  split.
  unfold Included in |- *.  intros.  unfold In in |- *.  unfold bool_expr_to_var_env'' in |- *.
  unfold te_ste_ok in H.  unfold In in H11.
  elim H11; clear H11; intros H13 H14.
  unfold set_1 in H13.  split.  apply mu_all_eval_semantics2.
  elim (mu_eval_lemma1 N te te_ok m H6).  intros.  apply H11.  assumption.  
  assumption.  unfold Evar_env'' in H13.  unfold var_env''_to_env' in |- *.  intros.
  apply not_false_is_true.  unfold not in |- *; intro.
  rewrite (proj2 H13 _ H12) in H11.  discriminate.  
  unfold new_t_to_rel in H.  unfold t_to_rel in H.  unfold t_to_rel1 in H.
  intros.  unfold bool_expr_to_var_env'' in H14.
  replace (eval_be' (mu_eval N te m re) ve') with
   (eval_be' (mu_eval N te m re)
      (var_env''_to_env' (var_env'_to_env'' 0 N ve'))).
  elim (H14 (var_env'_to_env'' 0 N ve')).  intros.  apply H15.  clear H14.
  apply (proj1 (H a x (var_env'_to_env'' 0 N ve'))).  rewrite <- H12.  
  split.  apply bool_fun_of_be_ext1.  intros.  unfold ad_to_be_ok in te_ok.
  cut (var_lu 0 (2 * N) x0 = true).  intro.  unfold var_lu in H15.
  elim (andb_prop _ _ H15).  intros.  unfold var_env'_or in |- *.
  unfold var_env'_to_env'' in |- *.  unfold var_env''_to_env' at 2 in |- *.
  elim (var_env'_to_var_env''_lemma2 (N - 0) 0 N ve' (refl_equal (N - 0))).
  intros x1 y.
  elim y; intros H19 H20.

  elim (var_env''_to_env' x (nat_of_N x0)).
  reflexivity.  simpl in |- *.  unfold var_env'_dash in |- *.
  elim (sumbool_of_bool (leb N (nat_of_N x0))).  intro y0.  rewrite y0.
  rewrite (H20 (N_of_nat (nat_of_N x0 - N))).
  rewrite (nat_of_N_of_nat (nat_of_N x0 - N)).  reflexivity.  
  unfold var_lu in |- *.  apply andb_true_intro.  split.  auto with arith.  
  rewrite (nat_of_N_of_nat (nat_of_N x0 - N)).  apply leb_correct.
  rewrite (minus_Sn_m (nat_of_N x0) N).  cut (N = 2 * N - N).  intro.
  replace (S (nat_of_N x0) - N <= N) with
   (S (nat_of_N x0) - N <= 2 * N - N).
  apply le_minus_le1.  apply leb_complete.  assumption.  unfold mult at 1 in |- *.
  replace (N + (N + 0) - N) with N.  reflexivity.  simpl in |- *.
  replace (N + 0) with N.  apply plus_minus.  reflexivity.  
  auto with arith.  apply leb_complete; assumption.  intro y0.  rewrite y0.
  reflexivity.  apply be_ok_be_x_free with (be := te t).  apply te_ok.  
  rewrite H5.  assumption.  
  unfold rel_1 in |- *.  unfold set_1 in |- *.  split.  assumption.  unfold In in |- *.
  unfold Evar_env'' in |- *.  unfold var_env'_to_env'' in |- *.
  elim (var_env'_to_var_env''_lemma2 (N - 0) 0 N ve' (refl_equal (N - 0))).
  unfold Evar_env'' in |- *.  unfold In in |- *.  intros x0 y.
  elim y; intros H14 H16; elim H14; clear H14; intros H14 H17.

  split.
  assumption.  assumption.  apply bool_fun_of_be_ext1.  intros.
  elim (mu_eval_lemma1 N te te_ok m H6 H9).  intros.  clear H17.
  rewrite (var_env'_to_env''_to_env' 0 N ve' x0).  reflexivity.  
  apply be_ok_be_x_free with (be := mu_eval N te m re).  apply H16.  assumption.
  assumption.  assumption.  unfold Included in |- *.  unfold In in |- *.  intros.
  unfold bool_expr_to_var_env'' in H11.
  elim H11; clear H11; intros H13 H14. 

  split.  unfold set_1 in |- *.  assumption.  intros.  unfold te_ste_ok in H.
  unfold bool_expr_to_var_env'' in |- *.  split.
  apply
   mu_all_eval_semantics1
    with (N := N) (t := te t) (ve := var_env''_to_env' x).
  elim (mu_eval_lemma1 N te te_ok m H6).  intros.  apply H12.  assumption.  
  assumption.  intros.  unfold Evar_env'', In in H14.
  unfold var_env''_to_env' in H12.
  elim H14; intros H16 H17.  
  unfold var_lu in |- *.
  rewrite (nat_of_N_of_nat n).  apply andb_true_intro.  split.
  auto with arith.  unfold var_lu in H17.
  cut (leb 0 n && leb (S n) N = true).  intros.
  elim (andb_prop _ _ H15).  intros.  assumption.  apply not_false_is_true.
  unfold not in |- *.  replace n with (nat_of_N (N_of_nat n)).  intro.
  rewrite (H17 _ H15) in H12.  discriminate.  apply nat_of_N_of_nat.  
  rewrite H5.  assumption.  unfold new_t_to_rel in H.
  elim (proj2 (H a x t1) H11).  intros.  unfold rel_1 in H15.
  unfold set_1 in H15.  unfold Evar_env'' in H15.  unfold In in H15.
  unfold var_env''_to_env' in H16.
  elim H15; intros H17 H18; elim H17; clear H17; intros H17 H20; elim H18;
   clear H18; intros H18 H21.

  apply not_false_is_true.  unfold not in |- *; intro.  rewrite (H21 _ H19) in H16.
  discriminate.  unfold new_t_to_rel in H.  unfold t_to_rel in H.
  unfold t_to_rel1 in H.  elim (H t x t1).  intros.  rewrite <- H5 in H11.
  elim (H15 H11).  intros.  assumption.  elim (H t x t1).  intros.
  rewrite <- H5 in H11.  elim (H15 H11).  intros.  unfold rel_1, set_1 in H17.
  exact (proj2 H17).  assumption.  assumption.  assumption.  assumption.  
  intros.  simpl in |- *.  (* Unfold set_ex. *)  inversion H1.  inversion H2.
  rewrite (H0 re sre).  apply Extensionality_Ensembles.  split.
  unfold Included in |- *.  intros.  unfold In in |- *.  unfold bool_expr_to_var_env'' in |- *.
  unfold te_ste_ok in H.  unfold In in H11.  (* Unfold set_ex in H11. *)  elim H11.
  intros.  elim (proj2 (H a s t1) H13).  intros.  unfold rel_1, set_1 in H16.
  split.  apply mu_ex_eval_semantics2.
  elim (mu_eval_lemma1 N te te_ok m H6 H9).  intros.  apply H17.  assumption.  
  unfold set_1, In in H12.  unfold Evar_env'' in H12.  intros.
  unfold var_env''_to_env' in H17.  apply not_false_is_true.  unfold not in |- *; intro.
  rewrite (proj2 H12 _ H18) in H17.  discriminate.  
  split with (var_env''_to_env' t1).  unfold In, Evar_env'' in H16.
  elim H16; intros H17 H18; elim H17; clear H17; intros H17 H20; elim H18;
   clear H18; intros H18 H21.

  split.  intros.  apply not_false_is_true.
  unfold not in |- *; intro.  unfold var_env''_to_env' in H19.
  rewrite (H21 _ H22) in H19.  discriminate.  split.  unfold t_to_rel in H15.
  unfold t_to_rel1 in H15.  assumption.  unfold eval_be' in |- *.  unfold In in H14.
  unfold bool_expr_to_var_env'' in H14.  unfold eval_be' in H14.
  exact (proj1 H14).  exact (proj1 H16).  unfold Included in |- *.  unfold In in |- *.
  unfold bool_expr_to_var_env'' in |- *.  intros.
  elim H11; clear H11; intros H13 H14.

  elim
   mu_ex_eval_semantics1
    with
      (N := N)
      (t := te a)
      (be := mu_eval N te m re)
      (ve := var_env''_to_env' x).
  intros.
  elim H11; clear H11; intros H15 H12; elim H12; clear H12; intros H12 H17.

  cut
   (forall s t0 : var_env'',
    In var_env'' set_1 s ->
    ste a s t0 ->
    In var_env''
      (fun ve : var_env'' =>
       eval_be' (mu_eval N te m re) (var_env''_to_env' ve) = true /\
       In var_env'' (Evar_env'' 0 N) ve) t0 ->
    In var_env''
      (set_ex (ste a)
         (fun ve : var_env'' =>
          eval_be' (mu_eval N te m re) (var_env''_to_env' ve) = true /\
          In var_env'' (Evar_env'' 0 N) ve)) s).
  unfold In in |- *.  intros.  apply H11 with (s := x) (t0 := var_env'_to_env'' 0 N x0).
  unfold set_1 in |- *.  assumption.  unfold te_ste_ok in H.
  apply (proj1 (H a x (var_env'_to_env'' 0 N x0))).  unfold new_t_to_rel in |- *.
  unfold t_to_rel in |- *.  unfold t_to_rel1 in |- *.  split.  rewrite <- H12.
  apply bool_fun_of_be_ext1.  intros.
  unfold var_env'_or, var_env''_to_env', var_env'_dash in |- *.
  rewrite (N_of_nat_of_N x1).  elim (sumbool_of_bool (in_dom unit x1 x)).
  intro y.  rewrite y.  simpl in |- *.  reflexivity.  intro y.  rewrite y.  simpl in |- *.
  elim (sumbool_of_bool (leb N (nat_of_N x1))).  intro y0.  rewrite y0.
  unfold var_env'_to_env'' in |- *.
  elim (var_env'_to_var_env''_lemma2 (N - 0) 0 N x0 (refl_equal (N - 0))).
  intros x2 y1.
  elim y1; intros H19 H20.

  rewrite (H20 (N_of_nat (nat_of_N x1 - N))).
  rewrite (nat_of_N_of_nat (nat_of_N x1 - N)).
  reflexivity.  unfold var_lu in |- *.  apply andb_true_intro.  split.
  apply leb_correct.  apply le_O_n.  
  rewrite (nat_of_N_of_nat (nat_of_N x1 - N)).
  cut (var_lu 0 (2 * N) x1 = true).  intro.  unfold var_lu in H18.
  elim (andb_prop _ _ H18).  intros.  clear H21.  apply leb_correct.
  rewrite (minus_Sn_m (nat_of_N x1) N).
  replace (S (nat_of_N x1) - N <= N) with
   (S (nat_of_N x1) - N <= 2 * N - N).
  apply le_minus_le1.  apply leb_complete.  assumption.  unfold mult at 1 in |- *.
  replace (N + (N + 0) - N) with N.  reflexivity.  simpl in |- *.
  replace (N + 0) with N.  apply plus_minus.  reflexivity.  
  auto with arith.  apply leb_complete; assumption.  
  apply be_ok_be_x_free with (be := te a).  apply te_ok.  assumption.  intro y0.
  rewrite y0.  reflexivity.  unfold rel_1 in |- *.  unfold set_1 in |- *.  split.  assumption.
  unfold var_env'_to_env'' in |- *.
  elim (var_env'_to_var_env''_lemma2 (N - 0) 0 N x0 (refl_equal (N - 0))).
  intros x1 y.  exact (proj1 y).  split.  rewrite <- H17.
  apply bool_fun_of_be_ext1.  intros.  apply var_env'_to_env''_to_env'.
  apply be_ok_be_x_free with (be := mu_eval N te m re).
  elim (mu_eval_lemma1 N te te_ok m H6 H9).  intros.  apply H18.  assumption.  
  assumption.  unfold Evar_env'', var_env'_to_env'' in |- *.
  elim (var_env'_to_var_env''_lemma2 (N - 0) 0 N x0 (refl_equal (N - 0))).
  intros x1 y.  unfold Evar_env'' in y.  unfold In in y.
  elim y; intros H16 H19; elim H16; clear H16; intros H16 H20.

  split.
  assumption.  assumption.  
  exact
   (setex_intro (ste a)
      (fun ve : var_env'' =>
       eval_be' (mu_eval N te m re) (var_env''_to_env' ve) = true /\
       In var_env'' (Evar_env'' 0 N) ve)).
  elim (mu_eval_lemma1 N te te_ok m H6 H9).  intros.  apply H11.  assumption.  
  unfold In, Evar_env'' in H14.
  elim H14; intros H12 H15.

  intros.
  apply not_false_is_true.  unfold not in |- *; intro.  unfold var_env''_to_env' in H11.
  rewrite (H15 _ H16) in H11.  discriminate.  assumption.  assumption.  
  assumption.  assumption.  assumption.  
  intros.  unfold bool_expr_to_var_env'' in |- *.  inversion H1.  inversion H2.
  apply Extensionality_Ensembles.  split.  unfold Included in |- *.  intros.
  simpl in H12.  unfold In in H12.  unfold set_mu in H12.  unfold In in |- *.
  cut (bool_expr_to_var_env'' 0 N (mu_eval N te (mu_mu a m) re) x).
  unfold bool_expr_to_var_env'' in |- *.  trivial.  unfold In in H12.  apply H12.
  unfold state_set in |- *.  unfold set_1, Included in |- *.
  unfold bool_expr_to_var_env'', Evar_env'', In in |- *.  intros.  exact (proj2 H13).
  unfold Included in |- *.  intros.  unfold In in |- *.  unfold In in H13.  
  cut
   (mu_form2set ste m
      (sre_put sre a
         (fun v : var_env'' =>
          bool_expr_to_var_env'' 0 N (mu_eval N te (mu_mu a m) re) v)) x0).
  rewrite
   (H0 (re_put re a (mu_eval N te (mu_mu a m) re))
      (sre_put sre a
         (fun v : var_env'' =>
          bool_expr_to_var_env'' 0 N (mu_eval N te (mu_mu a m) re) v)))
   .
  unfold bool_expr_to_var_env'' in |- *.  intros.
  elim H14; clear H14; intros H16 H17.

  elim (mu_eval_mu_is_lfp N te te_ok a m re).  intros.  unfold fp in H14.
  unfold be_eq in H14.  rewrite (H14 (var_env''_to_env' x0)).  split.  
  assumption.  assumption.  assumption.  assumption.  assumption.  assumption.
  assumption.  unfold ad_to_be_ok in |- *.  intros.  unfold re_put in |- *.
  elim (sumbool_of_bool (Neqb a x1)).  intro y.  rewrite y.
  elim (mu_eval_lemma1 N te te_ok (mu_mu a m)).  intros.  apply H14.
  assumption.  assumption.  assumption.  intro y.  rewrite y.  apply H3.  
  unfold re_sre_ok in |- *.  unfold re_put, sre_put in |- *.  intro.
  elim (sumbool_of_bool (Neqb a P1)).  intro y.  rewrite y.
  unfold bool_expr_to_var_env'' in |- *.  reflexivity.  intro y.  rewrite y.  apply H4. 
  assumption.
  unfold Included in |- *.  unfold In in |- *.  intros.  simpl in |- *.  unfold set_mu in |- *.  intros.
  elim H12; clear H12; intros H16 H17.

  elim (env_to_be_lemma1 X H13).  intro Be.
  intro.  elim H12.  clear H12.  intros y H00.
  rewrite (H0 (re_put re a Be) (sre_put sre a X)) in H14.  simpl in H16.
  elim (mu_eval_lemma1 N te te_ok m).  intros.
  elim H15; intros H19 H18; elim H18; clear H18; intros H18 H21.

  clear H15 H18.  rewrite <- y.  unfold bool_expr_to_var_env'' in |- *.  split.
  cut
   (be_le
      (fst
         (iter2n bool_expr be_eq_dec
            (fun be : bool_expr => mu_eval N te m (re_put re a be)) Zero N))
      Be).
  intro.  unfold be_le in H15.  apply H15.  assumption.  
  apply
   be_le_trans
    with
      (be2 := fst
                (iter2n bool_expr be_eq_dec
                   (fun be : bool_expr => mu_eval N te m (re_put re a be)) Be
                   N)).
  apply
   be_le_trans
    with
      (be2 := be_iter1
                (fun be : bool_expr => mu_eval N te m (re_put re a be)) Zero
                (two_power N)).
  apply be_eq_le.  apply be_iter2n_2n.  intros.  apply H21.
  unfold ad_to_be_eq, re_put in |- *.  intros.  elim (Neqb a x0).  assumption.  
  apply be_eq_refl.  
  apply
   be_le_trans
    with
      (be2 := be_iter1
                (fun be : bool_expr => mu_eval N te m (re_put re a be)) Be
                (two_power N)).
  apply be_iter1_le_preserved.  apply be_le_zero.  intros.
  unfold re_to_be_inc in H19.  apply H19.  assumption.  assumption.  
  apply be_eq_le.  apply be_eq_sym.  apply be_iter2n_2n.  intros.  apply H21.
  unfold ad_to_be_eq, re_put in |- *.  intro.  elim (Neqb a x0).  assumption.  
  apply be_eq_refl.  
  apply
   be_le_trans
    with
      (be2 := be_iter1
                (fun be : bool_expr => mu_eval N te m (re_put re a be)) Be
                (two_power N)).
  apply be_eq_le.  apply be_iter2n_2n.  intros.  apply H21.
  unfold ad_to_be_eq, re_put in |- *.  intro.  elim (Neqb a x0).  assumption.  
  apply be_eq_refl.  
  rewrite
   (be_iter1eq2 (fun be : bool_expr => mu_eval N te m (re_put re a be))
      (two_power N) Be).
  generalize (two_power N).  simple induction n.  simpl in |- *.  apply be_le_refl.  intros.
  simpl in |- *.  apply be_le_trans with (be2 := mu_eval N te m (re_put re a Be)).
  unfold re_to_be_inc in H19.  apply H19.  assumption.  assumption.  
  unfold be_le in |- *.  intro.
  replace (eval_be' (mu_eval N te m (re_put re a Be)) ve) with
   (eval_be' (mu_eval N te m (re_put re a Be))
      (var_env''_to_env' (var_env'_to_env'' 0 N ve))).
  replace (eval_be' Be ve) with
   (eval_be' Be (var_env''_to_env' (var_env'_to_env'' 0 N ve))).
  rewrite <- y in H14.  unfold Included, bool_expr_to_var_env'' in H14.
  unfold In in H14.  intros.  elim (H14 (var_env'_to_env'' 0 N ve)).  intros.
  assumption.  split.  assumption.  unfold var_env'_to_env'' in |- *.
  elim (var_env'_to_var_env''_lemma2 (N - 0) 0 N ve (refl_equal (N - 0))).
  intros x0 y0.  exact (proj1 y0).  apply bool_fun_of_be_ext1.  intros.
  unfold var_env''_to_env', var_env'_to_env'' in |- *.
  elim (var_env'_to_var_env''_lemma2 (N - 0) 0 N ve (refl_equal (N - 0))).
  intros x1 y0.
  elim y0; intros H22 H23.

  rewrite <- (H23 _ (be_ok_be_x_free _ _ H00 _ H18)).
  rewrite (N_of_nat_of_N x0).  reflexivity.  apply bool_fun_of_be_ext1.
  intros.  unfold var_env''_to_env', var_env'_to_env'' in |- *.
  elim (var_env'_to_var_env''_lemma2 (N - 0) 0 N ve (refl_equal (N - 0))).
  intros x1 y0.
  elim y0; intros H22 H23.

  rewrite (N_of_nat_of_N x0).
  rewrite <- (H23 x0).  reflexivity.  
  apply be_ok_be_x_free with (be := mu_eval N te m (re_put re a Be)).
  elim (mu_eval_lemma1 N te te_ok m).  intros.  apply H20.
  unfold ad_to_be_ok, re_put in |- *.  intros.  elim (Neqb a x2).  assumption.  
  apply H3.  assumption.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  unfold ad_to_be_ok, re_put in |- *.  intros.
  elim (Neqb a x0).  assumption.  apply H3.  unfold re_sre_ok, re_put, sre_put in |- *.
  intros.  elim (sumbool_of_bool (Neqb a P1)).  intro y0.  rewrite y0.
  assumption.  intro y0.  rewrite y0.  apply H4.  
Qed.

End mu2set.