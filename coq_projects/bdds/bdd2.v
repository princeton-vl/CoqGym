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

Definition var (cfg : BDDconfig) (node : ad) :=
  match MapGet _ (fst cfg) node with
  | None => (* Error *)  BDDzero
  | Some (x, (l, r)) => x
  end.

Definition low (cfg : BDDconfig) (node : ad) :=
  match MapGet _ (fst cfg) node with
  | None => (* Error *)  N0
  | Some (x, (l, r)) => l
  end.

Definition high (cfg : BDDconfig) (node : ad) :=
  match MapGet _ (fst cfg) node with
  | None => (* Error *)  N0
  | Some (x, (l, r)) => r
  end.

Definition config_node_OK (cfg : BDDconfig) := node_OK (fst cfg).
Definition is_internal_node (cfg : BDDconfig) (node : ad) :=
  exists x : BDDvar,
    (exists l : ad,
       (exists r : ad, MapGet _ (fst cfg) node = Some (x, (l, r)))).

Lemma BDDvar_ordered_low :
 forall (cfg : BDDconfig) (node : ad),
 BDDconfig_OK cfg ->
 is_internal_node cfg node ->
 is_internal_node cfg (low cfg node) ->
 BDDcompare (var cfg (low cfg node)) (var cfg node) = Datatypes.Lt.
Proof.
  intro cfg.  elim cfg.  clear cfg.  intros bs y.  elim y.  clear y.
  intros share counter.  intros node H H0 H1.  elim H0.  intros x H2.  elim H2.  intros l H3.
  elim H3.  intros r H4.  clear H2 H3.  elim H1.  intros x1 H2.  elim H2.
  intros l1 H3.  elim H3.  intros r1 H5.  clear H2 H3.  unfold var, low in |- *.
  rewrite H4.  unfold low in H5.  rewrite H4 in H5.  rewrite H5.  elim H.
  intros H2 H3.  clear H3.  elim H2.  intros H3 H6.  elim H6.  intros H7 H8.
  cut (BDD_OK bs node).  intro H9.  unfold BDD_OK in H9.  unfold BDDordered in H9.
  simpl in H4.  simpl in H5.  rewrite H4 in H9.
  cut
   (node = BDDzero \/
    node = BDDone \/
    (exists x0 : BDDvar,
       (exists l0 : BDDvar,
          (exists r0 : BDDvar,
             MapGet _ bs node = Some (x0, (l0, r0)) /\
             BDDcompare x0 (ad_S x) = Datatypes.Lt /\
             Neqb l0 r0 = false /\
             BDDbounded bs l0 x0 /\ BDDbounded bs r0 x0)))).
  intros H10.  elim H10.  intro H11.  rewrite H11 in H4.  rewrite H4 in H3.
  discriminate H3.  intro H11.  elim H11.  intro H12.  rewrite H12 in H4.
  rewrite H4 in H6.  elim H6.  intros H13 H14.  discriminate H13.  intros H12.  elim H12.
  clear H12.  intros x0 H12.  elim H12.  clear H12.  intros x2 H12.  elim H12.  intros x3 H13.
  clear H12.  clear H10 H11.  elim H13.  intros H10 H11.  rewrite H4 in H10.
  injection H10.  intros H12 H14 H15.  rewrite <- H12 in H11.  rewrite <- H14 in H11.
  rewrite <- H15 in H11.  clear H13 H10.  cut (BDDbounded bs l x).  intros H10.
  cut
   (l = BDDzero \/
    l = BDDone \/
    (exists xl : BDDvar,
       (exists ll : BDDvar,
          (exists rl : BDDvar,
             MapGet _ bs l = Some (xl, (ll, rl)) /\
             BDDcompare xl x = Datatypes.Lt /\
             Neqb ll rl = false /\
             BDDbounded bs ll xl /\ BDDbounded bs rl xl)))).
  intros H13.  elim H13.  intro H16.  rewrite H16 in H5.  rewrite H5 in H3.
  discriminate H3.  intro H16.  elim H16.  intro H17.  rewrite H17 in H5.
  rewrite H5 in H7.  discriminate H7.  intro H17.  clear H13 H16.  elim H17.
  clear H17.  intros x4 H13.  elim H13.  clear H13.  intros x5 H13.  elim H13.  clear H13.
  intros x6 H13.  elim H13.  clear H13.  intros H13 H16.  rewrite H5 in H13.  injection H13.
  intros H17 H18 H19.  rewrite <- H19 in H16.  exact (proj1 H16).  
  apply BDDbounded_lemma.  assumption.  
  exact (proj1 (proj2 (proj2 H11))).  apply BDDbounded_lemma.
  assumption.  apply H8.  unfold in_dom in |- *.  simpl in H4.  rewrite H4.  trivial.
Qed.

Lemma BDDvar_ordered_high :
 forall (cfg : BDDconfig) (node : ad),
 BDDconfig_OK cfg ->
 is_internal_node cfg node ->
 is_internal_node cfg (high cfg node) ->
 BDDcompare (var cfg (high cfg node)) (var cfg node) = Datatypes.Lt.
Proof.
  intro cfg.  elim cfg.  clear cfg.  intros bs y.  elim y.  clear y.
  intros share counter.  intros node H H0 H1.  elim H0.  intros x H2.  elim H2.  intros l H3.
  elim H3.  intros r H4.  clear H2 H3.  elim H1.  intros x1 H2.  elim H2.
  intros l1 H3.  elim H3.  intros r1 H5.  clear H2 H3.  unfold var, high in |- *.
  rewrite H4.  unfold high in H5.  rewrite H4 in H5.  rewrite H5.  elim H.
  intros H2 H3.  clear H3.  elim H2.  intros H3 H6.  elim H6.  intros H7 H8.
  cut (BDD_OK bs node).  intro H9.  unfold BDD_OK in H9.  unfold BDDordered in H9.
  simpl in H4.  simpl in H5.  rewrite H4 in H9.
  cut
   (node = BDDzero \/
    node = BDDone \/
    (exists x0 : BDDvar,
       (exists l0 : BDDvar,
          (exists r0 : BDDvar,
             MapGet _ bs node = Some (x0, (l0, r0)) /\
             BDDcompare x0 (ad_S x) = Datatypes.Lt /\
             Neqb l0 r0 = false /\
             BDDbounded bs l0 x0 /\ BDDbounded bs r0 x0)))).
  intros H10.  elim H10.  intro H11.  rewrite H11 in H4.  rewrite H4 in H3.
  discriminate H3.  intro H11.  elim H11.  intro H12.  rewrite H12 in H4.
  rewrite H4 in H6.  elim H6.  intros H13 H14.  discriminate H13.  intros H12.  elim H12.
  clear H12.  intros x0 H12.  elim H12.  clear H12.  intros x2 H12.  elim H12.  intros x3 H13.
  clear H12.  clear H10 H11.  elim H13.  intros H10 H11.  rewrite H4 in H10.
  injection H10.  intros H12 H14 H15.  rewrite <- H12 in H11.  rewrite <- H14 in H11.
  rewrite <- H15 in H11.  clear H13 H10.  cut (BDDbounded bs r x).  intros H10.
  cut
   (r = BDDzero \/
    r = BDDone \/
    (exists xr : BDDvar,
       (exists lr : BDDvar,
          (exists rr : BDDvar,
             MapGet _ bs r = Some (xr, (lr, rr)) /\
             BDDcompare xr x = Datatypes.Lt /\
             Neqb lr rr = false /\
             BDDbounded bs lr xr /\ BDDbounded bs rr xr)))).
  intros H13.  elim H13.  intro H16.  rewrite H16 in H5.  rewrite H5 in H3.
  discriminate H3.  intro H16.  elim H16.  intro H17.  rewrite H17 in H5.
  rewrite H5 in H7.  discriminate H7.  intro H17.  clear H13 H16.  elim H17.
  clear H17.  intros x4 H13.  elim H13.  clear H13.  intros x5 H13.  elim H13.  clear H13.
  intros x6 H13.  elim H13.  clear H13.  intros H13 H16.  rewrite H5 in H13.  injection H13.
  intros H17 H18 H19.  rewrite <- H19 in H16.  exact (proj1 H16).  
  apply BDDbounded_lemma.  assumption.  
  exact (proj2 (proj2 (proj2 H11))).  apply BDDbounded_lemma.
  assumption.  apply H8.  unfold in_dom in |- *.  simpl in H4.  rewrite H4.  trivial.
Qed.

(* An interpretation of BDDvar's *)
Definition var_binding := BDDvar -> bool.
 
(* A boolean function. However not all boolean functions represent a logical
   formula. *)
Definition bool_fun := var_binding -> bool.

(* Evaluation of a boolean function given a binding of variables *)
Definition bool_fun_eval (bf : bool_fun) (vb : var_binding) := bf vb.

(* The boolean functions representing ZERO and ONE *)
Definition bool_fun_zero (vb : var_binding) := false. 
Definition bool_fun_one (vb : var_binding) := true. 

Fixpoint bool_fun_of_BDD_1 (cfg : BDDconfig) (node : ad) 
 (bound : nat) {struct bound} : bool_fun :=
  match MapGet _ (fst cfg) node with
  | None => if Neqb node BDDzero then bool_fun_zero else bool_fun_one
  | Some (x, (l, r)) =>
      match bound with
      | O => (* Error *)  bool_fun_zero
      | S bound' =>
          let bfl := bool_fun_of_BDD_1 cfg l bound' in
          let bfr := bool_fun_of_BDD_1 cfg r bound' in
          fun vb : var_binding => if vb x then bfr vb else bfl vb
      end
  end.

Lemma bool_fun_of_BDD_1_semantics :
 forall cfg : BDDconfig,
 BDDconfig_OK cfg ->
 forall bound : nat,
 bool_fun_of_BDD_1 cfg BDDzero bound = bool_fun_zero /\
 bool_fun_of_BDD_1 cfg BDDone bound = bool_fun_one /\
 (forall node : ad,
  is_internal_node cfg node ->
  nat_of_N (var cfg node) < bound ->
  forall vb : var_binding,
  (vb (var cfg node) = true ->
   bool_fun_eval (bool_fun_of_BDD_1 cfg node bound) vb =
   bool_fun_eval (bool_fun_of_BDD_1 cfg (high cfg node) (pred bound)) vb) /\
  (vb (var cfg node) = false ->
   bool_fun_eval (bool_fun_of_BDD_1 cfg node bound) vb =
   bool_fun_eval (bool_fun_of_BDD_1 cfg (low cfg node) (pred bound)) vb)).
Proof.
  intro cfg.  elim cfg.  clear cfg.  intros bs y.  elim y.  clear y.
  intros share counter.  intro H.  simple induction bound.  split.
  unfold bool_fun_of_BDD_1 in |- *.  elim H.  intros H0 H1.  elim H0.  intros H2 H3.  simpl in |- *.
  rewrite H2.  trivial.  split.  elim H.  intros H0 H1.  elim H0.  intros H2 H3.
  unfold bool_fun_of_BDD_1 in |- *.  simpl in |- *.  rewrite (proj1 H3).  trivial.
  unfold is_internal_node in |- *.  intro node.  intro H0.  unfold var in |- *.  elim H0.  clear H0.
  intros x H0.  elim H0.  clear H0.  intros l H0.  elim H0.  clear H0.
  intros r H0.  rewrite H0.  intro H1.  cut (~ nat_of_N x < 0).
  unfold not in |- *.  tauto.  apply lt_n_O.  intros n H0.  elim H.  intros H1 H2.  elim H1.
  intros H3 H4.  elim H4.  intros H5 H6.  split.  unfold bool_fun_of_BDD_1 in |- *.  simpl in |- *.
  rewrite H3.  trivial.  split.  unfold bool_fun_of_BDD_1 in |- *.  simpl in |- *.
  rewrite H5.  trivial.  intro node.  intro H7.  unfold is_internal_node in H7.
  elim H7.  clear H7.  intro x.  intro H7.  elim H7.  clear H7.  intro x0.  intro H7.
  elim H7.  clear H7.  intro x1.  intro H7.  unfold var in |- *.  rewrite H7.  intro H8.
  intro vb.  split.  intro H9.  unfold bool_fun_of_BDD_1 in |- *.  rewrite H7.
  unfold high in |- *.  rewrite H7.  unfold pred in |- *.  unfold bool_fun_eval in |- *.  rewrite H9.
  trivial.  intro H9.  unfold bool_fun_of_BDD_1 in |- *.  rewrite H7.
  unfold bool_fun_eval in |- *.  rewrite H9.  unfold pred in |- *.  unfold low in |- *.  rewrite H7.
  trivial.
Qed.

Lemma bool_fun_of_BDD_1_semantics_1 :
 forall cfg : BDDconfig,
 BDDconfig_OK cfg ->
 forall bound : nat,
 bool_fun_of_BDD_1 cfg BDDzero bound = bool_fun_zero /\
 bool_fun_of_BDD_1 cfg BDDone bound = bool_fun_one /\
 (forall node : ad,
  is_internal_node cfg node ->
  nat_of_N (var cfg node) < bound ->
  bool_fun_of_BDD_1 cfg node bound =
  (fun vb : var_binding =>
   if vb (var cfg node)
   then bool_fun_of_BDD_1 cfg (high cfg node) (pred bound) vb
   else bool_fun_of_BDD_1 cfg (low cfg node) (pred bound) vb)).
Proof.
  intro cfg.  elim cfg.  clear cfg.  intros bs y.  elim y.  clear y.
  intros share counter.  intro H.  simple induction bound.  split.
  unfold bool_fun_of_BDD_1 in |- *.  elim H.  intros H0 H1.  elim H0.  intros H2 H3.  simpl in |- *.
  rewrite H2.  trivial.  split.  elim H.  intros H0 H1.  elim H0.  intros H2 H3.
  unfold bool_fun_of_BDD_1 in |- *.  simpl in |- *.  rewrite (proj1 H3).  trivial.
  unfold is_internal_node in |- *.  intro node.  intro H0.  unfold var in |- *.  elim H0.  clear H0.
  intros x H0.  elim H0.  clear H0.  intros l H0.  elim H0.  clear H0.
  intros r H0.  rewrite H0.  intro H1.  cut (~ nat_of_N x < 0).  unfold not in |- *.
  tauto.  apply lt_n_O.  intros n H0.  elim H.  intros H1 H2.  elim H1.  intros H3 H4.  elim H4.
  intros H5 H6.  split.  unfold bool_fun_of_BDD_1 in |- *.  simpl in |- *.  rewrite H3.  trivial.
  split.  unfold bool_fun_of_BDD_1 in |- *.  simpl in |- *.  rewrite H5.  trivial.  intro node.
  intro H7.  unfold is_internal_node in H7.  elim H7.  clear H7.  intro x.  intro H7.
  elim H7.  clear H7.  intro x0.  intro H7.  elim H7.  clear H7.  intro x1.  intro H7.
  unfold var in |- *.  rewrite H7.  intro H8.  unfold pred in |- *.  unfold bool_fun_of_BDD_1 at 1 in |- *.
  rewrite H7.  unfold high in |- *.  rewrite H7.  unfold low in |- *.  rewrite H7.  trivial.
Qed.

Lemma bool_fun_of_BDD_1_semantics_2 :
 forall (cfg : BDDconfig) (node : ad) (bound1 bound2 : nat),
 MapGet _ (fst cfg) node = None ->
 bool_fun_of_BDD_1 cfg node bound1 = bool_fun_of_BDD_1 cfg node bound2.
Proof.
  intros cfg node bound1 bound2 H.  case bound1.  simpl in |- *.  case bound2.  simpl in |- *.  reflexivity.  simpl in |- *.
  rewrite H.  trivial.  simpl in |- *.  rewrite H.  case bound2.  simpl in |- *.  rewrite H.
  trivial.  simpl in |- *.  rewrite H.  trivial.  
Qed.

Lemma bool_fun_of_BDD_1_change_bound :
 forall cfg : BDDconfig,
 BDDconfig_OK cfg ->
 forall (bound : nat) (node : ad),
 nat_of_N (var cfg node) < bound ->
 bool_fun_of_BDD_1 cfg node bound =
 bool_fun_of_BDD_1 cfg node (S (nat_of_N (var cfg node))).
Proof.
  intro cfg.  elim cfg.  clear cfg.  intros bs y.  elim y.  clear y.
  intros share counter.  intro H.  intro bound.
  apply
   lt_wf_ind
    with
      (P := fun bound : nat =>
            forall node : ad,
            nat_of_N (var (bs, (share, counter)) node) < bound ->
            bool_fun_of_BDD_1 (bs, (share, counter)) node bound =
            bool_fun_of_BDD_1 (bs, (share, counter)) node
              (S (nat_of_N (var (bs, (share, counter)) node)))).
  intros n H0 node H1.  elim (option_sum _ (MapGet _ (fst (bs, (share, counter))) node)).
  intros y.  elim y.  clear y.  intro x.  elim x.  clear x.  intros x y.  elim y.
  clear y.  intros l r.  intros y.
  cut (is_internal_node (bs, (share, counter)) node).  intro H2.
  cut
   (bool_fun_of_BDD_1 (bs, (share, counter)) node n =
    (fun vb : var_binding =>
     match vb (var (bs, (share, counter)) node) with
     | true =>
         bool_fun_of_BDD_1 (bs, (share, counter))
           (high (bs, (share, counter)) node) (pred n) vb
     | false =>
         bool_fun_of_BDD_1 (bs, (share, counter))
           (low (bs, (share, counter)) node) (pred n) vb
     end)).
  intro H3.  rewrite H3.
  cut
   (bool_fun_of_BDD_1 (bs, (share, counter)) node
      (S (nat_of_N (var (bs, (share, counter)) node))) =
    (fun vb : var_binding =>
     match vb (var (bs, (share, counter)) node) with
     | true =>
         bool_fun_of_BDD_1 (bs, (share, counter))
           (high (bs, (share, counter)) node)
           (pred (S (nat_of_N (var (bs, (share, counter)) node)))) vb
     | false =>
         bool_fun_of_BDD_1 (bs, (share, counter))
           (low (bs, (share, counter)) node)
           (pred (S (nat_of_N (var (bs, (share, counter)) node)))) vb
     end)).
  intro H4.  rewrite H4.  unfold pred at 3 4 in |- *.
  cut
   (bool_fun_of_BDD_1 (bs, (share, counter))
      (high (bs, (share, counter)) node) (pred n) =
    bool_fun_of_BDD_1 (bs, (share, counter))
      (high (bs, (share, counter)) node)
      (nat_of_N (var (bs, (share, counter)) node))).
  intro H5.  rewrite H5.
  cut
   (bool_fun_of_BDD_1 (bs, (share, counter))
      (low (bs, (share, counter)) node) (pred n) =
    bool_fun_of_BDD_1 (bs, (share, counter))
      (low (bs, (share, counter)) node)
      (nat_of_N (var (bs, (share, counter)) node))).
  intro H6.  rewrite H6.  trivial.  
  elim
   (option_sum _
      (MapGet _ (fst (bs, (share, counter)))
         (low (bs, (share, counter)) node))).
  intros y0.  elim y0.  clear y0.  intro x0.  elim x0.  clear x0.  intros xl y0.
  elim y0.  clear y0.  intros ll rl.  intros y0.
  cut
   (nat_of_N (var (bs, (share, counter)) (low (bs, (share, counter)) node)) <
    pred n).
  intro H6.
  cut
   (nat_of_N (var (bs, (share, counter)) (low (bs, (share, counter)) node)) <
    nat_of_N (var (bs, (share, counter)) node)).
  intro H7.  clear H3 H4 H5.  cut (pred n < n).  intro H3.
  rewrite (H0 (pred n) H3 (low (bs, (share, counter)) node) H6).
  rewrite
   (H0 (nat_of_N (var (bs, (share, counter)) node)) H1
      (low (bs, (share, counter)) node) H7).
  trivial.  apply lt_pred_n_n.  apply neq_O_lt.  unfold not in |- *.  intro H3.
  rewrite <- H3 in H1.
  cut (~ nat_of_N (var (bs, (share, counter)) node) < 0).  unfold not in |- *.
  tauto.  apply lt_n_O.  apply BDDcompare_lt.  apply BDDvar_ordered_low.
  assumption.  assumption.  unfold is_internal_node in |- *.  split with xl.
  split with ll.  split with rl.  assumption.  
  apply
   le_lt_trans with (m := pred (nat_of_N (var (bs, (share, counter)) node))).
  cut (forall x y : nat, x < y -> x <= pred y).  intro H6.  apply H6.
  apply BDDcompare_lt.  apply BDDvar_ordered_low.  assumption.  assumption.
  unfold is_internal_node in |- *.  split with xl.  split with ll.  split with rl.
  assumption.  unfold lt in |- *.  double induction x0 y1.  auto.  intro n0.  intros H6 H7.
  auto with arith.  auto with arith.  intros n0 H6 n1 H7 H8.  unfold pred in |- *.  auto with arith.
  apply lt_pred.  assumption.  unfold not in |- *.  intro H6.
  cut (var (bs, (share, counter)) node = N0).
  cut (var (bs, (share, counter)) node <> N0).  auto.
  apply
   INFERIEUR_neq_O
    with (x := var (bs, (share, counter)) (low (bs, (share, counter)) node)).
  apply BDDvar_ordered_low.  assumption.  assumption.  split with xl.
  split with ll.  split with rl.  assumption.  apply O_N0.  assumption.
  intros y0.  apply bool_fun_of_BDD_1_semantics_2.  assumption.
  elim
   (option_sum _
      (MapGet _ (fst (bs, (share, counter)))
         (high (bs, (share, counter)) node))).
  intros y0.  elim y0.  clear y0.  intro x0.  elim x0.  clear x0.  intros xr y0.
  elim y0.  clear y0.  intros lr rr.  intros y0.
  cut
   (nat_of_N (var (bs, (share, counter)) (high (bs, (share, counter)) node)) <
    pred n).
  intro H5.
  cut
   (nat_of_N (var (bs, (share, counter)) (high (bs, (share, counter)) node)) <
    nat_of_N (var (bs, (share, counter)) node)).
  intro H6.  clear H3 H4.  cut (pred n < n).  intro H3.
  rewrite
   (H0 (nat_of_N (var (bs, (share, counter)) node)) H1
      (high (bs, (share, counter)) node) H6).
  rewrite (H0 (pred n) H3 (high (bs, (share, counter)) node) H5).  trivial.
  apply lt_pred_n_n.  apply neq_O_lt.  unfold not in |- *.  intro H3.
  rewrite <- H3 in H1.
  cut (~ nat_of_N (var (bs, (share, counter)) node) < 0).  unfold not in |- *.
  tauto.  apply lt_n_O.  apply BDDcompare_lt.  apply BDDvar_ordered_high.
  assumption.  assumption.  unfold is_internal_node in |- *.  split with xr.
  split with lr.  split with rr.  assumption.
  apply
   le_lt_trans with (m := pred (nat_of_N (var (bs, (share, counter)) node))).
  cut (forall x y : nat, x < y -> x <= pred y).  intro H5.  apply H5.
  apply BDDcompare_lt.  apply BDDvar_ordered_high.  assumption.  assumption.
  unfold is_internal_node in |- *.  split with xr.  split with lr.  split with rr.
  assumption.  unfold lt in |- *.  double induction x0 y1.  auto.  intro n0.  intros H5 H6.
  auto with arith.  auto with arith.  intros n0 H5 n1 H6 H7.  unfold pred in |- *.  auto with arith.
  apply lt_pred.  assumption.  unfold not in |- *.  intro H5.
  cut (var (bs, (share, counter)) node = N0).
  cut (var (bs, (share, counter)) node <> N0).  auto.  
  apply
   INFERIEUR_neq_O
    with (x := var (bs, (share, counter)) (high (bs, (share, counter)) node)).
  apply BDDvar_ordered_high.  assumption.  assumption.  split with xr.
  split with lr.  split with rr.  assumption.  apply O_N0.  assumption.
  intro y0.  apply bool_fun_of_BDD_1_semantics_2.  assumption.
  apply
   (proj2
      (proj2
         (bool_fun_of_BDD_1_semantics_1 (bs, (share, counter)) H
            (S (nat_of_N (var (bs, (share, counter)) node)))))).
  unfold is_internal_node in |- *.  split with x.  split with l.  split with r.
  assumption.  auto with arith.  
  apply
   (proj2 (proj2 (bool_fun_of_BDD_1_semantics_1 (bs, (share, counter)) H n))).
  unfold is_internal_node in |- *.  split with x.  split with l.  split with r.
  assumption.  auto with arith.  unfold is_internal_node in |- *.  split with x.
  split with l.  split with r.  assumption.  intros y.
  apply bool_fun_of_BDD_1_semantics_2.  assumption.
Qed.

Definition bool_fun_of_BDD (cfg : BDDconfig) (node : ad) :=
  bool_fun_of_BDD_1 cfg node (S (nat_of_N (var cfg node))).

Lemma bool_fun_of_BDD_semantics :
 forall cfg : BDDconfig,
 BDDconfig_OK cfg ->
 bool_fun_of_BDD cfg BDDzero = bool_fun_zero /\
 bool_fun_of_BDD cfg BDDone = bool_fun_one /\
 (forall node : ad,
  is_internal_node cfg node ->
  bool_fun_of_BDD cfg node =
  (fun vb : var_binding =>
   if vb (var cfg node)
   then bool_fun_of_BDD cfg (high cfg node) vb
   else bool_fun_of_BDD cfg (low cfg node) vb)).
Proof.
  intros cfg H.  unfold bool_fun_of_BDD in |- *.  split.
  apply
   (proj1
      (bool_fun_of_BDD_1_semantics_1 cfg H (S (nat_of_N (var cfg BDDzero))))).
  split.
  apply
   (proj1
      (proj2
         (bool_fun_of_BDD_1_semantics_1 cfg H
            (S (nat_of_N (var cfg BDDone)))))).
  intros node H0.  cut (nat_of_N (var cfg node) < S (nat_of_N (var cfg node))).
  intro H1.
  rewrite
   (proj2
      (proj2
         (bool_fun_of_BDD_1_semantics_1 cfg H (S (nat_of_N (var cfg node)))))
      node H0 H1).
  cut
   (bool_fun_of_BDD_1 cfg (high cfg node)
      (pred (S (nat_of_N (var cfg node)))) =
    bool_fun_of_BDD_1 cfg (high cfg node)
      (S (nat_of_N (var cfg (high cfg node))))).
  intro H2.
  cut
   (bool_fun_of_BDD_1 cfg (low cfg node)
      (pred (S (nat_of_N (var cfg node)))) =
    bool_fun_of_BDD_1 cfg (low cfg node)
      (S (nat_of_N (var cfg (low cfg node))))).
  intro H3.  rewrite H2.  rewrite H3.  trivial.  unfold pred in |- *.
  elim (option_sum _ (MapGet _ (fst cfg) (low cfg node))).  intros y.  elim y.
  clear y.  intro x.  elim x.  clear x.  intros x y.  elim y.  clear y.
  intros l r.  intro y.
  cut (nat_of_N (var cfg (low cfg node)) < nat_of_N (var cfg node)).
  intro H3.
  rewrite
   (bool_fun_of_BDD_1_change_bound cfg H (nat_of_N (var cfg node))
      (low cfg node) H3).
  trivial.  apply BDDcompare_lt.  apply BDDvar_ordered_low.  assumption.
  assumption.  unfold is_internal_node in |- *.  split with x.  split with l.
  split with r.  assumption.  intros y.  apply bool_fun_of_BDD_1_semantics_2.
  assumption.  unfold pred in |- *.
  elim (option_sum _ (MapGet _ (fst cfg) (high cfg node))).  intros y.  elim y.
  clear y.  intro x.  elim x.  clear x.  intros x y.  elim y.  clear y.
  intros l r.  intro y.
  cut (nat_of_N (var cfg (high cfg node)) < nat_of_N (var cfg node)).
  intro H2.
  rewrite
   (bool_fun_of_BDD_1_change_bound cfg H (nat_of_N (var cfg node))
      (high cfg node) H2).
  trivial.  apply BDDcompare_lt.  apply BDDvar_ordered_high.  assumption.
  assumption.  unfold is_internal_node in |- *.  split with x.  split with l.
  split with r.  assumption.  intros y.  apply bool_fun_of_BDD_1_semantics_2.
  assumption.  unfold lt in |- *.  auto.  
Qed.

Definition bool_fun_eq (bf1 bf2 : bool_fun) :=
  forall vb : var_binding, bool_fun_eval bf1 vb = bool_fun_eval bf2 vb.

Lemma bool_fun_eq_symm :
 forall bf1 bf2 : bool_fun, bool_fun_eq bf1 bf2 -> bool_fun_eq bf2 bf1.
Proof.
  unfold bool_fun_eq in |- *.  unfold bool_fun_eval in |- *.  intros bf1 bf2 H vb.  rewrite (H vb).
  reflexivity.
Qed.

Lemma bool_fun_eq_trans :
 forall bf1 bf2 bf3 : bool_fun,
 bool_fun_eq bf1 bf2 -> bool_fun_eq bf2 bf3 -> bool_fun_eq bf1 bf3.
Proof.
  unfold bool_fun_eq in |- *.  unfold bool_fun_eval in |- *.  intros bf1 bf2 bf3 H H0 vb.  rewrite (H vb).
  rewrite <- (H0 vb).  reflexivity.
Qed.

Definition bool_fun_neg (bf : bool_fun) : bool_fun :=
  fun vb : var_binding => negb (bf vb).
Definition bool_fun_or (bf1 bf2 : bool_fun) : bool_fun :=
  fun vb : var_binding => bf1 vb || bf2 vb.

Lemma bool_fun_neg_semantics :
 forall (bf : bool_fun) (vb : var_binding),
 (bool_fun_eval bf vb = true -> bool_fun_eval (bool_fun_neg bf) vb = false) /\
 (bool_fun_eval bf vb = false -> bool_fun_eval (bool_fun_neg bf) vb = true).
Proof.
  intros bf vb.  unfold bool_fun_eval in |- *.  unfold bool_fun_neg in |- *.  unfold negb in |- *.
  elim (bf vb).  auto.  auto.
Qed.

Lemma bool_fun_neg_zero : bool_fun_neg bool_fun_zero = bool_fun_one.
Proof.
  unfold bool_fun_neg, bool_fun_zero, bool_fun_one in |- *.  simpl in |- *.  trivial.
Qed.

Lemma bool_fun_neg_one : bool_fun_neg bool_fun_one = bool_fun_zero.
Proof.
  unfold bool_fun_neg, bool_fun_zero, bool_fun_one in |- *.  simpl in |- *.  trivial.
Qed.

Lemma bool_fun_eq_neg :
 forall bf1 bf2 : bool_fun,
 bool_fun_eq (bool_fun_neg bf1) (bool_fun_neg bf2) -> bool_fun_eq bf1 bf2.
Proof.
  unfold bool_fun_eq, bool_fun_neg in |- *.  unfold bool_fun_eval in |- *.  intros bf1 bf2 H vb.
  cut (negb (bf1 vb) = negb (bf2 vb)).  unfold negb in |- *.  elim (bf1 vb).
  elim (bf2 vb).  intro H0.  reflexivity.  intro H0.  rewrite H0.  reflexivity.
  elim (bf2 vb).  intro H0.  rewrite H0.  reflexivity.  intro H0.  reflexivity.  
  apply H.
Qed.

Lemma bool_fun_eq_neg_1 :
 forall bf1 bf2 : bool_fun,
 bool_fun_eq bf1 bf2 -> bool_fun_eq (bool_fun_neg bf1) (bool_fun_neg bf2).
Proof.
unfold bool_fun_eq, bool_fun_neg in |- *.  unfold bool_fun_eval in |- *.  unfold negb in |- *.  intros bf1 bf2 H vb.
rewrite (H vb).  reflexivity.
Qed.

Definition BDDneg_memo := Map ad.
Definition BDDneg_memo_lookup (memo : BDDneg_memo) 
  (a : ad) := MapGet _ memo a.
Definition BDDneg_memo_put (memo : BDDneg_memo) (a node : ad) :=
  MapPut _ memo a node.

Definition BDDneg_memo_OK (cfg : BDDconfig) (memo : BDDneg_memo) :=
  forall a node : ad,
  BDDneg_memo_lookup memo a = Some node ->
  config_node_OK cfg node /\
  bool_fun_of_BDD cfg node = bool_fun_neg (bool_fun_of_BDD cfg a) /\
  var cfg a = var cfg node. 

Fixpoint BDDneg_2 (cfg : BDDconfig) (node : ad) (bound : nat) {struct bound} 
   : BDDconfig * ad :=
  match MapGet _ (fst cfg) node with
  | None => if Neqb node BDDzero then (cfg, BDDone) else (cfg, BDDzero)
  | Some (x, (l, r)) =>
      match bound with
      | O => (* Error *)  (initBDDconfig, BDDzero)
      | S bound' =>
          BDDmake (fst (BDDneg_2 (fst (BDDneg_2 cfg l bound')) r bound')) x
            (snd (BDDneg_2 cfg l bound'))
            (snd (BDDneg_2 (fst (BDDneg_2 cfg l bound')) r bound'))
      end
  end.

(*
Lemma BDDneg_2_lemma :
  (bound:nat)(cfg:BDDconfig)(node:ad)
  (BDDconfig_OK cfg) ->
  (config_node_OK cfg node) ->
  ( (is_internal_node cfg node) ->
    (lt (nat_of_N (var cfg node)) bound) ) ->
  (BDDconfig_OK (Fst (BDDneg_2 cfg node bound)))
  /\ ( (x:BDDvar)(l,r,a:ad)
       (MapGet ? (Fst cfg) a)=(Some (x,(l,r))) ->
       (MapGet ? (Fst (Fst (BDDneg_2 cfg node bound))) a)=
         (Some (x,(l,r)))
     )
  /\ ( (is_internal_node cfg node) ->
       (is_internal_node (Fst (BDDneg_2 cfg node bound))
                         (Snd (BDDneg_2 cfg node bound)))
       /\ (var cfg node)=(var (Fst (BDDneg_2 cfg node bound))
                         (Snd (BDDneg_2 cfg node bound))) )
  /\ (config_node_OK (Fst (BDDneg_2 cfg node bound))
                     (Snd (BDDneg_2 cfg node bound)))
  /\ (bool_fun_eq (bool_fun_of_BDD (Fst (BDDneg_2 cfg node bound))
                      (Snd (BDDneg_2 cfg node bound)))
        (bool_fun_neg (bool_fun_of_BDD cfg node))).
Proof.
  Intro.
  Apply lt_wf_ind with P:=[bound:nat] (cfg:BDDconfig; node:ad)
  (BDDconfig_OK cfg) ->(config_node_OK cfg node) ->((is_internal_node cfg node)
   ->(lt (nat_of_N (var cfg node)) bound)) ->(BDDconfig_OK (Fst (BDDneg_2 cfg
  node bound))) /\((x:BDDvar; l,r,a:ad) (MapGet ? (Fst cfg) a)=(Some
  (x,(l,r))) ->(MapGet ? (Fst (Fst (BDDneg_2 cfg node bound))) a) =(Some
  (x,(l,r)))) /\((is_internal_node cfg node) ->(is_internal_node (Fst (BDDneg_2 
  cfg node bound)) (Snd (BDDneg_2 cfg node bound))) /\(var cfg node) =(var (Fst
  (BDDneg_2 cfg node bound)) (Snd (BDDneg_2 cfg node bound)))) /\(config_node_OK
  (Fst (BDDneg_2 cfg node bound)) (Snd (BDDneg_2 cfg node bound))) /\
  (bool_fun_eq (bool_fun_of_BDD (Fst (BDDneg_2 cfg node bound)) (Snd (BDDneg_2
  cfg node bound))) (bool_fun_neg (bool_fun_of_BDD cfg node))).
  Intro.  Elim n.  Intro.  Intro.  Elim cfg.  Clear cfg.  Intros bs y.  Elim y.   Clear y.  Intros share counter.  Intros.  Unfold BDDneg_2.
  Elim (option_sum ?  (MapGet BDDvar*ad*ad (Fst (bs,(share,counter))) node)).  Intros.
  Elim y.  Clear y.  Intro y.  Elim y.  Clear y.  Intros x y.  Elim y.  Clear y.
  Intros l r.  Intro.  Cut False.  Tauto.  Cut ~(lt (nat_of_N (var (bs,(share,counter)) node)) (0)).
  Unfold not.  Intro.  Apply H3.  Apply H2.  Unfold is_internal_node.  Split with x.
  Split with l.  Split with r.  Assumption.  Apply lt_n_O.  Intro.  Rewrite y.
  Elim H1.  Intro.  Rewrite H3.  Simpl.  Split.  Exact H0.  Split.  Intros.
  Assumption.  Split.  Split.  Unfold is_internal_node in H4.  Elim H4.  Intros.
  Elim H5.  Intros.  Elim H6.  Intros.  Rewrite H3 in y.  Rewrite y in H7.
  Discriminate H7.  Unfold is_internal_node in H4.  Elim H4.  Intros.  Elim H5. 
  Intros.  Elim H6.  Intros.  Rewrite H3 in y.  Rewrite y in H7.
  Discriminate H7.  Split.  Right.  Left.  Reflexivity.
  Rewrite (proj1 ? ? (bool_fun_of_BDD_semantics (bs,(share, counter)) H0)).
  Rewrite (proj1 ? ?  (proj2 ? ?  (bool_fun_of_BDD_semantics (bs,(share,counter)) H0))).
  Unfold bool_fun_eq.  Unfold bool_fun_eval.  Unfold bool_fun_one bool_fun_zero bool_fun_neg.
  Simpl.  Reflexivity.  Intro.  Elim H3.  Clear H3.  Intro.  Rewrite H3.  Simpl.
  Split.  Exact H0.  Split.  Intros.  Assumption.  Split.  Split.  Unfold is_internal_node in H4.  Elim H4.
  Intros.  Elim H5.  Intros.  Elim H6.  Intros.  Rewrite H3 in y.  Rewrite y in
  H7.
  Discriminate H7.  Unfold is_internal_node in H4.  Elim H4.  Intros.  Elim H5.
  Intros.  Elim H6.  Intros.  Rewrite H3 in y.  Rewrite y in H7.  Discriminate H7.
  Split.  Left.  Reflexivity.  Rewrite (proj1 ? ?  (bool_fun_of_BDD_semantics (bs,(share,counter)) H0)).
  Rewrite (proj1 ? ?  (proj2 ? ?  (bool_fun_of_BDD_semantics (bs,(share,counter)) H0))).
  Unfold bool_fun_eq.  Unfold bool_fun_eval bool_fun_zero bool_fun_one bool_fun_neg.
  Reflexivity.  Clear H3.  Intro.  Unfold in_dom in H3.  Rewrite y in H3.
  Discriminate H3.  Intro.  Intro.  Intro.  Intro cfg.  Elim cfg.  Clear cfg.
  Intros bs y.  Elim y.  Clear y.  Intros share counter.  Intros.  Elim H2.
  Intro.  Rewrite H4.  Unfold BDDneg_2.  (Simpl; Rewrite (proj1 ? ? (proj1 ? ?
  H1))).
  Split.  Exact H1.  Split.  Intros.  Exact H5.  Split.  Intros.
  Unfold is_internal_node in H5.  (Elim H5; Intros; Elim H6; Intros; Elim H7; Intros).
  Simpl in H8.  Rewrite (proj1 ? ? (proj1 ? ? H1)) in H8.  Discriminate H8.  
  Split.  Simpl.  Right.  Left.  Reflexivity.  Rewrite (proj1 ? ?  (bool_fun_of_BDD_semantics (bs,(share,counter)) H1)).
  Simpl.  Rewrite (proj1 ? ?  (proj2 ? ?  (bool_fun_of_BDD_semantics (bs,(share,counter)) H1))).
  Unfold bool_fun_eq.  Reflexivity.  (Intro; Elim H4; Clear H4; Intro).  Rewrite  H4.
  (Simpl; Rewrite (proj1 ? ? (proj2 ? ? (proj1 ? ? H1)))).  Split.
  Unfold BDDneg_2.  Exact H1.  Split.  Intros.  Exact H5.  Split.  Intro.
  Unfold is_internal_node in H5.  (Elim H5; Intros).  (Elim H6; Intros; Elim H7;
  Intros).
  (Simpl in H8; Rewrite (proj1 ? ? (proj2 ? ? (proj1 ? ? H1))) in H8; Discriminate H8).
  Split.  Simpl.  (Left; Reflexivity).  (Simpl; Rewrite (proj1 ? ? (bool_fun_of_BDD_semantics (bs,(share,counter)) H1));
  Rewrite (proj1 ? ?  (proj2 ? ?  (bool_fun_of_BDD_semantics (bs,(share,counter)) H1)))).
  Unfold bool_fun_eq.  Reflexivity.  Elim (option_sum ? (MapGet ? (Fst (bs,(share,counter))) node)).
  (Intros; Elim y; Clear y; Intro y; Elim y; Clear y; Intros x y; Elim y; Clear y; Intros l r).
  Intro.  Cut (config_node_OK (bs,(share,counter)) l).  Cut (config_node_OK (bs,(share, counter)) r).
  Intros.  Simpl in y.  (Unfold BDDneg_2; Simpl; Rewrite y; Fold BDDneg_2).
  Cut (is_internal_node (bs,(share,counter)) l) ->(lt (nat_of_N (var (bs,(share,counter)) l)) n0).
  Cut (BDDconfig_OK (Fst (BDDneg_2 (bs, (share,counter)) l n0))) /\((x0:BDDvar; l0,r0,a:ad) (MapGet ? (Fst (bs,(share, counter))) a)=(Some (x0,(l0,r0))) ->(MapGet ? (Fst (Fst (BDDneg_2 (bs, (share,counter)) l n0))) a) =(Some (x0,(l0,r0)))) /\((is_internal_node (bs, (share,counter)) l) ->(is_internal_node (Fst (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (bs,(share,counter)) l n0))) /\(var (bs,(share,counter)) l) =(var (Fst (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (bs,(share, counter)) l n0)))) /\(config_node_OK (Fst (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (bs,(share,counter)) l n0))) /\(bool_fun_eq (bool_fun_of_BDD (Fst (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (bs,(share,counter)) l n0))) (bool_fun_neg (bool_fun_of_BDD (bs,(share, counter)) l))).
  Intros.  (Elim H7; Clear H7; Intros).  (Elim H9; Clear H9; Intros).  (Elim H10; Clear H10; Intros).
  (Elim H11; Clear H11; Intros).  Cut (config_node_OK (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r).
  Cut (is_internal_node (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r) ->(lt (nat_of_N (var (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r)) n0).
  Intros.  Cut (BDDconfig_OK (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))) /\((x0:BDDvar; l0,r0,a:ad) (MapGet ? (Fst (Fst (BDDneg_2 (bs,(share, counter)) l n0))) a) =(Some (x0,(l0,r0))) ->(MapGet ?  (Fst (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))) a)=(Some (x0,(l0,r0)))) /\((is_internal_node (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r) ->(is_internal_node (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))) /\(var (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r) =(var (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)))) /\(config_node_OK (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))) /\(bool_fun_eq (bool_fun_of_BDD (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))) (bool_fun_neg (bool_fun_of_BDD (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r))).
  Intros.  (Elim H15; Clear H15; Intros; Elim H16; Clear H16; Intros; Elim H17; Clear H17; Intros).
  Elim H18.  Clear H18.  Intros.  Cut (node_OK (Fst (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))) (Snd (BDDneg_2 (bs,(share,counter)) l n0))).
  Cut (node_OK (Fst (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))).
  Cut (xl:BDDvar; ll,rl:ad) (MapGet ?  (Fst (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))) (Snd (BDDneg_2 (bs,(share,counter)) l n0))) =(Some (xl,(ll,rl))) ->(BDDcompare xl x)=INFERIEUR.
  Cut (xr:BDDvar; lr,rr:ad) (MapGet ?  (Fst (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))) =(Some (xr,(lr,rr))) ->(BDDcompare xr x) =INFERIEUR.
  Intros.
  Cut (BDDconfig_OK (Fst (BDDmake (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)) x (Snd (BDDneg_2 (bs,(share, counter)) l n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))))) /\((Neqb (Snd (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))) =false ->(MapGet ?  (Fst (Fst (BDDmake (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)) x (Snd (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))))) (Snd (BDDmake (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)) x (Snd (BDDneg_2 (bs,(share, counter)) l n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))))) =(Some  (x, ((Snd (BDDneg_2 (bs,(share,counter)) l n0)), (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)))))) /\((Neqb (Snd (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs, (share,counter)) l n0)) r n0))) =true ->(Snd (BDDmake (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)) x (Snd (BDDneg_2 (bs,(share, counter)) l n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))))=(Snd (BDDneg_2 (bs,(share,counter)) l n0))) /\((a,l',r':ad; x':BDDvar) ((MapGet ?  (Fst (Fst (BDDmake (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share, counter)) l n0)) r n0)) x (Snd (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))))) a)=(Some (x', (l',r'))) ->(MapGet ?  (Fst (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))) a)=(Some (x',(l',r'))) \/(Snd (BDDmake (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)) x (Snd (BDDneg_2 (bs,(share, counter)) l n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))))=a) /\((MapGet ?  (Fst (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share, counter)) l n0)) r n0))) a)=(Some (x',(l',r'))) ->(MapGet ?  (Fst (Fst (BDDmake (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)) x (Snd (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs, (share,counter)) l n0)) r n0))))) a)=(Some (x',(l',r'))))) /\(node_OK (Fst (Fst (BDDmake (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)) x (Snd (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))))) (Snd (BDDmake (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)) x (Snd (BDDneg_2 (bs,(share, counter)) l n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))))).
  Intros.  (Elim H24; Clear H24; Intros; Elim H25; Clear H25; Intros; 
  Elim H26; Clear H26; Intros).  (Elim H27; Clear H27; Intros).  Split.
  Assumption.  Cut (x0:BDDvar; l0,r0,a:ad) (MapGet BDDvar*ad*ad bs a)=(Some BDDvar*ad*ad (x0,(l0,r0))) ->(MapGet BDDvar*ad*ad (Fst (Fst (BDDmake (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)) x (Snd (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share, counter)) l n0)) r n0))))) a)=(Some BDDvar*ad*ad (x0,(l0,r0))).
  Intros.  Split.  Assumption.  Cut (is_internal_node (bs,(share,counter)) node) ->(is_internal_node (Fst (BDDmake (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share, counter)) l n0)) r n0)) x (Snd (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)))) (Snd (BDDmake (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)) x (Snd (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs, (share,counter)) l n0)) r n0))))) /\(var (bs,(share,counter)) node) =(var (Fst (BDDmake (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)) x (Snd (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs, (share,counter)) l n0)) r n0)))) (Snd (BDDmake (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)) x (Snd (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))))).
  Intros.  Split.  Assumption.  Cut (config_node_OK (Fst (BDDmake (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)) x (Snd (BDDneg_2 (bs,(share, counter)) l n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)))) (Snd (BDDmake (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)) x (Snd (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))))).
  Intros.  Split.  Assumption.  Cut (bool_fun_eq (bool_fun_of_BDD (Fst (BDDmake (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)) x (Snd (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)))) (Snd (BDDneg_2 (bs,(share,counter)) l n0))) (bool_fun_neg (bool_fun_of_BDD (bs, (share,counter)) l))).
  Intro.  Cut (bool_fun_eq (bool_fun_of_BDD (Fst (BDDmake (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)) x (Snd (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs, (share,counter)) l n0)) r n0)))) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share, counter)) l n0)) r n0))) (bool_fun_neg (bool_fun_of_BDD (bs,(share,counter)) r))).
  Intro.  Cut (Neqb (Snd (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))) =false.
  Intro.  Cut (MapGet BDDvar*ad*ad (Fst (Fst (BDDmake (Fst (BDDneg_2 (Fst (BDDneg_2 (bs, (share,counter)) l n0)) r n0)) x (Snd (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))))) (Snd (BDDmake (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)) x (Snd (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs, (share,counter)) l n0)) r n0))))) =(Some BDDvar*ad*ad (x, ((Snd (BDDneg_2 (bs, (share,counter)) l n0)), (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))))).
  Intro.  Cut (is_internal_node (Fst (BDDmake (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)) x (Snd (BDDneg_2 (bs,(share, counter)) l n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)))) (Snd (BDDmake (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)) x (Snd (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))))).
  Intro.  Rewrite (proj2 ? ?  (proj2 ? ? (bool_fun_of_BDD_semantics ? H24)) ? H36).
  Cut (is_internal_node (bs,(share,counter)) node).  Intro.  Rewrite (proj2 ? ? (proj2 ? ?  (bool_fun_of_BDD_semantics ? H1)) ? H37).
  Unfold var high low.  Rewrite H35.  Simpl.  Rewrite y.  Unfold bool_fun_eq in H32.
  Unfold bool_fun_eval in H32.  Unfold bool_fun_eq.  Unfold bool_fun_eval.  Unfold bool_fun_neg.
  Intro.  Rewrite (H32 vb).  Unfold bool_fun_eq in H33.  Unfold bool_fun_eval in H33.
  Rewrite (H33 vb).  (Elim (vb x); Reflexivity).  Unfold is_internal_node.
  Split with x.  Split with l.  Split with r.  Assumption.  Unfold is_internal_node.
  Split with x.  Split with (Snd (BDDneg_2 (bs,(share, counter)) l n0)).
  Split with (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share, counter)) l n0)) r n0)). 
  Assumption.  Apply H25.  Assumption.  Cut ~(Neqb (Snd (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs, (share,counter)) l n0)) r n0))) =true.
  Elim (Neqb (Snd (BDDneg_2 (bs,(share, counter)) l n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))).
  Unfold not.  Intro.  Cut False.  Tauto.  Apply H34.  Reflexivity.  
  Intro.  Reflexivity.  Unfold not.  Intro.  Cut (Snd (BDDneg_2 (bs,(share, counter)) l n0)) =(Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)). 
  Intro.  Rewrite <- H35 in H33.  Cut (bool_fun_eq (bool_fun_neg (bool_fun_of_BDD (bs,(share,counter)) r)) (bool_fun_neg (bool_fun_of_BDD (bs, (share,counter)) l))).
  Intro.  Cut (bool_fun_eq (bool_fun_of_BDD (bs,(share, counter)) r) (bool_fun_of_BDD (bs,(share,counter)) l)).
  Intro.  Cut r=l.  Intro.  Cut (Neqb l r)=true.  Intro.  Elim H1.  Intros.
  Elim H40.  Intros.  Elim H43.  Intros.  Cut (BDD_OK bs node).  Unfold BDD_OK. 
  Unfold BDDordered.  Rewrite y.  Intro.  Cut node=BDDzero \/node=BDDone \/(EX x0:BDDvar | (EX l0:BDDvar | (EX r0:BDDvar | (MapGet ? bs node)=(Some (x0,(l0,r0))) /\(BDDcompare x0 (ad_S x))=INFERIEUR /\(Neqb l0 r0)=false /\(BDDbounded bs l0 x0)/\(BDDbounded bs r0 x0)))).
  Intro.  Elim H47.  Intro.  Rewrite H48 in y.  Rewrite y in H42.
  Discriminate H42.  (Clear H47; Intro).  Elim H47.  Clear H47.  Intro.
  (Rewrite H47 in y; Rewrite y in H44; Discriminate).  Intro.  Elim H48.
  Intros.  (Elim H49; Intros; Elim H50; Intros).  Elim H51.  Intros.  Rewrite y in H52.
  Injection H52.  Intros.  Rewrite <- H54 in H53.  Rewrite <- H55 in H53.
  Rewrite H39 in H53.  (Elim H53; Intros).  (Elim H58; Intros).  Discriminate H59.
  Apply BDDbounded_lemma.  Assumption.  Apply H45.  Unfold in_dom.  Rewrite y.  
  Reflexivity.  Rewrite H38.  Apply Neqb_correct.  Apply BDDunique with cfg:=(bs,(share,counter)).
  Assumption.  Assumption.  Assumption.  Assumption.  Apply bool_fun_eq_neg.
  Assumption.  Apply bool_fun_eq_trans with bf2:=(bool_fun_of_BDD (Fst (BDDmake (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)) x (Snd (BDDneg_2 (bs,(share, counter)) l n0)) (Snd (BDDneg_2 (bs,(share,counter)) l n0)))) (Snd (BDDneg_2 (bs,(share,counter)) l n0))).
  Apply bool_fun_eq_symm.  Assumption.  Rewrite H35.  Rewrite H35 in H32.
  Assumption.  Apply Neqb_complete.  Assumption.  Apply bool_fun_eq_trans with bf2:=(bool_fun_of_BDD (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))).
  Apply bool_fun_preservation.  Assumption.  Assumption.  Intros.  Apply (proj2 ? ? (H27 a l0 r0 x0)).
  Assumption.  Assumption.  Apply bool_fun_eq_trans with bf2:=(bool_fun_neg (bool_fun_of_BDD (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r)).
  Assumption.  Apply bool_fun_eq_neg_1.  Apply bool_fun_preservation.  Assumption.  
  Assumption.  Assumption.  Assumption.  Apply bool_fun_eq_trans with bf2:= (bool_fun_of_BDD (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)) (Snd (BDDneg_2 (bs,(share,counter)) l n0))).
  Apply bool_fun_preservation.  Assumption.  Assumption.  Intros.  Apply (proj2 ? ?  (H27 a l0 r0 x0)).
  Assumption.  Assumption.  Apply bool_fun_eq_trans with bf2 :=(bool_fun_of_BDD (Fst (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (bs,(share,counter)) l n0))).
  Apply bool_fun_preservation.  Assumption.  Assumption.  Assumption.  Assumption.
  Assumption.  Assumption.  Intro.  Elim (sumbool_of_bool (Neqb (Snd (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)))).
  Intro.  Cut (Snd (BDDneg_2 (bs,(share,counter)) l n0)) =(Snd (BDDneg_2 (Fst (BDDneg_2 (bs, (share,counter)) l n0)) r n0)).
  Intro.  Rewrite <- H31 in H19.  Cut (bool_fun_eq (bool_fun_of_BDD (Fst (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (bs,(share,counter)) l n0))) (bool_fun_neg (bool_fun_of_BDD (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r))).
  Intro.  Cut (bool_fun_eq (bool_fun_of_BDD (Fst (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (bs,(share,counter)) l n0))) (bool_fun_neg (bool_fun_of_BDD (bs,(share, counter)) r))).
  Intro.  Cut (Neqb l r)=true.  Intro.  Elim H1.  Intros.  (Elim H35; Intros). 
  (Elim H38; Intros).  Cut (BDD_OK bs node).  Unfold BDD_OK.  Unfold BDDordered.
  Rewrite y.  Intro.  Cut node=BDDzero \/node=BDDone \/(EX x0:BDDvar | (EX l0:BDDvar | (EX r0:BDDvar | (MapGet ? bs node)=(Some (x0,(l0,r0))) /\(BDDcompare x0 (ad_S x))=INFERIEUR /\(Neqb l0 r0)=false /\(BDDbounded bs l0 x0)/\(BDDbounded bs r0 x0)))).
  Intro.  (Elim H42; Intros).  (Rewrite H43 in y; Rewrite y in H37; Discriminate).
  Elim H43.  Intro.  (Rewrite H44 in y; Rewrite y in H39; Discriminate).  Intro.
  (Elim H44; Intros; Elim H45; Intros; Elim H46; Intros).  (Elim H47; Intros;
  Elim H48; Intros; Elim H49; Intros).  (Elim H51; Intros).  (Rewrite y in H48; 
  Injection H48).  Intros.  Rewrite <- H54 in H52.  Rewrite <- H55 in H52.
  Rewrite H34 in H52.  Discriminate H52.  Apply BDDbounded_lemma.  Assumption.
  Apply H40.  Assumption.  Cut l=r.  Intro.  (Rewrite H34; Apply Neqb_correct).
  Apply BDDunique with cfg:=(bs,(share,counter)).  Assumption.  Assumption.
  Assumption.  Apply bool_fun_eq_neg.  Apply bool_fun_eq_trans with bf2:= (bool_fun_of_BDD (Fst (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (bs,(share,counter)) l n0))).
  Apply bool_fun_eq_symm.  Assumption.  Assumption.  Apply bool_fun_eq_trans with bf2:=(bool_fun_neg (bool_fun_of_BDD (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r)).
  Assumption.  Apply bool_fun_eq_neg_1.  Apply bool_fun_preservation.  Assumption.
  Assumption.  Assumption.  Assumption.  Apply bool_fun_eq_trans with bf2:=(bool_fun_of_BDD (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))).
  Rewrite <- H31.  Apply bool_fun_eq_symm.  Apply bool_fun_preservation.  Assumption.  
  Assumption.  Intros.  Apply H16.  Assumption.  Assumption.  Rewrite <- H31.
  Assumption.  Apply Neqb_complete.  Assumption.  Intro.  Unfold
  is_internal_node var.
  Rewrite (H25 y0).  Simpl.  Rewrite y.  Split.  Split with x.
  Split with (Snd (BDDneg_2 (bs,(share,counter)) l n0)).  Split with (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)).
  Reflexivity.  Reflexivity.  Intros.  Apply (proj2 ? ? (H27 a l0 r0 x0)).
  Apply H16.  Apply H9.  Exact H29.  Apply BDDmake_semantics.  Assumption.
  Assumption.  Assumption.  Assumption.  Assumption.  Intros.  Elim H5.  Intro.
  Rewrite H21 in H19.  Rewrite (proj1 ? ?  (bool_fun_of_BDD_semantics (Fst (BDDneg_2 (bs,(share,counter)) l n0)) H7)) in H19.
  Rewrite bool_fun_neg_zero in H19.  Rewrite H21 in H15.  Rewrite <- (proj1 ? ?  (proj2 ? ?  (bool_fun_of_BDD_semantics (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) BDDzero n0)) H15))) in H19.
  Cut (Snd (BDDneg_2 (Fst (BDDneg_2 (bs, (share,counter)) l n0)) BDDzero n0)) =BDDone.
  Intro.  Rewrite H21 in H20.  Rewrite H22 in H20.  Rewrite (config_OK_one (Fst (BDDneg_2 (Fst (BDDneg_2 (bs, (share,counter)) l n0)) BDDzero n0)) H15) in H20. 
  Discriminate H20.  Apply BDDunique with cfg:=(Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) BDDzero n0)).
  Assumption.  Rewrite H21 in H18.  Assumption.  Right.  Left.  Reflexivity.
  Assumption.  Intro.  Elim H21.  (Clear H21; Intro).  Rewrite H21 in H19.
  Rewrite (proj1 ? ?  (proj2 ? ?  (bool_fun_of_BDD_semantics (Fst (BDDneg_2 (bs,(share,counter)) l n0)) H7))) in H19.
  Rewrite bool_fun_neg_one in H19.  Rewrite H21 in H15.  Rewrite <- (proj1 ? ?  (bool_fun_of_BDD_semantics (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) BDDone n0)) H15)) in H19.
  Cut (Snd (BDDneg_2 (Fst (BDDneg_2 (bs, (share,counter)) l n0)) BDDone n0)) =BDDzero.
  Intro.  Rewrite H21 in H20.  Rewrite H22 in H20.  Rewrite (config_OK_zero (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) BDDone n0)) H15) in H20.  
  Discriminate H20.  Apply BDDunique with cfg:=(Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) BDDone n0)).
  Assumption.  Rewrite H21 in H18.  Assumption.  (Left; Reflexivity).
  Assumption.  Intro.  Unfold in_dom in H22.  Elim (option_sum ?  (MapGet BDDvar*ad*ad (Fst (bs,(share,counter))) r)).
  Intro.  (Elim y0; Clear y0; Intro).  (Elim x0; Clear x0; Intro; Intro).
  (Elim y1; Clear y1; Intros).  Cut (is_internal_node (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r).
  Intro.  Cut (var (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r) =(var (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0)) (Snd (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))).
  Intro.  Cut (var (bs,(share, counter)) r) =(var (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r).
  Intro.  Rewrite <- H25 in H24.  Cut (BDDcompare (var (bs,(share,counter)) (high (bs, (share,counter)) node)) (var (bs,(share,counter)) node))=INFERIEUR.
  Unfold var high low.  Simpl.  Rewrite y.  Simpl in y3.  Rewrite y3.  Unfold var in H24.
  Simpl in H24.  Rewrite y3 in H24.  Rewrite H20 in H24.  Rewrite H24.  Trivial.
  Apply BDDvar_ordered_high.  Assumption.  Unfold is_internal_node.
  (Split with x; Split with l; Split with r; Assumption).  Unfold high.  (Simpl;
  Rewrite y).  (Split with y0; Split with y1; Split with y2; Assumption).
  Unfold var.  Rewrite y3.  Cut (MapGet BDDvar*ad*ad (Fst (Fst (BDDneg_2 (bs, (share,counter)) l n0))) r) =(Some (y0,(y1,y2))).
  Intro.  Rewrite H25.  Reflexivity.  Apply H9.  Assumption.  Exact (proj2 ? ? (H17 H23)).
  Unfold is_internal_node.  Split with y0.  Split with y1.  Split with y2.  Rewrite (H9 y0 y1 y2 r).
  Reflexivity.  Assumption.  Intro.  (Rewrite y0 in H22; Discriminate).  Intros.
  Elim (option_sum ? (MapGet ? (Fst (bs,(share, counter))) l)).  Intros.
  Elim y0.  Clear y0.  Intro.  (Elim x0; Clear x0; Intro; Intro).  (Elim y1; Clear y1; Intros).
  Cut (is_internal_node (Fst (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (bs,(share,counter)) l n0))) /\(var (bs,(share,counter)) l) =(var (Fst (BDDneg_2 (bs,(share,counter)) l n0)) (Snd (BDDneg_2 (bs,(share,counter)) l n0))).
  Intros.  (Elim H21; Clear H21; Intros).  Elim (option_sum ?  (MapGet ? (Fst (Fst (BDDneg_2 (bs,(share, counter)) l n0))) (Snd (BDDneg_2 (bs,(share,counter)) l n0)))).
  Intros.  (Elim y4; Clear y4; Intro).  (Elim x0; Clear x0; Intro; Intro).  (Elim y5; Clear y5; Intros).
  Unfold var in H22.  Rewrite y3 in H22.  Rewrite y7 in H22.
  Cut (MapGet BDDvar*ad*ad (Fst (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share, counter)) l n0)) r n0))) (Snd (BDDneg_2 (bs,(share,counter)) l n0))) =(Some BDDvar*ad*ad (y4,(y5,y6))).
  Intros.  Rewrite H20 in H23.  Injection H23.  Intros.  Rewrite H26.  Rewrite <- H22.
  Cut (BDDcompare (var (bs,(share,counter)) (low (bs,(share,counter)) node)) (var (bs,(share,counter)) node))=INFERIEUR.
  Unfold var high low.  Simpl.  Rewrite y.  Simpl in y3.  Rewrite y3.  Trivial. 
  Apply BDDvar_ordered_low.  Assumption.  Unfold is_internal_node.  (Split with x; Split with l; Split with r).
  Assumption.  Unfold low is_internal_node.  Simpl.  Rewrite y.  (Split with y0; Split with y1; Split with y2).
  Exact y3.  Apply H16.  Assumption.  Intro.  Unfold is_internal_node in H21.
  Rewrite y4 in H21.  Inversion H21.  Inversion H23.  Inversion H24.  Discriminate H25.
  Apply H10.  Unfold is_internal_node.  (Split with y0; Split with y1; Split with y2; Assumption).
  Intro.  Elim H6.  Intro.  Cut (Snd (BDDneg_2 (bs,(share,counter)) l n0))=BDDone.
  Intro.  Rewrite H22 in H20.  Unfold BDDconfig_OK in H15.  Cut (MapGet ?  (Fst
   (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))) BDDone)=(None).
  Intros.  Rewrite H23 in H20.  Discriminate H20.  Apply config_OK_one.  Assumption.
  Apply BDDunique with cfg:=(Fst (BDDneg_2 (bs,(share,counter)) l n0)).  Assumption.
  Assumption.  (Right; Left; Reflexivity).  Rewrite (proj1 ? ?  (proj2 ? ?
    (bool_fun_of_BDD_semantics (Fst (BDDneg_2 (bs,(share,counter)) l n0)) H7))).
  Rewrite <- bool_fun_neg_zero.  Rewrite <- (proj1 ? ?  (bool_fun_of_BDD_semantics (bs,(share,counter)) H1)).
  (Rewrite <- H21; Exact H12).  Intro.  (Elim H21; Clear H21).  Intro.
  Cut (Snd (BDDneg_2 (bs,(share,counter)) l n0))=BDDzero.  Intro.  Rewrite H22 in H20.
  Unfold BDDconfig_OK in H15.  Cut (MapGet ?  (Fst (Fst (BDDneg_2 (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r n0))) BDDzero)=(None).
  Intros.  Rewrite H23 in H20.  Discriminate H20.  Apply config_OK_zero.  Assumption.
  Apply BDDunique with cfg:=(Fst (BDDneg_2 (bs,(share,counter)) l n0)).  Assumption.
  Assumption.  (Left; Reflexivity).  Rewrite (proj1 ? ?  (bool_fun_of_BDD_semantics (Fst (BDDneg_2 (bs,(share,counter)) l n0)) H7)).
  Rewrite <- bool_fun_neg_one.  Rewrite <- (proj1 ? ?  (proj2 ? ?  (bool_fun_of_BDD_semantics (bs,(share,counter)) H1))).
  (Rewrite <- H21; Exact H12).  Unfold in_dom.  Rewrite y0.  (Intro; Discriminate).
  Assumption.  Elim H11.  Intro.  Rewrite H20.  (Left; Reflexivity).  Intro.
  (Elim H20; Intro).  (Rewrite H21; Right; Left; Reflexivity). 
  Elim (option_sum ?  (MapGet ? (Fst (Fst (BDDneg_2 (bs,(share,counter)) l n0))) (Snd (BDDneg_2 (bs,(share,counter)) l n0)))).
  Intro.  (Elim y0; Clear y0; Intro).  (Elim x0; Clear x0; Intro; Intro).  (Elim y1; Clear y1; Intros).
  Right.  Right.  Unfold in_dom.  Rewrite (H16 y0 y1 y2 (Snd (BDDneg_2 (bs,(share,counter)) l n0))).
  Reflexivity.  Assumption.  Intro.  Unfold in_dom in H21.  (Rewrite y0 in H21; Discriminate).
  Apply H0.  Unfold lt.  Apply le_n.  Assumption.  Assumption.  Assumption.  Intro.
  Apply lt_trans_1 with y:=(nat_of_N (var (bs,(share,counter)) node)).
  Apply BDDcompare_lt.  Cut (BDDcompare (var (bs,(share,counter)) (high (bs,(share,counter)) node)) (var (bs,(share,counter)) node))=INFERIEUR.
  Cut (var (bs,(share,counter)) r) =(var (Fst (BDDneg_2 (bs,(share,counter)) l n0)) r).
  Intro.  Unfold high.  Simpl.  Rewrite y.  Rewrite H14.  Trivial.  Unfold is_internal_node in H13.
  Inversion H13.  Inversion H14.  Inversion H15.  Elim H5.  Intro.  Rewrite H17 in H16.
  Rewrite (config_OK_zero (Fst (BDDneg_2 (bs,(share,counter)) l n0))) in H16.  Discriminate H16.
  Assumption.  Intro.  (Elim H17; Intro).  Rewrite H18 in H16.  Rewrite (config_OK_one (Fst (BDDneg_2 (bs,(share,counter)) l n0))) in H16.
  Discriminate H16.  Assumption.  Elim (option_sum ? (MapGet ? (Fst (bs,(share,counter))) r)).
  Intro.  (Elim y0; Clear y0; Intro).  (Elim x3; Clear x3; Intro).  Intro.
  (Elim y1; Clear y1; Intros).  Unfold var.  Rewrite y3.  Rewrite (H9 y0 y1 y2 r).
  Reflexivity.  Assumption.  Intro.  Unfold in_dom in H18.  (Rewrite y0 in H18; Discriminate).
  Apply BDDvar_ordered_high.  Assumption.  Unfold is_internal_node.  (Split with x; Split with l; Split with r; Assumption).
  Unfold high.  Simpl.  Rewrite y.  Unfold is_internal_node in H13.  (Inversion H13; Inversion H14; Inversion H15).
  (Elim H5; Intro).  Rewrite H17 in H16.  Rewrite (config_OK_zero (Fst (BDDneg_2 (bs,(share,counter)) l n0))) in H16.
  Discriminate H16.  Assumption.  (Elim H17; Intro).  Rewrite H18 in H16.  Rewrite (config_OK_one (Fst (BDDneg_2 (bs,(share,counter)) l n0))) in H16.
  Discriminate H16.  Assumption.  Unfold in_dom in H18.  Unfold is_internal_node.
  Elim (option_sum ? (MapGet BDDvar*ad*ad (Fst (bs,(share,counter))) r)).  Intros.
  (Elim y0; Intro).  (Elim x3; Intro; Intro).  (Elim y2; Intros).  (Split with y1; Split with y3; Split with y4; Assumption).
  Intro.  (Rewrite y0 in H18; Discriminate).  Apply H3.  Unfold is_internal_node.
  (Split with x; Split with l; Split with r; Exact y).  (Elim H5; Intro).  (Rewrite H13; Left; Reflexivity).
  (Elim H13; Intro).  (Rewrite H14; Right; Left; Reflexivity).  Unfold in_dom in H14.
  Elim (option_sum ? (MapGet BDDvar*ad*ad (Fst (bs,(share,counter))) r)).  Intro.
  (Elim y0; Intro).  (Elim x0; Intro; Intro).  (Elim y2; Intros).  (Right; Right).
  Unfold in_dom.  Rewrite (H9 y1 y3 y4 r y5).  Reflexivity.  Intro.  (Rewrite y0 in H14; Discriminate).
  Apply H0.  Unfold lt.  Apply le_n.  Assumption.  Assumption.  Intro.  Apply lt_trans_1 with y:=(nat_of_N (var (bs,(share,counter)) node)).
  Cut (lt (nat_of_N (var (bs,(share,counter)) (low (bs,(share,counter)) node))) (nat_of_N (var (bs,(share,counter)) node))).
  Unfold low.  Simpl.  Rewrite y.  Trivial.  Apply BDDcompare_lt.  Apply BDDvar_ordered_low.
  Assumption.  Unfold is_internal_node.  (Split with x; Split with l; Split with r; Exact y).
  Unfold low.  (Simpl; Rewrite y; Assumption).  Apply H3.  Unfold is_internal_node.
  (Split with x; Split with l; Split with r; Assumption).  Intro.  Apply lt_trans_1 with y:=(nat_of_N (var (bs,(share,counter)) node)).
  Cut (lt (nat_of_N (var (bs,(share,counter)) (low (bs,(share,counter)) node))) (nat_of_N (var (bs,(share,counter)) node))).
  Unfold low.  Simpl.  Rewrite y.  Trivial.  Apply BDDcompare_lt.  Apply BDDvar_ordered_low.
  Assumption.  Unfold is_internal_node.  (Split with x; Split with l; Split with r; Exact y).
  Unfold low.  (Simpl; Rewrite y; Assumption).  Apply H3.  Unfold is_internal_node.
  (Split with x; Split with l; Split with r; Assumption).  Elim H1.  Intros.  Elim H5.
  Intros.  Cut (BDD_OK bs node).  Unfold BDD_OK.  Unfold BDDordered.  Simpl in y.  Rewrite y.
  Intro.  Cut node=BDDzero \/node=BDDone \/(EX x0:BDDvar | (EX l0:BDDvar | (EX r0:BDDvar | (MapGet ? bs node)=(Some (x0,(l0,r0))) /\(BDDcompare x0 (ad_S x))=INFERIEUR /\(Neqb l0 r0)=false /\(BDDbounded bs l0 x0)/\(BDDbounded bs r0 x0)))).
  Intro.  (Elim H10; Intro).  (Rewrite H11 in y; Rewrite y in H7; Discriminate).
  (Elim H11; Intro).  (Rewrite H12 in y; Rewrite (proj1 ? ? H8) in y; Discriminate).  
  Inversion H12.  Inversion H13.  Inversion H14.  Inversion H15.  Rewrite y in H16.
  Injection H16.  Intros.  Rewrite <- H18 in H17.  Rewrite <- H19 in H17.  Unfold config_node_OK.  Apply BDDbounded_node_OK with n:=x0.
  Exact (proj2 ? ? (proj2 ? ? (proj2 ? ? H17))).  Apply BDDbounded_lemma.  Assumption.
  Apply (proj2 ? ? H8).  Unfold in_dom.  Simpl in y.  Rewrite y.  Reflexivity.  Elim H1.  Intros.
  Elim H5.  Intros.  Cut (BDD_OK bs node).  Unfold BDD_OK.  Unfold BDDordered.
  Simpl in y.  Rewrite y.  Intro.  Cut node=BDDzero \/node=BDDone \/(EX x0:BDDvar | (EX l0:BDDvar | (EX r0:BDDvar | (MapGet ? bs node)=(Some (x0,(l0,r0))) /\(BDDcompare x0 (ad_S x))=INFERIEUR /\(Neqb l0 r0)=false /\(BDDbounded bs l0 x0)/\(BDDbounded bs r0 x0)))).
  Intro.  (Elim H10; Intro).  (Rewrite H11 in y; Rewrite y in H7; Discriminate).
  (Elim H11; Intro).  (Rewrite H12 in y; Rewrite (proj1 ? ? H8) in y; Discriminate).  
  Inversion H12.  Inversion H13.  Inversion H14.  Inversion H15.  Rewrite y in H16.
  Injection H16.  Intros.  Rewrite <- H18 in H17.  Rewrite <- H19 in H17.  Unfold config_node_OK.
  Apply BDDbounded_node_OK with n:=x0.  Exact (proj1 ? ? (proj2 ? ? (proj2 ? ? H17))).
  Apply BDDbounded_lemma.  Assumption.  Apply (proj2 ? ? H8).  Unfold in_dom.
  Simpl in y.  Rewrite y.  Reflexivity.  Intro.  Unfold in_dom in H4.  Rewrite y in H4.
  Discriminate H4.
Qed.
*)

(*
Fixpoint BDDneg_1 [cfg:BDDconfig; node:ad; memo:BDDneg_memo; bound:nat]
       : BDDconfig*ad*BDDneg_memo :=
let (cfg',node'_memo') =
Cases (BDDneg_memo_lookup memo node) of
    (Some node') => (cfg,(node',memo))
  | None =>
    Cases (MapGet ? (Fst cfg) node) of
        None => if (Neqb node BDDzero) then (cfg,(BDDone,memo)) else
                        (cfg,(BDDzero,memo))
      | (Some (x,(l,r))) => 
         Cases bound of
             O => ( * Error * ) (initBDDconfig, (BDDzero, (newMap ad)))
           | (S bound') =>
              let (cfgl,nodel_memol) = (BDDneg_1 cfg l memo bound') in
              let (nodel,memol) = nodel_memol in
              let (cfgr,noder_memor) = (BDDneg_1 cfgl r memol bound') in
              let (noder,memor) = noder_memor in
              let (cfg'', node'') = (BDDmake cfgr x nodel noder) in
              (cfg'',(node'',memor)) 
         end
    end
end in
let (node',memo') = node'_memo' in
(cfg',(node',(BDDneg_memo_put memo' node node'))).

Lemma BDDneg_1_looksup_memo :
  (cfg:BDDconfig)(node1,node2:ad)(memo:BDDneg_memo)(bound:nat)
  (BDDneg_memo_lookup memo node1)=(Some node2) ->
    (Fst (Snd (BDDneg_1 cfg node1 memo bound)))=node2.
Proof.
  Intros.  Unfold BDDneg_1.  Elim bound.  Rewrite H.  Simpl.  Trivial.
  Rewrite H.  Intros.  Simpl.  Trivial.
Qed.

Lemma BDDneg_1_zero : (cfg:BDDconfig)(memo:BDDneg_memo)(bound:nat)
  (BDDconfig_OK cfg) ->
  (BDDneg_memo_OK cfg memo) ->
  (bool_fun_of_BDD cfg (Fst (Snd (BDDneg_1 cfg BDDzero memo bound))))
   =bool_fun_one.
Proof.
  Intros.  Elim (option_sum ? (BDDneg_memo_lookup memo BDDzero)).  Intros.
  Elim y.  Clear y.  Intros.  Elim bound.  Simpl.  Rewrite y.  Simpl.
  Cut (bool_fun_of_BDD cfg x) =(bool_fun_neg (bool_fun_of_BDD cfg BDDzero)).
  Intros.  Rewrite H1.  Rewrite (proj1 ? ? (bool_fun_of_BDD_semantics cfg H)).
  Exact bool_fun_neg_zero.  Exact (proj1 ? ? (proj2 ? ? (H0 BDDzero x y))).
  Intros.  Simpl.  Rewrite y.  Simpl.
  Cut (bool_fun_of_BDD cfg x) =(bool_fun_neg (bool_fun_of_BDD cfg BDDzero)).
  Intros.  Rewrite H2.  Rewrite (proj1 ? ? (bool_fun_of_BDD_semantics cfg H)).
  Exact bool_fun_neg_zero.  Exact (proj1 ? ? (proj2 ? ? (H0 BDDzero x y))).
  Intros.  Elim bound.  Simpl.  Rewrite y.
  Cut (MapGet BDDvar*ad*ad (Fst cfg) BDDzero)=(None).  Intro.  Rewrite H1.
  Simpl.  Exact (proj1 ? ? (proj2 ? ? (bool_fun_of_BDD_semantics cfg H))).
  Unfold BDDconfig_OK in H.  Apply config_OK_zero.  Assumption.  Intros.
  Unfold BDDneg_1.  Rewrite y.  Rewrite (config_OK_zero cfg H).  Simpl.
  Exact (proj1 ? ? (proj2 ? ? (bool_fun_of_BDD_semantics cfg H))).
Qed.

Lemma BDDneg_1_one : (cfg:BDDconfig)(memo:BDDneg_memo)(bound:nat)
  (BDDconfig_OK cfg) ->
  (BDDneg_memo_OK cfg memo) ->
  (bool_fun_of_BDD cfg (Fst (Snd (BDDneg_1 cfg BDDone memo bound))))
   =bool_fun_zero.
Proof.
  Intros.  Elim (option_sum ? (BDDneg_memo_lookup memo BDDone)).  Intros.
  Elim y.  Clear y.  Intros.  Elim bound.  Simpl.  Rewrite y.  Simpl.
  Cut (bool_fun_of_BDD cfg x)=(bool_fun_neg (bool_fun_of_BDD cfg BDDone)).
  Intros.  Rewrite H1.
  Rewrite (proj1 ? ? (proj2 ? ? (bool_fun_of_BDD_semantics cfg H))).
  Exact bool_fun_neg_one.  Intros.  Simpl.  Simpl.
  Cut (bool_fun_of_BDD cfg x)=(bool_fun_neg (bool_fun_of_BDD cfg BDDone)).
  Intros.  Rewrite H1.
  Rewrite (proj1 ? ? (proj2 ? ? (bool_fun_of_BDD_semantics cfg H))).
  Exact bool_fun_neg_one.  Exact (proj1 ? ? (proj2 ? ? (H0 BDDone x y))).
  Intros.  Elim bound.  Simpl.  Rewrite y.
  Cut (MapGet BDDvar*ad*ad (Fst cfg) BDDone)=(None).  Intro.  Simpl.
  Rewrite (proj1 ? ? (proj2 ? ? (H0 BDDone x y))).
  Rewrite (proj1 ? ? (proj2 ? ? (bool_fun_of_BDD_semantics cfg H))).
  Exact bool_fun_neg_one.  Apply config_OK_one.  Assumption.  Intro.  Auto.  
  Intro.  Unfold BDDneg_1.  Elim bound.  Rewrite y.  Simpl.
  Cut (MapGet BDDvar*ad*ad (Fst cfg) BDDone)=(None).  Intro.  Rewrite H1.
  Simpl.  Exact (proj1 ? ? (bool_fun_of_BDD_semantics cfg H)).  
  Apply config_OK_one.  Assumption.  Intros.  Unfold BDDneg_1.  Rewrite y.
  Rewrite (config_OK_one cfg H).  Simpl.
  Exact (proj1 ? ? (bool_fun_of_BDD_semantics cfg H)).
(*
  Intros.  Elim (option_sum ? (BDDneg_memo_lookup memo BDDone)).  Intros.
  Elim y.  Clear y.  Intros.  Elim bound.  Simpl.  Rewrite y.  Simpl.
  Cut (bool_fun_of_BDD cfg x)=(bool_fun_neg (bool_fun_of_BDD cfg BDDone)).
  Intros.  Rewrite H1.
  Rewrite (proj1 ? ? (proj2 ? ? (bool_fun_of_BDD_semantics cfg H))).
  Exact bool_fun_neg_one.  Exact (proj2 ? ? (H0 BDDzero x y)).  Intros.  Simpl.
  Rewrite y.  Simpl.
  Cut (bool_fun_of_BDD cfg x)=(bool_fun_neg (bool_fun_of_BDD cfg BDDone)).
  Intros.  Rewrite H1.
  Rewrite (proj1 ? ? (proj2 ? ? (bool_fun_of_BDD_semantics cfg H))).
  Exact bool_fun_neg_one.  Exact (proj2 ? ? (H0 BDDone x y)).  Intros.
  Elim bound.  Simpl.  Rewrite y.
  Cut (MapGet BDDvar*ad*ad (Fst cfg) BDDone)=(None).  Intro.

  Rewrite H1.  Simpl.  Exact (proj1 ? ? (bool_fun_of_BDD_semantics cfg H)).
  Unfold BDDconfig_OK in H.  Apply config_OK_one.  Assumption.  Intros.
  Unfold BDDneg_1.  Rewrite y.  Rewrite (config_OK_one cfg H).  Simpl.
  Exact (proj1 ? ? (bool_fun_of_BDD_semantics cfg H)).
*)
Qed.

(*
Lemma BDDneg_1_internal_node :
  (bound:nat)(cfg:BDDconfig)(node:ad)(memo:BDDneg_memo)
  (BDDconfig_OK cfg) ->
  (BDDneg_memo_OK cfg memo) ->
  (config_node_OK cfg node) ->
  (lt (nat_of_N (var cfg node)) bound) ->
  (BDDconfig_OK (Fst (BDDneg_1 cfg node memo bound)))
  /\ (BDDneg_memo_OK (Fst (BDDneg_1 cfg node memo bound))
                     (Snd (Snd (BDDneg_1 cfg node memo bound))))
  /\ ( (x:BDDvar)(l,r,a:ad)
       (MapGet ? (Fst cfg) a)=(Some (x,(l,r))) ->
       (MapGet ? (Fst (Fst (BDDneg_1 cfg node memo bound))) a)=
         (Some (x,(l,r)))
     )
  /\ ( (is_internal_node cfg node) ->
       (is_internal_node (Fst (BDDneg_1 cfg node memo bound))
                         (Fst (Snd (BDDneg_1 cfg node memo bound))))
       /\ (var cfg node)=(var (Fst (BDDneg_1 cfg node memo bound))
                         (Fst (Snd (BDDneg_1 cfg node memo bound)))) )
  /\ (config_node_OK (Fst (BDDneg_1 cfg node memo bound))
                     (Fst (Snd (BDDneg_1 cfg node memo bound))))
  /\ (bool_fun_of_BDD (Fst (BDDneg_1 cfg node memo bound))
                      (Fst (Snd (BDDneg_1 cfg node memo bound))))
       =(bool_fun_neg (bool_fun_of_BDD cfg node)).
Proof.

Qed.
*)

Definition BDDneg := [cfg:BDDconfig; node:ad]
   Cases (MapGet ? (Fst cfg) node) of
       None => if (Neqb node BDDzero) then (cfg,BDDone) else (cfg,BDDone)
     | (Some (x,(l,r))) =>
          let (cfg',node'_memo) =
               (BDDneg_1 cfg node (newMap ad) (S (nat_of_N x))) in
          let (node',memo) = node'_memo in
           (cfg',node')
   end.
*)