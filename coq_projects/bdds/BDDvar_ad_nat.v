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


(******** Copied variables upto bdd5_2.v *)

Require Import Bool.
Require Import Sumbool.
Require Import Arith.
Require Import ZArith NArith Nnat Ndec Ndigits.
From IntMap Require Import Allmaps.
Definition BDDzero := N0.
Definition BDDone := Npos 1.

  Definition BDDvar := ad.

  Definition BDDcompare (x y : BDDvar) :=
    match x, y with
    | N0, N0 => Datatypes.Eq
    | N0, Npos _ => Datatypes.Lt
    | Npos _, N0 => Datatypes.Gt
    | Npos p1, Npos p2 => Pcompare p1 p2 Datatypes.Eq
    end.

Definition BDDvar_eq := Neqb.

  Definition ad_S (a : ad) :=
    match a with
    | N0 => Npos 1
    | Npos p => Npos (Psucc p)
    end.

  Lemma ad_S_is_S : forall a : ad, nat_of_N (ad_S a) = S (nat_of_N a).
  Proof.
    simple induction a. reflexivity.
    simpl in |- *. unfold nat_of_P in |- *. intro p. exact (Pmult_nat_succ_morphism p 1).
  Qed.

Lemma lt_pred : forall x y : nat, x < y -> x <> 0 -> pred x < pred y.
Proof.
  simple induction x.  intros y H H0.  absurd (0 = 0).  assumption.  reflexivity.  intros n H y H0 H1.
  apply lt_pred.  assumption.
Qed.

Lemma O_N0 : forall x : ad, nat_of_N x = 0 -> x = N0.
Proof.
  cut (0 = nat_of_N N0).  intro H.  rewrite H.  intros x H0.  replace x with (N_of_nat (nat_of_N x)).
  replace N0 with (N_of_nat (nat_of_N N0)).  rewrite H0.  reflexivity.
  rewrite (N_of_nat_of_N N0).  reflexivity.  rewrite (N_of_nat_of_N x).
  reflexivity.  reflexivity.
Qed.
Lemma INFERIEUR_neq_O :
 forall x y : ad, BDDcompare x y = Datatypes.Lt -> y <> N0.
Proof.
  double induction x y.  simpl in |- *.  intro; discriminate.  unfold not in |- *; intros.
  discriminate.  simpl in |- *.  intros; discriminate.  unfold not in |- *; intros.  discriminate.
Qed.

 Lemma BDDcompare_trans :
  forall x y z : BDDvar,
  BDDcompare x y = Datatypes.Lt ->
  BDDcompare y z = Datatypes.Lt -> BDDcompare x z = Datatypes.Lt.
  Proof.
    double induction x y.  simpl in |- *.  intros z H H0.  discriminate H.  simpl in |- *.  intro p.
    simple induction z.  intros H H0.  discriminate H0.  trivial.  simpl in |- *.  intros p z H H0.
    discriminate H.  intro p.  intro p0.  simple induction z.  simpl in |- *.  trivial.  intro p1.
    simpl in |- *.  intros H H0.  cut (nat_of_P p0 < nat_of_P p).
    cut (nat_of_P p < nat_of_P p1).  intros H1 H2.
    apply nat_of_P_lt_Lt_compare_complement_morphism.  apply lt_trans with (m := nat_of_P p).
    assumption.  assumption.  apply nat_of_P_lt_Lt_compare_morphism.  assumption.
    apply nat_of_P_lt_Lt_compare_morphism.  assumption.
  Qed.

  Lemma ad_S_le_then_le :
   forall x y : ad, Nleb (ad_S x) y = true -> Nleb x y = true.
  Proof.
    intros x y H.  cut (Nleb x (ad_S x) = true).  intro H0.
    apply Nleb_trans with (b := ad_S x).  assumption.  assumption.  unfold Nleb in |- *.
    apply leb_correct.  rewrite (ad_S_is_S x).  apply le_S.  apply le_n.
  Qed.

  Lemma le_then_le_S :
   forall x y : ad, Nleb x y = true -> Nleb x (ad_S y) = true.
  Proof.
    intros x y H.  cut (Nleb y (ad_S y) = true).  intro H0.  apply Nleb_trans with (b := y).
    assumption.  assumption.  unfold Nleb in |- *.  apply leb_correct.  rewrite (ad_S_is_S y).
    apply le_S.  apply le_n.
  Qed.

  Lemma ad_S_le_then_neq :
   forall x y : ad, Nleb (ad_S x) y = true -> Neqb x y = false.
  Proof.
    intros x y H.  cut (Neqb x y = true \/ Neqb x y = false).  intro H0.  elim H0.
    clear H0.  intro H0.  cut (x = y).  intro H1.  rewrite H1 in H.  unfold Nleb in H.
    rewrite (ad_S_is_S y) in H.
    cut (leb (S (nat_of_N y)) (nat_of_N y) = false).  rewrite H.  intro H2.
    discriminate H2.  cut (nat_of_N y < S (nat_of_N y)).  intro H2.
    apply leb_correct_conv.  assumption.  unfold lt in |- *.  trivial.
    apply Neqb_complete.  assumption.  trivial. elim (Neqb x y). auto. auto.
  Qed.

  Lemma BDDcompare_succ :
   forall a : BDDvar, BDDcompare a (ad_S a) = Datatypes.Lt.
  Proof.
    simple induction a.  simpl in |- *.  trivial.  simpl in |- *.  intro p.
    cut (nat_of_P p < nat_of_P (Psucc p)).  intro H.
    apply nat_of_P_lt_Lt_compare_complement_morphism.  assumption.
    cut (nat_of_P (Psucc p) = 1 + nat_of_P p).  intro H.  rewrite H.
    simpl in |- *.  unfold lt in |- *.  trivial.  unfold nat_of_P in |- *.  apply Pmult_nat_succ_morphism.
  Qed.

  Lemma BDDcompare_lt :
   forall x y : BDDvar,
   BDDcompare x y = Datatypes.Lt -> nat_of_N x < nat_of_N y.
  Proof.
    double induction x y.  simpl in |- *.  intro H.  discriminate.  simpl in |- *.  intros p H.
    cut (exists h : nat, nat_of_P p = S h).  intro H0.  inversion H0.  rewrite H1.
    apply lt_O_Sn.  apply ZL4.  simpl in |- *.  intros p H.  discriminate.  simpl in |- *.  intros p p0 H.
    apply nat_of_P_lt_Lt_compare_morphism.  assumption.
  Qed.


Lemma BDDlt_compare :
 forall x y : BDDvar,
 nat_of_N x < nat_of_N y -> BDDcompare x y = Datatypes.Lt.
Proof.
  double induction x y.  simpl in |- *.  intro H.  absurd (0 < 0).  apply lt_n_O.  assumption.
  simpl in |- *.  reflexivity.  simpl in |- *.  intro p.  cut (exists h : nat, nat_of_P p = S h).  intro H.
  inversion H.  rewrite H0.  intro H1.  absurd (S x0 < 0).  apply lt_n_O.
  assumption.  apply ZL4.  simpl in |- *.  intro p.  intros p0 H.  apply nat_of_P_lt_Lt_compare_complement_morphism.
  assumption.
Qed.

Lemma relation_sum :
 forall r : Datatypes.comparison,
 {r = Datatypes.Eq} + {r = Datatypes.Lt} + {r = Datatypes.Gt}.
Proof.
  intro r.  elim r.  left; left; reflexivity.  left; right; reflexivity.  right; reflexivity.
Qed.

Lemma BDD_EGAL_complete :
 forall x y : BDDvar, BDDcompare x y = Datatypes.Eq -> x = y.
Proof.
  double induction x y.  reflexivity.  simpl in |- *.  intros; discriminate.  simpl in |- *.
  intros; discriminate.  simpl in |- *.  intros p p0 H.  cut (p0 = p).  intro H0.  rewrite H0; reflexivity.
  apply Pcompare_Eq_eq.  assumption.
Qed.

  Lemma lt_trans_1 : forall x y z : nat, x < y -> y < S z -> x < z.
  Proof.
    intros x y z H H0.  unfold lt in H0.  unfold lt in H.  unfold lt in |- *.
    apply le_trans with (m := y).  assumption.  apply le_S_n.  assumption.
  Qed.

Lemma BDDcompare_sup_inf :
 forall x y : BDDvar,
 BDDcompare x y = Datatypes.Gt -> BDDcompare y x = Datatypes.Lt.
Proof.
  double induction x y.  simpl in |- *.  intro; discriminate.  simpl in |- *.  intro p.  intro; discriminate.
  simpl in |- *.  reflexivity.  unfold BDDcompare in |- *.  intros p p0 H.  apply ZC1.  assumption.
Qed.

  Lemma BDDcompare_1 :
   forall x y : BDDvar,
   BDDcompare x y = Datatypes.Lt ->
   BDDcompare (ad_S x) y = Datatypes.Lt \/ ad_S x = y.
  Proof.
    intros x y H.  elim (relation_sum (BDDcompare (ad_S x) y)).  intro y0.  elim y0; intro.
    right.  apply BDD_EGAL_complete.  assumption.  left; assumption.  intro y0.
    absurd (nat_of_N x < nat_of_N x).  apply lt_irrefl.  apply lt_trans_1 with (y := nat_of_N y).
    apply BDDcompare_lt.  assumption.  rewrite <- (ad_S_is_S x).  apply BDDcompare_lt.
    apply BDDcompare_sup_inf.  assumption.
  Qed.

Definition max (m n : nat) := if leb m n then n else m.

Lemma lt_max_1_2 :
 forall x1 y1 x2 y2 : nat, x1 < x2 -> y1 < y2 -> max x1 y1 < max x2 y2.
Proof.
  intros x1 y1 x2 y2 H H0.  unfold max in |- *.  elim (sumbool_of_bool (leb x2 y2)).  intro y.  rewrite y.
  elim (leb x1 y1).  assumption.  apply lt_le_trans with (m := x2).  assumption.
  apply leb_complete.  assumption.  intro y.  rewrite y.  elim (leb x1 y1).
  apply lt_trans with (m := y2).  assumption.  apply leb_complete_conv.  assumption.
  assumption.
Qed.

Lemma lt_max_2 :
 forall x1 y1 x2 y2 : nat, x1 < y2 -> y1 < y2 -> max x1 y1 < max x2 y2.
Proof.
  intros x1 y1 x2 y2 H H0.  unfold max in |- *.  elim (leb x1 y1).  elim (sumbool_of_bool (leb x2 y2)).
  intro y.  rewrite y.  assumption.  intro y.  rewrite y.  apply lt_trans with (m := y2).
  assumption.  apply leb_complete_conv.  assumption.  elim (sumbool_of_bool (leb x2 y2)).
  intro y.  rewrite y.  assumption.  intro y.  rewrite y.  apply lt_trans with (m := y2).
  assumption.  apply leb_complete_conv.  assumption.
Qed.

Lemma lt_max_12 :
 forall x1 y1 x2 y2 : nat, x1 < x2 -> y1 < x2 -> max x1 y1 < max x2 y2.
Proof.
  intros x1 y1 x2 y2 H H0.  unfold max in |- *.  elim (leb x1 y1).  elim (sumbool_of_bool (leb x2 y2)); intro y; rewrite y.
  apply lt_le_trans with (m := x2).  assumption.  apply leb_complete; assumption.
  assumption.  elim (sumbool_of_bool (leb x2 y2)).  intro y.  rewrite y.  apply lt_le_trans with (m := x2).
  assumption.  apply leb_complete; assumption.  intro y; rewrite y.  assumption.
Qed.

Lemma BDDcompare_eq :
 forall x y : BDDvar, BDDcompare x y = Datatypes.Eq -> x = y.
Proof.
  double induction x y.  reflexivity.  simpl in |- *.  intros; discriminate.  simpl in |- *.
  intros; discriminate.  simpl in |- *.  intros p p0 H.  cut (p0 = p).  intro H0.  rewrite H0; reflexivity.
  apply Pcompare_Eq_eq.  assumption.
Qed.
