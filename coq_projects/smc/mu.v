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
Require Import List.
Require Import myMap.
Require Import Wf_nat.
Require Import EqNat.
Require Import Peano_dec.
Require Import Ensembles.
Require Import Finite_sets.
Require Import Finite_sets_facts.
Require Import Image.

Require Import misc.
Require Import bool_fun.
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
Require Import Compare.

(* "two_power" and "zero_lt_pow" are copied from 
    contribs/BORDEAUX/Additions/two_power.v
    to avoid Requiring the contribution *)
Fixpoint two_power (m : nat) : nat :=
  match m with
  | O => 1
  | S n => 2 * two_power n
  end.
Lemma zero_lt_pow : forall a : nat, 0 < two_power a.
Proof.
 simple induction a; simpl in |- *.  auto.  intros.  apply lt_plus_trans; auto.
Qed.

Definition be_to_be_inc (f : bool_expr -> bool_expr) :=
  forall be1 be2 : bool_expr, be_le be1 be2 -> be_le (f be1) (f be2).

Definition fp (bef : bool_expr -> bool_expr) (be : bool_expr) :=
  be_eq be (bef be).

Definition lfp_be (bef : bool_expr -> bool_expr) (be1 be : bool_expr) :=
  fp bef be /\
  be_le be1 be /\
  (forall be' : bool_expr, fp bef be' -> be_le be1 be' -> be_le be be').

Definition lfp (bef : bool_expr -> bool_expr) (be : bool_expr) :=
  fp bef be /\ (forall be' : bool_expr, fp bef be' -> be_le be be').

Lemma lt_mn_minus : forall n m : nat, m < n -> 0 < n - m.
Proof.
  simple induction n.  intros.  elim (lt_n_O _ H).  intros.  simpl in |- *.  elim (O_or_S m).
  intro y.  inversion y.  rewrite <- H1.  apply H.  apply lt_S_n.  rewrite H1.
  assumption.  intro y.  rewrite <- y.  apply lt_O_Sn.
Qed.

Lemma le_minus_minus : forall m n : nat, n <= m -> n = m - (m - n).
Proof.
  simple induction m.  intros.  simpl in |- *.  symmetry  in |- *.  apply le_n_O_eq.  assumption.  
  intros.  elim (le_le_S_eq _ _ H0).  intros.  rewrite <- (minus_Sn_m n n0).
  simpl in |- *.  apply H.  apply le_S_n.  assumption.  apply le_S_n.  assumption.
  intros.  rewrite H1.  simpl in |- *.  rewrite <- (minus_n_n n).  reflexivity.
Qed.

Lemma minus_n_m_le_n : forall n m : nat, n - m <= n.
Proof.
  simple induction n.  simpl in |- *.  intros.  apply le_n.  intro.  intro.  intro.  elim m.
  apply le_n.  intros.  simpl in |- *.  apply le_S.  apply H.  
Qed.

Lemma le_minus_le : forall p n m : nat, n <= m -> p - m <= p - n.
Proof.
  simple induction p.  simpl in |- *.  intros.  apply le_O_n.  intros.  elim (O_or_S m).
  intro y.  inversion y.  rewrite <- H1.  simpl in |- *.  elim (O_or_S n0).  intro y0.
  inversion y0.  rewrite <- H2.  apply H.  apply le_S_n.  rewrite H1.
  rewrite H2.  assumption.  intro y0.  rewrite <- y0.  apply le_S.
  apply minus_n_m_le_n.  intro y.  rewrite <- y.  rewrite <- y in H0.
  rewrite (le_n_O_eq n0 H0).  apply le_n.  
Qed.

Section Nsec.
Variable N : nat.

Definition lxN := lx N.
Definition lx'N := lx' N.

Lemma Splus_nm : forall n m : nat, S (n + m) = S n + m.
Proof.
  reflexivity.
Qed.

Lemma empty_map_card :
 forall (A : Set) (m : Map A),
 (forall x : ad, in_dom _ x m = false) -> MapCard _ m = 0.
Proof.
  simple induction m.  reflexivity.  intros.  cut (in_dom _ a (M1 _ a a0) = false).
  unfold in_dom in |- *.  simpl in |- *.  rewrite (Neqb_correct a).  intro.  discriminate.
  apply H.  intros.  simpl in |- *.  unfold in_dom in H1.  rewrite H.  rewrite H0.
  reflexivity.  intro.
  cut
   (match MapGet A (M2 A m0 m1) (Ndouble_plus_one x) with
    | None => false
    | Some _ => true
    end = false).
  rewrite
   (MapGet_M2_bit_0_1 A (Ndouble_plus_one x) (Ndouble_plus_one_bit0 x) m0
      m1).
  unfold in_dom in |- *.  rewrite (Ndouble_plus_one_div2 x).  trivial.  apply H1.
  intro.  cut
   (match MapGet A (M2 A m0 m1) (Ndouble x) with
    | None => false
    | Some _ => true
    end = false).
  rewrite (MapGet_M2_bit_0_0 A (Ndouble x) (Ndouble_bit0 x) m0 m1).
  unfold in_dom in |- *.  rewrite (Ndouble_div2 x).  trivial.  apply H1.
Qed.

Fixpoint Map_eq (m1 m2 : Map unit) {struct m2} : bool :=
  match m1, m2 with
  | M0, M0 => true
  | M1 a1 _, M1 a2 _ => Neqb a1 a2
  | M2 m1 m1', M2 m2 m2' => Map_eq m1 m2 && Map_eq m1' m2'
  | _, _ => false
  end.

Lemma Map_eq_complete :
 forall m1 m2 : Map unit, Map_eq m1 m2 = true -> m1 = m2.
Proof.
  double induction m1 m2.  reflexivity.  simpl in |- *.  intros; discriminate.  simpl in |- *.
  intros; discriminate.  simpl in |- *.  intros; discriminate.  simpl in |- *.  intros.
  elim a0.  elim a2.  rewrite (Neqb_complete a1 a).  reflexivity.  assumption.
  simpl in |- *.  intros; discriminate.  simpl in |- *.  intros; discriminate.  simpl in |- *.
  intros; discriminate.  simpl in |- *.  intros.  elim (andb_prop _ _ H3).  intros.
  rewrite (H1 _ H4).  rewrite (H2 _ H5).  reflexivity.  
Qed.

Lemma Map_eq_correct : forall m : Map unit, Map_eq m m = true.
Proof.
  simple induction m.  reflexivity.  simpl in |- *.  intros.  apply Neqb_correct.  simpl in |- *.
  intros.  rewrite H.  rewrite H0.  reflexivity.  
Qed.

Lemma Map_eq_dec : forall m1 m2 : Map unit, m1 = m2 \/ m1 <> m2.
Proof.
  intros.  elim (sumbool_of_bool (Map_eq m1 m2)).  intros y.  left.
  apply Map_eq_complete.  assumption.  intro y.  right.  unfold not in |- *; intro.
  rewrite H in y.  rewrite (Map_eq_correct m2) in y.  discriminate.  
Qed.

Section Intervals.

Variable L U : nat.
Definition nat_lu (n : nat) := leb L n && leb (S n) U.
Definition var_lu (x : ad) :=
  leb L (nat_of_N x) && leb (S (nat_of_N x)) U.
Definition var_env_eq (e1 e2 : var_env) :=
  forall x : BDDvar, var_lu x = true -> e1 x = e2 x.

Section Sequence.
  Variable A : Set.
  Variable A_eq : A -> A -> Prop.
  Definition seq := nat -> A.
  Definition seq_eq (s1 s2 : seq) :=
    forall n : nat, nat_lu n = true -> A_eq (s1 n) (s2 n).
  Definition seq_inj (s : seq) :=
    forall i j : nat,
    nat_lu i = true -> nat_lu j = true -> A_eq (s i) (s j) -> i = j.
  Definition seq_surj (s : seq) :=
    forall a : A, exists i : nat, nat_lu i = true /\ A_eq (s i) a.
End Sequence.

Lemma var_lu_nat_lu :
 forall x : ad, var_lu x = true -> nat_lu (nat_of_N x) = true.
Proof.
  trivial.
Qed.

Lemma nat_lu_var_lu :
 forall n : nat, nat_lu n = true -> var_lu (N_of_nat n) = true.
Proof.
  unfold var_lu, nat_lu in |- *.  intro.  rewrite (nat_of_N_of_nat n).  trivial.
Qed.

Lemma eval_be_independent :
 forall ve1 ve2 : var_env',
 seq_eq _ (eq (A:=_)) ve1 ve2 ->
 forall be : bool_expr, be_ok var_lu be -> eval_be' be ve1 = eval_be' be ve2.
Proof.
  unfold seq_eq, eval_be' in |- *.  intros ve1 ve2 H.  simple induction be.  trivial.
  trivial.  simpl in |- *.  unfold bool_fun_var in |- *.  unfold var_env'_to_env in |- *.  intros.
  apply H.  apply var_lu_nat_lu.  apply var_ok_inv.  assumption.  intros.
  simpl in |- *.  unfold bool_fun_neg in |- *.
  replace (bool_fun_of_bool_expr b (var_env'_to_env ve2)) with
   (bool_fun_of_bool_expr b (var_env'_to_env ve1)).
  reflexivity.  apply H0.  apply neg_ok_inv.  assumption.  
  simpl in |- *.  unfold bool_fun_or in |- *.  intros.
  replace (bool_fun_of_bool_expr b (var_env'_to_env ve2)) with
   (bool_fun_of_bool_expr b (var_env'_to_env ve1)).
  replace (bool_fun_of_bool_expr b0 (var_env'_to_env ve2)) with
   (bool_fun_of_bool_expr b0 (var_env'_to_env ve1)).
  reflexivity.  apply H1.  exact (proj2 (or_ok_inv _ _ _ H2)).
  apply H0.  exact (proj1 (or_ok_inv _ _ _ H2)).
  simpl in |- *.  unfold bool_fun_and in |- *.  intros.
  replace (bool_fun_of_bool_expr b (var_env'_to_env ve2)) with
   (bool_fun_of_bool_expr b (var_env'_to_env ve1)).
  replace (bool_fun_of_bool_expr b0 (var_env'_to_env ve2)) with
   (bool_fun_of_bool_expr b0 (var_env'_to_env ve1)).
  reflexivity.  apply H1.  exact (proj2 (and_ok_inv _ _ _ H2)).
  apply H0.  exact (proj1 (and_ok_inv _ _ _ H2)).
  simpl in |- *.  unfold bool_fun_impl in |- *.  intros.
  replace (bool_fun_of_bool_expr b (var_env'_to_env ve2)) with
   (bool_fun_of_bool_expr b (var_env'_to_env ve1)).
  replace (bool_fun_of_bool_expr b0 (var_env'_to_env ve2)) with
   (bool_fun_of_bool_expr b0 (var_env'_to_env ve1)).
  reflexivity.  apply H1.  exact (proj2 (impl_ok_inv _ _ _ H2)).
  apply H0.  exact (proj1 (impl_ok_inv _ _ _ H2)).
  simpl in |- *.  unfold bool_fun_iff in |- *.  intros.
  replace (bool_fun_of_bool_expr b (var_env'_to_env ve2)) with
   (bool_fun_of_bool_expr b (var_env'_to_env ve1)).
  replace (bool_fun_of_bool_expr b0 (var_env'_to_env ve2)) with
   (bool_fun_of_bool_expr b0 (var_env'_to_env ve1)).
  reflexivity.  apply H1.  exact (proj2 (iff_ok_inv _ _ _ H2)).
  apply H0.  exact (proj1 (iff_ok_inv _ _ _ H2)).
Qed.

Definition Evar_env' : Ensemble var_env' :=
  fun ve : var_env' => forall n : nat, nat_lu n = false -> ve n = false.
Definition Evar_env'' : Ensemble var_env'' :=
  fun ve : var_env'' =>
  mapcanon _ ve /\ (forall x : ad, var_lu x = false -> in_dom _ x ve = false).

Lemma cardinal_Union :
 forall (U : Type) (X : Ensemble U) (m : nat),
 cardinal U X m ->
 forall (Y : Ensemble U) (n : nat),
 cardinal U Y n -> forall p : nat, cardinal U (Union U X Y) p -> p <= m + n.
Proof.
  intros U0 X m H.  elim H.  intros Y n.  rewrite (Empty_set_zero U0 Y).  simpl in |- *.
  intros.  rewrite (cardinal_is_functional _ _ _ H0 _ _ H1).  apply le_n.  
  reflexivity.  intros A n H0.  intros H1 x H2 Y n0 H3.  simpl in |- *.
  rewrite (Union_commutative U0 (Add U0 A x) Y).
  rewrite <- (Union_add U0 Y A x).  rewrite (Union_commutative U0 Y A).  intro.
  cut (exists q : nat, cardinal U0 (Union U0 A Y) q).  intro.  elim H4.
  intros q H5.  intros.  apply le_trans with (m := S q).
  apply card_Add_gen with (A := Union U0 A Y) (x := x).  assumption.  assumption.
  apply le_n_S.  apply H1 with (Y := Y).  assumption.  assumption.
  apply finite_cardinal.  apply Union_preserves_Finite.
  apply cardinal_finite with (n := n).  assumption.  
  apply cardinal_finite with (n := n0).  assumption.  
Qed.

End Intervals.

Definition Evar_env'ntoSn (U : nat) (ve : var_env') : var_env' :=
  fun n : nat => if beq_nat n U then true else ve n.
Definition Evar_env''ntoSn (U : nat) (ve : var_env'') : var_env'' :=
  MapPut _ ve (N_of_nat U) tt.

Lemma beq_Eq_true : forall m n : nat, beq_nat m n = true <-> eq_nat m n.
Proof.
  double induction m n; simpl in |- *.  split.  trivial.  reflexivity.  intros.  split.
  intro; discriminate.  intro.  elim H0.  split; intros.  discriminate.  
  elim H0.  intros.  apply H0.  
Qed.

Lemma beq_complete : forall m n : nat, beq_nat m n = true -> m = n.
Proof.
  intros.  apply eq_nat_eq.  apply (proj1 (beq_Eq_true _ _) H).
Qed.

Lemma beq_correct : forall n : nat, beq_nat n n = true.
Proof.
  simple induction n; simpl in |- *.  reflexivity.  trivial.  
Qed.

Lemma Evar_env'ntoSn_lemma :
 forall (L U : nat) (ve : var_env'),
 L <= U ->
 In _ (Evar_env' L U) ve -> In _ (Evar_env' L (S U)) (Evar_env'ntoSn U ve).
Proof.
  unfold In in |- *.  unfold Evar_env', Evar_env'ntoSn in |- *.  intros.  unfold nat_lu in H1.
  elim (andb_false_elim _ _ H1).  intro y.  cut (beq_nat n U = false).  intro.
  rewrite H2.  apply H0.  unfold nat_lu in |- *.  rewrite y.  reflexivity.  
  apply not_true_is_false.  unfold not in |- *; intro.
  rewrite (beq_complete _ _ H2) in y.  rewrite (leb_correct _ _ H) in y.
  discriminate.  simpl in |- *.  intro y.  cut (beq_nat n U = false).  intro.  rewrite H2.
  apply H0.  unfold nat_lu in |- *.  replace (leb (S n) U) with false.
  elim (leb L n).  reflexivity.  reflexivity.  symmetry  in |- *.
  apply not_true_is_false.  unfold not in |- *; intro.  cut (leb n U = true).  intro.
  rewrite H4 in y; discriminate.  apply leb_correct.  apply le_Sn_le.
  apply leb_complete.  assumption.  apply not_true_is_false.
  unfold not in |- *; intro.  rewrite (beq_complete _ _ H2) in y.
  rewrite (leb_correct U U) in y.  discriminate.  apply le_n.  
Qed.

Lemma Evar_env''ntoSn_lemma :
 forall (L U : nat) (ve : var_env''),
 L <= U ->
 In _ (Evar_env'' L U) ve -> In _ (Evar_env'' L (S U)) (Evar_env''ntoSn U ve).
Proof.
  unfold In in |- *.  unfold Evar_env'', Evar_env''ntoSn in |- *.  split.  apply MapPut_canon.
  exact (proj1 H0).  elim H0.  clear H0.  intro.  clear H0.  intros.
  unfold var_lu in H1.  elim (andb_false_elim _ _ H1).  intro y.
  cut (Neqb (N_of_nat U) x = false).  intro.  unfold in_dom in |- *.
  rewrite (MapPut_semantics unit ve (N_of_nat U) tt x).  rewrite H2.
  unfold in_dom in H0.  apply H0.  unfold var_lu in |- *.  rewrite y.  reflexivity.
  apply not_true_is_false.  unfold not in |- *; intro.
  cut (Nleb (N_of_nat L) (N_of_nat U) = true).
  rewrite (Neqb_complete _ _ H2).  unfold Nleb in |- *.  rewrite (nat_of_N_of_nat L).
  rewrite y.  intro; discriminate.  unfold Nleb in |- *.  rewrite (nat_of_N_of_nat L).
  rewrite (nat_of_N_of_nat U).  apply leb_correct.  assumption.
  simpl in |- *.  intro y.  unfold in_dom in |- *.
  rewrite (MapPut_semantics unit ve (N_of_nat U) tt x).
  cut (Neqb (N_of_nat U) x = false).  intro.  rewrite H2.  unfold in_dom in H0.
  apply H0.  unfold var_lu in |- *.  replace (leb (S (nat_of_N x)) U) with false.
  elim (leb L (nat_of_N x)).  reflexivity.  reflexivity.  symmetry  in |- *.
  apply not_true_is_false.  unfold not in |- *; intro.
  cut (leb (nat_of_N x) U = true).  intro.
  rewrite H4 in y; discriminate.  apply leb_correct.  apply le_Sn_le.
  apply leb_complete.  assumption.  apply not_true_is_false.
  unfold not in |- *; intro.  rewrite <- (Neqb_complete _ _ H2) in y.
  rewrite (nat_of_N_of_nat U) in y.
  rewrite (leb_correct U U) in y.  discriminate.  apply le_n.
Qed.

Section Evar_env''LULSU.

Variable L U : nat.
Definition Evar_env'LU : Ensemble var_env' := Evar_env' L U.
Definition Evar_env''LU : Ensemble var_env'' := Evar_env'' L U.
Definition Evar_env'LSU : Ensemble var_env' := Evar_env' L (S U).
Definition Evar_env''LSU : Ensemble var_env'' := Evar_env'' L (S U).
Definition f1 : var_env' -> var_env' := Evar_env'ntoSn U.
Definition f1' : var_env'' -> var_env'' := Evar_env''ntoSn U.
Definition imagef1 : Ensemble var_env' := Im _ _ Evar_env'LU f1.
Definition imagef1' : Ensemble var_env'' := Im _ _ Evar_env''LU f1'.
Definition f2 (x : var_env') : var_env' := x.
Definition f2' (x : var_env'') : var_env'' := x.
Definition imagef2 : Ensemble var_env' := Im _ _ Evar_env'LU f2.
Definition imagef2' : Ensemble var_env'' := Im _ _ Evar_env''LU f2'.
Definition imagef1orf2 : Ensemble var_env' := Union _ imagef1 imagef2.
Definition imagef1'orf2' : Ensemble var_env'' := Union _ imagef1' imagef2'.

Lemma var_env''M0 :
 forall ve : var_env'', U - L = 0 -> In _ Evar_env''LU ve -> ve = M0 _.
Proof.
  intros.  unfold In in H0.  unfold Evar_env''LU in H0.
  unfold Evar_env'' in H0.  apply (mapcanon_unique unit).  exact (proj1 H0).
  apply M0_canon.  unfold eqmap, eqm in |- *.  simpl in |- *.  intro.
  cut (in_dom unit a ve = false).  unfold in_dom in |- *.  elim (MapGet unit ve a).
  Focus 2.
  reflexivity.  intros.  discriminate.  apply (proj2 H0).  unfold var_lu in |- *.
  apply not_true_is_false.  unfold not in |- *; intro.  elim (andb_prop _ _ H1).
  intros.  cut (0 < U - L).  rewrite H.  intro.  exact (lt_n_O _ H4).
  apply lt_mn_minus.  unfold lt in |- *.  apply le_trans with (m := S (nat_of_N a)).
  apply le_n_S.  apply leb_complete.  assumption.  apply leb_complete.
  assumption.
Qed.

Lemma same_set_same_cardinal :
 forall (U : Type) (X Y : Ensemble U) (n m : nat),
 cardinal U X n -> cardinal U Y m -> Same_set U X Y -> n = m.
Proof.
  intros.  apply le_antisym.  apply incl_card_le with (X := X) (Y := Y).  assumption.
  assumption.  exact (proj1 H1).  apply incl_card_le with (X := Y) (Y := X).
  assumption.  assumption.  exact (proj2 H1).  
Qed.

Lemma same_set_finite :
 forall (U : Type) (X Y : Ensemble U),
 Finite U X -> Same_set U X Y -> Finite U Y.
Proof.
  intros.  elim (finite_cardinal _ X H).  intros.
  apply Finite_downward_closed with (A := X).  assumption.  exact (proj2 H0).
Qed.

Lemma singleton_add_empty :
 forall (U : Type) (x : U),
 Same_set _ (Singleton _ x) (Add _ (Empty_set _) x).
Proof.
  intros.  unfold Same_set in |- *.  split.  unfold Included in |- *.  intro.  unfold Add in |- *.
  intro.  inversion H.  apply Union_intror.  apply In_singleton.
  unfold Included in |- *.  intro.  unfold Add in |- *.  intro.  inversion H.  elim H0.  
  assumption.
Qed.

Lemma singleton_cardinal_one :
 forall (U : Type) (x : U), cardinal _ (Singleton _ x) 1.
Proof.
  intros.  cut (Finite _ (Singleton U0 x)).  intro.
  elim (finite_cardinal _ _ H).  intros.
  cut (cardinal _ (Add _ (Empty_set _) x) 1).  intro.
  rewrite
   (same_set_same_cardinal _ (Singleton U0 x) (Add U0 (Empty_set U0) x) x0 1)
    in H0.
  assumption.  assumption.  assumption.  apply singleton_add_empty.  
  apply card_add.  apply card_empty.  unfold not in |- *; intro.  elim H1.  
  apply Singleton_is_finite.
Qed.

Lemma M0inEvar_env'' : In (Map unit) Evar_env''LU (M0 unit).
Proof.
  unfold In in |- *.  unfold Evar_env''LU in |- *.  unfold Evar_env'' in |- *.  split.  apply M0_canon.
  intros.  unfold in_dom in |- *.  simpl in |- *.  reflexivity.  
Qed.

Lemma var_env''singleton :
 U - L = 0 -> Same_set _ Evar_env''LU (Singleton _ (M0 _)).
Proof.
  intros.  unfold Same_set in |- *.  split.  unfold Included in |- *.  intros.
  rewrite (var_env''M0 x).  apply In_singleton.  assumption.  assumption.
  unfold Included in |- *.  intros.  rewrite <- (Singleton_inv _ _ _ H0).
  exact M0inEvar_env''.
Qed.

Lemma var_env''cardinal_one : U - L = 0 -> cardinal _ Evar_env''LU 1.
Proof.
  intros.  cut (Finite _ Evar_env''LU).  intro.  elim (finite_cardinal _ _ H0).
  intros.  cut (Same_set _ Evar_env''LU (Singleton _ (M0 _))).  intro.
  rewrite <-
   (same_set_same_cardinal var_env'' Evar_env''LU
      (Singleton (Map unit) (M0 unit)) x 1).
  assumption.  assumption.  apply singleton_cardinal_one.  
  apply var_env''singleton.  assumption.  apply var_env''singleton.  assumption.
  apply (same_set_finite var_env'' (Singleton _ (M0 _)) Evar_env''LU).
  apply Singleton_is_finite.  split.  exact (proj2 (var_env''singleton H)).
  exact (proj1 (var_env''singleton H)).
Qed.

Lemma imagef1lemma' :
 forall ve : var_env'',
 In _ Evar_env''LSU ve ->
 in_dom _ (N_of_nat U) ve = true ->
 exists ve' : var_env'', In _ Evar_env''LU ve' /\ f1' ve' = ve.
Proof.
  intros.  unfold Evar_env''LSU in H.  unfold Evar_env'' in H.  unfold In in H.
  split with (MapRemove _ ve (N_of_nat U)).  split.  unfold In in |- *.
  unfold Evar_env''LU in |- *.  unfold Evar_env'' in |- *.  split.  apply MapRemove_canon.
  exact (proj1 H).  intros.  unfold in_dom in |- *.
  rewrite (MapRemove_semantics unit ve (N_of_nat U) x).
  elim (sumbool_of_bool (Neqb (N_of_nat U) x)).  intro y.  rewrite y.
  reflexivity.  intro y.  rewrite y.  unfold in_dom in H.  apply (proj2 H).
  unfold var_lu in |- *.  unfold var_lu in H1.  elim (andb_false_elim _ _ H1).  intro y0.
  rewrite y0.  reflexivity.  intro y0.
  replace (leb (S (nat_of_N x)) (S U)) with false.
  elim (leb L (nat_of_N x)); reflexivity.  symmetry  in |- *.
  apply not_true_is_false.  unfold not in |- *; intro.  cut (nat_of_N x <= U).
  intro.  elim (le_le_S_eq _ _ H3).  intro.
  rewrite (leb_correct _ _ H4) in y0.  discriminate.  intro.
  rewrite <- H4 in y.  rewrite (N_of_nat_of_N x) in y.
  rewrite (Neqb_correct x) in y.  discriminate.  apply le_S_n.
  apply leb_complete.  assumption.  unfold f1' in |- *.  unfold Evar_env''ntoSn in |- *.
  unfold var_env'' in ve.  apply
   (mapcanon_unique _
      (MapPut unit (MapRemove unit ve (N_of_nat U)) (N_of_nat U) tt) ve).
  apply MapPut_canon.  apply MapRemove_canon.  exact (proj1 H).
  exact (proj1 H).  unfold eqmap in |- *.  unfold eqm in |- *.  intro.
  rewrite
   (MapPut_semantics unit (MapRemove unit ve (N_of_nat U)) 
      (N_of_nat U) tt a).
  elim H; intros.  elim (sumbool_of_bool (Neqb (N_of_nat U) a)).  intro y.
  rewrite y.  unfold in_dom in H0.  rewrite (Neqb_complete _ _ y) in H0.
  elim (option_sum _ (MapGet unit ve a)).  intro y0.  elim y0.  intro x.  elim x.
  intros y1.  rewrite y1.  reflexivity.  intro y0.  rewrite y0 in H0.  discriminate.
  intro y.  rewrite y.  rewrite (MapRemove_semantics unit ve (N_of_nat U) a).
  rewrite y.  reflexivity.
Qed.

Lemma imagef2lemma' :
 forall ve : var_env'',
 In _ Evar_env''LSU ve ->
 in_dom _ (N_of_nat U) ve = false ->
 exists ve' : var_env'', In _ Evar_env''LU ve' /\ f2' ve' = ve.
Proof.
  intros.  unfold Evar_env''LSU in H.  unfold Evar_env'' in H.  unfold In in H.
  split with ve.  split.  unfold In in |- *.  unfold Evar_env''LU in |- *.  unfold Evar_env'' in |- *.
  split.  exact (proj1 H).  intros.  unfold var_lu in H1.
  elim (andb_false_elim _ _ H1).  intro y.  apply (proj2 H).  unfold var_lu in |- *.
  rewrite y.  reflexivity.  intro y.
  elim (sumbool_of_bool (Neqb x (N_of_nat U))).  intro y0.
  rewrite <- (Neqb_complete _ _ y0) in H0.  assumption.  intro y0.
  apply (proj2 H).  unfold var_lu in |- *.
  replace (leb (S (nat_of_N x)) (S U)) with false.
  elim (leb L (nat_of_N x)); reflexivity.  symmetry  in |- *.  simpl in |- *.
  apply not_true_is_false.  unfold not in |- *; intro.
  elim (le_le_S_eq _ _ (leb_complete _ _ H2)).  intro.
  rewrite (leb_correct _ _ H3) in y.  discriminate.  intro.
  rewrite <- H3 in y0.  rewrite (N_of_nat_of_N x) in y0.
  rewrite (Neqb_correct x) in y0.  discriminate.  reflexivity.  
Qed.

Lemma imagef1'orf2'lemma :
 forall ve : var_env'', In _ Evar_env''LSU ve -> In _ imagef1'orf2' ve.
Proof.
  intros.  unfold Evar_env''LSU in H.  unfold Evar_env'' in H.  unfold In in H.
  unfold imagef1'orf2' in |- *.  elim (sumbool_of_bool (in_dom _ (N_of_nat U) ve)).
  intro y.  apply Union_introl.  unfold imagef1' in |- *.  elim (imagef1lemma' ve H y).
  intros.  apply (Im_intro _ _ Evar_env''LU f1' x).  exact (proj1 H0).
  rewrite (proj2 H0).  reflexivity.  intro y.  elim (imagef2lemma' ve H y).
  intros.  apply Union_intror.  unfold imagef2' in |- *.  elim (imagef2lemma' ve H y).
  intros.  apply (Im_intro _ _ Evar_env''LU f2' x).  exact (proj1 H0).  
  rewrite (proj2 H0).  reflexivity.
Qed.

Section CardImage.

Variable n : nat.
Hypothesis H : cardinal _ Evar_env''LU n.

Lemma card_imagef1'lemma : forall m : nat, cardinal _ imagef1' m -> m <= n.
Proof.
  unfold imagef1' in |- *.  intros.
  apply cardinal_decreases with (A := Evar_env''LU) (f := f1').  assumption.
  assumption.
Qed.

Lemma card_imagef2'lemma : forall m : nat, cardinal _ imagef2' m -> m <= n.
Proof.
  unfold imagef2' in |- *.  intros.
  apply cardinal_decreases with (A := Evar_env''LU) (f := f2').  assumption.
  assumption.
Qed.

Lemma imagef1'finite : Finite _ imagef1'.
Proof.
  unfold imagef1' in |- *.  apply finite_image.  apply cardinal_finite with (n := n).
  assumption.
Qed.

Lemma imagef2'finite : Finite _ imagef2'.
Proof.
  unfold imagef2' in |- *.  apply finite_image.  apply cardinal_finite with (n := n).
  assumption.
Qed.

Lemma card_imagef1'orf2'lemma :
 forall m : nat, cardinal _ imagef1'orf2' m -> m <= 2 * n.
Proof.
  intros.  simpl in |- *.  rewrite <- (plus_n_O n).
  elim (finite_cardinal _ _ imagef1'finite).  intros.
  elim (finite_cardinal _ _ imagef2'finite).  intros.
  apply le_trans with (m := x + x0).  unfold imagef1'orf2' in H0.
  apply cardinal_Union with (X := imagef1') (Y := imagef2').  assumption.  assumption.
  assumption.  apply plus_le_compat.  apply card_imagef1'lemma.  assumption.
  apply card_imagef2'lemma.  assumption.
Qed.

Lemma imagef1'orf2'finite : Finite _ imagef1'orf2'.
Proof.
  unfold imagef1'orf2' in |- *.  apply Union_preserves_Finite.  apply imagef1'finite.
  apply imagef2'finite.
Qed.

Lemma card_Evar_env''LSU_lemma :
 forall m : nat, cardinal _ Evar_env''LSU m -> m <= 2 * n.
Proof.
  intros.  elim (finite_cardinal _ imagef1'orf2').  intros.
  apply le_trans with (m := x).
  apply incl_card_le with (X := Evar_env''LSU) (Y := imagef1'orf2').  assumption.
  assumption.  exact imagef1'orf2'lemma.  apply card_imagef1'orf2'lemma.
  assumption.  apply imagef1'orf2'finite.  
Qed.

Lemma Evar_env''LSU_finite : Finite _ Evar_env''LSU.
Proof.
  apply Finite_downward_closed with (A := imagef1'orf2').
  apply imagef1'orf2'finite.  exact imagef1'orf2'lemma.  
Qed.

End CardImage.
End Evar_env''LULSU.

Lemma Evar_env''LSULU :
 forall L U : nat, Evar_env''LSU L U = Evar_env''LU L (S U).
Proof.
  reflexivity.
Qed.

Lemma Eenv_var''LU_finite :
 forall n L U : nat, n = U - L -> Finite _ (Evar_env''LU L U).
Proof.
  simple induction n.  intros.  apply cardinal_finite with (n := 1).
  apply var_env''cardinal_one.  rewrite H.  reflexivity.  intros.
  cut (U = S (L + n0)).  intro.  rewrite H1.
  rewrite <- (Evar_env''LSULU L (L + n0)).
  elim (finite_cardinal _ (Evar_env''LU L (L + n0))).  intros.
  apply Evar_env''LSU_finite with (n := x).  assumption.  apply H.  symmetry  in |- *.
  apply minus_plus.  rewrite (Splus_nm L n0).  rewrite (plus_Snm_nSm L n0).
  rewrite H0.  apply le_plus_minus.  apply lt_le_weak.  apply lt_O_minus_lt.
  rewrite <- H0.  auto with arith.  
Qed.

Lemma Eenv_var''LU_card :
 forall n L U c : nat,
 n = U - L -> cardinal _ (Evar_env''LU L U) c -> c <= two_power n.
Proof.
  simple induction n.  simpl in |- *.  intros.
  cut (cardinal var_env'' (Evar_env''LU L U) 1).  intro.
  rewrite (cardinal_unicity _ _ _ H0 _ H1).  auto with arith.  
  apply var_env''cardinal_one.  rewrite H.  reflexivity.  intros.
  cut (U = S (L + n0)).  intro.  rewrite H2 in H1.
  replace (two_power (S n0)) with (2 * two_power n0).
  elim (finite_cardinal _ (Evar_env''LU L (L + n0))).  intros.
  apply le_trans with (m := 2 * x).
  apply card_Evar_env''LSU_lemma with (L := L) (U := L + n0).  assumption.  
  assumption.  simpl in |- *.  rewrite <- (plus_n_O x).
  rewrite <- (plus_n_O (two_power n0)).  cut (x <= two_power n0).  intro.
  apply plus_le_compat.  assumption.  assumption.
  apply H with (L := L) (U := L + n0).  symmetry  in |- *.  apply minus_plus.  assumption.
  apply Eenv_var''LU_finite with (n := n0).  symmetry  in |- *.  apply minus_plus.  
  reflexivity.  rewrite (Splus_nm L n0).  rewrite (plus_Snm_nSm L n0).
  rewrite H0.  apply le_plus_minus.  apply lt_le_weak.  apply lt_O_minus_lt.
  rewrite <- H0.  auto with arith.  
Qed.

Lemma Eenv''_var''finite : forall L U : nat, Finite _ (Evar_env'' L U).
Proof.
  intros.  apply Eenv_var''LU_finite with (n := U - L).  reflexivity.
Qed.

Lemma Eenv''_var''card :
 forall L U n : nat,
 cardinal _ (Evar_env''LU L U) n -> n <= two_power (U - L).
Proof.
  intros.  apply Eenv_var''LU_card with (L := L) (U := U).  reflexivity.  assumption.
Qed.

(*
Inductive index : Set := i_intro : (n:nat)(le L n) -> (lt n U) -> index.
Definition order := [i:index]Cases i of (i_intro n _ _) => n end.
Definition index_eq := [i,j:index](order i)=(order j).

Section Sequence.
  Variable A:Set.
  Variable A_eq:A->A->Prop.
  Definition seq := index -> A.
  Definition seq_ok := [s:seq](i,j:index)(index_eq i j) -> (A_eq (s i) (s j)).
  Definition seq_inj := [s:seq](i,j:index)(A_eq (s i) (s j)) -> (index_eq i j).
  Definition seq_surj := [s:seq](a:A)(EX i:index|(A_eq (s i) a)).
End Sequence.

Lemma nat_to_index : (n:nat)(le L n) -> (lt n U) -> (EX i:index|(order i)=n).
Proof.
  Intros.  Split with (i_intro n H H0).  Auto with v62.
Qed.

Lemma var_lu_to_index1 :
  (x:ad)(var_lu x)=true->index.
Proof.
  Unfold var_lu.  Intros.  Elim (andb_prop ? ? H).  Intros.
  Refine (i_intro (nat_of_N x) ? ?).  Apply leb_complete.  Assumption.
  Unfold lt.  Apply leb_complete.  Assumption.
Qed.

Lemma var_lu_to_index2 :
  (x:BDDvar; pi:(var_lu x)=true)(order (var_lu_to_index1 x pi))=(nat_of_N x).
Lemma var_lu_to_index :
  (x:ad)(var_lu x)=true->(EX i:index|(order i)=(nat_of_N x)).
Proof.
  Unfold var_lu.  Intros.  Elim (andb_prop ? ? H).  Intros.
  Split with (i_intro (nat_of_N x) (leb_complete ? ? H0)
        (leb_complete ? ? H1)).
  Reflexivity.
Qed.

Inductive be_lu : Set := be_lu_intro : (be:bool_expr)(be_ok var_lu be) -> be_lu.
Definition be_of_be_lu := [bel:be_lu]Cases bel of (be_lu_intro be _) => be end.
Definition var_env_lu := (seq bool).

Definition env_lu_to_var_binding := [vel:var_env_lu;x:BDDvar]
(* problem in defining this function *)
  Cases (var_lu x) of
      true => (([pi:true=(var_lu x)](vel (var_lu_to_index1 x (sym_eq ? ? ? pi)))) (refl_equal ? (var_lu x)))
    | false => false
  end.

Lemma eval_be' : be_lu -> var_env_lu -> bool.
(* to be completed *)
Proof.
  Unfold var_env_lu.  Unfold seq.  Intros.  Elim H.  Induction be.  Intros.
  Exact false.  Intros.  Exact true.

  Intros.  Exact true.  Intros.  Exact true.  Intros.  Exact true.  Intros.
  Exact true.  Intros.  Exact true.  Intros.  Exact true.
Qed.
*)

Lemma minusUL0_var_lu :
 forall L U : nat, U - L = 0 -> forall x : ad, var_lu L U x = false.
Proof.
  intros.  apply not_true_is_false.  unfold var_lu in |- *.  unfold not in |- *; intro.
  elim (andb_prop _ _ H0).  intros.  absurd (0 < U - L).  rewrite H.
  apply lt_irrefl.  apply lt_mn_minus.  unfold lt in |- *.
  apply le_trans with (m := S (nat_of_N x)).  apply le_n_S.
  apply leb_complete.  assumption.  apply leb_complete.  assumption.
Qed.

Definition bool_expr_to_var_env'' (L U : nat) (be : bool_expr) :
  Ensemble var_env'' :=
  fun ve =>
  eval_be' be (var_env''_to_env' ve) = true /\ In _ (Evar_env'' L U) ve.

Definition be_le1 (L U : nat) (be1 be2 : bool_expr) :=
  forall ve : var_env'',
  In _ (bool_expr_to_var_env'' L U be1) ve ->
  In _ (bool_expr_to_var_env'' L U be2) ve.

Lemma var_env'_to_var_env''_lemma1 :
 forall (n L U : nat) (ve : var_env'),
 n = U - L ->
 exists ve'' : var_env'',
   In _ (Evar_env'' L U) ve'' /\
   (forall x : ad, var_lu L U x = true -> in_dom _ x ve'' = ve (nat_of_N x)).
Proof.
  simple induction n.  intros.  split with (M0 unit).  split.  apply M0inEvar_env''.
  unfold var_lu in |- *.  intros.  absurd (0 < U - L).  rewrite H.  apply lt_irrefl.
  apply lt_mn_minus.  elim (andb_prop _ _ H0).  intros.  unfold lt in |- *.
  apply le_trans with (m := S (nat_of_N x)).  apply le_n_S.
  apply leb_complete.  assumption.  apply leb_complete.  assumption.  
  intros.  cut (U = S (L + n0)).  intro.  elim (H L (L + n0) ve).  intros.
  elim (sumbool_of_bool (ve (L + n0))).  intros y.
  split with (MapPut _ x (N_of_nat (L + n0)) tt).  intros.  unfold in_dom in |- *.
  split.  rewrite H1.  fold (Evar_env''ntoSn (L + n0) x) in |- *.
  apply Evar_env''ntoSn_lemma.  apply le_plus_l.  exact (proj1 H2).  intros.
  rewrite (MapPut_semantics unit x (N_of_nat (L + n0)) tt x0).
  elim (sumbool_of_bool (Neqb (N_of_nat (L + n0)) x0)).  intro y0.
  rewrite y0.  rewrite <- (Neqb_complete _ _ y0).
  rewrite (nat_of_N_of_nat (L + n0)).  rewrite y.  reflexivity.  intro y0.
  rewrite y0.  unfold in_dom in H2.  apply (proj2 H2).
  elim (andb_prop _ _ H3).  intros.  unfold var_lu in |- *.  rewrite H4.
  replace (leb (S (nat_of_N x0)) (L + n0)) with true.  reflexivity.  
  symmetry  in |- *.  elim (le_le_S_eq (nat_of_N x0) (L + n0)).  intro.
  apply leb_correct.  assumption.  intro.  rewrite <- H6 in y0.
  rewrite (N_of_nat_of_N x0) in y0.  rewrite (Neqb_correct x0) in y0.
  discriminate.  apply le_S_n.  rewrite <- H1.  apply leb_complete.
  assumption.  intro y.  split with (MapRemove _ x (N_of_nat (L + n0))).
  split.  unfold Evar_env'' in |- *.  unfold In in |- *.  split.  apply MapRemove_canon.
  exact (proj1 (proj1 H2)).  intros.  unfold in_dom in |- *.
  rewrite (MapRemove_semantics unit x (N_of_nat (L + n0)) x0).
  rewrite H1 in H3.
  elim (sumbool_of_bool (Neqb (N_of_nat (L + n0)) x0)).  intro y0.
  rewrite y0.  reflexivity.  intro y0.  rewrite y0.  unfold Evar_env'' in H2.
  unfold In in H2.  unfold in_dom in H2.  apply (proj2 (proj1 H2)).
  apply not_true_is_false.  unfold not in |- *.  intro.  unfold var_lu in H4.
  unfold var_lu in H3.
  elim (andb_prop _ _ H4); intros H6 H7.
  rewrite H6 in H3.
  elim (le_le_S_eq (nat_of_N x0) (L + n0)).  intro.
  cut (leb (S (nat_of_N x0)) (S (L + n0)) = true).  intro.
  rewrite H8 in H3.  discriminate.  apply leb_correct.
  apply le_trans with (m := L + n0).  assumption.  apply le_n_Sn.  intro.
  rewrite <- H5 in y0.  rewrite (N_of_nat_of_N x0) in y0.
  rewrite (Neqb_correct x0) in y0.  discriminate.
  apply le_trans with (m := S (nat_of_N x0)).  apply le_n_Sn.
  apply leb_complete.  assumption.  intros.  unfold in_dom in |- *.
  rewrite (MapRemove_semantics unit x (N_of_nat (L + n0)) x0).
  rewrite H1 in H3.  elim (andb_prop _ _ H3).  intros.
  elim (sumbool_of_bool (Neqb (N_of_nat (L + n0)) x0)).  intro y0.
  rewrite y0.  rewrite <- (Neqb_complete _ _ y0).
  rewrite (nat_of_N_of_nat (L + n0)).  rewrite y.  reflexivity.  intro y0.
  rewrite y0.  unfold in_dom in H2.  apply (proj2 H2).  unfold var_lu in |- *.
  rewrite H4.  replace (leb (S (nat_of_N x0)) (L + n0)) with true.
  reflexivity.  symmetry  in |- *.  elim (le_le_S_eq (nat_of_N x0) (L + n0)).
  intro.  apply leb_correct.  assumption.  intro.  rewrite <- H6 in y0.
  rewrite (N_of_nat_of_N x0) in y0.  rewrite (Neqb_correct x0) in y0.
  discriminate.  apply le_S_n.  apply leb_complete.  assumption.  symmetry  in |- *.
  apply minus_plus.  rewrite (Splus_nm L n0).  rewrite (plus_Snm_nSm L n0).
  rewrite H0.  apply le_plus_minus.  apply lt_le_weak.  apply lt_O_minus_lt.
  rewrite <- H0.  auto with arith.  
Qed.

Lemma var_env'_to_var_env''_lemma2 :
 forall (n L U : nat) (ve : var_env'),
 n = U - L ->
 {ve'' : var_env'' |
 In _ (Evar_env'' L U) ve'' /\
 (forall x : ad, var_lu L U x = true -> in_dom _ x ve'' = ve (nat_of_N x))}.
Proof.
  simple induction n.  intros.  split with (M0 unit).  split.  apply M0inEvar_env''.
  unfold var_lu in |- *.  intros.  absurd (0 < U - L).  rewrite H.  apply lt_irrefl.
  apply lt_mn_minus.  elim (andb_prop _ _ H0).  intros.  unfold lt in |- *.
  apply le_trans with (m := S (nat_of_N x)).  apply le_n_S.
  apply leb_complete.  assumption.  apply leb_complete.  assumption.  
  intros.  cut (U = S (L + n0)).  intro.  elim (H L (L + n0) ve).  intros x y.
  elim (sumbool_of_bool (ve (L + n0))).  intros y0.
  split with (MapPut _ x (N_of_nat (L + n0)) tt).  intros.  unfold in_dom in |- *.
  split.  rewrite H1.  fold (Evar_env''ntoSn (L + n0) x) in |- *.
  apply Evar_env''ntoSn_lemma.  apply le_plus_l.  exact (proj1 y).  intros.
  rewrite (MapPut_semantics unit x (N_of_nat (L + n0)) tt x0).
  elim (sumbool_of_bool (Neqb (N_of_nat (L + n0)) x0)).  intro y1.
  rewrite y1.  rewrite <- (Neqb_complete _ _ y1).
  rewrite (nat_of_N_of_nat (L + n0)).  rewrite y0.  reflexivity.  intro y1.
  rewrite y1.  unfold in_dom in y.  apply (proj2 y).
  elim (andb_prop _ _ H2).  intros.  unfold var_lu in |- *.  rewrite H3.
  replace (leb (S (nat_of_N x0)) (L + n0)) with true.  reflexivity.  
  symmetry  in |- *.  elim (le_le_S_eq (nat_of_N x0) (L + n0)).  intro.
  apply leb_correct.  assumption.  intro.  rewrite <- H5 in y1.
  rewrite (N_of_nat_of_N x0) in y1.  rewrite (Neqb_correct x0) in y1.
  discriminate.  apply le_S_n.  rewrite <- H1.  apply leb_complete.
  assumption.  intro y0.  split with (MapRemove _ x (N_of_nat (L + n0))).
  split.  unfold Evar_env'' in |- *.  unfold In in |- *.  split.  apply MapRemove_canon.
  exact (proj1 (proj1 y)).  intros.  unfold in_dom in |- *.
  rewrite (MapRemove_semantics unit x (N_of_nat (L + n0)) x0).
  rewrite H1 in H2.
  elim (sumbool_of_bool (Neqb (N_of_nat (L + n0)) x0)).  intro y1.
  rewrite y1.  reflexivity.  intro y1.  rewrite y1.  unfold Evar_env'' in y.
  unfold In in y.  unfold in_dom in y.  apply (proj2 (proj1 y)).
  apply not_true_is_false.  unfold not in |- *.  intro.  unfold var_lu in H3.
  unfold var_lu in H2. 
  elim (andb_prop _ _ H3); intros H5 H6.
  rewrite H5 in H2.
  elim (le_le_S_eq (nat_of_N x0) (L + n0)).  intro.
  cut (leb (S (nat_of_N x0)) (S (L + n0)) = true).  intro.
  rewrite H7 in H2.  discriminate.  apply leb_correct.
  apply le_trans with (m := L + n0).  assumption.  apply le_n_Sn.  intro.
  rewrite <- H4 in y1.  rewrite (N_of_nat_of_N x0) in y1.
  rewrite (Neqb_correct x0) in y1.  discriminate.
  apply le_trans with (m := S (nat_of_N x0)).  apply le_n_Sn.
  apply leb_complete.  assumption.  intros.  unfold in_dom in |- *.
  rewrite (MapRemove_semantics unit x (N_of_nat (L + n0)) x0).
  rewrite H1 in H2.  elim (andb_prop _ _ H2).  intros.
  elim (sumbool_of_bool (Neqb (N_of_nat (L + n0)) x0)).  intro y1.
  rewrite y1.  rewrite <- (Neqb_complete _ _ y1).
  rewrite (nat_of_N_of_nat (L + n0)).  rewrite y0.  reflexivity.  intro y1.
  rewrite y1.  unfold in_dom in y.  apply (proj2 y).  unfold var_lu in |- *.
  rewrite H3.  replace (leb (S (nat_of_N x0)) (L + n0)) with true.
  reflexivity.  symmetry  in |- *.  elim (le_le_S_eq (nat_of_N x0) (L + n0)).
  intro.  apply leb_correct.  assumption.  intro.  rewrite <- H5 in y1.
  rewrite (N_of_nat_of_N x0) in y1.  rewrite (Neqb_correct x0) in y1.
  discriminate.  apply le_S_n.  apply leb_complete.  assumption.  symmetry  in |- *.
  apply minus_plus.  rewrite (Splus_nm L n0).  rewrite (plus_Snm_nSm L n0).
  rewrite H0.  apply le_plus_minus.  apply lt_le_weak.  apply lt_O_minus_lt.
  rewrite <- H0.  auto with arith.  
Qed.

Definition var_env'_to_env'' (L U : nat) (ve : var_env') :=
  match var_env'_to_var_env''_lemma2 (U - L) L U ve (refl_equal _) with
  | exist ve'' _ => ve''
  end.

Lemma var_env'_to_env''_lemma3 :
 forall (L U : nat) (ve : var_env'),
 In _ (Evar_env'' L U) (var_env'_to_env'' L U ve) /\
 (forall x : ad,
  var_lu L U x = true ->
  in_dom _ x (var_env'_to_env'' L U ve) = ve (nat_of_N x)).
Proof.
  intros L U ve.  unfold var_env'_to_env'' in |- *.
  elim (var_env'_to_var_env''_lemma2 (U - L) L U ve (refl_equal (U - L))).
  intros.  assumption.
Qed.

Lemma be_le1_le :
 forall (L U : nat) (be1 be2 : bool_expr),
 be_ok (var_lu L U) be1 ->
 be_ok (var_lu L U) be2 -> be_le1 L U be1 be2 -> be_le be1 be2.
Proof.
  intros.  unfold be_le in |- *.  intros.  unfold be_le1 in H1.
  elim (var_env'_to_var_env''_lemma1 (U - L) L U ve).  intros.
  unfold bool_expr_to_var_env'' in H1.  unfold In in H1.  unfold In in H3.
  cut (seq_eq L U _ (eq (A:=_)) ve (var_env''_to_env' x)).  intro.  elim (H1 x).
  intros.  rewrite (eval_be_independent L U ve (var_env''_to_env' x) H4 be2).
  assumption.  assumption.  split.
  rewrite (eval_be_independent L U ve (var_env''_to_env' x) H4 be1) in H2.
  assumption.  assumption.  exact (proj1 H3).  unfold seq_eq in |- *.  intros.
  unfold var_env''_to_env' in |- *.  symmetry  in |- *.
  replace (ve n) with (ve (nat_of_N (N_of_nat n))).  apply (proj2 H3).
  apply nat_lu_var_lu.  assumption.  rewrite (nat_of_N_of_nat n).  reflexivity.
  reflexivity.
Qed.

Lemma be_le_le1 :
 forall (L U : nat) (be1 be2 : bool_expr),
 be_le be1 be2 -> be_le1 L U be1 be2.
Proof.
  intros.  unfold be_le1 in |- *.  unfold In in |- *.  unfold bool_expr_to_var_env'' in |- *.  intros.
  split.  apply H.  exact (proj1 H0).  exact (proj2 H0).  
Qed.

Definition var_env''le (ve1 ve2 : var_env'') :=
  forall x : ad, in_dom _ x ve1 = true -> in_dom _ x ve2 = true.

Lemma var_env''le_refl : forall ve : var_env'', var_env''le ve ve.
Proof.
  unfold var_env''le in |- *.  trivial.  
Qed.

Lemma var_env''le_trans :
 forall ve1 ve2 ve3 : var_env'',
 var_env''le ve1 ve2 -> var_env''le ve2 ve3 -> var_env''le ve1 ve3.
Proof.
  unfold var_env''le in |- *.  intros.  apply H0.  apply H.  assumption.
Qed.

Lemma be_le_ens_inc :
 forall (be1 be2 : bool_expr) (L U : nat),
 be_le be1 be2 ->
 Included _ (bool_expr_to_var_env'' L U be1) (bool_expr_to_var_env'' L U be2).
Proof.
  unfold Included, bool_expr_to_var_env'' in |- *.  intros.  unfold In in |- *.  unfold In in H0.
  unfold be_le in H.  split.  apply H.  exact (proj1 H0).  
  exact (proj2 H0).  
Qed.

Lemma incl_eq :
 forall (U : Type) (A B : Ensemble U) (n : nat),
 Included _ A B -> cardinal _ A n -> cardinal _ B n -> Included _ B A.
Proof.
  intros.  unfold Included in |- *.  intros.  elim (classic (In _ A x)). trivial.  
  intro.  elim (lt_irrefl n).  fold (n > n) in |- *.
  apply incl_st_card_lt with (X := A) (Y := B).  assumption.  assumption.  split.
  assumption.  unfold not in |- *; intro.  rewrite H4 in H3.  apply H3.  assumption.  
Qed.

Lemma decreasing_seq :
 forall (n : nat) (f : nat -> nat),
 f 0 = n ->
 (forall n : nat, f (S n) <= f n) -> exists m : nat, m <= n /\ f m = f (S m).
Proof.
  intro.
  apply
   lt_wf_ind
    with
      (P := fun n : nat =>
            forall f : nat -> nat,
            f 0 = n ->
            (forall n : nat, f (S n) <= f n) ->
            exists m : nat, m <= n /\ f m = f (S m)).
  intros.  elim (eq_nat_decide (f 0) (f 1)).  intro y.  split with 0.  split.
  apply le_O_n.  apply eq_nat_eq.  assumption.  intro y.  cut (f 1 < n0).
  intro.  elim (H (f 1) H2 (fun n : nat => f (S n))).  intros.  split with (S x).
  split.  fold (x < n0) in |- *.  apply le_lt_trans with (m := f 1).
  exact (proj1 H3).  assumption.  exact (proj2 H3).  reflexivity.  
  intro.  apply H1.  rewrite <- H0.  elim (le_le_S_eq (f 1) (f 0)).  intro.
  assumption.  intro.  rewrite H2 in y.  elim (y (eq_nat_refl _)).  apply H1.
Qed.

Lemma decreasing_ens_seq :
 forall (U : Type) (n : nat) (f : nat -> Ensemble U),
 cardinal _ (f 0) n ->
 (forall k : nat, Finite _ (f k)) ->
 (forall k : nat, Included _ (f (S k)) (f k)) ->
 exists m : nat,
   (exists c : nat, m <= n /\ cardinal _ (f m) c /\ cardinal _ (f (S m)) c).
Proof.
  intros U n.
  apply
   lt_wf_ind
    with
      (P := fun n : nat =>
            forall f : nat -> Ensemble U,
            cardinal U (f 0) n ->
            (forall k : nat, Finite U (f k)) ->
            (forall k : nat, Included U (f (S k)) (f k)) ->
            exists m : nat,
              (exists c : nat,
                 m <= n /\ cardinal U (f m) c /\ cardinal U (f (S m)) c)).
  intros.  elim (finite_cardinal _ _ (H1 1)).  intros.
  elim (eq_nat_decide n0 x).  intros y.  split with 0.  split with n0.  split.
  apply le_O_n.  split.  assumption.  rewrite (eq_nat_eq _ _ y).  assumption.
  intro y.  cut (x < n0).  intro.  elim (H x H4 (fun n : nat => f (S n))).  intros.
  elim H5; clear H5.  intros.  split with (S x0).  split with x1.  split.
  fold (x0 < n0) in |- *.  apply le_lt_trans with (m := x).  exact (proj1 H5).
  assumption.  exact (proj2 H5).  assumption.  intro.  apply H1.  intros.
  apply H2.  elim (le_le_S_eq x n0).  intro.  assumption.  intro.
  rewrite H4 in y.  elim (y (eq_nat_refl _)).
  apply incl_card_le with (X := f 1) (Y := f 0).  assumption.  assumption.  
  apply H2.  
Qed.

Lemma bool_expr_to_var_env''_finite :
 forall (L U : nat) (be : bool_expr),
 be_ok (var_lu L U) be -> Finite _ (bool_expr_to_var_env'' L U be).
Proof.
  intros.  apply Finite_downward_closed with (A := Evar_env'' L U).
  apply Eenv_var''LU_finite with (n := U - L).  reflexivity.  
  unfold bool_expr_to_var_env'' in |- *.  unfold Included in |- *.  intros.
  exact (proj2 H0).
Qed.

Lemma bool_expr_to_var_env''_card :
 forall (L U n : nat) (be : bool_expr),
 be_ok (var_lu L U) be ->
 cardinal _ (bool_expr_to_var_env'' L U be) n -> n <= two_power (U - L).
Proof.
  intros.  elim (finite_cardinal _ _ (Eenv_var''LU_finite (U - L) L U (refl_equal _))).
  intros.  apply le_trans with (m := x).  apply
   incl_card_le
    with (Y := Evar_env''LU L U) (X := bool_expr_to_var_env'' L U be).
  assumption.  assumption.  unfold bool_expr_to_var_env'' in |- *.  unfold Included in |- *.
  intros.  exact (proj2 H2).  apply Eenv_var''LU_card with (L := L) (U := U).
  reflexivity.  assumption.  
Qed.

Lemma decreasing_be_seq :
 forall (n L U : nat) (f : nat -> bool_expr),
 cardinal _ (bool_expr_to_var_env'' L U (f 0)) n ->
 (forall k : nat, be_le (f (S k)) (f k)) ->
 (forall k : nat, be_ok (var_lu L U) (f k)) ->
 exists m : nat, m <= n /\ be_le (f m) (f (S m)).
Proof.
  intros.  elim
   (decreasing_ens_seq var_env'' n
      (fun n : nat => bool_expr_to_var_env'' L U (f n))).
  intros.  elim H2; clear H2.  intros.  decompose [and] H2.  clear H2.
  split with x.  split.  assumption.  apply be_le1_le with (L := L) (U := U).  apply H1.
  apply H1.  unfold be_le1 in |- *.
  fold
   (Included _ (bool_expr_to_var_env'' L U (f x))
      (bool_expr_to_var_env'' L U (f (S x)))) in |- *.
  apply incl_eq with (n := x0).
  unfold Included in |- *.
  fold (be_le1 L U (f (S x)) (f x)) in |- *.  apply be_le_le1.  apply H0.  assumption.
  assumption.  assumption.  intro.  apply bool_expr_to_var_env''_finite.
  apply H1.  unfold Included in |- *.  intro.  fold (be_le1 L U (f (S k)) (f k)) in |- *.
  apply be_le_le1.  apply H0.  
Qed.

Lemma decreasing_be_seq_1 :
 forall (L U : nat) (f : nat -> bool_expr),
 (forall k : nat, be_ok (var_lu L U) (f k)) ->
 (forall k : nat, be_le (f (S k)) (f k)) ->
 exists m : nat, m <= two_power (U - L) /\ be_eq (f m) (f (S m)).
Proof.
  intros.
  elim (finite_cardinal _ _ (bool_expr_to_var_env''_finite L U (f 0) (H 0))).
  intros.  elim (decreasing_be_seq x L U f).  intros.  split with x0.  split.
  apply le_trans with (m := x).  exact (proj1 H2).  
  apply bool_expr_to_var_env''_card with (be := f 0).  apply H.  assumption.  
  apply be_le_antisym.  exact (proj2 H2).  apply H0.  assumption.  
  assumption.  assumption.  
Qed.

Lemma increasing_be_seq_1 :
 forall (L U : nat) (f : nat -> bool_expr),
 (forall k : nat, be_ok (var_lu L U) (f k)) ->
 (forall k : nat, be_le (f k) (f (S k))) ->
 exists m : nat, m <= two_power (U - L) /\ be_eq (f m) (f (S m)).
Proof.
  intros.  elim (decreasing_be_seq_1 L U (fun n : nat => Neg (f n))).  intros.
  split with x.  split.  exact (proj1 H1).  apply neg_eq_eq.
  exact (proj2 H1).  intros.  apply neg_ok.  apply H.  intro.
  apply be_le_not_1.  apply H0.  
Qed.

Lemma increasing_seq :
 forall (n : nat) (f : nat -> nat),
 (forall k : nat, f k <= n) ->
 (forall k : nat, f k <= f (S k)) ->
 exists m : nat, m <= n - f 0 /\ f m = f (S m).
Proof.
  intros.  elim (decreasing_seq (n - f 0) (fun k : nat => n - f k)).
  intros.  split with x.  split.  exact (proj1 H1).  
  rewrite (le_minus_minus n (f x)).  rewrite (le_minus_minus n (f (S x))).
  rewrite (proj2 H1).  reflexivity.  apply H.  apply H.  reflexivity.  
  intro.  apply le_minus_le.  apply H0.  
Qed.

Definition unprimed_var := var_lu 0 N.

Definition rel_env := ad -> bool_expr.
Definition Brel_env := Map ad.
Definition trans_env := ad -> bool_expr.
Definition Btrans_env := Map ad.
Definition re_put (re : rel_env) (x : ad) (be : bool_expr) : rel_env :=
  fun y => if Neqb x y then be else re y.

Inductive mu_form : Set :=
  | mu_0 : mu_form
  | mu_1 : mu_form
  | mu_ap : ad -> mu_form
  | mu_rel_var : ad -> mu_form
  | mu_neg : mu_form -> mu_form
  | mu_and : mu_form -> mu_form -> mu_form
  | mu_or : mu_form -> mu_form -> mu_form
  | mu_impl : mu_form -> mu_form -> mu_form
  | mu_iff : mu_form -> mu_form -> mu_form
  | mu_all : ad -> mu_form -> mu_form
  | mu_ex : ad -> mu_form -> mu_form
  | mu_mu : ad -> mu_form -> mu_form.

(* (mu_rel_free P f) means that there is a free occurrence of the relational
   variable P in the formula f *)
Fixpoint mu_rel_free (P : ad) (f : mu_form) {struct f} : bool :=
  match f with
  | mu_0 => false
  | mu_1 => false
  | mu_ap _ => false
  | mu_rel_var Q => Neqb P Q
  | mu_neg g => mu_rel_free P g
  | mu_and g h => mu_rel_free P g || mu_rel_free P h
  | mu_or g h => mu_rel_free P g || mu_rel_free P h
  | mu_impl g h => mu_rel_free P g || mu_rel_free P h
  | mu_iff g h => mu_rel_free P g || mu_rel_free P h
  | mu_all t g => mu_rel_free P g
  | mu_ex t g => mu_rel_free P g
  | mu_mu Q g => negb (Neqb P Q) && mu_rel_free P g
  end.

(* (mu_t_free t f) means that there is a free occurrence of the transition
   variable t in the formula f *)
Fixpoint mu_t_free (t : ad) (f : mu_form) {struct f} : bool :=
  match f with
  | mu_0 => false
  | mu_1 => false
  | mu_ap _ => false
  | mu_rel_var P => false
  | mu_neg g => mu_t_free t g
  | mu_and g h => mu_t_free t g || mu_t_free t h
  | mu_or g h => mu_t_free t g || mu_t_free t h
  | mu_impl g h => mu_t_free t g || mu_t_free t h
  | mu_iff g h => mu_t_free t g || mu_t_free t h
  | mu_all u g => Neqb t u || mu_t_free t g
  | mu_ex u g => Neqb t u || mu_t_free t g
  | mu_mu Q g => mu_t_free t g
  end.

(* Applies the function f n times on argument a *)
Fixpoint iter (A : Type) (A_eq : A -> A -> bool) (f : A -> A) 
 (a : A) (n : nat) {struct n} : A :=
  match n with
  | O => a
  | S m => if A_eq a (f a) then f a else iter _ A_eq f (f a) m
  end.

Definition be_iter (f : bool_expr -> bool_expr) (be : bool_expr) 
  (n : nat) := iter _ be_eq_dec f be n.

Fixpoint iter2n (A : Set) (A_eq : A -> A -> bool) (f : A -> A) 
 (a : A) (n : nat) {struct n} : A * bool :=
  match n with
  | O => (f a, A_eq a (f a))
  | S m =>
      match iter2n _ A_eq f a m with
      | (b, true) => (b, true)
      | (b, false) => iter2n _ A_eq f b m
      end
  end.

Definition be_iter2n := iter2n _ be_eq_dec.

Lemma be_iter_prop_preserved :
 forall (n : nat) (be : bool_expr) (f : bool_expr -> bool_expr)
   (pr : bool_expr -> Prop),
 pr be ->
 (forall be' : bool_expr, pr be' -> pr (f be')) -> pr (be_iter f be n).
Proof.
  simple induction n.  unfold be_iter in |- *.  simpl in |- *.  trivial.  unfold be_iter in |- *.  simpl in |- *.
  intros.  elim (be_eq_dec be (f be)).  apply H1.  assumption.  apply H.
  apply H1.  assumption.  assumption.  
Qed.

Lemma be_iter2n_prop_preserved :
 forall (n : nat) (be : bool_expr) (f : bool_expr -> bool_expr)
   (pr : bool_expr -> Prop),
 pr be ->
 (forall be' : bool_expr, pr be' -> pr (f be')) ->
 pr (fst (be_iter2n f be n)).
Proof.
  simple induction n.  unfold be_iter2n in |- *.  simpl in |- *.  intros.  apply H0.  assumption.
  unfold be_iter2n in |- *.  simpl in |- *.  intros.
  elim (prod_sum _ _ (iter2n bool_expr be_eq_dec f be n0)).  intros.
  inversion H2.  rewrite H3.  elim x0.  simpl in |- *.
  replace x with (fst (iter2n bool_expr be_eq_dec f be n0)).  apply H.
  assumption.  assumption.  rewrite H3.  reflexivity.  apply H.
  replace x with (fst (iter2n bool_expr be_eq_dec f be n0)).  apply H.
  assumption.  assumption.  rewrite H3.  reflexivity.  assumption.
Qed.

Lemma be_iter_eq_preserved :
 forall (n : nat) (be : bool_expr) (f1 f2 : bool_expr -> bool_expr),
 (forall be' : bool_expr, f1 be' = f2 be') ->
 be_iter f1 be n = be_iter f2 be n.
Proof.
  simple induction n.  unfold be_iter in |- *.  simpl in |- *.  reflexivity.  unfold be_iter in |- *.  simpl in |- *.
  intros n0 H be f3 f4 H0.  rewrite (H0 be).  elim (be_eq_dec be (f4 be)).  reflexivity.  
  apply H.  assumption.  
Qed.

Lemma be_iter2n_eq_preserved :
 forall (n : nat) (be : bool_expr) (f1 f2 : bool_expr -> bool_expr),
 (forall be' : bool_expr, f1 be' = f2 be') ->
 be_iter2n f1 be n = be_iter2n f2 be n.
Proof.
  simple induction n.  unfold be_iter2n in |- *.  simpl in |- *.  intros.  rewrite (H be).  intuition. 
  simpl in |- *.  intros n0 H be f3 f4 H0.  unfold be_iter2n in |- *.  simpl in |- *.  unfold be_iter2n in H.
  rewrite (H be f3 f4 H0).  elim (iter2n bool_expr be_eq_dec f4 be n0).  intros y y0.
  rewrite (H y f3 f4 H0).  reflexivity.
Qed.

Lemma be_iter_eq_1 :
 forall (n : nat) (be : bool_expr) (f : bool_expr -> bool_expr),
 be_eq (f be) be -> be_eq (be_iter f be n) be.
Proof.
  simple induction n.  unfold be_iter in |- *.  simpl in |- *.  intros.  apply be_eq_refl.  
  unfold be_iter in |- *.  simpl in |- *.  intros.  replace (be_eq_dec be (f be)) with true.
  assumption.  symmetry  in |- *.  apply be_eq_eq_dec.  apply be_eq_sym.  assumption.
Qed.

Lemma be_iter_eq_preserved_1 :
 forall (n : nat) (be1 be2 : bool_expr) (f1 f2 : bool_expr -> bool_expr),
 be_eq be1 be2 ->
 (forall be1' be2' : bool_expr, be_eq be1' be2' -> be_eq (f1 be1') (f1 be2')) ->
 (forall be1' be2' : bool_expr, be_eq be1' be2' -> be_eq (f2 be1') (f2 be2')) ->
 (forall be1' be2' : bool_expr, be_eq be1' be2' -> be_eq (f1 be1') (f2 be2')) ->
 be_eq (be_iter f1 be1 n) (be_iter f2 be2 n).
Proof.
  simple induction n.  unfold be_iter in |- *.  simpl in |- *.  intros.  assumption.  unfold be_iter in |- *.
  simpl in |- *.  intros n0 H be1 be2 f3 f4 H0 H1 H2 H3.  elim (sumbool_of_bool (be_eq_dec be1 (f3 be1))).  intro y.
  rewrite y.  elim (sumbool_of_bool (be_eq_dec be2 (f4 be2))).  intro y0.
  rewrite y0.  apply H3.  assumption.  intro y0.  rewrite y0.
  apply be_eq_trans with (be2 := iter bool_expr be_eq_dec f3 (f3 be1) n0).
  apply be_eq_sym.  fold (be_iter f3 (f3 be1) n0) in |- *.  apply be_iter_eq_1.
  apply H1.  apply be_eq_sym.  apply be_eq_dec_eq.  assumption.  apply H.
  apply H3.  assumption.  assumption.  assumption.  assumption.  intro y.
  rewrite y.  elim (sumbool_of_bool (be_eq_dec be2 (f4 be2))).  intro y0.
  rewrite y0.
  apply be_eq_trans with (be2 := iter bool_expr be_eq_dec f4 (f4 be2) n0).
  apply H.  apply H3.  assumption.  assumption.  assumption.  assumption.  
  fold (be_iter f4 (f4 be2) n0) in |- *.  apply be_iter_eq_1.  apply H2.
  apply be_eq_sym.  apply be_eq_dec_eq.  assumption.  intro y0.  rewrite y0.
  apply H.  apply H3.  assumption.  assumption.  assumption.  assumption.  
Qed.

Lemma be_iter2n_eq_preserved_1 :
 forall (n : nat) (be1 be2 : bool_expr) (f1 f2 : bool_expr -> bool_expr),
 be_eq be1 be2 ->
 (forall be1' be2' : bool_expr, be_eq be1' be2' -> be_eq (f1 be1') (f1 be2')) ->
 (forall be1' be2' : bool_expr, be_eq be1' be2' -> be_eq (f2 be1') (f2 be2')) ->
 (forall be1' be2' : bool_expr, be_eq be1' be2' -> be_eq (f1 be1') (f2 be2')) ->
 be_eq (fst (be_iter2n f1 be1 n)) (fst (be_iter2n f2 be2 n)) /\
 snd (be_iter2n f1 be1 n) = snd (be_iter2n f2 be2 n).
Proof.
  simple induction n.  unfold be_iter2n in |- *.  simpl in |- *.  intros be1 be2 f3 f4 H H0 H1 H2.  split.  apply H2.
  assumption.  elim (sumbool_of_bool (be_eq_dec be1 (f3 be1))).  intros y.
  rewrite y.  symmetry  in |- *.  apply be_eq_eq_dec.  apply be_eq_trans with (be2 := be1).
  apply be_eq_sym.  assumption.  apply be_eq_trans with (be2 := f3 be1).
  apply be_eq_dec_eq.  assumption.  apply H2.  assumption.  intros y.
  elim (sumbool_of_bool (be_eq_dec be2 (f4 be2))).  intro y0.  rewrite y0.
  apply be_eq_eq_dec.  apply be_eq_trans with (be2 := be2).  assumption.  
  apply be_eq_trans with (be2 := f4 be2).  apply be_eq_dec_eq.  assumption.  
  apply be_eq_sym.  apply H2.  assumption.  intro y0.  rewrite y.  rewrite y0.
  reflexivity.  unfold be_iter2n in |- *.  intros n0 H be1 be2 f3 f4 H0 H1 H2 H3.  simpl in |- *.
  elim (prod_sum _ _ (iter2n bool_expr be_eq_dec f3 be1 n0)).  intros.
  inversion H4.  elim (prod_sum _ _ (iter2n bool_expr be_eq_dec f4 be2 n0)).
  intros.  inversion H6.  cut (be_eq x x1 /\ x0 = x2).  intros.  inversion H8.
  rewrite H5.  rewrite H7.  rewrite H10.  elim x2.  simpl in |- *.
  split; [ assumption | reflexivity ].  apply H.  assumption.  assumption.  
  assumption.  assumption.  
  replace x with (fst (iter2n bool_expr be_eq_dec f3 be1 n0)).
  replace x0 with (snd (iter2n bool_expr be_eq_dec f3 be1 n0)).
  replace x1 with (fst (iter2n bool_expr be_eq_dec f4 be2 n0)).
  replace x2 with (snd (iter2n bool_expr be_eq_dec f4 be2 n0)).  apply H.
  assumption.  assumption.  assumption.  assumption.  rewrite H7; reflexivity.
  rewrite H7; reflexivity.  rewrite H5; reflexivity.  rewrite H5; reflexivity.  
Qed.

Lemma be_iter2n_eq_preserved_2 :
 forall (n : nat) (be1 be2 : bool_expr) (f1 f2 : bool_expr -> bool_expr),
 be_eq be1 be2 ->
 (forall be1' be2' : bool_expr, be_eq be1' be2' -> be_eq (f1 be1') (f1 be2')) ->
 (forall be1' be2' : bool_expr, be_eq be1' be2' -> be_eq (f2 be1') (f2 be2')) ->
 (forall be1' be2' : bool_expr, be_eq be1' be2' -> be_eq (f1 be1') (f2 be2')) ->
 be_eq (fst (be_iter2n f1 be1 n)) (fst (be_iter2n f2 be2 n)).
Proof.
  intros n be1 be2 f3 f4.  intros.  elim (be_iter2n_eq_preserved_1 n be1 be2 f3 f4).  trivial.  
  assumption.  assumption.  assumption.  assumption.
Qed.

Lemma be_iter_le_preserved :
 forall (n : nat) (be1 be2 : bool_expr) (f1 f2 : bool_expr -> bool_expr),
 be_le be1 be2 ->
 (forall be1' be2' : bool_expr, be_eq be1' be2' -> be_eq (f1 be1') (f1 be2')) ->
 (forall be1' be2' : bool_expr, be_eq be1' be2' -> be_eq (f2 be1') (f2 be2')) ->
 (forall be1' be2' : bool_expr, be_le be1' be2' -> be_le (f1 be1') (f2 be2')) ->
 be_le (be_iter f1 be1 n) (be_iter f2 be2 n).
Proof.
  simple induction n.  unfold be_iter in |- *.  simpl in |- *.  intros be1 be2 f3 f4 H H0 H1 H2.  assumption.  unfold be_iter in |- *.
  simpl in |- *.  intros n0 H be1 be2 f3 f4 H0 H1 H2 H3.  elim (sumbool_of_bool (be_eq_dec be1 (f3 be1))).  intro y.
  rewrite y.  elim (sumbool_of_bool (be_eq_dec be2 (f4 be2))).  intro y0.
  rewrite y0.  apply H3.  assumption.  intro y0.  rewrite y0.
  apply be_le_trans with (be2 := iter bool_expr be_eq_dec f3 (f3 be1) n0).
  apply be_eq_le.  apply be_eq_sym.  fold (be_iter f3 (f3 be1) n0) in |- *.
  apply be_iter_eq_1.  apply H1.  apply be_eq_sym.  apply be_eq_dec_eq.
  assumption.  apply H.  apply H3.  assumption.  assumption.  assumption.  
  assumption.  intro y.  rewrite y.
  elim (sumbool_of_bool (be_eq_dec be2 (f4 be2))).  intro y0.  rewrite y0.
  apply be_le_trans with (be2 := iter bool_expr be_eq_dec f4 (f4 be2) n0).
  apply H.  apply H3.  assumption.  assumption.  assumption.  assumption.  
  apply be_eq_le.  fold (be_iter f4 (f4 be2) n0) in |- *.  apply be_iter_eq_1.
  apply H2.  apply be_eq_sym.  apply be_eq_dec_eq.  assumption.  intro y0.
  rewrite y0.  apply H.  apply H3.  assumption.  assumption.  assumption.  
  assumption.
Qed.

Lemma be_iter2n_true :
 forall (n : nat) (be : bool_expr) (f : bool_expr -> bool_expr),
 (forall be1 be2 : bool_expr, be_eq be1 be2 -> be_eq (f be1) (f be2)) ->
 snd (be_iter2n f be n) = true -> fp f (fst (be_iter2n f be n)).
Proof.
  simple induction n.  unfold fp in |- *.  simpl in |- *.  intros.  apply H.
  apply be_eq_dec_eq; assumption.  unfold fp in |- *.  simpl in |- *.  intros n0 H be f H0.
  unfold be_iter2n in |- *.  simpl in |- *.
  elim (prod_sum _ _ (iter2n bool_expr be_eq_dec f be n0)).  intros be1 H1.
  elim H1; clear H1.  intro b.  elim b.  intro.  rewrite H1.  simpl in |- *.  intro.
  replace be1 with (fst (iter2n bool_expr be_eq_dec f be n0)).
  unfold be_iter2n in H.  apply H.  assumption.  rewrite H1; reflexivity.  
  rewrite H1; reflexivity.  intro.  rewrite H1.  intro.  unfold be_iter2n in H.
  apply H.  assumption.  assumption.
Qed.

Lemma be_iter2n_0 :
 forall (n : nat) (be : bool_expr) (f : bool_expr -> bool_expr),
 (forall be1 be2 : bool_expr, be_eq be1 be2 -> be_eq (f be1) (f be2)) ->
 fp f be -> be_eq be (fst (be_iter2n f be n)).
Proof.
  simple induction n.  unfold fp in |- *.  simpl in |- *.  trivial.  unfold be_iter2n in |- *.  simpl in |- *.  intros.
  elim (prod_sum _ _ (iter2n bool_expr be_eq_dec f be n0)).  intros.
  inversion H2.  rewrite H3.  elim x0.
  replace x with (fst (iter2n bool_expr be_eq_dec f be n0)).  simpl in |- *.  apply H.
  assumption.  assumption.  rewrite H3.  reflexivity.  
  apply be_eq_trans with (be2 := x).
  replace x with (fst (iter2n bool_expr be_eq_dec f be n0)).  apply H.
  assumption.  assumption.  rewrite H3.  reflexivity.  apply H.  assumption.  
  unfold fp in |- *.  apply be_eq_trans with (be2 := be).  apply be_eq_sym.
  replace x with (fst (iter2n bool_expr be_eq_dec f be n0)).  apply H.
  assumption.  assumption.  rewrite H3.  reflexivity.
  apply be_eq_trans with (be2 := f be).  exact H1.  apply H0.
  replace x with (fst (iter2n bool_expr be_eq_dec f be n0)).  apply H.
  assumption.  assumption.  rewrite H3.  reflexivity.
Qed.

  Section Be_iter1.

  Variable bef : bool_expr -> bool_expr.
  Hypothesis bef_inc : be_to_be_inc bef.
  Hypothesis
    bef_ok :
      forall be : bool_expr,
      be_ok (var_lu 0 N) be -> be_ok (var_lu 0 N) (bef be).

  Fixpoint be_iter1 (be : bool_expr) (n : nat) {struct n} : bool_expr :=
    match n with
    | O => be
    | S m => be_iter1 (bef be) m
    end.

  Fixpoint be_iter2 (be : bool_expr) (n : nat) {struct n} : bool_expr :=
    match n with
    | O => be
    | S m => bef (be_iter2 be m)
    end.

  Lemma be_iter1_plus :
   forall (m n : nat) (be : bool_expr),
   be_iter1 (be_iter1 be m) n = be_iter1 be (m + n).
  Proof.
    simple induction m.  simpl in |- *.  reflexivity.  simpl in |- *.  intros.  apply H.
  Qed.

  Lemma be_iter1eq2 :
   forall (n : nat) (be : bool_expr), be_iter1 be n = be_iter2 be n.
  Proof.
    simple induction n.  reflexivity.  intros.  simpl in |- *.  rewrite <- (H be).
    transitivity (be_iter1 be (S n0)).  reflexivity.  symmetry  in |- *.
    transitivity (be_iter1 (be_iter1 be n0) 1).  reflexivity.  
    replace (S n0) with (n0 + 1).  apply be_iter1_plus.
    rewrite (plus_comm n0 1).  reflexivity.
  Qed.

  Lemma be_iter1_inc :
   forall (k : nat) (be : bool_expr),
   be_le be (bef be) -> be_le (be_iter1 be k) (be_iter1 be (S k)).
  Proof.
    simple induction k.  unfold be_iter1 in |- *.  trivial.  simpl in |- *.  intros.  apply H.
    apply bef_inc.  assumption.
  Qed.

  Lemma be_iter1_ok :
   forall (k : nat) (be : bool_expr),
   be_ok (var_lu 0 N) be -> be_ok (var_lu 0 N) (be_iter1 be k).
  Proof.
    simple induction k.  trivial.  simpl in |- *.  intros.  apply H.  apply bef_ok.
    assumption.
  Qed.

  Lemma be_iter1_fix_ex :
   forall be : bool_expr,
   be_ok (var_lu 0 N) be ->
   be_le be (bef be) ->
   exists m : nat,
     m <= two_power N /\ be_eq (be_iter1 be m) (be_iter1 be (S m)).
  Proof.
    intros.  replace N with (N - 0).  apply increasing_be_seq_1.  intros.
    apply be_iter1_ok.  assumption.  intros.  apply be_iter1_inc.  assumption.
    elim N; reflexivity.
  Qed.
  
End Be_iter1.

Lemma be_iter1_preserves_eq :
 forall (n : nat) (be1 be2 : bool_expr) (f : bool_expr -> bool_expr),
 (forall be1 be2 : bool_expr, be_eq be1 be2 -> be_eq (f be1) (f be2)) ->
 be_eq be1 be2 -> be_eq (be_iter1 f be1 n) (be_iter1 f be2 n).
Proof.
  simple induction n.  trivial.  simpl in |- *.  intros.  apply H.  intros.  apply H0.
  assumption.  apply H0.  assumption.
Qed.

Lemma be_iter1_plus1 :
 forall (m n : nat) (be : bool_expr) (f : bool_expr -> bool_expr),
 be_eq (be_iter1 f (be_iter1 f be m) n) (be_iter1 f be (m + n)).
Proof.
  intros.  rewrite (be_iter1_plus f m n be).  apply be_eq_refl.
Qed.

Lemma be_iter2n_false :
 forall (n : nat) (be : bool_expr) (f : bool_expr -> bool_expr),
 (forall be1 be2 : bool_expr, be_eq be1 be2 -> be_eq (f be1) (f be2)) ->
 snd (be_iter2n f be n) = false ->
 be_eq (fst (be_iter2n f be n)) (be_iter1 f be (two_power n)).
Proof.
  simple induction n.  simpl in |- *.  intros.  apply be_eq_refl.  unfold be_iter2n in |- *.  simpl in |- *.
  intros.  elim (prod_sum _ _ (iter2n bool_expr be_eq_dec f be n0)).  intros.
  inversion H2.  rewrite H3 in H1.  rewrite H3.  elim (sumbool_of_bool x0).
  intro y.  rewrite y in H1.  discriminate.  intro y.  rewrite y in H1.  rewrite y.
  apply be_eq_trans with (be2 := be_iter1 f x (two_power n0)).  apply H.
  assumption.  assumption.
  apply
   be_eq_trans
    with (be2 := be_iter1 f (be_iter1 f be (two_power n0)) (two_power n0)).
  apply be_iter1_preserves_eq.  assumption.  
  replace x with (fst (iter2n bool_expr be_eq_dec f be n0)).  apply H.
  assumption.  rewrite H3.  assumption.  rewrite H3.  reflexivity.  
  apply be_eq_trans with (be2 := be_iter1 f be (two_power n0 + two_power n0)).
  apply be_iter1_plus1.  rewrite <- (plus_n_O (two_power n0)).  apply be_eq_refl.
Qed.

Lemma be_iter2n_2n :
 forall (n : nat) (be : bool_expr) (f : bool_expr -> bool_expr),
 (forall be1 be2 : bool_expr, be_eq be1 be2 -> be_eq (f be1) (f be2)) ->
 be_eq (fst (be_iter2n f be n)) (be_iter1 f be (two_power n)).
Proof.
  simple induction n.  simpl in |- *.  intros.  apply be_eq_refl.  unfold be_iter2n in |- *.  simpl in |- *.
  intros.  elim (prod_sum _ _ (iter2n bool_expr be_eq_dec f be n0)).  intros.
  inversion H1.  rewrite H2.  elim (sumbool_of_bool x0).  intros y.  rewrite y.
  simpl in |- *.  apply
   be_eq_trans
    with (be2 := be_iter1 f (be_iter1 f be (two_power n0)) (two_power n0)).
  apply be_eq_trans with (be2 := be_iter1 f x (two_power n0)).
  apply be_eq_trans with (be2 := fst (be_iter2n f x n0)).  apply be_iter2n_0.
  assumption.  replace x with (fst (iter2n bool_expr be_eq_dec f be n0)).
  fold (be_iter2n f be n0) in |- *.  apply be_iter2n_true.  assumption.
  unfold be_iter2n in |- *.  rewrite H2.  rewrite y.  reflexivity.  rewrite H2.
  reflexivity.  unfold be_iter2n in |- *.  apply H.  assumption.  
  apply be_iter1_preserves_eq.  assumption.  
  replace x with (fst (iter2n bool_expr be_eq_dec f be n0)).  apply H.
  assumption.  rewrite H2.  reflexivity.  rewrite <- (plus_n_O (two_power n0)).
  apply be_iter1_plus1.  intro y.  rewrite y.
  apply be_eq_trans with (be2 := be_iter1 f x (two_power n0)).  apply H.
  assumption.  rewrite <- (plus_n_O (two_power n0)).
  apply
   be_eq_trans
    with (be2 := be_iter1 f (be_iter1 f be (two_power n0)) (two_power n0)).
  apply be_iter1_preserves_eq.  assumption.  
  replace x with (fst (iter2n bool_expr be_eq_dec f be n0)).  apply H.
  assumption.  rewrite H2.  reflexivity.  apply be_iter1_plus1.
Qed.

Lemma be_iter1_le_preserved :
 forall (n : nat) (be1 be2 : bool_expr) (f1 f2 : bool_expr -> bool_expr),
 be_le be1 be2 ->
 (forall be1' be2' : bool_expr, be_le be1' be2' -> be_le (f1 be1') (f2 be2')) ->
 be_le (be_iter1 f1 be1 n) (be_iter1 f2 be2 n).
Proof.
  simple induction n.  simpl in |- *.  trivial.  simpl in |- *.  intros.  apply H.  apply H1.
  assumption.  assumption.
Qed.

Lemma be_iter2n_le_preserved :
 forall (n : nat) (be1 be2 : bool_expr) (f1 f2 : bool_expr -> bool_expr),
 be_le be1 be2 ->
 (forall be1' be2' : bool_expr, be_eq be1' be2' -> be_eq (f1 be1') (f1 be2')) ->
 (forall be1' be2' : bool_expr, be_eq be1' be2' -> be_eq (f2 be1') (f2 be2')) ->
 (forall be1' be2' : bool_expr, be_le be1' be2' -> be_le (f1 be1') (f2 be2')) ->
 be_le (fst (be_iter2n f1 be1 n)) (fst (be_iter2n f2 be2 n)).
Proof.
  intros n be1 be2 f3 f4 H H0 H1 H2.  apply be_le_trans with (be2 := be_iter1 f3 be1 (two_power n)).
  apply be_eq_le.  apply be_iter2n_2n.  assumption.  
  apply be_le_trans with (be2 := be_iter1 f4 be2 (two_power n)).
  apply be_iter1_le_preserved.  assumption.  assumption.  apply be_eq_le.
  apply be_eq_sym.  apply be_iter2n_2n.  assumption.
Qed.

Fixpoint BDDiter (f : BDDconfig -> ad -> BDDconfig * ad) 
 (cfg : BDDconfig) (node : ad) (n : nat) {struct n} : 
 BDDconfig * ad :=
  match n with
  | O => (cfg, node)
  | S m =>
      match f cfg node with
      | (cfg1, node1) =>
          if Neqb node node1 then (cfg1, node1) else BDDiter f cfg1 node1 m
      end
  end.

Fixpoint BDDiter2n (f : BDDconfig -> ad -> BDDconfig * ad) 
 (cfg : BDDconfig) (node : ad) (n : nat) {struct n} :
 BDDconfig * ad * bool :=
  match n with
  | O =>
      match f cfg node with
      | (cfg1, node1) => (cfg1, node1, Neqb node node1)
      end
  | S m =>
      match BDDiter2n f cfg node m with
      | ((cfg1, node1), true) => (cfg1, node1, true)
      | ((cfg1, node1), false) => BDDiter2n f cfg1 node1 m
      end
  end.

Definition cfgnode_eq (cfgnode1 cfgnode2 : BDDconfig * ad) :=
  Neqb (snd cfgnode1) (snd cfgnode2).

Lemma BDDiter_as_iter :
 forall (n : nat) (cfg : BDDconfig) (node : ad)
   (f : BDDconfig -> ad -> BDDconfig * ad),
 BDDiter f cfg node n =
 iter _ cfgnode_eq (fun x => f (fst x) (snd x)) (cfg, node) n.
Proof.
  simple induction n.  reflexivity.  intros.  simpl in |- *.  elim (prod_sum _ _ (f cfg node)).
  intros cfg1 H0.  elim H0; clear H0.  intros node1 H0.  rewrite H0.
  unfold cfgnode_eq in |- *.  simpl in |- *.  rewrite (H cfg1 node1 f).  reflexivity.  
Qed.

(* (mu_form_ap_ok vf f) means that for all atomic propositions p occurring in f
   (vf ap)=true *)
Inductive mu_form_ap_ok (vf : ad -> bool) : mu_form -> Prop :=
  | mu_0_ok : mu_form_ap_ok vf mu_0
  | mu_1_ok : mu_form_ap_ok vf mu_1
  | mu_ap_ok : forall p : ad, vf p = true -> mu_form_ap_ok vf (mu_ap p)
  | mu_rel_var_ok : forall P : ad, mu_form_ap_ok vf (mu_rel_var P)
  | mu_neg_ok :
      forall f : mu_form, mu_form_ap_ok vf f -> mu_form_ap_ok vf (mu_neg f)
  | mu_and_ok :
      forall f g : mu_form,
      mu_form_ap_ok vf f ->
      mu_form_ap_ok vf g -> mu_form_ap_ok vf (mu_and f g)
  | mu_or_ok :
      forall f g : mu_form,
      mu_form_ap_ok vf f ->
      mu_form_ap_ok vf g -> mu_form_ap_ok vf (mu_or f g)
  | mu_impl_ok :
      forall f g : mu_form,
      mu_form_ap_ok vf f ->
      mu_form_ap_ok vf g -> mu_form_ap_ok vf (mu_impl f g)
  | mu_iff_ok :
      forall f g : mu_form,
      mu_form_ap_ok vf f ->
      mu_form_ap_ok vf g -> mu_form_ap_ok vf (mu_iff f g)
  | mu_all_ok :
      forall (t : ad) (f : mu_form),
      mu_form_ap_ok vf f -> mu_form_ap_ok vf (mu_all t f)
  | mu_ex_ok :
      forall (t : ad) (f : mu_form),
      mu_form_ap_ok vf f -> mu_form_ap_ok vf (mu_ex t f)
  | mu_mu_ok :
      forall (P : ad) (f : mu_form),
      mu_form_ap_ok vf f -> mu_form_ap_ok vf (mu_mu P f).

Lemma mu_ap_ok_inv :
 forall (vf : ad -> bool) (p : ad), mu_form_ap_ok vf (mu_ap p) -> vf p = true.
Proof.
  intros.  inversion H.  assumption.  
Qed.

(* (f_P_even P f true) means that all free occurrences of the relational
   variable P in f are under an even number of negations.
   (f_P_even P f false) means that all free occurrences of the relational 
   variable P in f are under an odd number of negations. *)
Inductive f_P_even (P : ad) : mu_form -> bool -> Prop :=
  | mu_0_even : f_P_even P mu_0 true
  | mu_0_odd : f_P_even P mu_0 false
  | mu_1_even : f_P_even P mu_1 true
  | mu_1_odd : f_P_even P mu_1 false
  | mu_ap_even : forall p : ad, f_P_even P (mu_ap p) true
  | mu_ap_odd : forall p : ad, f_P_even P (mu_ap p) false
  | mu_rel_var_even :
      forall Q : ad,
      f_P_even P (mu_rel_var Q) true
      (* one new clause added ... *)
  | mu_rel_var_odd :
      forall Q : ad, Neqb P Q = false -> f_P_even P (mu_rel_var Q) false
  | mu_neg_odd :
      forall f : mu_form, f_P_even P f true -> f_P_even P (mu_neg f) false
  | mu_neg_even :
      forall f : mu_form, f_P_even P f false -> f_P_even P (mu_neg f) true
  | mu_and_even :
      forall f g : mu_form,
      f_P_even P f true -> f_P_even P g true -> f_P_even P (mu_and f g) true
  | mu_and_odd :
      forall f g : mu_form,
      f_P_even P f false ->
      f_P_even P g false -> f_P_even P (mu_and f g) false
  | mu_or_even :
      forall f g : mu_form,
      f_P_even P f true -> f_P_even P g true -> f_P_even P (mu_or f g) true
  | mu_or_odd :
      forall f g : mu_form,
      f_P_even P f false ->
      f_P_even P g false -> f_P_even P (mu_or f g) false
  | mu_impl_even :
      forall f g : mu_form,
      f_P_even P f false ->
      f_P_even P g true -> f_P_even P (mu_impl f g) true
  | mu_impl_odd :
      forall f g : mu_form,
      f_P_even P f true ->
      f_P_even P g false -> f_P_even P (mu_impl f g) false
  | mu_iff_even :
      forall f g : mu_form,
      f_P_even P f true ->
      f_P_even P g true ->
      f_P_even P f false ->
      f_P_even P g false -> f_P_even P (mu_iff f g) true
  | mu_iff_odd :
      forall f g : mu_form,
      f_P_even P f true ->
      f_P_even P g true ->
      f_P_even P f false ->
      f_P_even P g false -> f_P_even P (mu_iff f g) false
  | mu_all_even :
      forall (t : ad) (f : mu_form),
      f_P_even P f true -> f_P_even P (mu_all t f) true
  | mu_all_odd :
      forall (t : ad) (f : mu_form),
      f_P_even P f false -> f_P_even P (mu_all t f) false
  | mu_ex_even :
      forall (t : ad) (f : mu_form),
      f_P_even P f true -> f_P_even P (mu_ex t f) true
  | mu_ex_odd :
      forall (t : ad) (f : mu_form),
      f_P_even P f false -> f_P_even P (mu_ex t f) false
  | mu_mu_P_even : forall f : mu_form, f_P_even P (mu_mu P f) true
  | mu_mu_P_odd : forall f : mu_form, f_P_even P (mu_mu P f) false
  | mu_mu_Q_even :
      forall (Q : ad) (f : mu_form),
      Neqb P Q = false -> f_P_even P f true -> f_P_even P (mu_mu Q f) true
  | mu_mu_Q_odd :
      forall (Q : ad) (f : mu_form),
      Neqb P Q = false -> f_P_even P f false -> f_P_even P (mu_mu Q f) false.

Inductive f_ok : mu_form -> Prop :=
  | mu_0_f_ok : f_ok mu_0
  | mu_1_f_ok : f_ok mu_1
  | mu_ap_f_ok : forall p : ad, f_ok (mu_ap p)
  | mu_rel_var_f_ok : forall P : ad, f_ok (mu_rel_var P)
  | mu_neg_f_ok : forall f : mu_form, f_ok f -> f_ok (mu_neg f)
  | mu_and_f_ok : forall f g : mu_form, f_ok f -> f_ok g -> f_ok (mu_and f g)
  | mu_or_f_ok : forall f g : mu_form, f_ok f -> f_ok g -> f_ok (mu_or f g)
  | mu_impl_f_ok :
      forall f g : mu_form, f_ok f -> f_ok g -> f_ok (mu_impl f g)
  | mu_iff_f_ok : forall f g : mu_form, f_ok f -> f_ok g -> f_ok (mu_iff f g)
  | mu_all_f_ok : forall (t : ad) (f : mu_form), f_ok f -> f_ok (mu_all t f)
  | mu_ex_f_ok : forall (t : ad) (f : mu_form), f_ok f -> f_ok (mu_ex t f)
  | mu_mu_f_ok :
      forall (P : ad) (f : mu_form),
      f_ok f -> f_P_even P f true -> f_ok (mu_mu P f).

Definition cfg_ul_bre_ok (cfg : BDDconfig) (ul : list ad) 
  (bre : Brel_env) :=
  forall P node : ad, MapGet _ bre P = Some node -> used_node' cfg ul node.

Definition cfg_ul_bte_ok (cfg : BDDconfig) (ul : list ad)
  (bte : Btrans_env) :=
  forall t node : ad, MapGet _ bte t = Some node -> used_node' cfg ul node.

Definition cfg_re_bre_ok (cfg : BDDconfig) (re : rel_env) 
  (bre : Brel_env) :=
  forall P node : ad,
  MapGet _ bre P = Some node ->
  bool_fun_eq (bool_fun_of_BDD cfg node) (bool_fun_of_bool_expr (re P)).

Definition cfg_te_bte_ok (cfg : BDDconfig) (te : trans_env)
  (bte : Btrans_env) :=
  forall t node : ad,
  MapGet _ bte t = Some node ->
  bool_fun_eq (bool_fun_of_BDD cfg node) (bool_fun_of_bool_expr (te t)).

Definition f_bre_ok (f : mu_form) (bre : Brel_env) :=
  forall P : ad, mu_rel_free P f = true -> in_dom _ P bre = true.

Definition f_bte_ok (f : mu_form) (bte : Btrans_env) :=
  forall t : ad, mu_t_free t f = true -> in_dom _ t bte = true.

Lemma mu_and_bre_ok :
 forall (g h : mu_form) (bre : Brel_env),
 f_bre_ok (mu_and g h) bre -> f_bre_ok g bre /\ f_bre_ok h bre.
Proof.
  unfold f_bre_ok in |- *.  simpl in |- *.  auto with bool.
Qed.

Lemma mu_or_bre_ok :
 forall (g h : mu_form) (bre : Brel_env),
 f_bre_ok (mu_or g h) bre -> f_bre_ok g bre /\ f_bre_ok h bre.
Proof.
  unfold f_bre_ok in |- *.  simpl in |- *.  auto with bool.
Qed.

Lemma mu_impl_bre_ok :
 forall (g h : mu_form) (bre : Brel_env),
 f_bre_ok (mu_impl g h) bre -> f_bre_ok g bre /\ f_bre_ok h bre.
Proof.
  unfold f_bre_ok in |- *.  simpl in |- *.  auto with bool.
Qed.

Lemma mu_iff_bre_ok :
 forall (g h : mu_form) (bre : Brel_env),
 f_bre_ok (mu_iff g h) bre -> f_bre_ok g bre /\ f_bre_ok h bre.
Proof.
  unfold f_bre_ok in |- *.  simpl in |- *.  auto with bool.
Qed.

Lemma mu_and_bte_ok :
 forall (g h : mu_form) (bte : Btrans_env),
 f_bte_ok (mu_and g h) bte -> f_bte_ok g bte /\ f_bte_ok h bte.
Proof.
  unfold f_bte_ok in |- *.  simpl in |- *.  auto with bool.
Qed.

Lemma mu_or_bte_ok :
 forall (g h : mu_form) (bte : Btrans_env),
 f_bte_ok (mu_or g h) bte -> f_bte_ok g bte /\ f_bte_ok h bte.
Proof.
  unfold f_bte_ok in |- *.  simpl in |- *.  auto with bool.
Qed.

Lemma mu_impl_bte_ok :
 forall (g h : mu_form) (bte : Btrans_env),
 f_bte_ok (mu_impl g h) bte -> f_bte_ok g bte /\ f_bte_ok h bte.
Proof.
  unfold f_bte_ok in |- *.  simpl in |- *.  auto with bool.
Qed.

Lemma mu_iff_bte_ok :
 forall (g h : mu_form) (bte : Btrans_env),
 f_bte_ok (mu_iff g h) bte -> f_bte_ok g bte /\ f_bte_ok h bte.
Proof.
  unfold f_bte_ok in |- *.  simpl in |- *.  auto with bool.
Qed.

Lemma mu_all_bre_ok :
 forall (t : ad) (g : mu_form) (bre : Brel_env),
 f_bre_ok (mu_all t g) bre -> f_bre_ok g bre.
Proof.
  auto with bool.
Qed.

Lemma mu_all_bte_ok :
 forall (t : ad) (g : mu_form) (bte : Btrans_env),
 f_bte_ok (mu_all t g) bte -> f_bte_ok g bte.
Proof.
  intros.  unfold f_bte_ok in |- *.  intros.  apply H.  simpl in |- *.  rewrite H0.
  elim (Neqb t0 t); reflexivity.
Qed.

Lemma mu_ex_bre_ok :
 forall (t : ad) (g : mu_form) (bre : Brel_env),
 f_bre_ok (mu_ex t g) bre -> f_bre_ok g bre.
Proof.
  auto with bool.
Qed.
 
Lemma mu_ex_bte_ok :
 forall (t : ad) (g : mu_form) (bte : Btrans_env),
 f_bte_ok (mu_ex t g) bte -> f_bte_ok g bte.
Proof.
  intros.  unfold f_bte_ok in |- *.  intros.  apply H.  simpl in |- *.  rewrite H0.
  elim (Neqb t0 t); reflexivity.
Qed.

Lemma mu_mu_bre_ok :
 forall (P node : ad) (g : mu_form) (bre : Brel_env),
 f_bre_ok (mu_mu P g) bre -> f_bre_ok g (MapPut _ bre P node).
Proof.
  intros.  unfold f_bre_ok in |- *.  unfold in_dom in |- *.  intro.
  rewrite (MapPut_semantics ad bre P node P0).
  elim (sumbool_of_bool (Neqb P P0)).  intro y.  rewrite y.  reflexivity.  
  intro y.  rewrite y.  intro.  unfold f_bre_ok in H.  unfold in_dom in H.
  apply H.  simpl in |- *.  rewrite (Neqb_comm P0 P).  rewrite y.  rewrite H0.
  reflexivity.
Qed.

Lemma cfg_ul_re_bre_ok_preserved :
 forall (cfg cfg1 : BDDconfig) (ul : list ad) (re : rel_env) (bre : Brel_env),
 BDDconfig_OK cfg ->
 BDDconfig_OK cfg1 ->
 used_list_OK cfg ul ->
 cfg_ul_bre_ok cfg ul bre ->
 cfg_re_bre_ok cfg re bre ->
 used_nodes_preserved cfg cfg1 ul ->
 cfg_ul_bre_ok cfg1 ul bre /\ cfg_re_bre_ok cfg1 re bre.
Proof.
  unfold cfg_ul_bre_ok, cfg_re_bre_ok in |- *.  intros.  split.  intros.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.  assumption.
  apply H2 with (P := P) (node := node).  assumption.  intros.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg node).
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  assumption.
  assumption.  assumption.  apply H2 with (P := P) (node := node).  assumption.
  apply H3.  assumption.
Qed.

Lemma cfg_ul_te_bte_ok_preserved :
 forall (cfg cfg1 : BDDconfig) (ul : list ad) (te : trans_env)
   (bte : Btrans_env),
 BDDconfig_OK cfg ->
 BDDconfig_OK cfg1 ->
 used_list_OK cfg ul ->
 cfg_ul_bte_ok cfg ul bte ->
 cfg_te_bte_ok cfg te bte ->
 used_nodes_preserved cfg cfg1 ul ->
 cfg_ul_bte_ok cfg1 ul bte /\ cfg_te_bte_ok cfg1 te bte.
Proof.
  unfold cfg_ul_bte_ok, cfg_te_bte_ok in |- *.  intros.  split.  intros.
  apply used_nodes_preserved_used_node' with (cfg := cfg).  assumption.  assumption.
  apply H2 with (t := t) (node := node).  assumption.  intros.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg node).
  apply used_nodes_preserved'_bool_fun with (ul := ul).  assumption.  assumption.
  assumption.  assumption.  apply H2 with (t := t) (node := node).  assumption.
  apply H3.  assumption.
Qed.

Lemma cfg_ul_bre_cons_ok :
 forall (cfg : BDDconfig) (ul : list ad) (bre : Brel_env) (node : ad),
 cfg_ul_bre_ok cfg ul bre -> cfg_ul_bre_ok cfg (node :: ul) bre.
Proof.
  unfold cfg_ul_bre_ok in |- *.  intros.  apply used_node'_cons_node'_ul.
  apply H with (P := P) (node := node0).  assumption.
Qed.

Lemma cfg_ul_bte_cons_ok :
 forall (cfg : BDDconfig) (ul : list ad) (bte : Btrans_env) (node : ad),
 cfg_ul_bte_ok cfg ul bte -> cfg_ul_bte_ok cfg (node :: ul) bte.
Proof.
  unfold cfg_ul_bte_ok in |- *.  intros.  apply used_node'_cons_node'_ul.
  apply H with (t := t) (node := node0).  assumption.
Qed.

Lemma cfg_re_bre_ok_put :
 forall (cfg : BDDconfig) (re : rel_env) (bre : Brel_env) 
   (be : bool_expr) (P node : ad),
 cfg_re_bre_ok cfg re bre ->
 bool_fun_eq (bool_fun_of_BDD cfg node) (bool_fun_of_bool_expr be) ->
 cfg_re_bre_ok cfg (re_put re P be) (MapPut _ bre P node).
Proof.
  intros.  unfold cfg_re_bre_ok in |- *.  unfold re_put in |- *.  intros P0 node0.
  rewrite (MapPut_semantics ad bre P node P0).  elim (Neqb P P0).  intro.
  inversion H1.  rewrite <- H3.  assumption.  intro.  apply H.  assumption.
Qed.

Lemma cfg_ul_bre_ok_put :
 forall (cfg : BDDconfig) (ul : list ad) (bre : Brel_env) (P node : ad),
 cfg_ul_bre_ok cfg ul bre ->
 cfg_ul_bre_ok cfg (node :: ul) (MapPut _ bre P node).
Proof.
  intros.  unfold cfg_ul_bre_ok in |- *.  intros P0 node0.
  rewrite (MapPut_semantics _ bre P node).  elim (sumbool_of_bool (Neqb P P0)).
  intro y.  rewrite y.  intros.  injection H0.  intros.  rewrite <- H1.
  apply used_node'_cons_node_ul.  intro y.  rewrite y.  intro.
  apply used_node'_cons_node'_ul.  apply H with (P := P0).  assumption.  
Qed.

Lemma BDDiter2n_lemma2 :
 forall (te : trans_env) (bte : Btrans_env) (g : mu_form)
   (Bf : mu_form -> BDDconfig -> list ad -> Brel_env -> BDDconfig * ad)
   (f : mu_form -> rel_env -> bool_expr),
 (forall (cfg : BDDconfig) (ul : list ad) (re : rel_env) (bre : Brel_env),
  BDDconfig_OK cfg ->
  used_list_OK cfg ul ->
  cfg_ul_bre_ok cfg ul bre ->
  cfg_re_bre_ok cfg re bre ->
  cfg_ul_bte_ok cfg ul bte ->
  cfg_te_bte_ok cfg te bte ->
  f_bre_ok g bre ->
  f_bte_ok g bte ->
  BDDconfig_OK (fst (Bf g cfg ul bre)) /\
  config_node_OK (fst (Bf g cfg ul bre)) (snd (Bf g cfg ul bre)) /\
  used_nodes_preserved cfg (fst (Bf g cfg ul bre)) ul /\
  bool_fun_eq
    (bool_fun_of_BDD (fst (Bf g cfg ul bre)) (snd (Bf g cfg ul bre)))
    (bool_fun_of_bool_expr (f g re))) ->
 forall (n : nat) (P : ad) (cfg : BDDconfig) (node : ad) 
   (ul : list ad) (be : bool_expr) (re : rel_env) (bre : Brel_env),
 BDDconfig_OK cfg ->
 config_node_OK cfg node ->
 used_list_OK cfg ul ->
 cfg_ul_bre_ok cfg ul bre ->
 cfg_re_bre_ok cfg re bre ->
 cfg_ul_bte_ok cfg ul bte ->
 cfg_te_bte_ok cfg te bte ->
 (forall x : ad, f_bre_ok g (MapPut _ bre P x)) ->
 f_bte_ok g bte ->
 bool_fun_eq (bool_fun_of_BDD cfg node) (bool_fun_of_bool_expr be) ->
 BDDconfig_OK
   (fst
      (fst
         (BDDiter2n
            (fun (cfg0 : BDDconfig) (node0 : ad) =>
             Bf g cfg0 (node0 :: ul) (MapPut ad bre P node0)) cfg node n))) /\
 config_node_OK
   (fst
      (fst
         (BDDiter2n
            (fun (cfg0 : BDDconfig) (node0 : ad) =>
             Bf g cfg0 (node0 :: ul) (MapPut ad bre P node0)) cfg node n)))
   (snd
      (fst
         (BDDiter2n
            (fun (cfg0 : BDDconfig) (node0 : ad) =>
             Bf g cfg0 (node0 :: ul) (MapPut ad bre P node0)) cfg node n))) /\
 used_nodes_preserved cfg
   (fst
      (fst
         (BDDiter2n
            (fun (cfg0 : BDDconfig) (node0 : ad) =>
             Bf g cfg0 (node0 :: ul) (MapPut ad bre P node0)) cfg node n)))
   ul /\
 bool_fun_eq
   (bool_fun_of_BDD
      (fst
         (fst
            (BDDiter2n
               (fun (cfg0 : BDDconfig) (node0 : ad) =>
                Bf g cfg0 (node0 :: ul) (MapPut ad bre P node0)) cfg node n)))
      (snd
         (fst
            (BDDiter2n
               (fun (cfg0 : BDDconfig) (node0 : ad) =>
                Bf g cfg0 (node0 :: ul) (MapPut ad bre P node0)) cfg node n))))
   (bool_fun_of_bool_expr
      (fst
         (iter2n _ be_eq_dec (fun be : bool_expr => f g (re_put re P be)) be
            n))) /\
 snd
   (BDDiter2n
      (fun (cfg0 : BDDconfig) (node0 : ad) =>
       Bf g cfg0 (node0 :: ul) (MapPut ad bre P node0)) cfg node n) =
 snd (iter2n _ be_eq_dec (fun be : bool_expr => f g (re_put re P be)) be n).
Proof.
  intros te bte g Bf f H.  simple induction n.  simpl in |- *.  intros.
  elim (prod_sum _ _ (Bf g cfg (node :: ul) (MapPut ad bre P node))).
  intros cfg1 H11.  elim H11; clear H11.  intros node1 H11.  rewrite H11.
  simpl in |- *.  cut (used_list_OK cfg (node :: ul)).  intro.
  cut (cfg_ul_bre_ok cfg (node :: ul) (MapPut _ bre P node)).  intro.
  cut (cfg_ul_bte_ok cfg (node :: ul) bte).  intro.
  cut (cfg_re_bre_ok cfg (re_put re P be) (MapPut _ bre P node)).  intro.
  elim
   (H cfg (node :: ul) (re_put re P be) (MapPut _ bre P node) H0 H10 H12 H14
      H13 H6 (H7 node) H8).
  rewrite H11.  simpl in |- *.  intros.
  elim H16; intros H18 H17; elim H17; clear H17; intros H17 H20.
  clear H16.
  cut (used_nodes_preserved cfg cfg1 ul).  intro.
  elim (cfg_ul_re_bre_ok_preserved cfg cfg1 ul re bre H0 H15 H2 H3 H4 H16).
  intros.
  elim (cfg_ul_te_bte_ok_preserved cfg cfg1 ul te bte H0 H15 H2 H5 H6 H16).
  intros.  split.  assumption.  split.  assumption.  split.  assumption.  
  split.  assumption.  elim (sumbool_of_bool (Neqb node node1)).  intro y.
  rewrite y.  symmetry  in |- *.  apply be_eq_dec_correct.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg node).
  apply bool_fun_eq_sym; assumption.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg1 node1).
  rewrite <- (Neqb_complete _ _ y).  apply bool_fun_eq_sym.
  apply used_nodes_preserved'_bool_fun with (ul := node :: ul).  assumption.  
  assumption.  assumption.  assumption.  apply used_node'_cons_node_ul.  
  assumption.  intro y.
  elim (sumbool_of_bool (be_eq_dec be (f g (re_put re P be)))).  intro y0.
  cut (Neqb node node1 = true).  intro.  rewrite H24 in y.  discriminate.  
  apply BDDunique with (cfg := cfg1).  assumption.  
  apply used_node'_OK with (ul := node :: ul).  assumption.  
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.  assumption.  
  apply used_node'_cons_node_ul.  assumption.  
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_bool_expr be).
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfg node).
  apply used_nodes_preserved'_bool_fun with (ul := node :: ul).  assumption.
  assumption.  assumption.  assumption.  apply used_node'_cons_node_ul.  
  assumption.  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_of_bool_expr (f g (re_put re P be))).
  apply be_eq_dec_complete.  assumption.  apply bool_fun_eq_sym.  assumption.  
  intro y0.  rewrite y.  rewrite y0.  reflexivity.  
  apply used_nodes_preserved_cons with (node := node).  assumption.
  apply cfg_re_bre_ok_put.  assumption.  assumption.  apply cfg_ul_bte_cons_ok.
  assumption.  apply cfg_ul_bre_ok_put.  assumption.  apply node_OK_list_OK.
  assumption.  assumption.  simpl in |- *.  intros.
  elim
   (prod_sum _ _
      (iter2n bool_expr be_eq_dec
         (fun be0 : bool_expr => f g (re_put re P be0)) be n0)).
  intros.  inversion H11; clear H11.
  elim
   (prod_sum _ _
      (BDDiter2n
         (fun (cfg0 : BDDconfig) (node0 : ad) =>
          Bf g cfg0 (node0 :: ul) (MapPut ad bre P node0)) cfg node n0)).
  intros.  inversion H11.  elim (prod_sum _ _ x1).  intros.  inversion H14.
  clear H11 H14.  elim (H0 P cfg node ul be re bre H1 H2 H3 H4 H5 H6 H7 H8 H9 H10).
  intros.  rewrite H12.  rewrite H13.  simpl in |- *.  rewrite H15.  simpl in |- *.
  elim (sumbool_of_bool x2).  intro y.  rewrite y.  simpl in |- *.  rewrite H12 in H14.
  rewrite H13 in H14.  rewrite H13 in H11.  simpl in H11, H14.
  rewrite H15 in H11.  rewrite H15 in H14.  simpl in H11, H14.
  elim H14; intros H17 H16; elim H16; clear H16; intros H16 H18; elim H18;
   clear H18; intros H18 H20.
  split.  assumption.  split.  assumption.  split.
  assumption.  rewrite <- H20.  rewrite y.  split.  assumption.  reflexivity.  
  intro y; rewrite y.  rewrite H12 in H14.  rewrite H13 in H11.
  rewrite H13 in H14.  rewrite H15 in H14.  rewrite H15 in H11.
  simpl in H11, H14.
  elim H14; intros H17 H16; elim H16; clear H16; intros H16 H18; elim H18;
   clear H18; intros H18 H20. 
  rewrite <- H20.  rewrite y.
  cut (used_list_OK x3 ul).  intro.
  elim (cfg_ul_re_bre_ok_preserved cfg x3 ul re bre H1 H11 H3 H4 H5 H16).
  intros.  elim (cfg_ul_te_bte_ok_preserved cfg x3 ul te bte H1 H11 H3 H6 H7 H16).
  intros.  elim (H0 P x3 x4 ul x re bre H11 H17 H19 H21 H22 H23 H24 H8 H9 H18).
  intros.  split.  assumption.  decompose [and] H26.  split.  assumption.  
  split.  apply used_nodes_preserved_trans with (cfg2 := x3).  assumption.  
  assumption.  assumption.  split.  assumption.  assumption.  
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.  assumption.
Qed.

Lemma BDDiter2n_lemma1 :
 forall (te : trans_env) (bte : Btrans_env) (g : mu_form)
   (Bf : mu_form -> BDDconfig -> list ad -> Brel_env -> BDDconfig * ad)
   (f : mu_form -> rel_env -> bool_expr),
 (forall (cfg : BDDconfig) (ul : list ad) (re : rel_env) (bre : Brel_env),
  BDDconfig_OK cfg ->
  used_list_OK cfg ul ->
  cfg_ul_bre_ok cfg ul bre ->
  cfg_re_bre_ok cfg re bre ->
  cfg_ul_bte_ok cfg ul bte ->
  cfg_te_bte_ok cfg te bte ->
  f_bre_ok g bre ->
  f_bte_ok g bte ->
  BDDconfig_OK (fst (Bf g cfg ul bre)) /\
  config_node_OK (fst (Bf g cfg ul bre)) (snd (Bf g cfg ul bre)) /\
  used_nodes_preserved cfg (fst (Bf g cfg ul bre)) ul /\
  bool_fun_eq
    (bool_fun_of_BDD (fst (Bf g cfg ul bre)) (snd (Bf g cfg ul bre)))
    (bool_fun_of_bool_expr (f g re))) ->
 forall (n : nat) (P : ad) (cfg : BDDconfig) (node : ad) 
   (ul : list ad) (be : bool_expr) (re : rel_env) (bre : Brel_env),
 BDDconfig_OK cfg ->
 config_node_OK cfg node ->
 used_list_OK cfg ul ->
 cfg_ul_bre_ok cfg ul bre ->
 cfg_re_bre_ok cfg re bre ->
 cfg_ul_bte_ok cfg ul bte ->
 cfg_te_bte_ok cfg te bte ->
 (forall x : ad, f_bre_ok g (MapPut _ bre P x)) ->
 f_bte_ok g bte ->
 bool_fun_eq (bool_fun_of_BDD cfg node) (bool_fun_of_bool_expr be) ->
 BDDconfig_OK
   (fst
      (fst
         (BDDiter2n
            (fun (cfg0 : BDDconfig) (node0 : ad) =>
             Bf g cfg0 (node0 :: ul) (MapPut ad bre P node0)) cfg node n))) /\
 config_node_OK
   (fst
      (fst
         (BDDiter2n
            (fun (cfg0 : BDDconfig) (node0 : ad) =>
             Bf g cfg0 (node0 :: ul) (MapPut ad bre P node0)) cfg node n)))
   (snd
      (fst
         (BDDiter2n
            (fun (cfg0 : BDDconfig) (node0 : ad) =>
             Bf g cfg0 (node0 :: ul) (MapPut ad bre P node0)) cfg node n))) /\
 used_nodes_preserved cfg
   (fst
      (fst
         (BDDiter2n
            (fun (cfg0 : BDDconfig) (node0 : ad) =>
             Bf g cfg0 (node0 :: ul) (MapPut ad bre P node0)) cfg node n)))
   ul /\
 bool_fun_eq
   (bool_fun_of_BDD
      (fst
         (fst
            (BDDiter2n
               (fun (cfg0 : BDDconfig) (node0 : ad) =>
                Bf g cfg0 (node0 :: ul) (MapPut ad bre P node0)) cfg node n)))
      (snd
         (fst
            (BDDiter2n
               (fun (cfg0 : BDDconfig) (node0 : ad) =>
                Bf g cfg0 (node0 :: ul) (MapPut ad bre P node0)) cfg node n))))
   (bool_fun_of_bool_expr
      (fst
         (iter2n _ be_eq_dec (fun be : bool_expr => f g (re_put re P be)) be
            n))).
Proof.
  intros.  elim (BDDiter2n_lemma2 te bte g Bf f H n P cfg node ul be re bre).
  intros.  decompose [and] H11.  split.  assumption.  split.  assumption.  
  split.  assumption.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  assumption.  assumption.  assumption.
  assumption.
Qed.

Section MuEval.

Variable gc : BDDconfig -> list ad -> BDDconfig.
Hypothesis gc_is_OK : gc_OK gc.

Variable te : trans_env.
Variable bte : Btrans_env.

(* semantics for mu_calculus formulae; but the fixpoint operator is instead
   interpreted as iteration of a function atmost 2^n times *)
Fixpoint mu_eval (f : mu_form) : rel_env -> bool_expr :=
  fun re =>
  match f with
  | mu_0 => Zero
  | mu_1 => One
  | mu_ap p => Var p
  | mu_rel_var P => re P
  | mu_neg g => Neg (mu_eval g re)
  | mu_and g h => ANd (mu_eval g re) (mu_eval h re)
  | mu_or g h => Or (mu_eval g re) (mu_eval h re)
  | mu_impl g h => Impl (mu_eval g re) (mu_eval h re)
  | mu_iff g h => Iff (mu_eval g re) (mu_eval h re)
  | mu_all t g => mu_all_eval N (te t) (mu_eval g re)
  | mu_ex t g => mu_ex_eval N (te t) (mu_eval g re)
  | mu_mu P g =>
      fst (iter2n _ be_eq_dec (fun be => mu_eval g (re_put re P be)) Zero N)
  end.

Definition re_to_be_inc (f : rel_env -> bool_expr) 
  (P : ad) :=
  forall (re : rel_env) (be1 be2 : bool_expr),
  be_le be1 be2 -> be_le (f (re_put re P be1)) (f (re_put re P be2)).

Definition re_to_be_dec (f : rel_env -> bool_expr) 
  (P : ad) :=
  forall (re : rel_env) (be1 be2 : bool_expr),
  be_le be1 be2 -> be_le (f (re_put re P be2)) (f (re_put re P be1)).

Definition ad_to_be_ok (vf : ad -> bool) (abe : ad -> bool_expr) :=
  forall x : ad, be_ok vf (abe x).

Definition ad_to_be_eq (f1 f2 : ad -> bool_expr) :=
  forall x : ad, be_eq (f1 x) (f2 x).

Hypothesis te_ok : ad_to_be_ok (var_lu 0 (2 * N)) te.

Lemma mu_all_eval_lu :
 forall t be : bool_expr,
 be_ok (var_lu 0 (2 * N)) t ->
 be_ok (var_lu 0 N) be -> be_ok (var_lu 0 N) (mu_all_eval N t be). 
Proof.
  intros.  apply be_x_free_be_ok.  intros.  elim (mu_all_x_free _ _ _ _ H1).
  intros.  elim H3.  intro.  cut (var_lu 0 (2 * N) x = true).  intro.
  unfold var_lu in H5.  elim (andb_prop _ _ H5).  intros.  unfold var_lu in |- *.
  rewrite H6.  unfold andb in |- *.  unfold ifb in |- *.  apply not_false_is_true.
  unfold not in |- *; intro.  apply H2.  replace x with (N_of_nat (nat_of_N x)).
  apply in_lx'.  apply le_S_n.  fold (N < S (nat_of_N x)) in |- *.
  apply leb_complete_conv.  assumption.  apply leb_complete.  assumption.
  apply N_of_nat_of_N.  apply be_ok_be_x_free with (be := t).  assumption.  
  assumption.  intros.  decompose [and] H4.  apply be_ok_be_x_free with (be := be).
  assumption.  assumption.  
Qed.

Lemma mu_ex_eval_lu :
 forall t be : bool_expr,
 be_ok (var_lu 0 (2 * N)) t ->
 be_ok (var_lu 0 N) be -> be_ok (var_lu 0 N) (mu_ex_eval N t be).
Proof.
  intros.  apply be_x_free_be_ok.  intros.  elim (mu_ex_x_free _ _ _ _ H1).
  intros.  elim H3.  intro.  cut (var_lu 0 (2 * N) x = true).  intro.
  unfold var_lu in H5.  elim (andb_prop _ _ H5).  intros.  unfold var_lu in |- *.
  rewrite H6.  unfold andb in |- *.  unfold ifb in |- *.  apply not_false_is_true.
  unfold not in |- *; intro.  apply H2.  replace x with (N_of_nat (nat_of_N x)).
  apply in_lx'.  apply le_S_n.  fold (N < S (nat_of_N x)) in |- *.
  apply leb_complete_conv.  assumption.  apply leb_complete.  assumption.
  apply N_of_nat_of_N.  apply be_ok_be_x_free with (be := t).  assumption.
  assumption.  intros.  decompose [and] H4.  apply be_ok_be_x_free with (be := be).
  assumption.  assumption.
Qed.


Definition ad_to_be_eq1 (f : mu_form) (f1 f2 : ad -> bool_expr) :=
  forall x : ad, mu_rel_free x f = true -> be_eq (f1 x) (f2 x).

Lemma mu_eval_lemma2 :
 forall f : mu_form,
 f_ok f ->
 mu_form_ap_ok (var_lu 0 N) f ->
 (forall re : rel_env,
  ad_to_be_ok (var_lu 0 N) re -> be_ok (var_lu 0 N) (mu_eval f re)) /\
 (forall P : ad, f_P_even P f true -> re_to_be_inc (mu_eval f) P) /\
 (forall P : ad, f_P_even P f false -> re_to_be_dec (mu_eval f) P) /\
 (forall re1 re2 : rel_env,
  ad_to_be_eq1 f re1 re2 -> be_eq (mu_eval f re1) (mu_eval f re2)).
Proof.
  simple induction f.
  simpl in |- *.  intros.  split.  intros.  apply zero_ok.  split.  intros.
  unfold re_to_be_inc in |- *.  intros.  apply be_le_refl.  split.  unfold re_to_be_dec in |- *.
  intros.  apply be_le_refl.  intros.  apply be_eq_refl.
  simpl in |- *.  intros.  split.  intros.  apply one_ok.  split.  intros.
  unfold re_to_be_inc in |- *.  intros.  apply be_le_refl.  split.  unfold re_to_be_dec in |- *.
  intros.  apply be_le_refl.  intros.  apply be_eq_refl.
  simpl in |- *.  intros.  split.  intros.  apply var_ok.  apply mu_ap_ok_inv.
  assumption.  unfold re_to_be_inc in |- *.  split.  intros.  apply be_le_refl.  split.
  unfold re_to_be_dec in |- *.  intros.  apply be_le_refl.  intros.  apply be_eq_refl.
  simpl in |- *.  intros.  split.  intros.  apply H1.  split.  intros.
  unfold re_to_be_inc in |- *.  intros.  unfold re_put in |- *.  elim (Neqb P a).  assumption.
  apply be_le_refl.  split.  intros.  inversion H1.  unfold re_to_be_dec in |- *.
  unfold re_put in |- *.  rewrite H3.  intros.  apply be_le_refl.  intros.
  apply H1.  simpl in |- *.  apply Neqb_correct.
  simpl in |- *.  intros.  elim H.  clear H.  intros.  split.  intros.  apply neg_ok.
  apply H.  assumption.  split.  unfold re_to_be_inc in |- *.  intros.
  apply be_le_not_1.  unfold re_to_be_dec in H2.
  apply (proj1 (proj2 H2)).  inversion H3.  assumption.  assumption.  
  split.  unfold re_to_be_dec in |- *.  intros.  unfold re_to_be_inc in H2.
  apply be_le_not_1.  apply (proj1 H2).  inversion H3.  assumption.  
  assumption.  intros.  apply eq_neg_eq.  apply (proj2 (proj2 H2)).
  assumption.  inversion H0.  assumption.  inversion H1.  assumption.
  simpl in |- *.  intros.  inversion H1.  clear H3 H4.  clear f0 g.  inversion H2.
  clear H3 H4.  clear f0 g.
  elim (H H5 H7); clear H; intros H4 H3; elim H3; clear H3; intros H3 H9;
   elim H9; clear H9; intros H9 H11.
  elim (H0 H6 H8); clear H0; intros H10 H; elim H; clear H; intros H H12;
   elim H12; clear H12; intros H12 H14.

  split.  intros.  apply and_ok.
  apply H4.  assumption.  apply H10.  assumption.  split.  intros.
  unfold re_to_be_inc in |- *.  intros.  inversion H0.  clear H15 H16.  clear f0 g.
  apply and_le.  unfold re_to_be_inc in H3.  apply H3.  assumption.  assumption.
  unfold re_to_be_inc in H.  apply H.  assumption.  assumption.  split.  intros.
  unfold re_to_be_dec in |- *.  intros.  inversion H0.  clear H15 H16.  clear f0 g.
  apply and_le.  unfold re_to_be_dec in H9.  apply H9.  assumption.  assumption.
  unfold re_to_be_dec in H12.  apply H12.  assumption.  assumption.  intros.
  apply and_eq.  apply H11.  unfold ad_to_be_eq1 in |- *.  intros.  apply H0.  simpl in |- *.
  rewrite H13.  reflexivity.  apply H14.  unfold ad_to_be_eq1 in |- *.  intros.
  apply H0.  simpl in |- *.  rewrite H13.  auto with bool. (* end and *)
  simpl in |- *.  intros.  inversion H1.  clear H3 H4.  clear f0 g.  inversion H2.
  clear H3 H4.  clear f0 g.
  elim (H H5 H7); clear H; intros H4 H3; elim H3; clear H3; intros H3 H9;
   elim H9; clear H9; intros H9 H11.
  elim (H0 H6 H8); clear H0; intros H10 H; elim H; clear H; intros H H12;
   elim H12; clear H12; intros H12 H14.
  split.  intros.  apply or_ok.
  apply H4.  assumption.  apply H10.  assumption.  split.  intros.
  unfold re_to_be_inc in |- *.  intros.  inversion H0.  clear H15 H16.  clear f0 g.
  apply or_le.  unfold re_to_be_inc in H3.  apply H3.  assumption.  assumption.
  unfold re_to_be_inc in H.  apply H.  assumption.  assumption.  split.  intros.
  unfold re_to_be_dec in |- *.  intros.  inversion H0.  clear H15 H16.  clear f0 g.
  apply or_le.  unfold re_to_be_dec in H9.  apply H9.  assumption.  assumption.
  unfold re_to_be_dec in H12.  apply H12.  assumption.  assumption.  intros.
  apply or_eq.  apply H11.  unfold ad_to_be_eq1 in |- *.  intros.  apply H0.  simpl in |- *.
  rewrite H13.  reflexivity.  apply H14.  unfold ad_to_be_eq1 in |- *.  intros.
  apply H0.  simpl in |- *.  rewrite H13.  auto with bool. (* end or *)
  simpl in |- *.  intros.  inversion H1.  clear H3 H4.  clear f0 g.  inversion H2.
  clear H3 H4.  clear f0 g.
  elim (H H5 H7); clear H; intros H4 H3; elim H3; clear H3; intros H3 H9;
   elim H9; clear H9; intros H9 H11.
  elim (H0 H6 H8); clear H0; intros H10 H; elim H; clear H; intros H H12;
   elim H12; clear H12; intros H12 H14.

  split.  intros.  apply impl_ok.
  apply H4.  assumption.  apply H10.  assumption.  split.  intros.
  unfold re_to_be_inc in |- *.  intros.  inversion H0.  clear H15 H16.  clear f0 g.
  apply impl_le.  unfold re_to_be_dec in H9.  apply H9.  assumption.  assumption. 
  unfold re_to_be_inc in H.  apply H.  assumption.  assumption.  split.  intros.
  unfold re_to_be_dec in |- *.  intros.  inversion H0.  clear H15 H16.  clear f0 g.
  apply impl_le.  unfold re_to_be_inc in H3.  apply H3.  assumption.  assumption. 
  unfold re_to_be_dec in H12.  apply H12.  assumption.  assumption.  intros.
  apply impl_eq.  apply H11.  unfold ad_to_be_eq1 in |- *.  intros.  apply H0.  simpl in |- *.
  rewrite H13.  reflexivity.  apply H14.  unfold ad_to_be_eq1 in |- *.  intros.
  apply H0.  simpl in |- *.  rewrite H13.  auto with bool. (*end impl*)
  simpl in |- *.  intros.  inversion H1.  clear H3 H4.  clear f0 g.  inversion H2.
  clear H3 H4.  clear f0 g.
  elim (H H5 H7); clear H; intros H4 H3; elim H3; clear H3; intros H3 H9;
   elim H9; clear H9; intros H9 H11.
  elim (H0 H6 H8); clear H0; intros H10 H; elim H; clear H; intros H H12;
   elim H12; clear H12; intros H12 H14.

  split.  intros.  apply iff_ok.
  apply H4.  assumption.  apply H10.  assumption.  unfold re_to_be_inc in |- *.
  unfold re_to_be_dec in |- *.  unfold re_to_be_inc in H3.  unfold re_to_be_inc in H.
  unfold re_to_be_dec in H9.  unfold re_to_be_dec in H12.  split.  intros.
  inversion H0.  clear H15 H16 f0 g.  apply be_eq_le.  apply iff_eq.
  apply be_le_antisym.  apply H3.  assumption.  assumption.  apply H9.
  assumption.  assumption.  apply be_le_antisym.  apply H.  assumption.
  assumption.  apply H12.  assumption.  assumption.  split.  intros.
  inversion H0.  clear H15 H16 f0 g.  apply be_eq_le.  apply iff_eq.
  apply be_le_antisym.  apply H9.  assumption.  assumption.  apply H3.
  assumption.  assumption.  apply be_le_antisym.  apply H12.  assumption.  
  assumption.  apply H.  assumption.  assumption.  intros.
  apply iff_eq.  apply H11.  unfold ad_to_be_eq1 in |- *.  intros.  apply H0.  simpl in |- *.
  rewrite H13.  reflexivity.  apply H14.  unfold ad_to_be_eq1 in |- *.  intros.
  apply H0.  simpl in |- *.  rewrite H13.  auto with bool. (* end iff *) 
  simpl in |- *.  intros.  inversion H0.  clear H2 H4 t f0.  inversion H1.
  clear H2 H5 t f0.
  elim (H H3 H4); clear H; intros H5 H2; elim H2; clear H2; intros H2 H6;
   elim H6; clear H6; intros H6 H8.
  split.  intros.
  apply mu_all_eval_lu.  apply te_ok.  apply H5.  assumption.  split.  intros.
  inversion H.
  clear H7 H10 t f0.
  unfold re_to_be_inc in |- *.  intros.
  apply mu_all_le.  unfold re_to_be_inc in H2.  apply H2.  assumption.  
  assumption.  split.  intros.  inversion H.
  clear H7 H10 t f0.
  unfold re_to_be_dec in |- *.  intros.  apply mu_all_le.  unfold re_to_be_dec in H6.
  apply H6.  assumption.  assumption.  intros.  apply mu_all_eq.  apply H8.
  assumption.
  simpl in |- *.  intros.  inversion H0.  clear H2 H4 t f0.  inversion H1.
  clear H2 H5 t f0.
  elim (H H3 H4); clear H; intros H5 H2; elim H2; clear H2; intros H2 H6;
   elim H6; clear H6; intros H6 H8.
  split.  intros.
  apply mu_ex_eval_lu.  apply te_ok.  apply H5.  assumption.  split.  intros.
  inversion H.
  clear H7 H10 t f0.
  unfold re_to_be_inc in |- *.  intros.
  apply mu_ex_le.  unfold re_to_be_inc in H2.  apply H2.  assumption.
  assumption.  split.  intros.  inversion H.
  clear H7 H10 t f0.
  unfold re_to_be_dec in |- *.  intros.  apply mu_ex_le.  unfold re_to_be_dec in H6.
  apply H6.  assumption.  assumption.  intros.  apply mu_ex_eq.  apply H8.
  assumption.
  simpl in |- *.  intros.  inversion H0.  clear H2 H3 P f0.
  inversion H1.  clear H2 H6 P f0.
  elim (H H4 H3); clear H; intros H6 H2; elim H2; clear H2; intros H2 H7;
   elim H7; clear H7; intros H7 H9.
  split.  intros.
  fold (be_iter2n (fun be : bool_expr => mu_eval m (re_put re a be)) Zero N)
   in |- *.
  apply be_iter2n_prop_preserved.  apply zero_ok.  intros.  apply H6.
  unfold re_put in |- *.  unfold ad_to_be_ok in |- *.  intros.  elim (Neqb a x).  assumption.  
  apply H.  split.
  intros.  unfold re_to_be_inc in |- *.  intros.
  fold
   (be_iter2n
      (fun be : bool_expr => mu_eval m (re_put (re_put re P be1) a be)) Zero
      N) in |- *.
  fold
   (be_iter2n
      (fun be : bool_expr => mu_eval m (re_put (re_put re P be2) a be)) Zero
      N) in |- *.
  unfold re_to_be_inc in H2.  inversion H.  clear H12 H11 f0.
  apply be_eq_le.
  apply be_iter2n_eq_preserved_2.  apply be_eq_refl.  intros.
  apply H9.  unfold ad_to_be_eq in |- *.  unfold re_put in |- *.  intro.  elim (Neqb a x).
  intros.  assumption.  intros.  apply be_eq_refl.  intros.  apply H9.
  unfold ad_to_be_eq1 in |- *. intros.
  unfold re_put in |- *.  intro.  elim (Neqb a x).  apply H10.  reflexivity.
  intros.  apply H9.  unfold ad_to_be_eq1 in |- *.  unfold re_put in |- *.  intro.
  elim (Neqb a x).  intros.  assumption.  intros.  apply be_eq_refl.
  rename H13 into H14.
  apply be_iter2n_le_preserved.
  apply be_le_refl.  intros.  apply H9.  unfold re_put at 1 3 in |- *.  unfold ad_to_be_eq1 in |- *.
  intro.  elim (Neqb a x).  intros.  assumption.  intros.  apply be_eq_refl.
  intros.  apply H9.
  unfold re_put at 1 3 in |- *.  unfold ad_to_be_eq1 in |- *.  intro.  elim (Neqb a x).
  intros.  assumption.  intros.  apply be_eq_refl.  intros.
  apply be_le_trans with (be2 := mu_eval m (re_put (re_put re P be1) a be2')).
  apply H2.  assumption.  assumption.  
  apply be_le_trans with (be2 := mu_eval m (re_put (re_put re a be2') P be1)).
  rename H13 into H15.
  apply be_eq_le.  apply H9.  unfold ad_to_be_eq1 in |- *.  intro.  unfold re_put in |- *.
  elim (sumbool_of_bool (Neqb P x)).  intros y H16.  rewrite y.
  cut (Neqb a x = false).
  intro H17.
  rewrite H17.  apply be_eq_refl.  
  rewrite <- (Neqb_complete _ _ y).  rewrite (Neqb_comm a P).  assumption.  
  intros y H16.  rewrite y.  apply be_eq_refl.  
  apply be_le_trans with (be2 := mu_eval m (re_put (re_put re a be2') P be2)).
  apply H2.  assumption.  assumption.  apply be_eq_le.  apply H9.
  unfold ad_to_be_eq1 in |- *.  intro.  unfold re_put in |- *.
  elim (sumbool_of_bool (Neqb P x)).
  intros y H16.
  rewrite y.
  cut (Neqb a x = false).
  intro H17.
  rewrite H17.  apply be_eq_refl.  
  rewrite <- (Neqb_complete _ _ y).  rewrite (Neqb_comm a P).  assumption.  
  intros y H16.  rewrite y.  apply be_eq_refl.  split.
  intros.  unfold re_to_be_dec in |- *.  intros.
  unfold re_to_be_dec in H7.  inversion H.  clear H12 H11 f0.
  apply be_eq_le.
  fold
   (be_iter2n
      (fun be : bool_expr => mu_eval m (re_put (re_put re a be2) a be)) Zero
      N) in |- *.
  fold
   (be_iter2n
      (fun be : bool_expr => mu_eval m (re_put (re_put re a be1) a be)) Zero
      N) in |- *.
  apply be_iter2n_eq_preserved_2.  apply be_eq_refl.  intros.
  apply H9.  unfold ad_to_be_eq1 in |- *.  unfold re_put in |- *.  intro.  elim (Neqb a x).
  intros.  assumption.  intros.  apply be_eq_refl.  intros.  apply H9.
  unfold ad_to_be_eq1 in |- *.
  unfold re_put in |- *.  intros.  elim (Neqb a x).  assumption.  apply be_eq_refl.
  intros.  apply H9.  unfold ad_to_be_eq1 in |- *.  unfold re_put in |- *.  intros.
  elim (Neqb a x).  assumption.  apply be_eq_refl.
  fold
   (be_iter2n
      (fun be : bool_expr => mu_eval m (re_put (re_put re P be2) a be)) Zero
      N) in |- *.
  fold
   (be_iter2n
      (fun be : bool_expr => mu_eval m (re_put (re_put re P be1) a be)) Zero
      N) in |- *.
  apply be_iter2n_le_preserved.
  apply be_le_refl.  intros.  apply H9.  unfold re_put at 1 3 in |- *.  unfold ad_to_be_eq1 in |- *.
  intros.  elim (Neqb a x).  assumption.  apply be_eq_refl.  intros.  apply H9.
  unfold re_put at 1 3 in |- *.  unfold ad_to_be_eq1 in |- *.  intros.  elim (Neqb a x).
  assumption.  apply be_eq_refl.  intros.
  apply be_le_trans with (be2 := mu_eval m (re_put (re_put re P be2) a be2')).
  unfold re_to_be_inc in H2.  apply H2.  assumption.  assumption.
  apply be_le_trans with (be2 := mu_eval m (re_put (re_put re a be2') P be2)).
  apply be_eq_le.  apply H9.  unfold ad_to_be_eq1 in |- *.  intros.  unfold re_put in |- *.
  elim (sumbool_of_bool (Neqb P x)).  intro y.  rewrite y.
  cut (Neqb a x = false).
  intro H17.
  rewrite H17.  apply be_eq_refl.
  rewrite <- (Neqb_complete _ _ y).  rewrite (Neqb_comm a P).  assumption.
  intro y.  rewrite y.  apply be_eq_refl.
  apply be_le_trans with (be2 := mu_eval m (re_put (re_put re a be2') P be1)).
  apply H7.  assumption.  assumption.  apply be_eq_le.  apply H9.
  unfold ad_to_be_eq1 in |- *.  intros.  unfold re_put in |- *.
  elim (sumbool_of_bool (Neqb P x)).  intro y.  rewrite y.
  cut (Neqb a x = false).
  intro H17.
  rewrite H17.  apply be_eq_refl.
  rewrite <- (Neqb_complete _ _ y).  rewrite (Neqb_comm a P).  assumption.
  intro y.  rewrite y.  apply be_eq_refl.  intros.
  fold (be_iter2n (fun be : bool_expr => mu_eval m (re_put re1 a be)) Zero N)
   in |- *.
  fold (be_iter2n (fun be : bool_expr => mu_eval m (re_put re2 a be)) Zero N)
   in |- *.
  apply be_iter2n_eq_preserved_2.  apply be_eq_refl. 
  intros.  apply H9.  unfold ad_to_be_eq1, re_put in |- *.  intros.  elim (Neqb a x).
  assumption.  apply be_eq_refl.  intros.  apply H9.  unfold ad_to_be_eq1, re_put in |- *.
  intros.  elim (Neqb a x).  assumption.  apply be_eq_refl.  intros.  apply H9.
  unfold ad_to_be_eq1, re_put in |- *.  intros.  elim (sumbool_of_bool (Neqb a x)).
  intro y.  rewrite y.  assumption.  intro y.  rewrite y.  apply H.  simpl in |- *.
  rewrite (Neqb_comm x a).  rewrite y.  rewrite H10.  reflexivity.  
Qed.

Lemma mu_eval_lemma1 :
 forall f : mu_form,
 f_ok f ->
 mu_form_ap_ok (var_lu 0 N) f ->
 (forall re : rel_env,
  ad_to_be_ok (var_lu 0 N) re -> be_ok (var_lu 0 N) (mu_eval f re)) /\
 (forall P : ad, f_P_even P f true -> re_to_be_inc (mu_eval f) P) /\
 (forall P : ad, f_P_even P f false -> re_to_be_dec (mu_eval f) P) /\
 (forall re1 re2 : rel_env,
  ad_to_be_eq re1 re2 -> be_eq (mu_eval f re1) (mu_eval f re2)).
Proof.
  intros.  elim (mu_eval_lemma2 f H H0).  intros.
  elim H2; intros H4 H3; elim H3; clear H3; intros H3 H6.
  split.  assumption.  split.  assumption.  split.  assumption.  intros.
  apply H6.  unfold ad_to_be_eq1 in |- *.  intros.  apply H5.
Qed.

Lemma lfp_be_lfp :
 forall (bef : bool_expr -> bool_expr) (be : bool_expr),
 lfp bef be <-> lfp_be bef Zero be.
Proof.
  unfold lfp, lfp_be in |- *.  intros.  unfold be_le in |- *.  unfold eval_be' in |- *.  simpl in |- *.
  unfold bool_fun_zero in |- *.  split.  intro.
  elim H; intros H1 H2.
  split.  assumption.
  split.  intros.  discriminate.  intros.  apply H2.  assumption.  assumption.
  intro.
  elim H; intros H1 H0; elim H0; clear H0; intros H0 H3.

  split.  assumption.  intros.  apply H3.
  assumption.  intros.  discriminate.  assumption.  
Qed.

Lemma be_iter_is_lfp_be :
 forall (bef : bool_expr -> bool_expr) (n : nat) (be : bool_expr),
 be_le be (bef be) ->
 (forall be1 be2 : bool_expr, be_eq be1 be2 -> be_eq (bef be1) (bef be2)) ->
 (forall be1 be2 : bool_expr, be_le be1 be2 -> be_le (bef be1) (bef be2)) ->
 (exists m : nat, m <= n /\ be_eq (be_iter1 bef be m) (be_iter1 bef be (S m))) ->
 lfp_be bef be (be_iter bef be n).
Proof.
  intro.  simple induction n.  intros be H01 H02 H00 H.  elim H.  intros.
  elim H0; intros H2 H3.

  cut (x = 0).  intro.  rewrite H1 in H3.  simpl in H3.
  unfold lfp_be in |- *.  split.  unfold fp in |- *.  unfold be_iter in |- *.  simpl in |- *.  assumption.  
  split.  unfold be_iter in |- *.  simpl in |- *.  apply be_le_refl.  unfold be_iter in |- *.  simpl in |- *.
  trivial.  symmetry  in |- *.  apply le_n_O_eq.  assumption.  simpl in |- *.
  intros n0 H be H01 H02 H00 H0.  elim H0.  intros.
  elim H1; intros H3 H4.
  elim (H (bef be)).  intros.
  elim H5; intros H7 H8.
  unfold be_iter in |- *.  simpl in |- *.
  elim (sumbool_of_bool (be_eq_dec be (bef be))).  intro y.  rewrite y.  split.
  unfold fp in |- *.  apply H02.  apply be_eq_dec_eq.  assumption.  split.  assumption.
  intros.  apply be_le_trans with (be2 := be).  apply be_eq_le.  apply be_eq_sym.
  apply be_eq_dec_eq.  assumption.  assumption.  intro y.  rewrite y.  split.
  exact H2.  split.  apply be_le_trans with (be2 := bef be).  assumption.  
  exact H7.  intros.  apply H8.  assumption.
  apply be_le_trans with (be2 := bef be').  apply H00.  assumption.
  apply be_eq_le.  unfold fp in H6.  apply be_eq_sym.  assumption.  apply H00.
  assumption.  assumption.  assumption.  elim (O_or_S x).  intro y.  elim y.
  intros x0 y0.  split with x0.  split.  apply le_S_n.  rewrite y0.  assumption.  
  rewrite <- y0 in H4.  simpl in H4.  assumption.  intro y.  split with 0.  split.
  apply le_O_n.  simpl in |- *.  rewrite <- y in H4.  simpl in H4.  apply H02.  
  assumption.
Qed.

Lemma be_iter1_n_le :
 forall (n : nat) (be : bool_expr) (bef : bool_expr -> bool_expr),
 n <> 0 ->
 (forall be1 be2 : bool_expr, be_le be1 be2 -> be_le (bef be1) (bef be2)) ->
 be_le be (bef be) -> be_le be (be_iter1 bef be n).
Proof.
  simple induction n.  intros.  elim (H (refl_equal _)).  intro.  elim n0.  simpl in |- *.
  trivial.  intros.  apply be_le_trans with (be2 := be_iter1 bef be (S n1)).
  apply H0.  auto with arith.  assumption.  simpl in |- *.  assumption.  simpl in |- *.
  apply be_iter1_le_preserved.  apply H2.  assumption.  assumption.
Qed.

Lemma be_iter2n_is_lfp_be :
 forall (bef : bool_expr -> bool_expr) (n : nat) (be : bool_expr),
 be_le be (bef be) ->
 (forall be1 be2 : bool_expr, be_eq be1 be2 -> be_eq (bef be1) (bef be2)) ->
 (forall be1 be2 : bool_expr, be_le be1 be2 -> be_le (bef be1) (bef be2)) ->
 (exists m : nat,
    m <= two_power n /\ be_eq (be_iter1 bef be m) (be_iter1 bef be (S m))) ->
 lfp_be bef be (fst (be_iter2n bef be n)).
Proof.
  intros.  inversion H2.  inversion H3.  clear H2 H3.  split.  unfold fp in |- *.
  apply be_eq_trans with (be2 := be_iter1 bef be (two_power n)).
  apply be_iter2n_2n.  assumption.  
  apply be_eq_trans with (be2 := bef (be_iter1 bef be (two_power n))).
  apply
   be_eq_trans
    with (be2 := be_iter1 bef (be_iter1 bef be x) (two_power n - x)).
  apply be_eq_trans with (be2 := be_iter1 bef be (x + (two_power n - x))).
  rewrite <- (le_plus_minus x (two_power n)).  apply be_eq_refl.  assumption.  
  apply be_eq_sym.  apply be_iter1_plus1.  
  apply
   be_eq_trans
    with (be2 := be_iter1 bef (be_iter1 bef be (S x)) (two_power n - x)).
  apply be_iter1_preserves_eq.  assumption.  assumption.  
  apply be_eq_trans with (be2 := be_iter1 bef be (S x + (two_power n - x))).
  apply be_iter1_plus1.  rewrite <- (Splus_nm x (two_power n - x)).
  rewrite <- (le_plus_minus x (two_power n)).
  apply
   be_eq_trans with (be2 := be_iter1 bef (be_iter1 bef be (two_power n)) 1).
  apply be_eq_trans with (be2 := be_iter1 bef be (two_power n + 1)).
  rewrite (plus_comm (two_power n) 1).  apply be_eq_refl.  apply be_eq_sym.
  apply be_iter1_plus1.  apply be_eq_refl.  assumption.  apply H0.
  apply be_eq_sym.  apply be_iter2n_2n.  assumption.  split.
  apply be_le_trans with (be2 := be_iter1 bef be (two_power n)).
  apply be_iter1_n_le.  unfold not in |- *; intro.  apply (lt_irrefl 0).
  replace (0 < 0) with (0 < two_power n).  apply zero_lt_pow.  rewrite H2.
  reflexivity.  assumption.  assumption.  apply be_eq_le.  apply be_eq_sym.
  apply be_iter2n_2n.  assumption.  intros.
  apply be_le_trans with (be2 := fst (be_iter2n bef be' n)).
  apply be_iter2n_le_preserved.  assumption.  assumption.  assumption.
  assumption.  apply be_eq_le.  apply be_eq_sym.  apply be_iter2n_0.
  assumption.  assumption.
Qed.

Lemma be_le_zero : forall be : bool_expr, be_le Zero be.
Proof.
  unfold be_le in |- *.  unfold eval_be' in |- *.  simpl in |- *.  unfold bool_fun_zero in |- *.  intros.
  discriminate.
Qed.


Section Mu_eval_as_fix.

  Variable P : ad.
  Variable f : mu_form.
  Variable re : rel_env.

  Hypothesis f_is_ok : f_ok f.
  Hypothesis f_ap_ok : mu_form_ap_ok (var_lu 0 N) f.
  Hypothesis f_even : f_P_even P f true.
  Hypothesis re_ok : ad_to_be_ok (var_lu 0 N) re.

  Definition mf (be : bool_expr) := mu_eval f (re_put re P be).
  Definition mfs (n : nat) := fst (be_iter2n mf Zero n).

  Lemma mf_inc : be_to_be_inc mf.
  Proof.
    unfold mf in |- *.
    intros.  unfold be_to_be_inc in |- *.  intros.  elim (mu_eval_lemma1 f).  intros.
    elim H1; intros H3 H2; elim H2; clear H2; intros H2 H5.

    unfold re_to_be_inc in H3.  apply H3.  assumption.
    assumption.  assumption.  assumption.
  Qed.

  Lemma mf_be_ok :
   forall be : bool_expr, be_ok (var_lu 0 N) be -> be_ok (var_lu 0 N) (mf be).
  Proof.
    unfold mf in |- *.  intros.  elim (mu_eval_lemma1 f).  intros.  apply H0.
    unfold ad_to_be_ok, re_put in |- *.  intro.  elim (Neqb P x).  assumption.
    apply re_ok.  assumption.  assumption.
  Qed.

  Lemma mf_preserves_eq :
   forall be1 be2 : bool_expr, be_eq be1 be2 -> be_eq (mf be1) (mf be2).
  Proof.
    unfold mf in |- *.  elim (mu_eval_lemma1 f).  intros.
    elim H0; intros H3 H2; elim H2; clear H2; intros H2 H5.
 
    apply H5.  unfold ad_to_be_eq in |- *.  unfold re_put in |- *.  intro.  elim (Neqb P x).
    assumption.  apply be_eq_refl.  assumption.  assumption.  
  Qed.
 
  Lemma mf_fix_ex :
   exists m : nat,
     m <= two_power N /\ be_eq (be_iter1 mf Zero m) (be_iter1 mf Zero (S m)).
  Proof.
    apply be_iter1_fix_ex.  exact mf_inc.  intros.  apply mf_be_ok.  assumption.
    apply zero_ok.  apply be_le_zero.  
  Qed.

  Lemma mf_lfp : lfp mf (fst (be_iter2n mf Zero N)).
  Proof.
    apply (proj2 (lfp_be_lfp mf (fst (be_iter2n mf Zero N)))).
    apply be_iter2n_is_lfp_be.  apply be_le_zero.  intros.  apply mf_preserves_eq.
    assumption.  exact mf_inc.  exact mf_fix_ex.  
  Qed.

End Mu_eval_as_fix.


Lemma mu_eval_mu_is_lfp :
 forall (P : ad) (f : mu_form) (re : rel_env),
 f_ok (mu_mu P f) ->
 mu_form_ap_ok (var_lu 0 N) (mu_mu P f) ->
 ad_to_be_ok (var_lu 0 N) re ->
 lfp (fun be : bool_expr => mu_eval f (re_put re P be))
   (mu_eval (mu_mu P f) re).
Proof.
  intros.  inversion H.  inversion H0.  elim (mf_lfp P f re).  intros.
  split; assumption.  assumption.  assumption.  assumption.  assumption.
Qed.


Fixpoint BDDmu_eval (f : mu_form) :
 BDDconfig -> list ad -> Brel_env -> BDDconfig * ad :=
  fun cfg ul bre =>
  match f with
  | mu_0 => (cfg, BDDzero)
  | mu_1 => (cfg, BDDone)
  | mu_ap p => BDDvar_make gc cfg ul p
  | mu_rel_var P =>
      match MapGet _ bre P with
      | None => (cfg, BDDzero)
      | Some node => (cfg, node)
      end
  | mu_neg g =>
      match BDDmu_eval g cfg ul bre with
      | (cfgg, nodeg) => BDDneg gc cfgg (nodeg :: ul) nodeg
      end
  | mu_and g h =>
      match BDDmu_eval g cfg ul bre with
      | (cfgg, nodeg) =>
          match BDDmu_eval h cfgg (nodeg :: ul) bre with
          | (cfgh, nodeh) =>
              BDDand gc cfgh (nodeh :: nodeg :: ul) nodeg nodeh
          end
      end
  | mu_or g h =>
      match BDDmu_eval g cfg ul bre with
      | (cfgg, nodeg) =>
          match BDDmu_eval h cfgg (nodeg :: ul) bre with
          | (cfgh, nodeh) => BDDor gc cfgh (nodeh :: nodeg :: ul) nodeg nodeh
          end
      end
  | mu_impl g h =>
      match BDDmu_eval g cfg ul bre with
      | (cfgg, nodeg) =>
          match BDDmu_eval h cfgg (nodeg :: ul) bre with
          | (cfgh, nodeh) =>
              BDDimpl gc cfgh (nodeh :: nodeg :: ul) nodeg nodeh
          end
      end
  | mu_iff g h =>
      match BDDmu_eval g cfg ul bre with
      | (cfgg, nodeg) =>
          match BDDmu_eval h cfgg (nodeg :: ul) bre with
          | (cfgh, nodeh) =>
              BDDiff gc cfgh (nodeh :: nodeg :: ul) nodeg nodeh
          end
      end
  | mu_all t g =>
      match MapGet _ bte t with
      | None => (cfg, BDDzero)
      | Some nodet =>
          match BDDmu_eval g cfg ul bre with
          | (cfgg, nodeg) => BDDmu_all N gc cfgg (nodeg :: ul) nodet nodeg
          end
      end
  | mu_ex t g =>
      match MapGet _ bte t with
      | None => (cfg, BDDzero)
      | Some nodet =>
          match BDDmu_eval g cfg ul bre with
          | (cfgg, nodeg) => BDDmu_ex N gc cfgg (nodeg :: ul) nodet nodeg
          end
      end
  | mu_mu P g =>
      fst
        (BDDiter2n
           (fun cfg node =>
            BDDmu_eval g cfg (node :: ul) (MapPut _ bre P node)) cfg BDDzero
           N)
  end.


Lemma BDDmu_eval_ok :
 forall (f : mu_form) (cfg : BDDconfig) (ul : list ad) 
   (re : rel_env) (bre : Brel_env),
 BDDconfig_OK cfg ->
 used_list_OK cfg ul ->
 cfg_ul_bre_ok cfg ul bre ->
 cfg_re_bre_ok cfg re bre ->
 cfg_ul_bte_ok cfg ul bte ->
 cfg_te_bte_ok cfg te bte ->
 f_bre_ok f bre ->
 f_bte_ok f bte ->
 BDDconfig_OK (fst (BDDmu_eval f cfg ul bre)) /\
 config_node_OK (fst (BDDmu_eval f cfg ul bre))
   (snd (BDDmu_eval f cfg ul bre)) /\
 used_nodes_preserved cfg (fst (BDDmu_eval f cfg ul bre)) ul /\
 bool_fun_eq
   (bool_fun_of_BDD (fst (BDDmu_eval f cfg ul bre))
      (snd (BDDmu_eval f cfg ul bre))) (bool_fun_of_bool_expr (mu_eval f re)).
Proof.
  simple induction f.
  simpl in |- *.  intros.  split.  assumption.  split.  apply zero_OK.  split.
  apply used_nodes_preserved_refl.  apply bool_fun_of_BDD_zero.  assumption.
  simpl in |- *.  intros.  split.  assumption.  split.  apply one_OK.  split.
  apply used_nodes_preserved_refl.  apply bool_fun_of_BDD_one.  assumption.
  intro p.  simpl in |- *.  intros.  split.  apply BDDvar_make_config_OK.  assumption.
  assumption.  assumption.  split.  apply BDDvar_make_node_OK.  assumption.
  assumption.  assumption.  split.  apply BDDvar_make_used_nodes_preserved.
  assumption.  assumption.  assumption.  apply BDDvar_make_is_var.  assumption.
  assumption.  assumption.  
  intro P.  simpl in |- *.  unfold f_bre_ok in |- *.  unfold in_dom in |- *.  intros.  simpl in H5.
  cut
   (match MapGet ad bre P with
    | None => false
    | Some _ => true
    end = true).
  intro.  elim (option_sum _ (MapGet ad bre P)).  intro y.  elim y; clear y.
  intros node H8.  rewrite H8.  simpl in |- *.  split.  assumption.  split.
  apply used_node'_OK with (ul := ul).  assumption.  assumption.  
  unfold cfg_ul_bre_ok in H1.  apply H1 with (P := P).  assumption.  split.
  apply used_nodes_preserved_refl.  apply H2.  assumption.  intro y.
  rewrite y in H7.  discriminate.  apply H5.  apply Neqb_correct.
  intro g.  simpl in |- *.  intros.  elim (prod_sum _ _ (BDDmu_eval g cfg ul bre)).
  intros cfgg H8.  elim H8; clear H8.  intros nodeg H8.
  cut
   (BDDconfig_OK (fst (BDDmu_eval g cfg ul bre)) /\
    config_node_OK (fst (BDDmu_eval g cfg ul bre))
      (snd (BDDmu_eval g cfg ul bre)) /\
    used_nodes_preserved cfg (fst (BDDmu_eval g cfg ul bre)) ul /\
    bool_fun_eq
      (bool_fun_of_BDD (fst (BDDmu_eval g cfg ul bre))
         (snd (BDDmu_eval g cfg ul bre)))
      (bool_fun_of_bool_expr (mu_eval g re))).
  rewrite H8.  simpl in |- *.  intro.
  elim H9; clear H9; intros H11 H10; elim H10; clear H10; intros H10 H12;
   elim H12; clear H12; intros H12 H14.

  cut (used_list_OK cfgg (nodeg :: ul)).  intro.  split.
  apply BDDneg_config_OK.  assumption.  assumption.  assumption.  
  apply used_node'_cons_node_ul.  split.  apply BDDneg_node_OK.  assumption.
  assumption.  assumption.  apply used_node'_cons_node_ul.  split.
  apply used_nodes_preserved_trans with (cfg2 := cfgg).  assumption.  assumption.
  apply used_nodes_preserved_cons with (node := nodeg).
  apply BDDneg_used_nodes_preserved.  assumption.  assumption.  assumption.
  apply used_node'_cons_node_ul.  
  apply bool_fun_eq_trans with (bool_fun_neg (bool_fun_of_BDD cfgg nodeg)).
  apply BDDneg_is_neg.  assumption.  assumption.  assumption.  
  apply used_node'_cons_node_ul.  apply bool_fun_neg_preserves_eq.  assumption.
  apply node_OK_list_OK.  assumption.
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.  assumption.
  apply H.  assumption.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.
  simpl in |- *.  intros g H h.  intros.  elim (prod_sum _ _ (BDDmu_eval g cfg ul bre)).
  intros cfgg H9.  elim H9; clear H9.  intros nodeg H9.  rewrite H9.
  elim (prod_sum _ _ (BDDmu_eval h cfgg (nodeg :: ul) bre)).  intros cfgh H10.
  elim H10; clear H10.  intros nodeh H10.  rewrite H10.
  elim (mu_and_bre_ok _ _ _ H7); intros H12 H13.
  elim (mu_and_bte_ok _ _ _ H8); intros H14 H15.

  cut
   (BDDconfig_OK (fst (BDDmu_eval g cfg ul bre)) /\
    config_node_OK (fst (BDDmu_eval g cfg ul bre))
      (snd (BDDmu_eval g cfg ul bre)) /\
    used_nodes_preserved cfg (fst (BDDmu_eval g cfg ul bre)) ul /\
    bool_fun_eq
      (bool_fun_of_BDD (fst (BDDmu_eval g cfg ul bre))
         (snd (BDDmu_eval g cfg ul bre)))
      (bool_fun_of_bool_expr (mu_eval g re))).
  rewrite H9.  simpl in |- *.  intros.
  elim H11; clear H11; intros H17 H16; elim H16; clear H16; intros H16 H18;
   elim H18; clear H18; intros H18 H20.

  cut (used_list_OK cfgg (nodeg :: ul)).  intro.  
  elim (cfg_ul_re_bre_ok_preserved cfg cfgg ul re bre).  intros.
  elim (cfg_ul_te_bte_ok_preserved cfg cfgg ul te bte).  intros.
  cut (cfg_ul_bre_ok cfgg (nodeg :: ul) bre).  intro.
  cut (cfg_ul_bte_ok cfgg (nodeg :: ul) bte). intro.
  cut
   (BDDconfig_OK (fst (BDDmu_eval h cfgg (nodeg :: ul) bre)) /\
    config_node_OK (fst (BDDmu_eval h cfgg (nodeg :: ul) bre))
      (snd (BDDmu_eval h cfgg (nodeg :: ul) bre)) /\
    used_nodes_preserved cfgg (fst (BDDmu_eval h cfgg (nodeg :: ul) bre))
      (nodeg :: ul) /\
    bool_fun_eq
      (bool_fun_of_BDD (fst (BDDmu_eval h cfgg (nodeg :: ul) bre))
         (snd (BDDmu_eval h cfgg (nodeg :: ul) bre)))
      (bool_fun_of_bool_expr (mu_eval h re))).
  rewrite H10.  simpl in |- *.  intro.
  elim H26; clear H26; intros H28 H27; elim H27; clear H27; intros H27 H29;
   elim H29; clear H29; intros H29 H31.

  cut (used_list_OK cfgh (nodeh :: nodeg :: ul)).  intro.  split.
  apply BDDand_config_OK.  assumption.  assumption.  assumption.  
  apply used_node'_cons_node'_ul.  apply used_node'_cons_node_ul.
  apply used_node'_cons_node_ul.  split.  apply BDDand_node_OK.  assumption.
  assumption.  assumption.  apply used_node'_cons_node'_ul.
  apply used_node'_cons_node_ul.  apply used_node'_cons_node_ul.  split.
  apply used_nodes_preserved_trans with (cfg2 := cfgg).  assumption.  assumption.  
  apply used_nodes_preserved_cons with (node := nodeg).
  apply used_nodes_preserved_trans with (cfg2 := cfgh).  assumption.  assumption.  
  apply used_nodes_preserved_cons with (node := nodeh).
  apply BDDand_used_nodes_preserved.  assumption.  assumption.  assumption.
  apply used_node'_cons_node'_ul.  apply used_node'_cons_node_ul.
  apply used_node'_cons_node_ul.  
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_and (bool_fun_of_BDD cfgh nodeg)
                (bool_fun_of_BDD cfgh nodeh)).
  apply BDDand_is_and.  assumption.  assumption.  assumption.  
  apply used_node'_cons_node'_ul.  apply used_node'_cons_node_ul.
  apply used_node'_cons_node_ul.  apply bool_fun_and_preserves_eq.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfgg nodeg).
  apply used_nodes_preserved'_bool_fun with (ul := nodeg :: ul).  assumption.
  assumption.  assumption.  assumption.  apply used_node'_cons_node_ul.  
  assumption.  assumption.  apply node_OK_list_OK.  assumption.  
  apply used_nodes_preserved_list_OK with (cfg := cfgg).  assumption.  assumption.
  apply H0.  assumption.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  apply cfg_ul_bte_cons_ok.  assumption.
  apply cfg_ul_bre_cons_ok.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  apply node_OK_list_OK.  assumption.
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.  assumption.  
  apply H.  assumption.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.
  simpl in |- *.  intros g H h.  intros.  elim (prod_sum _ _ (BDDmu_eval g cfg ul bre)).
  intros cfgg H9.  elim H9; clear H9.  intros nodeg H9.  rewrite H9.
  elim (prod_sum _ _ (BDDmu_eval h cfgg (nodeg :: ul) bre)).  intros cfgh H10.
  elim H10; clear H10.  intros nodeh H10.  rewrite H10.
  elim (mu_or_bre_ok _ _ _ H7); intros H12 H13.
  elim (mu_or_bte_ok _ _ _ H8); intros H14 H15.

  cut
   (BDDconfig_OK (fst (BDDmu_eval g cfg ul bre)) /\
    config_node_OK (fst (BDDmu_eval g cfg ul bre))
      (snd (BDDmu_eval g cfg ul bre)) /\
    used_nodes_preserved cfg (fst (BDDmu_eval g cfg ul bre)) ul /\
    bool_fun_eq
      (bool_fun_of_BDD (fst (BDDmu_eval g cfg ul bre))
         (snd (BDDmu_eval g cfg ul bre)))
      (bool_fun_of_bool_expr (mu_eval g re))).
  rewrite H9.  simpl in |- *.  intros.
  elim H11; clear H11; intros H17 H16; elim H16; clear H16; intros H16 H18;
   elim H18; clear H18; intros H18 H20.

  cut (used_list_OK cfgg (nodeg :: ul)).  intro.  
  elim (cfg_ul_re_bre_ok_preserved cfg cfgg ul re bre).  intros.
  elim (cfg_ul_te_bte_ok_preserved cfg cfgg ul te bte).  intros.
  cut (cfg_ul_bre_ok cfgg (nodeg :: ul) bre).  intro.
  cut (cfg_ul_bte_ok cfgg (nodeg :: ul) bte). intro.
  cut
   (BDDconfig_OK (fst (BDDmu_eval h cfgg (nodeg :: ul) bre)) /\
    config_node_OK (fst (BDDmu_eval h cfgg (nodeg :: ul) bre))
      (snd (BDDmu_eval h cfgg (nodeg :: ul) bre)) /\
    used_nodes_preserved cfgg (fst (BDDmu_eval h cfgg (nodeg :: ul) bre))
      (nodeg :: ul) /\
    bool_fun_eq
      (bool_fun_of_BDD (fst (BDDmu_eval h cfgg (nodeg :: ul) bre))
         (snd (BDDmu_eval h cfgg (nodeg :: ul) bre)))
      (bool_fun_of_bool_expr (mu_eval h re))).
  rewrite H10.  simpl in |- *.  intro.
  elim H26; clear H26; intros H28 H27; elim H27; clear H27; intros H27 H29;
   elim H29; clear H29; intros H29 H31.

  cut (used_list_OK cfgh (nodeh :: nodeg :: ul)).  intro.  split.
  apply BDDor_config_OK.  assumption.  assumption.  assumption.  
  apply used_node'_cons_node'_ul.  apply used_node'_cons_node_ul.
  apply used_node'_cons_node_ul.  split.  apply BDDor_node_OK.  assumption.
  assumption.  assumption.  apply used_node'_cons_node'_ul.
  apply used_node'_cons_node_ul.  apply used_node'_cons_node_ul.  split.
  apply used_nodes_preserved_trans with (cfg2 := cfgg).  assumption.  assumption.  
  apply used_nodes_preserved_cons with (node := nodeg).
  apply used_nodes_preserved_trans with (cfg2 := cfgh).  assumption.  assumption.  
  apply used_nodes_preserved_cons with (node := nodeh).
  apply BDDor_used_nodes_preserved.  assumption.  assumption.  assumption.
  apply used_node'_cons_node'_ul.  apply used_node'_cons_node_ul.
  apply used_node'_cons_node_ul.  
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_or (bool_fun_of_BDD cfgh nodeg)
                (bool_fun_of_BDD cfgh nodeh)).
  apply BDDor_is_or.  assumption.  assumption.  assumption.  
  apply used_node'_cons_node'_ul.  apply used_node'_cons_node_ul.
  apply used_node'_cons_node_ul.  apply bool_fun_or_preserves_eq.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfgg nodeg).
  apply used_nodes_preserved'_bool_fun with (ul := nodeg :: ul).  assumption.
  assumption.  assumption.  assumption.  apply used_node'_cons_node_ul.  
  assumption.  assumption.  apply node_OK_list_OK.  assumption.  
  apply used_nodes_preserved_list_OK with (cfg := cfgg).  assumption.  assumption.
  apply H0.  assumption.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  apply cfg_ul_bte_cons_ok.  assumption.
  apply cfg_ul_bre_cons_ok.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  apply node_OK_list_OK.  assumption.
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.  assumption.  
  apply H.  assumption.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.
  simpl in |- *.  intros g H h.  intros.  elim (prod_sum _ _ (BDDmu_eval g cfg ul bre)).
  intros cfgg H9.  elim H9; clear H9.  intros nodeg H9.  rewrite H9.
  elim (prod_sum _ _ (BDDmu_eval h cfgg (nodeg :: ul) bre)).  intros cfgh H10.
  elim H10; clear H10.  intros nodeh H10.  rewrite H10.
  elim (mu_impl_bre_ok _ _ _ H7); intros H12 H13.
  elim (mu_impl_bte_ok _ _ _ H8); intros H14 H15.

  cut
   (BDDconfig_OK (fst (BDDmu_eval g cfg ul bre)) /\
    config_node_OK (fst (BDDmu_eval g cfg ul bre))
      (snd (BDDmu_eval g cfg ul bre)) /\
    used_nodes_preserved cfg (fst (BDDmu_eval g cfg ul bre)) ul /\
    bool_fun_eq
      (bool_fun_of_BDD (fst (BDDmu_eval g cfg ul bre))
         (snd (BDDmu_eval g cfg ul bre)))
      (bool_fun_of_bool_expr (mu_eval g re))).
  rewrite H9.  simpl in |- *.  intros.
  elim H11; clear H11; intros H17 H16; elim H16; clear H16; intros H16 H18;
   elim H18; clear H18; intros H18 H20.

  cut (used_list_OK cfgg (nodeg :: ul)).  intro.  
  elim (cfg_ul_re_bre_ok_preserved cfg cfgg ul re bre).  intros.
  elim (cfg_ul_te_bte_ok_preserved cfg cfgg ul te bte).  intros.
  cut (cfg_ul_bre_ok cfgg (nodeg :: ul) bre).  intro.
  cut (cfg_ul_bte_ok cfgg (nodeg :: ul) bte). intro.
  cut
   (BDDconfig_OK (fst (BDDmu_eval h cfgg (nodeg :: ul) bre)) /\
    config_node_OK (fst (BDDmu_eval h cfgg (nodeg :: ul) bre))
      (snd (BDDmu_eval h cfgg (nodeg :: ul) bre)) /\
    used_nodes_preserved cfgg (fst (BDDmu_eval h cfgg (nodeg :: ul) bre))
      (nodeg :: ul) /\
    bool_fun_eq
      (bool_fun_of_BDD (fst (BDDmu_eval h cfgg (nodeg :: ul) bre))
         (snd (BDDmu_eval h cfgg (nodeg :: ul) bre)))
      (bool_fun_of_bool_expr (mu_eval h re))).
  rewrite H10.  simpl in |- *.  intro.
  elim H26; clear H26; intros H28 H27; elim H27; clear H27; intros H27 H29;
   elim H29; clear H29; intros H29 H31.

  cut (used_list_OK cfgh (nodeh :: nodeg :: ul)).  intro.  split.
  apply BDDimpl_config_OK.  assumption.  assumption.  assumption.  
  apply used_node'_cons_node'_ul.  apply used_node'_cons_node_ul.
  apply used_node'_cons_node_ul.  split.  apply BDDimpl_node_OK.  assumption.
  assumption.  assumption.  apply used_node'_cons_node'_ul.
  apply used_node'_cons_node_ul.  apply used_node'_cons_node_ul.  split.
  apply used_nodes_preserved_trans with (cfg2 := cfgg).  assumption.  assumption.  
  apply used_nodes_preserved_cons with (node := nodeg).
  apply used_nodes_preserved_trans with (cfg2 := cfgh).  assumption.  assumption.  
  apply used_nodes_preserved_cons with (node := nodeh).
  apply BDDimpl_used_nodes_preserved.  assumption.  assumption.  assumption.
  apply used_node'_cons_node'_ul.  apply used_node'_cons_node_ul.
  apply used_node'_cons_node_ul.  
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_impl (bool_fun_of_BDD cfgh nodeg)
                (bool_fun_of_BDD cfgh nodeh)).
  apply BDDimpl_is_impl.  assumption.  assumption.  assumption.  
  apply used_node'_cons_node'_ul.  apply used_node'_cons_node_ul.
  apply used_node'_cons_node_ul.  apply bool_fun_impl_preserves_eq.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfgg nodeg).
  apply used_nodes_preserved'_bool_fun with (ul := nodeg :: ul).  assumption.
  assumption.  assumption.  assumption.  apply used_node'_cons_node_ul.  
  assumption.  assumption.  apply node_OK_list_OK.  assumption.  
  apply used_nodes_preserved_list_OK with (cfg := cfgg).  assumption.  assumption.
  apply H0.  assumption.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  apply cfg_ul_bte_cons_ok.  assumption.
  apply cfg_ul_bre_cons_ok.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  apply node_OK_list_OK.  assumption.
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.  assumption.  
  apply H.  assumption.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.
  simpl in |- *.  intros g H h.  intros.  elim (prod_sum _ _ (BDDmu_eval g cfg ul bre)).
  intros cfgg H9.  elim H9; clear H9.  intros nodeg H9.  rewrite H9.
  elim (prod_sum _ _ (BDDmu_eval h cfgg (nodeg :: ul) bre)).  intros cfgh H10.
  elim H10; clear H10.  intros nodeh H10.  rewrite H10.
  elim (mu_iff_bre_ok _ _ _ H7); intros H12 H13.
  elim (mu_iff_bte_ok _ _ _ H8); intros H14 H15.

  cut
   (BDDconfig_OK (fst (BDDmu_eval g cfg ul bre)) /\
    config_node_OK (fst (BDDmu_eval g cfg ul bre))
      (snd (BDDmu_eval g cfg ul bre)) /\
    used_nodes_preserved cfg (fst (BDDmu_eval g cfg ul bre)) ul /\
    bool_fun_eq
      (bool_fun_of_BDD (fst (BDDmu_eval g cfg ul bre))
         (snd (BDDmu_eval g cfg ul bre)))
      (bool_fun_of_bool_expr (mu_eval g re))).
  rewrite H9.  simpl in |- *.  intros.
  elim H11; clear H11; intros H17 H16; elim H16; clear H16; intros H16 H18;
   elim H18; clear H18; intros H18 H20.

  cut (used_list_OK cfgg (nodeg :: ul)).  intro.  
  elim (cfg_ul_re_bre_ok_preserved cfg cfgg ul re bre).  intros.
  elim (cfg_ul_te_bte_ok_preserved cfg cfgg ul te bte).  intros.
  cut (cfg_ul_bre_ok cfgg (nodeg :: ul) bre).  intro.
  cut (cfg_ul_bte_ok cfgg (nodeg :: ul) bte). intro.
  cut
   (BDDconfig_OK (fst (BDDmu_eval h cfgg (nodeg :: ul) bre)) /\
    config_node_OK (fst (BDDmu_eval h cfgg (nodeg :: ul) bre))
      (snd (BDDmu_eval h cfgg (nodeg :: ul) bre)) /\
    used_nodes_preserved cfgg (fst (BDDmu_eval h cfgg (nodeg :: ul) bre))
      (nodeg :: ul) /\
    bool_fun_eq
      (bool_fun_of_BDD (fst (BDDmu_eval h cfgg (nodeg :: ul) bre))
         (snd (BDDmu_eval h cfgg (nodeg :: ul) bre)))
      (bool_fun_of_bool_expr (mu_eval h re))).
  rewrite H10.  simpl in |- *.  intro.
  elim H26; clear H26; intros H28 H27; elim H27; clear H27; intros H27 H29;
   elim H29; clear H29; intros H29 H31.

  cut (used_list_OK cfgh (nodeh :: nodeg :: ul)).  intro.  split.
  apply BDDiff_config_OK.  assumption.  assumption.  assumption.  
  apply used_node'_cons_node'_ul.  apply used_node'_cons_node_ul.
  apply used_node'_cons_node_ul.  split.  apply BDDiff_node_OK.  assumption.
  assumption.  assumption.  apply used_node'_cons_node'_ul.
  apply used_node'_cons_node_ul.  apply used_node'_cons_node_ul.  split.
  apply used_nodes_preserved_trans with (cfg2 := cfgg).  assumption.  assumption.  
  apply used_nodes_preserved_cons with (node := nodeg).
  apply used_nodes_preserved_trans with (cfg2 := cfgh).  assumption.  assumption.  
  apply used_nodes_preserved_cons with (node := nodeh).
  apply BDDiff_used_nodes_preserved.  assumption.  assumption.  assumption.
  apply used_node'_cons_node'_ul.  apply used_node'_cons_node_ul.
  apply used_node'_cons_node_ul.  
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_iff (bool_fun_of_BDD cfgh nodeg)
                (bool_fun_of_BDD cfgh nodeh)).
  apply BDDiff_is_iff.  assumption.  assumption.  assumption.  
  apply used_node'_cons_node'_ul.  apply used_node'_cons_node_ul.
  apply used_node'_cons_node_ul.  apply bool_fun_iff_preserves_eq.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD cfgg nodeg).
  apply used_nodes_preserved'_bool_fun with (ul := nodeg :: ul).  assumption.
  assumption.  assumption.  assumption.  apply used_node'_cons_node_ul.  
  assumption.  assumption.  apply node_OK_list_OK.  assumption.  
  apply used_nodes_preserved_list_OK with (cfg := cfgg).  assumption.  assumption.
  apply H0.  assumption.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  apply cfg_ul_bte_cons_ok.  assumption.
  apply cfg_ul_bre_cons_ok.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  apply node_OK_list_OK.  assumption.
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.  assumption.  
  apply H.  assumption.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.
  simpl in |- *.  intros t g.  intros.  cut (f_bre_ok g bre).  cut (f_bte_ok g bte).
  intros.  elim (prod_sum _ _ (BDDmu_eval g cfg ul bre)).  intros cfgg H10.
  elim H10; clear H10.  intros nodeg H10.  rewrite H10.  unfold f_bte_ok in H7.
  simpl in H7.  cut (in_dom _ t bte = true).  unfold in_dom in |- *.  intro.
  elim (option_sum _ (MapGet ad bte t)).  clear H11.  intro y.  elim y; clear y.
  intros nodet H11.  rewrite H11.
  cut
   (BDDconfig_OK (fst (BDDmu_eval g cfg ul bre)) /\
    config_node_OK (fst (BDDmu_eval g cfg ul bre))
      (snd (BDDmu_eval g cfg ul bre)) /\
    used_nodes_preserved cfg (fst (BDDmu_eval g cfg ul bre)) ul /\
    bool_fun_eq
      (bool_fun_of_BDD (fst (BDDmu_eval g cfg ul bre))
         (snd (BDDmu_eval g cfg ul bre)))
      (bool_fun_of_bool_expr (mu_eval g re))).
  rewrite H10.  simpl in |- *.  intro.
  elim H12; clear H12; intros H14 H13; elim H13; clear H13; intros H13 H15;
   elim H15; clear H15; intros H15 H17.

  cut (used_list_OK cfgg (nodeg :: ul)).  intro.
  elim (cfg_ul_re_bre_ok_preserved cfg cfgg ul re bre).  intros.
  elim (cfg_ul_te_bte_ok_preserved cfg cfgg ul te bte).  intros.
  cut (cfg_ul_bre_ok cfgg (nodeg :: ul) bre).  intro.
  cut (cfg_ul_bte_ok cfgg (nodeg :: ul) bte).  intro.
  cut (used_node' cfgg (nodeg :: ul) nodet).  intro.  split.
  apply BDDmu_all_config_OK.  assumption.  assumption.  assumption.  assumption.
  apply used_node'_cons_node_ul.  split.  apply BDDmu_all_node_OK.  assumption.
  assumption.  assumption.  assumption.  apply used_node'_cons_node_ul.  split.
  apply used_nodes_preserved_trans with (cfg2 := cfgg).  assumption.  assumption.  
  apply used_nodes_preserved_cons with (node := nodeg).
  apply BDDmu_all_used_nodes_preserved.  assumption.  assumption.  assumption.  
  assumption.  apply used_node'_cons_node_ul.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_mu_all N (bool_fun_of_BDD cfgg nodet)
                (bool_fun_of_BDD cfgg nodeg)).
  apply BDDmu_all_is_mu_all.  assumption.  assumption.  assumption.  assumption.
  apply used_node'_cons_node_ul.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_mu_all N (bool_fun_of_bool_expr (te t))
                (bool_fun_of_bool_expr (mu_eval g re))).
  apply bool_fun_mu_all_preserves_eq.  apply H20.  assumption.  assumption.
  apply bool_fun_eq_sym.  apply mu_all_eval_ok.  apply H22 with (t := t).
  assumption.  apply cfg_ul_bte_cons_ok.  assumption.  apply cfg_ul_bre_cons_ok.
  assumption.  assumption.  assumption.  assumption.  assumption.  assumption.  
  assumption.  assumption.  assumption.  assumption.  assumption.  assumption.
  assumption.  apply node_OK_list_OK.  assumption.
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.  assumption.
  apply H.  assumption.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  intro y.  rewrite y in H11.
  discriminate.  apply H7.  rewrite (Neqb_correct t).  reflexivity.  
  apply mu_all_bte_ok with (t := t).  assumption.  apply mu_all_bre_ok with (t := t).
  assumption.
  simpl in |- *.  intros t g.  intros.  cut (f_bre_ok g bre).  cut (f_bte_ok g bte).
  intros.  elim (prod_sum _ _ (BDDmu_eval g cfg ul bre)).  intros cfgg H10.
  elim H10; clear H10.  intros nodeg H10.  rewrite H10.  unfold f_bte_ok in H7.
  simpl in H7.  cut (in_dom _ t bte = true).  unfold in_dom in |- *.  intro.
  elim (option_sum _ (MapGet ad bte t)).  clear H11.  intro y.  elim y; clear y.
  intros nodet H11.  rewrite H11.
  cut
   (BDDconfig_OK (fst (BDDmu_eval g cfg ul bre)) /\
    config_node_OK (fst (BDDmu_eval g cfg ul bre))
      (snd (BDDmu_eval g cfg ul bre)) /\
    used_nodes_preserved cfg (fst (BDDmu_eval g cfg ul bre)) ul /\
    bool_fun_eq
      (bool_fun_of_BDD (fst (BDDmu_eval g cfg ul bre))
         (snd (BDDmu_eval g cfg ul bre)))
      (bool_fun_of_bool_expr (mu_eval g re))).
  rewrite H10.  simpl in |- *.  intro.
  elim H12; clear H12; intros H14 H13; elim H13; clear H13; intros H13 H15;
   elim H15; clear H15; intros H15 H17.

  cut (used_list_OK cfgg (nodeg :: ul)).  intro.
  elim (cfg_ul_re_bre_ok_preserved cfg cfgg ul re bre).  intros.
  elim (cfg_ul_te_bte_ok_preserved cfg cfgg ul te bte).  intros.
  cut (cfg_ul_bre_ok cfgg (nodeg :: ul) bre).  intro.
  cut (cfg_ul_bte_ok cfgg (nodeg :: ul) bte).  intro.
  cut (used_node' cfgg (nodeg :: ul) nodet).  intro.  split.
  apply BDDmu_ex_config_OK.  assumption.  assumption.  assumption.  assumption.
  apply used_node'_cons_node_ul.  split.  apply BDDmu_ex_node_OK.  assumption.
  assumption.  assumption.  assumption.  apply used_node'_cons_node_ul.  split.
  apply used_nodes_preserved_trans with (cfg2 := cfgg).  assumption.  assumption.  
  apply used_nodes_preserved_cons with (node := nodeg).
  apply BDDmu_ex_used_nodes_preserved.  assumption.  assumption.  assumption.  
  assumption.  apply used_node'_cons_node_ul.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_mu_ex N (bool_fun_of_BDD cfgg nodet)
                (bool_fun_of_BDD cfgg nodeg)).
  apply BDDmu_ex_is_mu_ex.  assumption.  assumption.  assumption.  assumption.
  apply used_node'_cons_node_ul.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_mu_ex N (bool_fun_of_bool_expr (te t))
                (bool_fun_of_bool_expr (mu_eval g re))).
  apply bool_fun_mu_ex_preserves_eq.  apply H20.  assumption.  assumption.
  apply bool_fun_eq_sym.  apply mu_ex_eval_ok.  apply H22 with (t := t).
  assumption.  apply cfg_ul_bte_cons_ok.  assumption.  apply cfg_ul_bre_cons_ok.
  assumption.  assumption.  assumption.  assumption.  assumption.  assumption.  
  assumption.  assumption.  assumption.  assumption.  assumption.  assumption.
  assumption.  apply node_OK_list_OK.  assumption.
  apply used_nodes_preserved_list_OK with (cfg := cfg).  assumption.  assumption.
  apply H.  assumption.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  intro y.  rewrite y in H11.
  discriminate.  apply H7.  rewrite (Neqb_correct t).  reflexivity.  
  apply mu_ex_bte_ok with (t := t).  assumption.  apply mu_ex_bre_ok with (t := t).
  assumption.
  simpl in |- *.  intros P g.  intros.  apply BDDiter2n_lemma1 with (te := te) (bte := bte).
  intros.  apply H.  assumption.  assumption.  assumption.  assumption.
  assumption.  assumption.  assumption.  assumption.  assumption.
  apply zero_OK.  assumption.  assumption.  assumption.  assumption.
  assumption.  intro.  apply mu_mu_bre_ok.  assumption.  assumption.
  apply bool_fun_of_BDD_zero.  assumption.  
Qed.

End MuEval.

End Nsec.