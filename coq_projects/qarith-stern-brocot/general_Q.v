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


(** General Facts About Q and Qpositive, the functions Qpositive_c and Qpositive_i and the operations Qmult, Qpositive, Qlt *)

Require Import FunInd.
Require Export Qpositive.
Require Export Q_field.
Require Export Q_order.
Require Import Field_Theory_Q. 
Require Export Zaux.

(* An auxiliary lemma about [Z] *)

Lemma Z_of_nat_Zabs_nat_pos: forall z, (0<=z)%Z -> Z_of_nat (Z.abs_nat z) = z.
Proof.
 intros z Hz;
 destruct (Z_of_nat_complete_inf z Hz) as [n Hn];
 transitivity (Z_of_nat n); auto;
 apply (f_equal Z_of_nat);
 rewrite <- absolu_inj_nat;
 apply (f_equal Z.abs_nat); trivial.
Qed.

(** For decoding and encoing elements of Q: binary sequneces versus pairs of integers. *) 


(*** Building the rational number m/n *)
Definition make_Q (m n : Z) :=
  match m, n with
  | Zpos _, Zpos _ =>
      Qpos (Qpositive_c (Z.abs_nat m) (Z.abs_nat n) (Z.abs_nat m + Z.abs_nat n))
  | Zneg _, Zneg _ =>
      Qpos (Qpositive_c (Z.abs_nat m) (Z.abs_nat n) (Z.abs_nat m + Z.abs_nat n))
  | Z0, _ => Zero
  | _, Z0 => Zero (* dummy *) 
  | _, _ =>
      Qneg (Qpositive_c (Z.abs_nat m) (Z.abs_nat n) (Z.abs_nat m + Z.abs_nat n))
  end.

(*** decoding a sequnce consisting of dL and nR and ending in One. *) 
Definition decode_Q (q : Q) :=
  match q with
  | Qpos p =>
      (Z_of_nat (fst (Qpositive_i p)), Z_of_nat (snd (Qpositive_i p)))
  | Qneg p =>
      ((- Z_of_nat (fst (Qpositive_i p)))%Z, Z_of_nat (snd (Qpositive_i p)))
  | Zero => (0%Z, 1%Z)
  end.

Definition numerator (q:Q) :Z := fst (decode_Q q).

Definition denominator (q:Q) :Z := snd (decode_Q q).

(** Definition of various functions *) 
Definition Z_to_Qpositive : forall x : Z, (0 < x)%Z -> Qpositive.
intros [| p| p].
intros H; abstract discriminate H.
intro.
exact (Qpositive_c (nat_of_P p) 1 (S (nat_of_P p))).
intro; abstract discriminate H.
Defined.

Definition Z_to_Q (x : Z) : Q :=
  match x with
  | Z0 => Zero
  | Zpos p => Qpos (Qpositive_c (nat_of_P p) 1 (S (nat_of_P p)))
  | Zneg p => Qneg (Qpositive_c (nat_of_P p) 1 (S (nat_of_P p)))
  end.
 
Definition Qpositive_tail (z : Qpositive) :=
  match z with
  | nR p => p
  | dL p => p
  | One => One
  end.
 
Definition Q_tail (z : Q) :=
  match z with
  | Zero => One
  | Qpos p => p
  | Qneg p => p
  end.
 
Definition Qsgn (q : Q) :=
  match q with
  | Zero => 0%Z
  | Qpos _ => 1%Z
  | Qneg _ => (-1)%Z
  end.

(** These two only consider the length, we won't use them further *)
Fixpoint length_of_Qpositive_to_positive (qp : Qpositive) : positive :=
  match qp with
  | One => 1%positive
  | dL qp' => Pos.succ (length_of_Qpositive_to_positive qp')
  | nR qp' => Pos.succ (length_of_Qpositive_to_positive qp')
  end.

Fixpoint length_of_Qpositive (qp : Qpositive) : Z :=
  match qp with
  | One => 0%Z
  | dL qp' => (1 + length_of_Qpositive qp')%Z
  | nR qp' => (1 + length_of_Qpositive qp')%Z
  end.


(** This is the oredr preserving projection from Q to Z *)

Fixpoint Qpositive_to_Z (qp : Qpositive) : Z :=
  match qp with
  | One => 1%Z
  | dL qp' => 0%Z
  | nR qp' => (1 + Qpositive_to_Z qp')%Z
  end.


Definition Q_to_Z (x : Q) : Z :=
  match x with
  | Zero => 0%Z
  | Qpos qp => Qpositive_to_Z qp
  | Qneg qp => (- Qpositive_to_Z qp)%Z
  end.

Coercion Z_to_Q : Z >-> Q.


Definition Qlt (x y : Q) : Prop := Qgt y x.

Definition Qle (x y : Q) : Prop := ~ Qlt y x. 

Lemma Qlt_zero_pos : forall x' : Qpositive, Qlt Zero (Qpos x').
Proof.
 unfold Qlt in |- *; auto with *.
Qed.

Lemma Qlt_neg_pos : forall x' y' : Qpositive, Qlt (Qneg y') (Qpos x').
Proof.
 unfold Qlt in |- *; auto with *.
Qed.


Lemma Qlt_neg_zero : forall x' : Qpositive, Qlt (Qneg x') Zero.
 unfold Qlt in |- *; auto with *.
Qed.

Hint Resolve Qlt_neg_pos Qlt_neg_zero Qlt_zero_pos.

Ltac QltCleanAbsurdCases :=
  match goal with
  | id1:(Qlt Zero (Qneg _)) |- _ => inversion id1
  | id1:(Qlt (Qpos _) Zero) |- _ =>
      inversion id1
  | id1:(Qlt (Qpos _) (Qneg _)) |- _ =>
      inversion id1
  | id1:(Qle Zero (Qneg _)) |- _ =>
      apply False_ind; apply id1; auto with *
  | id1:(Qle (Qpos _) Zero) |- _ =>
      apply False_ind; apply id1; auto with *
  | id1:(Qle (Qpos _) (Qneg _)) |- _ =>
      apply False_ind; apply id1; auto with *
  end.
 


(* Hints Unfold Qle.*)


(** Properties of  Qpositive_c *)
Functional Scheme Qpositive_c_ind := Induction for Qpositive_c Sort Prop.

Lemma Qpositive_c_0 : forall p q n : nat, n = 0 -> Qpositive_c p q n = One.
Proof.
 intros p q n.
 functional induction (Qpositive_c p q n); trivial || (intros; discriminate).
(*
 Intros p q n Hn;
 Rewrite Hn;
 Simpl;
 Reflexivity.
*)
Qed.

Lemma Qpositive_c_1_0_0 :
 forall p q n' : nat, p - q = 0 -> q - p = 0 -> Qpositive_c p q (S n') = One.
Proof.
 intros p q n.
 functional induction (Qpositive_c p q (S n));trivial.
 rewrite e1;intros;discriminate.
 rewrite e0;intros;discriminate.
Qed.

Lemma Qpositive_c_equal_One :
 forall m n p : nat, m = n -> Qpositive_c m n p = One.
Proof.
 intros p q [| n'] Hpq;
  [ apply Qpositive_c_0
  | apply Qpositive_c_1_0_0; rewrite Hpq; rewrite <- minus_n_n ]; 
  reflexivity.
Qed.

Lemma Qpositive_c_1_0_1 :
 forall p q n' : nat,
 p - q = 0 ->
 q - p <> 0 -> Qpositive_c p q (S n') = dL (Qpositive_c p (q - p) n').
Proof.
 intros p q n' Hpq Hqp; simpl in |- *; rewrite Hpq; elim (not_O_S _ Hqp);
  intros p' Hqp'; rewrite Hqp'; simpl in |- *; reflexivity.
Qed.

Lemma Qpositive_c_dL :
 forall p q n' : nat,
 p < q -> Qpositive_c p q (S n') = dL (Qpositive_c p (q - p) n').
Proof.
 intros p q n Hpq.
 generalize (lt_minus_eq_0 p q Hpq) (lt_minus_neq p q Hpq).
 intros Hpq0 Hqp.
 apply (Qpositive_c_1_0_1 _ _ n Hpq0 Hqp).
Qed.

Lemma Qpositive_c_1_1 :
 forall p q n' : nat,
 p - q <> 0 -> Qpositive_c p q (S n') = nR (Qpositive_c (p - q) q n').
Proof.
 intros p q n' Hpq; simpl in |- *; elim (not_O_S _ Hpq); intros p' Hpq';
  rewrite Hpq'; simpl in |- *; reflexivity.
Qed.


Lemma Qpositive_c_nR :
 forall p q n' : nat,
 q < p -> Qpositive_c p q (S n') = nR (Qpositive_c (p - q) q n').
Proof.
 intros p q n Hqp.
 generalize (lt_minus_neq q p Hqp).
 intros Hpq.
 apply (Qpositive_c_1_1 _ _ n Hpq).
Qed.

Functional Scheme Qpositive_i_ind := Induction for Qpositive_i Sort Prop.
Lemma Qpositive_i_nR_with_let :
 forall w : Qpositive,
 let (p, q) := Qpositive_i w in Qpositive_i (nR w) = (p + q, q).
Proof.
 intros w;simpl Qpositive_i. 
 functional induction (Qpositive_i w);subst;trivial.
Qed.

Lemma Qpositive_i_nR :
 forall (w : Qpositive) (p q : nat),
 Qpositive_i w = (p, q) -> Qpositive_i (nR w) = (p + q, q).
Proof.
 intros w p q H_w; generalize (Qpositive_i_nR_with_let w); rewrite H_w;
  trivial.
Qed.


Lemma Qpositive_i_c :
 forall m p : nat,
 0 < m -> S m <= p -> Qpositive_i (Qpositive_c m 1 p) = (m, 1).
Proof.
 intros m p. 
 generalize m; clear m.
 induction p.
 intros m H1 H2.
 inversion H2.
 intros m H1 H2.

 case (le_lt_eq_dec 1 m).
 auto with arith.
 intro H_1_m.
 
 rewrite (Qpositive_c_nR _ _ p H_1_m). 
 rewrite (Qpositive_i_nR (Qpositive_c (m - 1) 1 p) (m - 1) 1). 
 apply pair_2; simpl in |- *; trivial; omega.
 apply IHp; omega.
 intro H_1_1.
 rewrite <- H_1_1.
 reflexivity.
Qed.

Lemma Qpositive_c_equal :
 forall m n p p' : nat,
 0 < m ->
 0 < n -> m + n <= p -> m + n <= p' -> Qpositive_c m n p = Qpositive_c m n p'.
Proof.
 intros m n p.
 functional induction (Qpositive_c m n p) as  [| | p q  p' H_eq_1  | ].
 intros p' _ _ Hpq. 
 generalize (le_plus_O_l p q Hpq) (le_plus_O_r p q Hpq).
 intros Hp Hq.
 rewrite Hp.
 rewrite Hq.
 case p'; simpl in |- *; reflexivity.
  (* 2 *)
 intros p' _ _ _ _. 
 symmetry  in |- *.
 apply Qpositive_c_equal_One.
 apply le_antisym; apply minus_O_le; assumption.
 (* 3 *)
 intros [| p'x] HpO HqO Hpq Hpq'.
 generalize (le_plus_O_r p q Hpq') (le_plus_O_l p q Hpq').
 intros Hq Hp.
 apply False_ind;omega.
(*  rewrite Hp in H_eq_1.  *)
(*  rewrite Hq in H_eq_1. *)
(*  apply False_ind. *)
(*  abstract discriminate H_eq_1. *)
 rewrite Qpositive_c_1_0_1;auto.
 apply f_equal with Qpositive. 
 rewrite (IHq p'x);try omega.
 unfold Qpositive_c at 2;fold Qpositive_c.
 rewrite e1. 
 destruct (q - p);tauto.
 omega.
 (* 4 *)
 intros [| p'x] HpO HqO Hpq Hpq'.
 generalize (le_plus_O_r p q Hpq') (le_plus_O_l p q Hpq').
 intros Hq Hp.
 apply False_ind;omega.
 unfold Qpositive_c at 2;fold Qpositive_c.
  
 rewrite e0.
 rewrite (IHq p'x);try omega.
 reflexivity.
Qed.

Lemma Qpositive_c_equal_strong :
 forall m1 m2 n1 n2 p1 p2 : nat,
 m1 = m2 ->
 n1 = n2 ->
 0 < m1 ->
 0 < n1 ->
 m1 + n1 <= p1 ->
 m2 + n2 <= p2 -> Qpositive_c m1 n1 p1 = Qpositive_c m2 n2 p2.
Proof.
 intros m1 m2 n1 n2 p1 p2 Hm Hn Hm' Hn' H1 H2; subst; apply Qpositive_c_equal;
  assumption.
Qed.

Functional Scheme Qpositive_plus_ind := Induction for Qpositive_plus Sort Prop.

Lemma what_nR_does : forall p : Qpositive, nR p = Qpositive_plus p One.
Proof.
 intros qp.
 unfold Qpositive_plus;fold Qpositive_plus.
 functional induction (Qpositive_plus qp One).
 rewrite e;rewrite e0.
 rename e into H_pq.
 rename e0 into H_p'q'.
 generalize (interp_non_zero qp).
 rename q0 into q.
 intros (p0', (q0', Hpq')).

 rewrite H_pq in Hpq'.
 let f_local := eval compute in (f_equal (fst (B:=_)) Hpq') in
 let g_local := eval compute in (sym_eq (f_equal (fst (B:=_)) H_p'q')) in
 generalize f_local g_local. 
 let f_local := eval compute in (f_equal (snd (B:=_)) Hpq') in
 let g_local := eval compute in (sym_eq (f_equal (snd (B:=_)) H_p'q')) in
 generalize f_local g_local. 
 intros Hq Hq' Hp Hp'. 
 subst.
 rewrite <- (mult_n_Sm (S q0') 0).
 repeat rewrite <- plus_n_Sm.
 rewrite <- mult_n_O.
 rewrite plus_O_n.
 rewrite mult_1_l.
 rewrite mult_1_r.
 rewrite Qpositive_c_nR. 
 rewrite plus_comm.
 rewrite minus_plus.
 apply f_equal with Qpositive.
 symmetry  in |- *; apply construct_correct.
 assumption.
 rewrite plus_comm.
 apply le_plus_l.
 clear;  omega.
Qed.



Functional Scheme Qpositive_mult_ind := Induction for Qpositive_mult Sort Prop.

Lemma what_dL_does :
 forall p : Qpositive,
 dL p = Qpositive_mult p (Qpositive_inv (Qpositive_plus p One)).
Proof.
 intros qp.

(* induction bug ? *)  unfold Qpositive_plus. (* /*)

 functional induction (Qpositive_plus qp One).
 rewrite e;rewrite e0.
 rename q0 into q;
   rename e into H_eq_;
     rename e0 into H_eq_0.

 generalize (interp_non_zero qp).
 intros (p0, (q0, Hpq)).
 rewrite H_eq_ in Hpq.
 let f_local := eval compute in (f_equal (fst (B:=_)) Hpq) in
 let g_local := eval compute in (sym_eq (f_equal (fst (B:=_)) H_eq_0)) in
 generalize f_local g_local. 
 let f_local := eval compute in (f_equal (snd (B:=_)) Hpq) in
 let g_local := eval compute in (sym_eq (f_equal (snd (B:=_)) H_eq_0)) in
 generalize f_local g_local. 
 intros Hq Hq' Hp Hp'. 
 subst.
 rewrite <- (mult_n_Sm (S q0) 0).
 repeat rewrite <- plus_n_Sm.
 rewrite <- mult_n_O.
 rewrite plus_O_n.
 rewrite mult_1_l.
 rewrite mult_1_r.
 unfold Qpositive_mult in |- *.
 rewrite H_eq_.
 set
  (P :=
   Qpositive_i (Qpositive_c (S p0 + S q0) (S q0) (S (S p0 + S q0 + q0))))
  in *.
 set (p' := fst P) in *.
 set (q' := snd P) in *.
 assert
  (H_P :
   Qpositive_i (Qpositive_c (S p0 + S q0) (S q0) (S (S p0 + S q0 + q0))) =
   (p', q')).
 replace (p', q') with P; trivial; unfold p', q' in |- *; apply pair_1.
 rewrite (inv_correct _ _ _ H_P).
 rewrite (Qpositive_c_unfold1 p0 q0 (S p0 + S q0 + q0)) in H_P.
 rewrite
  (construct_correct qp (S p0) (S q0) (S p0 + S q0 + q0) H_eq_
     (le_plus_l _ _)) in H_P.  
 rewrite (Qpositive_i_nR qp _ _ H_eq_) in H_P.
 let f_local :=
  eval cbv beta delta -[plus] in (sym_eq (f_equal (fst (B:=_)) H_P)) in
 let g_local :=
  eval cbv beta delta -[plus] in (sym_eq (f_equal (snd (B:=_)) H_P)) in
 generalize f_local g_local. 
 intros Hp' Hq'; rewrite Hp'; rewrite Hq'.
 clear H_eq_0 Hpq H_P Hp' Hq' P p' q'.
 rewrite <- (mult_n_Sm (S p0) q0).
 rewrite <- plus_n_Sm.
 rewrite (plus_Sn_m (S p0 * q0 + p0)).
 replace (S (S p0 * q0 + p0)) with (S q0 * S p0).
 rewrite Qpositive_c_dL.
 replace (S q0 * (S p0 + S q0) - S q0 * S p0) with (S q0 * S q0).
 apply f_equal with Qpositive.
 symmetry  in |- *.
 rewrite
  (construct_correct4' (S q0 * S p0) (S q0 * S q0) 
     (S p0) (S q0) (S p0 * q0 + p0 + S q0 * (S p0 + S q0)) 
     (S p0 + S q0)).
 apply construct_correct.  
 assumption.
 omega.
 rewrite <- mult_n_Sm.
 rewrite <- plus_n_Sm.
 auto with arith.
 rewrite <- mult_n_Sm.
 rewrite <- plus_n_Sm.
 auto with arith.
 auto with arith.
 auto with arith.
 rewrite mult_plus_distr_l.
 apply le_plus_r.
 apply le_n.
 rewrite (mult_comm (S q0) (S p0)).
 auto with arith.
 rewrite mult_plus_distr_l.
 rewrite minus_plus; reflexivity.
 rewrite mult_plus_distr_l.
 rewrite plus_comm.
 repeat rewrite <- mult_n_Sm.
 rewrite <- plus_n_Sm.
 rewrite <- plus_n_Sm with (m := q0).
 generalize (S q0 * p0 + q0) (S q0 * q0 + q0); clear qp H_eq_; intros;
  omega.
 rewrite mult_comm.
 rewrite <- mult_n_Sm.
 rewrite <- plus_n_Sm; reflexivity.
 rewrite plus_n_Sm.
 apply le_n.
Qed.

Lemma Qpos_nR : forall p : Qpositive, Qpos (nR p) = Qplus (Qpos p) Qone.
Proof.
 intros.
 simpl in |- *.
 apply f_equal with Qpositive.
 apply what_nR_does.
Qed. 

Lemma Qmult_Z_nR :
 forall (a : Z) (p : Qpositive),
 Qmult (Z_to_Q a) (Qpos (nR p)) =
 Qplus (Qmult (Z_to_Q a) (Qpos p)) (Z_to_Q a).
Proof.
 intros.
 rewrite Qpos_nR.
 ring.
Qed.

Lemma Qpos_dL :
 forall p : Qpositive,
 Qpos (dL p) = Qmult (Qpos p) (Qinv (Qplus (Qpos p) Qone)).
Proof.
 intros.
 simpl in |- *.
 apply f_equal with Qpositive.
 apply what_dL_does.
Qed. 

Lemma Qmult_Z_dL :
 forall (a : Z) (p : Qpositive),
 Qmult (Z_to_Q a) (Qpos (dL p)) =
 Qmult (Qmult (Z_to_Q a) (Qpos p)) (Qinv (Qplus (Qpos p) Qone)).
Proof.
 intros.
 rewrite Qpos_dL.
 ring.
Qed.

(** mappings between Q and Z *)


Lemma length_of_Qpositive_is_length :
 forall p : positive,
 length_of_Qpositive (Qpositive_c (nat_of_P p) 1 (S (nat_of_P p))) =
 (Zpos p - 1)%Z.
Proof.
 intro p.
 generalize (lt_O_nat_of_P p).
 rewrite <- ZL9.
 generalize (nat_of_P p).
 induction n.
 intro.
 inversion H.
 intro.
 case (le_lt_eq_dec 1 (S n) (lt_le_S _ _ H)).
 intro H1.
 rewrite (Qpositive_c_nR _ _ (S n) H1).
 transitivity (1 + length_of_Qpositive (Qpositive_c (S n - 1) 1 (S n)))%Z.
 reflexivity.
 rewrite Znat.inj_S.
 rewrite Zplus_comm.
 unfold Z.succ in |- *. 
 transitivity (n - 1 + 1)%Z; [ idtac | omega ].
 apply f_equal2 with Z Z; trivial. 
 rewrite <- IHn.
 apply f_equal with Qpositive.
 apply f_equal3 with nat nat nat; trivial.
 simpl in |- *; auto with arith. 
 omega.
 intro H1; rewrite <- H1.
 rewrite Qpositive_c_equal_One; trivial.
Qed.

Lemma Qpositive_to_Z_is_integer_part :
 forall x : positive,
 Qpositive_to_Z (Qpositive_c (nat_of_P x) 1 (S (nat_of_P x))) = Zpos x.
Proof.
 intro p.
 generalize (lt_O_nat_of_P p).
 rewrite <- ZL9.
 generalize (nat_of_P p).
 induction n; intro H.
 inversion H.
 case (le_lt_eq_dec 1 (S n) (lt_le_S _ _ H)).
 intro H1.
 rewrite (Qpositive_c_nR _ _ (S n) H1).
 transitivity (1 + Qpositive_to_Z (Qpositive_c (S n - 1) 1 (S n)))%Z.
 reflexivity.
 rewrite Znat.inj_S.
 rewrite Zplus_comm.
 unfold Z.succ in |- *. 
 apply f_equal2 with Z Z; trivial. 
 rewrite <- IHn.
 apply f_equal with Qpositive.
 apply f_equal3 with nat nat nat; trivial.
 simpl in |- *; auto with arith. 
 omega.
 intro H1; rewrite <- H1.
 rewrite Qpositive_c_equal_One; trivial.
Qed.
 

Lemma Q_to_Z_to_Q : forall x : Z, Q_to_Z (Z_to_Q x) = x.
Proof.
 intros [| x| x]; trivial; unfold Z_to_Q in |- *; unfold Q_to_Z in |- *;
  rewrite Qpositive_to_Z_is_integer_part; reflexivity.
Qed.
  
Lemma eq_Z_to_Q : forall x y : Z, Z_to_Q x = Z_to_Q y -> x = y.
Proof.
 intros x y H.
 generalize (f_equal Q_to_Z H). 
 intro H0.
 rewrite (Q_to_Z_to_Q x) in H0.
 rewrite (Q_to_Z_to_Q y) in H0.
 assumption.
Qed.

Lemma Z_to_Qpositive_equal :
 forall (m1 m2 : Z) (Hm1 : (0 < m1)%Z) (Hm2 : (0 < m2)%Z),
 m1 = m2 -> Z_to_Qpositive m1 Hm1 = Z_to_Qpositive m2 Hm2.
Proof.
  intros m1;
  induction m1.

  discriminate Hm1.

  unfold Z_to_Qpositive.
  intros m2 H Hm2 H_eq;revert Hm2.
  rewrite <- H_eq;reflexivity.

  intros m2 m1 abs;discriminate.
Qed. 

Functional Scheme Z_to_Q_ind := Induction for Z_to_Q Sort Prop.

Lemma Z_to_Qpositive_to_Q :
 forall (m : Z) (Hm : (0 < m)%Z), Z_to_Q m = Qpos (Z_to_Qpositive m Hm).
Proof.
 intros m; functional induction (Z_to_Q m); intros Hm;
            discriminate Hm || trivial.
Qed. 

Lemma Qpos_injective :
 forall qp1 qp2 : Qpositive, Qpos qp1 = Qpos qp2 -> qp1 = qp2.
Proof.
 intros qp1 qp2 H; injection H; trivial.
Qed.

Lemma Qneg_injective :
 forall qp1 qp2 : Qpositive, Qneg qp1 = Qneg qp2 -> qp1 = qp2.
Proof.
 intros qp1 qp2 H; injection H; trivial.
Qed.


Lemma Q_tail_Q_pos : forall q : Q, Qlt Zero q -> q = Qpos (Q_tail q).
Proof.
 intros [| q| q]; unfold Qlt in |- *; intros H;
            inversion H || unfold Q_tail in |- *; reflexivity.
Qed.

Lemma Q_tail_Q_neg : forall q : Q, Qlt q Zero -> q = Qneg (Q_tail q).
Proof.
 intros [| q| q]; unfold Qlt in |- *; intros H;
            inversion H || unfold Q_tail in |- *; reflexivity.
Qed.

Lemma Qpositive_to_Z_nonneg : forall x : Qpositive, (0 <= Qpositive_to_Z x)%Z.
Proof.
 intros x; induction  x as [x Hrecx| x Hrecx| ];
            [ replace (Qpositive_to_Z (nR x)) with (1 + Qpositive_to_Z x)%Z;
               trivial; abstract omega
            | simpl in |- *; apply Z.le_refl
            | simpl in |- *; intro H; discriminate ].
Qed. 
 
Functional Scheme Qpositive_le_bool_ind := 
  Induction for Qpositive_le_bool Sort Prop.

Lemma Qpositive_to_Z_Qpositive_le :
 forall x y : Qpositive,
 (Qpositive_to_Z x < Qpositive_to_Z y)%Z -> Qpositive_le x y.
Proof.
 intros x y.
 unfold Qpositive_le in |- *.
 functional induction (Qpositive_le_bool x y) ;intros; 
    trivial.
 apply IHb.
 unfold Qpositive_to_Z in H;fold Qpositive_to_Z in H. 
 omega.
unfold Qpositive_to_Z in H;fold Qpositive_to_Z in H;
 generalize (Qpositive_to_Z_nonneg y);intros;
 apply False_ind;omega.
unfold Qpositive_to_Z in H;fold Qpositive_to_Z in H;
 generalize (Qpositive_to_Z_nonneg y);intros;
 apply False_ind;omega.
 apply IHb.
 unfold Qpositive_to_Z in H;fold Qpositive_to_Z in H. 
 omega.
 unfold Qpositive_to_Z in H;fold Qpositive_to_Z in H;discriminate.
Qed.


Lemma Q_to_Z_monotone : forall x y : Q, Qlt x y -> (Q_to_Z x <= Q_to_Z y)%Z.
Proof.
 intros x y.
 unfold Qlt in |- *.
 intro H.
 induction H; simpl in |- *; apply not_Zlt; intro H1.
 apply H; apply Qpositive_to_Z_Qpositive_le; assumption.
 generalize (Zmin_cancel_Zlt _ _ H1); intro H2; apply H;
  apply Qpositive_to_Z_Qpositive_le; assumption.
 apply Z.lt_irrefl with 0%Z; generalize (Qpositive_to_Z_nonneg x'); intro H2;
  omega.
 apply Z.lt_irrefl with 0%Z; generalize (Qpositive_to_Z_nonneg x');
  generalize (Qpositive_to_Z_nonneg y'); intros H2 H3; abstract 
  omega.
 apply Z.lt_irrefl with 0%Z; generalize (Qpositive_to_Z_nonneg x'); intro H2;
  omega.
Qed.



Lemma Qlt_irreflexive : forall x : Q, ~ Qlt x x.
Proof.
 intro x; unfold Qlt in |- *; intro H; apply Qgt_antisym with x x; assumption.
Qed.

Hint Resolve Qlt_irreflexive.

Lemma Qlt_not_eq : forall x y : Q, Qlt x y -> y <> x.
Proof.
 intros x y Hxlty Hxy; rewrite Hxy in Hxlty; apply Qlt_irreflexive with x;
  assumption.
Qed. 

Hint Resolve Qlt_not_eq.

Lemma Qlt_transitive : forall x y z : Q, Qlt x y -> Qlt y z -> Qlt x z.
Proof.
 intros x y z H1 H2.
 unfold Qlt in |- *.
 apply Qgt_trans with y; assumption.
Qed.

Lemma Z_to_Qopp : forall x : Z, Z_to_Q (- x) = Qopp (Z_to_Q x).
Proof.
 intros [| x| x]; trivial.
Qed. 

Lemma Z_to_Qplus_POS :
 forall p1 p2 : positive,
 Z_to_Q (Zpos p1 + Zpos p2) = Qplus (Z_to_Q (Zpos p1)) (Z_to_Q (Zpos p2)).
Proof.
 intros p1 p2.
  unfold Z_to_Q at 2 3 in |- *.
  unfold Qplus in |- *.
  rewrite <- BinInt.Zpos_plus_distr.
  unfold Z_to_Q at 1 in |- *.
  apply f_equal with Qpositive.
  unfold Qpositive_plus in |- *.
  repeat rewrite Qpositive_i_c. 
  repeat rewrite mult_1_l.
  repeat rewrite mult_1_r.
  apply f_equal3 with nat nat nat; trivial.
  apply nat_of_P_plus_morphism.
  rewrite nat_of_P_plus_morphism.
  omega.
  apply lt_O_nat_of_P.
  constructor.
  apply lt_O_nat_of_P.
  constructor. 
Qed.

Lemma Z_to_Qplus_POS_NEG :
 forall p1 p2 : positive,
 Z_to_Q (Zpos p1 + Zneg p2) = Qplus (Z_to_Q (Zpos p1)) (Z_to_Q (Zneg p2)).
Proof.
 intros p1 p2.

  assert
   (H :
    Qplus (Z_to_Q (Zpos p1 + Zneg p2)) (Z_to_Q (Zpos p2)) = Z_to_Q (Zpos p1)).
  set (P := (Zpos p1 + Zneg p2)%Z) in *.
  assert (P = (Zpos p1 + Zneg p2)%Z); trivial.
  destruct P.
  unfold Z_to_Q at 1 in |- *.
  rewrite Qplus_zero_left.
  apply f_equal with Z.
  transitivity (- Zneg p2)%Z; trivial.
  omega.
  rewrite <- Z_to_Qplus_POS.
  apply f_equal with Z.
  replace (Zpos p2) with (- Zneg p2)%Z; trivial.  
  omega.
  
  unfold Z_to_Q at 1 2 3 in |- *.
  assert (Hp : (Zpos p < Zpos p2)%Z).
  apply Zmin_cancel_Zlt.
  unfold Z.opp in |- *.
  rewrite H.
  rewrite <- (Zplus_0_l (Zneg p2)).
  apply Zplus_lt_compat_r.
  constructor.

  unfold Qplus in |- *.
  
  case
   (Qpositive_le_dec (Qpositive_c (nat_of_P p) 1 (S (nat_of_P p)))
      (Qpositive_c (nat_of_P p2) 1 (S (nat_of_P p2)))); 
   intro H1.
   case
    (Qpositive_eq_dec (Qpositive_c (nat_of_P p) 1 (S (nat_of_P p)))
       (Qpositive_c (nat_of_P p2) 1 (S (nat_of_P p2)))); 
    intro H2.
    apply False_ind.
    generalize (f_equal Qpositive_to_Z H2). 
    do 2 rewrite Qpositive_to_Z_is_integer_part.
    apply Zorder.Zlt_not_eq; assumption.

    assert (Hp' : Zpos p2 = (Zpos p1 + Zpos p)%Z).
    clear H1 H2.
    replace (Zpos p) with (- Zneg p)%Z; trivial.
    rewrite H.
    replace (Zneg p2) with (- Zpos p2)%Z; trivial.
    auto with zarith.
    rewrite <- BinInt.Zpos_plus_distr in Hp'.
    generalize (POS_resp_eq _ _ Hp').
    intro Hp2.

    apply f_equal with Qpositive.
    unfold Qpositive_sub in |- *.
    repeat rewrite Qpositive_i_c. 
    repeat rewrite mult_1_l.
    repeat rewrite mult_1_r.
    clear H1 H2; apply Qpositive_c_equal_strong; trivial; try omega;
     rewrite Hp2; rewrite nat_of_P_plus_morphism.
    omega.
    replace (nat_of_P p1 + nat_of_P p - nat_of_P p) with (nat_of_P p1);
     [ apply lt_O_nat_of_P | omega ].
    apply lt_O_nat_of_P.
    constructor.
    apply lt_O_nat_of_P.
    constructor. 

   apply False_ind; apply H1.
   apply Qpositive_to_Z_Qpositive_le.
   do 2 rewrite Qpositive_to_Z_is_integer_part.
   assumption.
  
 rewrite <- H.
 replace (Zneg p2) with (- Zpos p2)%Z; trivial.
 rewrite Z_to_Qopp.
 ring.
Qed. 
 
Lemma Z_to_Qplus_NEG :
 forall p1 p2 : positive,
 Z_to_Q (Zneg p1 + Zneg p2) = Qplus (Z_to_Q (Zneg p1)) (Z_to_Q (Zneg p2)).
Proof.
 intros p1 p2.
 replace (Zneg p1) with (- Zpos p1)%Z; trivial.
 replace (Zneg p2) with (- Zpos p2)%Z; trivial.
 rewrite <- Zopp_plus_distr.
 repeat rewrite Z_to_Qopp.
 rewrite Z_to_Qplus_POS.
 ring. 
Qed.

Lemma Z_to_Qplus :
 forall x y : Z, Z_to_Q (x + y) = Qplus (Z_to_Q x) (Z_to_Q y).
Proof.
 intros [| x| x] [| y| y]; trivial;
  [ apply Z_to_Qplus_POS
  | apply Z_to_Qplus_POS_NEG
  | rewrite Zplus_comm; rewrite Qplus_sym; apply Z_to_Qplus_POS_NEG
  | apply Z_to_Qplus_NEG ].
Qed.

Lemma Z_to_Qminus :
 forall x y : Z, Z_to_Q (x - y) = Qminus (Z_to_Q x) (Z_to_Q y).
Proof.
 intros x y.
 unfold Zminus in |- *.
 rewrite Z_to_Qplus.
 rewrite Z_to_Qopp.
 reflexivity.
Qed.

Lemma Z_to_Qmult_POS :
 forall p1 p2 : positive,
 Z_to_Q (Zpos p1 * Zpos p2) = Qmult (Z_to_Q (Zpos p1)) (Z_to_Q (Zpos p2)).
Proof.
 intros p1 p2.
 unfold Z_to_Q at 2 3 in |- *.
 unfold Qmult in |- *.
 replace (Zpos p1 * Zpos p2)%Z with (Zpos (p1 * p2)); trivial. 
 unfold Z_to_Q at 1 in |- *.
 apply f_equal with Qpositive.
 unfold Qpositive_mult in |- *.
 repeat rewrite Qpositive_i_c. 
 repeat rewrite mult_1_l.
 apply f_equal3 with nat nat nat; trivial.
 apply nat_of_P_mult_morphism.
 rewrite nat_of_P_mult_morphism.
 omega.
 apply lt_O_nat_of_P.
 constructor.
 apply lt_O_nat_of_P.
 constructor. 
Qed.

Lemma Z_to_Qmult_POS_NEG :
 forall p1 p2 : positive,
 Z_to_Q (Zpos p1 * Zneg p2) = Qmult (Z_to_Q (Zpos p1)) (Z_to_Q (Zneg p2)).
Proof.
 intros p1 p2.
 unfold Z_to_Q at 2 3 in |- *.
 unfold Qmult in |- *.
 replace (Zpos p1 * Zneg p2)%Z with (Zneg (p1 * p2)); trivial. 
 unfold Z_to_Q at 1 in |- *.
 apply f_equal with Qpositive.
 unfold Qpositive_mult in |- *.
 repeat rewrite Qpositive_i_c. 
 repeat rewrite mult_1_l.
 apply f_equal3 with nat nat nat; trivial.
 apply nat_of_P_mult_morphism.
 rewrite nat_of_P_mult_morphism.
 omega.
 apply lt_O_nat_of_P.
 constructor.
 apply lt_O_nat_of_P.
 constructor. 
Qed.

Lemma Z_to_Qmult_NEG :
 forall p1 p2 : positive,
 Z_to_Q (Zneg p1 * Zneg p2) = Qmult (Z_to_Q (Zneg p1)) (Z_to_Q (Zneg p2)).
Proof.
 intros p1 p2.
 unfold Z_to_Q at 2 3 in |- *.
 unfold Qmult in |- *.
 replace (Zneg p1 * Zneg p2)%Z with (Zpos (p1 * p2)); trivial. 
 unfold Z_to_Q at 1 in |- *.
 apply f_equal with Qpositive.
 unfold Qpositive_mult in |- *.
 repeat rewrite Qpositive_i_c. 
 repeat rewrite mult_1_l.
 apply f_equal3 with nat nat nat; trivial.
 apply nat_of_P_mult_morphism.
 rewrite nat_of_P_mult_morphism.
 omega.
 apply lt_O_nat_of_P.
 constructor.
 apply lt_O_nat_of_P.
 constructor. 
Qed.

Lemma Z_to_Qmult :
 forall x y : Z, Z_to_Q (x * y) = Qmult (Z_to_Q x) (Z_to_Q y).
Proof.
 intros [| x| x] [| y| y]; trivial;
  [ apply Z_to_Qmult_POS
  | apply Z_to_Qmult_POS_NEG
  | rewrite Zmult_comm; rewrite Qmult_sym; apply Z_to_Qmult_POS_NEG
  | apply Z_to_Qmult_NEG ].
Qed.


Lemma Z_to_Q_S:forall k, Z_to_Q (Z_of_nat (S k))=Qplus k Qone.
Proof.
 induction k; trivial.
 rewrite inj_S; unfold Z.succ; rewrite Z_to_Qplus; rewrite IHk;
 unfold Z_to_Q at 2; simpl; fold Qone; ring.
Qed.

Lemma Z_to_Q_min_one:Z_to_Q (-1)%Z= Qopp Qone.
Proof.
 reflexivity.
Qed.

Lemma Qlt_Zero_Qminus : forall x y : Q, Qlt Zero (Qminus y x) -> Qlt x y. 
Proof.
 intros x y H; replace x with (Qplus x Zero); [ idtac | ring ];
            replace y with (Qplus x (Qminus y x)); 
            [ idtac | ring ]; unfold Qlt in |- *; apply Qgt_plus; 
            assumption.
Qed.

Lemma Z_to_Qlt : forall x y : Z, (x < y)%Z -> Qlt x y.
Proof. 
 intros x y H.
 apply Qlt_Zero_Qminus.
 generalize (Z.lt_gt _ _ H); clear H; intro H.
 case (Zcompare_Gt_spec _ _ H).
 intros p Hp.
 rewrite <- Z_to_Qminus.
 unfold Zminus in |- *.
 rewrite Hp.
 unfold Z_to_Q in |- *.
 apply Qlt_zero_pos.
Qed.


Lemma lt_Z_to_Q : forall x y : Z, Qlt (Z_to_Q x) (Z_to_Q y) -> (x < y)%Z.
Proof.
 intros x y H.  
 case (Z_dec' x y).
 intros [H1| H1]; trivial.
 apply False_ind.
 apply Qlt_irreflexive with x.
 apply Qlt_transitive with y; trivial.
 apply Z_to_Qlt; assumption.
 intro H1.
 apply False_ind.
 rewrite H1 in H.
 generalize H.
 apply Qlt_irreflexive.
Qed. 
 
Lemma pos_Z_to_Q : forall x : Z, Qlt Zero (Z_to_Q x) -> (0 < x)%Z.
Proof.
 intros x H.
 apply lt_Z_to_Q; assumption.
Qed.

Lemma neg_Z_to_Q : forall x : Z, Qlt (Z_to_Q x) Zero -> (x < 0)%Z.
Proof.
 intros x H.
 apply lt_Z_to_Q; assumption.
Qed.

Lemma Qlt_le_weak : forall x y : Q, Qlt x y -> Qle x y.
Proof.
 intros x y H.
 unfold Qle in |- *.
 intro H2; apply Qlt_irreflexive with x; apply Qlt_transitive with y;
  assumption. 
Qed.


Lemma Z_to_Qle : forall x y : Z, (x <= y)%Z -> Qle x y.
Proof.
 intros x y H.
 case (Z_le_lt_eq_dec _ _ H); intro H1.
 apply Qlt_le_weak; apply Z_to_Qlt; assumption.
 rewrite H1; unfold Qle in |- *; apply Qlt_irreflexive.
Qed.

Lemma Z_to_Q_pos : forall x : Z, (0 < x)%Z -> Qlt Zero x.
Proof.
 intros x H.
 replace Zero with (Z_to_Q 0); trivial.
 apply Z_to_Qlt; assumption.
Qed.


Lemma Z_to_Q_neg : forall x : Z, (x < 0)%Z -> Qlt x Zero.
Proof.
 intros x H.
 replace Zero with (Z_to_Q 0); trivial.
 apply Z_to_Qlt; assumption.
Qed.

Lemma Z_to_Q_nonneg : forall x : Z, (0 <= x)%Z -> Qle Zero x.
Proof.
 intros x H.
 replace Zero with (Z_to_Q 0); trivial.
 apply Z_to_Qle; assumption.
Qed.

Lemma Z_to_Q_nonpos : forall x : Z, (x <= 0)%Z -> Qle x Zero.
Proof.
 intros x H.
 replace Zero with (Z_to_Q 0); trivial.
 apply Z_to_Qle; assumption.
Qed.


Lemma Z_to_Q_not_eq : forall a b : Z, a <> b -> Z_to_Q a <> Z_to_Q b.
Proof.
 intros a b Hab HabQ; apply Hab; apply eq_Z_to_Q; assumption.
Qed.


Lemma Qmult_Z_plus_Z_dL :
 forall (a b : Z) (p : Qpositive),
 Qplus (Qmult (Z_to_Q a) (Qpos (dL p))) (Z_to_Q b) =
 Qmult (Qplus (Qmult (Z_to_Q (a + b)) (Qpos p)) (Z_to_Q b))
   (Qinv (Qplus (Qpos p) Qone)).
Proof.
 intros; rewrite Qmult_Z_dL.
 rewrite Z_to_Qplus; field; discriminate.
Qed.

Lemma Qinv_0 : forall q : Q, Qinv q = Zero -> q = Zero. 
Proof.
 intros [| qp | qp ] Hqp; try trivial; discriminate Hqp.
Qed. 

Lemma Qmult_resp_nonzero :
 forall x y : Q, x <> Zero -> y <> Zero -> Qmult x y <> Zero.
Proof.
 intros x y Hx Hy Hxy; generalize (Q_integral _ _ Hxy); intros [H| H];
  [ apply Hx | apply Hy ]; assumption.
Qed.

Hint Resolve Qmult_resp_nonzero.

Lemma Qlt_mult_pos_pos :
 forall x y : Q, Qlt Zero x -> Qlt Zero y -> Qlt Zero (Qmult x y).
Proof.
 intros [| x| x] [| y| y] Hx Hy; trivial; simpl in |- *;
            auto with *; [ inversion Hy | inversion Hx ].
Qed.


Lemma Qlt_mult_neg_pos :
 forall x y : Q, Qlt x Zero -> Qlt Zero y -> Qlt (Qmult x y) Zero.
Proof.
 intros [| x| x] [| y| y] Hx Hy; trivial; simpl in |- *;
            auto with *; [ inversion Hx | inversion Hy ].
Qed.

Hint Resolve Qlt_mult_pos_pos Qlt_mult_neg_pos.


Lemma Qlt_plus_pos_pos :
 forall x y : Q, Qlt Zero x -> Qlt Zero y -> Qlt Zero (Qplus x y).
Proof.
 intros [| x| x] [| y| y] Hx Hy; trivial; simpl in |- *;
            auto with *; [ inversion Hy | inversion Hx | inversion Hx ].
Qed.

Hint Resolve Qlt_plus_pos_pos.



(** This lemma also holds for q2=Zero, due to our definition of (Qinv Zero):=Zero,
    Perhaps it is not right to state it like this but anyways it is true *)
Lemma Qdiv_num_denom :
 forall q1 q2 p : Q,
 p <> Zero -> Qmult q1 (Qinv q2) = Qmult (Qmult q1 p) (Qinv (Qmult q2 p)).
Proof.
intros q1 [| qp| qp] p Hp;
 (simpl in |- *; ring) || (field; split; discriminate || assumption).
Qed.


Lemma Qinv_1 : forall q : Q, Qlt Zero (Qinv q) -> Qlt Zero q.
Proof.
 intros [| q| q] Hq; trivial; inversion Hq.
Qed.

Lemma Qinv_2 : forall q : Q, Qlt (Qinv q) Zero -> Qlt q Zero.
Proof.
 intros [| q| q] Hq; trivial; inversion Hq.
Qed.

Lemma Qinv_pos : forall q : Q, Qlt Zero q -> Qlt Zero (Qinv q).
Proof.
 intros [| q| q] Hq; simpl in |- *; trivial; inversion Hq.
Qed.

Lemma Qmult_one_right : forall x : Q, Qmult x Qone = x.
Proof.
 intro q; rewrite Qmult_sym; apply Qmult_one_left.
Qed.

Lemma Qpos_POS_1 :
 forall (m : Z) (qp : Qpositive), Z_to_Q m = Qpos qp -> (0 < m)%Z.
Proof.
 intros m qp Hm; apply pos_Z_to_Q; rewrite Hm; apply Qlt_zero_pos.
Qed.

Lemma Qneg_NEG_1 :
 forall (m : Z) (qp : Qpositive), Z_to_Q m = Qneg qp -> (m < 0)%Z.
Proof.
 intros m qp Hm; apply neg_Z_to_Q; rewrite Hm; apply Qlt_neg_zero.
Qed.


Lemma Qopp_Qpos : forall q : Qpositive, Qneg q = Qopp (Qpos q).
Proof.
 trivial.
Qed.

Lemma Qopp_Qneg : forall q : Qpositive, Qpos q = Qopp (Qneg q).
Proof.
 trivial.
Qed.

Lemma Qopp_linear :
 forall (a b : Z) (q : Qpositive),
 Qplus (Qmult (Z_to_Q (- a)) (Qpos q)) (Z_to_Q (- b)) =
 Qopp (Qplus (Qmult (Z_to_Q a) (Qpos q)) (Z_to_Q b)).
Proof.
 intros a b q; repeat rewrite Zopp_eq_mult_neg_1;
            repeat rewrite Z_to_Qmult; repeat rewrite <- Qmult_assoc;
            rewrite (Qmult_sym (-1)%Z); repeat rewrite Qmult_assoc;
            repeat rewrite <- Q_distr_left;
            replace (Z_to_Q (-1)) with (Qopp Qone); 
            [ ring | reflexivity ].
Qed. 


Lemma Qopp_resp_nonzero : forall x : Q, x <> Zero -> Qopp x <> Zero.
Proof.
 intros [| qx| qx] H; discriminate || Falsum.
Qed.

(** This also holds for q=Zero so we don't exclude that case *)
Lemma Qinv_Qopp : forall q : Q, Qinv (Qopp q) = Qopp (Qinv q).
Proof.
 intros [| q| q]; reflexivity.
Qed. 

Lemma Qmult_Qopp_left : forall x y : Q, Qmult (Qopp x) y = Qopp (Qmult x y).
Proof.
 intros [| qx| qx] [| qy| qy]; reflexivity.
Qed.


Lemma Qpositive_dec_One : forall p : Qpositive, {p = One} + {p <> One}.
Proof. 
 intro p; exact (Qpositive_eq_dec p One).
Defined.

Lemma Q_zerop : forall x : Q, {x = Zero} + {x <> Zero}.
Proof.
 intros [| px| px]; solve [ left; trivial | right; discriminate ].
Qed.         
 
Lemma Qinv_resp_nonzero : forall x : Q, x <> Zero -> Qinv x <> Zero.
Proof.
 intros [| px| px] Hx; solve [ Falsum | discriminate ].
Qed. 

Lemma Qlt_zero_one : Qlt Zero Qone.
Proof.
 unfold Qone in |- *; apply Qlt_zero_pos. 
Qed.

Hint Resolve Qlt_zero_one.

Lemma Z_to_Qpositive_Q_tail_pos :
 forall (a : Z) (Ha : (0 < a)%Z), Z_to_Qpositive a Ha = Q_tail a.
Proof.
 intros [| px| px] Hx; discriminate Hx || reflexivity.
Qed.

Lemma Q_tail_Qinv : forall x : Q, Q_tail (Qinv x) = Qpositive_inv (Q_tail x).
Proof.
 intros [| px| px]; trivial.
Qed.

Lemma Q_tail_Qmult :
 forall x y : Q,
 x <> Zero ->
 y <> Zero -> Q_tail (Qmult x y) = Qpositive_mult (Q_tail x) (Q_tail y). 
Proof.
 intros [| px| px] [| py| py] Hx Hy; trivial; Falsum.
Qed.


Lemma Q_tail_Qplus_pos :
 forall x y : Q,
 Qlt Zero x ->
 Qlt Zero y -> Q_tail (Qplus x y) = Qpositive_plus (Q_tail x) (Q_tail y). 
Proof.
 intros [| px| px] [| py| py] Hx Hy; trivial; solve
            [ inversion Hx | inversion Hy ].
Qed.


Lemma Q_tail_Qplus_neg :
 forall x y : Q,
 Qlt x Zero ->
 Qlt y Zero -> Q_tail (Qplus x y) = Qpositive_plus (Q_tail x) (Q_tail y). 
Proof.
 intros [| px| px] [| py| py] Hx Hy; trivial; solve
            [ inversion Hx | inversion Hy ].
Qed.


Lemma Qplus_zero_right : forall n : Q, Qplus n Zero = n.
Proof.
 intros; field.
Qed.

Lemma Qmult_zero_right : forall x : Q, Qmult x Zero = Zero.
Proof.
 intros; field.
Qed.

Lemma Qle_Qpositive_le_pos :
 forall x y : Qpositive, Qle (Qpos x) (Qpos y) -> Qpositive_le x y.
Proof.
 intros x y H.
 case (Qpositive_le_dec x y); intros H1; trivial; apply False_ind; apply H;
  constructor; assumption.
Qed. 

Lemma Qle_Qpositive_le_neg :
 forall x y : Qpositive, Qle (Qneg x) (Qneg y) -> Qpositive_le y x.
Proof.
 intros x y H.
 case (Qpositive_le_dec y x); intros H1; trivial; apply False_ind; apply H;
  constructor; assumption.
Qed. 

Lemma Qle_lt_eq_dec : forall x y : Q, Qle x y -> {Qlt x y} + {x = y}.
Proof.
 intros [| x| x] [| y| y] Hxy;
  try solve
   [ right; reflexivity
   | left; auto with *
   | right; auto with *
   | apply False_rec; apply Hxy; auto with * ];
  [ generalize (Qle_Qpositive_le_pos _ _ Hxy)
  | generalize (Qle_Qpositive_le_neg _ _ Hxy) ]; clear Hxy; 
  intro Hxy;
  match goal with
  | id1:(Qpositive_le ?X1 ?X2) |- _ =>
      case (Qpositive_le_dec X2 X1); intro H;
       [ right; apply f_equal with Qpositive; apply Qpositive_le_antisym;
          assumption
       | left; constructor; assumption ]
  end. 
Qed.

Lemma Qle_lt_trans : forall x y z : Q, Qle x y -> Qlt y z -> Qlt x z.
Proof.
 intros [| x| x] [| y| y] [| z| z] Hxy Hyz; trivial; try QltCleanAbsurdCases;
  case (Qle_lt_eq_dec _ _ Hxy); intro Hxy';
  [ apply Qlt_transitive with (Qpos y)
  | rewrite Hxy'
  | apply Qlt_transitive with (Qneg y)
  | rewrite Hxy' ]; assumption.
Qed.

Lemma Qlt_le_trans : forall x y z : Q, Qlt x y -> Qle y z -> Qlt x z.
Proof.
 intros [| x| x] [| y| y] [| z| z] Hxy Hyz; trivial; try QltCleanAbsurdCases;
  case (Qle_lt_eq_dec _ _ Hyz); intro Hyz';
  [ apply Qlt_transitive with (Qpos y)
  | rewrite <- Hyz'
  | apply Qlt_transitive with (Qneg y)
  | rewrite <- Hyz' ]; assumption.
Qed.


Lemma Qle_trans : forall x y z : Q, Qle x y -> Qle y z -> Qle x z.
Proof.
 intros x y z Hxy Hyz Hxz; apply Hyz; apply Qlt_le_trans with x; assumption.
Qed.

Lemma Qlt_plus_plus :
 forall a b c d : Q, Qlt a b -> Qlt c d -> Qlt (Qplus a c) (Qplus b d).
Proof.
 intros a b c d Hab Hcd.
 apply Qlt_transitive with (Qplus b c); unfold Qlt in |- *;
  [ rewrite (Qplus_sym a); rewrite (Qplus_sym b) | idtac ]; 
  apply Qgt_plus; assumption.
Qed.

Lemma Qle_lt_reg :
 forall a b c d : Q, Qle a b -> Qlt c d -> Qlt (Qplus a c) (Qplus b d).
Proof.
 intros a b c d Hab Hcd.
 case (Qle_lt_eq_dec _ _ Hab); intro Hab';
  [ apply Qlt_plus_plus | rewrite Hab'; unfold Qlt in |- *; apply Qgt_plus ];
  assumption.
Qed.

 
Lemma Qlt_le_reg :
 forall a b c d : Q, Qlt a b -> Qle c d -> Qlt (Qplus a c) (Qplus b d).
Proof.
 intros a b c d Hab Hcd; rewrite (Qplus_sym a); rewrite (Qplus_sym b);
  apply Qle_lt_reg; assumption.
Qed.

Lemma Qlt_le_reg_pos :
 forall b d : Q, Qlt Zero b -> Qle Zero d -> Qlt Zero (Qplus b d).
Proof.
 intros b d Hb Hd; replace Zero with (Qplus Zero Zero); trivial;
  apply Qlt_le_reg; assumption.
Qed.

Lemma Qle_lt_reg_pos :
 forall b d : Q, Qle Zero b -> Qlt Zero d -> Qlt Zero (Qplus b d).
Proof.
 intros b d Hb Hd; replace Zero with (Qplus Zero Zero); trivial;
  apply Qle_lt_reg; assumption.
Qed.

Lemma Qlt_le_reg_neg :
 forall b d : Q, Qlt b Zero -> Qle d Zero -> Qlt (Qplus b d) Zero.
Proof.
 intros b d Hb Hd; replace Zero with (Qplus Zero Zero); trivial;
  apply Qlt_le_reg; assumption.
Qed.
 
Lemma Qle_lt_reg_neg :
 forall b d : Q, Qle b Zero -> Qlt d Zero -> Qlt (Qplus b d) Zero.
Proof.
 intros b d Hb Hd; replace Zero with (Qplus Zero Zero); trivial;
  apply Qle_lt_reg; assumption.
Qed.

Lemma Qle_plus_plus :
 forall a b c d : Q, Qle a b -> Qle c d -> Qle (Qplus a c) (Qplus b d).
Proof.
 intros a b c d Hab Hcd.
 apply Qle_trans with (Qplus b c); unfold Qlt in |- *;
  [ rewrite (Qplus_sym a); rewrite (Qplus_sym b) | idtac ];
  [ case (Qle_lt_eq_dec _ _ Hab) | case (Qle_lt_eq_dec _ _ Hcd) ]; 
  intro H_;
  [ apply Qlt_le_weak; apply Qle_lt_reg;
     [ unfold Qle in |- *; apply Qlt_irreflexive | assumption ]
  | rewrite H_; unfold Qle in |- *; apply Qlt_irreflexive
  | apply Qlt_le_weak; apply Qle_lt_reg;
     [ unfold Qle in |- *; apply Qlt_irreflexive | assumption ]
  | rewrite H_; unfold Qle in |- *; apply Qlt_irreflexive ].
Qed.

Lemma Qle_plus_pos_pos :
 forall x y : Q, Qle Zero x -> Qle Zero y -> Qle Zero (Qplus x y).
Proof.
 intros b d Hb Hd; replace Zero with (Qplus Zero Zero); trivial;
  apply Qle_plus_plus; assumption.
Qed.

Lemma Qle_plus_neg_neg :
 forall x y : Q, Qle x Zero -> Qle y Zero -> Qle (Qplus x y) Zero.
Proof.
 intros b d Hb Hd; replace Zero with (Qplus Zero Zero); trivial;
  apply Qle_plus_plus; assumption.
Qed.

Lemma Qle_mult_nonneg_nonneg :
 forall x y : Q, Qle Zero x -> Qle Zero y -> Qle Zero (Qmult x y).
Proof.
 intros [| x| x] [| y| y] Hx Hy; trivial; try QltCleanAbsurdCases;
  simpl in |- *; intro H_; inversion H_.
Qed.

Lemma Qle_mult_nonpos_nonneg :
 forall x y : Q, Qle x Zero -> Qle Zero y -> Qle (Qmult x y) Zero.
Proof.
 intros [| x| x] [| y| y] Hx Hy; trivial; try QltCleanAbsurdCases;
  simpl in |- *; intro H_; inversion H_.
Qed.

Lemma Qle_mult_nonneg_nonpos :
 forall x y : Q, Qle Zero x -> Qle y Zero -> Qle (Qmult x y) Zero.
Proof.
 intros [| x| x] [| y| y] Hx Hy; trivial; try QltCleanAbsurdCases;
  simpl in |- *; intro H_; inversion H_.
Qed.

Lemma Qle_mult_nonpos_pos:
 forall x y : Q, Qle x Zero -> Qlt Zero y -> Qle (Qmult x y) Zero.
Proof.
 intros [| x| x] [| y| y] Hx Hy; trivial; try QltCleanAbsurdCases;
  simpl in |- *; intro H_; inversion H_.
Qed.

Lemma Qle_mult_neg_nonneg :
 forall x y : Q, Qlt x Zero -> Qle Zero y -> Qle (Qmult x y) Zero.
Proof.
 intros [| x| x] [| y| y] Hx Hy; trivial; try QltCleanAbsurdCases;
  simpl in |- *; intro H_; inversion H_.
Qed.

Lemma Qle_reflexive:forall x, Qle x x.
Proof.
 intro x; unfold Qle; apply Qlt_irreflexive.
Qed.

Hint Resolve Qplus_zero_right Qlt_le_reg_pos Qle_lt_reg_pos Qlt_le_reg
  Qle_lt_reg Qlt_le_weak Qlt_le_reg_neg Qle_lt_reg_neg Qle_plus_pos_pos
  Qle_plus_neg_neg Qle_mult_nonneg_nonneg Qle_mult_nonneg_nonpos
  Qle_mult_nonpos_nonneg Qle_mult_nonpos_pos Qle_mult_neg_nonneg
  Qle_reflexive.

Lemma Qpos_not_lt_Zero : forall x, ~ Qlt (Qpos x) Zero.
Proof.
intros x Hc; apply (Qlt_irreflexive Zero); apply Qlt_transitive with (Qpos x);trivial.
Qed.

Lemma Qlt_dec_Qpos : forall x y, {~ Qlt (Qpos y) (Qpos x)} + {Qlt (Qpos y) (Qpos x)}.
  intros x y; case Qpositive_le_dec with x y; intro H'; [left;intro H; inversion H; contradiction | right;unfold Qlt; constructor; trivial].
Qed.

Lemma Zero_not_lt_Qneg : forall x, ~ Qlt Zero (Qneg x).
Proof.
intros x Hc; apply (Qlt_irreflexive Zero); apply Qlt_transitive with (Qneg x);trivial.
Qed.

Lemma Qpos_not_lt_Qneg : forall x y, ~ Qlt (Qpos y) (Qneg x).
Proof.
intros x y Hc; apply (Qlt_irreflexive (Qneg x)); apply Qlt_transitive with (Qpos y); trivial.
Qed.

Lemma Qlt_dec_Qneg : forall x y, {~ Qlt (Qneg y) (Qneg x)} + {Qlt (Qneg y) (Qneg x)}.
Proof.
intros x y; case Qpositive_le_dec with y x; intro H'; [left;intro H; inversion H; contradiction | right;unfold Qlt; constructor; trivial].
Qed.

Lemma Q_le_lt_dec:forall (x y:Q), {Qle x y}+{Qlt y x}.
Proof.
  intros [|x|x] [|y|y]; unfold Qle; try (right; trivial || fail).
  left; apply Qlt_irreflexive.
  left; apply Qpos_not_lt_Zero.
  apply Qlt_dec_Qpos.
  left; apply Zero_not_lt_Qneg.
  left; apply Qpos_not_lt_Qneg.
  apply Qlt_dec_Qneg.
Qed.

Lemma Qle_dec:forall (x y:Q), {Qle x y}+{~(Qle x y)}.
Proof.
 intros x y.
 case (Q_le_lt_dec x y);
 intros; [ left | right ] ; trivial.
 intros H'; apply H'; trivial.
Qed.

Lemma Qlt_dec:forall (x y:Q), {Qlt x y}+{~(Qlt x y)}.
Proof.
 intros x y.
 case (Q_le_lt_dec y x);
 intros; [ right | left ] ; trivial.
Qed.

Lemma Qtrichotomy_inf:forall x y,{Qlt x y}+{x=y}+{Qlt y x}.
Proof.
 intros x y.
 case (Q_le_lt_dec x y); intros H;
 [ case (Qle_lt_eq_dec x y H); intros H0; left;[left|right]
 | right
 ]; trivial.
Qed.

Lemma Qle_dec_weak:forall (x y:Q), {Qle x y}+{(Qle y x)}.
Proof.
 intros x y; case (Q_le_lt_dec x y); intros; [ left | right ] ; trivial; apply Qlt_le_weak; trivial.
Qed.

Lemma not_Qeq_inf : forall x y : Q, x <> y -> {Qlt x y} + {Qlt y x}.
Proof.
 intros x y Hxy; destruct (Q_le_lt_dec x y) as [H|H]; try tauto; 
 left; destruct (Qle_lt_eq_dec _ _ H) as [H'|H']; trivial; contradiction.
Qed.

Lemma Qlt_stepl:forall x y z, Qlt x y -> x=z -> Qlt z y.
Proof.
 intros x y z H_lt H_eq; subst; assumption.
Qed.

Lemma Qlt_stepr:forall x y z, Qlt x y -> y=z -> Qlt x z.
Proof.
 intros x y z H_lt H_eq; subst; assumption.
Qed.

Lemma Qle_stepl:forall x y z, Qle x y -> x=z -> Qle z y.
Proof.
 intros x y z H_lt H_eq; subst; assumption.
Qed.

Lemma Qle_stepr:forall x y z, Qle x y -> y=z -> Qle x z.
Proof.
 intros x y z H_lt H_eq; subst; assumption.
Qed.


Lemma Qneq_stepl:forall (x y z:Q), x<>y -> x=z -> z<>y.
Proof.
 intros x y z H_lt H_eq; subst; assumption.
Qed.

Lemma Qneq_stepr:forall (x y z:Q), x<>y -> y=z -> x<>z.
Proof.
 intros x y z H_lt H_eq; subst; assumption.
Qed.


Declare Left Step Qlt_stepl.
Declare Right Step Qlt_stepr.
Declare Left Step Qle_stepl.
Declare Right Step Qle_stepr.
Declare Left Step Qneq_stepl.
Declare Right Step Qneq_stepr.


(** Properties of Qsgn *)

Lemma Qsgn_1: forall x:Q,{(Qsgn x) = 0}+{(Qsgn x) = 1}+{(Qsgn x) = (-1)%Z}. 
Proof.
 intros [|x|x]; simpl; auto. 
Qed.

Lemma Qsgn_2 : forall x : Q, Qsgn x = 0%Z -> x = Zero.
Proof.
 intros [| x| x] Hx; trivial; inversion Hx.
Qed.

Lemma Qsgn_7 : forall x : Q, Qlt Zero x -> Qsgn x = 1%Z.
Proof.
 intros [| x| x] Hx; trivial; inversion Hx.
Qed.

Lemma Qsgn_8 : forall x : Q, Qlt x Zero -> Qsgn x = (-1)%Z.
Proof.
 intros [| x| x] Hx; trivial; inversion Hx.
Qed.

Lemma Qsgn_9 : forall x : Q, Qsgn x = 1%Z -> Qlt Zero x.
Proof.
 intros [| x| x] Hx; trivial; inversion Hx.
Qed.

Lemma Qsgn_10 : forall x : Q, Qsgn x = (-1)%Z -> Qlt x Zero.
Proof.
 intros [| x| x] Hx; trivial; inversion Hx.
Qed.

Lemma Qsgn_15 : forall x y : Q, Qsgn (Qmult x y) = (Qsgn x * Qsgn y)%Z.
Proof.
 intros [| x| x] [| y| y]; trivial. 
Qed.
 
Lemma Qsgn_25 : forall x : Q, Qsgn (Qopp x) = (- Qsgn x)%Z.
Proof.
 intros [| x| x]; trivial. 
Qed.

Lemma Qsgn_28 : forall x : Q, Qsgn (Qinv x) = Qsgn x.
Proof.
 intros [| x| x]; trivial. 
Qed.

Lemma Qsgn_29 : forall x : Z, Qsgn (Z_to_Q x) = Z.sgn x. 
Proof.
 intros [| x| x]; trivial. 
Qed.

Lemma Qsgn_30 : forall x y : Q, Qsgn (Qdiv x y) = (Qsgn x * Qsgn y)%Z.
Proof.
 intros [| x| x] [| y| y]; trivial. 
Qed.

Lemma Qsgn_31:forall x:Q, Qle x Zero-> Qsgn x <> 1.
Proof.
 intros [|x|x] Hx; try discriminate; apply False_ind; apply Hx; apply Qlt_zero_pos.
Qed.

Lemma Qsgn_32:forall x:Q, Qsgn x <> 1 -> Qle x  Zero.
Proof.
 intros [|x|x] Hx; auto; try apply Qle_reflexive; apply False_ind; apply Hx; reflexivity.
Qed.

Lemma Qsgn_33:forall x:Q, Qle Zero x -> Qsgn x <> (-1)%Z.
Proof.
 intros [|x|x] Hx; try discriminate; apply False_ind; apply Hx; auto.
Qed.

Lemma Qsgn_34:forall x:Q, Qsgn x <> (-1)%Z -> Qle Zero x.
Proof.
 intros [|x|x] Hx; auto; try apply Qle_reflexive; apply False_ind; apply Hx; reflexivity.
Qed.

Hint Resolve Qsgn_2 Qsgn_7 Qsgn_8 Qsgn_9 Qsgn_10 Qsgn_15 Qsgn_25 Qsgn_28
  Qsgn_29 Qsgn_30.

(* Not all of these properties are necessary at the moment. We Uncomment one any time we need it *)
(* Axiom Qsgn_3: (x:Q)~x=Zero->`(Qsgn x) <> 0`. *)
(* Axiom Qsgn_5: (a,b,x,y:Q)~x= Zero->~y=Zero->(Qmult (Qsgn a) x) = (Qmult (Qsgn b) y)->(Qmult (Qsgn a) y) =(Qmult (Qsgn b) x). *)
(* Axiom Qsgn_6: (x:Q)x = Zero->`(Qsgn x) = 0`. *)
(* Axiom Qsgn_11: (x:Q)`(Qsgn x) < 0`->(Qlt x Zero). *)
(* Axiom Qsgn_12: (x:Q)`0 < (Qsgn x)`->(Qlt Zero x). *)
(* Axiom Qsgn_13: (x:Q)`0 <= (Qsgn x)`->(Qle Zero  x). *)
(* Axiom Qsgn_14: (x:Q)`(Qsgn x) <= 0`->(Qle x Zero). *)
(* Axiom Qsgn_16:(x,y:Q)`(Qsgn (Qmult x y)) = 1`->{(Qlt Zero x)/\(Qlt Zero y)}+{(Qlt x Zero)/\(Qlt y Zero)}. *)
(* Axiom Qsgn_17: (x,y:Q)`(Qsgn (Qmult x y)) = (-1)`->{(Qlt Zero x)/\(Qlt y Zero)}+{(Qlt x Zero)/\(Qlt Zero y)}. *)
(* Axiom Qsgn_18: (x,y:Q)`(Qsgn (Qmult x y)) = 0`->{x = Zero}+{y = Zero}. *)
(* Axiom Qsgn_19: (x,y:Q)`0 < (Qsgn x)+(Qsgn y)`->(Qlt Zero (Qplus x y)). *)
(* Axiom Qsgn_20: (x,y:Q)`(Qsgn x)+(Qsgn y) < 0`->(Qlt (Qplus x y) Zero). *)
(* Axiom Qsgn_21: (x,y:Q)`0 < (Qsgn x)+(Qsgn y)`->(Qle Zero x). *)
(* Axiom Qsgn_22: (x,y:Q)`(Qsgn x)+(Qsgn y) < 0`->(Qle x Zero). *)
(* Axiom Qsgn_23: (x,y:Q)`0 < (Qsgn x)+(Qsgn y)`->(Qle Zero y). *)
(* Axiom Qsgn_24: (x,y:Q)`(Qsgn x)+(Qsgn y) < 0`->(Qle y Zero). *)
(* Axiom Qsgn_26: (x:Q)(Qlt Zero x)->`0 < (Qsgn x)`. *)
(* Axiom Qsgn_27: (x:Q)(Qlt x Zero)->`(Qsgn x) < 0`. *)

Ltac qnat_zero :=  replace (Z_to_Q (Z_of_nat 0)) with Zero;  trivial.
Ltac natq_zero :=  replace Zero with (Z_to_Q (Z_of_nat 0));  trivial.
Ltac qnat_one :=  replace (Z_to_Q (Z_of_nat (S 0))) with Qone;  trivial.
Ltac natq_one :=  replace Qone with (Z_to_Q (Z_of_nat (S 0)));  trivial.
Ltac qnat_S k :=  replace (Z_to_Q (Z_of_nat (S k))) with (Qplus k Qone); [idtac | rewrite Z_to_Q_S; trivial].
Ltac natq_S k :=  try qnat_one; replace (Qplus k Qone) with (Z_to_Q (Z_of_nat (S k))); [idtac | rewrite <- Z_to_Q_S; trivial].
Ltac qnat_S_rec k :=  
             try qnat_one; replace (Qplus k Qone) with (Z_to_Q (Z_of_nat (S k))); [idtac | rewrite <- Z_to_Q_S; trivial];
             try qnat_S_rec (k-1).

Ltac natZ_numerals  := 
 match goal with 
 | [ |- context [Z0] ] => replace Z0 with (Z_of_nat O); trivial; natZ_numerals
 | [ |- context [(Zpos ?X1)] ] => let v:= eval compute in (Z.abs_nat (Z.pred (Zpos X1))) in 
         replace (Zpos X1) with (Z_of_nat (S v)); trivial; natZ_numerals
 | [ |- context [(Zneg ?X1)] ] => let v:= eval compute in (Z.abs_nat (Z.succ (Zpos X1))) in 
         replace (Zneg X1) with (Z.opp (Z_of_nat (S v))); trivial; natZ_numerals
 | [ |- _ ] => idtac
 end.
