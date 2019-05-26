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


Require Import FunInd.
Require Import Field_Theory_Q. 
Require Export Qhomographic_Qpositive_to_Q_properties.

Definition spec_fraction_encoding (a b : Z) : Q := Qmult a (Qinv b).

Definition spec_positive_fraction_encoding (a b : Z) 
  (Ha : (0 < a)%Z) (Hb : (0 < b)%Z) :=
  Qpositive_mult (Z_to_Qpositive a Ha) (Qpositive_inv (Z_to_Qpositive b Hb)). 

Definition spec_positive_fraction_encoding1 (a b : Z) :=
  Q_tail (Qmult a (Qinv b)).

Definition spec_positive_fraction_encoding2 (a b : Z) :=
  Qpositive_mult (Q_tail a) (Qpositive_inv (Q_tail b)). 

Lemma spec_coding :
 forall m n : nat,
 Qpositive_c (S m) (S n) (S m + S n) =
 spec_positive_fraction_encoding1 (m + 1) (n + 1).
Proof.
 unfold spec_positive_fraction_encoding1 in |- *.
 unfold Qmult in |- *.
 intros m n.
 transitivity
  (Qpositive_mult (Qpositive_c (S m) 1 (S (S m)))
     (Qpositive_inv (Qpositive_c (S n) 1 (S (S n))))).
 (* 1.1 *)
 unfold Qpositive_mult in |- *.
 rewrite Qpositive_i_c; [ idtac | apply lt_O_Sn | apply le_n ].

 set (P := Qpositive_i (Qpositive_c (S n) 1 (S (S n)))) in *.
 set (p := fst P) in *.
 set (q := snd P) in *. 
 transitivity (Qpositive_c (S m * 1) (1 * S n) (S m * 1 + 1 * S n)).
  (* 1.1.1 *)
  repeat rewrite mult_1_l; repeat rewrite mult_1_r; reflexivity.
  (* 1.1.2 *)
  assert (P = (S n, 1)).
  unfold P in |- *.
  apply Qpositive_i_c; try apply lt_O_Sn.
  apply le_n.
  replace (Qpositive_i (Qpositive_inv (Qpositive_c (S n) 1 (S (S n))))) with
   (q, p).
  replace q with 1.
  replace p with (S n).
  reflexivity.
  change (S n = fst P) in |- *.
  rewrite H.
  reflexivity.
  change (1 = snd P) in |- *.
  rewrite H.
  reflexivity.
  symmetry  in |- *.
  apply inv_correct.
  transitivity P.
  reflexivity.
  unfold p, q in |- *.
  apply pair_1.
 (* 1.2 *)
 replace (m + 1)%Z with (Z.succ m); [ idtac | reflexivity ].
 rewrite <- Znat.inj_S.
 replace (n + 1)%Z with (Z.succ n); [ idtac | reflexivity ].
 rewrite <- Znat.inj_S.
 simpl in |- *.
 repeat rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
 reflexivity.
Defined.

Lemma spec_positive_fraction_encoding1_positive_fraction_encoding :
 forall (m n : Z) (Hm : (0 < m)%Z) (Hn : (0 < n)%Z),
 spec_positive_fraction_encoding m n Hm Hn =
 spec_positive_fraction_encoding1 m n.
Proof.
 intros;
  unfold spec_positive_fraction_encoding, spec_positive_fraction_encoding1
   in |- *; elim (inject_nat_S_inf m Hm); elim (inject_nat_S_inf n Hn);
  intros nn Hnn mm Hmm; generalize Hn Hm; rewrite Hnn; 
  rewrite Hmm; intros; unfold Qmult in |- *; simpl in |- *;
  repeat rewrite nat_of_P_o_P_of_succ_nat_eq_succ; 
  reflexivity.
Defined.

Lemma spec_positive_fraction_encoding1_positive_fraction_encoding2 :
 forall (m n : Z) (Hm : (0 < m)%Z) (Hn : (0 < n)%Z),
 spec_positive_fraction_encoding m n Hm Hn =
 spec_positive_fraction_encoding2 m n.
Proof.
 intros m n Hm Hn;
  unfold spec_positive_fraction_encoding2, spec_positive_fraction_encoding
   in |- *; apply f_equal2 with Qpositive Qpositive;
  try apply f_equal with Qpositive; destruct m as [| pm| pm];
  try discriminate Hm; destruct n as [| pn| pn]; try discriminate Hn;
  reflexivity.
Defined.



Lemma coding :
 forall (m n : Z) (Hm : (0 < m)%Z) (Hn : (0 < n)%Z),
 positive_fraction_encoding m n Hm Hn =
 spec_positive_fraction_encoding m n Hm Hn. 
Proof.
 intros m n Hm Hn.
 transitivity
  (Qpositive_c (S (pred_nat m Hm)) (S (pred_nat n Hn))
     (S (pred_nat m Hm) + S (pred_nat n Hn))).
 (* T1 *)
 unfold positive_fraction_encoding in |- *.
 generalize (Zminus2_wf m n Hm Hn); intro f.
 generalize Hm Hn; clear Hm Hn.
 pattern m, n, f in |- *.
 elim f using fractionalAcc_ind_dep; clear m n f; intros.
 (* 1 *)
 rewrite (encoding_algorithm_0 m n Hm Hn (fractionalacc0 m n e) e).
 generalize Hm Hn.
 rewrite e.
 intros.
 symmetry  in |- *.
 apply Qpositive_c_equal_One.
 apply f_equal with nat.
 apply pred_nat_equal.
 (* 2 *)
 generalize (Zlt_minus n m l0).
 intro Hmn.
 rewrite
  (encoding_algorithm_1 m n Hm Hn (fractionalacc1 m n l l0 f) l0 l Hmn f)
  .
 rewrite plus_Sn_m.
 rewrite Qpositive_c_dL.
 apply f_equal with Qpositive.
 rewrite minus_pred_nat with n m Hn Hm Hmn.
 rewrite
  Qpositive_c_equal with (p' := S (pred_nat m Hm) + S (pred_nat (n - m) Hmn));
  try auto with arith.
 rewrite (encoding_algorithm_equal m (n - m) l Hm Hmn Hmn f f).
 apply H.
 repeat rewrite absolu_pred_nat.
 replace (pred_nat m Hm) with (Z.abs_nat (m - 1)). 
 repeat rewrite <- absolu_plus; try abstract omega.
 apply le_absolu; try abstract omega.
 rewrite pred_nat_absolu; reflexivity.
 repeat rewrite absolu_pred_nat.
 apply lt_absolu; try abstract omega.
 (* 3 *)
 generalize (Zlt_minus m n l0).
 intro Hmn.
 rewrite
  (encoding_algorithm_2 m n Hm Hn (fractionalacc2 m n l l0 f) l0 Hmn l f)
  .
 rewrite plus_Sn_m.
 rewrite Qpositive_c_nR.
 apply f_equal with Qpositive.
 rewrite minus_pred_nat with m n Hm Hn Hmn.
 rewrite
  Qpositive_c_equal with (p' := S (pred_nat (m - n) Hmn) + S (pred_nat n Hn));
  try auto with arith.
 rewrite (encoding_algorithm_equal (m - n) n Hmn Hmn l Hn f f).
 apply H.
 repeat rewrite absolu_pred_nat.
 replace (pred_nat m Hm) with (Z.abs_nat (m - 1)). 
 repeat rewrite <- absolu_plus; try abstract omega.
 apply le_absolu; try abstract omega.
 rewrite pred_nat_absolu; reflexivity.
 repeat rewrite absolu_pred_nat.
 apply lt_absolu; try abstract omega.

 (* T2 *)
 rewrite spec_positive_fraction_encoding1_positive_fraction_encoding.
 transitivity
  (spec_positive_fraction_encoding1 (S (pred_nat m Hm)) (S (pred_nat n Hn))).
 (* T2.1 *)
 repeat rewrite Znat.inj_S.
 unfold Z.succ in |- *.
 apply spec_coding.
 (* T2.2 *)
 repeat rewrite <- pred_nat_unfolded.
 reflexivity.
Defined.




Functional Scheme Qmult_ind := Induction for Qmult Sort Prop.

Lemma coding_Q :
 forall (m n : Z) (Hdenom : n <> 0%Z),
 fraction_encoding m n Hdenom = spec_fraction_encoding m n. 
Proof.
 intros m n Hdenom; unfold spec_fraction_encoding in |- *.
(*  unfold fraction_encoding in |- *. *)
 functional induction (fraction_encoding m n Hdenom).
 (* 1 *)
 (* Here I should explicitly write the coercions, and still even after that the generated predicate is independent of m and n *)
 (* Functional Induction Qmult (Z_to_Q m) (Qinv (Z_to_Q n)). *)
 (* So I should add the following equalities *)
 set (x := Qinv n) in *.
 set (y := Z_to_Q m) in *.
 assert (x = Qinv n); trivial.
 assert (y = m); trivial.
 generalize H H0.
 clear  H H0 e .
 functional induction (Qmult y x); intros.
 (* Qneg 0: 1 *)
 apply False_ind.
 apply (Zorder.Zlt_not_eq _ _ z).
 rewrite <- Zsgn_15.
 apply Zsgn_6.
 rewrite Z_eq_mult; try reflexivity.
 apply eq_Z_to_Q.
 symmetry  in |- *; assumption.
 (* Qneg 0 : 2 *)
 apply False_ind.
 apply Hdenom.
 apply eq_Z_to_Q.
 apply Qinv_0.
 symmetry  in |- *; assumption.
 (* Qneg Qpos : 1 *)
 apply False_ind.
 apply (Zlt_asym _ _ z).
 rewrite <- Zsgn_15.
 apply Zsgn_26.
 assert (Hm : (0 < m)%Z);
  [ idtac | assert (Hn' : (0 < n)%Z); [ idtac | abstract auto with zarith ] ].
 apply Qpos_POS_1 with x'.
 symmetry  in |- *; assumption.
 apply pos_Z_to_Q.
 apply Qinv_1.
 rewrite <- H.
 abstract auto with *.
 (* Qneg Qneg : 1 *)
 apply f_equal with Qpositive. 
 rewrite coding. 
 unfold spec_positive_fraction_encoding in |- *.
 apply f_equal2 with Qpositive Qpositive.
 assert (Hm : (0 < m)%Z);
  [ apply Qpos_POS_1 with x'; symmetry  in |- *; assumption | idtac ].
 rewrite <- (Z_to_Qpositive_equal m (Z.abs m) Hm).
 apply Qpos_injective.
 rewrite <- Z_to_Qpositive_to_Q.
 symmetry  in |- *; assumption.
 symmetry  in |- *; apply Z.abs_eq; apply Zlt_le_weak; assumption.
 apply Qneg_injective.
 rewrite H.
 change (Qinv (Qneg (Z_to_Qpositive (Z.abs n) (Zabs_11 n Hdenom))) = Qinv n)
  in |- *.
 apply f_equal with Q.
 assert (Hn' : (n < 0)%Z);
  [ apply neg_Z_to_Q; apply Qinv_2; rewrite <- H; apply Qlt_neg_zero
  | idtac ]. 
 destruct n as [| pn| pn]; try discriminate Hn'.
 unfold Z_to_Q in |- *.
 apply f_equal with Qpositive.
 reflexivity.
 (* Qneg 0 : 3 *)
 apply False_ind.
 apply Hdenom.
 apply eq_Z_to_Q.
 apply Qinv_0.
 symmetry  in |- *; assumption.
 (* Qneg Qneg : 2 *)
 apply f_equal with Qpositive. 
 rewrite coding. 
 unfold spec_positive_fraction_encoding in |- *.
 apply f_equal2 with Qpositive Qpositive.
 apply Qneg_injective.
 assert (Hm : (m < 0)%Z);
  [ apply neg_Z_to_Q; rewrite <- H0; apply Qlt_neg_zero | idtac ].
 destruct m as [| pm| pm]; try discriminate Hm.
 rewrite H0.
 unfold Z_to_Q in |- *.
 apply f_equal with Qpositive.
 reflexivity.

 apply Qpos_injective.
 rewrite H.
 change (Qinv (Qpos (Z_to_Qpositive (Z.abs n) (Zabs_11 n Hdenom))) = Qinv n)
  in |- *.
 apply f_equal with Q.
 rewrite <- Z_to_Qpositive_to_Q.
 rewrite Z.abs_eq; try reflexivity.
 apply Zlt_le_weak.
 apply pos_Z_to_Q.
 apply Qinv_1.
 rewrite <- H.
 apply Qlt_zero_pos.
 (* Qneg Qpos : 2 *)
 apply False_ind.
 apply (Zlt_asym _ _ z).
 rewrite <- Zsgn_15.
 apply Zsgn_26.
 assert (Hm : (m < 0)%Z);
  [ idtac | assert (Hn' : (n < 0)%Z); [ idtac | abstract auto with zarith ] ].
 apply Qneg_NEG_1 with x'.
 symmetry  in |- *; assumption.
 apply neg_Z_to_Q.
 apply Qinv_2.
 rewrite <- H.
 apply Qlt_neg_zero.

 (* 2 *)
 set (x := Qinv n) in *.
 set (y := Z_to_Q m) in *.
 assert (x = Qinv n); trivial.
 assert (y = m); trivial.
 generalize H H0.
 clear e H H0.
 functional induction (Qmult y x); intros.
 (* Qpos 0: 1 *)
 apply False_ind.
 generalize (Z.gt_lt _ _ z); clear z; intro z.
 apply (Zorder.Zlt_not_eq _ _ z).
 symmetry  in |- *.
 rewrite <- Zsgn_15.
 apply Zsgn_6.
 rewrite Z_eq_mult; try reflexivity.
 apply eq_Z_to_Q.
 symmetry  in |- *; assumption.
 (* Qpos 0 : 2 *) (* C *)
 apply False_ind.
 apply Hdenom.
 apply eq_Z_to_Q.
 apply Qinv_0.
 symmetry  in |- *; assumption.
 (* Qpos Qpos : 1 *)
 apply f_equal with Qpositive. 
 rewrite coding. 
 unfold spec_positive_fraction_encoding in |- *.
 apply f_equal2 with Qpositive Qpositive.
 assert (Hm : (0 < m)%Z);
  [ apply Qpos_POS_1 with x'; symmetry  in |- *; assumption | idtac ].
 rewrite <- (Z_to_Qpositive_equal m (Z.abs m) Hm).
 apply Qpos_injective.
 rewrite <- Z_to_Qpositive_to_Q.
 symmetry  in |- *; assumption.
 symmetry  in |- *; apply Z.abs_eq; apply Zlt_le_weak; assumption.
 apply Qpos_injective.
 rewrite H.
 change (Qinv (Qpos (Z_to_Qpositive (Z.abs n) (Zabs_11 n Hdenom))) = Qinv n)
  in |- *.
 apply f_equal with Q.
 rewrite <- Z_to_Qpositive_to_Q.
 rewrite Z.abs_eq; try reflexivity.
 apply Zlt_le_weak.
 apply pos_Z_to_Q.
 apply Qinv_1.
 rewrite <- H.
 apply Qlt_zero_pos.
 (* Qpos Qneg : 1 *)
 apply False_ind.
 generalize (Z.gt_lt _ _ z); clear z; intro z.
 apply (Zlt_asym _ _ z).
 rewrite <- Zsgn_15.
 apply Zsgn_27.
 assert (Hm : (0 < m)%Z);
  [ idtac
  | assert (Hn' : (n < 0)%Z); [ idtac | try abstract auto with zarith ] ].
 apply Qpos_POS_1 with x'.
 symmetry  in |- *; assumption.
 apply neg_Z_to_Q.
 apply Qinv_2.
 rewrite <- H.
 abstract auto with *.
 (* Qpos 0 : 3 *)  (* C *)
 apply False_ind.
 apply Hdenom.
 apply eq_Z_to_Q.
 apply Qinv_0.
 symmetry  in |- *; assumption.
 (* Qpos Qneg : 2 *)
 apply False_ind.
 generalize (Z.gt_lt _ _ z); clear z; intro z.
 apply (Zlt_asym _ _ z).
 rewrite <- Zsgn_15.
 apply Zsgn_27.
 assert (Hm : (m < 0)%Z);
  [ idtac | assert (Hn' : (0 < n)%Z); [ idtac | abstract auto with zarith ] ].
 apply Qneg_NEG_1 with x'.
 symmetry  in |- *; assumption.
 apply pos_Z_to_Q.
 apply Qinv_1.
 rewrite <- H.
 apply Qlt_zero_pos.
 (* Qpos Qpos : 2 *)
 apply f_equal with Qpositive. 
 rewrite coding. 
 unfold spec_positive_fraction_encoding in |- *.
 apply f_equal2 with Qpositive Qpositive.
 apply Qneg_injective.
 assert (Hm : (m < 0)%Z);
  [ apply neg_Z_to_Q; rewrite <- H0; apply Qlt_neg_zero | idtac ].
 destruct m as [| pm| pm]; try discriminate Hm.
 rewrite H0.
 unfold Z_to_Q in |- *.
 apply f_equal with Qpositive.
 reflexivity.

 apply Qneg_injective.
 rewrite H.
 change (Qinv (Qneg (Z_to_Qpositive (Z.abs n) (Zabs_11 n Hdenom))) = Qinv n)
  in |- *.
 apply f_equal with Q.
 assert (Hn' : (n < 0)%Z);
  [ apply neg_Z_to_Q; apply Qinv_2; rewrite <- H; apply Qlt_neg_zero
  | idtac ]. 
 destruct n as [| pn| pn]; try discriminate Hn'.
 unfold Z_to_Q in |- *.
 apply f_equal with Qpositive.
 reflexivity.
 (* 3 *)
 replace m with 0%Z.
 reflexivity.
 symmetry  in |- *; apply Zmult_integral_l with n;
  [ idtac | apply Zsgn_2; rewrite Zsgn_15 ]; assumption.
Defined.


Definition spec_h (a b c d : Z) (q : Q) : Q :=
  Qmult (Qplus (Qmult a q) b) (Qinv (Qplus (Qmult c q) d)).



Definition spec_Qhomographic_Qpositive_to_Q (a b c d : Z) 
  (p : Qpositive) : Q :=
  Qmult (Qplus (Qmult a (Qpos p)) b) (Qinv (Qplus (Qmult c (Qpos p)) d)).

Definition spec_ni (a b c d : Z) (p : Qpositive) : Qpositive :=
  Q_tail
    (Qmult (Qplus (Qmult a (Qpos p)) b) (Qinv (Qplus (Qmult c (Qpos p)) d))).

(* Here we should expect that a*p+b > 0 and c*p+d > 0, this follow from homographicAcc *)
Definition spec_ni2 (a b c d : Z) (p : Qpositive) : Qpositive :=
  Qpositive_mult (Q_tail (Qplus (Qmult a (Qpos p)) b))
    (Qpositive_inv (Q_tail (Qplus (Qmult c (Qpos p)) d))).

Lemma spec_Qhomographic_Qpositive_to_Q_nR :
 forall (a b c d : Z) (q : Qpositive),
 spec_Qhomographic_Qpositive_to_Q a b c d (nR q) =
 spec_Qhomographic_Qpositive_to_Q a (a + b) c (c + d) q.
Proof.
 intros.
 unfold spec_Qhomographic_Qpositive_to_Q in |- *.
 do 2 rewrite Qmult_Z_nR.
 repeat rewrite <- Qplus_assoc. 
 repeat rewrite <- Z_to_Qplus.
 reflexivity.
Defined.


Lemma spec_Qhomographic_Qpositive_to_Q_dL :
 forall (a b c d : Z) (q : Qpositive),
 spec_Qhomographic_Qpositive_to_Q a b c d (dL q) =
 spec_Qhomographic_Qpositive_to_Q (a + b) b (c + d) d q.
Proof.
 intros.
 unfold spec_Qhomographic_Qpositive_to_Q in |- *.
 do 2 rewrite Qmult_Z_plus_Z_dL.
 set (p := Qpos q) in *.
 set (A := Z_to_Q (a + b)) in *.
 set (C := Z_to_Q (c + d)) in *. 
 rewrite <- Qdiv_num_denom.
 reflexivity.
 (* Here Abstract Discriminate doesn't work , even if we unfold p *)
 discriminate.
Defined.

Lemma spec_Qhomographic_Qpositive_to_Q_nR_unfolded :
 forall (a b c d : Z) (q : Qpositive),
 Qmult (Qplus (Qmult a (Qpos (nR q))) b)
   (Qinv (Qplus (Qmult c (Qpos (nR q))) d)) =
 Qmult (Qplus (Qmult a (Qpos q)) (a + b)%Z)
   (Qinv (Qplus (Qmult c (Qpos q)) (c + d)%Z)).
Proof spec_Qhomographic_Qpositive_to_Q_nR.

Lemma spec_Qhomographic_Qpositive_to_Q_dL_unfolded :
 forall (a b c d : Z) (q : Qpositive),
 Qmult (Qplus (Qmult a (Qpos (dL q))) b)
   (Qinv (Qplus (Qmult c (Qpos (dL q))) d)) =
 Qmult (Qplus (Qmult (a + b)%Z (Qpos q)) b)
   (Qinv (Qplus (Qmult (c + d)%Z (Qpos q)) d)).
Proof spec_Qhomographic_Qpositive_to_Q_dL.




Lemma spec_ni2_nR :
 forall (a b c d : Z) (q : Qpositive),
 spec_ni2 a b c d (nR q) = spec_ni2 a (a + b) c (c + d) q.
Proof.
 intros.
 unfold spec_ni2 in |- *.
 do 2 rewrite Qmult_Z_nR.
 repeat rewrite <- Qplus_assoc. 
 repeat rewrite <- Z_to_Qplus.
 reflexivity.
Defined.

Lemma spec_ni2_dL :
 forall (a b c d : Z) (q : Qpositive),
 Qplus (Qmult (a + b)%Z (Qpos q)) b <> Zero ->
 Qplus (Qmult (c + d)%Z (Qpos q)) d <> Zero ->
 spec_ni2 a b c d (dL q) = spec_ni2 (a + b) b (c + d) d q.
Proof.
 intros a b c d p Hnum Hdenom.
 unfold spec_ni2 in |- *.
 do 2 rewrite Qmult_Z_plus_Z_dL.
 repeat rewrite <- Q_tail_Qinv.
 repeat rewrite <- Q_tail_Qmult; try assumption.
 apply f_equal with Q.
 rewrite <- Qdiv_num_denom; [ reflexivity | discriminate ].
 apply Qinv_resp_nonzero; assumption.
 apply Qmult_resp_nonzero; [ assumption | discriminate ].
 apply Qinv_resp_nonzero; apply Qmult_resp_nonzero;
  [ assumption | discriminate ].
Defined.

Lemma spec_ni2_nR_emission :
 forall (a b c d : Z) (q : Qpositive),
 Qlt Zero (Qplus (Qmult a (Qpos q)) b) ->
 Qlt Zero (Qplus (Qmult c (Qpos q)) d) ->
 Qlt Zero (Qplus (Qmult (a - c)%Z (Qpos q)) (b - d)%Z) ->
 nR (spec_ni2 (a - c) (b - d) c d q) = spec_ni2 a b c d q.
Proof.
 intros a b c d q Hab Hcd Habcd;
  generalize (Qlt_not_eq _ _ Hab) (Qlt_not_eq _ _ Hcd) (Qlt_not_eq _ _ Habcd);
  intros Hab' Hcd' Habcd'.
 rewrite what_nR_does.
 unfold spec_ni2 in |- *.
 rewrite <- Q_tail_Qinv.
 repeat rewrite <- Q_tail_Qmult;
  match goal with
  |  |- (Qinv _ <> _) => apply Qinv_resp_nonzero
  |  |- _ => idtac
  end; try assumption.
 replace One with (Q_tail Qone); trivial.
 rewrite <- Q_tail_Qplus_pos.
 apply f_equal with Q.
 repeat rewrite Z_to_Qminus. 
 abstract (field; assumption).
 apply Qlt_mult_pos_pos; try apply Qinv_pos; assumption.
 apply Qlt_zero_one.
Defined.


Lemma spec_ni2_dL_emission :
 forall (a b c d : Z) (q : Qpositive),
 Qlt Zero (Qplus (Qmult a (Qpos q)) b) ->
 Qlt Zero (Qplus (Qmult c (Qpos q)) d) ->
 Qlt Zero (Qplus (Qmult (c - a)%Z (Qpos q)) (d - b)%Z) ->
 dL (spec_ni2 a b (c - a) (d - b) q) = spec_ni2 a b c d q.
Proof.
 intros a b c d q Hab Hcd Habcd;
  generalize (Qlt_not_eq _ _ Hab) (Qlt_not_eq _ _ Hcd) (Qlt_not_eq _ _ Habcd);
  intros Hab' Hcd' Habcd'.
 rewrite what_dL_does.
 unfold spec_ni2 in |- *.
 repeat rewrite <- Q_tail_Qinv.
 repeat rewrite <- Q_tail_Qmult;
  match goal with
  |  |- (Qinv _ <> _) => apply Qinv_resp_nonzero
  |  |- _ => idtac
  end; try assumption.
 replace One with (Q_tail Qone); trivial.
 rewrite <- Q_tail_Qplus_pos.
 rewrite <- Q_tail_Qinv.
 repeat rewrite <- Q_tail_Qmult;
  repeat
   match goal with
   |  |- (Qinv _ <> _) => apply Qinv_resp_nonzero
   |  |- (Qmult _ _ <> _) => apply Qmult_resp_nonzero
   end; try assumption.
 apply f_equal with Q.
 repeat rewrite Z_to_Qminus.
Opaque Qmult Qplus Qinv Qone.
 field.
 repeat
  match goal with
  |  |- (Qinv _ <> _) => apply Qinv_resp_nonzero
  |  |- (Qmult _ _ <> _) => apply Qmult_resp_nonzero
  |  |- (Qplus _ _ <> _) => do 2 rewrite Z_to_Qminus in Habcd'; assumption
  end; try assumption.
 split.
  apply Qlt_not_eq; trivial.
  do 2 rewrite Z_to_Qminus in Habcd'; assumption.
apply Qlt_not_eq; apply Qlt_plus_pos_pos.
apply Qlt_mult_pos_pos; try assumption.
apply Qinv_pos; assumption.
apply Qlt_zero_one.
apply Qlt_mult_pos_pos; try apply Qinv_pos; assumption.
apply Qlt_zero_one.
Defined.

Lemma homographic_sign :
 forall (a b c d : Z) (p : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
 h_sign a b c d p H_Qhomographic_sg_denom_nonzero =
 Qsgn (spec_Qhomographic_Qpositive_to_Q a b c d p).
Proof.
 intros a b c d p H_Qhomographic_sg_denom_nonzero.
 unfold h_sign in |- *.
 functional induction
  (Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero).
 (* (nR1) : b=0 & d=0  *)
 unfold spec_Qhomographic_Qpositive_to_Q in |- *.
 simpl in |- *.
 transitivity
  (Qsgn (Qmult (Qmult a (Qpos (nR q))) (Qinv (Qmult c (Qpos (nR q)))))).
 repeat rewrite Qsgn_15.
 rewrite Qsgn_28.
 rewrite Qsgn_15.
 simpl in |- *.
 repeat rewrite Qsgn_29.
 abstract ring.
 apply f_equal with Q.
 field.
 split.
  discriminate.
  intro;
  generalize
   (Qhomographic_sg_denom_nonzero_nonzero_3 c 0 (nR q)
      H_Qhomographic_sg_denom_nonzero); intros [H_| H_]; 
  apply H_; clear H_; [ apply eq_Z_to_Q; assumption | reflexivity].
 (* (nR2) : b=0 & d<>0 & 0<o2  *)
 unfold spec_Qhomographic_Qpositive_to_Q in |- *.
  clear e2 e0 e1; simpl in |- *.
 transitivity
  (Qsgn
     (Qmult (Qmult a (Qpos (nR q))) (Qinv (Qplus (Qmult c (Qpos (nR q))) d)))).
 repeat rewrite Qsgn_15.  
 rewrite Qsgn_28.
 simpl in |- *.
 generalize (Zsgn_21 _ _ _x1) (Zsgn_23 _ _ _x1) (Zsgn_19 _ _ _x1);
  intros Hc_nonneg Hd_nonneg Hcd_pos.
 replace (Qsgn (Qplus (Qmult c (Qpos (nR q))) d)) with 1%Z.
 rewrite Qsgn_29.
 abstract auto with zarith.
 symmetry  in |- *.
 apply Qsgn_7.
 generalize (Zlt_cotrans_pos _ _ Hcd_pos); intros [Hc| Hd];
  [ apply Qlt_le_reg_pos;
     [ apply Qsgn_9; rewrite Qsgn_15; simpl in |- *; rewrite Qsgn_29;
        rewrite Zmult_1_r; abstract auto with zarith
     | apply Z_to_Q_nonneg; assumption ]
  | apply Qle_lt_reg_pos;
     [ apply Qle_mult_nonneg_nonneg;
        [ apply Z_to_Q_nonneg; assumption | auto with * ]
     | apply Z_to_Q_pos; assumption ] ].
 
 apply f_equal with Q.
 apply f_equal2 with Q Q; [ field | reflexivity ].   

 (* (nR3) : b=0 & d<>0 & ~0<o2 & o2<0  *)
 unfold spec_Qhomographic_Qpositive_to_Q in |- *;
  clear e3 e0 e1 e2; 
  simpl in |- *.
 transitivity
  (Qsgn
     (Qmult (Qmult a (Qpos (nR q))) (Qinv (Qplus (Qmult c (Qpos (nR q))) d)))).
 repeat rewrite Qsgn_15.  
 rewrite Qsgn_28.
 simpl in |- *.
 generalize (Zsgn_22 _ _ _x2) (Zsgn_24 _ _ _x2) (Zsgn_20 _ _ _x2);
  intros Hc_nonpos Hd_nonpos Hcd_neg.
 replace (Qsgn (Qplus (Qmult c (Qpos (nR q))) d)) with (-1)%Z.
 rewrite Qsgn_29.
 abstract auto with zarith.
 symmetry  in |- *.
 apply Qsgn_8.
 generalize (Zlt_cotrans_neg _ _ Hcd_neg); intros [Hc| Hd];
  [ apply Qlt_le_reg_neg;
     [ apply Qsgn_10; rewrite Qsgn_15; simpl in |- *; rewrite Qsgn_29;
        rewrite Zmult_1_r; abstract auto with zarith
     | apply Z_to_Q_nonpos; assumption ]
  | apply Qle_lt_reg_neg;
     [ apply Qle_mult_nonpos_pos;
        [ apply Z_to_Q_nonpos; assumption | auto with * ]
     | apply Z_to_Q_neg; assumption ] ].
 
 apply f_equal with Q.
 apply f_equal2 with Q Q; [ field | reflexivity ].   
 (* (nR4) : b=0 & d<>0 & ~0<o2 & ~o2<0  *)
 clear e3 e0 e1 e2;
  rewrite spec_Qhomographic_Qpositive_to_Q_nR; rewrite IHp0; 
  reflexivity.
 (* (nR5) : b<>0 & d=0 & 0<o1  *)
 unfold spec_Qhomographic_Qpositive_to_Q in |- *;
  clear e2 e0 e1.
 simpl in |- *.
 transitivity
  (Qsgn
     (Qmult (Qplus (Qmult a (Qpos (nR q))) b) (Qinv (Qmult c (Qpos (nR q)))))).
 repeat rewrite Qsgn_15.  
 rewrite Qsgn_28.
 rewrite Qsgn_15.
 simpl in |- *.
 generalize (Zsgn_21 _ _ _x1) (Zsgn_23 _ _ _x1) (Zsgn_19 _ _ _x1);
  intros Ha_nonneg Hb_nonneg Hab_pos.
 replace (Qsgn (Qplus (Qmult a (Qpos (nR q))) b)) with 1%Z.
 rewrite Qsgn_29.
 abstract auto with zarith.
 symmetry  in |- *.
 apply Qsgn_7.
 generalize (Zlt_cotrans_pos _ _ Hab_pos); intros [Ha_| Hb_];
  [ apply Qlt_le_reg_pos;
     [ apply Qsgn_9; rewrite Qsgn_15; simpl in |- *; rewrite Qsgn_29;
        rewrite Zmult_1_r; abstract auto with zarith
     | apply Z_to_Q_nonneg; assumption ]
  | apply Qle_lt_reg_pos;
     [ apply Qle_mult_nonneg_nonneg;
        [ apply Z_to_Q_nonneg; assumption | auto with * ]
     | apply Z_to_Q_pos; assumption ] ].
 
 apply f_equal with Q.
 apply f_equal2 with Q Q;
  [ reflexivity | apply f_equal with Q; abstract ring ].

 (* (nR6) : b<>0 & d=0 & ~0<o1 & o1<0  *)
 unfold spec_Qhomographic_Qpositive_to_Q in |- *;
  clear e3 e0 e1 e2;
  simpl in |- *.
 transitivity
  (Qsgn
     (Qmult (Qplus (Qmult a (Qpos (nR q))) b) (Qinv (Qmult c (Qpos (nR q)))))).
 repeat rewrite Qsgn_15.  
 rewrite Qsgn_28.
 rewrite Qsgn_15.
 simpl in |- *.
 generalize (Zsgn_22 _ _ _x2) (Zsgn_24 _ _ _x2) (Zsgn_20 _ _ _x2);
  intros Ha_nonpos Hb_nonpos Hab_neg.
 replace (Qsgn (Qplus (Qmult a (Qpos (nR q))) b)) with (-1)%Z.
 rewrite Qsgn_29.
 abstract auto with zarith.
 symmetry  in |- *.
 apply Qsgn_8.
 generalize (Zlt_cotrans_neg _ _ Hab_neg); intros [Ha_| Hb_];
  [ apply Qlt_le_reg_neg;
     [ apply Qsgn_10; rewrite Qsgn_15; simpl in |- *; rewrite Qsgn_29;
        rewrite Zmult_1_r; abstract auto with zarith
     | apply Z_to_Q_nonpos; assumption ]
  | apply Qle_lt_reg_neg;
     [ apply Qle_mult_nonpos_pos;
        [ apply Z_to_Q_nonpos; assumption | auto with * ]
     | apply Z_to_Q_neg; assumption ] ].
 
 apply f_equal with Q.
 apply f_equal2 with Q Q;
  [ reflexivity | apply f_equal with Q; abstract ring ].   
 (* (nR7) : b<>0 & d=0 & ~0<o1 & ~o1<0  *)
 clear e3 e0 e1 e2 ;
  rewrite spec_Qhomographic_Qpositive_to_Q_nR; rewrite IHp0; 
  reflexivity.
 (* (nR8) : b<>0 & d<>0 & (i1 o1 o2) *)
 unfold spec_Qhomographic_Qpositive_to_Q in |- *;
  clear e2 e0 e1  .
 repeat rewrite Qsgn_15.  
 rewrite Qsgn_28.
 case (inside_interval_1_inf _ _ _x1); clear _x1;
  intros (Hab, Hcd);
  repeat
   match goal with
   | id1:(0 < outside_interval _ _)%Z |- _ =>
       generalize (Zsgn_21 _ _ id1) (Zsgn_23 _ _ id1) (Zsgn_19 _ _ id1);
        clear id1
   | id1:(outside_interval _ _ < 0)%Z |- _ =>
       generalize (Zsgn_22 _ _ id1) (Zsgn_24 _ _ id1) (Zsgn_20 _ _ id1);
        clear id1
   end; intros Ha_ Hb_ Hab_ Hc_ Hd_ Hcd_.
 replace (Qsgn (Qplus (Qmult a (Qpos (nR q))) b)) with 1%Z.
 replace (Qsgn (Qplus (Qmult c (Qpos (nR q))) d)) with 1%Z.
 abstract auto with zarith.
 symmetry  in |- *; apply Qsgn_7; generalize (Zlt_cotrans_pos _ _ Hcd_);
  intros [Hc_1| Hd_1];
  [ apply Qlt_le_reg_pos;
     [ apply Qsgn_9; rewrite Qsgn_15; simpl in |- *; rewrite Qsgn_29;
        rewrite Zmult_1_r; abstract auto with zarith
     | apply Z_to_Q_nonneg; assumption ]
  | apply Qle_lt_reg_pos;
     [ apply Qle_mult_nonneg_nonneg;
        [ apply Z_to_Q_nonneg; assumption | auto with * ]
     | apply Z_to_Q_pos; assumption ] ].
 symmetry  in |- *; apply Qsgn_7; generalize (Zlt_cotrans_pos _ _ Hab_);
  intros [Ha_1| Hb_1];
  [ apply Qlt_le_reg_pos;
     [ apply Qsgn_9; rewrite Qsgn_15; simpl in |- *; rewrite Qsgn_29;
        rewrite Zmult_1_r; abstract auto with zarith
     | apply Z_to_Q_nonneg; assumption ]
  | apply Qle_lt_reg_pos;
     [ apply Qle_mult_nonneg_nonneg;
        [ apply Z_to_Q_nonneg; assumption | auto with * ]
     | apply Z_to_Q_pos; assumption ] ].
 replace (Qsgn (Qplus (Qmult a (Qpos (nR q))) b)) with (-1)%Z.
 replace (Qsgn (Qplus (Qmult c (Qpos (nR q))) d)) with (-1)%Z.
 abstract auto with zarith.
 symmetry  in |- *; apply Qsgn_8; generalize (Zlt_cotrans_neg _ _ Hcd_);
  intros [Hc_1| Hd_1];
  [ apply Qlt_le_reg_neg;
     [ apply Qsgn_10; rewrite Qsgn_15; simpl in |- *; rewrite Qsgn_29;
        rewrite Zmult_1_r; abstract auto with zarith
     | apply Z_to_Q_nonpos; assumption ]
  | apply Qle_lt_reg_neg;
     [ apply Qle_mult_nonpos_pos;
        [ apply Z_to_Q_nonpos; assumption | auto with * ]
     | apply Z_to_Q_neg; assumption ] ].
 symmetry  in |- *; apply Qsgn_8; generalize (Zlt_cotrans_neg _ _ Hab_);
  intros [Ha_1| Hb_1];
  [ apply Qlt_le_reg_neg;
     [ apply Qsgn_10; rewrite Qsgn_15; simpl in |- *; rewrite Qsgn_29;
        rewrite Zmult_1_r; abstract auto with zarith
     | apply Z_to_Q_nonpos; assumption ]
  | apply Qle_lt_reg_neg;
     [ apply Qle_mult_nonpos_pos;
        [ apply Z_to_Q_nonpos; assumption | auto with * ]
     | apply Z_to_Q_neg; assumption ] ].
 (* (nR9) : b<>0 & d<>0 & ~(i1 o1 o2) & (i2 o1 o2)*)
 unfold spec_Qhomographic_Qpositive_to_Q in |- *;
  clear e3 e0 e1 e2  _x1.
 repeat rewrite Qsgn_15.  
 rewrite Qsgn_28.
 case (inside_interval_2_inf _ _ _x2); clear _x2;
  intros (Hab, Hcd);
  repeat
   match goal with
   | id1:(0 < outside_interval _ _)%Z |- _ =>
       generalize (Zsgn_21 _ _ id1) (Zsgn_23 _ _ id1) (Zsgn_19 _ _ id1);
        clear id1
   | id1:(outside_interval _ _ < 0)%Z |- _ =>
       generalize (Zsgn_22 _ _ id1) (Zsgn_24 _ _ id1) (Zsgn_20 _ _ id1);
        clear id1
   end.
 intros Hc_ Hd_ Hcd_ Ha_ Hb_ Hab_.
 replace (Qsgn (Qplus (Qmult a (Qpos (nR q))) b)) with 1%Z.
 replace (Qsgn (Qplus (Qmult c (Qpos (nR q))) d)) with (-1)%Z.
 abstract auto with zarith.
 symmetry  in |- *; apply Qsgn_8; generalize (Zlt_cotrans_neg _ _ Hcd_);
  intros [Hc_1| Hd_1];
  [ apply Qlt_le_reg_neg;
     [ apply Qsgn_10; rewrite Qsgn_15; simpl in |- *; rewrite Qsgn_29;
        rewrite Zmult_1_r; abstract auto with zarith
     | apply Z_to_Q_nonpos; assumption ]
  | apply Qle_lt_reg_neg;
     [ apply Qle_mult_nonpos_pos;
        [ apply Z_to_Q_nonpos; assumption | auto with * ]
     | apply Z_to_Q_neg; assumption ] ].
 symmetry  in |- *; apply Qsgn_7; generalize (Zlt_cotrans_pos _ _ Hab_);
  intros [Ha_1| Hb_1];
  [ apply Qlt_le_reg_pos;
     [ apply Qsgn_9; rewrite Qsgn_15; simpl in |- *; rewrite Qsgn_29;
        rewrite Zmult_1_r; abstract auto with zarith
     | apply Z_to_Q_nonneg; assumption ]
  | apply Qle_lt_reg_pos;
     [ apply Qle_mult_nonneg_nonneg;
        [ apply Z_to_Q_nonneg; assumption | auto with * ]
     | apply Z_to_Q_pos; assumption ] ].
 intros Ha_ Hb_ Hab_ Hc_ Hd_ Hcd_. 
 replace (Qsgn (Qplus (Qmult a (Qpos (nR q))) b)) with (-1)%Z.
 replace (Qsgn (Qplus (Qmult c (Qpos (nR q))) d)) with 1%Z.
 abstract auto with zarith.
 symmetry  in |- *; apply Qsgn_7; generalize (Zlt_cotrans_pos _ _ Hcd_);
  intros [Hc_1| Hd_1];
  [ apply Qlt_le_reg_pos;
     [ apply Qsgn_9; rewrite Qsgn_15; simpl in |- *; rewrite Qsgn_29;
        rewrite Zmult_1_r; abstract auto with zarith
     | apply Z_to_Q_nonneg; assumption ]
  | apply Qle_lt_reg_pos;
     [ apply Qle_mult_nonneg_nonneg;
        [ apply Z_to_Q_nonneg; assumption | auto with * ]
     | apply Z_to_Q_pos; assumption ] ].
 symmetry  in |- *; apply Qsgn_8; generalize (Zlt_cotrans_neg _ _ Hab_);
  intros [Ha_1| Hb_1];
  [ apply Qlt_le_reg_neg;
     [ apply Qsgn_10; rewrite Qsgn_15; simpl in |- *; rewrite Qsgn_29;
        rewrite Zmult_1_r; abstract auto with zarith
     | apply Z_to_Q_nonpos; assumption ]
  | apply Qle_lt_reg_neg;
     [ apply Qle_mult_nonpos_pos;
        [ apply Z_to_Q_nonpos; assumption | auto with * ]
     | apply Z_to_Q_neg; assumption ] ].
 (* (nR10) : b<>0 & d<>0 & ~(i1 o1 o2) & ~(i2 o1 o2)*)
 clear e3 e0 e1 e2;
  rewrite spec_Qhomographic_Qpositive_to_Q_nR; rewrite IHp0; 
  reflexivity.
 (* Now we just copy-paste the above 10 cases and change nR to dL, the only different cases are recursive calls in which we use
    spec_Qhomographic_Qpositive_to_Q_dL instead of spec_Qhomographic_Qpositive_to_Q_nR  (cases nR4,nR7,nR10 above) *)
 (* (dL1) : b=0 & d=0  *)
 unfold spec_Qhomographic_Qpositive_to_Q in |- *; clear e1 e0.
 simpl in |- *.
 transitivity
  (Qsgn (Qmult (Qmult a (Qpos (dL q))) (Qinv (Qmult c (Qpos (dL q)))))).
 repeat rewrite Qsgn_15.
 rewrite Qsgn_28.
 rewrite Qsgn_15.
 simpl in |- *.
 repeat rewrite Qsgn_29.
 abstract ring.
 apply f_equal with Q.
 field.
 split.
  discriminate. 
  intro;
  generalize
   (Qhomographic_sg_denom_nonzero_nonzero_3 c 0 (dL q)
      H_Qhomographic_sg_denom_nonzero); intros [H_| H_]; 
  apply H_; clear H_; [ apply eq_Z_to_Q; assumption | reflexivity].
 (* (dL2) : b=0 & d<>0 & 0<o2  *)
 unfold spec_Qhomographic_Qpositive_to_Q in |- *.
  clear e2 e0 e1; simpl in |- *.
 transitivity
  (Qsgn
     (Qmult (Qmult a (Qpos (dL q))) (Qinv (Qplus (Qmult c (Qpos (dL q))) d)))).
 repeat rewrite Qsgn_15.  
 rewrite Qsgn_28.
 simpl in |- *.
 generalize (Zsgn_21 _ _ _x1) (Zsgn_23 _ _ _x1) (Zsgn_19 _ _ _x1);
  intros Hc_nonneg Hd_nonneg Hcd_pos.
 replace (Qsgn (Qplus (Qmult c (Qpos (dL q))) d)) with 1%Z.
 rewrite Qsgn_29.
 abstract auto with zarith.
 symmetry  in |- *.
 apply Qsgn_7.
 generalize (Zlt_cotrans_pos _ _ Hcd_pos); intros [Hc| Hd];
  [ apply Qlt_le_reg_pos;
     [ apply Qsgn_9; rewrite Qsgn_15; simpl in |- *; rewrite Qsgn_29;
        rewrite Zmult_1_r; abstract auto with zarith
     | apply Z_to_Q_nonneg; assumption ]
  | apply Qle_lt_reg_pos;
     [ apply Qle_mult_nonneg_nonneg;
        [ apply Z_to_Q_nonneg; assumption | auto with * ]
     | apply Z_to_Q_pos; assumption ] ].
 
 apply f_equal with Q.
 apply f_equal2 with Q Q; [ field | reflexivity ].   

 (* (dL3) : b=0 & d<>0 & ~0<o2 & o2<0  *)
 unfold spec_Qhomographic_Qpositive_to_Q in |- *;
  clear e3 e0 e1 e2;
  simpl in |- *.
 transitivity
  (Qsgn
     (Qmult (Qmult a (Qpos (dL q))) (Qinv (Qplus (Qmult c (Qpos (dL q))) d)))).
 repeat rewrite Qsgn_15.  
 rewrite Qsgn_28.
 simpl in |- *.
 generalize (Zsgn_22 _ _ _x2) (Zsgn_24 _ _ _x2) (Zsgn_20 _ _ _x2);
  intros Hc_nonpos Hd_nonpos Hcd_neg.
 replace (Qsgn (Qplus (Qmult c (Qpos (dL q))) d)) with (-1)%Z.
 rewrite Qsgn_29.
 abstract auto with zarith.
 symmetry  in |- *.
 apply Qsgn_8.
 generalize (Zlt_cotrans_neg _ _ Hcd_neg); intros [Hc| Hd];
  [ apply Qlt_le_reg_neg;
     [ apply Qsgn_10; rewrite Qsgn_15; simpl in |- *; rewrite Qsgn_29;
        rewrite Zmult_1_r; abstract auto with zarith
     | apply Z_to_Q_nonpos; assumption ]
  | apply Qle_lt_reg_neg;
     [ apply Qle_mult_nonpos_pos;
        [ apply Z_to_Q_nonpos; assumption | auto with * ]
     | apply Z_to_Q_neg; assumption ] ].
 
 apply f_equal with Q.
 apply f_equal2 with Q Q; [ field | reflexivity ].   
 (* (dL4) : b=0 & d<>0 & ~0<o2 & ~o2<0  *)
 clear e3 e0 e1 e2;
  rewrite spec_Qhomographic_Qpositive_to_Q_dL; rewrite IHp0; 
  reflexivity.
 (* (dL5) : b<>0 & d=0 & 0<o1  *)
 unfold spec_Qhomographic_Qpositive_to_Q in |- *;
  clear e2 e0 e1 .
 simpl in |- *.
 transitivity
  (Qsgn
     (Qmult (Qplus (Qmult a (Qpos (dL q))) b) (Qinv (Qmult c (Qpos (dL q)))))).
 repeat rewrite Qsgn_15.  
 rewrite Qsgn_28.
 rewrite Qsgn_15.
 simpl in |- *.
 generalize (Zsgn_21 _ _ _x1) (Zsgn_23 _ _ _x1) (Zsgn_19 _ _ _x1);
  intros Ha_nonneg Hb_nonneg Hab_pos.
 replace (Qsgn (Qplus (Qmult a (Qpos (dL q))) b)) with 1%Z.
 rewrite Qsgn_29.
 abstract auto with zarith.
 symmetry  in |- *.
 apply Qsgn_7.
 generalize (Zlt_cotrans_pos _ _ Hab_pos); intros [Ha_| Hb_];
  [ apply Qlt_le_reg_pos;
     [ apply Qsgn_9; rewrite Qsgn_15; simpl in |- *; rewrite Qsgn_29;
        rewrite Zmult_1_r; abstract auto with zarith
     | apply Z_to_Q_nonneg; assumption ]
  | apply Qle_lt_reg_pos;
     [ apply Qle_mult_nonneg_nonneg;
        [ apply Z_to_Q_nonneg; assumption | auto with * ]
     | apply Z_to_Q_pos; assumption ] ].
 
 apply f_equal with Q.
 apply f_equal2 with Q Q;
  [ reflexivity | apply f_equal with Q; abstract ring ].

 (* (dL6) : b<>0 & d=0 & ~0<o1 & o1<0  *)
 unfold spec_Qhomographic_Qpositive_to_Q in |- *;
  clear e3 e0 e1 e2;
  simpl in |- *.
 transitivity
  (Qsgn
     (Qmult (Qplus (Qmult a (Qpos (dL q))) b) (Qinv (Qmult c (Qpos (dL q)))))).
 repeat rewrite Qsgn_15.  
 rewrite Qsgn_28.
 rewrite Qsgn_15.
 simpl in |- *.
 generalize (Zsgn_22 _ _ _x2) (Zsgn_24 _ _ _x2) (Zsgn_20 _ _ _x2);
  intros Ha_nonpos Hb_nonpos Hab_neg.
 replace (Qsgn (Qplus (Qmult a (Qpos (dL q))) b)) with (-1)%Z.
 rewrite Qsgn_29.
 abstract auto with zarith.
 symmetry  in |- *.
 apply Qsgn_8.
 generalize (Zlt_cotrans_neg _ _ Hab_neg); intros [Ha_| Hb_];
  [ apply Qlt_le_reg_neg;
     [ apply Qsgn_10; rewrite Qsgn_15; simpl in |- *; rewrite Qsgn_29;
        rewrite Zmult_1_r; abstract auto with zarith
     | apply Z_to_Q_nonpos; assumption ]
  | apply Qle_lt_reg_neg;
     [ apply Qle_mult_nonpos_pos;
        [ apply Z_to_Q_nonpos; assumption | auto with * ]
     | apply Z_to_Q_neg; assumption ] ].
 
 apply f_equal with Q.
 apply f_equal2 with Q Q;
  [ reflexivity | apply f_equal with Q; abstract ring ].   
 (* (dL7) : b<>0 & d=0 & ~0<o1 & ~o1<0  *)
 clear e3 e0 e1 e2 ;
  rewrite spec_Qhomographic_Qpositive_to_Q_dL; rewrite IHp0; 
  reflexivity.
 (* (dL8) : b<>0 & d<>0 & (i1 o1 o2) *)
 unfold spec_Qhomographic_Qpositive_to_Q in |- *;
  clear e2 e0 e1  .
 repeat rewrite Qsgn_15.  
 rewrite Qsgn_28.
 case (inside_interval_1_inf _ _ _x1); clear _x1;
  intros (Hab, Hcd);
  repeat
   match goal with
   | id1:(0 < outside_interval _ _)%Z |- _ =>
       generalize (Zsgn_21 _ _ id1) (Zsgn_23 _ _ id1) (Zsgn_19 _ _ id1);
        clear id1
   | id1:(outside_interval _ _ < 0)%Z |- _ =>
       generalize (Zsgn_22 _ _ id1) (Zsgn_24 _ _ id1) (Zsgn_20 _ _ id1);
        clear id1
   end; intros Ha_ Hb_ Hab_ Hc_ Hd_ Hcd_.
 replace (Qsgn (Qplus (Qmult a (Qpos (dL q))) b)) with 1%Z.
 replace (Qsgn (Qplus (Qmult c (Qpos (dL q))) d)) with 1%Z.
 abstract auto with zarith.
 symmetry  in |- *; apply Qsgn_7; generalize (Zlt_cotrans_pos _ _ Hcd_);
  intros [Hc_1| Hd_1];
  [ apply Qlt_le_reg_pos;
     [ apply Qsgn_9; rewrite Qsgn_15; simpl in |- *; rewrite Qsgn_29;
        rewrite Zmult_1_r; abstract auto with zarith
     | apply Z_to_Q_nonneg; assumption ]
  | apply Qle_lt_reg_pos;
     [ apply Qle_mult_nonneg_nonneg;
        [ apply Z_to_Q_nonneg; assumption | auto with * ]
     | apply Z_to_Q_pos; assumption ] ].
 symmetry  in |- *; apply Qsgn_7; generalize (Zlt_cotrans_pos _ _ Hab_);
  intros [Ha_1| Hb_1];
  [ apply Qlt_le_reg_pos;
     [ apply Qsgn_9; rewrite Qsgn_15; simpl in |- *; rewrite Qsgn_29;
        rewrite Zmult_1_r; abstract auto with zarith
     | apply Z_to_Q_nonneg; assumption ]
  | apply Qle_lt_reg_pos;
     [ apply Qle_mult_nonneg_nonneg;
        [ apply Z_to_Q_nonneg; assumption | auto with * ]
     | apply Z_to_Q_pos; assumption ] ].
 replace (Qsgn (Qplus (Qmult a (Qpos (dL q))) b)) with (-1)%Z.
 replace (Qsgn (Qplus (Qmult c (Qpos (dL q))) d)) with (-1)%Z.
 abstract auto with zarith.
 symmetry  in |- *; apply Qsgn_8; generalize (Zlt_cotrans_neg _ _ Hcd_);
  intros [Hc_1| Hd_1];
  [ apply Qlt_le_reg_neg;
     [ apply Qsgn_10; rewrite Qsgn_15; simpl in |- *; rewrite Qsgn_29;
        rewrite Zmult_1_r; abstract auto with zarith
     | apply Z_to_Q_nonpos; assumption ]
  | apply Qle_lt_reg_neg;
     [ apply Qle_mult_nonpos_pos;
        [ apply Z_to_Q_nonpos; assumption | auto with * ]
     | apply Z_to_Q_neg; assumption ] ].
 symmetry  in |- *; apply Qsgn_8; generalize (Zlt_cotrans_neg _ _ Hab_);
  intros [Ha_1| Hb_1];
  [ apply Qlt_le_reg_neg;
     [ apply Qsgn_10; rewrite Qsgn_15; simpl in |- *; rewrite Qsgn_29;
        rewrite Zmult_1_r; abstract auto with zarith
     | apply Z_to_Q_nonpos; assumption ]
  | apply Qle_lt_reg_neg;
     [ apply Qle_mult_nonpos_pos;
        [ apply Z_to_Q_nonpos; assumption | auto with * ]
     | apply Z_to_Q_neg; assumption ] ].
 (* (dL9) : b<>0 & d<>0 & ~(i1 o1 o2) & (i2 o1 o2)*)
 unfold spec_Qhomographic_Qpositive_to_Q in |- *;
  clear e3 e0 e1 e2  _x1.
 repeat rewrite Qsgn_15.  
 rewrite Qsgn_28.
 case (inside_interval_2_inf _ _ _x2); clear _x2;
  intros (Hab, Hcd);
  repeat
   match goal with
   | id1:(0 < outside_interval _ _)%Z |- _ =>
       generalize (Zsgn_21 _ _ id1) (Zsgn_23 _ _ id1) (Zsgn_19 _ _ id1);
        clear id1
   | id1:(outside_interval _ _ < 0)%Z |- _ =>
       generalize (Zsgn_22 _ _ id1) (Zsgn_24 _ _ id1) (Zsgn_20 _ _ id1);
        clear id1
   end.
 intros Hc_ Hd_ Hcd_ Ha_ Hb_ Hab_.
 replace (Qsgn (Qplus (Qmult a (Qpos (dL q))) b)) with 1%Z.
 replace (Qsgn (Qplus (Qmult c (Qpos (dL q))) d)) with (-1)%Z.
 abstract auto with zarith.
 symmetry  in |- *; apply Qsgn_8; generalize (Zlt_cotrans_neg _ _ Hcd_);
  intros [Hc_1| Hd_1];
  [ apply Qlt_le_reg_neg;
     [ apply Qsgn_10; rewrite Qsgn_15; simpl in |- *; rewrite Qsgn_29;
        rewrite Zmult_1_r; abstract auto with zarith
     | apply Z_to_Q_nonpos; assumption ]
  | apply Qle_lt_reg_neg;
     [ apply Qle_mult_nonpos_pos;
        [ apply Z_to_Q_nonpos; assumption | auto with * ]
     | apply Z_to_Q_neg; assumption ] ].
 symmetry  in |- *; apply Qsgn_7; generalize (Zlt_cotrans_pos _ _ Hab_);
  intros [Ha_1| Hb_1];
  [ apply Qlt_le_reg_pos;
     [ apply Qsgn_9; rewrite Qsgn_15; simpl in |- *; rewrite Qsgn_29;
        rewrite Zmult_1_r; abstract auto with zarith
     | apply Z_to_Q_nonneg; assumption ]
  | apply Qle_lt_reg_pos;
     [ apply Qle_mult_nonneg_nonneg;
        [ apply Z_to_Q_nonneg; assumption | auto with * ]
     | apply Z_to_Q_pos; assumption ] ].
 intros Ha_ Hb_ Hab_ Hc_ Hd_ Hcd_. 
 replace (Qsgn (Qplus (Qmult a (Qpos (dL q))) b)) with (-1)%Z.
 replace (Qsgn (Qplus (Qmult c (Qpos (dL q))) d)) with 1%Z.
 abstract auto with zarith.
 symmetry  in |- *; apply Qsgn_7; generalize (Zlt_cotrans_pos _ _ Hcd_);
  intros [Hc_1| Hd_1];
  [ apply Qlt_le_reg_pos;
     [ apply Qsgn_9; rewrite Qsgn_15; simpl in |- *; rewrite Qsgn_29;
        rewrite Zmult_1_r; abstract auto with zarith
     | apply Z_to_Q_nonneg; assumption ]
  | apply Qle_lt_reg_pos;
     [ apply Qle_mult_nonneg_nonneg;
        [ apply Z_to_Q_nonneg; assumption | auto with * ]
     | apply Z_to_Q_pos; assumption ] ].
 symmetry  in |- *; apply Qsgn_8; generalize (Zlt_cotrans_neg _ _ Hab_);
  intros [Ha_1| Hb_1];
  [ apply Qlt_le_reg_neg;
     [ apply Qsgn_10; rewrite Qsgn_15; simpl in |- *; rewrite Qsgn_29;
        rewrite Zmult_1_r; abstract auto with zarith
     | apply Z_to_Q_nonpos; assumption ]
  | apply Qle_lt_reg_neg;
     [ apply Qle_mult_nonpos_pos;
        [ apply Z_to_Q_nonpos; assumption | auto with * ]
     | apply Z_to_Q_neg; assumption ] ].
 (* (dL10) : b<>0 & d<>0 & ~(i1 o1 o2) & ~(i2 o1 o2)*)
 clear e3 e0 e1 e2;
  rewrite spec_Qhomographic_Qpositive_to_Q_dL; rewrite IHp0; 
  reflexivity.
(**********************************************************)
 (* (One1) : (Z.sgn (a+b)) = 0 *)
 unfold spec_Qhomographic_Qpositive_to_Q in |- *; clear e0.
 rewrite Qsgn_15.    
 replace (Qsgn (Qplus (Qmult a (Qpos One)) b)) with 0%Z.
 abstract auto with zarith.
 rewrite Qmult_sym.
 rewrite Qmult_one_left.
 rewrite <- Z_to_Qplus.
 symmetry  in |- *.
 rewrite Qsgn_29.
 assumption.
 (* (One2) : (Z.sgn (a+b))<>0 & (Z.sgn (a+b))=(Z.sgn (c+d)) *)
 Transparent Qone.
 unfold spec_Qhomographic_Qpositive_to_Q in |- *; clear e1 e0 ;
  rewrite Qsgn_15; repeat rewrite Qmult_one_right;
  rewrite Qsgn_28; repeat rewrite <- Z_to_Qplus; repeat rewrite Qsgn_29;
     rewrite <- _x1; rewrite <- Zsgn_15; symmetry  in |- *; 
  apply Zsgn_7'; abstract auto with zarith.
 (* (One2) : (Z.sgn (a+b))<>0 & (Z.sgn (a+b))<>(Z.sgn (c+d)) *)
 unfold spec_Qhomographic_Qpositive_to_Q in |- *; clear e1 e0;
     abstract (rewrite Qsgn_15; repeat rewrite Qmult_one_right; rewrite Qsgn_28;
       repeat rewrite <- Z_to_Qplus; repeat rewrite Qsgn_29;
         generalize
           (Zsgn_3 _
             (Qhomographic_signok_1 _ _ _x));
           intro Hcd_; generalize (Zsgn_1 (a + b)) (Zsgn_1 (c + d));
             intros [[Hab| Hab]| Hab] [[Hcd| Hcd]| Hcd]; 
               try solve [ Falsum ]; rewrite Hab in _x1; 
		 rewrite Hcd in _x1; try solve [ Falsum ]; 
		   rewrite Hab; rewrite Hcd; constructor).
Defined.


Lemma homographicAcc_positive :
 forall (a b c d : Z) (p : Qpositive),
 homographicAcc a b c d p ->
 Qlt Zero (Qplus (Qmult (Z_to_Q a) (Qpos p)) (Z_to_Q b)) /\
 Qlt Zero (Qplus (Qmult (Z_to_Q c) (Qpos p)) (Z_to_Q d)).
Proof.
 intros.
 induction H;
  try
   match goal with
   | id1:(_ /\ _) |- _ => elim id1; clear id1; intros IH_xind1 IH_ind2
   end.
 (* 1 *)
 split; rewrite H; rewrite Qmult_one_right; rewrite <- Z_to_Qplus;
  apply Z_to_Q_pos; assumption.
 (* 2 *)
 split; try assumption; replace a with (a - c + c)%Z;
  try abstract auto with zarith; replace b with (b - d + d)%Z;
  try abstract auto with zarith; repeat rewrite Z_to_Qplus;
  replace (Qplus (Qmult (Qplus (a - c)%Z c) (Qpos p)) (Qplus (b - d)%Z d))
   with
   (Qplus (Qplus (Qmult (a - c)%Z (Qpos p)) (b - d)%Z)
      (Qplus (Qmult c (Qpos p)) d)); try abstract ring;
  apply Qlt_plus_pos_pos; assumption.
 (* 3 *)
 split; try assumption; replace c with (c - a + a)%Z;
  try abstract auto with zarith; replace d with (d - b + b)%Z;
  try abstract auto with zarith; repeat rewrite Z_to_Qplus;
  replace (Qplus (Qmult (Qplus (c - a)%Z a) (Qpos p)) (Qplus (d - b)%Z b))
   with
   (Qplus (Qplus (Qmult (c - a)%Z (Qpos p)) (d - b)%Z)
      (Qplus (Qmult a (Qpos p)) b)); try abstract ring;
  apply Qlt_plus_pos_pos; assumption.
 (* 4 *)
 split; rewrite Qmult_Z_nR; rewrite <- Qplus_assoc; rewrite <- Z_to_Qplus;
  assumption.
 (* 5 *)
 split; rewrite Qmult_Z_plus_Z_dL; apply Qlt_mult_pos_pos; try assumption;
  apply Qinv_pos; abstract auto with *.
Defined. 


Lemma homographicAcc_positive_numerator :
 forall (a b c d : Z) (p : Qpositive),
 homographicAcc a b c d p ->
 Qlt Zero (Qplus (Qmult (Z_to_Q a) (Qpos p)) (Z_to_Q b)).
Proof.
 intros; elim (homographicAcc_positive _ _ _ _ _ H); trivial.
Defined.

Lemma homographicAcc_positive_denominator :
 forall (a b c d : Z) (p : Qpositive),
 homographicAcc a b c d p ->
 Qlt Zero (Qplus (Qmult (Z_to_Q c) (Qpos p)) (Z_to_Q d)).
Proof.
 intros; elim (homographicAcc_positive _ _ _ _ _ H); trivial.
Defined.


Lemma output_bit :
 forall (a b c d : Z) (p : Qpositive) (hyp_Acc : homographicAcc a b c d p),
 Qhomographic_Qpositive_to_Qpositive a b c d p hyp_Acc = spec_ni2 a b c d p.
Proof.
 intros a b c d p hyp_Acc.
 generalize (homographicAcc_positive_numerator _ _ _ _ _ hyp_Acc).
 generalize (homographicAcc_positive_denominator _ _ _ _ _ hyp_Acc).
 pattern a, b, c, d, p, hyp_Acc in |- *.
 elim hyp_Acc using homographicAcc_ind_dep; clear a b c d p hyp_Acc; intros;
  simpl in |- *.
 (* (One1) p= One *)
 unfold spec_ni2 in |- *; case (Qpositive_dec_One p); intros Hp;
  [ idtac | Falsum ]; rewrite coding;
  unfold spec_positive_fraction_encoding in |- *; replace (Qpos p) with Qone;
  [ idtac | rewrite e; trivial ]; repeat rewrite Qmult_one_right;
  repeat rewrite <- Z_to_Qplus; repeat rewrite Z_to_Qpositive_Q_tail_pos;
  reflexivity.
 (* (2) ~p=One & (top_more a b c d) *) 
 case (Qpositive_dec_One p); intros Hp; [ Falsum | idtac ];
  case (top_more_informative a b c d); intros Habcd; 
  [ idtac | Falsum ];
  generalize (homographicAcc_positive_numerator _ _ _ _ _ h); 
  intros H_acpbd; rewrite H; trivial; apply spec_ni2_nR_emission; 
  assumption.
 (* (3) ~p=One & ~(top_more a b c d)&(top_more c d a b) *) 
 case (Qpositive_dec_One p); intros Hp; [ Falsum | idtac ];
  case (top_more_informative a b c d); intros Habcd; 
  [ Falsum | idtac ]; case (top_more_informative c d a b); 
  intros Hcdab; [ idtac | Falsum ];
  generalize (homographicAcc_positive_denominator _ _ _ _ _ h);
  intros H_acpbd; rewrite H; trivial; apply spec_ni2_dL_emission; 
  assumption.
 (* (nR4) p=(nR xs) & ~(top_more a b c d)&~(top_more c d a b) *) 
 case (top_more_informative a b c d); intros Habcd; [ Falsum | idtac ];
  case (top_more_informative c d a b); intros Hcdab; 
  [ Falsum | idtac ];
  generalize (homographicAcc_positive_numerator _ _ _ _ _ h);
  generalize (homographicAcc_positive_denominator _ _ _ _ _ h);
  intros H_acpbd H_acpbd'; rewrite H; trivial; rewrite spec_ni2_nR;
  reflexivity.
 (* (dL5) p=(dL xs) & ~(top_more a b c d)&~(top_more c d a b) *) 
 case (top_more_informative a b c d); intros Habcd; [ Falsum | idtac ];
  case (top_more_informative c d a b); intros Hcdab; 
  [ Falsum | idtac ];
  generalize (homographicAcc_positive_numerator _ _ _ _ _ h);
  generalize (homographicAcc_positive_denominator _ _ _ _ _ h);
  intros H_acpbd H_acpbd'; rewrite H; trivial.
 rewrite spec_ni2_dL; reflexivity || apply Qlt_not_eq; assumption.
Defined.


Lemma spec_Qhomographic_Qpositive_to_Q_spec_ni2_pos :
 forall (a b c d : Z) (q : Qpositive),
 Qsgn (spec_Qhomographic_Qpositive_to_Q a b c d q) = 1%Z ->
 spec_Qhomographic_Qpositive_to_Q a b c d q = Qpos (spec_ni2 a b c d q).
Proof.
 intros a b c d p H.
 unfold spec_Qhomographic_Qpositive_to_Q in |- *.
 unfold spec_ni2 in |- *.
 rewrite <- Q_tail_Qinv.
 rewrite <- Q_tail_Qmult.
 rewrite <- Q_tail_Q_pos.
 reflexivity.
 apply Qsgn_9.
 assumption.

 intro H_absurd.
 unfold spec_Qhomographic_Qpositive_to_Q in H.
 rewrite H_absurd in H.
 discriminate H.

 intro H_absurd.
 unfold spec_Qhomographic_Qpositive_to_Q in H.
 rewrite H_absurd in H.
 rewrite Qmult_sym in H.
 discriminate H.
Defined.

(* This lemma is useless, to be removed later *)
Lemma spec_Qhomographic_Qpositive_to_Q_spec_ni2_neg :
 forall (a b c d : Z) (q : Qpositive),
 Qsgn (spec_Qhomographic_Qpositive_to_Q a b c d q) = (-1)%Z ->
 spec_Qhomographic_Qpositive_to_Q a b c d q = Qneg (spec_ni2 a b c d q).
Proof.
 intros a b c d p H.
 unfold spec_Qhomographic_Qpositive_to_Q in |- *.
 unfold spec_ni2 in |- *.
 rewrite <- Q_tail_Qinv.
 rewrite <- Q_tail_Qmult.
 rewrite <- Q_tail_Q_neg.
 reflexivity.
 apply Qsgn_10.
 assumption.

 intro H_absurd.
 unfold spec_Qhomographic_Qpositive_to_Q in H.
 rewrite H_absurd in H.
 discriminate H.

 intro H_absurd.
 unfold spec_Qhomographic_Qpositive_to_Q in H.
 rewrite H_absurd in H.
 rewrite Qmult_sym in H.
 discriminate H.
Defined.

(** We use this when (Z.sgn a+b)<0 *)
Lemma spec_Qhomographic_Qpositive_to_Q_spec_ni2_neg_1 :
 forall (a b c d : Z) (q : Qpositive),
 Qsgn (spec_Qhomographic_Qpositive_to_Q a b c d q) = (-1)%Z ->
 spec_Qhomographic_Qpositive_to_Q a b c d q =
 Qneg (spec_ni2 (- a) (- b) c d q).
Proof.
 intros a b c d p H.
 unfold spec_Qhomographic_Qpositive_to_Q in |- *.
 unfold spec_ni2 in |- *.
 rewrite <- Q_tail_Qinv.
 rewrite <- Q_tail_Qmult.
 rewrite Qopp_Qpos.
 rewrite <- Q_tail_Q_pos.
 rewrite Qopp_linear.
 abstract ring.

 apply Qsgn_9.
 rewrite Qopp_linear.
 rewrite Qmult_Qopp_left.
 rewrite Qsgn_25.
 unfold spec_Qhomographic_Qpositive_to_Q in H.
 rewrite H.
 constructor.

 rewrite Qopp_linear.
 apply Qopp_resp_nonzero.

 intro H_absurd.
 unfold spec_Qhomographic_Qpositive_to_Q in H.
 rewrite H_absurd in H.
 discriminate H.

 intro H_absurd.
 unfold spec_Qhomographic_Qpositive_to_Q in H.
 rewrite H_absurd in H.
 rewrite Qmult_sym in H.
 discriminate H.
Defined.

(** We use this when 0<=(Z.sgn a+b) *)
Lemma spec_Qhomographic_Qpositive_to_Q_spec_ni2_neg_2 :
 forall (a b c d : Z) (q : Qpositive),
 Qsgn (spec_Qhomographic_Qpositive_to_Q a b c d q) = (-1)%Z ->
 spec_Qhomographic_Qpositive_to_Q a b c d q =
 Qneg (spec_ni2 a b (- c) (- d) q).
Proof.
 intros a b c d p H.
 unfold spec_Qhomographic_Qpositive_to_Q in |- *.
 unfold spec_ni2 in |- *.
 rewrite <- Q_tail_Qinv.
 rewrite <- Q_tail_Qmult.
 rewrite Qopp_Qpos.
 rewrite <- Q_tail_Q_pos.
 rewrite Qopp_linear.
 rewrite Qinv_Qopp.
 abstract ring.

 apply Qsgn_9.
 rewrite Qopp_linear.
 rewrite Qinv_Qopp.
 rewrite Qmult_sym.
 rewrite Qmult_Qopp_left.
 rewrite Qsgn_25.
 rewrite Qmult_sym.
 unfold spec_Qhomographic_Qpositive_to_Q in H.
 rewrite H.
 constructor.


 intro H_absurd.
 unfold spec_Qhomographic_Qpositive_to_Q in H.
 rewrite H_absurd in H.
 discriminate H.

 rewrite Qopp_linear.
 rewrite Qinv_Qopp.
 apply Qopp_resp_nonzero.

 intro H_absurd.
 unfold spec_Qhomographic_Qpositive_to_Q in H.
 rewrite H_absurd in H.
 rewrite Qmult_sym in H.
 discriminate H.
Defined.


(** Here we don't require that a*q+b<>0, maybe we should! but the lemma is true anyway! *) 
Lemma spec_Qhomographic_Qpositive_to_Q_Zopp :
 forall (a b c d : Z) (q : Qpositive),
 spec_Qhomographic_Qpositive_to_Q (- a) (- b) (- c) (- d) q =
 spec_Qhomographic_Qpositive_to_Q a b c d q.
Proof.
 intros a b c d q.
 unfold spec_Qhomographic_Qpositive_to_Q in |- *.
 repeat rewrite Zopp_eq_mult_neg_1.

 repeat rewrite Z_to_Qmult.
 repeat rewrite <- Qmult_assoc.
 rewrite (Qmult_sym (-1)%Z).
 repeat rewrite Qmult_assoc.
 repeat rewrite <- Q_distr_left.
 rewrite <- Qdiv_num_denom with (p := (-1)%Z).
 reflexivity.
 abstract discriminate.
Defined.
 


(** Here we don't require that a*q+b<>0, maybe we should! but the lemma is true anyway! *) 
Lemma spec_Qhomographic_Qpositive_to_Q_Zopp_2 :
 forall (a b c d : Z) (q : Qpositive),
 spec_Qhomographic_Qpositive_to_Q (- a) (- b) c d q =
 Qopp (spec_Qhomographic_Qpositive_to_Q a b c d q).
Proof.
 intros a b c d q.
 unfold spec_Qhomographic_Qpositive_to_Q in |- *.
 rewrite Qopp_linear.
 apply Qmult_Qopp_left.
Defined.
 
Lemma spec_Qhomographic_Qpositive_to_Q_Zopp_3 :
 forall (a b c d : Z) (q : Qpositive),
 spec_Qhomographic_Qpositive_to_Q a b (- c) (- d) q =
 Qopp (spec_Qhomographic_Qpositive_to_Q a b c d q).
Proof.
 intros a b c d q; unfold spec_Qhomographic_Qpositive_to_Q in |- *;
  rewrite Qopp_linear; rewrite Qinv_Qopp; rewrite Qmult_sym;
  rewrite Qmult_Qopp_left; rewrite Qmult_sym; reflexivity.
Defined.

Lemma sg_pres_fraction :
 forall (a b c d : Z) (p : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
 Qmult
   (Qplus
      (Qmult (new_a a b c d p H_Qhomographic_sg_denom_nonzero)
         (Qpos (new_p a b c d p H_Qhomographic_sg_denom_nonzero)))
      (new_b a b c d p H_Qhomographic_sg_denom_nonzero))
   (Qinv
      (Qplus
         (Qmult (new_c a b c d p H_Qhomographic_sg_denom_nonzero)
            (Qpos (new_p a b c d p H_Qhomographic_sg_denom_nonzero)))
         (new_d a b c d p H_Qhomographic_sg_denom_nonzero))) =
 Qmult (Qplus (Qmult a (Qpos p)) b) (Qinv (Qplus (Qmult c (Qpos p)) d)).
Proof.
intros a b c d p H_Qhomographic_sg_denom_nonzero.
unfold new_a, new_b, new_c, new_d, new_p in |- *.
functional induction (Qhomographic_sign a b c d p
                             H_Qhomographic_sg_denom_nonzero);
try reflexivity;rewrite IHp0; clear IHp0;symmetry  in |- *;
try first [
    apply spec_Qhomographic_Qpositive_to_Q_nR_unfolded | 
       apply spec_Qhomographic_Qpositive_to_Q_dL_unfolded
].
Qed.


Lemma a_field_equality_1 :
 forall x y z t w : Q,
 Qmult x t = Qmult y z ->
 t <> Zero ->
 Qplus (Qmult z w) t <> Zero ->
 Qmult (Qplus (Qmult x w) y) (Qinv (Qplus (Qmult z w) t)) = Qmult y (Qinv t).
Proof.
 intros a b c d p H_xt_eq_yz Ht H_denom;
 rewrite Qdiv_num_denom with (p := d); [ idtac | assumption ];
 replace (Qmult (Qplus (Qmult a p) b) d) with
   (Qplus (Qmult (Qmult a d) p) (Qmult b d));
 [ idtac | ring ]; rewrite H_xt_eq_yz;
 field; auto.
Defined.

Lemma Qhomographic_sg_denom_nonzero_correct_1 :
 forall (c d : Z) (p : Qpositive),
 Qhomographic_sg_denom_nonzero c d p -> Qplus (Qmult c (Qpos p)) d <> Zero.
Proof.
 intros c d p H_Qhomographic_sg_denom_nonzero.
 induction H_Qhomographic_sg_denom_nonzero.
  (* 1 *)
  replace Zero with (Z_to_Q 0); trivial.
  rewrite H.
  rewrite Qmult_one_right.
  rewrite <- Z_to_Qplus.
  apply Z_to_Q_not_eq.
  assumption.
  (* 2 *)
  rewrite Qpos_nR.  
  replace (Qplus (Qmult c (Qplus (Qpos xs) Qone)) d) with
   (Qplus (Qmult c (Qpos xs)) (Qplus c d)).
  rewrite <- Z_to_Qplus.
  assumption.
  abstract ring.
  (* 3 *)
  rewrite Qpos_dL.  
  replace (Qplus (Qmult c (Qmult (Qpos xs) (Qinv (Qplus (Qpos xs) Qone)))) d)
   with
   (Qmult (Qplus (Qmult (Qplus c d) (Qpos xs)) d)
      (Qinv (Qplus (Qpos xs) Qone))).
  apply Qmult_resp_nonzero.
  rewrite <- Z_to_Qplus.
  assumption.
  abstract discriminate.   
  abstract (field; discriminate).
Defined.

Lemma Qhomographic_sg_denom_nonzero_correct_2 :
 forall (c d : Z) (p : Qpositive),
 Qplus (Qmult c (Qpos p)) d <> Zero -> Qhomographic_sg_denom_nonzero c d p.
Proof.
 intros c d p.
 generalize c d.
 clear c d.
 induction p.
 (* nR *)
 intros.
 apply Qhomographic_signok1.
 apply IHp.
 replace (Qplus (Qmult c (Qpos p)) (c + d)%Z) with
  (Qplus (Qmult c (Qplus (Qpos p) Qone)) d).
 rewrite Qpos_nR in H; assumption.
 rewrite Z_to_Qplus.
 abstract ring.
 (* dL *)
 intros.
 apply Qhomographic_signok2.
 apply IHp.
 intro.
 apply H.
 rewrite Qpos_dL.  
 replace (Qplus (Qmult c (Qmult (Qpos p) (Qinv (Qplus (Qpos p) Qone)))) d)
  with
  (Qmult (Qplus (Qmult (Qplus c d) (Qpos p)) d) (Qinv (Qplus (Qpos p) Qone))).
 rewrite <- Z_to_Qplus.
 rewrite H0.
 rewrite Qmult_zero; reflexivity.

 abstract (field; discriminate).
 (* One *)
 intros.
 apply Qhomographic_signok0; trivial.
 intro.
 apply H.
 rewrite Qmult_one_right.
 rewrite <- Z_to_Qplus.
 replace Zero with (Z_to_Q 0); trivial.
 apply f_equal with Z; assumption.
Defined.


Lemma homography_positive_input :
 forall (a b c d : Z) (p : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
 Qhomographic_Qpositive_to_Q a b c d p H_Qhomographic_sg_denom_nonzero =
 Qmult (Qplus (Qmult a (Qpos p)) b) (Qinv (Qplus (Qmult c (Qpos p)) d)).
Proof.
 intros a b c d p H_Qhomographic_sg_denom_nonzero.
 functional induction
   (Qhomographic_Qpositive_to_Q a b c d p H_Qhomographic_sg_denom_nonzero).

 (* 1 *)
 clear e e0 e1 .
 rename x into Hc0;
 rename _x into ad_eq_bc;
   rewrite coding_Q.
 assert (b0_eq_zero : b = 0%Z).
 rewrite Zmult_0_r in ad_eq_bc.
        apply Zmult_integral_l with c;assumption || symmetry  in |- *;
        assumption.

	rewrite b0_eq_zero.
	simpl in *.
        unfold spec_fraction_encoding in |- *;
        repeat rewrite Qplus_zero_right;
        abstract (
                   (* Field.
                           Anomaly: Search error. Please report.
                         *)
                   rewrite <- Qdiv_num_denom; [ reflexivity | discriminate ]) .
 clear e e0 e1.
 rename H into Hc0;
 rename _x into ad_eq_bc;
   rewrite coding_Q.
 assert (b0_eq_zero : b = 0%Z).
 rewrite Zmult_0_r in ad_eq_bc.
        apply Zmult_integral_l with c;assumption || symmetry  in |- *;
        assumption.

	rewrite b0_eq_zero.
	simpl in *.
        unfold spec_fraction_encoding in |- *;
        repeat rewrite Qplus_zero_right;
        abstract (
                   (* Field.
                           Anomaly: Search error. Please report.
                         *)
                   rewrite <- Qdiv_num_denom; [ reflexivity | discriminate ]) .
 (* 2 *)
  rewrite coding_Q;
  unfold spec_fraction_encoding in |- *; symmetry  in |- *;
  apply a_field_equality_1;
  [ repeat rewrite <- Z_to_Qmult; apply f_equal with Z
  | replace Zero with (Z_to_Q 0); trivial; apply Z_to_Q_not_eq
  | apply Qhomographic_sg_denom_nonzero_correct_1 ]; 
  assumption.
 (* 3 *)
 clear e0 e; 
   symmetry  in |- *;
  replace
   (Qmult (Qplus (Qmult a (Qpos p)) b) (Qinv (Qplus (Qmult c (Qpos p)) d)))
   with (spec_Qhomographic_Qpositive_to_Q a b c d p); 
  trivial; apply Qsgn_2;
  rewrite <- (homographic_sign a b c d p H_Qhomographic_sg_denom_nonzero);
  assumption.
 (* 4 *)
 rewrite output_bit;
  rewrite <- spec_Qhomographic_Qpositive_to_Q_spec_ni2_pos;
  unfold spec_Qhomographic_Qpositive_to_Q in |- *; 
  rewrite sg_pres_fraction;
  [ reflexivity
  | change (Qsgn (spec_Qhomographic_Qpositive_to_Q a b c d p) = 1%Z) in |- *;
     rewrite <- (homographic_sign a b c d p H_Qhomographic_sg_denom_nonzero);
     assumption ].
 (* 5 *)
 rewrite output_bit;
  rewrite <- spec_Qhomographic_Qpositive_to_Q_spec_ni2_pos;
  rewrite spec_Qhomographic_Qpositive_to_Q_Zopp;
  unfold spec_Qhomographic_Qpositive_to_Q in |- *; 
  rewrite sg_pres_fraction;
  [ reflexivity
  | change (Qsgn (spec_Qhomographic_Qpositive_to_Q a b c d p) = 1%Z) in |- *;
     rewrite <- (homographic_sign a b c d p H_Qhomographic_sg_denom_nonzero);
     assumption ].
 (* 6 *)
 rewrite output_bit;
  rewrite <- spec_Qhomographic_Qpositive_to_Q_spec_ni2_neg_1;
  unfold spec_Qhomographic_Qpositive_to_Q in |- *; 
  rewrite sg_pres_fraction;
  [ reflexivity
  | change (Qsgn (spec_Qhomographic_Qpositive_to_Q a b c d p) = (-1)%Z)
     in |- *;
     rewrite <- (homographic_sign a b c d p H_Qhomographic_sg_denom_nonzero);
     assumption ].
 (* 7 *)
 rewrite output_bit;
  rewrite <- spec_Qhomographic_Qpositive_to_Q_spec_ni2_neg_2;
  unfold spec_Qhomographic_Qpositive_to_Q in |- *; 
  rewrite sg_pres_fraction;
  [ reflexivity
  | change (Qsgn (spec_Qhomographic_Qpositive_to_Q a b c d p) = (-1)%Z)
     in |- *;
     rewrite <- (homographic_sign a b c d p H_Qhomographic_sg_denom_nonzero);
     assumption ].
Defined.

Lemma homography :
 forall (a b c d : Z) (s : Q)
   (H_Qhomographic_denom_nonzero : Qhomographic_denom_nonzero c d s),
 Qhomographic a b c d s H_Qhomographic_denom_nonzero = spec_h a b c d s.
Proof.
 intros a b c d [| s| s] H_Qhomographic_denom_nonzero.
 (* (1) s=Zero *)
 unfold Qhomographic in |- *.
 unfold spec_h in |- *.
 rewrite Qmult_sym with a Zero.
 rewrite Qmult_sym with c Zero.
 repeat rewrite Qmult_zero.
 repeat rewrite Qplus_zero_left.
 rewrite coding_Q.
 reflexivity.
 (* (2) s=(Qpos s) *)
 unfold Qhomographic in |- *.
 unfold spec_h in |- *.
 apply homography_positive_input.
 (* (3) s=(Qneg s) *)
 unfold Qhomographic in |- *.
 unfold spec_h in |- *.
 rewrite homography_positive_input.
 apply f_equal2 with Q Q; [ idtac | apply f_equal with Q ];
  apply f_equal2 with Q Q; trivial; repeat rewrite Z_to_Qopp;
  repeat rewrite <- Qmult_neg; abstract ring.
Defined.
 
Lemma Qhomographic_denom_nonzero_correct_1 :
 forall (c d : Z) (q : Q),
 Qplus (Qmult c q) d <> Zero -> Qhomographic_denom_nonzero c d q.
Proof.
 abstract (intros c d [| p| p] H_denom;
            [  (* Zero *)
               apply Qhomographicok0; trivial; intros H; 
               apply H_denom; rewrite H; replace (Z_to_Q 0) with Zero;
               trivial; abstract ring
            |  (* Qpos *)
               apply Qhomographicok1 with p; trivial;
               apply Qhomographic_sg_denom_nonzero_correct_2; 
               assumption
            |  (* Qneg *)
               apply Qhomographicok2 with p; trivial;
               apply Qhomographic_sg_denom_nonzero_correct_2; 
               intro H; apply H_denom;
               replace (Qmult c (Qneg p)) with (Qmult (- c)%Z (Qpos p));
               trivial; rewrite Z_to_Qopp; rewrite Qopp_Qpos; abstract 
               ring ]).
Defined.
 
 
Lemma Qhomographic_denom_nonzero_correct_2 :
 forall (c d : Z) (q : Q),
 Qhomographic_denom_nonzero c d q -> Qplus (Qmult c q) d <> Zero.
Proof.
 abstract (intros c d q H_Qhomographic_denom_nonzero;
            induction H_Qhomographic_denom_nonzero;
            [  (* Zero *)
               rewrite H; replace (Qmult c Zero) with Zero;
               [ idtac | abstract ring ]; rewrite Qplus_zero_left;
               replace Zero with (Z_to_Q 0); trivial; 
               apply Z_to_Q_not_eq; assumption
            |  (* Qpos *)
               rewrite H; apply Qhomographic_sg_denom_nonzero_correct_1;
               assumption
            |  (* Qneg *)
               rewrite H;
               replace (Qmult c (Qneg p)) with (Qmult (- c)%Z (Qpos p));
               [ apply Qhomographic_sg_denom_nonzero_correct_1; assumption
               | rewrite Z_to_Qopp; rewrite Qopp_Qpos; abstract ring ] ]).
Defined.
 
Theorem homography_algorithm_is_correct :
 forall (a b c d : Z) (q : Q) (H_denom : Qplus (Qmult c q) d <> Zero),
 Qhomographic a b c d q (Qhomographic_denom_nonzero_correct_1 c d q H_denom) =
 Qmult (Qplus (Qmult a q) b) (Qinv (Qplus (Qmult c q) d)).
Proof.
 intros a b c d q H_denom;
  apply
   (homography a b c d q (Qhomographic_denom_nonzero_correct_1 c d q H_denom)).
Defined.
