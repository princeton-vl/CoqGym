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


Require Export Q_field.
 
Theorem Qmult_sym : forall n m : Q, Qmult n m = Qmult m n.
intros n m; case m; case n; auto; intros n' m'; simpl in |- *;
 rewrite Qpositive_mult_sym; auto.
Qed.
 
Theorem Qmult_assoc :
 forall n m p : Q, Qmult n (Qmult m p) = Qmult (Qmult n m) p.
intros n m p; case p; case m; case n; auto; intros n' m' p'; simpl in |- *;
 rewrite Qpositive_mult_assoc; auto.
Qed.
 
Theorem Qplus_zero_left : forall n : Q, Qplus Zero n = n.
intros n; case n; auto.
Qed.
 
Theorem Qmult_one_left : forall n : Q, Qmult (Qpos One) n = n.
intros n; case n; simpl in |- *; auto; intros; rewrite Qpositive_mult_One;
 auto.
Qed.
 
Theorem Q_opp_def : forall n : Q, Qplus n (Qopp n) = Zero.
intros n; case n; simpl in |- *; auto.
intros n'; Case' (Qpositive_le_dec n' n').
case (Qpositive_eq_dec n' n'); auto.
intros H; elim H; auto.
intros H; elim H; auto.
intros n'; Case' (Qpositive_le_dec n' n').
case (Qpositive_eq_dec n' n'); auto.
intros H; elim H; auto.
intros H; elim H; auto.
Qed.
 
Definition Q_eq (n m : Q) :=
  match n, m with
  | Zero, Zero => true
  | Qpos n', Qpos m' =>
      match Qpositive_eq_dec n' m' with
      | left h => true
      | right h => false
      end
  | Qneg n', Qneg m' =>
      match Qpositive_eq_dec n' m' with
      | left h => true
      | right h => false
      end
  | _, _ => false
  end.
 
Theorem Q_eq_prop : forall x y : Q, Q_eq x y = true -> x = y.
intros x y Htrue; generalize Htrue; clear Htrue.
case y; case x; try (intros; simpl in Htrue; discriminate; fail).
(* Focus 1 *)
auto.
(* Focus 2 *)
intros x' y'; simpl in |- *; case (Qpositive_eq_dec x' y').
intros H; rewrite H; auto.
intros; discriminate.
(* Focus 3 *)
intros x' y'; simpl in |- *; case (Qpositive_eq_dec x' y').
intros H; rewrite H; auto.
intros; discriminate.
Qed.
 
Theorem not_one_zero : Qpos One <> Zero.
discriminate.
Qed.
 
Definition Qinv (x : Q) :=
  match x with
  | Qpos x => Qpos (Qpositive_inv x)
  | Qneg x => Qneg (Qpositive_inv x)
  | Zero => Zero
  end.
 
Theorem Qinv_def : forall x : Q, x <> Zero -> Qmult x (Qinv x) = Qpos One.
intros x; case x.
(* 2 *)
2: intros x' Hneg; simpl in |- *.
2: rewrite Qpositive_mult_inv; auto.
(* 1 *)
intros H; elim H; auto.
(* 3 *)
intros x' Hneg; simpl in |- *.
rewrite Qpositive_mult_inv; auto.
Qed.
 
Theorem Q_integral : forall x y : Q, Qmult x y = Zero -> x = Zero \/ y = Zero.
intros x y; case y; case x; simpl in |- *; auto; intros x' y' H;
 discriminate H.
Qed.
 
Inductive Qgt : Q -> Q -> Prop :=
  | Qgt_pos_pos :
      forall x' y' : Qpositive,
      ~ Qpositive_le x' y' -> Qgt (Qpos x') (Qpos y')
  | Qgt_neg_neg :
      forall x' y' : Qpositive,
      ~ Qpositive_le y' x' -> Qgt (Qneg x') (Qneg y')
  | Qgt_pos_zero : forall x' : Qpositive, Qgt (Qpos x') Zero
  | Qgt_pos_neg : forall x' y' : Qpositive, Qgt (Qpos x') (Qneg y')
  | Qgt_zero_neg : forall x' : Qpositive, Qgt Zero (Qneg x').
Hint Resolve Qgt_pos_pos Qgt_neg_neg Qgt_pos_zero Qgt_pos_neg Qgt_zero_neg.
 
Theorem Qgt_total : forall x y : Q, Qgt x y \/ x = y \/ Qgt y x.
intros x y; case y; case x; auto.
intros x' y'; case (Qpositive_le_dec x' y'); auto with *.
case (Qpositive_eq_dec x' y').
intros e q; right; left; rewrite e; auto.
intros n q; right; right; apply Qgt_pos_pos.
red in |- *; intros H; elim n; apply Qpositive_le_antisym; auto.
intros x' y'; case (Qpositive_le_dec x' y'); auto with *.
case (Qpositive_eq_dec x' y').
intros e q; right; left; rewrite e; auto.
intros n q; left; apply Qgt_neg_neg.
red in |- *; intros H; elim n; apply Qpositive_le_antisym; auto.
Qed.
 
Definition Q_eq_dec : forall x y : Q, {x = y} + {x <> y}.
intros x y; case x; case y; try (right; discriminate).
(* Focus 1 *)
auto.
(* Focus 2 *)
intros y' x'; case (Qpositive_eq_dec x' y').
intros H; left; rewrite H; auto.
intros H; right; red in |- *; intros H'; elim H.
injection H'; auto.
(* Focus 3 *)
intros y' x'; case (Qpositive_eq_dec x' y').
intros H; left; rewrite H; auto.
intros H; right; red in |- *; intros H'; elim H.
injection H'; auto.
Qed.
 
Theorem Qgt_antisym : forall x y : Q, Qgt x y -> ~ Qgt y x.
intros x y H; elim H.
intros x' y' H1; red in |- *; intros H2; elim H1.
inversion H2.
apply not_Qpositive_le_Qpositive_le'; auto with *.
intros x' y' H1; red in |- *; intros H2; elim H1.
inversion H2; apply not_Qpositive_le_Qpositive_le'; auto.
unfold not in |- *; intros x' H1; inversion H1.
unfold not in |- *; intros x' y' H1; inversion H1.
unfold not in |- *; intros x' H1; inversion H1.
Qed.
 
Theorem Qgt_trans : forall x y z : Q, Qgt x y -> Qgt y z -> Qgt x z.
intros x y z H; elim H; auto with *.
intros x' y' H1 H2; inversion H2; auto with *.
apply Qgt_pos_pos.
red in |- *; intros H5; elim H3.
apply Qpositive_le_trans with x'; auto with *.
apply not_Qpositive_le_Qpositive_le'.
auto.
intros x' y' H1 H2; inversion H2; auto with *.
apply Qgt_neg_neg.
red in |- *; intros H5; elim H3.
apply Qpositive_le_trans with x'; auto with *.
apply not_Qpositive_le_Qpositive_le'.
auto.
intros x' H1; inversion H1; auto with *.
intros x' y' H1; inversion H1; auto with *.
intros x' H1; inversion H1; auto.
Qed.
 
Theorem Qpositive_le_plus_simpl :
 forall x y z : Qpositive,
 Qpositive_le (Qpositive_plus x z) (Qpositive_plus y z) -> Qpositive_le x y.
intros x y z H; rewrite <- (Qpositive_sub_correct x z).
rewrite <- (Qpositive_sub_correct y z).
apply Qpositive_le_sub_r; auto with *.
rewrite Qpositive_plus_sym; apply sym_not_equal; apply Qpositive_plus_diff.
rewrite Qpositive_plus_sym; apply sym_not_equal; apply Qpositive_plus_diff.
rewrite Qpositive_plus_sym; apply Qpositive_plus_le.
rewrite Qpositive_plus_sym; apply Qpositive_plus_le.
Qed.
 
Theorem Qpositive_le_sub_simpl_r :
 forall x y z : Qpositive,
 Qpositive_le z x ->
 Qpositive_le z y ->
 z <> x ->
 z <> y ->
 Qpositive_le (Qpositive_sub x z) (Qpositive_sub y z) -> Qpositive_le x y.
intros x y z H H0 H1 H2 H3.
rewrite <- (Qpositive_sub_correct2 x z); auto.
rewrite <- (Qpositive_sub_correct2 y z); auto.
apply Qpositive_le_add.
auto.
Qed.
 
Theorem Qpositive_le_sub_simpl_l :
 forall x y z : Qpositive,
 Qpositive_le x z ->
 Qpositive_le y z ->
 z <> x ->
 z <> y ->
 Qpositive_le (Qpositive_sub z x) (Qpositive_sub z y) -> Qpositive_le y x.
intros x y z H H0 H1 H2 H3.
replace y with (Qpositive_sub z (Qpositive_sub z y)).
replace x with (Qpositive_sub z (Qpositive_sub z x)).
apply Qpositive_le_sub_l.
apply sym_not_equal; apply Qpositive_sub_diff; auto.
apply sym_not_equal; apply Qpositive_sub_diff; auto.
apply Qpositive_sub_le; auto.
apply Qpositive_sub_le; auto.
auto.
rewrite Qpositive_sub_sub_assoc; auto.
rewrite Qpositive_plus_sym; rewrite Qpositive_sub_correct; auto.
apply Qpositive_sub_diff.
auto.
auto.
apply Qpositive_sub_le; auto.
rewrite Qpositive_sub_sub_assoc; auto.
rewrite Qpositive_plus_sym; rewrite Qpositive_sub_correct; auto.
apply Qpositive_sub_diff.
auto.
auto.
apply Qpositive_sub_le; auto.
Qed.
 
Theorem Qgt_plus : forall x y z : Q, Qgt x y -> Qgt (Qplus z x) (Qplus z y).
intros x y z H; elim H.
intros x' y' Hnle; generalize (not_Qpositive_le_Qpositive_le' _ _ Hnle).
intros Hle; generalize (not_Qpositive_le_not_eq _ _ Hnle).
intros Hneq.
case z; simpl in |- *; auto.
(* z=(Qpos z') *)
intros z'; apply Qgt_pos_pos.
red in |- *; intros Hle'; elim Hneq; apply Qpositive_le_antisym.
apply Qpositive_le_plus_simpl with z';
 repeat rewrite <- (Qpositive_plus_sym z'); auto with *.
auto.
(* z=(Qneg z') *)
intros z'; Case' (Qpositive_le_dec z' x').
case (Qpositive_eq_dec z' x').
Case' (Qpositive_le_dec z' y').
intros q e q0.
elim Hnle.
rewrite <- e; auto.
auto.
Case' (Qpositive_le_dec z' y').
case (Qpositive_eq_dec z' y').
auto.
intros n q n0 q0.
apply Qgt_pos_pos.
red in |- *; intros H0.
elim Hnle; apply Qpositive_le_sub_simpl_r with z'; auto with *.
auto.
Case' (Qpositive_le_dec z' y').
intros q H0 H1 H2.
elim Hneq; apply Qpositive_le_antisym; auto with *.
apply Qpositive_le_trans with z'; auto.
intros H0 H1 H4 H2 H3 H5.
apply Qgt_neg_neg.
red in |- *; intros H6.
elim Hnle.
apply Qpositive_le_sub_simpl_l with z'; auto.

(*  (x',y':Qpositive)~(Qpositive_le y' x') *)
intros x' y' Hnle; case z; auto.
(* Focus 1 *)
simpl in |- *; auto.
(* Focus 2 *)
intros z'; simpl in |- *.
Case' (Qpositive_le_dec z' x').
case (Qpositive_eq_dec z' x').
Case' (Qpositive_le_dec z' y').
case (Qpositive_eq_dec z' y').
intros e q e0 q0; elim Hnle; rewrite <- e; rewrite <- e0;
 apply Qpositive_le_refl.
auto.
intros H0 H1 H2 e q; elim Hnle; rewrite <- e; auto.
Case' (Qpositive_le_dec z' y').
case (Qpositive_eq_dec z' y').
intros e q n q0; elim Hnle; rewrite <- e; try assumption.
intros n q n0 q0.
apply Qgt_neg_neg.
red in |- *; intros H0.
elim Hnle; apply Qpositive_le_sub_simpl_r with z'; auto with *.
intros H0 H1 H2 n q; elim Hnle; apply Qpositive_le_trans with z'; auto.
Case' (Qpositive_le_dec z' y').
case Qpositive_eq_dec; auto with *.
intros H0 H1 H4 H2 H3 H5.
apply Qgt_pos_pos.
red in |- *; intros H6; elim Hnle.
apply Qpositive_le_sub_simpl_l with z'; auto.
(* Focus 3 *)
simpl in |- *.
intros z'; apply Qgt_neg_neg.
red in |- *; intros H0; elim Hnle; apply Qpositive_le_plus_simpl with z'.
repeat rewrite <- (Qpositive_plus_sym z').
auto.

(*  (Qgt x y)->(x':Qpositive)(Qgt (Qplus z (Qpos x')) (Qplus z Zero)) *)
intros x'; case z.
(* Focus 1 *)
simpl in |- *; auto.
(* Focus 2 *)
intros z'; simpl in |- *.
apply Qgt_pos_pos.
red in |- *; intros H0; elim (Qpositive_plus_diff z' x').
apply Qpositive_le_antisym; auto.
apply Qpositive_plus_le.
(* Focus 3 *)
intros z'; simpl in |- *.
Case' (Qpositive_le_dec z' x').
case (Qpositive_eq_dec z' x'); auto with *.
intros H0 H1 H2; apply Qgt_neg_neg.
red in |- *; intros H3; elim (Qpositive_sub_diff z' x'); auto with *.
apply Qpositive_le_antisym; auto.
apply Qpositive_sub_le; auto.
(*   (x',y':Qpositive)(Qgt (Qplus z (Qpos x')) (Qplus z (Qneg y'))) *)
intros x' y'; case z; simpl in |- *; auto with *.
(* Goal 1 is solved with Auto *)
(* Focus 2 *)
intros z'; Case' (Qpositive_le_dec z' y').
case (Qpositive_eq_dec z' y'); auto with *.
intros H0 H1 H2; apply Qgt_pos_pos.
red in |- *; intros H3; elim (Qpositive_plus_diff z' x').
apply Qpositive_le_antisym.
apply Qpositive_plus_le.
apply Qpositive_le_trans with (Qpositive_sub z' y'); auto with *.
apply Qpositive_sub_le; auto.
(* Focus 3 *)
intros z'; Case' (Qpositive_le_dec z' x').
case (Qpositive_eq_dec z' x').
auto.
auto.
intros H0 H1 H2; apply Qgt_neg_neg.
red in |- *; intros H3; elim (Qpositive_plus_diff z' y').
apply Qpositive_le_antisym.
apply Qpositive_plus_le.
apply Qpositive_le_trans with (Qpositive_sub z' x'); auto with *.
apply Qpositive_sub_le; auto.

(* (x':Qpositive)(Qgt (Qplus z Zero) (Qplus z (Qneg x'))) *)
intros x'; case z; simpl in |- *.
(* Focus 1 *)
auto.
(* Focus 2 *)
intros z'; Case' (Qpositive_le_dec z' x').
case (Qpositive_eq_dec z' x').
auto.
auto.
intros H0 H1 H2; apply Qgt_pos_pos.
red in |- *; intros H3; elim (Qpositive_sub_diff z' x'); auto.
apply Qpositive_le_antisym; auto with *.
apply Qpositive_sub_le; auto.
(* Focus 3 *)
intros z'; apply Qgt_neg_neg.
red in |- *; intros H0; elim (Qpositive_plus_diff z' x').
apply Qpositive_le_antisym; auto.
apply Qpositive_plus_le.
Qed.
 
Theorem Qgt_mult :
 forall x y z : Q, Qgt z Zero -> Qgt x y -> Qgt (Qmult z x) (Qmult z y).
intros x y z; case z.
(* Focus 1 *)
intros H; inversion H.

(* Focus 2 *)
case y; case x; auto.
(* 2.1.1 is solved by Auto *)  
(* Focus 2.1.2 z>0 y=0 x>0 *)
simpl in |- *; auto.
(* Focus 2.1.3 z>0 y=0 x<0 *)
intros x' y' H H1; inversion H1.

(* Focus 2.2.1 z>0 y>0 x=0 *)
intros x' y' H H1; inversion H1.
(* Focus 2.2.2  z>0  y>0  x>0 *)
simpl in |- *; intros x' y' z' H H0; apply Qgt_pos_pos.
red in |- *; intros H1.
inversion H0.
elim H4; rewrite <- (Qpositive_mult_One x').
rewrite <- (Qpositive_mult_One y').
rewrite <- (Qpositive_mult_inv z').
repeat rewrite Qpositive_mult_assoc.
repeat rewrite (Qpositive_mult_sym (Qpositive_inv z')).
repeat rewrite <- Qpositive_mult_assoc.
apply Qpositive_le_mult.
auto.
(* Focus 2.2.3 z>0 y>0 x<0 *)
intros x' y' z' H H1; inversion H1.

(* Focus 2.3.1 z>0 y<0 x=0 *)
simpl in |- *; auto.
(* Focus 2.3.2 z>0 y<0 x>0*)
simpl in |- *; auto.
(* Focus 2.3.3 z>0 y<0 x<0 *)
simpl in |- *; intros x' y' z' H H1; apply Qgt_neg_neg.
red in |- *; intros H0; inversion H1.
elim H4; rewrite <- (Qpositive_mult_One y').
rewrite <- (Qpositive_mult_One x').
rewrite <- (Qpositive_mult_inv z').
repeat rewrite Qpositive_mult_assoc.
repeat rewrite (Qpositive_mult_sym (Qpositive_inv z')).
repeat rewrite <- Qpositive_mult_assoc.
apply Qpositive_le_mult.
auto.

(* Focus 3 *)
intros z' H; inversion H.
Qed.
 
Theorem Qpositive_mult_simpl :
 forall w w' w'' : Qpositive,
 Qpositive_mult w w'' = Qpositive_mult w' w'' -> w = w'.
intros w w' w'' H; rewrite <- (Qpositive_mult_One w);
 rewrite <- (Qpositive_mult_One w'); rewrite <- (Qpositive_mult_inv w'').
repeat rewrite Qpositive_mult_assoc;
 repeat rewrite (Qpositive_mult_sym (Qpositive_inv w''));
 repeat rewrite <- Qpositive_mult_assoc.
repeat rewrite (Qpositive_mult_sym w'').
rewrite H; auto.
Qed.
 
Theorem Q_distr_left_aux :
 forall (x y : Q) (z' : Qpositive),
 Qmult (Qplus x y) (Qpos z') = Qplus (Qmult x (Qpos z')) (Qmult y (Qpos z')).
intros x y z'; case y.
(* Focus 1 *) 
repeat rewrite <- (Qplus_sym Zero).
repeat rewrite Qplus_zero_left; auto with *.

(* Focus 2 *)
case x.
(* 2.1 *)
simpl in |- *; auto with *.
(* 2.2 *)
intros x' y'; simpl in |- *.
rewrite Qpositive_mult_distr.
auto.
(* 2.3 *)
intros x' y'; simpl in |- *.
Case' (Qpositive_le_dec x' y').
case (Qpositive_eq_dec x' y').
simpl in |- *.
intros Heq; rewrite Heq.
Case' (Qpositive_le_dec (Qpositive_mult y' z') (Qpositive_mult y' z')).
case (Qpositive_eq_dec (Qpositive_mult y' z') (Qpositive_mult y' z')).
auto.
intros H; elim H; auto.
intros H; elim H; auto.
Case' (Qpositive_le_dec (Qpositive_mult x' z') (Qpositive_mult y' z')).
case (Qpositive_eq_dec (Qpositive_mult x' z') (Qpositive_mult y' z')).
intros e q n q0; elim n.
apply Qpositive_mult_simpl with z'.
auto.
simpl in |- *; intros; rewrite Qpositive_mult_minus_distr; auto with *.
intros H H0 H1 n q; elim H.
apply Qpositive_le_antisym; auto.
apply Qpositive_le_mult; auto with *.
Case' (Qpositive_le_dec (Qpositive_mult x' z') (Qpositive_mult y' z')).
case (Qpositive_eq_dec (Qpositive_mult x' z') (Qpositive_mult y' z')).
intros e q H H0 H1; elim H.
apply Qpositive_mult_simpl with z'; auto.
intros n q H H0 H1; elim H.
apply Qpositive_mult_simpl with z'; apply Qpositive_le_antisym; auto with *.
apply Qpositive_le_mult; auto.
intros H H0 H3 H1 H2 H4.
simpl in |- *.
rewrite Qpositive_mult_minus_distr; auto.

(* Focus 3 *)
intros y'; case x.
(* 3.1 *)
simpl in |- *; repeat rewrite Qplus_zero_left; auto.
(* 3.2 *)
intros x'; simpl in |- *.
Case' (Qpositive_le_dec x' y').
case (Qpositive_eq_dec x' y').
Case' (Qpositive_le_dec (Qpositive_mult x' z') (Qpositive_mult y' z')).
case (Qpositive_eq_dec (Qpositive_mult x' z') (Qpositive_mult y' z')).
auto.
intros n q e q0; elim n; rewrite e; auto.
intros n H0 H1 e q; elim n; rewrite e; auto.
Case' (Qpositive_le_dec (Qpositive_mult x' z') (Qpositive_mult y' z')).
case (Qpositive_eq_dec (Qpositive_mult x' z') (Qpositive_mult y' z')).
intros e q n; elim n; apply Qpositive_mult_simpl with z'; auto.
simpl in |- *.
intros; rewrite Qpositive_mult_minus_distr; auto with *.
intros H H0 H1 n q; elim H1; apply Qpositive_le_mult; auto with *.
Case' (Qpositive_le_dec (Qpositive_mult x' z') (Qpositive_mult y' z')).
case (Qpositive_eq_dec (Qpositive_mult x' z') (Qpositive_mult y' z')).
intros e q n; elim n; apply Qpositive_mult_simpl with z'; auto.
intros n q H H0 H1; elim n.
apply Qpositive_le_antisym; auto.
apply Qpositive_le_mult; auto with *.
simpl in |- *.
intros; rewrite Qpositive_mult_minus_distr; auto.
(* 3.3 *)
intros x'; simpl in |- *; rewrite Qpositive_mult_distr; auto with *.
Qed.
 
Theorem Qmult_zero : forall x : Q, Qmult Zero x = Zero.
intros x; case x; simpl in |- *; auto.
Qed.
 
Theorem Qmult_neg :
 forall (x : Q) (y' : Qpositive),
 Qopp (Qmult x (Qneg y')) = Qmult x (Qpos y').
intros x; case x; auto.
Qed.
 
Theorem Qopp_plus :
 forall x y : Q, Qopp (Qplus x y) = Qplus (Qopp x) (Qopp y).
intros x y.
rewrite <- (Qplus_zero_left (Qplus (Qopp x) (Qopp y))).
rewrite <- (Q_opp_def (Qplus x y)).
rewrite (Qplus_sym (Qplus x y)).
pattern (Qplus x y) at 3 in |- *; rewrite Qplus_sym.
rewrite Qplus_assoc.
rewrite Qplus_assoc.
rewrite <- (fun a b : Q => Qplus_assoc a b (Qopp x)).
rewrite Q_opp_def.
rewrite <- (Qplus_sym Zero); rewrite Qplus_zero_left.
rewrite <- Qplus_assoc; rewrite Q_opp_def.
rewrite <- (Qplus_sym Zero); rewrite Qplus_zero_left.
auto.
Qed.
 
Theorem Q_distr_left :
 forall x y z : Q, Qmult (Qplus x y) z = Qplus (Qmult x z) (Qmult y z).
intros x y z; case z.
(* Focus 1 *)
repeat rewrite <- (Qmult_sym Zero); repeat rewrite Qmult_zero; auto with *.
(* Focus 2 *)
exact (Q_distr_left_aux x y).
(* Focus 3 *)
intros z'.
rewrite <- (Qplus_zero_left (Qmult (Qplus x y) (Qneg z'))).
rewrite <- (Q_opp_def (Qplus (Qmult x (Qneg z')) (Qmult y (Qneg z')))).
rewrite Qopp_plus.
repeat rewrite Qmult_neg.
rewrite <- Q_distr_left_aux.
rewrite <- (Qmult_neg (Qplus x y)).
repeat rewrite <- Qplus_assoc.
rewrite <- (Qplus_sym (Qmult (Qplus x y) (Qneg z'))).
rewrite Q_opp_def.
rewrite <- (Qplus_sym Zero).
rewrite Qplus_zero_left.
auto.
Qed.

Definition Qminus (q1 q2 : Q) : Q := Qplus q1 (Qopp q2).
Definition Qdiv (q1 q2 : Q) : Q := Qmult q1 (Qinv q2).
