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


Require Export quadratic_correctness.
Require Import Eqdep_dec.
Import Field_Theory_Q.


Lemma Qopp_lazy_Qopp : forall x : Q, Qopp_lazy x = Qopp x.
Proof.
 intros x.
 unfold Qopp_lazy in |- *.
 rewrite homography.
 unfold spec_h in |- *.
 replace (Z_to_Q 1) with Qone; trivial.
 replace (Z_to_Q (-1)) with (Qopp Qone); trivial.
 unfold Z_to_Q in |- *.
 rewrite Qmult_Qopp_left.
 rewrite Qmult_zero.
 rewrite Qplus_zero_right.
 rewrite Qplus_zero_left.
 rewrite Qmult_one_right.
 rewrite Qmult_one_left.
 reflexivity.
Defined.


Lemma Qinv_lazy_Qinv :
 forall (x : Q) (Hx : x <> Zero), Qinv_lazy x Hx = Qinv x.
Proof.
 intros x Hx.
 unfold Qinv_lazy in |- *.
 rewrite homography.
 unfold spec_h in |- *.
 replace (Z_to_Q 1) with Qone; trivial.
 unfold Z_to_Q in |- *.
 repeat rewrite Qmult_one_left.
 rewrite Qplus_zero_right.
 reflexivity.
Defined.


Lemma Qplus_lazy_Qplus : forall x y : Q, Qplus_lazy x y = Qplus x y.
Proof.
 intros x y.
 unfold Qplus_lazy in |- *.
 rewrite quadratic.
 unfold spec_q in |- *.
 replace (Z_to_Q 1) with Qone; trivial.
 unfold Z_to_Q in |- *.
 repeat rewrite Qmult_one_left.
 rewrite Qmult_one_right.
 repeat rewrite Qmult_zero.
 rewrite Qplus_zero_left.
 rewrite Qplus_zero_right.
 reflexivity.
Defined.

Lemma Qminus_lazy_Qminus : forall x y : Q, Qminus_lazy x y = Qminus x y.
intros x y.
unfold Qminus_lazy in |- *.
rewrite quadratic in |- *.
unfold spec_q in |- *.
change (Z_to_Q 1) with Qone in |- *.
unfold Z_to_Q in |- *.
simpl Qpositive_c in |- *.
field.
discriminate.
Defined.

Lemma Qmult_lazy_Qmult : forall x y : Q, Qmult_lazy x y = Qmult x y.
Proof.
 intros x y.
 unfold Qmult_lazy in |- *.
 rewrite quadratic.
 unfold spec_q in |- *.
 change (Z_to_Q 1) with Qone.
 unfold Z_to_Q in |- *.
 rewrite Qmult_one_left.
 rewrite Qmult_one_right.
 repeat rewrite Qmult_zero.
 repeat rewrite Qplus_zero_right.
 repeat rewrite Qplus_zero_left.
 reflexivity.
Defined.

Lemma Qdiv_lazy_Qdiv :
  forall (x y : Q) (Hy : y <> Zero), Qdiv_lazy x y Hy = Qdiv x y.
intros x y Hy.
unfold Qdiv_lazy in |- *.
rewrite quadratic in |- *.
unfold spec_q in |- *.
change (Z_to_Q 1) with Qone in |- *.
unfold Z_to_Q in |- *.
field.
trivial.
Defined.

Lemma second_Q_Ring_Theory :
 ring_theory Zero Qone Qplus_lazy Qmult_lazy Qminus_lazy Qopp_lazy (eq(A:=Q)).
  split; intros n m p || intros n m || intros n;
  repeat rewrite Qplus_lazy_Qplus;
  repeat rewrite Qmult_lazy_Qmult;
  repeat rewrite Qminus_lazy_Qminus;
  repeat rewrite Qdiv_lazy_Qdiv;
  repeat rewrite Qopp_lazy_Qopp;
  repeat rewrite Qinv_lazy_Qinv;
 try first
      [ apply Qplus_sym
      | apply Qplus_assoc
      | apply Qmult_sym
      | apply Qmult_assoc
      | apply Qplus_zero_left
      | apply Qmult_one_left
      | apply Q_opp_def
      | apply Q_distr_left
      | reflexivity ].
Defined.

(** If we want to use the Field tactic , the multiplicative inverse
should be total. We make our [Qinv_lazy] a total function by
outputting a dummy variable (Zero) whenever the denominator is
zero. Note that we can not do this in the case of real numbers (being
Zero is undecidable) but for rational numbers there is no problem *)
Definition total_Qinv_lazy (x : Q) :=
  match Q_zerop x with
  | left _ => Zero
  | right h => Qinv_lazy x h
  end.

Lemma Qinv_lazy_defT :
 forall (n : Q) (Hn : n <> Zero), Qmult_lazy (Qinv_lazy n Hn) n = Qone.
Proof.
 intros n Hn; rewrite Qinv_lazy_Qinv; rewrite Qmult_lazy_Qmult; 
  rewrite Qmult_sym; apply Qinv_def; intro; apply Hn; 
  assumption.
Defined.

Lemma total_Qinv_lazy_defT :
 forall n : Q, n <> Zero -> Qmult_lazy (total_Qinv_lazy n) n = Qone.
Proof.
 intros n Hn.
 unfold total_Qinv_lazy in |- *; case (Q_zerop n); intros Hn';
  [ Falsum
  | apply Qinv_lazy_defT ].
Defined.

Definition total_Qdiv_lazy (x y : Q) :=
  match Q_zerop y with
  | left _ => Zero
  | right h => Qdiv_lazy x y h
  end.


Lemma second_QField :
  field_theory Zero Qone Qplus_lazy Qmult_lazy Qminus_lazy
    Qopp_lazy total_Qdiv_lazy total_Qinv_lazy (eq(A:=Q)).
constructor.
 apply second_Q_Ring_Theory.
 discriminate.
 intros; unfold total_Qdiv_lazy, total_Qinv_lazy in |- *.
  destruct (Q_zerop q).
   rewrite Qmult_lazy_Qmult in |- *.
   ring.
   rewrite Qdiv_lazy_Qdiv in |- *; rewrite Qmult_lazy_Qmult in |- *;
     rewrite Qinv_lazy_Qinv in |- *; reflexivity.
 exact total_Qinv_lazy_defT.
Defined.

Add Field second_Qfield : second_QField
  (decidable Q_eq_prop, constants [Qcst]).

Definition not_eq2eqT (A : Set) (x y : A) (H1 : x <> y) : 
  x <> y := fun H2 : x = y => H1 H2.
