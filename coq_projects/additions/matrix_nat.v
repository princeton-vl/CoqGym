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


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(* ---                        matrix.v                                  --- *)
(*                                                                          *)
(* Author: Pierre Casteran.                                                 *)
(*    LABRI, URA CNRS 1304,                                                 *)
(*    Departement d'Informatique, Universite Bordeaux I,                    *)
(*    33405 Talence CEDEX,                                                  *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                                 *)

(*          2-2 matrices with natural coefficients                          *)

(* original version using nat instead of Z                                  *)

Require Import monoid.
Require Import Arith.
Require Import Compare_dec.
Require Import fmpc.

Record Mat2 : Set := mat2 {M11 : nat; M12 : nat; M21 : nat; M22 : nat}.

Definition Id2 := mat2 1 0 0 1.

Definition Mat_mult (M M' : Mat2) :=
  mat2 (M11 M * M11 M' + M12 M * M21 M') (M11 M * M12 M' + M12 M * M22 M')
    (M21 M * M11 M' + M22 M * M21 M') (M21 M * M12 M' + M22 M * M22 M').

Axiom
  Mat_assoc :
    forall M M' M'' : Mat2,
    Mat_mult M (Mat_mult M' M'') = Mat_mult (Mat_mult M M') M''.


Lemma matrix : monoid Mat2.
 refine (mkmonoid Mat2 Id2 Mat_mult _ _ _).
 exact Mat_assoc.
 simple induction a.
  intros M13 M14 M23 M24.
  unfold Id2, Mat_mult in |- *; simpl in |- *.
  repeat rewrite plus_0_r.
  case M13; case M14; case M23; case M24; auto.
  simple induction a.
  intros.
  unfold Id2, Mat_mult in |- *; simpl in |- *.
  repeat rewrite mult_0_r.
  repeat rewrite mult_1_r.
  simpl in |- *; repeat rewrite plus_0_r.
  auto.
Defined.

(* Fibonacci numbers *)

(* definition *)

Fixpoint Fib (n : nat) : nat :=
  match n return nat with
  | O => (* O *)  1
      (* (S p ) *)
  | S p =>
      match p return nat with
      | O => (* O *)  1
          (* S q *)
      | S q => Fib q + Fib p
      end
  end.

Lemma Unfold_FibO : Fib 0 = 1.
Proof.
 unfold Fib in |- *; simpl in |- *; auto with arith.
Qed.

Lemma Unfold_Fib1 : Fib 1 = 1.
Proof.
 unfold Fib in |- *; simpl in |- *; auto with arith.
Qed.

Lemma Unfold_FibSSn : forall n : nat, Fib (S (S n)) = Fib (S n) + Fib n.
Proof.
 intro n; unfold Fib at 1 in |- *.
 simpl in |- *; auto with arith.
Qed.

(* A "Decaled" Fibonnacci function *)

Definition shift_Fib (n : nat) :=
  match n return nat with
  | O => 0
  | S p => Fib p
  end.

Lemma Unfold_shift_Fib : forall n : nat, shift_Fib (S n) = Fib n.
Proof.
 intro n; unfold shift_Fib in |- *; auto with arith.
Qed.

Lemma Simpl_shift_Fib :
 forall n : nat, shift_Fib (S (S n)) = shift_Fib (S n) + shift_Fib n.
Proof.
 simple induction n.
 unfold shift_Fib, Fib in |- *; simpl in |- *; auto with arith.
 intros.
 unfold shift_Fib in |- *.
 rewrite Unfold_FibSSn; auto with arith.
Qed.


Definition fib_mat := mat2 1 1 1 0.


Lemma fib_mat_n :
 forall (n : nat) (a b d : nat),
 power Mat2 matrix fib_mat n = mat2 a b b d ->
 power Mat2 matrix fib_mat (S n) = mat2 (a + b) (b + d) a b.
Proof.
 intros; simpl in |- *.
 rewrite H.
 unfold Mat_mult in |- *.
 simpl in |- *.
 repeat rewrite plus_0_r.
 case a; case b; case d; auto.
Qed.

Lemma fib_n :
 forall n : nat,
 power Mat2 matrix fib_mat (S n) =
 mat2 (shift_Fib (S (S n))) (shift_Fib (S n))
   (shift_Fib (S n)) (shift_Fib n).
Proof.
 simple induction n.
 unfold power, shift_Fib, o, u in |- *; simpl in |- *.
 unfold fib_mat in |- *; simpl in |- *.
 unfold Mat_mult, Id2 in |- *; simpl in |- *; auto with arith.
 intros.
 rewrite (fib_mat_n (S n0) _ _ _ H).
 rewrite (Simpl_shift_Fib (S n0)).
 pattern (shift_Fib (S (S n0))) at 4 in |- *.
 rewrite (Simpl_shift_Fib n0).
 auto with arith.
Qed.


Lemma fib_computation :
 forall n : nat,
 0 < n -> Fib n = M11 (power Mat2 matrix fib_mat n).
Proof.
 simple induction n.
 intro; absurd (0 < 0); auto with arith.
 intros.
 rewrite fib_n; unfold M11 in |- *; auto with arith.
Qed.
