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


(** %\subsection*{ examples :  Matrix\_multiplication.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export vecspace_Mmn.
Require Export pointwise.
Require Export sums.

(** - Remember that (Fn F n) is the vectorspace $F^n$, based on the setoid (seq n F),
 and (Mmn F m n) is the vectorspace $M_{mn}$ of $m\times n$-matrices over $F$; based 
 on the setoid (matrix F m n) *)

Section matrix_x_vector.
Definition mat_vec_mult_fun :
  forall (F : field) (m n : Nat), Mmn F m n -> Fn F n -> Fn F m.
intros.
simpl in X, X0.
simpl in |- *.
apply
 (Build_Map
    (Ap:=fun i : fin m =>
         sum (pointwise (uncurry (RING_comp (R:=F))) (Ap2_Map X i) X0))).
red in |- *; simpl in |- *.
intros.
apply sum_comp; auto with algebra;
 (apply toMap; apply pointwise_comp; auto with algebra).
simpl in |- *.
red in |- *; simpl in |- *.
intro; destruct X; simpl in |- *; auto with algebra.
Defined.

Definition matXvec :
  forall (F : field) (m n : Nat), Map2 (Mmn F m n) (Fn F n) (Fn F m).
intros; apply (Build_Map2 (Ap2:=mat_vec_mult_fun (F:=F) (m:=m) (n:=n))).
red in |- *; simpl in |- *; red in |- *; simpl in |- *.
intros.
apply sum_comp; auto with algebra;
 (apply toMap; apply pointwise_comp; auto with algebra).
simpl in |- *.
red in |- *; simpl in |- *.
intro; (apply H; auto with algebra).
Defined.
End matrix_x_vector.

Section matrix_x_matrix.
Definition mat_mat_mult_fun :
  forall (F : field) (m n p : Nat), Mmn F m n -> Mmn F n p -> Mmn F m p.
intros F m n p M N.
apply
 (Build_Map2
    (Ap2:=fun i j =>
          sum (pointwise (uncurry (RING_comp (R:=F))) (row M i) (col N j)))).
red in |- *; simpl in |- *.
intros.
apply sum_comp; auto with algebra.
apply toMap; apply pointwise_comp; auto with algebra.
change (row M x =' row M x' in _) in |- *.
apply row_comp; auto with algebra.
change (col N y =' col N y' in _) in |- *.
apply col_comp; auto with algebra.
Defined.

Definition matXmat :
  forall (F : field) (m n p : Nat), Map2 (Mmn F m n) (Mmn F n p) (Mmn F m p).
intros;
 apply (Build_Map2 (Ap2:=mat_mat_mult_fun (F:=F) (m:=m) (n:=n) (p:=p))).
red in |- *; simpl in |- *.
intros.
apply sum_comp; auto with algebra;
 (apply toMap; apply pointwise_comp; auto with algebra).
change (row x i =' row x' i' in _) in |- *.
apply row_comp; auto with algebra.
change (col y j =' col y' j' in _) in |- *.
apply col_comp; auto with algebra.
Defined.
End matrix_x_matrix.

Section facts.
Variable F : field.
Variable n m p : Nat.
Variable M : Mmn F m n.
Variable N : Mmn F n p.
Lemma matXmat_col :
 forall i : fin p,
 col (matXmat _ _ _ _ M N) i =' matXvec _ _ _ M (col N i) in _.
intros.
unfold col, matXmat, matXvec in |- *.
simpl in |- *.
red in |- *; simpl in |- *.
intros.
apply sum_comp; auto with algebra.
Qed.
End facts.

Section morefacts.
From Algebra Require Export Cfield_facts.
Variable F : cfield.
Variable n m p : Nat.
Variable M : Mmn F m n.
Variable N : Mmn F n p.
Lemma matXmat_row :
 forall i : fin m,
 row (matXmat _ _ _ _ M N) i =' matXvec _ _ _ (transpose N) (row M i) in _.
intros.
unfold transpose, row, matXmat, matXvec in |- *.
simpl in |- *.
destruct N.
red in |- *; simpl in |- *.
unfold row, col in |- *.
intros.
apply sum_comp; auto with algebra.
simpl in |- *.
red in |- *; simpl in |- *.
auto with algebra.
Qed.
End morefacts.
(* Note that one needs the fact that F is a *commutative* field *)
