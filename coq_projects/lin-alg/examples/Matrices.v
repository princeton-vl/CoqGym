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


(** %\subsection*{ examples :  Matrices.v }%*)
(** - Some preliminary notions about matrices *)
Set Automatic Coercions Import.
Set Implicit Arguments.
Unset Strict Implicit.
Require Export Map2.
Require Export vecspace_Fn.

Definition Matrix_general_type (A : Setoid) (n m : Nat) :=
  MAP2 (fin n) (fin m) A.

Definition matrix (F : field) := Matrix_general_type F.

Section add.
Let matrix_addition_fun (F : field) (m n : Nat) (M N : matrix F m n) :
  matrix F m n.
intros.
apply (Build_Map2 (Ap2:=fun i j => M i j +' N i j)).
red in |- *.
intros.
apply SGROUP_comp; auto with algebra.
apply (Ap2_comp_proof M); auto with algebra.
apply (Ap2_comp_proof N); auto with algebra.
Defined.

Definition matrix_addition (F : field) (m n : Nat) :
  MAP2 (matrix F m n) (matrix F m n) (matrix F m n).
intros.
apply (Build_Map2 (Ap2:=matrix_addition_fun (F:=F) (m:=m) (n:=n))).
red in |- *.
simpl in |- *; intros.
apply SGROUP_comp; auto with algebra.
Defined.
End add.

Section mult.
Definition matrix_scmult_fun (F : field) (m n : Nat) 
  (c : F) (M : matrix F m n) : matrix F m n.
intros.
apply (Build_Map2 (Ap2:=fun i j => c rX M i j)).
red in |- *.
intros.
apply RING_comp; auto with algebra.
apply (Ap2_comp_proof M); auto with algebra.
Defined.

Definition matrix_scmult (F : field) (m n : Nat) :
  MAP2 F (matrix F m n) (matrix F m n).
intros.
apply (Build_Map2 (Ap2:=matrix_scmult_fun (F:=F) (m:=m) (n:=n))).
red in |- *.
simpl in |- *; intros.
apply RING_comp; auto with algebra.
Defined.
End mult.

Section transpose.
Definition transpose :
  forall (F : field) (m n : Nat), matrix F m n -> matrix F n m.
intros.
red in |- *.
red in |- *.
red in X; red in X.
destruct X.
apply (Build_Map2 (Ap2:=fun i j => Ap2 j i)); auto with algebra.
red in Ap2_comp_proof; red in |- *.
intros.
auto with algebra.
Defined.

Definition transpose_map :
  forall (F : field) (m n : Nat), MAP (matrix F m n) (matrix F n m).
intros.
apply (Build_Map (Ap:=transpose (F:=F) (m:=m) (n:=n))).
red in |- *.
unfold transpose in |- *.
intros; destruct x; destruct y.
simpl in |- *.
auto with algebra.
Defined.

Lemma transpose_defprop :
 forall (F : field) (m n : Nat) (M : matrix F m n) (i : fin n) (j : fin m),
 transpose M i j =' M j i in _.
intros.
unfold transpose in |- *; destruct M; simpl in |- *.
apply Refl.
Qed.
End transpose.
Hint Resolve transpose_defprop: algebra.

Definition zero_matrix : forall (F : field) (n m : Nat), matrix F n m.
intros.
apply (Build_Map2 (Ap2:=fun (i : fin n) (j : fin m) => zero F)).
red in |- *.
auto with algebra.
Defined.

Definition is_square (F : field) (n m : Nat) (M : matrix F n m) :=
  n =' m in _.

Definition is_diagonal (F : field) (n : Nat) (M : matrix F n n) :=
  forall i j : fin n, index i <> index j -> M i j =' (zero F) in _.

Definition identity_matrix : forall (F : field) (n : Nat), matrix F n n.
intros.
apply
 (Build_Map2
    (Ap2:=fun i j : fin n => Kronecker one (zero F) (index i) (index j))).
red in |- *.
unfold Kronecker in |- *.
intros; destruct x; destruct x'; destruct y; destruct y'.
simpl in |- *.
simpl in H, H0.
rewrite H.
rewrite H0.
auto with algebra.
Defined.

Lemma id_is_square :
 forall (F : field) (n : Nat), is_square (identity_matrix F n).
red in |- *.
simpl in |- *.
auto.
Qed.

Definition row (F : field) :
  forall m n : Nat, matrix F m n -> fin m -> Fn F n :=
  fun n m M i => Ap2_Map M i.

Definition col (F : field) :
  forall m n : Nat, matrix F m n -> fin n -> Fn F m :=
  fun n m M j => Ap2_Map' M j.

Lemma row_transpose_col :
 forall (F : field) (m n : Nat) (M : matrix F m n) (i : fin m),
 row M i =' col (transpose M) i in _.
intros; simpl in |- *.
red in |- *; simpl in |- *.
intros; (apply Sym; auto with algebra).
Qed.

Lemma row_comp :
 forall (F : field) (m n : Nat) (M M' : matrix F m n) (i i' : fin m),
 M =' M' in _ -> i =' i' in _ -> row M i =' row M' i' in _.
intros.
simpl in |- *.
red in |- *; simpl in |- *.
intros.
destruct M; destruct M'; simpl in |- *.
simpl in H.
apply Trans with (Ap2 i' x); auto with algebra.
Qed.

Lemma col_comp :
 forall (F : field) (m n : Nat) (M M' : matrix F m n) (i i' : fin n),
 M =' M' in _ -> i =' i' in _ -> col M i =' col M' i' in _.
intros.
simpl in |- *.
red in |- *; simpl in |- *.
intros.
destruct M; destruct M'; simpl in |- *.
simpl in H.
apply Trans with (Ap2 x i'); auto with algebra.
Qed.

Hint Resolve row_comp col_comp: algebra.