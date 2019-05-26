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


(** %\subsection*{ examples :  up\_lo\_triang\_mat.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export vecspace_Mmn.
Require Export subspaces.
 
(** - Upper, lower and diagonal matrices. Note that whereas the triangular matrices may
 be generally $m\times n$, diagonal matrices must be $n\times n$. *)

Definition is_up_triang (F : field) (m n : Nat) (M : matrix F m n) :=
  forall (i : fin m) (j : fin n), index j < index i -> M i j =' (zero F) in _.

Definition is_lo_triang (F : field) (m n : Nat) (M : matrix F m n) :=
  forall (i : fin m) (j : fin n), index i < index j -> M i j =' (zero F) in _.

Definition is_upper_triangular_pred :
  forall (F : field) (m n : Nat), Predicate (Mmn F m n).
intros.
apply (Build_Predicate (Pred_fun:=is_up_triang (F:=F) (m:=m) (n:=n))).
red in |- *; simpl in |- *; red in |- *.
intros.
red in H.
apply Trans with (x i j); auto with algebra.
Defined.

Definition is_lower_triangular_pred :
  forall (F : field) (m n : Nat), Predicate (Mmn F m n).
intros.
apply (Build_Predicate (Pred_fun:=is_lo_triang (F:=F) (m:=m) (n:=n))).
red in |- *; simpl in |- *; red in |- *.
intros.
red in H.
apply Trans with (x i j); auto with algebra.
Defined.

Definition is_diagonal_pred :
  forall (F : field) (n : Nat), Predicate (Mmn F n n).
intros.
apply (Build_Predicate (Pred_fun:=is_diagonal (F:=F) (n:=n))).
red in |- *; simpl in |- *; red in |- *.
intros.
red in H.
apply Trans with (x i j); auto with algebra.
Defined.

Section trivial_lemmas.
Lemma id_is_diagonal :
 forall (F : field) (n : Nat), is_diagonal (identity_matrix F n).
simpl in |- *.
red in |- *.
simpl in |- *.
intros; destruct i; destruct j.
simpl in |- *; simpl in H.
apply Kronecker_case_unequal; auto with algebra.
Qed.

Lemma is_upper_and_lower_then_diagonal :
 forall (F : field) (n : Nat) (M : matrix F n n),
 is_up_triang M -> is_lo_triang M -> is_diagonal M.
intros; red in H, H0.
red in |- *.
intros.
case (nat_total_order _ _ H1); intro; auto with algebra.
Qed.
End trivial_lemmas.

Lemma up_triang_subspace :
 forall (F : field) (m n : Nat), is_subspace (is_upper_triangular_pred F m n).
intros.
red in |- *.
split; try split.
simpl in |- *.
red in |- *.
intros; simpl in |- *.
auto with algebra.
intros.
red in H0, H.
simpl in |- *; red in |- *.
intros.
apply Trans with (x i j +' y i j); auto with algebra.
apply Trans with ((zero F) +' (zero F)); auto with algebra.
intros; simpl in H; red in H; simpl in |- *; red in |- *.
intros; (apply Trans with (c rX (zero F)); auto with algebra).
simpl in |- *.
apply RING_comp; auto with algebra.
Qed.

Lemma lo_triang_subspace :
 forall (F : field) (m n : Nat), is_subspace (is_lower_triangular_pred F m n).
intros.
red in |- *.
split; try split.
simpl in |- *.
red in |- *.
intros; simpl in |- *.
auto with algebra.
intros.
red in H0, H.
simpl in |- *; red in |- *.
intros.
apply Trans with (x i j +' y i j); auto with algebra.
apply Trans with ((zero F) +' (zero F)); auto with algebra.
intros; simpl in H; red in H; simpl in |- *; red in |- *.
intros; (apply Trans with (c rX (zero F)); auto with algebra).
simpl in |- *.
apply RING_comp; auto with algebra.
Qed.

Lemma is_diagonal_subspace :
 forall (F : field) (n : Nat), is_subspace (is_diagonal_pred F n).
intros.
red in |- *.
split; try split.
simpl in |- *.
red in |- *.
intros; simpl in |- *.
auto with algebra.
intros.
red in H0, H.
simpl in |- *; red in |- *.
intros.
apply Trans with (x i j +' y i j); auto with algebra.
apply Trans with ((zero F) +' (zero F)); auto with algebra.
intros; simpl in H; red in H; simpl in |- *; red in |- *.
intros; (apply Trans with (c rX (zero F)); auto with algebra).
simpl in |- *.
apply RING_comp; auto with algebra.
Qed.