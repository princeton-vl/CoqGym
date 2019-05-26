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


(** %\subsection*{ examples :  antisymmetric\_matrices.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export vecspace_Mmn.
Require Export subspaces.

Definition is_antisymmetric (F : field) (n : Nat) (M : Mmn F n n) :=
  forall i j : fin n, M i j =' (min M j i) in _.

Definition is_antisymmetric_pred :
  forall (F : field) (n : Nat), Predicate (Mmn F n n).
intros; apply (Build_Predicate (Pred_fun:=is_antisymmetric (F:=F) (n:=n))).
red in |- *; simpl in |- *.
intros.
red in |- *; red in H.
intros.
apply Trans with (x i j); auto with algebra.
apply Trans with (min x j i); auto with algebra.
apply GROUP_comp; auto with algebra.
apply Sym; auto with algebra.
Defined.

Lemma antisymm_matr_subspace :
 forall (n : Nat) (F : field), is_subspace (is_antisymmetric_pred F n).
red in |- *; intros.
split; try split; simpl in |- *.
red in |- *.
simpl in |- *.
auto with algebra.
intros.
red in H0, H.
destruct x; destruct y.
simpl in H0, H.
red in |- *; simpl in |- *.
intros.
apply Trans with ((min Ap2 j i) +' (min Ap0 j i)); auto with algebra.
apply Trans with ((min Ap0 j i) +' (min Ap2 j i)); auto with algebra.
intros; destruct x; red in H; red in |- *; simpl in H; simpl in |- *.
intros.
apply Trans with (c rX (min Ap2 j i)); auto with algebra.
Qed.

Definition antisym_subspace n F :=
  alt_Build_subspace (antisymm_matr_subspace n F).