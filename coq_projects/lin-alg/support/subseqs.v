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


(** %\subsection*{ support :  subseqs.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export conshdtl.

(** - subsequences, inductively defined *)
Section defs.
Variable A : Setoid.

Inductive is_subseq :
forall (m : Nat) (w : seq m A) (n : Nat) (v : seq n A), Prop :=
  | is_subseq_empty :
      forall (n : Nat) (v : seq n A) (w : seq 0 A), is_subseq w v
  | is_subseq_of_tail :
      forall (m : Nat) (w : seq m A) (n : Nat) (v : seq n A),
      is_subseq w v -> forall a : A, is_subseq w (a;; v)
  | is_subseq_cons :
      forall (m : Nat) (w : seq m A) (n : Nat) (v : seq n A),
      is_subseq w v -> forall a : A, is_subseq (a;; w) (a;; v)
  | is_subseq_comp :
      forall (m : Nat) (w w' : seq m A) (n : Nat) (v v' : seq n A),
      is_subseq w' v' -> w =' w' in _ -> v =' v' in _ -> is_subseq w v.

Lemma subseq_has_right_elements :
 forall (m : Nat) (w : seq m A) (n : Nat) (v : seq n A),
 is_subseq w v -> forall i : fin m, exists i' : fin n, w i =' v i' in _.
intros.
induction H.
apply False_ind; auto with algebra.
case (IHis_subseq i).
intros.
destruct x.
exists (Build_finiteT (lt_n_S _ _ in_range_prf)).
apply Trans with (v (Build_finiteT in_range_prf)); auto with algebra.
destruct i; destruct index as [| n0].
exists (Build_finiteT (lt_O_Sn n)).
auto with algebra.
generalize (IHis_subseq (Build_finiteT (lt_S_n _ _ in_range_prf))); intro.
inversion_clear H0.
destruct x.
exists (Build_finiteT (lt_n_S _ _ in_range_prf0)).
apply Trans with (v (Build_finiteT in_range_prf0)); auto with algebra.
generalize (IHis_subseq i).
intros.
inversion_clear H2.
exists x.
apply Trans with (w' i); auto with algebra.
apply Trans with (v' x); auto with algebra.
Qed.

Lemma subseqs_are_not_longer :
 forall (m n : Nat) (w : seq m A) (v : seq n A), is_subseq w v -> m <= n.
intros.
induction H; simpl in |- *; auto with algebra arith.
Qed.
End defs.
