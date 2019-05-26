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


(** %\subsection*{ support :  seq\_set\_facts.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export concat_facts.
From Algebra Require Export Union.
From Algebra Require Export Singleton.
Require Export Classical_Prop.

Section MAIN.

Variable A : Setoid.
Variable n : Nat.


Lemma seq_set_conseq_union :
 forall (v : seq n A) (a : A),
 seq_set (a;; v) =' union (seq_set v) (single a) in _.
intros.
simpl in |- *.
red in |- *.
split; intros.
simpl in H.
inversion_clear H.
destruct x0.
destruct index as [| n0].
simpl in |- *.
right; auto.
simpl in |- *.
left.
exists (Build_finiteT (lt_S_n n0 _ in_range_prf)).
auto.
simpl in H.
inversion_clear H.
inversion_clear H0.
simpl in |- *.
destruct x0.
exists (Build_finiteT (lt_n_S _ _ in_range_prf)).
apply Trans with (v (Build_finiteT in_range_prf)); auto with algebra.
simpl in |- *.
exists (Build_finiteT (lt_O_Sn n)).
auto.
Qed.

Lemma seq_set_concat_union :
 forall (m : Nat) (v : seq n A) (w : seq m A),
 seq_set (v ++ w) =' union (seq_set v) (seq_set w) in _.
simpl in |- *.
red in |- *.
intros.
split; intros.
simpl in |- *.
simpl in H.
inversion_clear H.
destruct x0.
case (classic (index < n)).
intro.
left.
exists (Build_finiteT H).
apply Trans with ((v ++ w) (Build_finiteT in_range_prf)); auto with algebra.
right.
assert (exists i : Nat, index = i + n).
clear H0 x w v A.
induction  m as [| m Hrecm].
assert (n + 0 = n); auto with arith.
rewrite H0 in in_range_prf.
absurd (index < n); auto.
assert (index < n + m \/ index = n + m).
apply le_lt_or_eq; auto with algebra.
assert (n + S m = S (n + m)); auto with arith.
rewrite H0 in in_range_prf.
auto with arith.
inversion_clear H0.
apply Hrecm; auto with algebra.
exists m.
apply trans_eq with (n + m); auto with arith.
inversion_clear H1.
assert (x0 < m).
apply plus_lt_reg_l with n.
replace (n + x0) with index.
auto.
transitivity (x0 + n); auto with arith.
exists (Build_finiteT H1).
generalize concat_second_part; intro p.
assert (irp' : n + x0 < n + m).
replace (n + x0) with (x0 + n); auto with arith.
rewrite <- H2; auto.
apply Trans with ((v ++ w) (Build_finiteT irp')); auto with algebra.
apply Trans with ((v ++ w) (Build_finiteT in_range_prf)); auto with algebra.
apply Ap_comp; auto with algebra.
simpl in |- *.
transitivity (x0 + n); auto with arith.

simpl in |- *.
simpl in H.
inversion_clear H.
inversion_clear H0.
destruct x0.
exists (Build_finiteT (lt_plus_trans _ _ m in_range_prf)).
apply Trans with (v (Build_finiteT in_range_prf)); auto with algebra.
inversion_clear H0.
destruct x0.
assert (n + index < n + m).
auto with arith.
exists (Build_finiteT H0).
apply Trans with (w (Build_finiteT in_range_prf)); auto with algebra.
Qed.

Lemma seq_set_head_or_tail :
 forall (v : seq (S n) A) (a : A),
 in_part a (seq_set v) -> ~ a =' head v in _ -> in_part a (seq_set (Seqtl v)).
intros.
simpl in H.
inversion_clear H.
destruct x.
destruct index as [| n0].
absurd (a =' head v in _); auto with algebra.
unfold head in |- *;
 (apply Trans with (v (Build_finiteT in_range_prf)); auto with algebra).
simpl in |- *.
exists (Build_finiteT (lt_S_n _ _ in_range_prf)).
apply Trans with (v (Build_finiteT in_range_prf)); auto with algebra.
Qed.

Lemma has_index :
 forall (v : seq n A) (a : seq_set v),
 exists i : fin n, seq_set v a =' v i in A.
intros.
elim a.
intros.
rename subtype_elt into a'.
rename subtype_prf into Ha'.
simpl in Ha'.
inversion_clear Ha'.
exists x.
simpl in |- *.
auto.
Qed.


End MAIN.
Hint Resolve seq_set_conseq_union seq_set_head_or_tail: algebra.
Hint Resolve has_index: algebra.
