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


(** %\subsection*{ support :  seq\_equality\_facts.v }%*)
Set Implicit Arguments.
Unset Strict Implicit. 
Require Export seq_equality.
Require Export concat_facts.
Require Export omit.
Require Export Classical_Prop.

(** - Some useful lemmas concerning seq_equal *)

Lemma seq_equal_length_equal :
 forall (A : Setoid) (n m : Nat) (v : seq n A) (w : seq m A),
 seq_equal v w -> n =' m in _.
intros.
red in H.
apply NNPP; intro.
assert (n < m \/ m < n).
apply nat_total_order; auto with algebra.
inversion_clear H1.
generalize (H n); clear H; intro.
inversion_clear H.
inversion_clear H1.
apply (lt_irrefl n); auto with algebra.
inversion_clear H1.
apply (lt_not_le n m); auto with algebra.
generalize (H m); clear H; intro.
inversion_clear H.
inversion_clear H1.
inversion_clear H.
apply (lt_irrefl m); auto with algebra.
inversion_clear H1.
apply (le_not_lt n m); auto with algebra.
Qed.

Hint Resolve seq_equal_length_equal: algebra.

Lemma seq_equal_equal_elements :
 forall (A : Setoid) (n m : Nat) (v : seq n A) (w : seq m A),
 seq_equal v w ->
 forall (i : fin n) (j : fin m), index i = index j -> v i =' w j in _.
intros.
red in H.
destruct i.
rename index into i.
destruct j.
rename index into j.
simpl in H0.
case (H i); clear H; intros.
inversion_clear H.
inversion_clear H1.
apply Trans with (v (Build_finiteT x)); auto with algebra.
apply Trans with (w (Build_finiteT x0)); auto with algebra.
inversion_clear H.
apply False_ind.
apply (le_not_lt n i); auto with algebra.
Qed.

Hint Resolve seq_equal_equal_elements: algebra.


(** - The interplay with other operations *)
Lemma seq_equal_head :
 forall (A : Setoid) (n m : Nat) (v : seq (S n) A) (w : seq (S m) A),
 seq_equal v w -> head v =' head w in _.
intros.
red in H.
case (H 0); clear H; intros.
inversion_clear H; inversion_clear H0.
apply Trans with (v (Build_finiteT x)); auto with algebra.
apply Trans with (w (Build_finiteT x0)); auto with algebra.
inversion_clear H; inversion_clear H0.
Qed.

Hint Resolve seq_equal_head: algebra.

Lemma seq_equal_seqtl :
 forall (A : Setoid) (n m : Nat) (v : seq n A) (w : seq m A),
 seq_equal v w -> seq_equal (Seqtl v) (Seqtl w).
intros.
destruct n.
red in |- *.
intro.
right.
split; simpl in |- *; auto with arith.
assert (0 = m).
apply seq_equal_length_equal with A v w; auto with algebra.
rewrite <- H0.
simpl in |- *; auto with arith.
destruct m as [| n0].
assert (S n = 0).
apply seq_equal_length_equal with A v w; auto with algebra.
inversion_clear H0.
red in H.
red in |- *.
simpl in |- *.
intro; case (H (S i)); clear H; intros.
inversion_clear H; inversion_clear H0.
left.
exists (lt_S_n _ _ x).
exists (lt_S_n _ _ x0).
apply Trans with (v (Build_finiteT x)); auto with algebra.
apply Trans with (w (Build_finiteT x0)); auto with algebra.
right.
inversion_clear H.
split; auto with arith.
Qed.

Hint Resolve seq_equal_seqtl: algebra.

Lemma seq_equal_cons :
 forall (A : Setoid) (n m : Nat) (v : seq n A) (w : seq m A) (a b : A),
 seq_equal v w -> a =' b in _ -> seq_equal (a;; v) (b;; w).
intros.
assert (n =' m in _).
apply (seq_equal_length_equal (v:=v) (w:=w)); auto with algebra.
red in |- *.
intro.
destruct i as [| n0].
left.
exists (lt_O_Sn n).
exists (lt_O_Sn m).
simpl in |- *.
auto.
case (le_or_lt (S n) (S n0)).
intro.
right.
split; auto.
rewrite <- H1.
auto.
left.
exists H2.
assert (S n0 < S m).
rewrite <- H1.
auto.
exists H3.
simpl in |- *.
apply seq_equal_equal_elements; auto with algebra.
Qed.

Hint Resolve seq_equal_cons: algebra.

Lemma seq_equal_concat :
 forall (A : Setoid) (n m p q : Nat) (v : seq n A) 
   (w : seq m A) (a : seq p A) (b : seq q A),
 seq_equal v w -> seq_equal a b -> seq_equal (v ++ a) (w ++ b).
intros.
generalize (seq_equal_length_equal H).
generalize (seq_equal_length_equal H0).
intros.
red in |- *.
intro.
generalize (le_or_lt (n + p) i).
intro.
case H3.
right.
split; try tauto.
rewrite <- H1.
rewrite <- H2.
tauto.
intro.
left.
exists H4.
assert (i < m + q).
rewrite <- H1.
rewrite <- H2.
tauto.
exists H5.
generalize (le_or_lt n i).
intro.
case H6; clear H6; intro.
2: assert (i < m).
2: rewrite <- H2.
2: auto.
2: apply Trans with (v (Build_finiteT H6)); auto with algebra.
2: apply Trans with (w (Build_finiteT H7)); auto with algebra.
assert (exists k : Nat, i =' n + k in _).
exists (i - n).
simpl in |- *; symmetry  in |- *.
auto with arith.
inversion_clear H7.
assert (n + x < n + p).
rewrite <- H8.
auto.
assert (m + x < m + q).
rewrite <- H2.
rewrite <- H1.
auto.
apply Trans with ((v ++ a) (Build_finiteT H7)); auto with algebra.
apply Trans with ((w ++ b) (Build_finiteT H9)).
2: apply Ap_comp; auto with algebra.
2: simpl in |- *.
2: symmetry  in |- *.
2: rewrite <- H2.
2: auto.
assert (x < p).
apply plus_lt_reg_l with n; auto with algebra.
apply Trans with (a (Build_finiteT H10)); auto with algebra.
assert (x < q).
rewrite <- H1.
auto.
apply Trans with (b (Build_finiteT H11)); auto with algebra.
Qed.

Hint Resolve seq_equal_concat: algebra.

Lemma seq_equal_seq_set :
 forall (A : Setoid) (n m : Nat) (v : seq n A) (w : seq m A),
 seq_equal v w -> seq_set v =' seq_set w in _.
intros.
assert (n =' m in _).
apply seq_equal_length_equal with A v w; auto with algebra.
simpl in |- *.
red in |- *.
split; intro.
simpl in |- *; simpl in H1.
inversion_clear H1.
destruct x0.
rename index into i.
case (H i).
intro.
inversion_clear H1.
inversion_clear H3.
exists (Build_finiteT x1).
apply Trans with (v (Build_finiteT in_range_prf)); auto with algebra.
intro.
inversion_clear H1.
apply False_ind; auto with algebra.
apply (le_not_lt n i); auto with algebra.
simpl in |- *; simpl in H1.
inversion_clear H1.
destruct x0.
rename index into i.
case (H i).
intro.
inversion_clear H1.
inversion_clear H3.
exists (Build_finiteT x0).
apply Trans with (w (Build_finiteT in_range_prf)); auto with algebra.
intro.
inversion_clear H1.
apply False_ind; auto with algebra.
apply (le_not_lt m i); auto with algebra.
Qed.


Lemma seq_equal_omit :
 forall (A : Setoid) (n m : Nat) (v : seq n A) (w : seq m A) 
   (i : fin n) (j : fin m),
 index i = index j -> seq_equal v w -> seq_equal (omit v i) (omit w j).
intros.
assert (n =' m in _).
apply seq_equal_length_equal with A v w; auto with algebra.
generalize dependent j.
generalize dependent i.
generalize dependent w.
generalize dependent v.

destruct n; [ destruct m as [| n] | destruct m as [| n0] ].
simpl in |- *.
auto.
inversion_clear H1.
inversion_clear H1.

rename n0 into m.
intros.
generalize dependent H.
clear H1.
generalize n m v w H0 i j.
clear j i H0 w v m n.
induction n; induction m; intros.
simpl in |- *.
apply seq_equal_refl.

assert (1 = S (S m)).
apply seq_equal_length_equal with A v w; auto with algebra.
inversion_clear H1.

assert (S (S n) = 1).
apply seq_equal_length_equal with A v w; auto with algebra.
inversion_clear H1.

destruct i; destruct j.
destruct index as [| n0];
 [ destruct index0 as [| n0] | destruct index0 as [| n1] ].
apply seq_equal_trans with (S n) (Seqtl v).
apply Map_eq_seq_equal.
auto with algebra.
apply seq_equal_trans with (S m) (Seqtl w).
apply seq_equal_seqtl with (v := v) (w := w); auto with algebra.
apply Map_eq_seq_equal.
apply Sym.
auto with algebra.
inversion_clear H.
inversion_clear H.

apply
 seq_equal_trans
  with
    (S n)
    (head v;; omit (Seqtl v) (Build_finiteT (lt_S_n _ _ in_range_prf))).
apply Map_eq_seq_equal.
auto with algebra.
apply
 seq_equal_trans
  with
    (S m)
    (head w;; omit (Seqtl w) (Build_finiteT (lt_S_n _ _ in_range_prf0))).
apply seq_equal_cons.

3: apply seq_equal_symm.
3: apply Map_eq_seq_equal.
3: auto with algebra.

generalize (IHn _ (Seqtl v) (Seqtl w)).
intros.
assert (seq_equal (Seqtl v) (Seqtl w)).
apply seq_equal_seqtl; auto with algebra.
generalize (H1 H2).
intro.
generalize
 (H3 (Build_finiteT (lt_S_n n0 (S n) in_range_prf))
    (Build_finiteT (lt_S_n n1 (S m) in_range_prf0))).
intuition.

generalize (H0 0).
intro p; inversion_clear p.
inversion_clear H1.
inversion_clear H2.
unfold head in |- *.
apply Trans with (v (Build_finiteT x)).
apply Ap_comp; auto with algebra.
apply Trans with (w (Build_finiteT x0)); auto with algebra.
inversion_clear H.
inversion_clear H1.
inversion_clear H.
Qed.