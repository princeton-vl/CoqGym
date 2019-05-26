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


(** * replacement_corollaries.v *)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export replacement_theorem.
Require Export counting_elements.

Section MAIN.
Variable F : field.
Variable V : vectorspace F.
(** - %\intoc{Corollary 1 to 1.10}% *)
Lemma finite_bases_always_equally_big :
 forall (n : Nat) (beta : basis V),
 has_n_elements n beta ->
 forall Sset : part_set V,
 lin_indep Sset -> has_n_elements n Sset -> is_basis Sset.
intros.
generalize replacement_theorem.
intro p.
generalize (p _ _ _ _ H); clear p; intro p.
assert (n <= n); auto.
generalize (p _ H0 _ H2 H1).
clear p.
intro.
inversion_clear H3.
inversion_clear H4.
assert (x =' empty beta in _).
red in H3.
inversion_clear H3.
inversion_clear H4.
simpl in |- *.
red in |- *.
split; intros.
simpl in |- *.
simpl in H3.
red in H3.
simpl in H3.
generalize (H3 (Build_subtype H4)).
clear H3; intro H3; inversion_clear H3.
generalize (H7 I); clear H7 H8; intro H3; inversion_clear H3.
generalize (minus_n_n n); intro.
generalize (cast_fin x2 (sym_eq H3)).
auto with algebra.
simpl in H4.
contradiction.
red in |- *.
split.
2: auto.
apply generates_comp with (union Sset (inject_subsets x)) (full V);
 auto with algebra.
apply Trans with (union Sset (inject_subsets (empty beta)));
 auto with algebra.
apply Trans with (union Sset (empty V)); auto with algebra.
apply union_comp; auto with algebra.
simpl in |- *.
red in |- *.
split; intro.
2: simpl in H6; contradiction.
simpl in H6.
inversion_clear H6.
inversion_clear x1.
simpl in subtype_prf.
contradiction.
Qed.

(** - %\intoc{Corollary 2 to 1.10}% (partly) *)
Lemma finite_basis_bounds_lin_indep_set_size :
 forall (n : Nat) (beta : basis V),
 has_n_elements n beta ->
 forall Sset : part_set V, has_at_least_n_elements (S n) Sset -> lin_dep Sset.
intros.
apply NNPP; intro.

inversion_clear H0.
assert (exists S1 : part_set V, included S1 Sset /\ has_n_elements n S1).
set (S1 := seq_set (Map_embed (Seqtl x))) in *.
exists S1.
split.
red in |- *.
intros.
rename x0 into v.
inversion_clear H0.
apply in_part_comp_l with (Map_embed (Seqtl x) x0); auto with algebra.
simpl in |- *.
destruct x0.
auto with algebra.
red in |- *.
exists (seq_set_seq (Map_embed (Seqtl x))).
split.
simpl in |- *; red in |- *; simpl in |- *.
intros; split; intro; auto.
unfold subtype_image_equal in |- *.
simpl in |- *.
destruct x0.
rename subtype_elt into v.
rename subtype_prf into Hv.
simpl in Hv.
inversion_clear Hv.
exists x0.
destruct x0.
simpl in |- *.
auto.
red in |- *.
intros.
simpl in |- *.
unfold subtype_image_equal in |- *.
simpl in |- *.
destruct i; destruct j; simpl in |- *.
intro.
apply
 (H2 (Build_finiteT (lt_n_S index n in_range_prf))
    (Build_finiteT (lt_n_S index0 n in_range_prf0))); 
 auto with algebra.
simpl in |- *.
simpl in H0.
auto with arith.
inversion_clear H0.
rename x0 into S1.
inversion_clear H3.

generalize (finite_bases_always_equally_big H).
intro p.
assert (lin_indep S1).
apply lin_indep_include with Sset; auto with algebra.
generalize (p _ H3 H4).
clear p; intro.
rename x into Sseq.
assert (exists x : V, in_part x Sset /\ ~ in_part x S1).
apply has_extra_element_strong with n (S n); auto with algebra.
red in |- *.
exists Sseq; auto.
inversion_clear H6.
inversion_clear H7.
assert (in_part x (span S1)).
inversion_clear H5.
red in H7.
apply in_part_comp_r with (full V); auto with algebra.

assert (lin_dep (union S1 (single x))).
elim (lin_dep_vs_span_lemma H3 H8).
intros.
apply H10; auto with algebra.

assert (included (union S1 (single x)) Sset).
red in |- *.
intros v H13.
simpl in H13.
inversion_clear H13.
auto with algebra.
apply in_part_comp_l with x; auto with algebra.

assert (lin_dep Sset).
apply lin_dep_include with (union S1 (single x)); auto with algebra.
apply H1; auto with algebra.
Qed.

(** - Corollary 2 to 1.10 (the rest): *)
Lemma finite_basis_bounds_lin_indep_set_size' :
 forall (n : Nat) (beta : basis V),
 has_n_elements n beta ->
 forall Sset : part_set V, lin_indep Sset -> has_at_most_n_elements n Sset.
intros.
generalize (finite_basis_bounds_lin_indep_set_size H).
intro p; generalize (p Sset); clear p; intro p.
apply not_at_least_then_at_most; auto with algebra.
Qed.

(** - %\intoc{Corollary 3 to 1.10}% *)

Lemma all_finite_bases_equally_big :
 forall (n : Nat) (beta : basis V),
 has_n_elements n beta -> forall Sset : basis V, has_n_elements n Sset.
intros.
generalize (finite_basis_bounds_lin_indep_set_size H).
intro p; generalize (p Sset); clear p; intro p.
inversion H.
assert (has_at_most_n_elements n Sset).
apply not_at_least_then_at_most; auto with algebra.
intro.
generalize (p H1).
elim (is_basis_prf Sset); auto with algebra.

inversion_clear H1.
rename x0 into m.
inversion_clear H2.
elim (is_basis_prf beta); intros.
generalize (finite_basis_bounds_lin_indep_set_size' H3 H4).
intros.
inversion_clear H5.
inversion_clear H6.

assert (x0 = n).
generalize has_n_elements_inj.
intros.
apply (H6 _ _ _ H7 _ _ H); auto with algebra.

assert (m = n).
rewrite H6 in H7.
apply le_antisym; auto with algebra.
rewrite <- H6.
auto.
rewrite <- H8.
auto.
Qed.

End MAIN.