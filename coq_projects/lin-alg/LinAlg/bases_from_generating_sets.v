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


(** * bases_from_generating_sets.v *)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export bases.
Require Export finite_subsets.
Require Export lin_dep_facts.

Section MAIN.
Variable F : field.
Variable V : vectorspace F.
Variable W0 : part_set V.
Variable H : is_finite_subset W0.
Variable H0 : generates W0 (full V).
(** - %\intoc{\bf Theorem 1.9}% in various flavours: *)
Lemma every_finite_generating_set_has_a_subset_that_is_a_basis :
 exists W : part_set W0, is_basis (inject_subsets W).
inversion_clear H.
inversion_clear H1.
assert
 (exists k : Nat,
    (exists v : seq k V,
       is_subseq v x0 /\ max_lin_indep (seq_set v) (seq_set x0))).
apply seq_has_max_lin_indep_subseq; auto with algebra.
inversion_clear H1.
inversion_clear H2.
inversion_clear H1.
assert (forall i : fin x1, in_part (x2 i) W0).
intro.
apply in_part_comp_r with (seq_set x0); auto with algebra.
simpl in |- *.
change (exists i0 : fin x, x2 i =' x0 i0 in _) in |- *.
apply subseq_has_right_elements; auto with algebra.
exists (seq_set (cast_map_to_subset H1)).
red in |- *.
split.
red in |- *.
red in H0.
apply Trans with (span W0:part_set V); auto with algebra.
apply Trans with (span (seq_set x0):part_set V); auto with algebra.
apply Trans with (span (seq_set x2):part_set V).
apply span_comp; auto with algebra.
unfold inject_subsets in |- *.
simpl in |- *.
red in |- *.
simpl in |- *.
split; intros.
inversion_clear H4.
destruct x4.
simpl in H5.
generalize subtype_elt subtype_prf H5; clear H5 subtype_prf subtype_elt. 
intros w wp H5.
inversion_clear wp.
exists x4.
apply Trans with (subtype_elt w); auto with algebra.
apply Trans with (subtype_elt (cast_map_to_subset H1 x4)); auto with algebra.

inversion_clear H4.
generalize (H1 x4); intro.
red in H4.
assert (in_part (Build_subtype H4:W0) (seq_set (cast_map_to_subset H1))).
simpl in |- *.
exists x4.
red in |- *.
simpl in |- *.
unfold cast_to_subset_fun in |- *.
destruct x2.
simpl in |- *.
auto with algebra.
red in H6.
exists (Build_subtype H6).
simpl in |- *.
auto with algebra.

apply Sym.
apply max_lin_indep_subset_has_same_span; auto with algebra.
inversion_clear H3.
inversion_clear H5.
apply lin_indep_comp with (seq_set x2); auto with algebra.
apply Sym.
unfold inject_subsets in |- *.
simpl in |- *.
red in |- *.
simpl in |- *.
split; intros.
inversion_clear H5.
destruct x4.
simpl in H7.
generalize subtype_elt subtype_prf H7; clear H7 subtype_prf subtype_elt. 
intros w wp H7.
inversion_clear wp.
exists x4.
apply Trans with (subtype_elt w); auto with algebra.
apply Trans with (subtype_elt (cast_map_to_subset H1 x4)); auto with algebra.

inversion_clear H5.
generalize (H1 x4); intro.
red in H5.
assert (in_part (Build_subtype H5:W0) (seq_set (cast_map_to_subset H1))).
simpl in |- *.
exists x4.
red in |- *.
simpl in |- *.
unfold cast_to_subset_fun in |- *.
destruct x2.
simpl in |- *.
auto with algebra.
red in H8.
exists (Build_subtype H8).
simpl in |- *.
auto with algebra.
Qed.

Lemma every_finite_generating_set_includes_a_basis :
 exists W : basis V, included W W0.
elim every_finite_generating_set_has_a_subset_that_is_a_basis;
 auto with algebra.
intros.
exists (Build_basis H1).
simpl in |- *.
red in |- *; simpl in |- *.
intros.
inversion_clear H2.
apply in_part_comp_l with (subtype_elt (subtype_elt x1)); auto with algebra.
Qed.

Lemma every_finitely_generated_vectorspace_has_a_finite_basis :
 exists W : part_set V, is_finite_subset W /\ is_basis W.
intros.
assert (exists W : part_set W0, is_basis (inject_subsets W)).
apply every_finite_generating_set_has_a_subset_that_is_a_basis;
 auto with algebra.
inversion_clear H1.
exists (inject_subsets x).
split; auto.
apply included_reflects_is_finite_subset with W0; auto with algebra.
Qed.
End MAIN.