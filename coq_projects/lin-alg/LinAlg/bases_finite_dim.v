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


(** * bases_finite_dim.v *)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export bases_from_generating_sets.
Require Export replacement_corollaries.

(** %\tocdef{is\_{\em[in]}finite\_dimensional}% *)
Definition is_finite_dimensional (F : field) (V : vectorspace F) :=
  exists beta : basis V, (exists n : Nat, has_n_elements n beta).

Definition is_infinite_dimensional (F : field) (V : vectorspace F) :=
  forall (beta : basis V) (n : Nat), ~ has_n_elements n beta.

(** %\tocdef{has\_dim}% *)
Definition has_dim (F : field) (n : Nat) (V : vectorspace F) :=
  exists beta : basis V, has_n_elements n beta.

Lemma finite_dim_vecsp_has_dim :
 forall (F : field) (V : vectorspace F),
 is_finite_dimensional V -> exists n : Nat, has_dim n V.
intros.
inversion_clear H.
rename x into beta.
inversion_clear H0.
inversion_clear H.
rename x into n.
exists n.
red in |- *.
exists beta; auto.
red in |- *.
exists x0; auto.
Qed.

Lemma has_dim_inj :
 forall (F : field) (V : vectorspace F) (n m : Nat),
 has_dim n V -> has_dim m V -> n =' m in _.
intros.
inversion_clear H.
inversion_clear H0.
assert (has_n_elements m x).
apply all_finite_bases_equally_big with x0; auto with algebra.
generalize has_n_elements_inj; intro p.
apply (p _ _ _ H1 _ _ H0); auto with algebra.
Qed.

Lemma has_dim_easy :
 forall (F : field) (V : vectorspace F) (b : part_set V),
 is_basis b -> forall n : nat, has_n_elements n b -> has_dim n V.
intros.
red in |- *.
exists (Build_basis H).
simpl in |- *.
auto.
Qed.

Section Part_3.
(** - %\intoc{Corollary 4 to 1.10}% *)
Lemma dimension_bounds_generating_set_size :
 forall (F : field) (V : vectorspace F) (n : Nat),
 has_dim n V ->
 forall S : part_set V,
 generates S (full V) ->
 has_at_most_n_elements n S -> is_basis S /\ has_n_elements n S.
intros.
generalize (every_finite_generating_set_has_a_subset_that_is_a_basis (W0:=S)).
intro p.
assert (is_finite_subset S).
red in |- *.
red in H1.
inversion_clear H1.
inversion_clear H2.
exists x.
generalize (n_element_subset_sequence H3).
intro.
inversion_clear H2.
inversion_clear H4.
exists x0; auto.
generalize (p H2 H0); clear p; intro p.
inversion_clear p.
rename x into S1.
red in H.
inversion_clear H.
rename x into beta.
generalize (all_finite_bases_equally_big H4 (Build_basis H3)).
intro.
assert (has_n_elements n S1).
apply inject_subsets_respects_has_n_elements; auto with algebra.
assert (has_at_least_n_elements n S).
apply subset_bounds_set_size_from_below with S1; auto with algebra.
assert (has_n_elements n S).
apply has_n_elements_by_at_least_at_most; auto with algebra.
split; auto.
apply is_basis_comp with (inject_subsets S1); auto with algebra.
assert (S1 =' full S in _).
apply subset_also_has_n_elements_then_it_is_full with n; auto with algebra.
apply Trans with (inject_subsets (full S)); auto with algebra.
Qed.

(** - %\intoc{Corollary 5 to 1.10}%: *)
Lemma every_lin_indep_set_can_be_extended_to_a_basis :
 forall (F : field) (V : vectorspace F),
 is_finite_dimensional V ->
 forall (beta : basis V) (Sset : part_set V),
 lin_indep Sset ->
 exists S1 : part_set V, included S1 beta /\ is_basis (union Sset S1).
intros.
generalize (finite_dim_vecsp_has_dim H); intro p.
inversion_clear p.
rename x into n.
generalize H1; intro HH2.
red in H1.
inversion_clear H1.
rename x into beta'.
assert (has_n_elements n beta).
apply all_finite_bases_equally_big with beta'; auto with algebra.
clear H2 beta'.
assert (exists m : Nat, has_n_elements m Sset /\ m <= n).
generalize (finite_basis_bounds_lin_indep_set_size' H1 H0); intros.
red in H2.
inversion_clear H2.
rename x into m.
exists m; intuition.

inversion_clear H2.
rename x into m.
inversion_clear H3.
generalize (replacement_theorem H1 H0 H4 H2); intro.
inversion_clear H3.
rename x into S1'.
set (S1 := inject_subsets S1') in *.
inversion_clear H5.

assert (has_at_most_n_elements n (union Sset S1)).
apply has_at_most_n_elements_comp with (m + (n - m)) (union Sset S1);
 auto with algebra.
2: auto with arith.
apply union_has_at_most_n_plus_m_elements; auto with algebra.
unfold S1 in |- *.
apply inject_subsets_preserves_has_n_elements; auto with algebra.
simpl in |- *; auto with arith.

exists S1.
generalize (dimension_bounds_generating_set_size HH2 H6 H5).
split; intuition.
unfold S1 in |- *.
apply inject_subsets_of_part_set_included.
Qed.

Lemma has_dim_zero_then_trivial :
 forall (F : field) (V : vectorspace F),
 has_dim 0 V -> full V =' single (zero V) in _.
intros.
red in H.
inversion_clear H.
rename x into beta.
generalize (is_basis_prf beta).
intro.
inversion_clear H.
red in H1.
apply Trans with (span beta:part_set _); auto with algebra.
apply Trans with (span_ind beta:part_set _); auto with algebra.
apply Trans with (span_ind (empty V):part_set _).
apply span_ind_comp; auto with algebra.
simpl in |- *.
red in |- *.
split; simpl in |- *; intro.
inversion_clear H.
generalize dependent x.
induction x0 as [| c| x1 IHx1 x2 IHx2| c x0 IHx0]; intros.
simpl in H3.
auto.
destruct c.
simpl in subtype_prf.
contradiction.
simpl in H3.
apply Trans with (span_ind_injection x1 +' span_ind_injection x2);
 auto with algebra.
apply Trans with (span_ind_injection x1 +' (zero V)); auto with algebra.
apply Trans with (span_ind_injection (Multvector c x0)); auto with algebra.
simpl in |- *.
apply Trans with (c mX (zero V)); auto with algebra.
exists (Zerovector (empty V)).
simpl in |- *.
auto.
Qed.

End Part_3.

(** %\tocdef{findimvecsp}% *)
Record findimvecsp (F : field) : Type := 
  {the_dim : nat;
   the_vectorspace :>
    module F
    (* Strangely, I cannot coerce to (vectorspace F) since other coercions *)
    (* stop being inferenced: e.g. W:(part_set V) will no longer be allowed... *)
   ;
   dim_prf : has_dim the_dim the_vectorspace}.