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


(** * maxlinindepsubsets.v *)
Set Implicit Arguments.
Unset Strict Implicit.
(** - This file would be the book's chapter 1.7. It doesn't have the last place in the
 dependency graph (and hence in the coqdoc-generated documentation you may be reading
 now): the ``finite'' stuff of 1.6 isn't needed. Finiteness is usually harder to do in
 type theory than more general number-agnostic stuff---and this file goes to show, I
 guess... *)
Require Export bases.
Require Export lin_dep_facts.

Section defs.
Variable X : Setoid.
(** - ``B properly contains A'' means $A\subset B$ and $A\neq B$, so ``no member of F
 properly contains A'' is $\not\exists B\in F. A\subset B\wedge A\neq B$: *)
Definition maximal (F : part_set (part_set X)) (A : part_set X) :=
  in_part A F /\
  ~ (exists B : part_set X, in_part B F /\ included A B /\ ~ A =' B in _).

Definition is_chain (F : part_set (part_set X)) :=
  forall A B : part_set X,
  in_part A F -> in_part B F -> included A B \/ included B A.

(** - Quoting the Maximal Principle from page 50:

 Let $\cal F$ be a family of sets. If for each chain $\cal C\subset \cal F$ there
 exists a member of $\cal F$ that contains each member of $\cal C$, then $\cal F$
 contains a maximal element.*)

(** %\tocdef{MAXIMAL\_PRINCIPLE}% *)
Axiom
  MAXIMAL_PRINCIPLE :
    forall F : part_set (part_set X),
    (forall C : part_set (part_set X),
     is_chain C ->
     included C F ->
     exists A : part_set X,
       in_part A F /\ (forall B : part_set X, in_part B C -> included B A)) ->
    exists A : part_set X, maximal F A.
End defs.


(** - %\intoc{\bf Theorem 1.12}% says every maximally linearly independent subset of
 any generating set is a basis *)
Lemma max_lin_indep_subsets_of_generating_sets_are_bases :
 forall (F : field) (V : vectorspace F) (W : part_set V),
 generates W (full V) ->
 forall beta : part_set V, max_lin_indep beta W -> is_basis beta.

intros.
red in |- *.
assert (lin_indep beta).
red in H0.
inversion_clear H0.
inversion_clear H2; auto.
split; auto.

cut (included W (span beta:part_set _)).
intro.
red in |- *.
red in H.
apply included_antisym; auto with algebra.
apply included_comp with (span W:part_set _) (span beta:part_set _);
 auto with algebra.
apply span_smallest_subspace_containing_subset; auto with algebra.

apply NNPP; intro.
assert (exists x : W, ~ in_part (W x) (span beta:part_set _)).
apply NNPP; intro; apply H2.
red in |- *.
intros.
apply NNPP; intro.
apply H3.
red in H4; exists (Build_subtype H4).
intro; apply H5.
simpl in H6.
simpl in |- *.
auto.

inversion_clear H3.
assert (~ in_part (W x) beta).
intro; apply H4.
apply set_included_in_its_span; auto with algebra.
assert (lin_indep (union beta (single (W x)))).
elim (lin_dep_vs_span_lemma H1 H3).
intros.
intro.
apply H4; auto with algebra.

red in H0.
inversion_clear H0.
inversion_clear H7.
apply H5; auto with algebra.
apply H8; auto with algebra.
apply in_part_comp_l with (subtype_elt x); auto with algebra.
Qed.

(** - %\intoc{Corollary to 1.12}%: *)
Lemma basis_iff_max_lin_indep :
 forall (F : field) (V : vectorspace F) (beta : part_set V),
 is_basis beta <-> max_lin_indep beta (full V).
split.
2: apply max_lin_indep_subsets_of_generating_sets_are_bases;
    auto with algebra.
2: red in |- *.
2: apply included_antisym; auto with algebra.
intro.
red in |- *.
split.
red in |- *.
simpl in |- *.
auto.
split.
red in H.
inversion_clear H.
auto.
red in H.
inversion_clear H.
intros.
elim (lin_dep_vs_span_lemma H1 H2).
intros.
apply H4; auto with algebra.
red in H0.
apply in_part_comp_r with (full V); auto with algebra.
Qed.

Lemma basis_is_max_lin_indep :
 forall (F : field) (V : vectorspace F) (beta : basis V),
 max_lin_indep beta (full V).
intros.
elim (basis_iff_max_lin_indep beta).
intros.
apply H; auto with algebra.
exact (is_basis_prf beta).
Qed.

(** - %\intoc{\bf Theorem 1.13}%: *)
Lemma max_lin_indep_subset_generated :
 forall (F : field) (V : vectorspace F) (W : part_set V),
 lin_indep W ->
 exists W' : part_set V, max_lin_indep W' (full V) /\ included W W'.
intros.
assert (pred_compatible (fun X : part_set V => included W X /\ lin_indep X)).
red in |- *.
intros.
inversion_clear H0.
split.
apply included_comp with W x; auto with algebra.
apply lin_indep_comp with x; auto with algebra.
set (FF := Build_Predicate H0:part_set (part_set V)) in *.
cut (exists W' : part_set V, maximal FF W').
intros.
inversion_clear H1.
rename x into W'; exists W'.
red in H2.
inversion_clear H2.
simpl in H1.
inversion_clear H1.
split; auto.
red in |- *.
split.
red in |- *.
simpl in |- *.
auto.
split.
auto.
intros.
simpl in H3.
apply NNPP; intro; apply H3.
exists (union W' (single y)).
split; split.
red in |- *.
simpl in |- *.
red in H2.
intros.
left; auto.
auto.
red in |- *; simpl in |- *; auto.
intro.
red in H7.
apply H5; auto with algebra.
elim (H7 y).
intros.
apply H9; auto with algebra.

apply MAXIMAL_PRINCIPLE; auto with algebra.
intros.
case (classic (C =' empty _ in _)).
intro.
exists W.
split.
simpl in |- *.
split; auto.
red in |- *.
auto.
intros.
assert (in_part B (empty _)).
apply in_part_comp_r with C; auto with algebra.
simpl in H5.
contradiction.

exists (union_part C).
split.
2: auto with algebra.
simpl in |- *.
split.
assert (forall B : part_set V, in_part B C -> included W B).
intros.
generalize (H2 _ H4).
intros.
simpl in H5.
inversion_clear H5; auto.
assert (exists A : part_set V, in_part A C).
apply NNPP; intro.
apply H3.
simpl in |- *.
red in |- *.
simpl in |- *.
split; intro.
apply H5.
exists x; auto.
contradiction.
inversion_clear H5.
rename x into A.
generalize (H2 _ H6).
intro.
red in |- *.
intros.
simpl in |- *.
exists A.
split; auto.
simpl in H5.
inversion_clear H5.
apply H8; auto with algebra.

set (U := union_part C) in *.
elim (lin_dep_defs_eqv U).
intros.
apply H5.
clear H4 H5.
red in |- *.
intros.
intro; apply H5.
rename a into c.
rename v into u.

assert (exists A : C, (forall i : fin _, in_part (U (u i)) (C A))).
clear H6 H5 H4 c H2 H.
generalize u; clear u.
induction n; intro.
assert (exists A : C, in_part (U (head u)) (C A)).
set (u1 := head u) in *.
destruct u1.
simpl in subtype_prf.
inversion_clear subtype_prf.
inversion_clear H.
red in H2.
exists (Build_subtype H2).
simpl in |- *.
auto.
inversion_clear H.
rename x into A.
exists A.
intro.
apply in_part_comp_l with (U (head u)); auto with algebra.
simpl in |- *.
apply subtype_elt_comp; auto with algebra.

assert (exists A : C, in_part (U (head u)) (C A)).
set (u1 := head u) in *.
destruct u1.
simpl in subtype_prf.
inversion_clear subtype_prf.
inversion_clear H.
red in H2.
exists (Build_subtype H2).
simpl in |- *.
auto.
inversion_clear H.
rename x into A1.
generalize (IHn (Seqtl u)); intro p; inversion_clear p.
rename x into A2345n.
red in H1.
assert (in_part (C A1) C /\ in_part (C A2345n) C).
split; simpl in |- *; auto with algebra.
inversion_clear H4.
generalize (H1 _ _ H5 H6).
intro p.
inversion_clear p.
exists A2345n.
assert (in_part (U (head u)) (C A2345n)).
apply H4; auto with algebra.
intro.
clear H4 H5 H6.
destruct i.
clear IHn H3 H1 FF H0 W H2.
generalize dependent n.
destruct index as [| n].
intros.
apply in_part_comp_l with (U (head u)); auto with algebra.
simpl in |- *; (apply subtype_elt_comp; auto with algebra).
unfold head in |- *.
intros.
apply
 in_part_comp_l with (U (Seqtl u (Build_finiteT (lt_S_n _ _ in_range_prf))));
 auto with algebra.
simpl in |- *; (apply subtype_elt_comp; auto with algebra).
exists A1.
assert (forall i : fin (S n), in_part (U (Seqtl u i)) (C A1)).
intro; (apply H4; auto with algebra).
intro.
clear H4 H5 H6 H.
destruct i.
clear IHn H3 H1 FF H0 W.
generalize dependent n.
destruct index as [| n].
intros.
apply in_part_comp_l with (U (head u)); auto with algebra.
simpl in |- *; (apply subtype_elt_comp; auto with algebra).
unfold head in |- *.
intros.
apply
 in_part_comp_l with (U (Seqtl u (Build_finiteT (lt_S_n _ _ in_range_prf))));
 auto with algebra.
simpl in |- *; (apply subtype_elt_comp; auto with algebra).

inversion_clear H7.
rename x into A.
assert (lin_indep (C A)).
destruct A.
assert (Pred_fun FF subtype_elt).
apply H2; auto with algebra.
simpl in H7.
simpl in |- *.
tauto.

assert (forall i : fin (S n), in_part (Map_embed u i) (C A)).
intro; simpl in |- *.
simpl in H8; (apply H8; auto with algebra).
set (u' := cast_map_to_subset H9:seq _ _) in *.
cut (sum (mult_by_scalars c (Map_embed u')) =' (zero V) in _).
cut (distinct u').
cut (lin_indep' (C A)).
intros.
red in H10.
generalize (H10 _ c _ H11).
intro.
apply NNPP; intro; (apply H13; auto with algebra).
elim (lin_dep_defs_eqv (C A)); tauto.
red in |- *; red in H4.
unfold u' in |- *; intros.
intro.
red in H4; (apply (H4 _ _ H10); auto with algebra).
apply Trans with (sum (mult_by_scalars c (Map_embed u))); auto with algebra.
Qed.

(** - %\intoc{Corollary to 1.13}% *)
Lemma every_vecsp_has_a_basis :
 forall (F : field) (V : vectorspace F),
 exists beta : part_set V, is_basis beta.
intros.
cut (exists beta : part_set V, max_lin_indep beta (full V)).
intro.
inversion_clear H.
exists x.
elim (basis_iff_max_lin_indep x); auto.
assert (lin_indep (empty V)).
apply empty_lin_indep; auto with algebra.
elim (max_lin_indep_subset_generated H).
intros; exists x; tauto.
Qed.