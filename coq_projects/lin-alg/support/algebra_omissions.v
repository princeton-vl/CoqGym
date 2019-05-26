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


(** %\subsection*{ support :  algebra\_omissions.v }%*)
(** - In this file I prove some results that do not pertain to linear algebra at all.
 Instead, they could have been proven solely for the algebra distribution. This is
 also why I do not use the syntactic sugar as defined in equal_syntax.v and 
 more_syntax.v *)

From Algebra Require Export Group_facts.
Set Implicit Arguments.
Unset Strict Implicit.

Lemma group_inverse_inj :
 forall (G : GROUP) (g g' : G),
 Equal (group_inverse _ g) (group_inverse _ g') -> Equal g g'.
intros.
apply Trans with (group_inverse _ (group_inverse _ g)); auto with algebra.
apply GROUP_law_inverse.
apply Trans with (sgroup_law _ (group_inverse _ g') g'); auto with algebra.
Qed.

(* Because of later notation, this should also be known as: *)

Definition min_inj := group_inverse_inj.


(** - Elements of subsets are really pairs of those elements and proofs that they belong
 to that subset. I prove that two of these pairs are equal (in the subsetoid) iff their
 first projections are (in the parent setoid) *)

Lemma subtype_elt_comp :
 forall (A : Setoid) (B : part_set A) (b b' : B),
 Equal b b' -> Equal (subtype_elt b) (subtype_elt b').
simpl in |- *.
unfold subtype_image_equal in |- *.
auto with algebra.
Qed.

Lemma subtype_elt_inj :
 forall (A : Setoid) (B : part_set A) (b b' : B),
 Equal (subtype_elt b) (subtype_elt b') -> Equal b b'.
simpl in |- *.
unfold subtype_image_equal in |- *.
auto with algebra.
Qed.

Hint Resolve subtype_elt_comp: algebra.

Lemma in_part_subtype_elt :
 forall (A : Setoid) (B : part_set A) (b : B), in_part (subtype_elt b) B.
intros.
red in |- *.
apply subtype_prf.
Qed.

Hint Resolve in_part_subtype_elt: algebra.


(** - The setoid mechanism as defined in the algebra contribution makes for a 'layered'
 structure when dealing with subsets. Suppose $C\subset B\subset A$. This is translated
 as [A:Setoid; B:(part_set A); C:(part_set B)]. But obviously also $C\subset A$. Now
 [inject_subsets] injects a subset of B into the subsets of [A]

 %\label{injectsubsets}% *)

Definition inject_subsets :
  forall (A : Setoid) (B : part_set A), part_set B -> part_set A.
intros A B C.
apply
 (Build_Predicate
    (Pred_fun:=fun a : A =>
               exists c : C, Equal a (subtype_elt (subtype_elt c)))).
red in |- *.
intros.
destruct H.
generalize dependent x0; intro c; intros.
exists c.
apply Trans with x; auto with algebra.
Defined.

Lemma inject_subsets_comp :
 forall (A : Setoid) (B : part_set A) (C C' : part_set B),
 Equal C C' -> Equal (inject_subsets C) (inject_subsets C').
intros.
simpl in H; simpl in |- *.
red in H; red in |- *.
intro a; split; intros.
simpl in |- *; simpl in H0.
destruct H0.
elim (H (C x)).
intros.
assert (in_part (C x) C).
simpl in |- *.
auto with algebra.
generalize (H1 H3); clear H1 H2 H3; intro.
red in H1.
exists (Build_subtype H1).
simpl in |- *.
auto.

simpl in |- *; simpl in H0.
destruct H0.
elim (H (C' x)).
intros.
assert (in_part (C' x) C').
simpl in |- *.
auto with algebra.
generalize (H2 H3); clear H1 H2 H3; intro.
red in H1.
exists (Build_subtype H1).
simpl in |- *.
auto.
Qed.

Hint Resolve inject_subsets_comp: algebra.

Lemma inject_subsets_of_part_set_included :
 forall (A : Setoid) (B : part_set A) (C : part_set B),
 included (inject_subsets C) B.
intros.
unfold included, inject_subsets in |- *.
simpl in |- *.
intros.
inversion_clear H.
apply in_part_comp_l with (subtype_elt (subtype_elt x0)); auto with algebra.
Qed.

Hint Resolve inject_subsets_of_part_set_included: algebra.

Lemma inject_subsets_full_inv :
 forall (A : Setoid) (B : part_set A), Equal (inject_subsets (full B)) B.
intros.
simpl in |- *.
red in |- *.
split; intros.
simpl in H.
inversion_clear H.
destruct x0.
simpl in H0.
generalize dependent subtype_elt; intro b; intros.
apply in_part_comp_l with (subtype_elt b); auto with algebra.

simpl in |- *.
red in H.
set (b := Build_subtype H:B) in *.
assert (in_part b (full B)); simpl in |- *; auto.
red in H0.
exists (Build_subtype H0).
simpl in |- *.
auto with algebra.
Qed.

Hint Resolve inject_subsets_full_inv: algebra.

(** - Once we have [inject_subsets], we may need to view an element of [C] as an element
of the injected subset: so, if [x:C] then [(inject_subsetsify x):(inject_subsets C)]

 %\label{injectsubsetsify}% *)

Definition inject_subsetsify :
  forall (A : Setoid) (B : part_set A) (C : part_set B),
  C -> inject_subsets C.
intros A B C c.
set (c' := B (C c)) in *.
assert (exists c : C, Equal c' (subtype_elt (subtype_elt c))).
exists c.
unfold c' in |- *; simpl in |- *.
auto with algebra.
exists c'.
auto.
Defined.

Lemma inject_subsetsify_comp :
 forall (A : Setoid) (B : part_set A) (C : part_set B) (c c' : C),
 Equal c c' -> Equal (inject_subsetsify c) (inject_subsetsify c').
intros.
simpl in |- *.
red in |- *.
simpl in |- *.
auto with algebra.
Qed.


(** - ...and vice versa: if [x:(inject_subsets C)] then [(uninject_subsets x):C]

 %\label{uninjectsubsetsify}% *)

Definition uninject_subsetsify :
  forall (A : Setoid) (B : part_set A) (C : part_set B),
  inject_subsets C -> C.
intros.
simpl in |- *.
destruct X.
generalize dependent subtype_elt.
intros a Ha.
simpl in Ha.
assert (in_part a B).
inversion_clear Ha.
apply in_part_comp_l with (subtype_elt (subtype_elt x)); auto with algebra.
red in H.
exists (Build_subtype H).
change (in_part (Build_subtype H:B) C) in |- *.
inversion_clear Ha.
apply in_part_comp_l with (subtype_elt x); auto with algebra.
Defined.

Lemma uninject_subsetsify_comp :
 forall (A : Setoid) (B : part_set A) (C : part_set B),
 fun_compatible (uninject_subsetsify (A:=A) (B:=B) (C:=C)).
red in |- *.
intros.
unfold uninject_subsetsify in |- *.
destruct x; destruct y.
simpl in |- *.
red in |- *.
simpl in |- *.
auto with algebra.
Qed.

Lemma in_part_included :
 forall (A : Setoid) (B C : part_set A) (a : A),
 in_part a B -> included B C -> in_part a C.
intros.
red in H0.
auto.
Qed.

Lemma exists_difference :
 forall n m : nat, n <= m -> exists q : nat, m = n + q.
induction m.
destruct n.
intro; exists 0; auto.
intro; inversion_clear H.
intro.
inversion_clear H.
exists 0; auto.
generalize (IHm H0); intro p; inversion_clear p.
exists (S x).
transitivity (S n + x).
simpl in |- *.
apply f_equal with (f := S).
auto.
simpl in |- *.
apply plus_n_Sm.
Qed.
