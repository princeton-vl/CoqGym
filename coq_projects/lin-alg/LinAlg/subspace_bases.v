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


(** * subspace_bases.v *)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export bases.
Require Export subspace_dim.

Lemma generates_inject_subsets :
 forall (F : field) (V : vectorspace F) (W : subspace V) (S X : part_set W),
 generates S X -> generates (inject_subsets S) (inject_subsets X).
intros.
red in |- *; red in H.
apply Trans with (span_ind (inject_subsets S):part_set V); auto with algebra.
assert (X =' span_ind S in part_set W).
apply Trans with (span S:part_set W); auto with algebra.
split; intros.
simpl in H1.
inversion_clear H1.
simpl in |- *.
clear H.
simpl in H0.
red in H0.
set (x0S := span_ind_uninject x0) in *.
set (xW := span_ind_injection x0S) in *.
elim (H0 xW).
intros.
cut (in_part xW (span_ind_set (V:=W) S)).
intro.
generalize dependent (H1 H3); intro p; red in p.
exists (Build_subtype p).
simpl in |- *.
unfold xW, x0S in |- *.
apply Trans with (span_ind_injection x0); auto with algebra.
apply span_ind_uninject_prop.
simpl in |- *.
exists x0S.
red in |- *.
unfold xW, x0S in |- *.
auto with algebra.

simpl in H1.
inversion_clear H1.
simpl in |- *.
clear H.
elim (H0 (subtype_elt x0)).
intros.
assert (in_part (subtype_elt x0) X); auto with algebra.
generalize dependent (H H3); intro.
simpl in H4.
inversion_clear H4.
clear H H1 H3.
red in H5.
generalize dependent x0.
generalize dependent x.
induction x1 as [| c| x0 IHx0 x2 IHx2| c x1 IHx1]; intros.

exists (Zerovector (inject_subsets S)).
apply Trans with (subtype_elt (subtype_elt x0)); auto with algebra.

exists (Immediately (inject_subsetsify c)).
apply Trans with (subtype_elt (subtype_elt x0)); auto with algebra.

set (x0V := subtype_elt (span_ind_injection x0)) in *.
elim (H0 (span_ind_injection x0)); intros.
assert (in_part (span_ind_injection x0) (span_ind (V:=W) S)).
simpl in |- *.
exists x0.
red in |- *; auto with algebra.
generalize dependent (H1 H3); intro p; red in p.
generalize dependent (IHx0 x0V (Build_subtype p)).
intro.
cut (x0V =' subtype_elt (subtype_elt (Build_subtype p)) in _).
intro q; generalize dependent (H4 q); clear H4 q; intro H4.
cut (subtype_elt (subtype_elt (Build_subtype p)) =' x0V in _).
intro q; generalize dependent (H4 q); clear H4 q; intro H4.
inversion_clear H4.
clear p H3 H1 H.

set (x2V := subtype_elt (span_ind_injection x2)) in *.
elim (H0 (span_ind_injection x2)); intros.
assert (in_part (span_ind_injection x2) (span_ind (V:=W) S)).
simpl in |- *.
exists x2.
red in |- *; auto with algebra.
generalize dependent (H1 H3); intro p; red in p.
generalize dependent (IHx2 x2V (Build_subtype p)).
intro.
cut (x2V =' subtype_elt (subtype_elt (Build_subtype p)) in _).
intro q; generalize dependent (H4 q); clear H4 q; intro H4.
cut (subtype_elt (subtype_elt (Build_subtype p)) =' x2V in _).
intro q; generalize dependent (H4 q); clear H4 q; intro H4.
inversion_clear H4.
clear p H3 H1 H.
exists (Plusvector x3 x4).
apply Trans with (subtype_elt (subtype_elt x1)); auto with algebra.
apply Trans with (subtype_elt (span_ind_injection (Plusvector x0 x2)));
 auto with algebra.
(* Simpl. takes too much time *)
apply
 Trans with (subtype_elt (span_ind_injection x0 +' span_ind_injection x2));
 [ apply subtype_elt_comp; simpl in |- *; red in |- *; apply Refl | idtac ].
apply Trans with (span_ind_injection x3 +' span_ind_injection x4);
 [ idtac | simpl in |- *; red in |- *; apply Refl ].
apply
 Trans
  with
    (subtype_elt (span_ind_injection x0) +'
     subtype_elt (span_ind_injection x2)).
simpl in |- *.
apply Refl.
fold x0V in |- *.
fold x2V in |- *.
apply SGROUP_comp; auto with algebra.
simpl in |- *.
apply Refl.
simpl in |- *; apply Refl.
simpl in |- *; apply Refl.
simpl in |- *; apply Refl.

set (x1V := subtype_elt (span_ind_injection x1)) in *.
elim (H0 (span_ind_injection x1)); intros.
assert (in_part (span_ind_injection x1) (span_ind (V:=W) S)).
simpl in |- *.
exists x1.
red in |- *; auto with algebra.
generalize dependent (H1 H3); intro p; red in p.
generalize dependent (IHx1 x1V (Build_subtype p)).
intro.
cut (x1V =' subtype_elt (subtype_elt (Build_subtype p)) in _).
intro q; generalize dependent (H4 q); clear H4 q; intro H4.
cut (subtype_elt (subtype_elt (Build_subtype p)) =' x1V in _).
intro q; generalize dependent (H4 q); clear H4 q; intro H4.
inversion_clear H4.
clear p H3 H1 H.
exists (Multvector c x2).
apply Trans with (subtype_elt (subtype_elt x0)); auto with algebra.
apply Trans with (subtype_elt (span_ind_injection (Multvector c x1)));
 auto with algebra.
simpl in |- *.
apply MODULE_comp; auto with algebra.
simpl in |- *.
apply Refl.
simpl in |- *; apply Refl.
Set Virtual Machine.
Qed.
Unset Virtual Machine.

Lemma bases_equal_then_subspace_equal :
 forall (F : field) (V : vectorspace F) (W1 W2 : subspace V) 
   (b1 : basis W1) (b2 : basis W2),
 inject_subsets b1 =' inject_subsets b2 in _ -> W1 =' W2 in part_set V.
intros.
destruct b1; destruct b2.
rename basis_carrier into b1.
rename basis_carrier0 into b2.
simpl in H.
inversion_clear is_basis_prf; inversion_clear is_basis_prf0.

assert (generates (inject_subsets b1) W1).
apply generates_comp with (inject_subsets b1) (inject_subsets (full W1));
 auto with algebra.
apply (inject_subsets_full_inv W1).
apply generates_inject_subsets.
auto.

assert (generates (inject_subsets b2) W2).
apply generates_comp with (inject_subsets b2) (inject_subsets (full W2));
 auto with algebra.
apply (inject_subsets_full_inv W2).
apply generates_inject_subsets.
auto.

split; intro.
generalize dependent is_lin_comb_from_generates.
intro.

red in H5.
elim (H5 x); intros.
apply H8.
simpl in |- *.

apply H7 with (W1:part_set V); auto with algebra.
apply generates_comp with (inject_subsets b1) (W1:part_set V);
 auto with algebra.

generalize dependent is_lin_comb_from_generates.
intro.

red in H4.
elim (H4 x); intros.
apply H8.
simpl in |- *.

apply H7 with (W2:part_set V); auto with algebra.
apply generates_comp with (inject_subsets b2) (W2:part_set V);
 auto with algebra.
Qed.
