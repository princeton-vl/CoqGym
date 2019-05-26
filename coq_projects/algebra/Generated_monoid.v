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


Set Implicit Arguments.
Unset Strict Implicit.
Require Export Monoid_kernel.
Require Export Free_monoid.
Section Generated_monoid_def.
Variable M : MONOID.
Variable A : part_set M.

Definition generated_monoid : submonoid M :=
  image_monoid_hom (FM_lift (inj_part A)).
End Generated_monoid_def.

Lemma generated_monoid_minimal :
 forall (M : MONOID) (A : part_set M) (H : submonoid M),
 included A H -> included (generated_monoid A) H.
unfold included in |- *.
simpl in |- *.
intros M A H H' x H'0; try assumption.
elim H'0; intros x0; clear H'0.
generalize x; clear x.
elim x0.
intros c; try assumption.
elim c.
simpl in |- *.
intros y subtype_prf x H'0; elim H'0; intros H'1 H'2; try exact H'2;
 clear H'0.
apply in_part_comp_l with y; auto with algebra.
intros f H'0 f0 H'1 x H'2; elim H'2; intros H'3 H'4; try exact H'4; clear H'2.
simpl in H'4.
apply
 in_part_comp_l
  with
    (sgroup_law M (FM_lift_fun (inj_part A) f) (FM_lift_fun (inj_part A) f0));
 auto with algebra.
simpl in |- *.
intros x H'0; elim H'0; intros H'1 H'2; try exact H'2; clear H'0.
apply in_part_comp_l with (monoid_unit M); auto with algebra.
Qed.

Lemma generated_monoid_prop_included :
 forall (M : MONOID) (A : part_set M), included A (generated_monoid A).
unfold included in |- *.
simpl in |- *.
intros M A x H'; try assumption.
exists (Var (V:=A) (Build_subtype (E:=M) (P:=A) (subtype_elt:=x) H')); split;
 [ idtac | try assumption ].
auto with algebra.
simpl in |- *.
auto with algebra.
Qed.

Lemma generated_monoid_prop :
 forall (M : MONOID) (A : part_set M) (y : M),
 in_part y (generated_monoid A) ->
 exists x : FM A, Equal y (FM_lift (inj_part A) x).
simpl in |- *; auto with algebra.
intros M A y H'; try assumption.
elim H'; intros x E; elim E; intros H'0 H'1; try exact H'1; clear E H'.
exists x; try assumption.
Qed.

Lemma generated_monoid_prop_rev :
 forall (M : MONOID) (A : part_set M) (y : M),
 (exists x : FM A, Equal y (FM_lift (inj_part A) x)) ->
 in_part y (generated_monoid A).
intros M A y H'; try assumption.
elim H'; intros x E; try exact E; clear H'.
simpl in |- *; auto with algebra.
exists x; split; [ idtac | try assumption ].
auto with algebra.
Qed.
Hint Resolve generated_monoid_minimal generated_monoid_prop_included
  generated_monoid_prop_rev: algebra.
