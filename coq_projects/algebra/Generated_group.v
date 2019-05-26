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
Require Export Group_kernel.
Require Export Free_group.
Section Generated_group_def.
Variable G : GROUP.
Variable A : part_set G.

Definition generated_group : subgroup G := coKer (FG_lift (inj_part A)).
End Generated_group_def.

Lemma generated_group_minimal :
 forall (G : GROUP) (A : part_set G) (H : subgroup G),
 included A H -> included (generated_group A) H.
unfold included in |- *.
simpl in |- *.
intros G A H H' x H'0; try assumption.
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
    (sgroup_law G (FG_lift_fun (inj_part A) f) (FG_lift_fun (inj_part A) f0));
 auto with algebra.
simpl in |- *.
intros x H'0; elim H'0; intros H'1 H'2; try exact H'2; clear H'0.
apply in_part_comp_l with (monoid_unit G); auto with algebra.
intros f H'0 x H'1; try assumption.
elim H'1; intros H'2 H'3; simpl in H'3; clear H'1.
apply in_part_comp_l with (group_inverse G (FG_lift_fun (inj_part A) f));
 auto with algebra.
Qed.

Lemma generated_group_prop_included :
 forall (G : GROUP) (A : part_set G), included A (generated_group A).
unfold included in |- *.
simpl in |- *.
intros G A x H'; try assumption.
exists (Var (V:=A) (Build_subtype (E:=G) (P:=A) (subtype_elt:=x) H')); split;
 [ idtac | try assumption ].
auto with algebra.
simpl in |- *.
auto with algebra.
Qed.

Lemma generated_group_prop :
 forall (G : GROUP) (A : part_set G) (y : G),
 in_part y (generated_group A) ->
 exists x : FG A, Equal y (FG_lift (inj_part A) x).
simpl in |- *; auto with algebra.
intros G A y H'; try assumption.
elim H'; intros x E; elim E; intros H'0 H'1; try exact H'1; clear E H'.
exists x; try assumption.
Qed.

Lemma generated_group_prop_rev :
 forall (G : GROUP) (A : part_set G) (y : G),
 (exists x : FG A, Equal y (FG_lift (inj_part A) x)) ->
 in_part y (generated_group A).
intros G A y H'; try assumption.
elim H'; intros x E; try exact E; clear H'.
simpl in |- *; auto with algebra.
exists x; split; [ idtac | try assumption ].
auto with algebra.
Qed.
Hint Resolve generated_group_minimal generated_group_prop_included
  generated_group_prop_rev: algebra.
