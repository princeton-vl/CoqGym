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
Require Export Module_kernel.
Require Export Free_module.
Section Generated_module_def.
Variable R : RING.
Variable Mod : MODULE R.
Variable A : part_set Mod.

Definition generated_module : submodule Mod := coKer (FMd_lift (inj_part A)).
End Generated_module_def.

Lemma generated_module_minimal :
 forall (R : RING) (Mod : MODULE R) (A : part_set Mod) (H : submodule Mod),
 included A H -> included (generated_module A) H.
unfold included in |- *.
simpl in |- *.
intros R Mod A H H' x H'0; try assumption.
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
    (sgroup_law Mod (FMd_lift_fun (inj_part A) f)
       (FMd_lift_fun (inj_part A) f0)); auto with algebra.
simpl in |- *.
intros x H'0; elim H'0; intros H'1 H'2; try exact H'2; clear H'0.
apply in_part_comp_l with (monoid_unit Mod); auto with algebra.
intros f H'0 x H'1; try assumption.
elim H'1; intros H'2 H'3; simpl in H'3; clear H'1.
apply in_part_comp_l with (group_inverse Mod (FMd_lift_fun (inj_part A) f));
 auto with algebra.
intros c f H'0 x H'1; try assumption.
simpl in H'1.
elim H'1; intros H'2 H'3; try exact H'3; clear H'1.
apply in_part_comp_l with (module_mult c (FMd_lift_fun (inj_part A) f));
 auto with algebra.
Qed.

Lemma generated_module_prop_included :
 forall (R : RING) (Mod : MODULE R) (A : part_set Mod),
 included A (generated_module A).
unfold included in |- *.
simpl in |- *.
intros R Mod A x H'; try assumption.
exists (Var R (V:=A) (Build_subtype (E:=Mod) (P:=A) (subtype_elt:=x) H'));
 split; [ idtac | try assumption ].
auto with algebra.
simpl in |- *.
auto with algebra.
Qed.

Lemma generated_module_prop :
 forall (R : RING) (Mod : MODULE R) (A : part_set Mod) (y : Mod),
 in_part y (generated_module A) ->
 exists x : FMd R A, Equal y (FMd_lift (inj_part A) x).
simpl in |- *; auto with algebra.
intros R Mod A y H'; try assumption.
elim H'; intros x E; elim E; intros H'0 H'1; try exact H'1; clear E H'.
exists x; try assumption.
Qed.

Lemma generated_module_prop_rev :
 forall (R : RING) (Mod : MODULE R) (A : part_set Mod) (y : Mod),
 (exists x : FMd R A, Equal y (FMd_lift (inj_part A) x)) ->
 in_part y (generated_module A).
intros R Mod A y H'; try assumption.
elim H'; intros x E; try exact E; clear H'.
simpl in |- *; auto with algebra.
exists x; split; [ idtac | try assumption ].
auto with algebra.
Qed.
Hint Resolve generated_module_minimal generated_module_prop_included
  generated_module_prop_rev: algebra.
