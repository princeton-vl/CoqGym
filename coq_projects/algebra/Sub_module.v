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
Require Export Sub_group.
Require Export Module_facts.
Require Export Module_util.
Require Export Monoid_util.
Require Export Group_util.
Section Def.
Variable R : RING.
Variable M : MODULE R.
Section Sub_module.
Variable N : subgroup M.
Hypothesis
  Nop : forall (a : R) (x : M), in_part x N -> in_part (module_mult a x) N.

Let Na : ABELIAN_GROUP.
apply
 (BUILD_ABELIAN_GROUP (E:=N) (genlaw:=sgroup_law N) (e:=
    monoid_unit N) (geninv:=group_inverse_map N)); 
 auto with algebra.
simpl in |- *.
unfold subtype_image_equal in |- *.
simpl in |- *.
auto with algebra.
simpl in |- *.
unfold subtype_image_equal in |- *.
simpl in |- *.
auto with algebra.
Defined.

Let endofun : R -> Endo_SET Na.
intros a; try assumption.
simpl in |- *.
apply
 (Build_Map (A:=N) (B:=N)
    (Ap:=fun x : N => Build_subtype (Nop a (subtype_prf x)))).
red in |- *.
simpl in |- *.
unfold subtype_image_equal in |- *.
simpl in |- *.
auto with algebra.
Defined.

Definition submodule_op : operation (ring_monoid R) Na.
simpl in |- *.
apply (BUILD_HOM_MONOID (G:=ring_monoid R) (G':=Endo_SET N) (ff:=endofun)).
simpl in |- *.
intros x y H'; red in |- *.
simpl in |- *.
unfold subtype_image_equal in |- *.
simpl in |- *.
auto with algebra.
simpl in |- *.
intros x y; red in |- *.
simpl in |- *.
unfold subtype_image_equal in |- *.
simpl in |- *.
intros x0; try assumption.
exact (MODULE_assoc x y (subtype_elt x0)).
simpl in |- *.
red in |- *.
simpl in |- *.
unfold subtype_image_equal in |- *.
simpl in |- *.
intros x; try assumption.
exact (MODULE_unit_l (subtype_elt x)).
Defined.

Definition submodule_module : module R.
apply (Build_module (R:=R) (module_carrier:=Na)).
apply (Build_module_on (R:=R) (M:=Na) (module_op:=submodule_op)).
red in |- *.
simpl in |- *.
unfold subtype_image_equal in |- *.
simpl in |- *.
auto with algebra.
red in |- *.
simpl in |- *.
unfold subtype_image_equal in |- *.
simpl in |- *.
auto with algebra.
Defined.
End Sub_module.

Record submodule : Type := 
  {submodule_subgroup : subgroup M;
   submodule_prop :
    forall (a : R) (x : M),
    in_part x submodule_subgroup ->
    in_part (module_mult a x) submodule_subgroup}.

Definition module_of_submodule (N : submodule) :=
  submodule_module (submodule_prop (s:=N)).
End Def.
Coercion module_of_submodule : submodule >-> module.
Coercion submodule_subgroup : submodule >-> subgroup.
Section Injection.
Variable R : RING.
Variable M : MODULE R.
Variable N : submodule M.

Lemma submodule_in_prop :
 forall (a : R) (x : M), in_part x N -> in_part (module_mult a x) N.
intros a x H'; try assumption.
apply (submodule_prop (R:=R) (M:=M) (s:=N)); auto with algebra.
Qed.

Definition inj_submodule : Hom (N:MODULE R) M.
apply
 (BUILD_HOM_MODULE (R:=R) (Mod:=N:MODULE R) (Mod':=M)
    (ff:=fun x : N => subtype_elt x)); auto with algebra.
Defined.

Lemma inj_submodule_injective : injective inj_submodule.
red in |- *.
auto with algebra.
Qed.
End Injection.
Hint Resolve submodule_in_prop inj_submodule_injective: algebra.
