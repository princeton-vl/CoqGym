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
Require Export Ring_cat.
Require Export Operation_of_monoid.
(** Title "The category of modules on a ring." *)
Section Def.
Variable R : RING.
Section Module_def.
Variable Mod : abelian_group.
Variable op : operation (ring_monoid R) Mod.

Definition op_lin_left :=
  forall (a b : R) (x : Mod),
  Equal (op (sgroup_law R a b) x) (sgroup_law Mod (op a x) (op b x)).

Definition op_lin_right :=
  forall (a : R) (x y : Mod),
  Equal (op a (sgroup_law Mod x y)) (sgroup_law Mod (op a x) (op a y)).
End Module_def.

Record module_on (M : abelian_group) : Type := 
  {module_op : operation (ring_monoid R) M;
   module_op_lin_left_prf : op_lin_left module_op;
   module_op_lin_right_prf : op_lin_right module_op}.

Record module : Type := 
  {module_carrier :> abelian_group;
   module_on_def :> module_on module_carrier}.
Coercion Build_module : module_on >-> module.

Definition module_mult (B : module) (a : R) (x : B) := module_op B a x.
Section Hom.
Variable E F : module.

Definition module_hom_prop (f : E -> F) :=
  forall (a : R) (x : E), Equal (f (module_mult a x)) (module_mult a (f x)).

Record module_hom : Type := 
  {module_monoid_hom :> monoid_hom E F;
   module_hom_prf : module_hom_prop module_monoid_hom}.
End Hom.

Definition module_hom_comp :
  forall E F Mod : module,
  module_hom F Mod -> module_hom E F -> module_hom E Mod.
intros E F Mod g f; try assumption.
apply
 (Build_module_hom (E:=E) (F:=Mod) (module_monoid_hom:=monoid_hom_comp g f)).
unfold module_hom_prop in |- *; auto with algebra.
simpl in |- *.
unfold comp_map_fun in |- *.
intros a x; try assumption.
apply
 Trans
  with
    (Ap (sgroup_map (monoid_sgroup_hom (module_monoid_hom g)))
       (module_mult a
          (Ap (sgroup_map (monoid_sgroup_hom (module_monoid_hom f))) x))).
cut
 (Equal
    (Ap (sgroup_map (monoid_sgroup_hom (module_monoid_hom f)))
       (module_mult a x))
    (module_mult a
       (Ap (sgroup_map (monoid_sgroup_hom (module_monoid_hom f))) x))).
auto with algebra.
apply (module_hom_prf f).
apply (module_hom_prf g).
Defined.

Definition module_id : forall E : module, module_hom E E.
intros E; try assumption.
apply (Build_module_hom (module_monoid_hom:=monoid_id E)).
red in |- *.
simpl in |- *; auto with algebra.
Defined.

Definition MODULE : category.
apply
 (subcat (C:=MONOID) (C':=module) (i:=module_carrier)
    (homC':=fun E F : module =>
            Build_subtype_image (E:=Hom (c:=ABELIAN_GROUP) E F)
              (subtype_image_carrier:=module_hom E F)
              (module_monoid_hom (E:=E) (F:=F))) (CompC':=module_hom_comp)
    (idC':=module_id)).
simpl in |- *.
intros a; try assumption.
red in |- *.
auto with algebra.
simpl in |- *.
intros a b c g f; try assumption.
red in |- *.
auto with algebra.
Defined.
End Def.