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
Require Export Sub_monoid.
Require Export Group_facts.
Section Def.
Variable G : GROUP.
Section Sub_group.
Variable H : submonoid G.
Hypothesis Hinv : forall x : G, in_part x H -> in_part (group_inverse _ x) H.

Definition subgroup_inv : MAP H H.
apply
 (Build_Map (A:=H) (B:=H)
    (Ap:=fun x : H => Build_subtype (Hinv (subtype_prf x)))).
red in |- *.
simpl in |- *.
unfold subtype_image_equal in |- *.
simpl in |- *.
auto with algebra.
Defined.

Definition subgroup_group : group.
apply (Build_group (group_monoid:=H)).
apply (Build_group_on (G:=H) (group_inverse_map:=subgroup_inv)).
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
End Sub_group.

Record subgroup : Type := 
  {subgroup_submonoid : submonoid G;
   subgroup_prop :
    forall x : G,
    in_part x subgroup_submonoid ->
    in_part (group_inverse _ x) subgroup_submonoid}.

Definition group_of_subgroup (H : subgroup) :=
  subgroup_group (subgroup_prop (s:=H)).
End Def.
Coercion group_of_subgroup : subgroup >-> group.
Coercion subgroup_submonoid : subgroup >-> submonoid.
Section Injection.
Variable G : GROUP.
Variable H : subgroup G.

Lemma subgroup_in_prop :
 forall x : G, in_part x H -> in_part (group_inverse _ x) H.
intros x H'; try assumption.
apply (subgroup_prop (G:=G) (s:=H)); auto with algebra.
Qed.

Definition inj_subgroup : Hom (H:GROUP) G.
apply (Build_monoid_hom (E:=H) (F:=G) (monoid_sgroup_hom:=inj_subsgroup H)).
red in |- *.
auto with algebra.
Defined.

Lemma inj_subgroup_injective : injective inj_subgroup.
red in |- *.
auto with algebra.
Qed.
End Injection.
Hint Resolve subgroup_in_prop inj_subgroup_injective: algebra.