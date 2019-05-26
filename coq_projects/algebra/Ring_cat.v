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
Require Export Abelian_group_cat.
(** Title "The categories of abelian rings." *)
Section Objects.

Definition dist_r (E : SET) (f g : law_of_composition E) :=
  forall x y z : E,
  Equal (f (couple (g (couple x y)) z))
    (g (couple (f (couple x z)) (f (couple y z)))).

Definition dist_l (E : SET) (f g : law_of_composition E) :=
  forall x y z : E,
  Equal (f (couple x (g (couple y z))))
    (g (couple (f (couple x y)) (f (couple x z)))).

Record ring_on (R : abelian_group) : Type := 
  {ring_mult_sgroup : sgroup_on R;
   ring_mult_monoid : monoid_on ring_mult_sgroup;
   ring_monoid :> monoid_on ring_mult_monoid;
   ring_dist_r_prf :
    dist_r (sgroup_law_map ring_mult_sgroup) (sgroup_law_map R);
   ring_dist_l_prf :
    dist_l (sgroup_law_map ring_mult_sgroup) (sgroup_law_map R)}.

Record ring : Type := 
  {ring_group :> abelian_group; ring_on_def :> ring_on ring_group}.
Coercion Build_ring : ring_on >-> ring.

Definition ring_mult (R : ring) (x y : R) : R :=
  sgroup_law_map (ring_mult_sgroup R) (couple x y).

Definition ring_unit (R : ring) : R := monoid_unit (ring_monoid R).

Record cring_on (R : ring) : Type := 
  {cring_com_prf : commutative (sgroup_law_map (ring_mult_monoid R))}.

Record cring : Type := 
  {cring_ring :> ring; cring_on_def :> cring_on cring_ring}.
Coercion Build_cring : cring_on >-> cring.

Definition cring_monoid : cring -> abelian_monoid.
intros R; try assumption.
apply (Build_abelian_monoid (abelian_monoid_monoid:=ring_monoid R)).
apply (Build_abelian_monoid_on (M:=ring_monoid R)).
apply (Build_abelian_sgroup_on (A:=ring_monoid R)).
exact (cring_com_prf R).
Defined.
End Objects.
Section Hom.
Variable E F : ring.

Definition ring_mult_hom_unit_prop (f : Map E F) :=
  Equal (f (ring_unit E)) (ring_unit F).

Definition ring_mult_hom_prop (f : Map E F) :=
  forall x y : E, Equal (f (ring_mult x y)) (ring_mult (f x) (f y)).

Record ring_hom : Type := 
  {ring_plus_hom :> monoid_hom E F;
   ring_mult_hom_unit : ring_mult_hom_unit_prop ring_plus_hom;
   ring_mult_hom_prf : ring_mult_hom_prop ring_plus_hom}.
End Hom.

Definition ring_hom_comp :
  forall E F G : ring, ring_hom F G -> ring_hom E F -> ring_hom E G.
intros E F G g f; try assumption.
apply (Build_ring_hom (ring_plus_hom:=monoid_hom_comp g f)).
unfold ring_mult_hom_unit_prop in |- *; auto with algebra.
simpl in |- *.
unfold comp_map_fun in |- *.
apply
 Trans
  with (Ap (sgroup_map (monoid_sgroup_hom (ring_plus_hom g))) (ring_unit F));
 auto with algebra.
cut
 (Equal (Ap (sgroup_map (monoid_sgroup_hom (ring_plus_hom f))) (ring_unit E))
    (ring_unit F)).
auto with algebra.
apply (ring_mult_hom_unit f).
apply (ring_mult_hom_unit g).
unfold ring_mult_hom_prop in |- *; auto with algebra.
simpl in |- *.
unfold comp_map_fun in |- *.
intros x y; try assumption.
apply
 Trans
  with
    (Ap (sgroup_map (monoid_sgroup_hom (ring_plus_hom g)))
       (ring_mult (Ap (sgroup_map (monoid_sgroup_hom (ring_plus_hom f))) x)
          (Ap (sgroup_map (monoid_sgroup_hom (ring_plus_hom f))) y)));
 auto with algebra.
cut
 (Equal
    (Ap (sgroup_map (monoid_sgroup_hom (ring_plus_hom f))) (ring_mult x y))
    (ring_mult (Ap (sgroup_map (monoid_sgroup_hom (ring_plus_hom f))) x)
       (Ap (sgroup_map (monoid_sgroup_hom (ring_plus_hom f))) y))).
auto with algebra.
apply (ring_mult_hom_prf f).
apply (ring_mult_hom_prf g).
Defined.

Definition ring_id : forall E : ring, ring_hom E E.
intros E; try assumption.
apply (Build_ring_hom (ring_plus_hom:=monoid_id E)).
red in |- *.
simpl in |- *; auto with algebra.
red in |- *.
simpl in |- *; auto with algebra.
Defined.

Definition RING : category.
apply
 (subcat (C:=ABELIAN_GROUP) (C':=ring) (i:=ring_group)
    (homC':=fun E F : ring =>
            Build_subtype_image (E:=Hom (c:=ABELIAN_GROUP) E F)
              (subtype_image_carrier:=ring_hom E F)
              (ring_plus_hom (E:=E) (F:=F))) (CompC':=ring_hom_comp)
    (idC':=ring_id)).
simpl in |- *.
intros a; try assumption.
red in |- *.
auto with algebra.
simpl in |- *.
intros a b c g f; try assumption.
red in |- *.
auto with algebra.
Defined.

Definition CRING := full_subcat (C:=RING) (C':=cring) cring_ring.