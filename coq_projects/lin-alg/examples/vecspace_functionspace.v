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


(** %\subsection*{ examples :  vecspace\_functionspace.v }%*)
(** - Another vectorspace, defined old-fashionedly. Fortunately, given vecspace_Fn, 
 this file is hardly more than cut-n-paste *)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export vecspaces_verybasic.
Require Export Map2.

Section Function_spaces.

Definition func_set (A B : Setoid) := MAP A B.

Let func_plus_fun :
  forall (A : Setoid) (B : sgroup),
  func_set A B -> func_set A B -> func_set A B.
intros A B f g.
simpl in |- *.
simpl in f.
simpl in g.
apply (Build_Map (A:=A) (B:=B) (Ap:=fun a : A => Ap f a +' Ap g a)).
red in |- *.
intros a a' Ha.
apply SGROUP_comp; auto with algebra.
Defined.

Definition func_plus :
  forall (A : Setoid) (B : sgroup), law_of_composition (func_set A B).
intros.
simpl in |- *.
apply Map2_Mapcart.
apply (Build_Map2 (Ap2:=func_plus_fun (A:=A) (B:=B))).
red in |- *.
intros f f' g g' Hf Hg.
unfold func_plus_fun in |- *.
simpl in |- *.
red in |- *.
intro a.
simpl in |- *.
apply SGROUP_comp; auto with algebra.
Defined.

Lemma func_plus_associative :
 forall (A : Setoid) (B : sgroup), associative (func_plus A B).
intros.
red in |- *.
intros f g h.
unfold func_plus in |- *.
simpl in |- *.
red in |- *.
intro a.
unfold func_plus_fun in |- *.
simpl in |- *.
apply SGROUP_assoc.
Qed.

Definition func_sgroup (A : Setoid) (B : sgroup) : SGROUP :=
  Build_sgroup (Build_sgroup_on (func_plus_associative (A:=A) (B:=B))).

Lemma func_plus_commutative :
 forall (A : Setoid) (B : abelian_sgroup), commutative (func_plus A B).
intros.
red in |- *.
intros f f'.
unfold func_plus in |- *.
simpl in |- *.
red in |- *.
intro a.
unfold func_plus_fun in |- *.
simpl in |- *.
apply ABELIAN_SGROUP_com.
Qed.

Definition func_absgp (A : Setoid) (B : abelian_sgroup) : ABELIAN_SGROUP :=
  Build_abelian_sgroup
    (Build_abelian_sgroup_on (A:=func_sgroup A B)
       (func_plus_commutative (A:=A) (B:=B))).

Definition func_zerofun : forall (A : Setoid) (B : monoid), func_set A B.
intros.
apply (Build_Map (Ap:=fun a : A => zero B)).
red in |- *.
intros.
apply Refl.
Defined.

Lemma func_zerofun_is_r_unit :
 forall (A : Setoid) (B : monoid),
 unit_r (sgroup_law_map (func_sgroup A B)) (func_zerofun A B).
intros A B.
red in |- *.
intro.
simpl in |- *.
red in |- *.
intro i.
simpl in |- *.
apply MONOID_unit_r.
Qed.

Lemma func_zerofun_is_l_unit :
 forall (A : Setoid) (B : monoid),
 unit_l (sgroup_law_map (func_sgroup A B)) (func_zerofun A B).
intros A B.
red in |- *.
intro.
simpl in |- *.
red in |- *.
intro i.
simpl in |- *.
apply MONOID_unit_l.
Qed.

Definition func_monoid (A : Setoid) (B : monoid) : MONOID :=
  Build_monoid
    (Build_monoid_on (A:=func_sgroup A B) (monoid_unit:=
       func_zerofun A B) (func_zerofun_is_r_unit (A:=A) (B:=B))
       (func_zerofun_is_l_unit (A:=A) (B:=B))).

Lemma func_monoid_is_abelian :
 forall (A : Setoid) (B : abelian_monoid),
 abelian_monoid_on (func_monoid A B).
intros.
apply Build_abelian_monoid_on.
apply Build_abelian_sgroup_on.
exact (func_plus_commutative (A:=A) (B:=B)).
Qed.

Definition func_abmon (A : Setoid) (B : abelian_monoid) : ABELIAN_MONOID :=
  Build_abelian_monoid (func_monoid_is_abelian A B).

Let func_inv_fun :
  forall (A : Setoid) (B : group), func_monoid A B -> func_monoid A B.
intros A B.
simpl in |- *.
intro v.
apply (Build_Map (Ap:=fun i : A => min v i)).
red in |- *.
intros i i' H.
apply GROUP_comp; auto with algebra.
Defined.

Definition func_inv :
  forall (A : Setoid) (B : group), Map (func_monoid A B) (func_monoid A B).
intros.
apply (Build_Map (Ap:=func_inv_fun (A:=A) (B:=B))).
red in |- *.
intros.
simpl in |- *.
red in |- *.
intro i.
simpl in H.
red in H.
simpl in |- *.
apply GROUP_comp; auto with algebra.
Defined.

Lemma func_inv_is_r_inverse :
 forall (A : Setoid) (B : group),
 inverse_r (func_plus A B) (func_zerofun A B) (func_inv A B).
intros.
red in |- *.
intro.
simpl in |- *.
red in |- *.
intro i.
simpl in |- *.
auto with algebra.
Qed.

Lemma func_inv_is_l_inverse :
 forall (A : Setoid) (B : group),
 inverse_l (func_plus A B) (func_zerofun A B) (func_inv A B).
intros.
red in |- *.
intro.
simpl in |- *.
red in |- *.
intro i.
simpl in |- *.
auto with algebra.
Qed.

Definition func_group (A : Setoid) (B : group) : GROUP :=
  Build_group
    (Build_group_on (group_inverse_map:=func_inv A B)
       (func_inv_is_r_inverse (A:=A) (B:=B))
       (func_inv_is_l_inverse (A:=A) (B:=B))).

Lemma func_group_is_abelian :
 forall (A : Setoid) (B : abelian_group), abelian_group_on (func_group A B).
intros.
apply Build_abelian_group_on.
apply Build_abelian_monoid_on.
apply Build_abelian_sgroup_on.
exact (func_plus_commutative (A:=A) (B:=B)).
Qed.

Definition func_abgp (A : Setoid) (B : abelian_group) : ABELIAN_GROUP :=
  Build_abelian_group (func_group_is_abelian A B).

Definition func_scmult_fun :
  forall (A : Setoid) (B : ring), B -> func_set A B -> func_set A B.
simpl in |- *.
intros A B c v.
apply (Build_Map (Ap:=fun i : A => c rX v i)).
red in |- *.
auto with algebra.
Defined.

Lemma func_scmult_fun_comp :
 forall (A : Setoid) (B : ring) (c c' : B) (v v' : func_set A B),
 c =' c' in _ ->
 v =' v' in _ -> func_scmult_fun c v =' func_scmult_fun c' v' in _.
intros A B.
simpl in |- *.
intros.
red in |- *.
intro i.
simpl in |- *.
apply RING_comp; auto with algebra.
Qed.

Section necessary_module_stuff.

Let func_scmult_fun_map :
  forall (A : Setoid) (B : ring), B -> MAP (func_set A B) (func_set A B).
intros A B c.
apply (Build_Map (Ap:=fun v : func_set A B => func_scmult_fun c v)).
red in |- *.
intros v v' H.
apply func_scmult_fun_comp; auto with algebra.
Defined.

Let func_scmult_F_to_EndoSet :
  forall (A : Setoid) (B : ring),
  Map (Build_monoid (ring_monoid B)) (Endo_SET (func_set A B)).
intros A B.
simpl in |- *.
apply (Build_Map (Ap:=fun c : B => func_scmult_fun_map A (B:=B) c)).
red in |- *.
intros c c' H.
simpl in |- *.
red in |- *.
intro v.
generalize
 (func_scmult_fun_comp (A:=A) (B:=B) (c:=c) (c':=c') (v:=v) (v':=v) H).
simpl in |- *.
generalize (Refl v).
intros.
simpl in H0.
apply H1; auto with algebra.
Defined.

Let func_scmult_sgroup_hom :
  forall (A : Setoid) (B : ring),
  sgroup_hom (Build_monoid (ring_monoid B)) (Endo_SET (func_set A B)).
intros.
apply (Build_sgroup_hom (sgroup_map:=func_scmult_F_to_EndoSet A B)).
red in |- *.
simpl in |- *.
red in |- *.
intros c c' v.
simpl in |- *.
red in |- *.
intro i.
simpl in |- *.
apply Trans with ((c rX c') rX v i); auto with algebra.
Defined.

Let func_scmult_monoid_hom :
  forall (A : Setoid) (B : ring),
  monoid_hom (Build_monoid (ring_monoid B)) (Endo_SET (func_set A B)).
intros A B.
apply (Build_monoid_hom (monoid_sgroup_hom:=func_scmult_sgroup_hom A B)).
red in |- *.
simpl in |- *.
red in |- *.
intro v.
simpl in |- *.
red in |- *.
intro i.
simpl in |- *.
apply Trans with (one rX v i); auto with algebra.
Defined.

Definition func_scmult :
  forall (A : Setoid) (B : ring),
  operation (Build_monoid (ring_monoid B)) (func_group A B).
simpl in |- *.
intros.
exact (func_scmult_monoid_hom A B).
Defined.

End necessary_module_stuff.

Lemma func_scmult_l_lin :
 forall (A : Setoid) (B : ring),
 op_lin_left (Mod:=func_abgp A B) (func_scmult A B).
red in |- *.
intros c c' v.
simpl in |- *.
red in |- *.
intro i.
simpl in |- *.
intros.
apply RING_dist_r.
Qed.

Lemma func_scmult_r_lin :
 forall (A : Setoid) (B : ring),
 op_lin_right (Mod:=func_abgp A B) (func_scmult A B).
intros A B.
red in |- *.
intros c c' v.
simpl in |- *.
red in |- *.
intro i.
simpl in |- *.
apply RING_dist_l.
Qed.

Definition func_mod (A : Setoid) (B : ring) : MODULE B :=
  Build_module
    (Build_module_on (func_scmult_l_lin (A:=A) (B:=B))
       (func_scmult_r_lin (A:=A) (B:=B))).

Definition func (A : Setoid) (B : field) : VECSP B :=
  func_mod A B:vectorspace B.

End Function_spaces.