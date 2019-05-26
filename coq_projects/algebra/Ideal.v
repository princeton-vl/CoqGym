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


Set Automatic Coercions Import.
Set Implicit Arguments.
Unset Strict Implicit.
Require Export Ring_facts.
Require Export Generated_module.
Section ideals.
Variable R : RING.

Definition is_ideal (I : subgroup R) :=
  forall x : R, in_part x I -> forall a : R, in_part (ring_mult a x) I.

Record ideal : Type := 
  {ideal_subgroup :> subgroup R; ideal_prf : is_ideal ideal_subgroup}.

Lemma ideal_prop :
 forall (I : ideal) (x : I) (a : R), in_part (ring_mult a (I x)) I.
intros I x a; try assumption.
apply (ideal_prf (i:=I)).
case x; simpl in |- *; auto with algebra.
Qed.

Lemma ideal_prop2 :
 forall (I : ideal) (x a : R), in_part x I -> in_part (ring_mult a x) I.
intros I x a H'; try assumption.
apply (ideal_prf (i:=I)); auto with algebra.
Qed.

Lemma ideal_prop3 :
 forall (I : ideal) (x y : R),
 in_part x I -> in_part y I -> in_part (sgroup_law R x y) I.
auto with algebra.
Qed.

Lemma ideal_prop4 :
 forall (I : ideal) (x : R), in_part x I -> in_part (group_inverse R x) I.
auto with algebra.
Qed.
End ideals.
Hint Resolve ideal_prop2: algebra.
Section Ring_as_module.
Variable R : ring.

Definition ring_module : module R.
apply
 (BUILD_MODULE_GROUP (R:=R) (module_util_G:=R)
    (gen_module_op:=fun a x : R => ring_mult a x));
 abstract auto with algebra.
Defined.
End Ring_as_module.
Coercion ring_module : ring >-> module.
Section Generated_ideal.
Variable R : RING.
Variable A : part_set R.

Definition generated_module_subgroup : subgroup R.
apply (BUILD_SUB_GROUP (G:=R) (H:=generated_module (R:=R) (Mod:=R) A));
 simpl in |- *; auto with algebra.
intros x y H' H'0; try assumption.
elim H'0; intros x0 E; elim E; intros H'1 H'2; try exact H'2; clear E H'0.
elim H'; intros x1 E; elim E; intros H'0 H'3; try exact H'3; clear E H'.
exists (Law x1 x0); split; [ try assumption | idtac ].
simpl in |- *.
exact (SGROUP_comp (E:=R) H'3 H'2).
exists (Unit R A); split; [ idtac | try assumption ].
auto with algebra.
simpl in |- *.
auto with algebra.
intros x H'; try assumption.
elim H'; intros x0 E; elim E; intros H'0 H'1; try exact H'1; clear E H'.
exists (Inv x0); split; [ idtac | try assumption ].
auto with algebra.
simpl in |- *.
exact (GROUP_comp (G:=R) H'1).
Defined.

Definition generated_ideal : ideal R.
apply (Build_ideal (R:=R) (ideal_subgroup:=generated_module_subgroup)).
red in |- *.
simpl in |- *.
intros x H' a; try assumption.
elim H'; intros x0 E; elim E; intros H'0 H'1; try exact H'1; clear E H'.
exists (Op a x0); split; [ idtac | try assumption ].
auto with algebra.
simpl in |- *.
exact (MODULE_comp (R:=R) (Mod:=R:MODULE R) (Refl a) H'1).
Defined.

Lemma generated_ideal_included : included A generated_ideal.
red in |- *.
simpl in |- *.
intros x H';
 exists (Var R (V:=A) (Build_subtype (E:=R) (P:=A) (subtype_elt:=x) H'));
 split; [ idtac | try assumption ].
auto with algebra.
simpl in |- *.
auto with algebra.
Qed.

Lemma generated_ideal_minimal :
 forall I : ideal R, included A I -> included generated_ideal I.
unfold included in |- *.
simpl in |- *.
intros I H' x H'0; try assumption.
elim H'0; intros x0 E; elim E; intros H'1 H'2; try exact H'2; clear E H'0.
generalize H'2; clear H'2; clear H'1.
generalize x; clear x.
elim x0.
simpl in |- *.
intros c x H'0; try assumption.
apply H'.
apply in_part_comp_l with (subtype_elt c); auto with algebra.
case c; auto with algebra.
intros f H'0 f0 H'1 x H'2; try assumption.
simpl in H'2.
apply
 in_part_comp_l
  with
    (sgroup_law R
       (FMd_lift_fun (R:=R) (V:=A) (Mod:=R:MODULE R) (inj_part A) f)
       (FMd_lift_fun (R:=R) (V:=A) (Mod:=R:MODULE R) (inj_part A) f0));
 auto with algebra.
simpl in |- *.
intros x H'0; try assumption.
apply in_part_comp_l with (monoid_unit R); auto with algebra.
intros f H'0 x H'1; try assumption.
simpl in H'1.
apply
 in_part_comp_l
  with
    (group_inverse R
       (FMd_lift_fun (R:=R) (V:=A) (Mod:=R:MODULE R) (inj_part A) f));
 auto with algebra.
intros c f H'0 x H'1; try assumption.
simpl in H'1.
apply
 in_part_comp_l
  with
    (module_mult c
       (FMd_lift_fun (R:=R) (V:=A) (Mod:=R:MODULE R) (inj_part A) f));
 auto with algebra.
change
  (in_part
     (ring_mult c
        (FMd_lift_fun (R:=R) (V:=A) (Mod:=R:MODULE R) (inj_part A) f))
     (subsgroup_part
        (submonoid_subsgroup (subgroup_submonoid (ideal_subgroup I)))))
 in |- *.
apply ideal_prop2; auto with algebra.
Qed.
End Generated_ideal.
Hint Resolve generated_ideal_minimal generated_ideal_included: algebra.
