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
Require Export Module_util.
Require Export Module_facts.
Section Free_Module_def.
Variable R : RING.
Variable V : SET.

Inductive FMd : Type :=
  | Var : V -> FMd
  | Law : FMd -> FMd -> FMd
  | Unit : FMd
  | Inv : FMd -> FMd
  | Op : R -> FMd -> FMd.

Inductive eqFMd : FMd -> FMd -> Prop :=
  | eqFMd_Var : forall x y : V, Equal x y -> (eqFMd (Var x) (Var y):Prop)
  | eqFMd_law :
      forall x x' y y' : FMd,
      eqFMd x x' -> eqFMd y y' -> (eqFMd (Law x y) (Law x' y'):Prop)
  | eqFMd_law_assoc :
      forall x y z : FMd, eqFMd (Law (Law x y) z) (Law x (Law y z)):Prop
  | eqFMd_law0r : forall x : FMd, eqFMd (Law x Unit) x:Prop
  | eqFMd_inv : forall x y : FMd, eqFMd x y -> eqFMd (Inv x) (Inv y)
  | eqFMd_invr : forall x : FMd, eqFMd (Law x (Inv x)) Unit
  | eqFMd_refl : forall x : FMd, eqFMd x x:Prop
  | eqFMd_sym : forall x y : FMd, eqFMd x y -> (eqFMd y x:Prop)
  | eqFMd_trans :
      forall x y z : FMd, eqFMd x y -> eqFMd y z -> (eqFMd x z:Prop)
  | eqFMd_com : forall x y : FMd, eqFMd (Law x y) (Law y x)
  | eqFMd_op_comp :
      forall (a b : R) (x y : FMd),
      Equal a b -> eqFMd x y -> (eqFMd (Op a x) (Op b y):Prop)
  | eqFMd_oplin_l :
      forall (a b : R) (x : FMd),
      eqFMd (Op (sgroup_law R a b) x) (Law (Op a x) (Op b x))
  | eqFMd_oplin_r :
      forall (a : R) (x y : FMd),
      eqFMd (Op a (Law x y)) (Law (Op a x) (Op a y))
  | eqFMd_op_assoc :
      forall (a b : R) (x : FMd),
      eqFMd (Op a (Op b x)) (Op (ring_mult a b) x)
  | eqFMd_op_unit : forall x : FMd, eqFMd (Op (ring_unit R) x) x.
Hint Resolve eqFMd_Var eqFMd_law eqFMd_law_assoc eqFMd_law0r eqFMd_invr
  eqFMd_refl: algebra.
Hint Immediate eqFMd_sym: algebra.

Lemma eqFMd_Equiv : equivalence eqFMd.
red in |- *.
split; [ try assumption | idtac ].
exact eqFMd_refl.
red in |- *.
split; [ try assumption | idtac ].
exact eqFMd_trans.
exact eqFMd_sym.
Qed.

Definition FMd_set := Build_Setoid eqFMd_Equiv.

Definition FreeModule : MODULE R.
apply
 (BUILD_MODULE (R:=R) (E:=FMd_set) (genlaw:=Law) (e:=Unit) (geninv:=Inv)
    (gen_module_op:=Op)).
exact eqFMd_law.
exact eqFMd_law_assoc.
exact eqFMd_law0r.
exact eqFMd_inv.
exact eqFMd_invr.
exact eqFMd_com.
exact eqFMd_op_comp.
exact eqFMd_oplin_l.
exact eqFMd_oplin_r.
exact eqFMd_op_assoc.
exact eqFMd_op_unit.
Defined.
Section Universal_prop.
Variable Mod : MODULE R.
Variable f : Hom V Mod.

Fixpoint FMd_lift_fun (p : FreeModule) : Mod :=
  match p with
  | Var v => f v
  | Law p1 p2 => sgroup_law Mod (FMd_lift_fun p1) (FMd_lift_fun p2)
  | Unit => monoid_unit Mod
  | Inv p1 => group_inverse Mod (FMd_lift_fun p1)
  | Op a p1 => module_mult a (FMd_lift_fun p1)
  end.

Definition FMd_lift : Hom FreeModule Mod.
apply
 (BUILD_HOM_MODULE (R:=R) (Mod:=FreeModule) (Mod':=Mod) (ff:=FMd_lift_fun)).
intros x y H'; try assumption.
elim H'; simpl in |- *; auto with algebra.
intros x0 y0 z H'0 H'1 H'2 H'3; try assumption.
apply Trans with (FMd_lift_fun y0); auto with algebra.
simpl in |- *; auto with algebra.
simpl in |- *; auto with algebra.
simpl in |- *; auto with algebra.
Defined.

Definition FMd_var : Hom V FreeModule.
apply (Build_Map (A:=V) (B:=FreeModule) (Ap:=Var)).
red in |- *.
simpl in |- *; auto with algebra.
Defined.

Lemma FMd_comp_prop :
 Equal f (comp_hom (FMd_lift:Hom (FreeModule:SET) Mod) FMd_var).
simpl in |- *.
red in |- *.
red in |- *.
simpl in |- *.
intros x; try assumption.
exact (Refl (f x)).
Qed.
End Universal_prop.
End Free_Module_def.
Hint Resolve FMd_comp_prop: algebra.
