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
Require Export Group_util.
Require Export Abelian_group_facts.
Section Free_abelian_group_def.
Variable V : SET.

Inductive FaG : Type :=
  | Var : V -> FaG
  | Law : FaG -> FaG -> FaG
  | Unit : FaG
  | Inv : FaG -> FaG.

Inductive eqFaG : FaG -> FaG -> Prop :=
  | eqFaG_Var : forall x y : V, Equal x y -> (eqFaG (Var x) (Var y):Prop)
  | eqFaG_law :
      forall x x' y y' : FaG,
      eqFaG x x' -> eqFaG y y' -> (eqFaG (Law x y) (Law x' y'):Prop)
  | eqFaG_law_assoc :
      forall x y z : FaG, eqFaG (Law (Law x y) z) (Law x (Law y z)):Prop
  | eqFaG_law0r : forall x : FaG, eqFaG (Law x Unit) x:Prop
  | eqFaG_inv : forall x y : FaG, eqFaG x y -> eqFaG (Inv x) (Inv y)
  | eqFaG_invr : forall x : FaG, eqFaG (Law x (Inv x)) Unit
  | eqFaG_refl : forall x : FaG, eqFaG x x:Prop
  | eqFaG_sym : forall x y : FaG, eqFaG x y -> (eqFaG y x:Prop)
  | eqFaG_trans :
      forall x y z : FaG, eqFaG x y -> eqFaG y z -> (eqFaG x z:Prop)
  | eqFaG_com : forall x y : FaG, eqFaG (Law x y) (Law y x).
Hint Resolve eqFaG_Var eqFaG_law eqFaG_law_assoc eqFaG_law0r eqFaG_invr
  eqFaG_refl eqFaG_com: algebra.
Hint Immediate eqFaG_sym: algebra.

Lemma eqFaG_Equiv : equivalence eqFaG.
red in |- *.
split; [ try assumption | idtac ].
exact eqFaG_refl.
red in |- *.
split; [ try assumption | idtac ].
exact eqFaG_trans.
exact eqFaG_sym.
Qed.

Definition FaG_set := Build_Setoid eqFaG_Equiv.

Definition FreeAbelianGroup : ABELIAN_GROUP.
apply
 (BUILD_ABELIAN_GROUP (E:=FaG_set) (genlaw:=Law) (e:=Unit) (geninv:=Inv)).
exact eqFaG_law.
exact eqFaG_law_assoc.
exact eqFaG_law0r.
exact eqFaG_inv.
exact eqFaG_invr.
exact eqFaG_com.
Defined.
Section Universal_prop.
Variable G : ABELIAN_GROUP.
Variable f : Hom V G.

Fixpoint FaG_lift_fun (p : FreeAbelianGroup) : G :=
  match p with
  | Var v => f v
  | Law p1 p2 => sgroup_law _ (FaG_lift_fun p1) (FaG_lift_fun p2)
  | Unit => monoid_unit G
  | Inv p1 => group_inverse G (FaG_lift_fun p1)
  end.

Definition FaG_lift : Hom FreeAbelianGroup G.
apply (BUILD_HOM_GROUP (G:=FreeAbelianGroup) (G':=G) (ff:=FaG_lift_fun)).
intros x y H'; try assumption.
elim H'; simpl in |- *; auto with algebra.
intros x0 y0 z H'0 H'1 H'2 H'3; try assumption.
apply Trans with (FaG_lift_fun y0); auto with algebra.
simpl in |- *; auto with algebra.
simpl in |- *; auto with algebra.
Defined.

Definition FaG_var : Hom V FreeAbelianGroup.
apply (Build_Map (A:=V) (B:=FreeAbelianGroup) (Ap:=Var)).
red in |- *.
simpl in |- *; auto with algebra.
Defined.

Lemma FaG_comp_prop :
 Equal f (comp_hom (FaG_lift:Hom (FreeAbelianGroup:SET) G) FaG_var).
simpl in |- *.
red in |- *.
simpl in |- *.
auto with algebra.
Qed.
End Universal_prop.
End Free_abelian_group_def.
Hint Resolve FaG_comp_prop: algebra.
