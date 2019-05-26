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
Section Free_group_def.
Variable V : SET.

Inductive FG : Type :=
  | Var : V -> FG
  | Law : FG -> FG -> FG
  | Unit : FG
  | Inv : FG -> FG.

Inductive eqFG : FG -> FG -> Prop :=
  | eqFG_Var : forall x y : V, Equal x y -> (eqFG (Var x) (Var y):Prop)
  | eqFG_law :
      forall x x' y y' : FG,
      eqFG x x' -> eqFG y y' -> (eqFG (Law x y) (Law x' y'):Prop)
  | eqFG_law_assoc :
      forall x y z : FG, eqFG (Law (Law x y) z) (Law x (Law y z)):Prop
  | eqFG_law0r : forall x : FG, eqFG (Law x Unit) x:Prop
  | eqFG_inv : forall x y : FG, eqFG x y -> eqFG (Inv x) (Inv y)
  | eqFG_invr : forall x : FG, eqFG (Law x (Inv x)) Unit
  | eqFG_refl : forall x : FG, eqFG x x:Prop
  | eqFG_sym : forall x y : FG, eqFG x y -> (eqFG y x:Prop)
  | eqFG_trans : forall x y z : FG, eqFG x y -> eqFG y z -> (eqFG x z:Prop).
Hint Resolve eqFG_Var eqFG_law eqFG_law_assoc eqFG_law0r eqFG_invr eqFG_refl:
  algebra.
Hint Immediate eqFG_sym: algebra.

Lemma eqFG_Equiv : equivalence eqFG.
red in |- *.
split; [ try assumption | idtac ].
exact eqFG_refl.
red in |- *.
split; [ try assumption | idtac ].
exact eqFG_trans.
exact eqFG_sym.
Qed.

Definition FG_set := Build_Setoid eqFG_Equiv.

Definition FreeGroup : GROUP.
apply (BUILD_GROUP (E:=FG_set) (genlaw:=Law) (e:=Unit) (geninv:=Inv)).
exact eqFG_law.
exact eqFG_law_assoc.
exact eqFG_law0r.
exact eqFG_inv.
exact eqFG_invr.
Defined.
Section Universal_prop.
Variable G : GROUP.
Variable f : Hom V G.

Fixpoint FG_lift_fun (p : FreeGroup) : G :=
  match p with
  | Var v => f v
  | Law p1 p2 => sgroup_law _ (FG_lift_fun p1) (FG_lift_fun p2)
  | Unit => monoid_unit G
  | Inv p1 => group_inverse G (FG_lift_fun p1)
  end.

Definition FG_lift : Hom FreeGroup G.
apply (BUILD_HOM_GROUP (G:=FreeGroup) (G':=G) (ff:=FG_lift_fun)).
intros x y H'; try assumption.
elim H'; simpl in |- *; auto with algebra.
intros x0 y0 z H'0 H'1 H'2 H'3; try assumption.
apply Trans with (FG_lift_fun y0); auto with algebra.
simpl in |- *; auto with algebra.
simpl in |- *; auto with algebra.
Defined.

Definition FG_var : Hom V FreeGroup.
apply (Build_Map (A:=V) (B:=FreeGroup) (Ap:=Var)).
red in |- *.
simpl in |- *; auto with algebra.
Defined.

Lemma FG_comp_prop :
 Equal f (comp_hom (FG_lift:Hom (FreeGroup:SET) G) FG_var).
simpl in |- *.
red in |- *.
simpl in |- *.
auto with algebra.
Qed.
End Universal_prop.
End Free_group_def.
Hint Resolve FG_comp_prop: algebra.
