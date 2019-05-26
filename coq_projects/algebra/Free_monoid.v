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
Require Export Monoid_cat.
Require Export Sgroup_facts.
Require Export Monoid_facts.
Require Export Monoid_util.
Section Free_monoid_def.
Variable V : SET.

Inductive FM : Type :=
  | Var : V -> FM
  | Law : FM -> FM -> FM
  | Unit : FM.

Inductive eqFM : FM -> FM -> Prop :=
  | eqFM_Var : forall x y : V, Equal x y -> (eqFM (Var x) (Var y):Prop)
  | eqFM_law :
      forall x x' y y' : FM,
      eqFM x x' -> eqFM y y' -> (eqFM (Law x y) (Law x' y'):Prop)
  | eqFM_law_assoc :
      forall x y z : FM, eqFM (Law (Law x y) z) (Law x (Law y z)):Prop
  | eqFM_law0r : forall x : FM, eqFM (Law x Unit) x:Prop
  | eqFM_law0l : forall x : FM, eqFM (Law Unit x) x:Prop
  | eqFM_refl : forall x : FM, eqFM x x:Prop
  | eqFM_sym : forall x y : FM, eqFM x y -> (eqFM y x:Prop)
  | eqFM_trans : forall x y z : FM, eqFM x y -> eqFM y z -> (eqFM x z:Prop).
Hint Resolve eqFM_Var eqFM_law eqFM_law_assoc eqFM_law0r eqFM_law0l
  eqFM_refl: algebra.
Hint Immediate eqFM_sym: algebra.

Lemma eqFM_Equiv : equivalence eqFM.
red in |- *.
split; [ try assumption | idtac ].
exact eqFM_refl.
red in |- *.
split; [ try assumption | idtac ].
exact eqFM_trans.
exact eqFM_sym.
Qed.

Definition FM_set := Build_Setoid eqFM_Equiv.

Definition FreeMonoid : MONOID.
apply (BUILD_MONOID (E:=FM_set) (genlaw:=Law) (e:=Unit)).
exact eqFM_law.
exact eqFM_law_assoc.
exact eqFM_law0r.
exact eqFM_law0l.
Defined.
Section Universal_prop.
Variable M : MONOID.
Variable f : Hom V M.

Fixpoint FM_lift_fun (p : FreeMonoid) : M :=
  match p with
  | Var v => f v
  | Law p1 p2 => sgroup_law _ (FM_lift_fun p1) (FM_lift_fun p2)
  | Unit => monoid_unit M
  end.

Definition FM_lift : Hom FreeMonoid M.
apply (BUILD_HOM_MONOID (G:=FreeMonoid) (G':=M) (ff:=FM_lift_fun)).
intros x y H'; try assumption.
elim H'; simpl in |- *; auto with algebra.
intros x0 y0 z H'0 H'1 H'2 H'3; try assumption.
apply Trans with (FM_lift_fun y0); auto with algebra.
simpl in |- *; auto with algebra.
simpl in |- *; auto with algebra.
Defined.

Definition FM_var : Hom V FreeMonoid.
apply (Build_Map (A:=V) (B:=FreeMonoid) (Ap:=Var)).
red in |- *.
simpl in |- *; auto with algebra.
Defined.

Lemma FM_comp_prop :
 Equal f (comp_hom (FM_lift:Hom (FreeMonoid:SET) M) FM_var).
simpl in |- *.
red in |- *.
simpl in |- *.
auto with algebra.
Qed.
End Universal_prop.
End Free_monoid_def.
Hint Resolve FM_comp_prop: algebra.