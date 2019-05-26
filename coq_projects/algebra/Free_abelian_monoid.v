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
Require Export Abelian_group_facts.
Section Free_abelian_monoid_def.
Variable V : SET.

Inductive FaM : Type :=
  | Var : V -> FaM
  | Law : FaM -> FaM -> FaM
  | Unit : FaM.

Inductive eqFaM : FaM -> FaM -> Prop :=
  | eqFaM_Var : forall x y : V, Equal x y -> (eqFaM (Var x) (Var y):Prop)
  | eqFaM_law :
      forall x x' y y' : FaM,
      eqFaM x x' -> eqFaM y y' -> (eqFaM (Law x y) (Law x' y'):Prop)
  | eqFaM_law_assoc :
      forall x y z : FaM, eqFaM (Law (Law x y) z) (Law x (Law y z)):Prop
  | eqFaM_law0r : forall x : FaM, eqFaM (Law x Unit) x:Prop
  | eqFaM_law0l : forall x : FaM, eqFaM (Law Unit x) x:Prop
  | eqFaM_refl : forall x : FaM, eqFaM x x:Prop
  | eqFaM_sym : forall x y : FaM, eqFaM x y -> (eqFaM y x:Prop)
  | eqFaM_trans :
      forall x y z : FaM, eqFaM x y -> eqFaM y z -> (eqFaM x z:Prop)
  | eqFaM_com : forall x y : FaM, eqFaM (Law x y) (Law y x).
Hint Resolve eqFaM_Var eqFaM_law eqFaM_law_assoc eqFaM_law0r eqFaM_law0l
  eqFaM_refl eqFaM_com: algebra.
Hint Immediate eqFaM_sym: algebra.

Lemma eqFaM_Equiv : equivalence eqFaM.
red in |- *.
split; [ try assumption | idtac ].
exact eqFaM_refl.
red in |- *.
split; [ try assumption | idtac ].
exact eqFaM_trans.
exact eqFaM_sym.
Qed.

Definition FaM_set := Build_Setoid eqFaM_Equiv.

Definition FreeAbelianMonoid : ABELIAN_MONOID.
apply (BUILD_ABELIAN_MONOID (E:=FaM_set) (genlaw:=Law) (e:=Unit)).
exact eqFaM_law.
exact eqFaM_law_assoc.
exact eqFaM_law0r.
exact eqFaM_law0l.
exact eqFaM_com.
Defined.
Section Universal_prop.
Variable M : ABELIAN_MONOID.
Variable f : Hom V M.

Fixpoint FaM_lift_fun (p : FreeAbelianMonoid) : M :=
  match p with
  | Var v => f v
  | Law p1 p2 => sgroup_law _ (FaM_lift_fun p1) (FaM_lift_fun p2)
  | Unit => monoid_unit M
  end.

Definition FaM_lift : Hom FreeAbelianMonoid M.
apply (BUILD_HOM_MONOID (G:=FreeAbelianMonoid) (G':=M) (ff:=FaM_lift_fun)).
intros x y H'; try assumption.
elim H'; simpl in |- *; auto with algebra.
intros x0 y0 z H'0 H'1 H'2 H'3; try assumption.
apply Trans with (FaM_lift_fun y0); auto with algebra.
simpl in |- *; auto with algebra.
simpl in |- *; auto with algebra.
Defined.

Definition FaM_var : Hom V FreeAbelianMonoid.
apply (Build_Map (A:=V) (B:=FreeAbelianMonoid) (Ap:=Var)).
red in |- *.
simpl in |- *; auto with algebra.
Defined.

Lemma FaM_comp_prop :
 Equal f (comp_hom (FaM_lift:Hom (FreeAbelianMonoid:SET) M) FaM_var).
simpl in |- *.
red in |- *.
simpl in |- *.
auto with algebra.
Qed.
End Universal_prop.
End Free_abelian_monoid_def.
Hint Resolve FaM_comp_prop: algebra.