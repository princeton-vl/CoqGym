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


(** %\subsection*{ examples :  vecspace\_Mmn.v }%*)
(** - The vectorspace of $n\times m$ matrices over $F$ *)
Set Automatic Coercions Import.
Set Implicit Arguments.
Unset Strict Implicit.
Require Export Matrices.

Section Vectorspace.
Variable F : field.
Variable m n : Nat.

Definition Mmn_set : SET.
simpl in |- *.
apply
 (Build_Setoid (Carrier:=matrix F m n)
    (Equal:=fun M M' : matrix F m n =>
            forall (i i' : fin m) (j j' : fin n),
            i =' i' in _ -> j =' j' in _ -> M i j =' M' i' j' in _)).
split; try split; red in |- *; unfold app_rel in |- *.
(*Refl*)
intros.
elim x.
auto with algebra.
(*Trans*)
intros.
apply Trans with (y i j); auto with algebra.
(*Sym*)
intros.
apply Sym; auto with algebra.
Defined.

Let add_law : law_of_composition Mmn_set.
simpl in |- *.
exact (Map2_Mapcart (matrix_addition F m n:MAP2 Mmn_set Mmn_set Mmn_set)).
Defined.

Definition Mmn_sgp : SGROUP.
apply (Build_sgroup (sgroup_set:=Mmn_set)).
apply (Build_sgroup_on (sgroup_law_map:=add_law)).
red in |- *.
simpl in |- *.
destruct x; destruct y; destruct z.
simpl in |- *.
intros.
apply Trans with (Ap2 i' j' +' Ap0 i' j' +' Ap1 i' j'); auto with algebra.
Defined.

Definition Mmn_mon : MONOID.
apply (Build_monoid (monoid_sgroup:=Mmn_sgp)).
apply (Build_monoid_on (monoid_unit:=zero_matrix F m n:Mmn_sgp)); red in |- *;
 intros; simpl in |- *; destruct x.
intros; simpl in |- *.
apply Trans with (Ap2 i j); auto with algebra.
intros; simpl in |- *.
apply Trans with (Ap2 i j); auto with algebra.
Defined.

Section group.
Let minmatrix : Mmn_mon -> Mmn_mon.
intro M.
apply (Build_Map2 (Ap2:=fun i j => min M i j)).
red in |- *.
intros.
apply GROUP_comp; auto with algebra.
destruct M; auto with algebra.
Defined.

Let minmatrixmap : Map Mmn_mon Mmn_mon.
apply (Build_Map (Ap:=minmatrix)).
red in |- *.
intros; simpl in |- *.
destruct x; destruct y; simpl in |- *.
intros.
apply Trans with (min Ap0 i j); auto with algebra.
Defined.

Definition Mmn_gp : GROUP.
apply (Build_group (group_monoid:=Mmn_mon)).
apply (Build_group_on (group_inverse_map:=minmatrixmap)); red in |- *; intros;
 simpl in |- *; intros; auto with algebra.
Defined.
End group.

Definition Mmn_abgp : ABELIAN_GROUP.
apply (Build_abelian_group (abelian_group_group:=Mmn_gp)).
apply (Build_abelian_group_on (G:=Mmn_gp)).
apply (Build_abelian_monoid_on (M:=Mmn_gp)).
apply (Build_abelian_sgroup_on (A:=Mmn_gp)).
red in |- *.
simpl in |- *.
intros; destruct x; destruct y; simpl in |- *.
apply Trans with (Ap0 i j +' Ap2 i j); auto with algebra.
Defined.

Section module.
Let scmult_sgp_fun : F -> Endo_SET Mmn_abgp.
intro c.
simpl in |- *.
apply (Build_Map (Ap:=matrix_scmult F m n c)).
red in |- *.
case matrix_scmult.
unfold fun2_compatible in |- *.
intros.
apply Ap2_comp_proof; auto with algebra.
Defined.

Let scmult_sgp_map : Map (Build_monoid (ring_monoid F)) (Endo_SET Mmn_abgp).
apply (Build_Map (Ap:=scmult_sgp_fun)); auto with algebra.
red in |- *.
intros; unfold scmult_sgp_fun in |- *.
simpl in |- *.
red in |- *; simpl in |- *.
intros.
apply RING_comp; auto with algebra.
elim x0.
intros p q; red in q.
simpl in |- *; auto with algebra.
Defined.

Let scmult_sgp_hom :
  sgroup_hom (Build_monoid (ring_monoid F)) (Endo_SET Mmn_abgp).
apply (Build_sgroup_hom (sgroup_map:=scmult_sgp_map)).
red in |- *.
simpl in |- *.
red in |- *.
simpl in |- *.
intros.
destruct x0.
red in Ap2_comp_proof.
apply Trans with (x rX y rX Ap2 i j); auto with algebra.
simpl in |- *.
apply Trans with ((x rX y) rX Ap2 i j); auto with algebra.
Defined.

Let scmult_mon_hom :
  monoid_hom (Build_monoid (ring_monoid F)) (Endo_SET Mmn_abgp).
apply (Build_monoid_hom (monoid_sgroup_hom:=scmult_sgp_hom)).
red in |- *.
simpl in |- *.
red in |- *.
simpl in |- *.
intros.
destruct x.
red in Ap2_comp_proof.
simpl in |- *.
apply Trans with (Ap2 i j); auto with algebra.
apply Trans with (one rX Ap2 i j); auto with algebra.
Defined.

Definition Mmn : VECSP F.
apply (Build_module (R:=F) (module_carrier:=Mmn_abgp)).
apply (Build_module_on (module_op:=scmult_mon_hom)); red in |- *.
simpl in |- *; intros.
destruct x.
simpl in |- *.
apply Trans with (a rX Ap2 i j +' b rX Ap2 i j); auto with algebra.
simpl in |- *; intros.
apply Trans with (a rX x i j +' a rX y i j); auto with algebra.
destruct x; destruct y; (apply SGROUP_comp; auto with algebra).
Defined.
End module.
End Vectorspace.

Definition row_Map2 :
  forall (F : field) (m n : Nat), MAP2 (Mmn F m n) (fin m) (Fn F n).
intros.
apply (Build_Map2 (Ap2:=row (F:=F) (m:=m) (n:=n))).
red in |- *; simpl in |- *.
red in |- *; simpl in |- *.
intros.
destruct x; destruct x'; simpl in |- *.
simpl in H.
apply Trans with (Ap0 y x0); auto with algebra.
Defined.

Definition col_Map2 :
  forall (F : field) (m n : Nat), MAP2 (Mmn F m n) (fin n) (Fn F m).
intros.
apply (Build_Map2 (Ap2:=col (F:=F) (m:=m) (n:=n))).
red in |- *; simpl in |- *.
red in |- *; simpl in |- *.
intros.
destruct x; destruct x'; simpl in |- *.
simpl in H.
apply Trans with (Ap0 x0 y); auto with algebra.
Defined.