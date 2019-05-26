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


(** * alt_build_vecsp.v *)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export vecspaces_verybasic.
Require Export Map2.


(** - It is very tedious to build up a vectorspace from scratch every time:
 One must build a setoid, then a semigroup, an abelian semigroup, a monoid,
 etc. etc. - hence this file: it provides a uniform way of building a
 vectorspace is one has proved the eight vectorspace axioms. *)

Section MAIN.
Variable V : Setoid.
Variable F : field.
Variable add : Map2 V V V.
Variable mlt : Map2 F V V.
Variable zer : V.
Variable mns : Map V V.
Definition VS1 := forall x y : V, add x y =' add y x in _.
Definition VS2 := forall x y z : V, add (add x y) z =' add x (add y z) in _.
Definition VS3 := forall x : V, add x zer =' x in _.
Definition VS4 := forall x : V, add x (mns x) =' zer in _.
Definition VS5 := forall x : V, mlt one x =' x in _.
Definition VS6 :=
  forall (a b : F) (x : V), mlt (a rX b) x =' mlt a (mlt b x) in _.
Definition VS7 :=
  forall (a : F) (x y : V), mlt a (add x y) =' add (mlt a x) (mlt a y) in _.
Definition VS8 :=
  forall (a b : F) (x : V), mlt (a +' b) x =' add (mlt a x) (mlt b x) in _.

Let Vsg_on : VS2 -> sgroup_on V.
intro VS2p.
apply (Build_sgroup_on (sgroup_law_map:=Map2_Mapcart add)).
red in |- *.
intros.
simpl in |- *.
auto with algebra.
Defined.

Let Vsg : VS2 -> sgroup.
intro VS2p.
apply (Build_sgroup (Vsg_on VS2p)).
Defined.

Let Vmon_on : VS1 -> forall VS2p : VS2, VS3 -> monoid_on (Vsg VS2p).
intros VS1p VS2p VS3p.
apply (Build_monoid_on (monoid_unit:=zer:Vsg VS2p)).
red in |- *; simpl in |- *.
auto.
red in |- *; simpl in |- *; intro.
apply Trans with (add x (zer:Vsg VS2p)); auto with algebra.
Defined.

Let Vmon : VS1 -> VS2 -> VS3 -> monoid.
intros VS1p VS2p VS3p.
apply (Build_monoid (Vmon_on VS1p VS2p VS3p)).
Defined.

Let Vgp_on :
  forall (VS1p : VS1) (VS2p : VS2) (VS3p : VS3),
  VS4 -> group_on (Vmon VS1p VS2p VS3p).
intros.
set (VMON := Vmon VS1p VS2p VS3p) in *.
apply (Build_group_on (group_inverse_map:=mns:Map VMON VMON)).
red in |- *; simpl in |- *.
auto with algebra.
red in |- *; simpl in |- *.
intro.
apply Trans with (add x (mns x)); auto with algebra.
Defined.

Let Vgp : VS1 -> VS2 -> VS3 -> VS4 -> group.
intros VS1p VS2p VS3p VS4p.
apply (Build_group (Vgp_on VS1p VS2p VS3p VS4p)).
Defined.

Let Vabgp_on :
  forall (VS1p : VS1) (VS2p : VS2) (VS3p : VS3) (VS4p : VS4),
  abelian_group_on (Vgp VS1p VS2p VS3p VS4p).
intros.
apply Build_abelian_group_on.
apply Build_abelian_monoid_on.
apply Build_abelian_sgroup_on.
red in |- *; simpl in |- *.
auto.
Defined.

Let Vabgp : VS1 -> VS2 -> VS3 -> VS4 -> abelian_group.
intros VS1p VS2p VS3p VS4p.
apply (Build_abelian_group (Vabgp_on VS1p VS2p VS3p VS4p)).
Defined.

Let F_act_map :
  forall (VS1p : VS1) (VS2p : VS2) (VS3p : VS3) (VS4p : VS4),
  Map (Build_monoid (ring_monoid F)) (Endo_SET (Vabgp VS1p VS2p VS3p VS4p)).
intros VS1p VS2p VS3p VS4p.
simpl in |- *.
apply (Build_Map (Ap:=fun c : F => Ap2_Map mlt c)).
red in |- *.
intros; destruct mlt; simpl in |- *.
red in |- *; simpl in |- *.
intro; auto with algebra.
Defined.

Let F_sgp_hom :
  forall (VS1p : VS1) (VS2p : VS2) (VS3p : VS3) (VS4p : VS4),
  VS6 ->
  sgroup_hom (Build_monoid (ring_monoid F))
    (Endo_SET (Vabgp VS1p VS2p VS3p VS4p)).
intros VS1p VS2p VS3p VS4p VS6p.
apply (Build_sgroup_hom (sgroup_map:=F_act_map VS1p VS2p VS3p VS4p)).
red in |- *.
intros; simpl in |- *.
red in |- *; simpl in |- *.
intro.
apply Trans with (mlt (x rX y) x0); auto with algebra.
Defined.

Let F_op :
  forall (VS1p : VS1) (VS2p : VS2) (VS3p : VS3) (VS4p : VS4),
  VS5 ->
  VS6 -> operation (Build_monoid (ring_monoid F)) (Vabgp VS1p VS2p VS3p VS4p).
intros VS1p VS2p VS3p VS4p VS5p VS6p.
apply
 (Build_monoid_hom (monoid_sgroup_hom:=F_sgp_hom VS1p VS2p VS3p VS4p VS6p)).
red in |- *.
simpl in |- *.
red in |- *.
intro; simpl in |- *.
apply Trans with (mlt one x); auto with algebra.
Defined.

Let Vmod_on :
  forall (VS1p : VS1) (VS2p : VS2) (VS3p : VS3) (VS4p : VS4),
  VS5 -> VS6 -> VS7 -> VS8 -> module_on F (Vabgp VS1p VS2p VS3p VS4p).
intros VS1p VS2p VS3p VS4p VS5p VS6p VS7p VS8p.
apply (Build_module_on (module_op:=F_op VS1p VS2p VS3p VS4p VS5p VS6p)).
red in |- *; simpl in |- *.
auto with algebra.
red in |- *.
intros.
simpl in |- *.
red in VS7p.
apply Trans with (mlt a (add x y)); auto with algebra.
apply Trans with (add (mlt a x) (mlt a y)); auto with algebra.
Defined.

Definition alt_Build_vectorspace :
  VS1 -> VS2 -> VS3 -> VS4 -> VS5 -> VS6 -> VS7 -> VS8 -> vectorspace F.
intros VS1p VS2p VS3p VS4p VS5p VS6p VS7p VS8p.
red in |- *.
simpl in |- *.
apply (Build_module (Vmod_on VS1p VS2p VS3p VS4p VS5p VS6p VS7p VS8p)).
Defined.

Definition vectorspace_construction :
  VS1 ->
  VS2 ->
  VS3 ->
  VS4 ->
  VS5 -> VS6 -> VS7 -> VS8 -> sigT (fun VV : vectorspace F => Carrier VV = V).
intros.
exists (alt_Build_vectorspace H H0 H1 H2 H3 H4 H5 H6).
simpl in |- *.
auto.
Defined.
End MAIN.