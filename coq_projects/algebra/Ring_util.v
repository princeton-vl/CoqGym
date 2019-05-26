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
Require Export Monoid_util.
Require Export Ring_cat.
(** Title "Tools for building rings." *)
Section Ring.
Variable E : Setoid.
Variable ringplus : E -> E -> E.
Variable ringmult : E -> E -> E.
Variable zero : E.
Variable un : E.
Variable ringopp : E -> E.
Hypothesis
  ringpluscomp :
    forall x x' y y' : E,
    Equal x x' -> Equal y y' -> Equal (ringplus x y) (ringplus x' y').
Hypothesis
  ringplusassoc :
    forall x y z : E,
    Equal (ringplus (ringplus x y) z) (ringplus x (ringplus y z)).
Hypothesis zerounitringplusr : forall x : E, Equal (ringplus x zero) x.
Hypothesis
  oppcomp : forall x y : E, Equal x y -> Equal (ringopp x) (ringopp y).
Hypothesis ringoppr : forall x : E, Equal (ringplus x (ringopp x)) zero.
Hypothesis ringpluscom : forall x y : E, Equal (ringplus x y) (ringplus y x).
Hypothesis
  ringmultcomp :
    forall x x' y y' : E,
    Equal x x' -> Equal y y' -> Equal (ringmult x y) (ringmult x' y').
Hypothesis
  ringmultassoc :
    forall x y z : E,
    Equal (ringmult (ringmult x y) z) (ringmult x (ringmult y z)).
Hypothesis ununitringmultr : forall x : E, Equal (ringmult x un) x.
Hypothesis ununitlringmult : forall x : E, Equal (ringmult un x) x.
Hypothesis
  ringdistl :
    forall x y z : E,
    Equal (ringmult x (ringplus y z))
      (ringplus (ringmult x y) (ringmult x z)).
Hypothesis
  ringdistr :
    forall x y z : E,
    Equal (ringmult (ringplus x y) z)
      (ringplus (ringmult x z) (ringmult y z)).

Definition G :=
  BUILD_ABELIAN_GROUP ringpluscomp ringplusassoc zerounitringplusr oppcomp
    ringoppr ringpluscom.

Definition M :=
  BUILD_MONOID ringmultcomp ringmultassoc ununitringmultr ununitlringmult.

Definition BUILD_RING : RING.
apply (Build_ring (ring_group:=G)).
apply (Build_ring_on (R:=G) (ring_mult_sgroup:=M) (ring_mult_monoid:=M) M).
abstract (red in |- *; simpl in |- *; intros x y z;
           apply Trans with (ringmult (ringplus x y) z); 
           auto with algebra).
abstract (red in |- *; simpl in |- *; auto with algebra).
Defined.
End Ring.
Section Hom.
Variable Ring1 Ring2 : ring.
Variable ff : Ring1 -> Ring2.
Hypothesis ffcomp : forall x y : Ring1, Equal x y -> Equal (ff x) (ff y).
Hypothesis
  ffplus :
    forall x y : Ring1,
    Equal (ff (sgroup_law Ring1 x y)) (sgroup_law Ring2 (ff x) (ff y)).
Hypothesis ffzero : Equal (ff (monoid_unit Ring1)) (monoid_unit Ring2).
Hypothesis
  ffmult :
    forall x y : Ring1, Equal (ff (ring_mult x y)) (ring_mult (ff x) (ff y)).
Hypothesis ffone : Equal (ff (ring_unit Ring1)) (ring_unit Ring2).

Definition BUILD_HOM_RING : Hom (Ring1:RING) (Ring2:RING).
apply
 (Build_ring_hom (E:=Ring1) (F:=Ring2)
    (ring_plus_hom:=BUILD_HOM_GROUP ffcomp ffplus ffzero));
 abstract (red in |- *; simpl in |- *; auto with algebra).
Defined.
End Hom.