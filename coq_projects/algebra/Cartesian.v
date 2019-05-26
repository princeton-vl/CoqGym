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
Require Export Sets.
(** Title "Cartesian product of two sets." *)
Section Def.
Variable E F : Setoid.
Comments "The type of elements of a cartesian product:".

Record cart_type : Type :=  {cart_l : E; cart_r : F}.
Comments "Equality of couples:".

Definition cart_eq (x y : cart_type) :=
  Equal (cart_l x) (cart_l y) /\ Equal (cart_r x) (cart_r y).

Lemma cart_eq_equiv : equivalence cart_eq.
red in |- *.
split; [ try assumption | idtac ].
red in |- *.
intros x; red in |- *.
elim x.
unfold cart_eq in |- *; simpl in |- *; auto with algebra.
red in |- *.
split; [ idtac | try assumption ].
red in |- *.
unfold app_rel, cart_eq in |- *.
intros x y z H' H'0; split; [ try assumption | idtac ].
apply Trans with (cart_l y); intuition.
apply Trans with (cart_r y); intuition.
red in |- *.
unfold app_rel, cart_eq in |- *.
intuition.
Qed.

Definition cart : Setoid := Build_Setoid cart_eq_equiv.
Comments "We will denote the cartesian product of" E "and" F "with"
  (cart E F).
End Def.
Section Projections.
Variable E F : Setoid.

Definition proj1 (x : cart E F) : E := cart_l x.

Definition proj2 (x : cart E F) : F := cart_r x.
Comments "We note" (proj1 x) "and" (proj2 x) "the components of a couple" x
  "in " (cart E F).

Lemma proj1_comp :
 forall x y : cart E F, Equal x y -> Equal (proj1 x) (proj1 y).
red in |- *.
simpl in |- *.
unfold app_rel, cart_eq in |- *; intuition.
Qed.

Lemma proj2_comp :
 forall x y : cart E F, Equal x y -> Equal (proj2 x) (proj2 y).
red in |- *.
simpl in |- *.
unfold app_rel, cart_eq in |- *; intuition.
Qed.
Hint Resolve proj1_comp proj2_comp: algebra.

Definition proj1_map : MAP (cart E F) E := Build_Map proj1_comp.

Definition proj2_map : MAP (cart E F) F := Build_Map proj2_comp.

Definition couple (x : E) (y : F) : cart E F := Build_cart_type x y.

Lemma couple_comp :
 forall (x x' : E) (y y' : F),
 Equal x x' -> Equal y y' -> Equal (couple x y) (couple x' y').
simpl in |- *.
unfold app_rel, cart_eq in |- *; intuition.
Qed.
Hint Resolve couple_comp: algebra.

Lemma coupl_proj : forall x : cart E F, Equal (couple (proj1 x) (proj2 x)) x.
simpl in |- *.
unfold app_rel, cart_eq in |- *; intuition.
Qed.
Hint Resolve coupl_proj: algebra.
End Projections.
Section Maps.
Variable E F G : Setoid.

Definition curry (f : MAP (cart E F) G) (x : E) (y : F) := f (couple x y).

Definition fun2_compatible (f : E -> F -> G) :=
  forall (x x' : E) (y y' : F),
  Equal x x' -> Equal y y' -> Equal (f x y) (f x' y').

Definition uncurry :
  forall f : E -> F -> G, fun2_compatible f -> MAP (cart E F) G.
intros f H'; try assumption.
apply (Build_Map (Ap:=fun x : cart E F => f (proj1 x) (proj2 x))).
red in |- *.
intros x y; try assumption.
elim x.
elim y.
simpl in |- *.
unfold app_rel, cart_eq in |- *; intuition.
Defined.
Variable f : MAP E (cart F G).

Definition map_proj1 : MAP E F := comp_map_map (proj1_map F G) f.

Definition map_proj2 : MAP E G := comp_map_map (proj2_map F G) f.

Definition map_couple : MAP E F -> MAP E G -> MAP E (cart F G).
intros g h.
apply (Build_Map (Ap:=fun x : E => couple (g x) (h x))).
red in |- *.
intros x y H'; try assumption.
apply couple_comp; auto with algebra.
Defined.

Lemma map_couple_proj_prop : Equal (map_couple map_proj1 map_proj2) f.
simpl in |- *.
red in |- *.
unfold map_proj1, map_proj2 in |- *; simpl in |- *.
unfold app_rel, cart_eq in |- *; intuition.
Qed.
End Maps.
Hint Resolve proj1_comp proj2_comp couple_comp coupl_proj
  map_couple_proj_prop: algebra.