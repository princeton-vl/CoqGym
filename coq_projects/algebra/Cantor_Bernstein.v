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
Require Export Parts2.
(** Title "Cantor Bernstein theorem" *)
Comments
  "We prove that if there is an injection from A to B, and an injection from B to A".
Comments "then there is a bijection between A and B.".
Section Cantor_Bernstein.
Variable E F : Setoid.
Variable f : MAP E F.
Variable g : MAP F E.
Hypothesis finj : injective f.
Hypothesis ginj : injective g.

Let h (X : part_set E) := compl (image g (compl (image f X))).

Let h_incr : forall A B : part_set E, included A B -> included (h A) (h B).
unfold h in |- *.
auto with algebra.
Qed.
Hint Resolve h_incr: algebra.

Let PX : part_set (part_set E).
apply (Build_Predicate (Pred_fun:=fun A : part_set E => included A (h A))).
red in |- *.
intros x y H' H'0; try assumption.
apply included_comp with x (h x); auto with algebra.
unfold h in |- *.
auto with algebra.
Defined.

Let X := union_part PX.

Let XhX : included X (h X).
unfold X in |- *.
apply union_part_upper_bound.
intros A H'; try assumption.
apply included_trans with (h A); auto with algebra.
Qed.

Let hXX : included (h X) X.
unfold X in |- *.
apply union_part_included.
simpl in |- *.
apply h_incr.
exact XhX.
Qed.

Let PXeq : Equal (h X) X.
apply included_antisym.
exact hXX.
exact XhX.
Qed.
Hint Resolve PXeq hXX XhX: algebra.

Let img : Equal (image g (compl (image f X))) (compl X).
apply Trans with (compl (h X)); auto with algebra.
unfold h in |- *; auto with algebra.
Qed.
Hint Resolve img: algebra.
Hypothesis
  partial_section :
    forall (E F : Setoid) (f : MAP E F),
    injective f -> exists g : MAP F E, Equal (comp_map_map g f) (Id E).
Hypothesis
  map_extend :
    forall (E F : Setoid) (f g : MAP E F) (A : part_set E),
    exists b : MAP E F,
      (forall x : E, in_part x A -> Equal (b x) (f x)) /\
      (forall x : E, ~ in_part x A -> Equal (b x) (g x)).

Theorem Cantor_Berstein : exists b : MAP E F, bijective b.
case (partial_section ginj).
intros g1 H'; try assumption.
case (map_extend f g1 X).
intros b H'1; try assumption.
exists b; try assumption.
elim H'1; intros H'2 H'3; try exact H'2; clear H'1.
red in |- *.
split; [ try assumption | idtac ].
red in |- *.
intros x y H'0; try assumption.
case (compl_not_compl X x); intros.
case (compl_not_compl X y); intros.
apply finj.
apply Trans with (b y); auto with algebra.
apply Trans with (b x); auto with algebra.
apply Sym; auto with algebra.
cut (in_part y (image g (compl (image f X)))).
intros H'1; try assumption.
generalize (image_in H'1).
intros H'4; try assumption.
elim H'4; intros x0 E0; try exact E0; clear H'4.
elim E0; intros H'4 H'5; try exact H'5; clear E0.
absurd (in_part x0 (compl (image f X))); auto with algebra.
apply not_in_comp_l with (Ap (Id F) x0); auto with algebra.
apply not_in_comp_l with (Ap (comp_map_map g1 g) x0); auto with algebra.
apply not_in_comp_l with (Ap g1 (Ap g x0)); auto with algebra.
apply not_in_comp_l with (Ap g1 y); auto with algebra.
apply not_in_comp_l with (Ap b y); auto with algebra.
apply not_in_comp_l with (Ap b x); auto with algebra.
apply not_in_comp_l with (Ap f x); auto with algebra.
apply Sym; auto with algebra.
apply in_part_comp_r with (compl X); auto with algebra.
case (compl_not_compl X y); intros.
cut (in_part x (image g (compl (image f X)))).
intros H'1; try assumption.
generalize (image_in H'1).
intros H'4; try assumption.
elim H'4; intros x0 E0; try exact E0; clear H'4.
elim E0; intros H'4 H'5; try exact H'5; clear E0.
absurd (in_part x0 (compl (image f X))); auto with algebra.
apply not_in_comp_l with (Ap (Id F) x0); auto with algebra.
apply not_in_comp_l with (Ap (comp_map_map g1 g) x0); auto with algebra.
apply not_in_comp_l with (Ap g1 (Ap g x0)); auto with algebra.
apply not_in_comp_l with (Ap g1 x); auto with algebra.
apply not_in_comp_l with (Ap b x); auto with algebra.
apply not_in_comp_l with (Ap b y); auto with algebra.
apply not_in_comp_l with (Ap f y); auto with algebra.
apply Sym; auto with algebra.
apply in_part_comp_r with (compl X); auto with algebra.
cut (in_part x (image g (compl (image f X)))).
cut (in_part y (image g (compl (image f X)))).
intros H'1 H'4; try assumption.
generalize (image_in H'1).
generalize (image_in H'4).
intros H'5 H'6; try assumption.
elim H'6; intros x0 E0; elim E0; intros H'7 H'8; try exact H'7; clear E0 H'6.
elim H'5; intros x1 E0; elim E0; intros H'6 H'9; try exact H'6; clear E0 H'5.
apply Trans with (Ap g x1); auto with algebra.
apply Trans with (Ap g x0); auto with algebra.
cut (Equal x1 x0).
auto with algebra.
cut (Equal (Ap (Id F) x1) (Ap (Id F) x0)).
auto with algebra.
cut (Equal (Ap (comp_map_map g1 g) x1) (Ap (comp_map_map g1 g) x0)).
intros H'5; try assumption.
apply Trans with (Ap (comp_map_map g1 g) x0); auto with algebra.
apply Trans with (Ap (comp_map_map g1 g) x1); auto with algebra.
simpl in |- *.
unfold comp_map_fun in |- *.
apply Trans with (Ap g1 x); auto with algebra.
apply Trans with (Ap g1 y); auto with algebra.
apply Trans with (Ap b x); auto with algebra.
apply Sym; auto with algebra.
apply Trans with (Ap b y); auto with algebra.
apply in_part_comp_r with (compl X); auto with algebra.
apply in_part_comp_r with (compl X); auto with algebra.
red in |- *.
intros y; try assumption.
case (compl_not_compl (image f X) y); intros.
generalize (image_in H).
intros H'0; try assumption.
elim H'0; intros x E0; elim E0; intros H'1 H'4; try exact H'1; clear E0 H'0.
exists x; try assumption.
apply Trans with (Ap f x); auto with algebra.
apply Sym; auto with algebra.
exists (g y); try assumption.
apply Trans with (Ap g1 (Ap g y)); auto with algebra.
apply Sym.
apply Trans with (Ap (Id F) y); auto with algebra.
apply Trans with (Ap (comp_map_map g1 g) y); auto with algebra.
apply Sym.
apply H'3.
cut (in_part (Ap g y) (compl X)).
auto with algebra.
apply in_part_comp_r with (image g (compl (image f X))); auto with algebra.
Qed.
End Cantor_Bernstein.