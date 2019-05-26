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
Require Export Fpart2.
Section tiroirs_def.
Variable E F : Setoid.
Variable f : MAP E F.

Lemma diff_add_part2 :
 forall (E : Setoid) (A : part_set E) (x : E),
 in_part x A -> Equal A (add_part (diff A (single x)) x).
intros E0 A x H'; try assumption.
apply in_eq_part.
intros x0 H'0; try assumption.
elim (classic (Equal x x0)); intros.
apply in_part_trans_eq with x; auto with *.
cut (in_part x0 (diff A (single x))).
unfold add_part in |- *; auto with *.
apply in_diff; auto with *.
intros x0 H'0; try assumption.
elim (classic (Equal x x0)); intros.
apply in_part_trans_eq with x; auto with *.
cut (in_part x0 (diff A (single x))).
intros H'1; try assumption.
apply diff_in_l with (single x).
auto with *.
unfold add_part in H'0.
elim (in_part_union H'0); intros.
auto with *.
absurd (Equal x x0); auto with *.
Qed.
Hint Resolve diff_add_part2: algebra.

Lemma cardinal_minus_part :
 forall (B : part_set F) (x : F) (n : nat),
 cardinal B (S n) -> in_part x B -> cardinal (diff B (single x)) n.
intros B x n H' H'0; try assumption.
apply cardinal_S with B x; auto with *.
unfold not in |- *; intros.
cut (~ in_part x (single x)).
unfold not in |- *; auto with *.
apply diff_in_r with B; auto with *.
Qed.
Hint Resolve cardinal_minus_part: algebra.

Lemma tiroirs :
 forall (n : nat) (Chaussettes : part_set E),
 cardinal Chaussettes n ->
 forall (m : nat) (Tiroirs : part_set F),
 cardinal Tiroirs m ->
 m < n ->
 (forall x : E, in_part x Chaussettes -> in_part (f x) Tiroirs) ->
 exists x : E, (exists y : E, ~ Equal x y /\ Equal (f x) (f y)).
simple induction n.
intros Chaussettes H' m Tiroirs H'0 H'1; try assumption.
inversion H'1.
intros n0 H' Chaussettes H'0 m Tiroirs H'1 H'2 H'3; try assumption.
inversion H'0.
elim (classic (ex (fun y : E => ~ Equal x y /\ Equal (Ap f x) (Ap f y))));
 intros.
exists x; try assumption.
cut (exists m0 : nat, m = S m0).
intros H'4; try assumption.
case H'4; clear H'4; intros.
apply H' with (diff Chaussettes (single x)) x0 (diff Tiroirs (single (f x))).
apply cardinal_S with Chaussettes x.
unfold not in |- *; intros.
absurd (~ in_part x (single x)); auto with *.
apply diff_in_r with Chaussettes; auto with *.
auto with *.
apply diff_add_part2.
apply in_part_comp_r with (add_part B x); auto with *.
auto with *.
apply cardinal_minus_part.
rewrite <- H5; auto with *.
apply H'3; auto with *.
apply in_part_comp_r with (add_part B x).
auto with *.
auto with *.
rewrite H5 in H'2; auto with *.
intros x1 H'4; try assumption.
apply in_diff.
apply H'3; auto with *.
apply diff_in_l with (single x); auto with *.
unfold not in |- *; intros.
unfold not in H4.
apply H4.
exists x1; try assumption.
split.
intros H'5; try assumption.
cut (~ in_part x1 (single x)).
intro.
apply H7.
apply in_part_trans_eq with x; auto with *.
apply diff_in_r with Chaussettes; auto with *.
auto with *.
inversion H'1.
cut (in_part (f x) Tiroirs).
intros H'4; try assumption.
absurd (in_part (f x) (empty F)); auto with *.
apply in_part_comp_r with Tiroirs; auto with *.
apply H'3.
apply in_part_comp_r with (add_part B x); auto with *.
exists n2; try assumption.
auto with *.
Qed.
End tiroirs_def.
