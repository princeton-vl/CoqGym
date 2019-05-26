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
Require Export Fpart.
Require Export Inter.
Require Export Arith.
Section fparts2_def.
Variable E : Setoid.

Definition disjoint (A B : part_set E) := Equal (inter A B) (empty E).

Lemma disjoint_comp :
 forall A A' B B' : part_set E,
 Equal A A' -> Equal B B' -> disjoint A B -> disjoint A' B'.
unfold disjoint in |- *.
intros A A' B B' H' H'0 H'1; try assumption.
apply Trans with (inter A B).
auto with *.
auto with *.
Qed.

Lemma empty_not_in :
 forall A : part_set E, Equal A (empty E) -> forall x : E, ~ in_part x A.
intros A; case A; intros a pa; simpl in |- *.
unfold eq_part, empty in |- *; simpl in |- *.
intuition.
intros.
elim (H x); auto with *.
Qed.

Lemma disjoint_inclus :
 forall A B C : part_set E, included A B -> disjoint B C -> disjoint A C.
unfold included, disjoint in |- *.
intros A B C H' H'0; try assumption.
apply not_in_empty.
unfold not in |- *; intros.
cut (in_part x (inter B C)).
generalize (empty_not_in (A:=inter B C) H'0).
unfold not in |- *; intros.
apply H0 with (x := x).
auto with *.
auto with *.
apply in_part_inter.
apply H'.
apply in_part_inter_l with C.
auto with *.
apply in_part_inter_r with A.
auto with *.
Qed.

Lemma included_add_part :
 forall (A : part_set E) (x : E), included A (add_part A x).
intros A x; red in |- *.
unfold add_part in |- *.
auto with *.
Qed.
Hint Resolve included_add_part: algebra.

Lemma union_not_in :
 forall (A B : part_set E) (x : E),
 ~ in_part x A -> ~ in_part x B -> ~ in_part x (union A B).
unfold not in |- *; intros.
cut (in_part x A \/ in_part x B).
intros H'; try assumption.
intuition.
auto with *.
Qed.
Hint Resolve union_not_in: algebra.

Lemma disjoint_not_in_r :
 forall (A B : part_set E) (x : E),
 disjoint A B -> in_part x A -> ~ in_part x B.
unfold disjoint in |- *.
unfold not in |- *; intros.
cut (in_part x (empty E)).
auto with *.
apply in_part_comp_r with (inter A B).
auto with *.
auto with *.
Qed.

Lemma cardinal_union_disjoint :
 forall (a b : nat) (A B : part_set E),
 cardinal A a -> cardinal B b -> disjoint A B -> cardinal (union A B) (a + b).
simple induction a.
intros.
apply cardinal_comp_l with (union (empty E) B); auto with *.
apply union_comp; auto with *.
apply Sym.
auto with *.
apply cardinal_comp_l with B; auto with *.
intros.
inversion H0.
simpl in |- *.
apply cardinal_add with (union B0 B) x; auto with *.
apply H; auto with *.
apply disjoint_inclus with (add_part B0 x); auto with *.
apply disjoint_comp with A B; auto with *.
apply union_not_in; auto with *.
apply disjoint_not_in_r with A; auto with *.
apply in_part_comp_r with (add_part B0 x); auto with *.
apply Trans with (union (add_part B0 x) B); auto with *.
unfold add_part in |- *.
apply Trans with (union B0 (union (single x) B)); auto with *.
apply Trans with (union B0 (union B (single x))); auto with *.
Qed.
Hint Resolve cardinal_union_disjoint: algebra.

Lemma in_eq_part :
 forall A B : part_set E,
 (forall x : E, in_part x A -> in_part x B) ->
 (forall x : E, in_part x B -> in_part x A) -> Equal A B.
intros A B.
case A; case B; simpl in |- *.
intros a pa b pb.
unfold eq_part in |- *; simpl in |- *.
intuition.
Qed.

Lemma diff_in_l :
 forall (A B : part_set E) (x : E), in_part x (diff A B) -> in_part x A.
intros A B.
case A; case B; simpl in |- *.
intros a pa b pb.
unfold eq_part in |- *; simpl in |- *.
intuition.
Qed.

Lemma diff_in_r :
 forall (A B : part_set E) (x : E), in_part x (diff A B) -> ~ in_part x B.
intros A B.
case A; case B; simpl in |- *.
intros a pa b pb.
unfold eq_part in |- *; simpl in |- *.
intuition.
Qed.

Lemma in_diff :
 forall (A B : part_set E) (x : E),
 in_part x A -> ~ in_part x B -> in_part x (diff A B).
intros A B.
case A; case B; simpl in |- *.
intros a pa b pb.
unfold eq_part in |- *; simpl in |- *.
intuition.
Qed.
Hint Resolve in_diff: algebra.

Lemma union_diff :
 forall A B : part_set E, Equal (union A (diff B A)) (union A B).
intros A B; try assumption.
apply in_eq_part.
intros x H'; try assumption.
elim (in_part_union H').
auto with *.
intros H'0; try assumption.
cut (in_part x B).
auto with *.
exact (diff_in_l H'0).
intros x H'; try assumption.
elim (in_part_union H').
auto with *.
intros H'0; try assumption.
elim (classic (in_part x A)).
auto with *.
intros H'1; try assumption.
cut (in_part x (diff B A)).
auto with *.
auto with *.
Qed.
Hint Resolve union_diff: algebra.

Lemma disjoint_diff : forall A B : part_set E, disjoint A (diff B A).
red in |- *.
intros A B; try assumption.
apply not_in_empty.
intros x; red in |- *; intros H'; try exact H'.
absurd (in_part x A).
apply diff_in_r with B.
auto with *.
apply in_part_inter_r with A; auto with *.
apply in_part_inter_l with (diff B A); auto with *.
Qed.
Hint Resolve disjoint_diff: algebra.

Lemma cardinal_union :
 forall (a b : nat) (A B : part_set E),
 cardinal A a -> cardinal (diff B A) b -> cardinal (union A B) (a + b).
intros.
apply cardinal_comp_l with (union A (diff B A)); auto with *.
Qed.
Hint Resolve cardinal_union: algebra.

Lemma empty_diff : forall A : part_set E, Equal (diff (empty E) A) (empty E).
intros A; try assumption.
apply in_eq_part.
intro.
intros H'; try assumption.
apply diff_in_l with A; auto with *.
intros x H'; try assumption.
absurd (in_part x (empty E)); auto with *.
Qed.
Hint Resolve empty_diff: algebra.

Lemma empty_inter :
 forall A : part_set E, Equal (inter (empty E) A) (empty E).
intros A; try assumption.
apply in_eq_part.
intros x H'; try assumption.
apply in_part_inter_l with A; auto with *.
intros x H'; try assumption.
absurd (in_part x (empty E)); auto with *.
Qed.
Hint Resolve empty_inter: algebra.

Lemma in_part_trans_eq :
 forall (A : part_set E) (x y : E), in_part x A -> Equal y x -> in_part y A.
intros A; case A; simpl in |- *.
intros a pa.
intros x y H' H'0; try assumption.
apply pa with x; auto with *.
Qed.

Lemma diff_add_part :
 forall (A B0 B : part_set E) (x : E),
 ~ in_part x B0 ->
 Equal A (add_part B0 x) -> in_part x B -> Equal (diff B0 B) (diff A B).
intros A B0 B x H' H'0 H'1; try assumption.
apply in_eq_part.
intros x0 H'2; try assumption.
apply in_diff.
apply in_part_comp_r with (add_part B0 x).
cut (in_part x0 B0).
unfold add_part in |- *.
auto with *.
apply diff_in_l with B; auto with *.
auto with *.
apply diff_in_r with B0; auto with *.
intros x0 H'2; try assumption.
elim (classic (Equal x0 x)).
intros H'3; try assumption.
absurd (in_part x B); auto with *.
cut (in_part x (diff A B)).
intros H'4; try assumption.
apply diff_in_r with A; auto with *.
apply in_part_trans_eq with x0; auto with *.
intros H'3; try assumption.
apply in_diff.
apply add_part_in_el_diff with x; auto with *.
apply in_part_comp_r with A; auto with *.
apply diff_in_l with B; auto with *.
apply diff_in_r with A; auto with *.
Qed.

Lemma diff_not_in :
 forall (A B : part_set E) (x : E), ~ in_part x A -> ~ in_part x (diff A B).
unfold not in |- *; intros.
apply H.
apply diff_in_l with B; auto with *.
Qed.
Hint Resolve diff_not_in: algebra.

Lemma inter_not_in :
 forall (A B : part_set E) (x : E), ~ in_part x A -> ~ in_part x (inter A B).
unfold not in |- *; intros.
apply H.
apply in_part_inter_l with B; auto with *.
Qed.
Hint Resolve inter_not_in: algebra.
(* OK *)

Lemma inter_add_part :
 forall (A B0 B : part_set E) (x : E),
 ~ in_part x B0 ->
 Equal A (add_part B0 x) ->
 in_part x B -> Equal (inter A B) (add_part (inter B0 B) x).
unfold add_part in |- *.
intros A B0 B x H' H'0 H'1; try assumption.
apply Trans with (inter (union B0 (single x)) B).
auto with *.
apply Trans with (union (inter B0 B) (inter (single x) B)).
auto with *.
apply union_comp; auto with *.
apply in_eq_part.
intros x0 H'2; try assumption.
apply in_part_inter_l with B; auto with *.
intros x0 H'2; try assumption.
apply in_part_inter; auto with *.
apply in_part_trans_eq with x; auto with *.
Qed.
Hint Resolve inter_add_part: algebra.

Lemma diff_add_part_not_in :
 forall (A B0 B : part_set E) (x : E),
 ~ in_part x B0 ->
 Equal A (add_part B0 x) ->
 ~ in_part x B -> Equal (diff A B) (add_part (diff B0 B) x).
intros A B0 B x H' H'0 H'1; try assumption.
apply in_eq_part.
intros x0 H'2; try assumption.
elim (classic (Equal x0 x)).
intros H'3; try assumption.
apply in_part_trans_eq with x; auto with *.
intros H'3; try assumption.
unfold add_part in |- *.
apply in_part_union_or.
left.
apply in_diff.
apply add_part_in_el_diff with x; auto with *.
apply in_part_comp_r with A; auto with *.
apply diff_in_l with B; auto with *.
apply diff_in_r with A; auto with *.
intros x0 H'2; try assumption.
apply in_diff.
apply in_part_comp_r with (add_part B0 x); auto with *.
elim (classic (Equal x0 x)).
intros H'3; try assumption.
apply in_part_trans_eq with x; auto with *.
intros H'3; try assumption.
unfold add_part in |- *.
apply in_part_union_or.
left.
unfold add_part in H'2.
elim (in_part_union H'2).
intros H'4; try assumption.
apply diff_in_l with B; auto with *.
intros H'4; try assumption.
absurd (in_part x0 (single x)); auto with *.
elim (classic (Equal x0 x)).
intros H'3; try assumption.
unfold not in |- *; intros.
unfold not in H'1.
apply H'1.
apply in_part_trans_eq with x0; auto with *.
intros H'3; try assumption.
apply diff_in_r with B0; auto with *.
apply add_part_in_el_diff with x; auto with *.
Qed.
Hint Resolve diff_add_part_not_in: algebra.

Lemma inter_add_part_not_in :
 forall (A B0 B : part_set E) (x : E),
 ~ in_part x B0 ->
 Equal A (add_part B0 x) -> ~ in_part x B -> Equal (inter B0 B) (inter A B).
unfold add_part in |- *.
intros A B0 B x H' H'0 H'1; try assumption.
apply Trans with (inter (union B0 (single x)) B).
auto with *.
apply Trans with (union (inter B0 B) (inter (single x) B)).
apply Trans with (union (inter B0 B) (empty E)).
auto with *.
apply union_comp; auto with *.
apply Sym.
apply in_eq_part.
intros x0 H'2; try assumption.
cut (Equal x x0).
intros H'3; try assumption.
absurd (in_part x0 B).
unfold not in |- *; intro.
unfold not in H'1.
apply H'1.
apply in_part_trans_eq with x0; auto with *.
apply in_part_inter_r with (single x).
auto with *.
cut (in_part x0 (single x)).
auto with *.
apply in_part_inter_l with B.
auto with *.
intros x0 H'2; try assumption.
absurd (in_part x0 (empty E)); auto with *.
auto with *.
auto with *.
Qed.

Lemma cardinal_diff :
 forall (a : nat) (A B : part_set E),
 cardinal A a ->
 exists b : nat,
   (exists c : nat,
      cardinal (diff A B) b /\ cardinal (inter A B) c /\ a = b + c).
simple induction a; intros.
exists 0; intros.
exists 0; intros.
simpl in |- *.
split.
apply cardinal_empty.
apply Trans with (diff (empty E) B); auto with *.
split.
apply cardinal_empty.
apply Trans with (inter (empty E) B); auto with *.
auto with *.
inversion H0.
elim (H B0 B); intros.
case H6; clear H6; intros.
case H6; clear H6; intros.
case H7; clear H7; intros.
case (classic (in_part x B)); intros.
exists x0.
exists (S x1).
split.
apply cardinal_comp_l with (diff B0 B); auto with *.
apply diff_add_part with x; auto with *.
split.
apply cardinal_add with (inter B0 B) x; auto with *.
rewrite H8.
auto with *.
exists (S x0).
exists x1.
split.
apply cardinal_add with (diff B0 B) x; auto with *.
split.
apply cardinal_comp_l with (inter B0 B); auto with *.
apply inter_add_part_not_in with x; auto with *.
rewrite H8; auto with *.
auto with *.
Qed.

Lemma cardinal_union_inter :
 forall (A B : part_set E) (a b c : nat),
 cardinal A a ->
 cardinal B b -> cardinal (inter A B) c -> cardinal (union A B) (a + b - c).
intros.
case (cardinal_diff A H0); intros.
case H2; clear H2; intros.
case H2; clear H2; intros.
case H3; clear H3; intros.
apply cardinal_comp with (union A (diff B A)) (a + x); auto with *.
rewrite H4.
replace c with x0.
rewrite plus_assoc.
replace (a + x + x0) with (x0 + (a + x)); auto with *.
apply (cardinal_unique H3); auto with *.
apply cardinal_comp_l with (inter A B); auto with *.
Qed.
Hint Resolve cardinal_union_inter: algebra.
End fparts2_def.
