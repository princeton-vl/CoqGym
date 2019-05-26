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
Require Export Union.
Require Export Singleton.
Require Export Diff.
Require Export Classical_Prop.
Section fparts_in_def.
Variable E : Setoid.

(*
	Add_part.
*)

Definition add_part (A : part_set E) (x : E) := union A (single x).

Lemma add_part_comp :
 forall (A A' : part_set E) (x x' : E),
 Equal A A' -> Equal x x' -> Equal (add_part A x) (add_part A' x').
unfold add_part in |- *; auto with algebra.
Qed.
Hint Resolve add_part_comp: algebra.

Lemma add_part_in : forall (A : part_set E) (x : E), in_part x (add_part A x).
simpl in |- *; auto with algebra.
Qed.
Hint Resolve add_part_in: algebra.

Lemma add_part_com :
 forall (A : part_set E) (x y : E),
 Equal (add_part (add_part A x) y) (add_part (add_part A y) x).
unfold add_part in |- *.
intros.
apply Trans with (union A (union (single x) (single y))); auto with algebra.
apply Trans with (union A (union (single y) (single x))); auto with algebra.
Qed.
Hint Immediate add_part_com: algebra.

Lemma add_in :
 forall (A : part_set E) (x : E), in_part x A -> Equal (add_part A x) A.
intro A.
case A.
simpl in |- *; unfold pred_compatible, eq_part, in_part in |- *;
 simpl in |- *.
intuition eauto.
Qed.
Hint Resolve add_in: algebra.

Lemma add_part_in_el_diff :
 forall (A : part_set E) (x y : E),
 in_part y (add_part A x) -> ~ Equal y x -> in_part y A.
simpl in |- *.
unfold eq_part, add_part, union, single in |- *; simpl in |- *.
intro.
case A; simpl in |- *.
intros a pa.
intuition.
Qed.

Lemma add_part_in_el_not_in :
 forall (A : part_set E) (x y : E),
 in_part y (add_part A x) -> ~ in_part y A -> Equal y x.
simpl in |- *.
unfold eq_part, add_part, union, single in |- *; simpl in |- *.
intro.
case A; simpl in |- *.
intros a pa.
intuition.
Qed.

Lemma add_part_simpl :
 forall (A B : part_set E) (x : E),
 ~ in_part x A ->
 ~ in_part x B -> Equal (add_part A x) (add_part B x) -> Equal A B.
intros A B.
case A; case B; simpl in |- *.
intros a pa b pb.
unfold eq_part, add_part, union, single in |- *; simpl in |- *.
intros.
elim (classic (Equal x x0)); intros.
split; intros.
apply pa with x; auto with algebra.
cut (b x).
intro.
absurd (b x); auto with algebra.
apply pb with x0; auto with algebra.
cut (a x).
intro.
absurd (a x); auto with algebra.
apply pa with x0; auto with algebra.
elim (H1 x0); intros.
split; intros.
lapply H3.
intros.
elim H6; intros.
auto with algebra.
absurd (Equal x0 x); auto with algebra.
left; auto with algebra.
lapply H4; intros.
elim H6; intros.
auto with algebra.
absurd (Equal x0 x); auto with algebra.
left.
auto with algebra.
Qed.

(*
	Minus_part.
*)

Definition minus_part (A : part_set E) (x : E) := diff A (single x).

Lemma minus_part_comp :
 forall (A A' : part_set E) (x x' : E),
 Equal A A' -> Equal x x' -> Equal (minus_part A x) (minus_part A' x').
unfold minus_part in |- *; auto with algebra.
Qed.
Hint Resolve minus_part_comp: algebra.

Lemma minus_part_not_in :
 forall (A : part_set E) (x : E), ~ in_part x (minus_part A x).
simpl in |- *.
intro.
case A; simpl in |- *.
intros a pa.
intuition.
Qed.
Hint Resolve minus_part_not_in: algebra.

Lemma minus_part_com :
 forall (A : part_set E) (x y : E),
 Equal (minus_part (minus_part A x) y) (minus_part (minus_part A y) x).
unfold minus_part in |- *.
intros.
simpl in |- *.
unfold eq_part, diff, single in |- *; simpl in |- *.
intro.
intuition.
Qed.
Hint Immediate minus_part_com: algebra.

Lemma minus_not_in :
 forall (A : part_set E) (x : E), ~ in_part x A -> Equal (minus_part A x) A.
simpl in |- *.
unfold eq_part, minus_part, diff, single in |- *; simpl in |- *.
intro A.
case A; unfold pred_compatible in |- *; simpl in |- *.
intros a pa x neg_a_x x0.
generalize (pa x0 x).
intuition auto with algebra.
Qed.
Hint Resolve minus_not_in: algebra.

Lemma minus_trans_not_in :
 forall (A : part_set E) (x y : E),
 ~ in_part y A -> ~ in_part y (minus_part A x).
simpl in |- *.
unfold eq_part, minus_part, diff, single in |- *; simpl in |- *.
intro.
case A; simpl in |- *.
intros a pa.
intuition.
Qed.
Hint Resolve minus_trans_not_in: algebra.
(*
	Some lemmas.
*)

Lemma union_unit_l : forall A : part_set E, Equal (union (empty E) A) A.
simpl in |- *.
unfold eq_part, union, empty in |- *; simpl in |- *.
intuition.
Qed.
Hint Resolve union_unit_l: algebra.

Lemma single_add : forall x : E, Equal (single x) (add_part (empty E) x).
unfold add_part in |- *.
auto with algebra.
Qed.
Hint Resolve single_add: algebra.

Lemma minus_add :
 forall (A : part_set E) (x : E),
 in_part x A -> Equal (add_part (minus_part A x) x) A.
simpl in |- *.
unfold eq_part, add_part, minus_part, union, diff, single in |- *;
 simpl in |- *.
intro.
case A; simpl in |- *.
intros a pa.
intros.
intuition.
apply pa with x; auto with algebra.
apply NNPP; intuition.
Qed.
Hint Resolve minus_add: algebra.

Lemma add_minus :
 forall (A : part_set E) (x : E),
 ~ in_part x A -> Equal (minus_part (add_part A x) x) A.
simpl in |- *.
unfold eq_part, add_part, minus_part, union, diff, single in |- *;
 simpl in |- *.
intro.
case A; simpl in |- *.
intros a pa.
intros.
intuition.
apply H.
apply pa with x0; auto with algebra.
Qed.
Hint Resolve add_minus: algebra.
(*
	Cardinal.
*)

Inductive cardinal : part_set E -> nat -> Prop :=
  | cardinal_empty : forall A : part_set E, Equal A (empty E) -> cardinal A 0
  | cardinal_add :
      forall (A B : part_set E) (n : nat),
      cardinal B n ->
      forall x : E,
      ~ in_part x B -> Equal A (add_part B x) -> cardinal A (S n).
Hint Immediate cardinal_empty: algebra.

Lemma cardinal_comp :
 forall (A B : part_set E) (n m : nat),
 Equal A B -> n = m -> cardinal A n -> cardinal B m.
intros.
inversion H1.
rewrite <- H0.
rewrite <- H4.
apply cardinal_empty.
apply Trans with A; auto with algebra.
rewrite <- H0.
rewrite <- H6.
apply cardinal_add with B0 x; auto with algebra.
apply Trans with A; auto with algebra.
Qed.
Hint Resolve cardinal_comp: algebra.

Lemma cardinal_comp_l :
 forall (A B : part_set E) (n : nat),
 Equal A B -> cardinal A n -> cardinal B n.
intros.
apply cardinal_comp with A n; auto with algebra.
Qed.

Lemma cardinal_comp_r :
 forall (A : part_set E) (n m : nat), n = m -> cardinal A n -> cardinal A m.
intros.
apply cardinal_comp with A n; auto with algebra.
Qed.

Lemma cardinal_empty_O : cardinal (empty E) 0.
auto with algebra.
Qed.
Hint Resolve cardinal_empty_O: algebra.

Lemma cardinal_single : forall x : E, cardinal (single x) 1.
intro.
apply cardinal_add with (empty E) x; auto with algebra.
Qed.
Hint Resolve cardinal_single: algebra.

Lemma cardinal_pair :
 forall x y : E, ~ Equal x y -> cardinal (union (single x) (single y)) 2.
intros.
apply cardinal_add with (single x) y; auto with algebra.
Qed.
Hint Resolve cardinal_pair: algebra.

Lemma cardinal_O_empty :
 forall A : part_set E, cardinal A 0 -> Equal A (empty E).
intros.
inversion H.
auto with algebra.
Qed.
Hint Resolve cardinal_O_empty: algebra.

Lemma cardinal_1_single :
 forall A : part_set E, cardinal A 1 -> exists x : E, Equal A (single x).
intros.
inversion H.
exists x.
apply Trans with (add_part B x); auto with algebra.
apply Trans with (add_part (empty E) x); auto with algebra.
Qed.
(*
	Some lemmas.
*)

Lemma not_in_empty :
 forall A : part_set E, (forall x : E, ~ in_part x A) -> Equal A (empty E).
intros A.
case A.
intros a pa.
simpl in |- *.
unfold eq_part, empty in |- *; simpl in |- *.
intuition eauto.
Qed.
Hint Immediate not_in_empty: algebra.

Lemma not_in_part_trans :
 forall (x : E) (A B : part_set E),
 ~ in_part x A -> Equal A B -> ~ in_part x B.
unfold in_part in |- *.
intros x A B.
case A; case B; simpl in |- *.
intros a pa b pb.
unfold eq_part in |- *; simpl in |- *.
intuition.
elim (H0 x); auto with algebra.
Qed.

Lemma not_in_part_trans_eq :
 forall (x y : E) (A : part_set E),
 ~ in_part x A -> Equal x y -> ~ in_part y A.
unfold in_part in |- *.
intros x y A.
case A; intros a pa.
simpl in |- *.
intuition.
apply H.
apply (pa y x); auto with algebra.
Qed.

Lemma cardinal_sup3 :
 forall (A B C : part_set E) (x y : E),
 Equal A (add_part B x) ->
 Equal A (add_part C y) ->
 ~ in_part x B ->
 ~ in_part y C ->
 ~ Equal x y ->
 exists D : part_set E,
   Equal B (add_part D y) /\
   Equal C (add_part D x) /\ ~ in_part x D /\ ~ in_part y D.
intros.
exists (minus_part B y).
split.
apply Sym.
apply minus_add.
cut (in_part y (add_part B x)).
intros.
apply add_part_in_el_diff with x; auto with algebra.
apply in_part_comp_r with A; auto with algebra.
apply in_part_comp_r with (add_part C y); auto with algebra.
split.
apply add_part_simpl with y; auto with algebra.
unfold not in |- *; intro.
absurd (Equal y x); auto with algebra.
apply add_part_in_el_not_in with (minus_part B y); auto with algebra.
apply Trans with (add_part (add_part (minus_part B y) y) x);
 auto with algebra.
apply Trans with (add_part B x); auto with algebra.
apply Trans with A; auto with algebra.
apply add_part_comp; auto with algebra.
apply Sym.
apply minus_add; auto with algebra.
apply add_part_in_el_diff with x; auto with algebra.
apply in_part_comp_r with (add_part C y); auto with algebra.
apply Trans with A; auto with algebra.
split.
apply minus_trans_not_in; auto with algebra.
auto with algebra.
Qed.

Lemma cardinal_ind2 :
 forall P : forall (n : nat) (A : part_set E), cardinal A n -> Prop,
 (forall (A : part_set E) (c : cardinal A 0), P 0 A c) ->
 (forall n : nat,
  (forall (B : part_set E) (c : cardinal B n), P n B c) ->
  forall (A B : part_set E) (x : E),
  ~ in_part x B ->
  Equal A (add_part B x) -> forall c' : cardinal A (S n), P (S n) A c') ->
 forall (n : nat) (A : part_set E) (c : cardinal A n), P n A c.
simple induction n.
auto with algebra.
intros.
inversion c.
apply (H0 n0 H1 A B x H4 H6 c).
Qed.

Lemma cardinal_S :
 forall (n : nat) (A B : part_set E) (x : E),
 ~ in_part x B -> Equal A (add_part B x) -> cardinal A (S n) -> cardinal B n.
simple induction n.
intros.
apply cardinal_empty.
inversion H1.
elim (classic (Equal x0 x)); intros.
apply Trans with B0.
apply add_part_simpl with x; auto with algebra.
apply not_in_part_trans_eq with x0; auto with algebra.
apply Trans with A; auto with algebra.
apply Trans with (add_part B0 x0); auto with algebra.
auto with algebra.
absurd (in_part x (single x0)).
intuition.
apply in_part_comp_r with (add_part B0 x0); auto with algebra.
apply in_part_comp_r with A; auto with algebra.
apply in_part_comp_r with (add_part B x); auto with algebra.
apply Trans with (add_part (empty E) x0); auto with algebra.
intros.
inversion H2.
elim (classic (Equal x x0)); intros.
apply cardinal_comp_l with B0; auto with algebra.
apply add_part_simpl with x; auto with algebra.
apply not_in_part_trans_eq with x0; auto with algebra.
apply Trans with A; auto with algebra.
apply Trans with (add_part B0 x0); auto with algebra.
elim (cardinal_sup3 (A:=A) (B:=B) (C:=B0) (x:=x) (y:=x0)); auto with algebra.
intros C H9.
elim H9; clear H9; intros.
elim H10; clear H10; intros.
elim H11; clear H11; intros.
apply cardinal_add with C x0; auto with algebra.
apply H with B0 x; auto with algebra.
Qed.

Lemma cardinalO_unique :
 forall A : part_set E, cardinal A 0 -> forall m : nat, cardinal A m -> 0 = m.
intros.
inversion H0; auto with algebra.
absurd (in_part x (empty E)); auto with algebra.
apply in_part_comp_r with A; auto with algebra.
apply in_part_comp_r with (add_part B x); auto with algebra.
Qed.

Lemma cardinal_unique :
 forall (n : nat) (A : part_set E),
 cardinal A n -> forall m : nat, cardinal A m -> n = m.
intros n A c.
apply
 cardinal_ind2
  with
    (P := fun (n : nat) (A : part_set E) (c : cardinal A n) =>
          forall m : nat, cardinal A m -> n = m); auto with algebra.
exact cardinalO_unique.
intros n0 H A0 B x H0 H1 c' m.
case m; intros.
absurd (in_part x (empty E)); auto with algebra.
apply in_part_comp_r with A0; auto with algebra.
apply in_part_comp_r with (add_part B x); auto with algebra.
cut (cardinal B n0).
cut (cardinal B n1).
intros.
cut (n0 = n1).
auto with algebra.
apply H with B; auto with algebra.
apply cardinal_S with A0 x; auto with algebra.
apply cardinal_S with A0 x; auto with algebra.
Qed.
(* OUF! *)
End fparts_in_def.
Hint Resolve single_law add_part_comp add_part_in add_in minus_part_comp
  minus_part_not_in minus_not_in minus_trans_not_in union_unit_l single_add
  minus_add add_minus cardinal_comp cardinal_empty_O cardinal_single
  cardinal_pair cardinal_O_empty: algebra.
Hint Immediate single_prop: algebra.
Hint Immediate single_prop_rev: algebra.
Hint Immediate add_part_com: algebra.
Hint Immediate minus_part_com: algebra.
Hint Immediate cardinal_empty: algebra.
Hint Immediate not_in_empty: algebra.
