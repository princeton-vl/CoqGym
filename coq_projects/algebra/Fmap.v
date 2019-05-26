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
Require Export Tiroirs.
Require Export Parts2.
Require Export Classical_Pred_Type.
Require Export Compare_dec.

Lemma not_injective_prop :
 forall (A B : Setoid) (f : MAP A B),
 ~ injective f ->
 exists x : A, (exists y : A, ~ Equal x y /\ Equal (f x) (f y)).
unfold injective in |- *.
intros A B f H'; try assumption.
cut
 (ex
    (fun x : A =>
     ~ (forall y : A, ~ (~ Equal x y /\ Equal (Ap f x) (Ap f y))))).
intros H'0; try assumption.
elim H'0; intros x E; try exact E; clear H'0.
exists x; try assumption.
cut (ex (fun y : A => ~ ~ (~ Equal x y /\ Equal (Ap f x) (Ap f y)))).
intros H'0; try assumption.
elim H'0; intros y E0; try exact E0; clear H'0.
exists y; try assumption.
apply NNPP; auto with *.
apply
 not_all_ex_not
  with (P := fun y : A => ~ (~ Equal x y /\ Equal (Ap f x) (Ap f y)));
 auto with *.
apply
 not_all_ex_not
  with
    (P := fun x : A =>
          forall y : A, ~ (~ Equal x y /\ Equal (Ap f x) (Ap f y)));
 auto with *.
red in |- *.
intros H'0; try assumption.
apply H'.
intros x y H'1; try assumption.
specialize  H'0 with (n := x) (y := y); rename H'0 into H'3; try exact H'3.
apply NNPP; tauto.
Qed.

Lemma not_surjective_prop :
 forall (A B : Setoid) (f : MAP A B),
 ~ surjective f -> exists y : B, ~ in_part y (image_map f).
intros A B f H'; try assumption.
apply not_all_ex_not with (P := fun y : B => in_part y (image_map f)).
red in |- *.
red in H'.
intros H'0; try assumption.
lapply H'; [ intros H'1; try exact H'1; clear H' | clear H' ].
red in |- *.
simpl in H'0.
intros y; try assumption.
elim (H'0 y); intros x E; elim E; intros H'1 H'2; try exact H'2; clear E.
exists x; try assumption.
Qed.
Parameter
  image_empty :
    forall (E F : Setoid) (f : MAP E F) (A : part_set E),
    Equal A (empty E) -> Equal (image f A) (empty F).
Hint Resolve image_empty: algebra.
Parameter
  image_union :
    forall (E F : Setoid) (f : MAP E F) (A B : part_set E),
    Equal (image f (union A B)) (union (image f A) (image f B)).
Hint Resolve image_union: algebra.
Parameter
  image_single :
    forall (E F : Setoid) (f : MAP E F) (A : part_set E) (x : E),
    Equal (image f (single x)) (single (f x)).
Hint Resolve image_single: algebra.
Parameter
  union_single_in :
    forall (E : Setoid) (A : part_set E) (x : E),
    in_part x A -> Equal (union A (single x)) A.
Hint Resolve union_single_in: algebra.

Lemma cardinal_image_lesser :
 forall (E F : Setoid) (f : MAP E F) (A : part_set E) (n : nat),
 cardinal A n -> exists m : nat, cardinal (image f A) m /\ m <= n.
intros E F f A n H'; try assumption.
apply
 cardinal_ind2
  with
    (P := fun (n : nat) (A : part_set E) (c : cardinal A n) =>
          ex (fun m : nat => cardinal (image f A) m /\ m <= n)).
intros A0 H'0; try assumption.
exists 0; split; [ idtac | auto with * ].
apply cardinal_empty; auto with *.
intros n0 H'0 A0 B x H'1 H'2 H'3; try assumption.
case (classic (in_part (f x) (image f B))).
intros H'4; try assumption.
elim (H'0 B);
 [ intros m E0; elim E0; intros H'7 H'8; try exact H'7; clear E0 | idtac ].
exists m; split; [ idtac | try assumption ].
apply cardinal_comp with (image f B) m; auto with *.
apply Sym.
apply Trans with (image f (add_part B x)); auto with *.
unfold add_part in |- *.
apply Trans with (union (image f B) (image f (single x))); auto with *.
apply Trans with (union (image f B) (single (Ap f x))); auto with *.
auto with *.
apply cardinal_S with A0 x; auto with *.
intros H'4; try assumption.
elim (H'0 B);
 [ intros m E0; elim E0; intros H'7 H'8; try exact H'7; clear E0 | idtac ].
exists (S m); split; [ try assumption | idtac ].
apply cardinal_add with (image f B) (Ap f x); auto with *.
unfold add_part in |- *.
unfold add_part in H'2.
apply Trans with (image f (union B (single x))); auto with *.
apply Trans with (union (image f B) (image f (single x))); auto with *.
auto with *.
apply cardinal_S with A0 x; auto with *.
auto with *.
Qed.

Lemma cardinal_image_injective :
 forall (E F : Setoid) (f : MAP E F) (A : part_set E) (n : nat),
 cardinal A n -> injective f -> cardinal (image f A) n.
intros E F f A n H' H'0; try assumption.
case (cardinal_image_lesser f H').
intros x H'1; try assumption.
elim H'1; intros H'2 H'3; try exact H'2; clear H'1.
cut (x < n \/ x = n).
intros H'1; try assumption.
elim H'1; [ intros H'4; try exact H'4; clear H'1 | intros H'4; clear H'1 ].
case
 (tiroirs (E:=E) (F:=F) (f:=f) (n:=n) (Chaussettes:=A) H' (m:=x)
    (Tiroirs:=image f A) H'2 H'4).
auto with *.
intros x0 H'1; try assumption.
elim H'1; intros y E0; elim E0; intros H'5 H'6; try exact H'5; clear E0 H'1.
red in H'0.
absurd (Equal x0 y); auto with *.
apply cardinal_comp with (image f A) x; auto with *.
case (lt_eq_lt_dec x n).
intros H'1; elim H'1;
 [ intros H'4; try exact H'4; clear H'1 | intros H'4; clear H'1 ];
 auto with *.
intros H'1; try assumption.
absurd (n < x); auto with *.
Qed.
Parameter
  not_in_part_comp_r :
    forall (E : Setoid) (A B : part_set E) (x : E),
    ~ in_part x A -> Equal A B -> ~ in_part x B.
Parameter
  diff_single_not_in :
    forall (E : Setoid) (A : part_set E) (x : E),
    ~ in_part x (diff A (single x)).
Hint Resolve diff_single_not_in: algebra.
Parameter
  diff_el_union_single :
    forall (E : Setoid) (A : part_set E) (x : E),
    in_part x A -> Equal A (union (diff A (single x)) (single x)).
Hint Resolve diff_el_union_single: algebra.

Lemma cardinal_image_strict_lesser :
 forall (E F : Setoid) (f : MAP E F) (n : nat),
 cardinal (full E) n ->
 ~ injective f -> exists m : nat, cardinal (image_map f) m /\ m < n.
intros E F f n; try assumption.
case n.
intros H' H'0; try assumption.
case (not_injective_prop H'0).
intros x H'1; try assumption.
absurd (in_part x (full E)); auto with *.
apply not_in_part_comp_r with (empty E); auto with *.
inversion H'.
auto with *.
intros n0 H' H'0; try assumption.
case (not_injective_prop H'0).
intros x H'1; try assumption.
elim H'1; intros y E0; elim E0; intros H'2 H'3; try exact H'2; clear E0 H'1.
cut (cardinal (diff (full E) (single x)) n0).
intros H'1; try assumption.
case (cardinal_image_lesser f H'1).
intros m H'4; try assumption.
exists m; split; [ try assumption | idtac ].
elim H'4; intros H'5 H'6; try exact H'5; clear H'4.
apply cardinal_comp with (image f (diff (full E) (single x))) m; auto with *.
apply included_antisym.
unfold image_map in |- *.
apply image_included; auto with *.
unfold image_map in |- *.
unfold included in |- *.
intros x0 H'4; try assumption.
elim H'4.
intros x1 H'7; try assumption.
case (classic (Equal x1 x)).
intros H'8; try assumption.
simpl in |- *.
exists y; split; [ idtac | try assumption ].
split; [ idtac | try assumption ].
auto with *.
auto with *.
apply Trans with (f x); auto with *.
elim H'7; intros H'9 H'10; try exact H'10; clear H'7.
apply Trans with (f x1); auto with *.
intros H'8; try assumption.
simpl in |- *.
exists x1; split; [ idtac | try assumption ].
auto with *.
elim H'7; intros H'9 H'10; try exact H'10; clear H'7.
elim H'4; intros H'5 H'6; try exact H'6; clear H'4; auto with *.
apply cardinal_S with (full E) x; auto with *.
unfold add_part in |- *.
auto with *.
Qed.

Lemma cardinal_image_equal_injective :
 forall (E F : Setoid) (f : MAP E F) (n : nat),
 cardinal (full E) n -> cardinal (image_map f) n -> injective f.
intros E F f n H' H'0; try assumption.
apply NNPP.
red in |- *; intros H'1; try exact H'1.
case (cardinal_image_strict_lesser H' H'1).
intros x H'2; elim H'2; intros H'3 H'4; try exact H'4; clear H'2.
absurd (x = n); auto with *.
red in |- *; intros H'2; try exact H'2.
absurd (x < n); auto with *.
rewrite H'2.
auto with *.
apply cardinal_unique with (E := F) (A := image_map f); auto with *.
Qed.
Parameter
  cardinal_equal_included_equal :
    forall (E : Setoid) (A B : part_set E) (n : nat),
    cardinal A n -> cardinal B n -> included B A -> Equal B A.
Parameter
  image_full_surjective :
    forall (E F : Setoid) (f : MAP E F),
    Equal (image_map f) (full F) -> surjective f.
Hint Resolve image_full_surjective: algebra.

Lemma finite_injective_surjective :
 forall (E F : Setoid) (f : MAP E F) (n : nat),
 cardinal (full E) n -> cardinal (full F) n -> injective f -> surjective f.
intros E F f n H' H'0 H'1; try assumption.
generalize (cardinal_image_injective H' H'1).
intros H'2; try assumption.
apply image_full_surjective; auto with *.
unfold image_map in |- *.
apply cardinal_equal_included_equal with n; auto with *.
Qed.
Parameter
  surjective_image_full :
    forall (E F : Setoid) (f : MAP E F),
    surjective f -> Equal (image_map f) (full F).
Hint Resolve surjective_image_full: algebra.

Lemma finite_surjective_injective :
 forall (E F : Setoid) (f : MAP E F) (n : nat),
 cardinal (full E) n -> cardinal (full F) n -> surjective f -> injective f.
intros E F f n H' H'0 H'1; try assumption.
apply cardinal_image_equal_injective with n; auto with *.
apply cardinal_comp with (full F) n; auto with *.
apply Sym; auto with *.
Qed.

Lemma not_included_exist :
 forall (E : Setoid) (A B : part_set E),
 included B A -> ~ Equal B A -> exists x : E, in_part x A /\ ~ in_part x B.
intros E A B; simpl in |- *.
unfold eq_part in |- *; simpl in |- *.
intros H' H'0; try assumption.
cut
 (ex
    (fun x : E =>
     ~ ((in_part x B -> in_part x A) /\ (in_part x A -> in_part x B)))).
intros H'1; try assumption.
elim H'1; intros x E0; try exact E0; clear H'1.
exists x; split; [ try assumption | idtac ].
red in E0.
apply NNPP.
red in |- *; intros H'1; try exact H'1.
lapply E0; [ intros H'2; apply H'2; clear E0 | clear E0 ].
split; [ idtac | intros H'2; try assumption ].
intros H'2; try assumption.
apply H'; auto with *.
absurd (in_part x A); auto with *.
red in |- *.
red in E0.
intros H'1; try assumption.
lapply E0; [ intros H'2; apply H'2; clear E0 | clear E0 ].
split; [ try assumption | idtac ].
intros H'2; try assumption.
apply H'; auto with *.
auto with *.
apply
 not_all_ex_not
  with
    (P := fun x : E =>
          (in_part x B -> in_part x A) /\ (in_part x A -> in_part x B));
 auto with *.
Qed.

Lemma cardinal_included :
 forall (E : Setoid) (A : part_set E) (n : nat),
 cardinal A n ->
 forall B : part_set E,
 included B A -> exists m : nat, cardinal B m /\ m <= n.
intros E A n H'; try assumption.
apply
 cardinal_ind2
  with
    (P := fun (n : nat) (A : part_set E) (c : cardinal A n) =>
          forall B : part_set E,
          included B A -> ex (fun m : nat => cardinal B m /\ m <= n)).
intros A0 H'0 B H'1; exists 0; split; [ try assumption | idtac ]; auto with *.
apply cardinal_empty.
inversion H'0.
cut (included B (empty E)); auto with *.
apply included_comp with B A0; auto with *.
intros n0 H'0 A0 B x H'1 H'2 H'3 B0 H'4; try assumption.
case (classic (Equal B0 A0)); intros.
exists (S n0); split; [ idtac | try assumption ].
apply cardinal_comp with A0 (S n0); auto with *.
auto with *.
case (not_included_exist H'4 H).
intros x0 H'5; try assumption.
elim H'5; intros H'6 H'7; try exact H'6; clear H'5.
lapply (H'0 (minus_part A0 x0));
 [ intros H'8; elim (H'8 B0);
    [ intros m E0; elim E0; intros H'11 H'12; try exact H'11; clear E0
    | idtac ]
 | idtac ]; auto with *.
exists m; split; [ try assumption | idtac ].
apply le_trans with n0; auto with *.
unfold minus_part in |- *; simpl in |- *.
red in |- *.
intros x1 H'5; try assumption.
simpl in |- *.
split; [ try assumption | idtac ].
apply H'4; auto with *.
red in |- *.
intros H'9; try assumption.
apply H'7.
apply in_part_comp_l with x1; auto with *.
apply cardinal_S with A0 x0; auto with *.
apply Sym.
apply minus_add; auto with *.
auto with *.
Qed.

Lemma map_not_injective :
 forall (A B : Setoid) (f : MAP A B) (n m : nat),
 cardinal (full A) n -> cardinal (full B) m -> m < n -> ~ injective f.
intros A B f n m H' H'0 H'1; red in |- *; intros H'2; try exact H'2.
red in H'2.
case (tiroirs (E:=A) (F:=B) (f:=f) H' H'0 H'1); auto with *.
intros x H'3; try assumption.
elim H'3; intros y E; elim E; intros H'4 H'5; try exact H'4; clear E H'3;
 auto with *.
Qed.

Definition finite (A : Setoid) := exists n : nat, cardinal (full A) n.