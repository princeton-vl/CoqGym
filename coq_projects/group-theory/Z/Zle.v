(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

Require Import Arith.
Require Import Zbase.
Require Import Z_succ_pred.
Require Import Zadd.

Definition leZ (x y : Z) :=
  match x return Prop with
  | OZ =>
      match y return Prop with
      | OZ => True
      | pos n => True
      | neg n => False
      end
  | pos n =>
      match y return Prop with
      | OZ => False
      | pos m => n <= m
      | neg m => False
      end
  | neg n =>
      match y return Prop with
      | OZ => True
      | pos m => True
      | neg m => m <= n
      end
  end.

Lemma sign_absZ : forall x : Z, leZ OZ (absZ x).
intros; elim x; simpl in |- *.
exact I.
intro; simpl in |- *.
exact I.
intro; simpl in |- *.
exact I.
Qed.

Lemma tech_le_pos_abs : forall x : Z, leZ OZ x -> absZ x = x.
intro x; elim x.
unfold absZ in |- *; reflexivity.
unfold absZ in |- *; reflexivity.
intros; elim H.
Qed.

Theorem leZ_antisymmetric : forall x y : Z, leZ x y -> leZ y x -> x = y.
intros x y; elim x.
elim y.
reflexivity.
intros; elim H0.
intros; elim H.
intro n; elim y.
intros; elim H.
simpl in |- *; intros; elim (le_antisym n n0 H H0); reflexivity.
intros; elim H.
intro n; elim y.
intros; elim H0.
intros; elim H0.
simpl in |- *; intros; elim (le_antisym n0 n H H0); reflexivity.
Qed.

Definition ltZ (x y : Z) := leZ (succZ x) y.

Definition lt_absZ (x y : Z) := ltZ (absZ x) (absZ y).

Lemma tech_lt_abs_OZ : forall x : Z, lt_absZ x (pos 0) -> x = OZ.
simple induction x.
reflexivity.
unfold lt_absZ in |- *; unfold absZ in |- *; unfold ltZ in |- *;
 unfold leZ in |- *; intros.
elim (le_Sn_O n H).
unfold lt_absZ in |- *; unfold absZ in |- *; unfold ltZ in |- *;
 unfold leZ in |- *; intros.
elim (le_Sn_O n H).
Qed.

Lemma tech_posOZ_pos : forall n : nat, leZ OZ (posOZ n).
intros; elim n.
simpl in |- *; exact I.
simpl in |- *; intros; exact I.
Qed.

Lemma le_opp_OZ_l : forall x : Z, leZ OZ x -> leZ (oppZ x) OZ.
intro x; elim x.
simpl in |- *; intros; exact I.
simpl in |- *; intros; exact I.
intros; elim H.
Qed.

Lemma le_opp_OZ :
 forall x y : Z, x = oppZ y -> leZ OZ x -> leZ OZ y -> x = OZ.
intros.
apply (leZ_antisymmetric x OZ).
rewrite H.
exact (le_opp_OZ_l y H1).
exact H0.
Qed.

Let opp_inv : forall x y : Z, x = oppZ y -> y = oppZ x.
intros x y; elim y; simpl in |- *.
intro H'; rewrite H'; auto with arith.
intros n H'; rewrite H'; auto with arith.
intros n H'; rewrite H'; auto with arith.
Qed.

Lemma le_opp_OZ2 :
 forall x y : Z, x = oppZ y -> leZ OZ x -> leZ OZ y -> x = y.
intros.
rewrite (le_opp_OZ x y H H0 H1).
cut (y = oppZ x).
intro H'; rewrite H'.
rewrite (le_opp_OZ x y H H0 H1); simpl in |- *; reflexivity.
apply opp_inv; trivial with arith.
Qed.


