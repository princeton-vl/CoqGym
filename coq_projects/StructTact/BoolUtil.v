Require Import Arith.
Require Import List.
Import ListNotations.
Require Import StructTact.StructTactics.

Set Implicit Arguments.

Lemma leb_false_lt : forall m n, leb m n = false -> n < m.
Proof.
  induction m; intros.
  - discriminate.
  - simpl in *. break_match; subst; auto with arith.
Qed.

Lemma leb_true_le : forall m n, leb m n = true -> m <= n.
Proof.
  induction m; intros.
  - auto with arith.
  - simpl in *. break_match; subst; auto with arith.
    discriminate.
Qed.

Lemma ltb_false_le : forall m n, m <? n = false -> n <= m.
Proof.
  induction m; intros; destruct n; try discriminate; auto with arith.
Qed.

Lemma ltb_true_lt : forall m n, m <? n = true -> m < n.
  induction m; intros; destruct n; try discriminate; auto with arith.
Qed.

Ltac do_bool :=
  repeat match goal with
    | [ H : beq_nat _ _ = true |- _ ] => apply beq_nat_true in H
    | [ H : beq_nat _ _ = false |- _ ] => apply beq_nat_false in H
    | [ H : andb _ _ = true |- _ ] => apply Bool.andb_true_iff in H
    | [ H : andb _ _ = false |- _ ] => apply Bool.andb_false_iff in H
    | [ H : orb _ _ = true |- _ ] => apply Bool.orb_prop in H
    | [ H : negb _ = true |- _ ] => apply Bool.negb_true_iff in H
    | [ H : negb _ = false |- _ ] => apply Bool.negb_false_iff in H
    | [ H : PeanoNat.Nat.ltb _ _ = true |- _ ] => apply ltb_true_lt in H
    | [ H : PeanoNat.Nat.ltb _ _ = false |- _ ] => apply ltb_false_le in H
    | [ H : leb _ _ = true |- _ ] => apply leb_true_le in H
    | [ H : leb _ _ = false |- _ ] => apply leb_false_lt in H
    | [ |- andb _ _ = true ]=> apply Bool.andb_true_iff
    | [ |- andb _ _ = false ] => apply Bool.andb_false_iff
    | [ |- leb _ _ = true ] => apply leb_correct
    | [ |-  _ <> false ] => apply Bool.not_false_iff_true
    | [ |- beq_nat _ _ = false ] => apply beq_nat_false_iff
    | [ |- beq_nat _ _ = true ] => apply beq_nat_true_iff
  end.

Definition null {A : Type} (xs : list A) : bool :=
  match xs with
    | [] => true
    | _ => false
  end.

Lemma null_sound :
  forall A (l : list A),
    null l = true -> l = [].
Proof.
  destruct l; simpl in *; auto; discriminate.
Qed.

Lemma null_false_neq_nil :
  forall A (l : list A),
    null l = false -> l <> [].
Proof.
  destruct l; simpl in *; auto; discriminate.
Qed.
