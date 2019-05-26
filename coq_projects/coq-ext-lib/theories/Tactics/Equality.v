Require Import ExtLib.Data.Eq.

Ltac eq_rw_goal :=
  autorewrite with eq_rw.

Ltac eq_rw_hyp H :=
  autorewrite with eq_rw in H.

Ltac eq_rw_star :=
  autorewrite with eq_rw in *.

Tactic Notation "eq_rw" := eq_rw_goal.
Tactic Notation "eq_rw" "in" hyp(H) := eq_rw_hyp H.
Tactic Notation "eq_rw" "in" "*" := eq_rw_star.