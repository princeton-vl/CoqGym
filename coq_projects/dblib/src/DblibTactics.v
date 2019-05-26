Set Implicit Arguments.
Require Export Omega.

(* A hint for invoking [f_equal] as part of [eauto] search. *)

Hint Extern 1 => f_equal : f_equal.

(* Hints for invoking omega on arithmetic subgoals. *)

Hint Extern 1 (_ = _ :> nat) => reflexivity : omega.

Hint Extern 1 (_ = _ :> nat) => omega : omega.
Hint Extern 1 (_ <> _ :> nat) => omega : omega.
Hint Extern 1 (_ < _) => omega : omega.
Hint Extern 1 (_ > _) => omega : omega.
Hint Extern 1 (_ <= _) => omega : omega.
Hint Extern 1 (_ >= _) => omega : omega.

(* Dealing with integer comparisons. *)

Ltac dblib_intro_case_clear :=
  let h := fresh in
  intro h; case h; clear h.

Ltac dblib_inspect_cases :=
  match goal with
  | |- context [le_gt_dec ?n ?n'] =>
      case (le_gt_dec n n')
  | h: context [le_gt_dec ?n ?n'] |- _ =>
      revert h; case (le_gt_dec n n'); intro h
  | |- context [eq_nat_dec ?n ?n'] =>
      case (eq_nat_dec n n')
  | h: context [eq_nat_dec ?n ?n'] |- _ =>
      revert h; case (eq_nat_dec n n'); intro h
  | |- context [(lt_eq_lt_dec ?n ?n')] =>
       case (lt_eq_lt_dec n n'); [ dblib_intro_case_clear | idtac ]
  | h: context [(lt_eq_lt_dec ?n ?n')] |- _ =>
       revert h; case (lt_eq_lt_dec n n'); [ dblib_intro_case_clear | idtac ]; intro h
  end.

Ltac dblib_by_cases :=
  repeat dblib_inspect_cases; try solve [ intros; elimtype False; omega ]; intros.

