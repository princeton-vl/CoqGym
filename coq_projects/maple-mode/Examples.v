(* Examples.v *)

Require Import Maple.
Require Import Reals.
Open Scope R_scope.

Section MapleExamples.

Variable x y a b : R.

(**** Tactic Simplify ****)

Lemma simp0 : x <> 0 -> x / x = 1.
Proof.
  intros.
  simplify (x / x).
  reflexivity.
  assumption.
Qed.

Lemma simp1 : 1 + x <> 0 -> (1 + x) / (1 + x) * (1 + y) - (1 + y) >= 0.
Proof.
  intros.
  simplify ((1 + x) / (1 + x)).
  ring_simplify (1 * (1 + y) - (1 + y)).
  unfold Rge in |- *; right; reflexivity.
  assumption.
Qed.

Lemma simp2 :
 x <> 0 ->
 y <> 0 -> (x / y + y / x) * x * y - (x^2 + y^2) + 1 > 0.
Proof.
  intros.
  simplify ((x / y + y / x) * x * y - (x^2 + y^2) + 1).
  prove_sup0.
  split; assumption.
Qed.

Lemma simp3 : x + y <> 0 -> x / (x + y) + y / (x + y) = 1.
Proof.
  intros.
  simplify (x / (x + y) + y / (x + y)).
  reflexivity.
  assumption.
Qed.

(**** Tactic Factor ****)

Lemma fact0 : a^2 + 2*a*b + b^2 = (a+b)^2.
Proof.
  factor (a^2 + 2*a*b + b^2).
  reflexivity.
Qed.

Lemma fact1 : a^2 - 2*a*b + b^2 = (a-b)^2.
Proof.
  factor (a^2 - 2*a*b + b^2).
  reflexivity.
Qed.

Lemma fact2 : a^2 - b^2 = (a-b) * (a+b).
Proof.
  factor (a^2 - b^2).
  reflexivity.
Qed.

Lemma fact3 : a^3 + 3*a^2*b + 3*a*b^2 + b^3 = (a+b)^3.
Proof.
  factor (a^3 + 3*a^2*b + 3*a*b^2 + b^3).
  reflexivity.
Qed.

(**** Tactic Expand ****)

Lemma expd0 : (a+b)^2 = a^2 + 2*a*b + b^2.
Proof.
  expand ((a + b)^2).
  reflexivity.
Qed.

Lemma expd1 : (a-b)^2 = a^2 - 2*a*b + b^2.
Proof.
  expand ((a-b)^2).
  reflexivity.
Qed.

Lemma expd2 : (a-b) * (a+b) = a^2 - b^2.
Proof.
  expand ((a-b) * (a+b)).
  reflexivity.
Qed.

Lemma expd3 : (a+b)^3 = a^3 + 3*a^2*b + 3*a*b^2 + b^3.
Proof.
  expand ((a+b)^3).
  reflexivity.
Qed.

(**** Tactic Normal ****)

Lemma norm0 : x <> 0 -> y <> 0 -> x / y + y / x = (x^2 + y^2) * / y * / x.
Proof.
  intros.
  normal (x / y + y / x).
  reflexivity.
  split; assumption.
Qed.

Lemma norm1 :
 x <> 0 ->
 x + 1 <> 0 ->
 / x + x / (x + 1) = (x + 1 + x^2) * / x * / (x + 1).
Proof.
  intros.
  normal (/ x + x / (x + 1)).
  reflexivity.
  split; assumption.
Qed.

Lemma norm2 :
 x - y <> 0 ->
 x * (x / (x-y)^2) - y * (y / (x-y)^2) = (x + y) / (x - y).
Proof.
  intros H.
  normal (x * (x / (x-y)^2) - y * (y / (x-y)^2)).
  reflexivity.
  assumption.
Qed.

Lemma norm3 :
 x - y <> 0 ->
 x + y <> 0 ->
 x^2 - y^2 <> 0 ->
 x / (x - y) + y / (x + y) + 2 * y * (y / (x^2 - y^2)) =
 (x + y) / (x - y).
Proof.
  intros H H0 H1.
  normal (x / (x - y) + y / (x + y) + 2 * y * (y / (x^2 - y^2))).
  reflexivity.
  repeat split; assumption.
Qed.

(**** Eval <Maple Tactic> in ****)

Lemma eval_simp0 : x <> 0 -> y <> 0 -> x / x + y / y = 2.
Proof.
  intros.
  let t := eval simplify in (x / x + y / y) in
  replace (x / x + y / y)%R with t.
  reflexivity.
  cbn; field; auto.
Qed.

Lemma eval_fact0 : x <> 0 -> y <> 0 -> x / x + x / y = (x + y) / y.
Proof.
  intros.
  let t := eval factor in (x / x + x / y) in
  replace (x / x + x / y) with t.
  rewrite Rplus_comm; reflexivity.
  cbn; field; auto.
Qed.

Lemma eval_expd0 :
 (3 * x + 3) * (y - 5 / 3) = 3 * x * y + - (5 * x) + 3 * y + -5.
Proof.
  intros.
  let t := eval expand in ((3*x+3)*(y-5/3)) in
  replace ((3*x+3)*(y-5/3)) with t.
  reflexivity.
  cbn; field.
Qed.

Lemma eval_norm0 : x <> 0 -> y <> 0 -> y / (x * y) + y / x = (1 + y) / x.
Proof.
  intros.
  let t := eval normal in (y / (x * y) + y / x) in
  replace (y / (x * y) + y / x) with t.
  unfold Rdiv in |- *; reflexivity.
  cbn; field; auto.
Qed.

Definition def0 := Eval simplify in 1 / 1.

Definition def1 := Eval simplify in (x/y+y)*y.

Definition def2 := Eval factor in x*y+x.

Definition def3 := Eval factor in x*y-3*x+7*y-21.

Definition def4 := Eval expand in (x+y)*x.

Definition def5 := Eval expand in (x-7)*(y+4).

Definition def6 := Eval normal in /x+/y.

Definition def7 := Eval normal in x^2*y/(x+y)+y*x*y/(x+y).

End MapleExamples.
