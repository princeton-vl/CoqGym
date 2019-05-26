Require Import PolTac.
Require Import ZArith.

(* Test for Z *)
Open Scope  Z_scope.

Ltac cg g := match goal with |- g => idtac end.


Goal forall a b c d, a + c = d -> b + d = c + d -> a + b + c = c + d.
intros a b c d H1 H2.
polr H1.
rewrite H1; auto. 
auto.
Qed.

Goal forall a b c d, d = 0 -> a + b + c = c + 0 -> a + b + c = c + d.
intros a b c d H1 H2.
polr H1.
rewrite H1; auto.
auto.
Qed.

Goal forall a b c d, a + c <= d -> b <= c -> a + b + c <= c + d.
intros a b c d H1 H2.
polr H1.
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d,  a + b  <= 0 -> 0 <= d -> a + b + c <= c + d.
intros.
polrx (0 < d) P.R P.R 1%Z.
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, a + c >= d -> b >= c -> a + b + c >= c + d.
intros.
polr (a + c < d).
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, a + b >= 0 -> 0 >= d -> a + b + c >= c + d.
intros.
polrx (0 < d) P.R P.R 1%Z.
pols.
auto.
pols.
auto.
Qed.


Goal forall a b c d, a + c < d -> b <= c -> a + b + c < c + d.
intros.
polr (a + c < d).
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, a + b <= 0 -> 0 < d -> a + b + c < c + d.
intros.
polrx (0 < d) P.R P.R 1%Z.
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, a + c > d -> c <= b -> a + b + c > c + d.
intros.
polr (a + c < d).
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, 0 <= a + b -> 0 > d -> a + b + c > c + d.
intros.
polrx (0 < d) P.R P.R 1%Z.
pols.
auto.
pols.
auto.
Qed.

(* Test for N *)
Require Import NAux.
Open Scope  N_scope.

Goal forall a b c d, a + c = d -> b = c -> a + b + c = c + d.
intros.
polr (a + c = d).
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, 0 = d -> a + b = 0 -> a + b + c = c + d.
intros.
polr (d = 0).
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, a + c <= d -> b <= c -> a + b + c <= c + d.
intros.
polr (a + c < d).
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, a + b <= 0 -> 0 <= d -> a + b + c <= c + d.
intros.
polrx (0 < d) P.R P.R 1%Z.
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, a + c >= d -> b >= c -> a + b + c >= c + d.
intros.
polr (a + c < d).
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, a + b >= 0 -> 0 >= d -> a + b + c >= c + d.
intros.
polrx (0 < d) P.R P.R 1%Z.
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, a + c < d -> b <= c -> a + b + c < c + d.
intros.
polr (a + c < d).
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, a + b <= 0 -> 0 < d -> a + b + c < c + d.
intros.
polrx (0 < d) P.R P.R 1%Z.
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, a + c > d -> c <= b -> a + b + c > c + d.
intros.
polr (a + c < d).
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, 0 <= a + b -> 0 > d -> a + b + c > c + d.
intros.
polrx (0 < d) P.R P.R 1%Z.
pols.
auto.
pols.
auto.
Qed.

Require Import Arith.
(* Test for Nat *)
Open Scope  nat_scope.

Goal forall a b c d, a + c = d -> b = c -> a + b + c = c + d.
intros.
polr (a + c = d).
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, 0 = d -> a + b = 0 -> a + b + c = c + d.
intros.
polr (d = 0).
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, a + c <= d -> b <= c -> a + b + c <= c + d.
intros.
polr (a + c < d).
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, a + b <= 0 -> 0 <= d -> a + b + c <= c + d.
intros.
polrx (0 < d) P.R P.R 1%Z.
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, a + c <= d -> b <= c -> a + b + c <= c + d.
intros.
polr (a + c < d).
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, a + b >= 0 -> 0 >= d -> a + b + c >= c + d.
intros.
polrx (0 < d) P.R P.R 1%Z. 
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, a + c < d -> b <= c -> a + b + c < c + d.
intros.
polr (a + c < d).
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, a + b <= 0 -> 0 < d -> a + b + c < c + d.
intros.
polrx (0 < d) P.R P.R 1%Z.
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, a + c > d -> c <= b -> a + b + c > c + d.
intros.
(*
NatPolR.npolrx (a + c < d) P.L P.L 1%Z.
*)
polr (a + c < d).
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, 0 <= a + b -> 0 > d -> a + b + c > c + d.
intros.
polrx (0 < d) P.R P.R 1%Z.
pols.
auto.
pols.
auto.
Qed.

(* Test for R *)
Require Import Reals.
Open Scope  R_scope.

Goal forall a b c d, a + c = d -> b = c -> a + b + c = c + d.
intros.
polr (a + c = d).
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, 0 = d -> a + b = 0 -> a + b + c = c + d.
intros.
polr (d = 0).
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, a + c <= d -> b <= c -> a + b + c <= c + d.
intros.
polr (a + c < d).
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, a + b <= 0 -> 0 <= d -> a + b + c <= c + d.
intros.
polrx (0 < d) P.R P.R 1%Z.
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, a + c >= d -> b >= c -> a + b + c >= c + d.
intros.
polr (a + c < d).
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, a + b >= 0 -> 0 >= d -> a + b + c >= c + d.
intros.
polrx (0 < d) P.R P.R 1%Z.
pols.
auto.
pols.
auto.
Qed.

Goal forall a b c d, a + c < d -> b <= c -> a + b + c < c + d.
intros.
polr (a + c < d).
pols.
auto.
pols.
auto.
Qed.
 
Goal forall a b c d, a + b <= 0 -> 0 < d -> a + b + c < c + d.
intros.
polrx (0 < d) P.R P.R 1%Z.
pols.
auto.
pols.
auto.
Qed. 

Goal forall a b c d, a + c > d -> b >= c -> a + b + c > c + d.
intros.
polr (a + c < d).
pols.
auto.
pols.
auto.
Qed. 

Goal forall a b c d, a + b >= 0 -> 0 > d -> a + b + c > c + d.
intros.
polrx (0 < d) P.R P.R 1%Z.
pols.
auto.
pols.
auto.
Qed.
