Require Import Reals.
Require Import PolTac.

Open Scope R_scope.
 
Theorem pols_test1: forall (x y : R), x < y ->  (x + x < y + x).
intros.
pols.
auto.
Qed.
 
Theorem pols_test2: forall (x y : R), 0 < y ->  (x  < x + y).
intros.
pols.
auto.
Qed.
 
Theorem pols_test3: forall (x y : R), 0 < y * y ->  ((x + y) * (x - y) < x * x).
intros.
pols.
auto with real.
Qed.

Theorem pols_test4:
 forall (x y : R),
 x * x  < y * y ->  ((x + y) * (x + y) < 2 * (x * y + y * y)).
intros.
pols.
auto.
Qed.
 
Theorem pols_test5:
 forall (x y z : R),
 x * (z + 2) < y * (2 * x + 1)->  (x * ((z + y) + 2) < y * (3 * x + 1)).
intros.
pols.
auto.
Qed.

Theorem polf_test1: forall x y, (0 <= x -> 1 <= y -> x  <=  x  * y)%R.
intros.
polf.
Qed.

Theorem polf_test2: forall x y, (0 < x -> x  <= x  * y -> 1 <= y)%R.
intros.
hyp_polf H0.
Qed.

Theorem polr_test1: forall x y z, (x + z) < y -> x + y + z < 2*y.
intros x y z H.
polr H.
pols.
auto.
pols.
auto with real.
Qed.

Theorem polr_test2: forall x y z t u, t <0 -> y = u -> x + z <  y ->  2* y * t <  x * t + t * u + z * t .
intros x y z t u H H1 H2.
polf.
polr H1; auto with real.
polr H2.
pols.
auto.
pols.
auto with real.
Qed.


