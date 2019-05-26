Require Import PolTac.

Theorem pols_test1: forall x y, x < y ->  (x + x < y + x).
intros.
pols.
auto.
Qed.

Theorem pols_test2: forall x y, y < 0 ->  (x + y < x).
intros.
pols.
auto.
Qed.
 
Theorem pols_test4:
 forall x y,
 x * x  < y * y ->  ((x + y) * (x + y) < 2 * (x * y + y * y)).
intros.
pols.
auto.
Qed.
 
Theorem pols_test5:
 forall x y z, x + y * (y + z) = 2 * z ->  2 * x + y * (y + z) = (x + z) + z.
intros.
pols.
auto.
Qed.


Theorem polf_test1: forall x y, (1 <= y -> x  <= x  * y).
intros.
polf.
Qed.

Theorem polf_test2: forall x y, 0 < x -> x  <= x  * y -> 1 <= y.
intros.
hyp_polf H0.
auto.
Qed.



Theorem polr_test1: forall x y z, (x + z) < y -> x + y + z < 2*y.
intros x y z H.
polr H.
pols.
auto.
pols.
auto.
Qed.
