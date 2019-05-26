Require Import ZArith.
Require Import PolTac.

Open Scope Z_scope.

Theorem pols_test1: forall (x y : Z), x < y ->  (x + x < y + x).
intros.
pols.
auto.
Qed.
 
Theorem pols_test2: forall (x y : Z), y < 0 ->  (x + y < x).
intros.
pols.
auto.
Qed.
 
Theorem pols_test3: forall (x y : Z), 0 < y * y ->  ((x + y) * (x - y) < x * x).
intros.
pols.
auto with zarith.
Qed.
 
Theorem pols_test4:
 forall (x y : Z),
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

Theorem polf_test1: forall x y, (0 <= x -> 1 <= y -> x  <= x  * y)%Z.
intros.
polf.
Qed.

Theorem polf_test2: forall x y, (0 < x -> x  <= x  * y -> 1 <= y)%Z.
intros.
hyp_polf H0.
Qed.

Theorem polr_test1: forall x y z, (x + z) < y -> x + y + z < 2*y.
intros x y z H.
polr H.
pols.
auto.
pols.
auto with zarith.
Qed.
