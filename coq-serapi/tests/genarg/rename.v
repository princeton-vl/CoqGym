Require Import ZArith.

Open Scope Z_scope.

Lemma Zplus0 : forall n, n + 0 = n.
Proof.
intros n.
rename n into m.
auto with zarith.
Qed.
