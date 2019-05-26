
From Hammer Require Import Hammer Reconstr.

Require Import ZArith.

Open Scope Z_scope.

Lemma lem_1 : forall f g,
    (exists c, forall x : Z, Z.abs (f x) <= c * (Z.abs (g x))) <->
    (exists c, c > 0 /\ forall x, Z.abs (f x) <= c * (Z.abs (g x))).
Proof.
  sauto.
  assert (c > 0 \/ c <= 0).
  Reconstr.reasy Reconstr.Empty (@Coq.ZArith.BinInt.Z.le, @Coq.ZArith.BinInt.Z.gt).
  sauto.
  assert (forall x, Z.abs (f x) <= 0).
  Reconstr.reasy (@Coq.ZArith.BinInt.Z.mul_nonpos_nonneg, @Coq.ZArith.BinInt.Z.abs_nonneg, @Coq.ZArith.BinInt.Z.le_trans) Reconstr.Empty.
  assert (forall x, Z.abs (g x) >= 0).
  Reconstr.reasy (@Coq.ZArith.BinInt.Z.abs_nonneg, @Coq.ZArith.BinInt.Z.ge_le_iff) Reconstr.Empty.
  exists 1; sauto.
  Reconstr.rblast (@Coq.ZArith.BinInt.Z.le_antisymm, @Coq.ZArith.BinInt.Z.lt_le_trans, @Coq.ZArith.BinInt.Z.lt_eq_cases, @Coq.ZArith.Zorder.Zle_0_pos, @Coq.ZArith.BinInt.Z.lt_nge) Reconstr.Empty.
  ycrush.
Qed.

Lemma lem_2 : forall f g,
    (exists c, forall x : Z, Z.abs (f x) <= c * (Z.abs (g x))) <->
    (exists c, c > 0 /\ forall x, Z.abs (f x) <= c * (Z.abs (g x))).
Proof.
  sauto.
  assert (c > 0 \/ c <= 0).
  Reconstr.reasy Reconstr.Empty (@Coq.ZArith.BinInt.Z.le, @Coq.ZArith.BinInt.Z.gt).
  sauto.
  assert (forall x, Z.abs (f x) <= Z.abs (g x)).
  Reconstr.reasy (@Coq.ZArith.BinInt.Z.mul_nonpos_nonneg, @Coq.ZArith.BinInt.Z.le_trans, @Coq.ZArith.BinInt.Z.abs_nonneg) Reconstr.Empty.
  exists 1; sauto.
Qed.
