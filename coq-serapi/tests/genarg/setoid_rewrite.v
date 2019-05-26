Require Setoid.
Require Import PeanoNat Le Gt Minus Bool Lt List.
Require Import Omega.

Section ReDun.

  Variable A : Type.

  Variable decA : forall (a b : A), {a = b}+{a <> b}.

  Theorem NoDup_count_occ' l:
    NoDup l <-> (forall x:A, In x l -> count_occ decA l x = 1).
  Proof.
    rewrite (NoDup_count_occ decA).
    setoid_rewrite (count_occ_In decA) at 1.
    unfold gt, lt in *.
    split; intros H x; specialize (H x);
    set (n := count_occ decA l x) in *; clearbody n; omega.
  Qed.
End ReDun.
