(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** Object-level encoding of bounded universal quantification I *)

Require Import Arith Nat Omega List Bool Setoid.
Require Import utils_tac gcd prime binomial sums bool_nat luca.
Require Import cipher dio_logic dio_expo.

Set Implicit Arguments.

Local Infix "≲" := binary_le (at level 70, no associativity).
Local Notation power := (mscal mult 1).
Local Notation "∑" := (msum plus 0).
Local Infix "⇣" := nat_meet (at level 40, left associativity).
Local Infix "⇡" := nat_join (at level 50, left associativity).

(** This result comes from Luca's theorem *)

Theorem binary_le_binomial n m : n ≲ m <-> rem (binomial m n) 2 = 1.
Proof.
  split.
  + induction 1 as [ n | n m H1 H2 IH2 ].
    * rewrite binomial_n0, rem_lt; omega.
    * rewrite lucas_lemma with (1 := prime_2) (2 := div_rem_spec1 m 2) (4 := div_rem_spec1 n 2);
        try (apply div_rem_spec2; omega).
      rewrite mult_comm, <- rem_mult_rem, IH2, Nat.mul_1_r.
      revert H1.
      generalize (rem_2_is_0_or_1 m) (rem_2_is_0_or_1 n).
      intros [ G1 | G1 ] [ G2 | G2 ]; rewrite G1, G2; intros; try omega.
      ++ rewrite binomial_n0, rem_lt; omega.
      ++ rewrite binomial_n0, rem_lt; omega.
      ++ rewrite binomial_n1, rem_lt; omega.
  + induction on n m as IH with measure m.
    destruct (eq_nat_dec m 0) as [ Hm | Hm ].
    * destruct n; try (intros; constructor; fail). 
      subst; rewrite binomial_gt, rem_lt; omega.
    * generalize (div_rem_spec1 m 2) (div_rem_spec1 n 2); intros H1 H2.
      rewrite lucas_lemma with (1 := prime_2) (2 := H1) (4 := H2); auto;
        try (apply div_rem_spec2; omega).
      rewrite rem_2_mult; intros (H3 & H4).
      apply IH in H3; try omega.
      constructor 2; auto.
      revert H4.
      generalize (rem_2_is_0_or_1 m) (rem_2_is_0_or_1 n).
      intros [ G1 | G1 ] [ G2 | G2 ]; rewrite G1, G2; intros; try omega.
      rewrite binomial_gt, rem_lt in H4; omega.
Qed.

Hint Resolve dio_rel_binomial dio_rel_remainder.

Section binary_le_dio.

  Let ble_equiv x y : x ≲ y <-> exists b, b = binomial y x /\ 1 = rem b 2.
  Proof.
    rewrite binary_le_binomial; split; eauto.
    intros (? & ? & ?); subst; auto.
  Qed.

  Theorem binary_le_diophantine x y : 𝔻P x -> 𝔻P y -> 𝔻R (fun v => x v ≲ y v).
  Proof.
    intros. 
    apply dio_rel_equiv with (1 := fun v => ble_equiv (x v) (y v)).
    dio_rel_auto.
  Defined.

End binary_le_dio.

Hint Resolve binary_le_diophantine.

Theorem nat_meet_diophantine a b c : 𝔻P a -> 𝔻P b -> 𝔻P c
                                  -> 𝔻R (fun v => a v = b v ⇣ c v).
Proof.
  intros.
  apply dio_rel_equiv with (1 := fun v => nat_meet_dio (a v) (b v) (c v)).
  dio_rel_auto.
Defined.

Hint Resolve nat_meet_diophantine.
