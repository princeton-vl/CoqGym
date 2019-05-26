Require Import ZArith Zquot.

Record radix := { radix_val :> Z ; radix_prop : Zle_bool 2 radix_val = true }.

Theorem Zpower_plus :
  forall n k1 k2, (0 <= k1)%Z -> (0 <= k2)%Z ->
  Zpower n (k1 + k2) = (Zpower n k1 * Zpower n k2)%Z.
Proof.
intros n k1 k2 H1 H2.
now apply Zpower_exp ; apply Z.le_ge.
Qed.

Theorem Zpower_Zpower_nat :
  forall b e, (0 <= e)%Z ->
  Zpower b e = Zpower_nat b (Z.abs_nat e).
Proof.
intros b [|e|e] He.
apply refl_equal.
apply Zpower_pos_nat.
elim He.
apply refl_equal.
Qed.

Theorem Zpower_nat_S :
  forall b e,
  Zpower_nat b (S e) = (b * Zpower_nat b e)%Z.
Proof.
intros b e.
rewrite (Zpower_nat_is_exp 1 e).
apply (f_equal (fun x => x * _)%Z).
apply Zmult_1_r.
Qed.

Section Beta.

Variable beta : radix.

Theorem radix_gt_0 : (0 < beta)%Z.
Proof.
apply Z.lt_le_trans with 2%Z.
easy.
apply Zle_bool_imp_le.
apply beta.
Qed.

Theorem Zpower_gt_0 :
  forall p,
  (0 <= p)%Z ->
  (0 < Zpower beta p)%Z.
Proof.
intros p Hp.
rewrite Zpower_Zpower_nat with (1 := Hp).
induction (Z.abs_nat p).
easy.
rewrite Zpower_nat_S.
apply Zmult_lt_0_compat with (2 := IHn).
apply radix_gt_0.
Qed.

Definition Zdigit n k := Z.rem (Z.quot n (Zpower beta k)) beta.

Theorem Zdigit_ge_Zpower_pos :
  forall e n,
  (0 <= n < Zpower beta e)%Z ->
  forall k, (e <= k)%Z -> Zdigit n k = Z0.
Proof.
intros e n Hn k Hk.
unfold Zdigit.
rewrite Z.quot_small.
apply Zrem_0_l.
split.
apply Hn.
apply Z.lt_le_trans with (1 := proj2 Hn).
replace k with (e + (k - e))%Z by ring.
rewrite Zpower_plus.
rewrite <- (Zmult_1_r (beta ^ e)) at 1.
apply Zmult_le_compat_l.
apply (Zlt_le_succ 0).
apply Zpower_gt_0.
now apply Zle_minus_le_0.
apply Zlt_le_weak.
now apply Z.le_lt_trans with n.
generalize (Z.le_lt_trans _ _ _ (proj1 Hn) (proj2 Hn)).
clear.
now destruct e as [|e|e].
now apply Zle_minus_le_0.
Qed.

End Beta.
