(* ArithCompl.v *)

(**********************************)
(* Some complements of arithmetic *)
(**********************************)

Require Export Wf_nat.
Require Export ZArith.
Require Export Znumtheory.
Require Export Reals.
Open Scope Z_scope.

Unset Standard Proposition Elimination Names.

(***************)
(* Regarding Z *)
(***************)

Definition is_sqr (n : Z) : Prop :=
  0 <= n /\ exists i : Z, i * i = n /\ 0 <= i.

Lemma is_sqr_sqr : forall n: Z, is_sqr (n * n).
Proof.
  intro; unfold is_sqr; split; try (apply Zge_le; apply sqr_pos);
    elim (Z_le_dec 0 n); intro;
      [ exists n; auto | exists (- n); intuition; ring ].
Qed.

Lemma is_sqr_mult : forall p q : Z, is_sqr p -> is_sqr q -> is_sqr (p * q).
Proof.
  unfold is_sqr; intros; elim H; clear H; intros; elim H0; clear H0; intros;
    elim H1; clear H1; intros; elim H1; clear H1; intros; elim H2; clear H2;
    intros; elim H2; clear H2; intros.
  split;
    [ auto with zarith
    | exists (x * x0); rewrite <- H1; rewrite <- H2; intuition; ring ].
Qed.

Lemma sqr_0 : forall z : Z, z * z = 0 -> z = 0.
Proof.
  intros; elim (Zmult_integral _ _ H); auto.
Qed.

Lemma sqr_compat : forall a b : Z, a * a = b * b -> a = b \/ a = -b.
Proof.
  intros; cut (a * a - b * b = 0); auto with zarith; clear H; intro;
    replace (a * a - b * b) with ((a + b) * (a - b)) in H; try ring;
    elim (Zmult_integral _ _ H); auto with zarith.
Qed.

Lemma sqr_le : forall a : Z, a <= a * a.
Proof.
  intro; elim (Z_le_dec 0 a); intro;
    [ elim (Z_eq_dec a 0); intro; try (rewrite a1; auto with zarith);
      pattern a at 1; replace a with (a * 1); try ring;
      apply (Zmult_le_compat a 1 a a)
    | generalize (sqr_pos a) ]; auto with zarith.
Qed.

Lemma sqr_spos : forall z : Z, z <> 0 -> z * z > 0.
Proof.
  intros; elim (not_Zeq _ _ H); clear H; intro.
  unfold Zlt in H; rewrite Zcompare_opp in H; fold (- (0) < - z) in H;
    simpl in H; cut (z * z = - z * - z);
      [ intro; rewrite H0; apply Zmult_gt_0_compat; auto with zarith
      | ring ].
  apply Zmult_gt_0_compat; auto with zarith.
Qed.

Lemma sqr_poss : forall z : Z, 0 < z * z -> z <> 0.
Proof.
intros;intro;rewrite H0 in H;auto with zarith.
Qed.

Lemma sqr_lt : forall a : Z, a <> 0 -> a <> 1 -> a < a * a.
Proof.
  intros; case (Z_le_dec 0 a); intro;
    [ pattern a at 1; rewrite <- Zmult_1_r; apply Zmult_lt_compat_l;
      auto with zarith
    | generalize (sqr_spos _ H); intro; auto with zarith ].
Qed.

Lemma sqr_sum : forall a b : Z, b <> 0 -> a * a + b * b <> 0.
Proof.
  intros; elim (Z_eq_dec a 0).
  intro; rewrite a0; simpl; generalize (sqr_spos b H); intro; auto with zarith.
  intro; generalize (sqr_spos a b0); intro; generalize (sqr_spos b H); intro;
    auto with zarith.
Qed.

Lemma sqr_sum2 : forall a b : Z, 0 <= a * a + b * b.
Proof.
  intros; generalize (Zplus_le_compat 0 (a * a) 0 (b * b)); simpl; intro;
    apply H; apply Zge_le; apply sqr_pos.
Qed.

Lemma sqr_sum3 : forall a b : Z, b > 0 -> a * a + b * b > 0.
Proof.
  intros; apply Zlt_gt; fold (0 + 0); apply Zplus_le_lt_compat;
    [ apply Zge_le; apply sqr_pos | apply Zgt_lt; auto with zarith ].
Qed.

Lemma sqr_sum4: forall a b : Z, a * a + b * b = 0 -> a = 0 /\ b = 0.
Proof.
  intros; elim (Z_eq_dec a 0); intro;
    [ elim (Z_eq_dec b 0); intro;
      [ auto | generalize (sqr_sum a _ b0); tauto ]
    | generalize (sqr_sum b _ b0); rewrite Zplus_comm in H; tauto].
Qed.

Lemma sqr_sub1 : forall a b : Z, 0 <= b -> b <= a -> 0 <= a * a - b * b.
Proof.
  intros; replace (a * a - b * b) with ((a + b) * (a - b)); try ring;
    apply Zmult_le_0_compat; auto with zarith.
Qed.

Lemma sqr_sub2 : forall a b : Z, 0 <= b -> b < a -> 0 < a * a - b * b.
Proof.
  intros; replace (a * a - b * b) with ((a + b) * (a - b)); try ring;
    apply Zmult_lt_0_compat; auto with zarith.
Qed.

Lemma sqr_sub3 : forall a b : Z, 0 < a -> 0 < b -> 0 < a * a - b * b -> b < a.
Proof.
  intros; replace (a * a - b * b) with ((a + b) * (a - b)) in H1; try ring;
    cut (0 < a + b); auto with zarith; intro; rewrite Zmult_comm in H1;
    generalize (Zmult_lt_0_reg_r _ _ H2 H1); clear H1 H2; intro;
    auto with zarith.
Qed.

Lemma sqr_2 : forall a : Z, 0 <= 2 * (a * a).
Proof.
  intro; generalize (sqr_pos a); auto with zarith.
Qed.

Lemma sqr_gt : forall a b : Z, a >= 0 -> a < b -> a * a < b * b.
Proof.
  intros; generalize (Zge_le _ _ H); clear H; intro;
    elim (Zle_lt_or_eq _ _ H); clear H; intro.
  generalize (Zmult_lt_compat_l _ _ _ H H0); intro; assert (0 < b);
    auto with zarith; generalize (Zmult_lt_compat_r _ _ _ H2 H0);
    auto with zarith.
  rewrite <- H; rewrite <- H in H0; apply Zgt_lt; auto with zarith.
Qed.

Lemma sqr_ge : forall a b : Z, a >= 0 -> a <= b -> a * a <= b * b.
Proof.
  intros; apply Zmult_le_compat; auto with zarith.
Qed.

Lemma Zle_square_simpl : forall n m:Z,
  0 <= n -> 0 <= m -> m * m <= n * n -> m <= n.
Proof.
  intros; elim (Zle_lt_or_eq _ _ H1); intro;
    [ generalize (Zlt_square_simpl _ m H H2)
    | generalize (Zeq_minus _ _ H2); clear H2; intro;
      replace (m * m - n * n) with ((m + n) * (m - n)) in H2; try ring;
      elim (Zmult_integral _ _ H2); clear H2; intro ]; auto with zarith.
Qed.

Lemma neq_1 : forall u v m n : Z,
  m <> 0 -> n <> 0 -> u * u = m * m + n * n -> v * v = n * n - m * m ->
  u <> 1 /\ v <> 1.
Proof.
  intros; case (Z_eq_dec u 1); intro; case (Z_eq_dec v 1); intro; try tauto;
    elimtype False;
      [ rewrite e in H1; simpl in H1; rewrite e0 in H2; simpl in H2;
        rewrite H2 in H1; cut (2 * (m * m) = 0); auto with zarith; intro;
        elim (Zmult_integral _ _ H3); auto with zarith; intro;
        generalize (sqr_0 _ H4); auto
      | rewrite e in H1; simpl in H1; generalize (sqr_pos m); intro;
        generalize (sqr_pos n); intro; cut (m * m = 0 \/ n * n = 0);
        try omega; intro; elim H5; clear H5; intros; generalize (sqr_0 _ H5);
        auto
      | rewrite e in H2; simpl in H2; replace (n * n - m * m) with
        ((n + m) * (n - m)) in H2; try ring; symmetry in H2;
        elim (Zmult_1_inversion_l _ _ H2); intro;
        rewrite Zmult_comm in H2; elim (Zmult_1_inversion_l _ _ H2);
        auto with zarith ].
Qed.

Lemma Zmult_eq_reg_l : forall z z1 z2, z * z1 = z * z2 -> z <> 0 -> z1 = z2.
Proof.
  intros; apply eq_IZR; generalize (IZR_eq _ _ H); intro;
    repeat rewrite mult_IZR in H1; generalize (not_O_IZR _ H0); intro;
    apply (Rmult_eq_reg_l (IZR z)); assumption.
Qed.

Lemma Zmult_neq_0 : forall a b : Z, a * b <> 0 -> a <> 0 /\ b <> 0.
Proof.
  intros; elim (Z_eq_dec a 0); intro;
    [ rewrite a0 in H; simpl in H; auto
    | elim (Z_eq_dec b 0); intro; try (rewrite a0 in H;
      rewrite Zmult_comm in H; simpl in H); auto ].
Qed.

Definition both_odd (x y : Z) := Zodd x /\ Zodd y.

Definition distinct_parity (a b : Z) :=
   (Zeven a) /\ (Zodd b) \/ (Zodd a) /\ (Zeven b).

Lemma ndistp_eq : forall a : Z, ~ distinct_parity a a.
Proof.
  red; intros; do 2 (elim H; clear H; intros);
    match goal with
    | id : Zeven _ |- _ => generalize (Zeven_not_Zodd _ id)
    end; auto.
Qed.

Lemma sqr_sum5 : forall a b: Z,
  a <> 0 -> b <> 0 -> distinct_parity a b -> a + b < a * a + b * b.
Proof.
  intros; case (Z_eq_dec a 1); intro;
    [ rewrite e; replace (1 * 1 + b * b) with (1+b*b);[idtac|ring];
      apply Zplus_lt_compat_l;
      case (Z_eq_dec b 1); intro;
      [ elimtype False; rewrite e in H1; rewrite e0 in H1;
        generalize (ndistp_eq 1); auto
      | apply sqr_lt; assumption ]
    | case (Z_eq_dec b 1); intro;
      [ rewrite e; replace (a * a + 1 * 1) with (a * a + 1); try ring;
        apply Zplus_lt_compat_r; apply sqr_lt; assumption
      | apply Zplus_lt_compat; apply sqr_lt; assumption ] ].
Qed.

Lemma Zeven_def1 : forall z : Z, (Zeven z) -> exists k : Z, z = 2 * k.
Proof.
  intros; generalize (Zeven_div2 _ H); intro; exists (Zdiv2 z); assumption.
Qed.

Lemma Zeven_def2 : forall z : Z, (exists k : Z, z = 2 * k) -> (Zeven z).
Proof.
  intros; elim H; intros; rewrite H0; elim x; intros; simpl; auto.
Qed.

Lemma Zodd_def1 : forall z : Z, (Zodd z) -> exists k : Z, z = 2 * k + 1.
Proof.
 apply Zodd_ex.
Qed.

Lemma Zodd_def2 : forall z : Z, (exists k : Z, z = 2 * k + 1) -> (Zodd z).
Proof.
  intros; elim H; intros; rewrite H0; elim x; intros; simpl; auto.
  elim p; simpl; auto.
Qed.

Lemma Zodd_0: forall n : Z, Zodd n -> n <> 0.
Proof.
  intros; intro; rewrite H0 in H; auto.
Qed.

Lemma Zodd_opp1 : forall a : Z, Zodd (-a) -> Zodd a.
Proof.
  intros; elim (Zodd_def1 _ H); clear H; intros; apply Zodd_def2;
    exists (-x - 1); rewrite <- (Zopp_involutive a); rewrite H; ring.
Qed.

Lemma Zodd_opp2 : forall a : Z, Zodd a -> Zodd (-a).
Proof.
  intros; elim (Zodd_def1 _ H); clear H; intros; apply Zodd_def2; rewrite H;
    exists (-x - 1); ring.
Qed.

Lemma Zodd_sum1 : forall a b : Z, Zodd a -> Zodd b -> Zeven (a + b).
Proof.
  intros; elim (Zodd_def1 _ H); clear H; intros; elim (Zodd_def1 _ H0);
    clear H0; intros; apply Zeven_def2; rewrite H; rewrite H0;
    exists (x + x0 + 1); ring.
Qed.

Lemma Zodd_sum2 : forall a b : Z, Zodd a -> Zodd b -> Zeven (a - b).
Proof.
  intros; generalize (Zodd_opp2 _ H0); clear H0; intro; unfold Zminus;
    apply Zodd_sum1; assumption.
Qed.

Lemma Zodd_sum3 : forall a b : Z, Zodd (a + 2 * b) -> Zodd a.
Proof.
  intros; elim (Zodd_def1 _ H); clear H; intros; cut (a = 2 * x + 1 - 2 * b);
    auto with zarith; clear H; intro; rewrite H; apply Zodd_def2;
    exists (x - b); ring.
Qed.

Lemma Zodd_mult : forall u v : Z,
  Zodd u -> Zodd v -> 
  (exists s : Z, 
    (exists w : Z, (u - v = 4 * s /\ u + v = 2 * w) \/
                   (u - v = 2 * w /\ u + v = 4 * s))).
Proof.
  intros; elim (Zodd_def1 u H); elim (Zodd_def1 v H0); intros k Hk k' Hk';
    elim (Zeven_odd_dec k); elim (Zeven_odd_dec k'); intros.
  elim (Zeven_def1 k a0); elim (Zeven_def1 k' a); intros t Ht t' Ht';
    split with (t - t'); split with (2 * t + 2 * t' + 1); left;
    auto with zarith.
  elim (Zeven_def1 k a); elim (Zodd_def1 k' b); intros t Ht t' Ht';
    split with (t + t' + 1); split with (2 * t - 2 * t' + 1); right;
    auto with zarith.
  elim (Zeven_def1 k' a); elim (Zodd_def1 k b); intros t Ht t' Ht';
    split with (t + t' +1); split with (2 * t' - 2 * t - 1); right;
    auto with zarith.
  elim (Zodd_def1 k b0); elim (Zodd_def1 k' b); intros t Ht t' Ht';
    split with (t - t'); split with (k' + k + 1); left; auto with zarith.
Qed.

Lemma Zeven_sqr1 : forall z : Z, Zeven z -> Zeven (z * z).
Proof.
  intros; generalize (Zeven_def1 _ H); clear H; intro; elim H; clear H; intros;
    rewrite H; apply Zeven_def2; exists (2 * x * x); ring.
Qed.

Lemma Zeven_sqr2 : forall n, Zeven (n * n) -> Zeven n.
Proof.
  induction n; auto; induction p; auto.
Qed.

Lemma Zodd_sqr1 : forall z : Z, Zodd z -> Zodd (z * z).
Proof.
  intros; generalize (Zodd_def1 _ H); clear H; intro; elim H; clear H; intros;
    rewrite H; apply Zodd_def2; exists (2 * x * x + 2 * x); ring.
Qed.

Lemma Zodd_sqr2 : forall n, Zodd (n * n) -> Zodd n.
Proof.
  induction n; auto; induction p; auto.
Qed.

Lemma distp_neq : forall p q : Z, distinct_parity p q -> p <> q.
Proof.
  intros; elim H; clear H; intro; elim H; clear H; intros;
    [ elim (Zeven_def1 _ H); clear H; intros; elim (Zodd_def1 _ H0); clear H0;
      intros; rewrite H; rewrite H0
    | elim (Zodd_def1 _ H); clear H; intros; elim (Zeven_def1 _ H0); clear H0;
      intros; rewrite H; rewrite H0 ]; auto with zarith.
Qed.

Lemma distp_sqr1 : forall p q : Z,
  (distinct_parity p q) -> (distinct_parity (p * p) (q * q)).
Proof.
  intros; unfold distinct_parity; do 2 (elim H; clear H; intros);
    [ generalize (Zeven_sqr1 _ H); clear H; intro; generalize (Zodd_sqr1 _ H0)
    | generalize (Zodd_sqr1 _ H); clear H; intro;
      generalize (Zeven_sqr1 _ H0) ]; tauto.
Qed.

Lemma distp_sqr2 : forall p q : Z,
  (distinct_parity (p * p) (q * q)) -> (distinct_parity p q).
Proof.
  intros; unfold distinct_parity; elim H; clear H; intros; elim H; clear H;
    intros; [ left | right ];
    repeat (match goal with
            | id : Zeven _ |- _ => generalize (Zeven_sqr2 _ id); clear id
            | id : Zodd _ |- _ => generalize (Zodd_sqr2 _ id); clear id
            end); tauto.
Qed.

Lemma distp_odd : forall p q : Z,
  (distinct_parity p q) -> both_odd (p + q) (q - p).
Proof.
  unfold distinct_parity, both_odd; intros; elim H; clear H; intro; elim H;
    clear H; intros;
      [ elim (Zeven_def1 _ H); clear H; intros; elim (Zodd_def1 _ H0);
        clear H0; intros
      | elim (Zodd_def1 _ H); clear H; intros; elim (Zeven_def1 _ H0);
        clear H0; intros ]; split; apply Zodd_def2; (exists (x + x0);
        rewrite H; rewrite H0; solve [ ring ]) || (exists (x0 - x); rewrite H;
        rewrite H0; solve [ ring ] ) || (exists (x0 - x - 1); rewrite H;
        rewrite H0; ring).
Qed.

Lemma not_divide1 : forall a b : Z,
  a <> 1 -> a <> -1 -> b <> 0 -> ~(a * b | b).
Proof.
  intros; red; intro; elim H2; clear H2; intros; rewrite Zmult_assoc in H2;
    pattern b at 1 in H2; rewrite -> (Zred_factor0 b) in H2;
    rewrite (Zmult_comm b 1) in H2; generalize (Zmult_reg_r _ _ _ H1 H2);
    clear H2; intro; generalize (sym_eq H2); clear H2; intro;
    rewrite Zmult_comm in H2; generalize (Zmult_1_inversion_l _ _ H2); tauto.
Qed.

Lemma not_divide2 : forall a b : Z, 0 < a -> 0 < b -> b < a -> ~(a | b).
Proof.
  intros; red; intro; elim H2; clear H2; intros; replace a with (1 * a) in H1;
    try ring; replace 0 with (0 * a) in H0; try ring; rewrite H2 in H1;
    rewrite H2 in H0; generalize (Zmult_lt_reg_r _ _ _ H H1); clear H1; intro;
    generalize (Zmult_lt_reg_r _ _ _ H H0); auto with zarith.
Qed.

Lemma rel_prime_1: forall a : Z, rel_prime 1 a.
Proof.
  intro; unfold rel_prime; apply Zis_gcd_intro; auto with zarith.
Qed.

Lemma prime_2 : prime 2.
Proof.
  apply prime_intro; auto with zarith; intros; case (Z_eq_dec n 1); intro;
    try (elimtype False; progress auto with zarith); rewrite e;
    apply rel_prime_1.
Qed.

Lemma rel_prime_sym : forall x y : Z, rel_prime x y -> rel_prime y x.
Proof.
  unfold rel_prime; intros; apply Zis_gcd_sym; assumption.
Qed.

Lemma rel_prime_dec : forall x y : Z, {rel_prime x y} + {~ rel_prime x y}.
Proof.
  intros; unfold rel_prime; elim (Zgcd_spec x y); intros; elim p; clear p;
    intros; elim (Z_eq_dec x0 1); intro;
      [ rewrite a in H; left; assumption
      | right; red; intro; elim H; clear H; intros; elim H1; clear H1; intros;
        generalize (H5 _ H H2); clear H H2 H3 H1 H4 H5; intro;
        elim (Zdivide_1  _ H); clear H; intro; auto with zarith ].
Qed.

Lemma not_rel_prime1 : forall x y : Z,
  ~ rel_prime x y -> exists d : Z, Zis_gcd x y d /\ d <> 1 /\ d <> -1.
Proof.
  unfold rel_prime; intros; elim (Zgcd_spec x y); intros; elim p; clear p;
    intros; exists x0; split;
      [ assumption
      | split;
        [ elim (Z_eq_dec x0 1); intro; [ rewrite a in H0; auto | assumption ]
        | elim (Z_eq_dec x0 (-1)); intro;
          [ rewrite a in H0; generalize (Zis_gcd_opp _ _ _ H0); simpl;
            clear H0; intro; generalize (Zis_gcd_sym _ _ _ H0); auto
          | assumption ] ] ].
Qed.

Lemma not_rel_prime2 : forall x y d : Z,
  (d | x) -> (d | y) -> d <> 1 -> d <> -1 -> ~ rel_prime x y.
Proof.
  intros; elim (rel_prime_dec x y); auto; unfold rel_prime; intro;
    elimtype False; elim a; clear a; intros; generalize (H5 _ H H0);
    clear H H0 H3 H4 H5; intro; elim (Zdivide_1 _ H); auto.
Qed.

Lemma gcd_rel_prime : forall x y d : Z,
  Zis_gcd x y d -> exists a : Z, exists b : Z,
    x = d * a /\ y = d * b /\ rel_prime a b.
Proof.
  intros; elim (Z_eq_dec d 0); intro;
    [ rewrite a in H; elim H; clear H; intros;
      destruct H as (q,H), H0 as (q0,H0); revert H H0;
      ring_simplify (q * 0); ring_simplify (q0 * 0); intros;
      exists 1; exists 1; rewrite a; intuition; apply rel_prime_1
    | elim H; clear H; intros; destruct H as (q,H), H0 as (q0,H0);
      exists q; exists q0; rewrite (Zmult_comm d q);
      rewrite (Zmult_comm d q0); intuition; elim (rel_prime_dec q q0); intro;
        [ auto
        | elimtype False; elim (not_rel_prime1 _ _ b0); clear b0; intros;
          elim H2; clear H2; intros; elim H2; clear H2; intros;
          generalize (Zdivide_mult_l _ _ d H2); intro; 
          generalize (Zdivide_mult_l _ _ d H4); intro; rewrite <- H in H6;
          rewrite <- H0 in H7; generalize (H1 _ H6 H7); clear H5 H6 H7; intro;
          elim H2; clear H2; intros; elim H4; clear H4; intros;
          rewrite H2 in H; clear H2; rewrite H4 in H0; clear H4;
          rewrite <- Zmult_assoc in H; rewrite <- Zmult_assoc in H0;
          generalize (Zdivide_intro (x0 * d) x _ H); clear H; intro;
          generalize (Zdivide_intro (x0 * d) y _ H0); clear H0; intro;
          generalize (H1 _ H H0); elim H3; clear H H0 H3; do 2 intro;
          apply not_divide1; auto ] ].
Qed.

Lemma relp_mult2 : forall a b : Z, rel_prime (a * b) a -> a = 1 \/ a = -1.
Proof.
  intros; elim (Z_eq_dec a 1); intro; try tauto; elim (Z_eq_dec a (-1)); intro;
    try tauto; elimtype False; generalize (Zdivide_refl a); intro;
    generalize (Zdivide_factor_r a b); intro;
    generalize (not_rel_prime2 _ _ _ H1 H0 b0 b1); auto.
Qed.

Lemma relp_mult3 : forall a b c : Z, rel_prime (a * b) c -> rel_prime a c.
Proof.
  intros; elim (rel_prime_dec a c); intro; try assumption; elimtype False;
    elim (not_rel_prime1 _ _ b0); clear b0; intros; do 2 (elim H0; clear H0;
    intros); elim H1; clear H1; intros; generalize (Zdivide_mult_l _ _ b H0);
    clear H0; intro; generalize (not_rel_prime2 _ _ _ H0 H2 H1 H4); auto.
Qed.

Lemma gcd2_rel_prime : forall a b s w : Z,
  (Zis_gcd a b 2) -> a = 4 * s -> b = 2 * w -> rel_prime s w.
Proof.
  intros; elim (gcd_rel_prime _ _ _ H); clear H; intros; rewrite H0 in H;
    rewrite H1 in H; do 2 (elim H; clear H; intros); elim H2; clear H2; intros;
    replace (4 * s) with (2 * (2 * s)) in H; try ring; cut (2 <> 0);
    auto with zarith; intro; generalize (Zmult_eq_reg_l _ _ _ H H4); intro;
    generalize (Zmult_eq_reg_l _ _ _ H2 H4); intro; rewrite <- H5 in H3;
    rewrite <- H6 in H3; rewrite Zmult_comm in H3;
    apply relp_mult3 with (b := 2); assumption.
Qed.

Lemma relp_neq : forall m n : Z, m <> 1 -> m <> -1 -> rel_prime m n -> m <> n.
Proof.
  intros; case (Z_eq_dec m n); auto; intro; elimtype False;
    generalize (Zdivide_refl m); intro; generalize (Zdivide_refl n);
    pattern n at 1; rewrite <- e; intro;
    generalize (not_rel_prime2 _ _ _ H2 H3 H H0); auto.
Qed.

Lemma prop2 : forall m n : Z, rel_prime m n -> rel_prime (m * m) (n * n).
Proof.
  intros; apply rel_prime_mult; apply rel_prime_sym; apply rel_prime_mult;
    apply rel_prime_sym; assumption.
Qed.

Lemma is_sqr_compat : forall k a : Z,
  k <> 0 -> is_sqr ((k * k) * a) -> is_sqr a.
Proof.
  intros; elim H0; clear H0; intros; do 2 (elim H1; clear H1; intros);
    elim (rel_prime_dec x k); intro;
      [ generalize (prop2 _ _ a0); clear a0; intro; rewrite H1 in H3;
        elim (relp_mult2 _ _ H3); intro;
          [ rewrite H4 in H1; rewrite Zmult_1_l in H1; rewrite <- H1;
            unfold is_sqr; intuition; exists x; intuition
          | elimtype False; generalize (sqr_pos k); intro; rewrite H4 in H5;
            auto with zarith ]
      | elim (not_rel_prime1 _ _ b); clear b; intros; elim H3; clear H3;
        intros; elim H4; clear H4; intros; elim (gcd_rel_prime _ _ _ H3);
        clear H3; intros; do 2 (elim H3; clear H3; intros); elim H6; clear H6;
        intros; rewrite H3 in H1; rewrite H6 in H1; elim (Z_eq_dec x0 0);
        intro; try (elimtype False; rewrite a0 in H6; simpl in H6; auto);
        replace (x0 * x1 * (x0 * x1)) with (x0 * x0 * (x1 * x1)) in H1;
        try ring; replace (x0 * x2 * (x0 * x2) * a) with
        (x0 * x0 * (x2 * x2 * a)) in H1; try ring; generalize (sqr_spos _ b);
        clear b; intro; cut ((x1 * x1) = x2 * x2 * a);
        try (apply Zcompare_Eq_eq;
        rewrite (Zmult_compare_compat_l (x1 * x1) (x2 * x2 * a) (x0 * x0) H8);
        elim (Zcompare_Eq_iff_eq (x0 * x0 * (x1 * x1))
        (x0 * x0 * (x2 * x2 * a))); auto); clear H1; intro;
        generalize (prop2 _ _ H7); clear H7; intro; rewrite H1 in H7;
        elim (relp_mult2 _ _ H7); intro;
          [ rewrite H9 in H1; rewrite Zmult_1_l in H1; rewrite <- H1;
            elim (Z_le_dec 0 x1); intro;
              [ unfold is_sqr; intuition; exists x1; intuition
              | split; [ apply Zge_le; apply sqr_pos | exists (-x1);
                intuition; ring ] ]
          | elimtype False; generalize (sqr_pos x2); intro; rewrite H9 in H10;
            auto with zarith ] ].
Qed.

Lemma divide_trans : forall a b c : Z, (a | b) -> (b | c) -> (a | c).
Proof.
  intros a b c (q,H) (q0,H0);
    rewrite H in H0; clear H; rewrite Zmult_assoc in H0;
    apply (Zdivide_intro a c (q0 * q)); assumption.
Qed.

Lemma divide_sum : forall a b c : Z, (a | b) -> (a | b + c) -> (a | c).
Proof.
  intros a b c (q,H) (q0,H0);
    cut (c = q0 * a - b); auto with zarith; clear H0; intro; rewrite H in H0;
    exists (q0 - q); rewrite H0; ring.
Qed.

Lemma divide_mult_l : forall a b c : Z, c <> 0 -> (c * a | c * b) -> (a | b).
Proof.
  intros a b c H (q,H0); replace (q * (c * a)) with (c * (q * a))
    in H0; try ring; generalize (Zmult_eq_reg_l _ _ _ H0 H); clear H0; intro;
    apply Zdivide_intro with (q := q); assumption.
Qed.

Lemma divide_0 : forall z : Z, (0 | z) -> z = 0.
Proof.
  intros; elim H; clear H; intros; auto with zarith.
Qed.

Lemma divide_2 : forall z : Z, 0 <= z -> z <> 0 -> z <> 1 -> (z | 2) -> z = 2.
Proof.
  intros; cut (2 <> 0); auto with zarith; intro;
    generalize (Zdivide_bounds _ _ H2 H3); clear H2; simpl; generalize H;
      generalize H0; generalize H1; elim z; simpl; intros;
      progress (auto with zarith) || (elimtype False; auto with zarith).
Qed.

Lemma divide_2b : forall z : Z,
  z <> 1 -> z <> -1 -> (z | 2) -> z = 2 \/ z = -2.
Proof.
  intros; elim (Z_eq_dec z 0); intro;
    [ elim H1; clear H1; intros; rewrite a in H1; auto with zarith
    | cut (2 <> 0); auto with zarith; intro;
      generalize (Zdivide_bounds _ _ H1 H2); clear H1; simpl; generalize H;
      generalize H0; generalize b; elim z; simpl; intros;
      progress (auto with zarith) || (generalize (Zle_0_pos p); intro;
      progress (auto with zarith)) || (rewrite <- Zopp_neg in H4;
      generalize (Zlt_neg_0 p); auto with zarith) ].
Qed.

Lemma divide_4 : forall a b : Z, (a * a * a * a | b * b * b * b) -> (a | b).
Proof.
  intros a b (q,H); cut (is_sqr ((a * a * (a * a)) * q));
    [ intro; elim (Z_eq_dec a 0); intro; try (rewrite a0 in H;
      rewrite (Zmult_comm q) in H; simpl in H; rewrite <- Zmult_assoc in H;
      do 2 (generalize (sqr_0 _ H); clear H; intro); rewrite H;
      apply Zdivide_0); cut (a * a <> 0); try (generalize (sqr_spos _ b0);
      solve [ auto with zarith ]); intro; generalize (is_sqr_compat _ _ H1 H0);
      clear H0; intro; elim H0; clear H0; intros; do 2 (elim H2; clear H2;
      intros); rewrite <- H2 in H; replace (x * x * (a * a * a * a)) with
      (a * a * x * (a * a * x)) in H; try ring; cut (0 <= a * a * x);
      try (apply Zmult_le_0_compat; try assumption; apply Zge_le;
      apply sqr_pos); intro; rewrite <- Zmult_assoc in H;
      elim (sqr_compat _ _ H); intro; try (elim (Z_eq_dec b 0); intro;
        [ rewrite a0; exists 0
        | elimtype False; generalize (sqr_spos _ b1); intro ];
      solve [ auto with zarith ]); cut (is_sqr (a * a * x));
      try (unfold is_sqr; intuition; elim (Z_le_dec b 0); intro;
      [ exists (-b) | exists b ]; intuition; rewrite <- H5; ring); intro;
      generalize (is_sqr_compat _ _ b0 H6); clear H6; intro; elim H6; clear H6;
      intros; do 2 (elim H7; clear H7; intros); rewrite <- H7 in H5;
      replace (a * a * (x0 * x0)) with (a * x0 * (a * x0)) in H5; try ring;
      elim (sqr_compat _ _ H5); intro; [ exists x0 | exists (-x0) ];
      rewrite H9; ring
    | split;
      [ replace (a * a * (a * a) * q) with (q * (a * a * a * a)); try ring;
        rewrite <- H; rewrite <- (Zmult_assoc (b * b)); apply Zge_le;
        apply sqr_pos
      | exists (b * b); split;
        [ rewrite Zmult_assoc; rewrite H; ring
        | apply Zge_le; apply sqr_pos ] ] ].
Qed.

Lemma divide_sqr : forall a b : Z, (a | b) -> (a * a | b * b).
Proof.
  intros a b (q,H); rewrite H; replace (q * a * (q * a)) with
    ((q * q) * (a * a)); try ring; apply Zdivide_factor_l.
Qed.

Lemma gcd2_relp_odd : forall u v : Z,
  Zodd u -> Zodd v -> rel_prime u v -> (Zis_gcd (u - v) (u + v) 2).
Proof.
  intros; elim (Zgcd_spec (u - v) (u + v)); intros; elim p; clear p; intros;
    elim H2; intros; generalize (Zdivide_plus_r _ _ _ H4 H5);
    ring_simplify (u - v + (u + v)); intro;
    generalize (Zdivide_opp_r _ _ H4); intro;
    generalize (Zdivide_plus_r _ _ _ H5 H8);
    ring_simplify (u + v + - (u - v));
    clear H8; intro; generalize (Zodd_sum2 _ _ H H0); intro;
    elim (Zeven_def1 _ H9); clear H9; intros; rewrite Zmult_comm in H9;
    generalize (Zdivide_intro _ _ _ H9); clear x0 H9; intro;
    generalize (Zodd_sum1 _ _ H H0); intro; elim (Zeven_def1 _ H10); clear H10;
    intros; rewrite Zmult_comm in H10; generalize (Zdivide_intro _ _ _ H10);
    clear x0 H10; intro; generalize (H6 _ H9 H10); clear H9 H10; intro;
    elim H9; clear H9; intros; rewrite Zmult_comm in H9; rewrite H9 in H7;
    rewrite H9 in H8; cut (2 <> 0); auto with zarith; intro;
    generalize (divide_mult_l _ _ _ H10 H7); clear H7; intro;
    generalize (divide_mult_l _ _ _ H10 H8); clear H8 H10; intro; elim H1;
    intros; generalize (H12 _ H7 H8); intro; elim (Zdivide_1 _ H13); intro;
    try (elimtype False; rewrite H14 in H9; progress auto with zarith);
    rewrite H14 in H9; simpl in H9; rewrite H9 in H2; assumption.
Qed.

Lemma rel_prime_opp : forall x y : Z, rel_prime x y -> rel_prime (-x) (-y).
Proof.
  unfold rel_prime; intros; do 2 (apply Zis_gcd_minus;
    rewrite Zopp_involutive); assumption.
Qed.

Lemma rel_prime_oppr : forall x y : Z, rel_prime x y -> rel_prime x (-y).
Proof.
  intros; unfold rel_prime; apply Zis_gcd_minus; apply Zis_gcd_sym;
    apply rel_prime_opp; assumption.
Qed.

Lemma rel_prime_2 : forall z : Z, Zodd z -> rel_prime 2 z.
Proof.
  intros; elim (rel_prime_dec 2 z); auto; intro; elimtype False;
    elim (Zodd_def1 _ H); clear H; intros; elim (not_rel_prime1 _ _ b);
    clear b; intros; do 2 (elim H0; clear H0; intros); elim H1; clear H1;
    intros; elim (divide_2b _ H1 H4 H0); clear H0 H3 H1 H4; intro;
    rewrite H0 in H2; clear H0; elim H2; clear H2; intros; rewrite H0 in H;
    clear H0; auto with zarith.
Qed.

Lemma relp_mult1 : forall a b c d k: Z, 0 <= a -> 0 <= b -> 0 < c -> 0 <= d ->
  a = k * c -> b = k * d -> rel_prime a b -> k = 1.
Proof.
  intros; rewrite H3 in H5; rewrite H4 in H5; rewrite H3 in H; clear H3 H4;
    elim H5; clear H5; intros; elim (Zdivide_1 k); auto with zarith; intro;
    rewrite H6 in H; clear H6; auto with zarith.
Qed.

Lemma relp_parity :
  forall x y : Z, (rel_prime x y) -> (distinct_parity x y) \/ (both_odd x y).
Proof.
  intros; unfold distinct_parity, both_odd; elim (Zeven_odd_dec x); intro;
    elim (Zeven_odd_dec y); intro; intuition.
  elimtype False; unfold rel_prime in H; elim (Zeven_def1 _ a); clear a;
    intros; elim (Zeven_def1 _ a0); clear a0; intros;
    rewrite Zmult_comm in H1; rewrite Zmult_comm in H0;
    generalize (Zdivide_intro _ _ x0 H0); clear H0; intro;
    generalize (Zdivide_intro _ _ x1 H1); clear H1; intro;
    elim H; clear H; intros; generalize (H3 _  H0 H1); clear H3; intro;
    elim H3; clear H3; intros; auto with zarith.
Qed.

Lemma relp_sum :
  forall m n : Z, (rel_prime (m + n) (m - n)) -> (rel_prime m n).
Proof.
  intros; elim (rel_prime_dec m n); intro; try assumption.
  elimtype False; elim (not_rel_prime1 _ _ b); clear b; intros; elim H0;
    clear H0; intros; elim H1; clear H1; intros; elim H0; clear H0; intros;
    elim H; clear H; intros; generalize (Zdivide_plus_r _ _ _ H0 H3); intro;
    generalize (Zdivide_minus_l _ _ _ H0 H3); clear H H0 H3 H4 H5; intro;
    generalize (H6 _ H7 H); clear H H6 H7; intro; elim (Zdivide_1 _ H);
    auto.
Qed.

Lemma prop1 : forall m n : Z,
  rel_prime m n -> distinct_parity m n -> rel_prime (m + n) (n - m).
Proof.
  unfold rel_prime; intros; elim (distp_odd _ _ H0); clear H0; intros;
    elim (Zgcd_spec (m + n) (n - m)); intros; elim p; clear p; intros;
    elim (Z_eq_dec x 1); intro;
      [ rewrite a in H2; assumption
      | elimtype False; elim H2; clear H2; intros;
        generalize (Zdivide_plus_r _ _ _ H2 H4);
        ring_simplify (m + n + (n - m)); intro;
        generalize (Zdivide_minus_l _ _ _ H2 H4);
        ring_simplify (m + n - (n - m));
        intro; elim (Zdivide_dec x 2); intro;
          [ elim (Z_eq_dec x 0); intro;
            [ rewrite a0 in a; clear a0; elim a; clear a; intros;
              auto with zarith
            | generalize (divide_2 _ H3 b0 b a); clear a; intro;
              rewrite H8 in H2; rewrite H8 in H4; clear x H3 b H5 H6 H7 b0 H8;
              destruct H2 as (q,H2), H4 as (q0,H3);
              rewrite Zmult_comm in H2; rewrite Zmult_comm in H3;
              generalize (Zeven_def2 _ (ex_intro (fun x => m + n = 2 * x)
              q H2)); clear q H2; intro; generalize (Zeven_not_Zodd _ H2);
              auto ]
          | elim (Zdivide_dec 2 x); intro;
            [ generalize (divide_trans _ _ _ a H2);
              clear H H1 x H3 b H2 H4 H5 H6 H7 b0 a; intro; destruct H as (q,H);
              rewrite Zmult_comm in H; generalize (Zeven_def2 _
              (ex_intro (fun x => m + n = 2 * x) q H)); clear H; intro;
              generalize (Zeven_not_Zodd _ H); auto
            | generalize (prime_rel_prime _ prime_2 _ b1); intro;
              generalize (rel_prime_sym _ _ H8); clear H8; intro;
              generalize (Gauss _ _ _ H6 H8); clear H6; intro;
              generalize (Gauss _ _ _ H7 H8); clear H7; intro;
              cut (x <> -1); auto with zarith; intro;
              generalize (not_rel_prime2 _ _ _ H7 H6 b H9); auto ] ] ].
Qed.

Lemma prop2b : forall m n : Z, rel_prime m n -> rel_prime m (m * m + n * n).
Proof.
  intros; elim (rel_prime_dec m (m * m + n * n)); intros; auto;
    elimtype False; elim (not_rel_prime1 _ _ b); clear b; intros;
    do 2 (elim H0; clear H0; intros); elim H1; clear H1; intros;
    generalize (Zdivide_mult_l _ _ m H0); intro;
    generalize (divide_sum _ _ (n * n) H5 H2); intro;
    generalize (prop2 _ _ H); clear H; intro;
    apply (not_rel_prime2 _ _ _ H5 H6 H1 H4); assumption.
Qed.

Lemma prop2c : forall m n : Z, rel_prime m n -> rel_prime m (m * m - n * n).
Proof.
  intros; elim (rel_prime_dec m (m * m - n * n)); intros; auto;
    elimtype False; elim (not_rel_prime1 _ _ b); clear b; intros;
    do 2 (elim H0; clear H0; intros); elim H1; clear H1; intros;
    generalize (Zdivide_mult_l _ _ m H0); intro;
    generalize (divide_sum _ _ (- (n * n)) H5 H2); intro;
    generalize (Zdivide_opp_r_rev _ _ H6); clear H6; intro;
    generalize (prop2 _ _ H); clear H; intro;
    apply (not_rel_prime2 _ _ _ H5 H6 H1 H4); assumption.
Qed.

Lemma prop3 : forall m n : Z, rel_prime (m * m) (n * n) -> rel_prime m n.
Proof.
  intros; elim H; intros; unfold rel_prime; apply Zis_gcd_intro;
    auto with zarith.
Qed.

Definition R_prime (x y : Z) := 1 < x /\ 1 < y /\ x < y.

Definition f_Z (x : Z) := Zabs_nat x.

Lemma R_prime_wf : well_founded R_prime.
Proof.
  apply (well_founded_lt_compat _ f_Z R_prime); unfold R_prime, f_Z; intros;
    apply Zabs_nat_lt; intuition.
Qed.

Lemma ind_prime : forall P : Z -> Prop,
  (forall x : Z, (forall y : Z, (R_prime y x -> P y)) -> P x) ->
  forall x : Z, P x.
Proof.
  intros; generalize (well_founded_ind R_prime_wf P); auto.
Qed.

Lemma prime_dec_gen : forall a b : Z, 1 < b -> b < a ->
  (forall c : Z, b < c < a -> rel_prime c a) -> prime a \/ ~ prime a.
Proof.
  intros a b; pattern b;
    match goal with
    | |- (?p _) =>
      simpl; case (Z_lt_dec 1 a); intro; try (right; red; intro; elim H2;
      clear H2; intros; progress auto); apply (ind_prime p); intros;
      case (rel_prime_dec x a); intro;
        [ case (Z_eq_dec x 2); intro;
          [ left; rewrite e in H2; rewrite e in r; generalize (rel_prime_1 a);
            intro; apply prime_intro; try assumption; intros;
            case (Z_eq_dec n 1); intro; try (rewrite e0; assumption);
            case (Z_eq_dec n 2); intro; try (rewrite e0; assumption); apply H2;
            auto with zarith
          | apply (H (x - 1)); try unfold R_prime; auto with zarith; intros;
            case (Z_eq_dec c x); intro; try (rewrite e; assumption); apply H2;
            auto with zarith ]
        | right; red; intro; elim H3; clear H3; intros; cut (1 <= x < a);
          auto with zarith; intro; generalize (H4 _ H5); auto ]
    end.
Qed.

Lemma prime_dec : forall a : Z, prime a \/ ~ prime a.
Proof.
  intros; case (Z_eq_dec a 2); intro;
    [ left; rewrite e; apply prime_2
    | case (Z_lt_dec 1 a); intro; try (right; red; intro; elim H; clear H;
      intros; progress auto); apply (prime_dec_gen a (a - 1));
      auto with zarith; intros; elimtype False; auto with zarith ].
Qed.

Lemma not_prime_gen : forall a b : Z, 1 < a -> 1 < b -> b < a -> ~ prime a ->
  (forall c : Z, b < c < a -> rel_prime c a) ->
  exists q : Z, exists b : Z, a = q * b /\ 1 < q /\ 1 < b.
Proof.
  induction b using ind_prime; intros.
  destruct (Zdivide_dec b a) as [(q,H5)|n].
  - exists q; exists b; intuition;
    apply (Zmult_gt_0_lt_reg_r 1 q b); auto with zarith.
  - case (rel_prime_dec b a); intro.
    * case (Z_eq_dec b 2); intro.
      + absurd (prime a); try assumption.
        apply prime_intro; auto; rewrite e in H4; rewrite e in r;
        generalize (rel_prime_1 a); intros; case (Z_eq_dec n0 1); intro;
        try (rewrite e0; assumption); case (Z_eq_dec n0 2); intro;
        try (rewrite e0; assumption); apply H4; auto with zarith.
      + assert (R_prime (b - 1) b) by (unfold R_prime; intuition).
        assert (1 < b - 1) by auto with zarith.
        assert (b - 1 < a) by auto with zarith.
        assert (forall c : Z, (b - 1) < c < a -> rel_prime c a)
        by (intros; case (Z_eq_dec c b); intro;
            try (rewrite e; assumption);
            apply H4; auto with zarith).
        elim (H _ H5 H0 H6 H7 H3 H8); intros; elim H9; clear H9; intros;
        exists x; exists x0; intuition.
    * elim (not_rel_prime1 _ _ n0); clear n0; intros;
      do 2 (elim H5; clear H5; intros); elim H6; clear H6; intros;
      destruct H7 as (q,H7).
      assert (x <> 0)
      by (assert (a <> 0) by auto with zarith; rewrite H7 in H10;
          elim (Zmult_neq_0 _ _ H10); auto).
      case (Z_le_dec 0 x); intro.
      + exists q; exists x; intuition; rewrite H7 in H0.
        assert (0 < q * x) by auto with zarith.
        assert (0 < x) by auto with zarith.
        generalize (Zmult_lt_0_reg_r _ _ H12 H11); intro;
        case (Z_eq_dec q 1); auto with zarith; intro; elimtype False;
        rewrite e in H7; rewrite Zmult_1_l in H7; destruct H5 as (q0,H5);
        rewrite H5 in H1; cut (0 < q0 * x); auto with zarith;
        intro; generalize (Zmult_lt_0_reg_r _ _ H12 H14); intro;
        rewrite H7 in H2; rewrite <- (Zmult_1_l x) in H2;
        rewrite H5 in H2; generalize (Zmult_lt_reg_r _ _ _ H12 H2);
        auto with zarith.
      + exists (-q); exists (-x); intuition; try (rewrite H7; ring);
        rewrite H7 in H0; replace (q * x) with (-q * -x) in H0 by ring.
        assert (0 < -q * -x) by auto with zarith.
        assert (0 < -x) by auto with zarith.
        generalize (Zmult_lt_0_reg_r _ _ H12 H11);
        intro; case (Z_eq_dec q (-1)); auto with zarith; intro;
        elimtype False; rewrite e in H7; rewrite Zmult_comm in H7;
        rewrite <- Zopp_eq_mult_neg_1 in H7; destruct H5 as (q0,H5);
        replace (q0 * x) with (-q0 * -x) in H5 by ring;
        rewrite H5 in H1;
        assert (0 < -q0 * -x) by auto with zarith;
        generalize (Zmult_lt_0_reg_r _ _ H12 H14); intro;
        rewrite <- (Zmult_1_l a) in H2; rewrite H7 in H2; rewrite H5 in H2;
        generalize (Zmult_lt_reg_r _ _ _ H12 H2); auto with zarith.
Qed.

Lemma not_prime : forall a : Z, 1 < a -> ~ prime a ->
  exists q : Z, exists b : Z, a = q * b /\ 1 < q /\ 1 < b.
Proof.
  intros; case (Z_eq_dec a 2); intro;
    [ elimtype False; rewrite e in H0; generalize (prime_2); auto
    | apply (not_prime_gen a (a - 1)); auto with zarith; intros;
      elimtype False; auto with zarith ].
Qed.

Definition R_fact (x y : Z) :=
  1 < x /\ 1 < y /\ exists q : Z, y = q * x /\ 1 < q.

Lemma R_fact_wf : well_founded R_fact.
Proof.
  apply (well_founded_lt_compat _ f_Z R_fact); unfold R_fact, f_Z; intros;
    apply Zabs_nat_lt; intuition; elim H2; clear H2; intros; elim H1; clear H1;
    intros; replace x with (1 * x); try ring; rewrite H1;
    apply Zmult_lt_compat_r; auto with zarith.
Qed.

Lemma ind_fact : forall P : Z -> Prop,
  (forall x : Z, (forall y : Z, (R_fact y x -> P y)) -> P x) ->
  forall x : Z, P x.
Proof.
  intros; generalize (well_founded_ind R_fact_wf P); auto.
Qed.

Lemma Zfact : forall a : Z, 1 < a -> exists b : Z, (b | a) /\ prime b.
Proof.
  intro a; pattern a;
    match goal with
    | |- (?p _) =>
      simpl; apply (ind_fact p); intros; case (prime_dec x); intro;
        [ exists x; intuition
        | elim (not_prime _ H0 H1); intros; do 2 (elim H2; clear H2; intros);
          elim H3; clear H3; intros; cut (exists b : Z, (b | x1) /\ prime b);
          try (apply H; try assumption; unfold R_fact; intuition; exists x0;
          intuition); intro; do 2 (elim H5; clear H5; intros); exists x2;
          intuition; elim H5; clear H5; intros; rewrite H5 in H2;
          rewrite Zmult_assoc in H2; apply (Zdivide_intro _ _ _ H2) ]
    end.
Qed.

Definition R_p4 (x y : Z) :=
  0 <= x /\ 1 < y /\ exists d : Z, y = d * d * x /\ 1 < d.

Lemma R_p4_wf : well_founded R_p4.
Proof.
  apply (well_founded_lt_compat _ f_Z R_p4); unfold R_p4, f_Z; intros;
    apply Zabs_nat_lt; intuition; elim H2; clear H2; intros; elim H1; clear H1;
    intros; cut (1 < x0 * x0); try (cut (1 >= 0); auto with zarith; intro;
    generalize (sqr_gt _ _ H3 H2); simpl; progress auto); intro; 
    cut (y <> 0); auto with zarith; intro; rewrite H1 in H4;
    elim (Zmult_neq_0 _ _ H4); intros; rewrite H1; pattern x at 1;
    replace x with (1 * x); try ring; apply Zmult_lt_compat_r;
    auto with zarith.
Qed.

Lemma ind_p4 : forall P : Z -> Prop,
  (forall x : Z, (forall y : Z, (R_p4 y x -> P y)) -> P x) ->
  forall x : Z, P x.
Proof.
  intros; generalize (well_founded_ind R_p4_wf P); auto.
Qed.

Lemma sqr_prime1 :
  forall a : Z, is_sqr a -> forall b : Z, (b | a) -> prime b -> (b * b | a).
Proof.
  intros; elim H; clear H; intros; elim H2; clear H2; intros; elim H2;
    clear H2; intros; rewrite <- H2 in H0; elim (prime_mult _ H1 _ _ H0);
    intro; generalize (divide_sqr _ _ H4); clear H4; intro; rewrite H2 in H4;
    assumption.
Qed.

Lemma sqr_prime2 : forall a b c : Z,
  (a | b) -> (a * a | b * c) -> prime a -> (a * a | b) \/ (a | c).
Proof.
  intros; elim H; intros q H2; elim H0; intros q0 H3;
  rewrite H2 in H3; elim H1; intros;
    replace (q * a * c) with (a * (q * c)) in H3; try ring;
    replace (q0 * (a * a)) with (a * (q0 * a)) in H3; try ring;
    cut (a <> 0); auto with zarith; intro;
    generalize (Zmult_eq_reg_l _ _ _ H3 H6); clear H3; intro;
    generalize (Zdivide_intro _ _ _ H3); clear H3; intro;
    elim (prime_mult _ H1 _ _ H3); try tauto; intro; elim H7; intros;
    rewrite H8 in H2; rewrite <- Zmult_assoc in H2;
    generalize (Zdivide_intro _ _ _ H2); tauto.
Qed.

Lemma prop4 : forall p q : Z,
  0 <= p -> 0 <= q -> rel_prime p q -> is_sqr (p * q) -> is_sqr p /\ is_sqr q.
Proof.
  split; generalize H2; generalize H1; generalize H0; generalize H;
    [ pattern p
    | pattern q ];
    match goal with
    | |- (?p _) =>
      simpl; apply (ind_p4 p); intros
    end;
    match goal with
    | |- is_sqr ?x => elim (Z_lt_dec 1 x); intro;
      [ idtac
      | elim (Z_eq_dec x 0); intro;
        [ rewrite a; unfold is_sqr; intuition; exists 0; intuition
        | elim (Z_eq_dec x 1); intro;
          [ rewrite a; unfold is_sqr; intuition; exists 1; intuition
          | elimtype False; auto with zarith ] ] ]
    end; generalize (sqr_prime1 _ H7); intro; elim (Zfact _ a); intros; 
    elim H9; clear H9; intros; (generalize (Zdivide_mult_l _ _ q H9); intro;
    generalize (H8 _ H11 H10)) || (generalize (Zdivide_mult_r _ p _ H9); intro;
    generalize (H8 _ H11 H10)); intro; elim (sqr_prime2 _ _ _ H9 H12 H10) ||
    (rewrite (Zmult_comm p) in H12; elim (sqr_prime2 _ _ _ H9 H12 H10));
    intros; try (elimtype False; elim H10; intros; cut (x0 <> 1);
    auto with zarith; intro; cut (x0 <> -1); auto with zarith; intro;
    generalize (not_rel_prime2 _ _ _ H9 H13 H16 H17); progress auto ||
    (generalize (rel_prime_sym _ _ H6); auto)); elim H13;
    intros q0 ?; cut (is_sqr q0); try (intro; elim H15; clear H15; intros;
    do 2 (elim H16; clear H16; intros); rewrite <- H16 in H14; unfold is_sqr;
    intuition; rewrite H14; exists (x0 * x1); split; try ring; elim H10;
    intros; apply Zmult_le_0_compat; auto with zarith); elim H10; intros;
    cut (0 <= q0); try (cut (x0 <> 0); auto with zarith; intro;
    generalize (sqr_spos _ H17); clear H17; intro; cut (0 < x);
    auto with zarith; intro; rewrite H14 in H18;
    generalize (Zmult_gt_0_lt_0_reg_r _ _ H17 H18); progress auto with zarith);
    intro; (apply H3; try assumption; [ unfold R_p4; intuition; exists x0;
    intuition; rewrite H14; ring | rewrite H14 in H6;
    (apply (relp_mult3 q0 (x0 * x0)) || (apply rel_prime_sym;
    apply (relp_mult3 q0 (x0 * x0)); apply rel_prime_sym)); assumption
    | rewrite H14 in H7; (replace (q0 * (x0 * x0) * q) with
    (x0 * x0 * (q0 * q)) in H7; try ring; apply (is_sqr_compat x0);
    progress auto with zarith) || (replace (p * (q0 * (x0 * x0))) with
    (x0 * x0 * (p * q0)) in H7; try ring; apply (is_sqr_compat x0);
    auto with zarith) ]).
Qed.

Lemma prop4b : forall p q : Z, 0 <= p -> 0 <= q -> p <= q -> rel_prime p q ->
  is_sqr (p * (q * (q * q - p * p))) ->
  is_sqr p /\ is_sqr q /\ is_sqr (q * q - p * p).
Proof.
  intros; generalize (prop2c _ _ H2); intro;
    generalize (rel_prime_oppr _ _ H4); clear H4; intro;
    replace (- (p * p - q * q)) with (q * q - p * p) in H4; try ring;
    generalize (rel_prime_sym _ _ H2); intro; generalize (prop2c _ _ H5);
    clear H5; intro; generalize (rel_prime_sym _ _ H4); clear H4; intro;
    generalize (rel_prime_sym _ _ H5); clear H5; intro;
    generalize (rel_prime_mult _ _ _ H4 H5); clear H4 H5; intro;
    generalize (rel_prime_sym _ _ H4); clear H4; intro;
    rewrite Zmult_assoc in H3; cut (0 <= p * q); auto with zarith; intro;
    cut (0 <= q * q - p * p); try (apply sqr_sub1; assumption); intro;
    generalize (prop4 _ _ H5 H6 H4 H3); clear H3 H4 H5 H6; intro; elim H3;
    clear H3; intros; generalize (prop4 _ _ H H0 H2 H3); tauto.
Qed.

Lemma relp_pq1 : forall p q : Z, p >= 0 -> p <= q -> (rel_prime p q) ->
  (distinct_parity p q) -> (rel_prime (q * q - p * p) (p * p + q * q)).
Proof.
  intros; cut (rel_prime (p * p) (q * q));
    [ clear H1; intro; cut (distinct_parity (p * p) (q * q));
      [ clear H2; intro; apply rel_prime_sym; apply prop1; try apply sqr_ge;
        assumption
      | apply (distp_sqr1 _ _ H2) ]
    | generalize (rel_prime_mult _ _ _ H1 H1); clear H1; intro;
      generalize (rel_prime_sym _ _ H1); clear H1; intro;
      generalize (rel_prime_mult _ _ _ H1 H1); clear H1; intro;
      apply rel_prime_sym; assumption ].
Qed.

Lemma relp_pq2 : forall p q : Z, (rel_prime p q) -> (distinct_parity p q) ->
  (rel_prime (2 * p * q) (p * p + q * q)).
Proof.
  intros; generalize (prop2b _ _ H); intro; generalize (rel_prime_sym _ _ H);
    intro; generalize (prop2b _ _ H2); clear H2; intro;
    rewrite Zplus_comm in H2; generalize (rel_prime_sym _ _ H1); clear H1;
    intro; generalize (rel_prime_sym _ _ H2); clear H2; intro;
    generalize (rel_prime_mult _ _ _ H1 H2); clear H1 H2; intro;
    cut (Zodd (p * p + q * q));
      [ intro; generalize (rel_prime_2 _ H2); clear H2; intro;
        generalize (rel_prime_sym _ _ H2); clear H2; intro;
        generalize (rel_prime_mult _ _ _ H2 H1); clear H1 H2; intro;
        apply rel_prime_sym; rewrite <- Zmult_assoc; assumption
      | generalize (distp_sqr1 _ _ H0); clear H0; intro;
        elim (distp_odd _ _ H0); auto ].
Qed.

(***************)
(* Regarding R *)
(***************)

Lemma not_IZR_0 : forall a : Z, (IZR a <> 0)%R -> a <> 0.
Proof.
  intros; red; intro; rewrite H0 in H; simpl in H; auto.
Qed.

Lemma sqr_inv : forall a b : Z, b <> 0 ->
  (1 + IZR a * / IZR b * (IZR a * / IZR b) <> 0)%R.
Proof.
  intros; cut (1 + IZR a * / IZR b * (IZR a * / IZR b) =
              ((IZR a * IZR a + IZR b * IZR b) / (IZR b * IZR b)))%R.
  intro; rewrite H0; unfold Rdiv; split_Rmult;
    [ discrR; apply sqr_sum; assumption
    | apply Rinv_neq_0_compat; split_Rmult; discrR; assumption ].
  field; discrR; assumption.
Qed.

Lemma Rdiv_ge_0 : forall a b : R, (a >= 0 -> b > 0 -> a / b >= 0)%R.
Proof.
  intros; unfold Rge; elim H; clear H; intro;
    [ left; unfold Rdiv, Rgt; unfold Rgt in H0; unfold Rgt in H;
      generalize (Rinv_0_lt_compat _ H0); clear H0; intro; 
      replace 0%R with (0 * / b)%R; [ apply Rmult_lt_compat_r; auto | ring ]
    | right; rewrite H; field; auto with real ].
Qed.

Lemma Rcross_prod : forall a b c d : R,
  (b <> 0 -> d <> 0 -> a / b = c / d -> a * d = b * c)%R.
Proof.
  intros; generalize (Rmult_eq_compat_l (b * d) _ _ H1); clear H1; intro;
    replace (b * d * (a / b))%R with (a * d)%R in H1;
      [ replace (b * d * (c / d))%R with (b * c)%R in H1;
        [ assumption | field; assumption ]
      | field; assumption ].
Qed.

(***********************)
(* Regarding rationals *)
(***********************)

Definition frac (a b : Z) := ((IZR a) / (IZR b))%R.
Definition is_rat (r : R) :=
  exists pq : Z * Z, let (p,q) := pq in ~(q = 0) /\ r = (frac p q).
Definition is_ratp (c : R * R) := let (x,y) := c in (is_rat x) /\ (is_rat y).

Lemma frac_eq : forall a b c d : Z,
  b <> 0 -> c <> 0 -> (frac a (b * c)) = (frac d c) -> a = b * d.
Proof.
  unfold frac; intros; cut (IZR (b * c) <> 0%R);
    [ intro; cut (IZR c <> 0%R);
      [ intro; generalize (Rcross_prod _ _ _ _ H2 H3 H1); clear H1; intro;
        rewrite mult_IZR in H1;
        cut (IZR c * IZR a = IZR c * (IZR b * IZR d))%R;
          [ clear H1; intro; generalize (Rmult_eq_reg_l _ _ _ H1 H3); clear H1;
            intro; rewrite <- mult_IZR in H1; apply eq_IZR; assumption
          | rewrite (Rmult_comm (IZR c) (IZR a)); rewrite H1; ring ]
      | apply not_O_IZR; assumption ]
    | rewrite mult_IZR; split_Rmult; apply not_O_IZR; assumption ].
Qed.

Lemma frac_rat : forall a b : Z,
  b <> 0 -> (frac a b >= 0)%R -> (frac a b <= 1)%R ->
    a >= 0 /\ b > 0 /\ a <= b \/ a <= 0 /\ b < 0 /\ b <= a.
Proof.
  unfold frac, Rdiv; intros; generalize (Rge_le _ _ H0); clear H0; intro; 
    elim (Z_dec b 0); intros; try (elim a0; clear a0; intros);
    [ right; cut (0 < -b); auto with zarith; intro;
      generalize (IZR_lt _ _ H2); clear H2; intro; simpl in H2;
      replace 0%R with (/ IZR (- b) * 0)%R in H0; try ring;
      rewrite (Rmult_comm (IZR a)) in H0;
      cut (/ IZR b * IZR a = / IZR (- b) * IZR (- a))%R;
      try (repeat rewrite Ropp_Ropp_IZR; field; 
      try rewrite <- Ropp_Ropp_IZR; apply not_O_IZR; auto with zarith);
      intro; rewrite H3 in H0; generalize (Rinv_0_lt_compat _ H2); clear H2;
      intro; generalize (Rmult_le_reg_l _ _ _ H2 H0); intro;
      generalize (le_O_IZR _ H4); clear H4; intro; rewrite Rmult_comm in H1;
      rewrite H3 in H1; replace 1%R with (/ IZR (- b) * IZR (- b))%R in H1;
      try (field; apply not_O_IZR; auto with zarith);
      generalize (Rmult_le_reg_l _ _ _ H2 H1); intro;
      generalize (le_IZR _ _ H5); clear H5; intro; intuition
    | left; generalize (Zgt_lt _ _ b0); intro; generalize (IZR_lt _ _ H2);
      clear H2; intro; simpl in H2; replace 0%R with (/ IZR b * 0)%R in H0;
      try ring; rewrite (Rmult_comm (IZR a)) in H0;
      generalize (Rinv_0_lt_compat _ H2); clear H2; intro;
      generalize (Rmult_le_reg_l _ _ _ H2 H0); intro;
      generalize (le_O_IZR _ H3); clear H3; intro; rewrite Rmult_comm in H1;
      replace 1%R with (/ IZR b * IZR b)%R in H1; try (field; apply not_O_IZR;
      auto with zarith); generalize (Rmult_le_reg_l _ _ _ H2 H1); intro;
      generalize (le_IZR _ _ H4); clear H4; intro; intuition
    | contradiction ].
Qed.

Lemma frac_simp : forall a b c : Z,
  b <> 0 -> c <> 0 -> frac (c * a) (c * b) = frac a b.
Proof.
  intros; unfold frac; repeat rewrite mult_IZR; field; split;
    apply not_O_IZR; assumption.
Qed.

Lemma frac_opp : forall a b : Z, b <> 0 -> frac (-a) (-b) = frac a b.
Proof.
  intros; replace (-a) with (-1 * a); try replace (-b) with (-1 * b);
    try rewrite frac_simp; auto with zarith.
Qed.

Lemma relp_rat : forall r : R, (is_rat r) -> (r >= 0)%R -> (r <= 1)%R ->
  exists pq : Z * Z,
  let (p,q) := pq in
  (p >= 0) /\ (q > 0) /\ (p <= q) /\ (rel_prime p q) /\ r = (frac p q).
Proof.
  intros; elim H; clear H; induction x; intro; elim H; clear H; intros;
    elim (rel_prime_dec a b); intro;
      [ rewrite H2 in H0; rewrite H2 in H1; elim (frac_rat _ _ H H0 H1); intro;
        [ exists (a, b); tauto
        | exists (-a, -b); intuition; 
          [ apply rel_prime_opp | rewrite (frac_opp a b H) ]; assumption ]
      | elim (not_rel_prime1 _ _ b0); clear b0; intros; elim H3; clear H3;
        intros; elim (gcd_rel_prime _ _ _ H3); clear H3; intros; elim H3;
        clear H3; intros; elim H3; clear H3; intros; elim H5; clear H5; intros;
        rewrite H5 in H; elim (Zmult_neq_0 _ _ H); clear H;
        intros; rewrite H3 in H2; rewrite H5 in H2;
        rewrite (frac_simp x0 _ _ H7 H) in H2; rewrite H2 in H0;
        rewrite H2 in H1; elim (frac_rat _ _ H7 H0 H1); intro;
        [ exists (x0, x1); intuition
        | exists (-x0, -x1); intuition;
          [ apply rel_prime_opp
          | rewrite (frac_opp x0 x1 H7) ]; assumption ] ].
Qed.

(***************************************)
(* Adding lemmas in the auto databases *)
(***************************************)

Hint Resolve rel_prime_sym : zarith.

Hint Immediate sqr_0 sqr_pos sqr_spos sqr_sum sqr_sum2 sqr_sum3 sqr_sum4
  sqr_sum5 sqr_sub1 sqr_sub2 sqr_sub3 sqr_ge : zarith.

Hint Immediate sqr_inv Rdiv_ge_0 : reals.
