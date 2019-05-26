(* Fermat4.v *)

(***********************************)
(* Fermat's last theorem for n = 4 *)
(***********************************)

Require Export Diophantus20.

Lemma fermat4_weak: 
  ~ exists x : Z, exists y : Z, exists z : Z,
      0 < x /\ 0 < y /\ 0 < z /\ rel_prime y z /\ distinct_parity y z /\
      x * x * x * x + y * y * y * y = z * z * z * z.
Proof.
  intro; elim_hyps; rename x0 into y; rename x1 into z;
    cut ((z * z + y * y) * (z * z - y * y) = x * x * (x * x)).
  intro; elim (diophantus20_equiv y z); auto with zarith.
  generalize (Zmult_lt_0_compat _ _ H H); intro;
    generalize (Zmult_lt_0_compat _ _ H6 H6); clear H6; intro;
    rewrite <- H5 in H6; generalize (Zlt_gt _ _ H0); intro;
    cut (z * z + y * y > 0); auto with zarith; intro;
    generalize (Zlt_gt _ _ H6); intro; generalize (Zmult_gt_0_reg_l _ _ H8 H9);
    intro; generalize (Zgt_lt _ _ H10); intro; cut (y < z); auto with zarith.
  split;
    [ rewrite H5; apply Zge_le; apply sqr_pos
    | exists (x * x); intuition ].
  replace ((z * z + y * y) * (z * z - y * y)) with
    (z * z * z * z - y * y * y * y); try solve [ ring ]; rewrite <- H4; ring.
Qed.

Lemma fermat4: 
  ~(exists x : Z, exists y : Z, exists z : Z,
        0 < x /\ 0 < y /\ 0 < z /\
        x * x * x * x + y * y * y * y = z * z * z * z).
Proof.
  intro; elim_hyps; rename x0 into y; rename x1 into z;
    elim (Zgcd_spec y z); intros; elim_hyps; elim (gcd_rel_prime _ _ _ H3);
    intros; elim_hyps; rewrite H5 in H2; rewrite H6 in H2;
    cut (x * x * x * x = ((x0 * x0 * x0 * x0) * (x2 * x2 * x2 * x2 -
    x1 * x1 * x1 * x1)));
      [ intro; rewrite (Zmult_comm (x0 * x0 * x0 * x0)) in H8;
        generalize (Zdivide_intro _ _ _ H8); intro;
        generalize (divide_4 _ _ H9); clear H9; intro; destruct H9 as (q,H9);
        rewrite H9 in H8; rewrite H9 in H; rewrite H5 in H0;
        rewrite H6 in H1; generalize H4; clear H4; intro;
        elim (Zle_lt_or_eq _ _ H4); clear H4; intro; try (rewrite <- H4 in H;
        auto with zarith); rewrite Zmult_comm in H0; rewrite Zmult_comm in H1;
        generalize (Zmult_lt_0_reg_r _ _ H4 H); clear H; intro;
        generalize (Zmult_lt_0_reg_r _ _ H4 H0); clear H0; intro;
        generalize (Zmult_lt_0_reg_r _ _ H4 H1); clear H1; intro;
        cut (q * q * q * q + x1 * x1 * x1 * x1 = x2 * x2 * x2 * x2);
        [ clear x y z x0 H3 H5 H6 H2 H9 H8 H4; intro
        | replace (q * x0 * (q * x0) * (q * x0) * (q * x0)) with
          (q * q * q * q * (x0 * x0 * x0 * x0)) in H8; try solve [ ring ];
          cut (x0 * x0 * x0 * x0 > 0);
          [ intro; apply Zcompare_Eq_eq; rewrite (Zmult_compare_compat_r
            (q * q * q * q + x1 * x1 * x1 * x1) (x2 * x2 * x2 * x2) _ H10);
            elim (Zcompare_Eq_iff_eq ((q * q * q * q + x1 * x1 * x1 * x1) *
            (x0 * x0 * x0 * x0)) (x2 * x2 * x2 * x2 * (x0 * x0 * x0 * x0)));
            intros; apply H12; replace ((q * q * q * q + x1 * x1 * x1 * x1) *
            (x0 * x0 * x0 * x0)) with (q * q * q * q * (x0 * x0 * x0 * x0) +
            x1 * x1 * x1 * x1 * (x0 * x0 * x0 * x0)); try solve [ ring ];
            rewrite H8; ring
          | auto with zarith ] ]
      | replace (x0 * x0 * x0 * x0 * (x2 * x2 * x2 * x2 - x1 * x1 * x1 * x1))
        with (x0 * x2 * (x0 * x2) * (x0 * x2) * (x0 * x2) -
        x0 * x1 * (x0 * x1) * (x0 * x1) * (x0 * x1)); auto with zarith; ring ].
  elim (relp_parity _ _ H7); intro;
    [ apply fermat4_weak; exists q; exists x1; exists x2; intuition
    | unfold both_odd in H3; elim_hyps;
      rewrite <- (Zmult_assoc (q * q) q q) in H2;
      rewrite <- (Zmult_assoc (x1 * x1) x1 x1) in H2;
      rewrite <- (Zmult_assoc (x2 * x2) x2 x2) in H2;
      cut (is_pytha (q * q) (x1 * x1) (x2 * x2));
      try (unfold is_pytha, pos_triple; solve [ intuition ]); intro;
      elim (pytha_thm1 _ _ _ H5); clear H5; intros; elim_hyps;
      [ rewrite <- Zmult_assoc in H10; generalize (Zeven_def2 _ (ex_intro
        (fun x => x1 * x1 = 2 * x) (x3 * (x * x0)) H10)); clear H10; intro;
        generalize (Zeven_sqr2 _ H10); clear H10; intro;
        generalize (Zeven_not_Zodd _ H10); auto
      | unfold cond_pq, cond_pqb in H9; elim_hyps;
        cut (Zeven q); try (apply Zeven_sqr2; apply Zeven_def2;
        exists (x3 * x * x0); rewrite H5; ring); intro;
        cut (distinct_parity q x2); try (unfold distinct_parity; tauto);
        intro; cut (rel_prime q x2);
        [ intro; rewrite (Zmult_assoc (x2 * x2)) in H2; apply fermat4_weak;
          exists x1; exists q; exists x2; intuition; rewrite <- H2; ring
        | elim (Z_eq_dec x3 1); intro;
          [ rewrite a in H5; rewrite a in H6; rewrite Zmult_1_r in H5;
            rewrite Zmult_1_l in H6; rewrite Zmult_assoc in H5; apply prop3;
            rewrite H5; rewrite H6; apply relp_pq2; assumption
          | elimtype False; cut (x3 <> (-1)); auto with zarith; intro;
            cut (x3 | x1 * x1); try (exists (x0 * x0 - x * x); rewrite H10;
            ring); intro; cut (x3 | x2 * x2); try (exists (x * x + x0 * x0);
            rewrite H6; ring); intro;
            generalize (not_rel_prime2 _ _ _ H18 H19 b H17); intro;
            generalize (prop2 _ _ H7); auto ] ] ] ].
Qed.
