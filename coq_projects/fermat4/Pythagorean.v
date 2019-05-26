(* Pythagorean.v *)

(***********************)
(* Pythagorean triples *)
(***********************)

Require Export Tactics.

(* A non nul predicate *)
Definition nnl_triple (a b c : Z) := ~(a = 0) /\ ~(b = 0) /\ ~(c = 0).

(* A positive predicate *)
Definition pos_triple (a b c : Z) := (a >= 0) /\ (b >= 0) /\ (c >= 0).

(* A Pythagorean predicate *)
Definition is_pytha (a b c : Z) := (pos_triple a b c) /\ a * a + b * b = c * c.

(* Unit circle and D_r *)
Definition in_ucirc (x y : R) := (x * x + y * y = 1)%R.
Definition D_r (r x y : R) := (y = r * (x + 1))%R.

(******************************)
(* Set of Pythagorean triples *)
(******************************)

(* step1 *)

Lemma pytha_ucirc1 : forall a b c : Z,
  (c > 0) -> (is_pytha a b c) -> (in_ucirc (frac a c) (frac b c)).
Proof.
  intros; unfold in_ucirc; unfold frac; field_simplify_eq.
  unfold is_pytha in H0; elim H0; intros. 
  repeat rewrite pow_IZR. rewrite <- plus_IZR. simpl Z_of_nat.
  ring_simplify [(sym_eq H2)] (c^2);trivial.
  discrR; auto with zarith.
Qed.

Lemma pytha_ucirc2 : forall a b c : Z, (a >= 0) /\ (b >= 0) /\ (c > 0) ->
  (in_ucirc (frac a c) (frac b c)) -> (is_pytha a b c).
Proof.
  unfold in_ucirc; unfold frac; unfold is_pytha; intros; split.
  unfold pos_triple; auto with zarith.
 apply eq_IZR; apply (Rmult_eq_reg_l (/ (IZR c * IZR c))).
 pattern (IZR c * IZR c)%R at 2; rewrite <- mult_IZR;rewrite Rinv_l.
 rewrite Rinv_mult_distr.
 rewrite <- H0; rewrite plus_IZR; repeat rewrite mult_IZR; field.
 discrR; auto with zarith.
 discrR; auto with zarith.
 discrR; auto with zarith.
 rewrite mult_IZR; split_Rmult; discrR; auto with zarith.
 apply Rinv_neq_0_compat; split_Rmult; discrR; auto with zarith.
Qed.

(* step 2 *)

(* Intersection between the unit circle and D_r *)
Definition interCDr (r x y : R) := (in_ucirc x y) /\ (D_r r x y).

(* Points of the intersection *)
Definition p1 := (-1,0)%R.
Definition p2 (r : R) :=
  let den := (1 + r * r)%R in
  ((1 - r * r) / den, 2 * r / den)%R.

(* Equality over points *)
Definition eqp (p1 p2 : R * R) := (fst p1) = (fst p2) /\ (snd p1)= (snd p2).

(* Total order over points (using R) *)
Lemma ordp : forall p1 p2 : R * R, (eqp p1 p2) \/ ~(eqp p1 p2).
Proof.
  intros p3 p4. unfold eqp; elim p3; elim p4; intros; simpl.
  elim (Req_dec a a0); elim (Req_dec b b0); intuition.
Qed.

(* Characterization of the intersection *)
Lemma interCDr_sol : forall r x y : R,
  (interCDr r x y) -> (eqp (x,y) p1) \/ (eqp (x,y) (p2 r)).
Proof.
  unfold interCDr;unfold in_ucirc;unfold D_r;unfold eqp, p1, p2;simpl.
  intros;elim H;intros;rewrite H1 in H0.
  cut (((1 + r * r) * Rsqr x + 2 * r * r * x + (r * r - 1)) = 0)%R.
  intro;cut ((1 + r * r) <> 0)%R.
  intro;cut (Delta_is_pos (mknonzeroreal (1 + r * r) H3) (2 * r * r)
            (r * r - 1))%R.
  intro;generalize (Rsqr_sol_eq_0_0 (mknonzeroreal (1 + r * r) H3) (2 * r * r)
                                    (r * r - 1) x H4 H2)%R.
  unfold sol_x1, sol_x2;unfold Delta;unfold Rsqr;simpl.
  cut ((2 * r * r * (2 * r * r) - 4 * (1 + r * r) * (r * r - 1))%R = 4%R).
  intro;rewrite H5. replace (4)%R with (2*2)%R by auto.
  rewrite sqrt_square.
  induction 1;[right|left].
  split;[rewrite H6;field;assumption
        |rewrite H1;rewrite H6;field;assumption].
  split;[rewrite H6;field;assumption
        |rewrite H1;rewrite H6;field;assumption].
  unfold Rle;left;prove_sup.
  ring.
  unfold Delta_is_pos;unfold Delta;unfold Rsqr;simpl;
    ring_simplify (2 * r * r * (2 * r * r) - 4 * (1 + r * r) * (r * r - 1))%R;
    unfold Rle;left;prove_sup.
  apply Rgt_not_eq;unfold Rgt;rewrite Rplus_comm;apply Rle_lt_0_plus_1;
    fold (Rsqr r);elim (Req_dec r 0);intro;
    [rewrite H3;rewrite Rsqr_0;unfold Rle;right;auto
    |unfold Rle;left;apply Rsqr_pos_lt;assumption].
  pattern 1%R at 2;rewrite <- H0;unfold Rsqr;ring.
Qed.

(* step 3 *)

Lemma rat_coo1 : forall x y : R, (in_ucirc x y) /\
  (exists r : R, (is_rat r) /\ (interCDr r x y)) -> (is_ratp (x,y)).
Proof.
  unfold in_ucirc, is_ratp, is_rat.
  unfold frac; intros; elim H; intros; elim H1; intros; elim H2; intros;
    elim H3; intro; elim x1;intros; elim H5; intros;
    elim (interCDr_sol x0 x y H4); unfold eqp, p1, p2; simpl; intro; elim H8;
    intros; rewrite H9; rewrite H10.
  split.
  exists (-1,1); split; [ auto with zarith | simpl; field; discrR ].
  exists (0,1); split; [ auto with zarith | simpl; field; discrR ].
  split.
  exists (b * b - a * a, a * a + b * b); split.
  auto with zarith.
  rewrite H7; rewrite <- Z_R_minus; rewrite plus_IZR; repeat rewrite mult_IZR;
    field; split;discrR; auto with zarith reals.
  exists (2 * a * b * b, (a * a + b * b) * b); split.
  apply not_IZR_0; rewrite mult_IZR; split_Rmult; discrR; auto with zarith.
  rewrite H7; repeat rewrite mult_IZR; rewrite plus_IZR;
    repeat rewrite mult_IZR; simpl; field; split; discrR;
    auto with zarith reals.
Qed.

Lemma rat_coo2 : forall x y : R, (in_ucirc x y) /\ (is_ratp (x,y)) ->
  exists r : R, (is_rat r) /\ (interCDr r x y).
Proof.
  unfold in_ucirc, is_ratp, is_rat, interCDr.
  unfold frac, in_ucirc, D_r; intros.
  elim (Req_dec x (-1)%R); intro.
  exists 1%R; split.
  exists (1,1); split; [ auto with zarith | field; discrR ].
  elim H; intros; split.
  assumption.
  rewrite H0; rewrite H0 in H1; ring_simplify (1 * (-1 + 1))%R;
    cut ((1 + y * y) = 1)%R;
    [ intro; apply Rsqr_0_uniq; unfold Rsqr;
      apply (Rplus_0_r_uniq 1 (y * y) H3)%R
    | pattern 1%R at 2; rewrite <- H1; ring ].
  exists (y / (x + 1))%R; cut ((x + 1) <> 0)%R;
    [ intro; split
    | rewrite <- (Ropp_involutive 1); fold (x - -1)%R; apply Rminus_eq_contra;
      assumption ].
  elim H; intros; elim H3; intros; elim H4; intro; elim x0; intros; elim H6;
    intros; elim H5; intro; elim x1; intros; elim H9; intros; rewrite H8;
    rewrite H11.
  cut (a + b <> 0);
    [ intro
    | apply not_IZR_0;
      cut (((IZR a / IZR b + 1) * IZR b)%R = (IZR a + IZR b)%R);
        [ intro; rewrite plus_IZR; rewrite <- H12; split_Rmult;
          [ rewrite <- H8; assumption
          | discrR; assumption ]
        | field; discrR; assumption ] ].
  exists (a0 * b, b0 * (a + b)); split.
  apply not_IZR_0; rewrite mult_IZR; rewrite plus_IZR; split_Rmult; discrR;
    assumption.
  repeat rewrite mult_IZR; rewrite plus_IZR; field; discrR; try assumption.
  repeat split; discrR; try assumption; fold (IZR a / IZR b)%R;
    rewrite <- H8; assumption.
  split; [ elim H; intros; assumption | field; assumption ].
Qed.

(* step 4 *)

(* Positivity predicate over points *)
Definition is_posp (c : R * R) := (fst c >= 0)%R /\ (snd c >= 0)%R.

(* Predicate for the positive rational coordinates of the unit circle *)
Definition is_ucp (c : R * R) :=
  (in_ucirc (fst c) (snd c)) /\ (is_ratp c) /\ (is_posp c).

(* Positive rational coordinates of the unit circle *)
Definition ucp (p q : Z) :=
  let pr := (IZR p) in
  let qr := (IZR q) in
  let den := (pr * pr + qr * qr)%R in
  ((qr * qr - pr * pr) / den, (2 * pr * qr) / den)%R.

(* A basic condition over p and q *)
Definition cond_pqb (p q : Z) := p >= 0 /\ q > 0 /\ p <= q /\ (rel_prime p q).

(* Set of positive rational coordinates of the unit circle *)
Definition in_ucp_setb (x y : R) :=
  exists p : Z, exists q : Z,
  x = (fst (ucp p q)) /\ y = (snd (ucp p q)) /\ (cond_pqb p q).

Lemma rat_pos_coo1 : forall x y : R, (is_ucp (x,y)) ->
  exists r : R, (is_rat r) /\ (r >= 0)%R /\ (r <= 1)%R /\ x = (fst (p2 r)) /\
  y = (snd (p2 r)).
Proof.
  intros; unfold is_ucp in H; elim H; intros; elim H1; intros;
    elim (rat_coo2 x y (conj H0 H2)); intros; elim H4; intros.
  elim (interCDr_sol x0 x y).
  unfold eqp; simpl; intro; elim H7; intros; elim H3; simpl; intros;
    rewrite H8 in H10; elimtype False; generalize (Rge_le (-1) 0 H10)%R;
    fold (~ (0 <= -1)%R); apply Rlt_not_le; prove_sup.
  cut (0 < / (1 + x0 * x0))%R;
    [ intro
    | apply Rinv_0_lt_compat; rewrite <- (Rplus_0_r 0)%R;
      apply Rplus_lt_le_compat;
        [ prove_sup
        | fold (Rsqr x0); elim (Req_dec x0 0); intro;
          [ rewrite H7; rewrite Rsqr_0; unfold Rle; right; auto
          | unfold Rle; left; apply Rsqr_pos_lt; assumption ] ] ].
  unfold eqp; simpl; intro; elim H8; intros; elim H3; simpl; rewrite H9; 
    rewrite H10; intros; exists x0; split.
  assumption.
  split.
  generalize (Rge_le (2 * x0 / (1 + x0 * x0)) 0 H12); intro;
    rewrite Rmult_comm in H13;
    rewrite <- (Rmult_0_l (2 / (1 + x0 * x0))) in H13;
    cut (0 < 2 / (1 + x0 * x0))%R;
      [ intro; rewrite Rmult_comm in H13; unfold Rdiv in H13;
        rewrite (Rmult_assoc x0 2) in H13;
        rewrite (Rmult_comm x0 (2 * / (1 + x0 * x0)))%R in H13;
        generalize (Rmult_le_reg_l (2 / (1 + x0 * x0)) 0 x0 H14 H13); intro;
        apply Rle_ge; assumption
      | unfold Rdiv; prove_sup; assumption ].
  split.
  generalize (Rge_le ((1 - x0 * x0) / (1 + x0 * x0)) 0 H11); intro;
    unfold Rdiv in H13; rewrite Rmult_comm in H13;
    rewrite <- (Rmult_0_r (/ (1 + x0 * x0)))%R in H13;
    generalize (Rmult_le_reg_l (/ (1 + x0 * x0)) 0 (1 - x0 * x0) H7 H13)%R;
    intro; generalize (Rplus_le_compat_r (x0 * x0) 0 (1 - x0 * x0) H14)%R;
    intro; rewrite Rplus_0_l in H15; unfold Rminus in H15;
    rewrite Rplus_assoc in H15; rewrite Rplus_opp_l in H15;
    rewrite Rplus_0_r in H15; rewrite <- (Rmult_1_r 1) in H15;
    fold (Rsqr x0) in H15; fold (Rsqr 1) in H15;
    apply (Rsqr_incr_0_var x0 1 H15); unfold Rle; left; prove_sup.
  auto.
  assumption.
Qed.

Lemma rat_pos_coo2 : forall x y : R, (is_ucp (x,y)) -> (in_ucp_setb x y).
Proof.
  intros; elim (rat_pos_coo1 x y H); simpl; intros; elim H0; intros; elim H2;
    intros; elim H4; intros; elim H6; intros; elim (relp_rat x0 H1 H3 H5);
    intro; elim x1; unfold frac; intros; elim H9; intros; elim H11; intros;
    elim H13; intros; elim H15; intros; unfold in_ucp_setb; simpl;
    unfold cond_pqb; exists a; exists b; rewrite H7; rewrite H8; rewrite H17.
  cut (b <> 0); auto with zarith; intro.
  split.
  field; split; discrR; auto with zarith reals.
  split.
  field; split; discrR; auto with zarith reals.
  tauto.
Qed.

(* Step 5 *)

(* The full condition over p and q *)
Definition cond_pq (p q : Z) := cond_pqb p q /\ (distinct_parity p q).

(* The (new) set of positive rational coordinates of the unit circle *)
Definition in_ucp_set (x y : R) :=
  exists p : Z, exists q : Z,
  (x = (fst (ucp p q)) /\ y = (snd (ucp p q)) \/
   x = (snd (ucp p q)) /\ y = (fst (ucp p q))) /\ (cond_pq p q).

(* Inclusion of in_ucp_set in in_ucp_setb *)
Lemma nrat_pos_coo1 : forall x y : R, (in_ucp_set x y) -> (in_ucp_setb x y).
Proof.
  unfold in_ucp_set, in_ucp_setb, cond_pq, cond_pqb; simpl; intros; elim_hyps.
  exists x0; exists x1; intuition.
  exists (x1 - x0); exists (x0 + x1); rewrite plus_IZR; rewrite <- Z_R_minus;
    rewrite H; rewrite H5.
  replace
   ((IZR x1 - IZR x0) * (IZR x1 - IZR x0) +
    (IZR x0 + IZR x1) * (IZR x0 + IZR x1))%R with
   (2 * (IZR x0 * IZR x0 + IZR x1 * IZR x1))%R by  ring.
  split;[idtac|split]; try (field; neq_0;apply sqr_sum; auto with zarith).
  do 3 try split; auto with zarith.
  generalize (prop1 _ _ H4 H1); auto with zarith.
Qed.

(* Inclusion of in_ucp_setb in in_ucp_set *)
Lemma nrat_pos_coo2 : forall x y : R, (in_ucp_setb x y) -> (in_ucp_set x y).
Proof.
  unfold in_ucp_setb, in_ucp_set, cond_pq, cond_pqb, distinct_parity; simpl;
    intros; elim_hyps.
  elim (relp_parity x0 x1 H4); intro.
  exists x0; exists x1; intuition.
  unfold both_odd in H5; elim_hyps; generalize (Zodd_def1 _ H5); clear H5;
    intro; generalize (Zodd_def1 _ H6); clear H6; intro; elim_hyps.
  exists (x2 - x3); exists (x2 + x3 + 1); split;
    [ right; rewrite H; rewrite H0; rewrite H5; rewrite H6; atomic_IZR; simpl;
      split; field; split; neq_0; apply sqr_sum; auto with zarith
    | rewrite H5 in H1; rewrite H6 in H2; rewrite H5 in H3; rewrite H6 in H3;
      do 4 try split; auto with zarith ].
  apply rel_prime_sym; apply relp_sum; ring_simplify (x2 + x3 + 1 + (x2 - x3));
    ring_simplify (x2 + x3 + 1 - (x2 - x3)); generalize H5; clear H5;
    ring_simplify (2 * x3 + 1);
    intro; generalize H6; clear H6; ring_simplify (2 * x2 + 1); intro;
    rewrite <- H5; rewrite <- H6; auto with zarith.
  elim (Zeven_odd_dec x2); intro; elim (Zeven_odd_dec x3); intro; Zparity_hyps;
    rewrite H7; rewrite H8;
    [ left; split; [ apply Zeven_def2; exists (x4 - x5)
                   | apply Zodd_def2; exists (x4 + x5) ]
    | right; split; [ apply Zodd_def2; exists (x5 - x4 - 1)
                    | apply Zeven_def2; exists (x5 + x4 + 1) ]
    | right; split; [ apply Zodd_def2; exists (x4 - x5)
                    | apply Zeven_def2; exists (x4 + x5 + 1) ]
    | left; split; [ apply Zeven_def2; exists (x4 - x5)
                   | apply Zodd_def2; exists (x4 + x5 + 1) ] ]; ring.
Qed.

(* step 6 *)

(* The set of Pythagorean triples *)
Definition pytha_set (a b c : Z) :=
  exists p : Z, exists q : Z, exists m : Z,
    (a = m * (q * q - p * p) /\ b = 2 * m * (p * q) \/
     a = 2 * m * (p * q) /\ b = m * (q * q - p * p)) /\
    c = m * (p * p + q * q) /\ m >= 0 /\ (cond_pq p q).

(* Relative primality and fractions *)
Lemma relp_frac : forall a b c d : Z,
  (b <> 0) -> (d <> 0) -> (frac a b) = (frac c d) -> (rel_prime c d) ->
  exists m : Z, m <> 0 /\ b = m * d.
Proof.
  unfold frac; intros.
  cut (c * b = a * d).
  intro; cut (d | c * b);
    [ intro; cut (rel_prime d c);
        try (intro; generalize (Gauss d c b H4 H5); intro; destruct H6 as (q,H6);
        exists q; intuition; rewrite H7 in H6); auto with zarith
    | apply (Zdivide_intro _ _ a H3) ].
  generalize (Rmult_eq_compat_l (IZR b * IZR d) _ _ H1); clear H1; intro;
    replace (IZR b * IZR d * (IZR a / IZR b))%R
            with ((IZR a) * (IZR d))%R in H1;
      [ replace (IZR b * IZR d * (IZR c / IZR d))%R
                with ((IZR c) * (IZR b))%R in H1;
        [ repeat rewrite <- mult_IZR in H1; generalize (eq_IZR _ _ H1); auto
        | field; discrR; assumption ]
      | field; discrR; assumption ].
Qed.

Lemma pytha_thm1 : forall a b c : Z, (is_pytha a b c) -> (pytha_set a b c).
Proof.
  do 3 intro; elim (Z_gt_dec c 0); [ idtac
    | unfold is_pytha, pytha_set, pos_triple, cond_pq, cond_pqb ]; intros.
  generalize (pytha_ucirc1 _ _ _ a0 H); intro;
    cut (is_ucp (frac a c, frac b c));
      [ clear H0; intro; generalize (rat_pos_coo2 _ _ H0); clear H0; intro;
        generalize (nrat_pos_coo2 _ _ H0); clear H0; intro;
        unfold in_ucp_set, cond_pq, cond_pqb in H0;
        unfold pytha_set, cond_pq, cond_pqb; simpl in H0; elim_hyps;
        generalize (relp_pq1 _ _ H1 H4 H5 H2); intro;
        generalize (Zgt_lt _ _ a0); intro; generalize (Zlt_not_eq _ _ H8);
        clear H8; intro; generalize (sym_not_eq H8); clear H8; intro;
        generalize (Zgt_lt _ _ H3); intro; generalize (Zlt_not_eq _ _ H9);
        clear H9; intro; generalize (sym_not_eq H9); clear H9; intro;
        (cut (x * x + x0 * x0 <> 0); [ intro | auto with zarith ];
        (cut ((IZR x0 * IZR x0 - IZR x * IZR x) /
             (IZR x * IZR x + IZR x0 * IZR x0) =
             frac (x0 * x0 - x * x) (x * x + x0 * x0))%R;
          [ intro | head_IZR; auto ];
        (cut (2 * IZR x * IZR x0 / (IZR x * IZR x + IZR x0 * IZR x0) =
             frac (2 * x * x0) (x * x + x0 * x0))%R;
          [ intro | head_IZR; auto ])))
      | idtac ].
  rewrite H11 in H0; clear H11; rewrite H12 in H6; clear H12;
    generalize (relp_frac _ _ _ _ H8 H10 H0 H7); intro; elim_hyps;
    rewrite H12 in H0; rewrite H12 in H6; exists x; exists x0; exists x1;
    generalize (frac_eq _ _ _ _ H11 H10 H0); clear H0; intro;
    generalize (frac_eq _ _ _ _ H11 H10 H6); clear H6; intro;
    rewrite H0; rewrite H6; rewrite H12; intuition; (left; split; ring) ||
    (cut (x1 * (x * x + x0 * x0) > 0);
      [ intro; rewrite Zmult_comm in H13; cut (x * x + x0 * x0 > 0);
        try (intro; generalize (Zmult_gt_0_reg_l _ _ H14 H13));
        auto with zarith
      | rewrite <- H12; assumption ]).
  rewrite H11 in H6; clear H11; rewrite H12 in H0; clear H12;
    generalize (relp_frac _ _ _ _ H8 H10 H6 H7); intro; elim_hyps;
    rewrite H12 in H0; rewrite H12 in H6; exists x; exists x0; exists x1;
    generalize (frac_eq _ _ _ _ H11 H10 H0); clear H0; intro;
    generalize (frac_eq _ _ _ _ H11 H10 H6); clear H6; intro;
    rewrite H0; rewrite H6; rewrite H12; intuition; (right; split; ring) ||
    (cut (x1 * (x * x + x0 * x0) > 0);
      [ intro; rewrite Zmult_comm in H13; cut (x * x + x0 * x0 > 0);
        try (intro; generalize (Zmult_gt_0_reg_l _ _ H14 H13)); 
        auto with zarith
      | rewrite <- H12; assumption ]).
  unfold is_ucp, is_ratp, is_posp; simpl; intuition; unfold is_rat;
    unfold is_pytha, pos_triple in H; elim_hyps; generalize (Zgt_lt _ _ a0);
    intro; generalize (IZR_lt _ _ H4); intro; simpl in H5;
    fold (IZR c > 0)%R in H5;
    [ exists (a, c); intuition | exists (b, c); intuition
    | unfold frac; generalize (IZR_ge _ _ H); clear H; intro; simpl in H
    | unfold frac; generalize (IZR_ge _ _ H2); clear H2; intro; simpl in H2 ];
    auto with reals.
  elim_hyps; cut (c = 0);
    [ intro; exists 0; exists 1; exists 0; rewrite H3; simpl; intuition;
      (left; rewrite H3 in H0; simpl in H0; progress auto with zarith)
      || (compute; auto with zarith)
    | auto with zarith ].
Qed.

Lemma pytha_thm2 : forall a b c : Z, (pytha_set a b c) -> (is_pytha a b c).
Proof.
  unfold pytha_set, is_pytha, cond_pq, cond_pqb, pos_triple; intros; elim_hyps;
    rewrite H; rewrite H7; rewrite H0; split; ring || (intuition; apply Zle_ge;
    generalize (Zge_le _ _ H2); clear H2; intro; generalize (Zgt_lt _ _ H4);
    clear H4; intro; generalize (Zlt_le_weak _ _ H4); intro;
    repeat apply Zmult_le_0_compat; auto with zarith).
Qed.

(* A specific case *)

Definition pytha_set_even (a b c : Z) :=
  exists p : Z, exists q : Z, exists m : Z,
    a = m * (q * q - p * p) /\ b = 2 * m * (p * q) /\
    c = m * (p * p + q * q) /\ m >= 0 /\ (cond_pq p q).

Lemma pytha_thm3 : forall a b c : Z,
  is_pytha a b c -> Zodd a -> pytha_set_even a b c.
Proof.
  intros; elim (pytha_thm1 _ _ _ H); clear H; intros;
    unfold cond_pq, cond_pqb in H; elim_hyps;
    unfold pytha_set_even, cond_pq, cond_pqb; exists x; exists x0; exists x1;
    try solve [ intuition ].
  elimtype False; rewrite <- Zmult_assoc in H;
  generalize (Zeven_def2 _ (ex_intro (fun x => a = 2 * x) (x1 * (x * x0)) H));
  intro; generalize (Zeven_not_Zodd _ H9); auto.
Qed.
