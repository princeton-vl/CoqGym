(* Diophantus20.v *)

(****************************)
(* Diophantus' 20th problem *)
(****************************)

Require Export Descent.
Require Export Pythagorean.

(*************************)
(* Some auxiliary lemmas *)
(*************************)

Lemma multiple4_2: forall u v : Z,
  Zodd v -> Zodd u -> v <= u -> rel_prime u v -> 1 < u -> 1 < v ->
  exists two : Z * Z,
    let (s, w) := two in
    (u - v = 4 * s /\ u + v = 2 * w \/
     u - v = 2 * w /\ u + v = 4 * s) /\ 0 < s /\ 0 < w /\ rel_prime s w.
Proof.
  intros; elim (Zodd_mult u v H0 H); intros; elim H5; clear H5; intros;
    elim_hyps; split with (x,x0); intuition; cut (u <> 1); auto with zarith;
    intro; cut (u <> -1); auto with zarith; intro.
  apply (Zmult_lt_0_reg_r 4 x); auto with zarith; rewrite Zmult_comm;
    rewrite <- H5; generalize (relp_neq _ _ H7 H8 H2); auto with zarith.
  apply (gcd2_rel_prime (u - v) (u + v) x x0); auto; apply gcd2_relp_odd; auto.
  apply (Zmult_lt_0_reg_r 2 x0); auto with zarith; rewrite Zmult_comm;
    rewrite <- H5; generalize (relp_neq _ _ H7 H8 H2); auto with zarith.
  apply (gcd2_rel_prime (u + v) (u - v) x x0); auto; apply Zis_gcd_sym;
    apply gcd2_relp_odd; auto.
Qed.

Lemma for_exists_ab : forall u v m n : Z,
  v <= u -> u * u = m * m + n * n -> v * v = n * n - m * m -> 1 < u -> 1 < v ->
  Zodd v -> Zodd u -> rel_prime u v ->
  exists two : Z * Z,
    let (a, b) := two in
    (u - v = 4 * (a * a) /\ u + v = 2 * (b * b) \/
     u - v = 2 * (b * b) /\ u + v = 4 * (a * a)) /\ 0 < a /\ 0 < b.
Proof.
  intros u v m n Huv H H0 H1 H2 H3 H4 H5;
    elim (multiple4_2 u v H3 H4 Huv H5 H1 H2); intro; elim x; intros;
    elim_hyps; (cut (is_sqr (a * b)); 
      [ intro Hab; elim (prop4 a b (Zlt_le_weak 0 a H7) (Zlt_le_weak 0 b H8) H9
        Hab); intros; elim H11; intros Ha H11'; elim H11'; clear H11';
        intros a0 H11'; elim H11'; clear H11'; intros H11' Ha0; elim H12;
        intros Hb H12'; elim H12'; clear H12'; intros b0 H12'; elim H12';
        clear H12'; intros H12' Hb0; split with (a0,b0); intuition;
          [ rewrite <- H11' in H7; generalize (sqr_poss a0 H7); intro;
            auto with zarith
          | rewrite <- H12' in H8; generalize (sqr_poss b0 H8); intro;
            auto with zarith ]
      | apply (is_sqr_compat 2); try discriminate;
        replace (2 * 2 * (a * b)) with (m * m);
          [ apply is_sqr_sqr
          | apply (Zmult_eq_reg_l 2); try discriminate;
            replace (2 * (m * m)) with ((u * u) - (v * v)); 
              [ replace (u * u - v * v) with ((u - v) * (u + v)); 
                [ rewrite H6; rewrite H10; ring | ring ]
              | replace (2 * (m * m)) with ((m * m + n * n) - (n * n - m * m));
                [ rewrite H; rewrite H0; ring | ring ] ] ] ]).
Qed.

(***********************)
(* Diophantus' problem *)
(***********************)

Lemma for_mba_pytha1: forall m n u v a b : Z,
  u * u = m * m + n * n -> v * v = n * n - m * m -> u - v = 4 * (a * a) ->
  u + v = 2 * (b * b) -> b * b * (b * b) + 2 * (a * a) * (2 * (a * a)) = n * n.
Proof.
  intros; cut (2 * n * n = u * u + v * v).
  intro; cut (u = 2 * a * a + b * b).
  intro; cut (v = b * b - 2 * a * a).
  intro; rewrite H4 in H3; rewrite H5 in H3; symmetry;
    apply (Zmult_eq_reg_l 2).
  replace (2 * (n * n)) with (2 * n * n); [ rewrite H3; ring | ring ].
  discriminate.
  apply (Zmult_eq_reg_l 2).
  replace (2 * v) with (u + v - (u - v));
    [ rewrite H2; rewrite H1; ring | ring ].
  discriminate.
  apply (Zmult_eq_reg_l 2).
  replace (2 * u) with (u + v + (u - v));
    [ rewrite H2; rewrite H1; ring | ring ].
  discriminate.
  replace (2 * n * n) with (m * m + n * n + (n * n - m * m));
    [ rewrite H; rewrite H0; ring | ring ].
Qed.

Lemma for_mba_pytha2: forall m n u v a b : Z,
  u * u = m * m + n * n -> v * v = n * n - m * m -> u - v = 2 * (b * b) ->
  u + v = 4 * (a * a) -> b * b * (b * b) + 2 * (a * a) * (2 * (a * a)) = n * n.
Proof.
  intros; cut (2 * n * n = u * u + v * v).
  intro; cut (u = 2 * a * a + b * b).
  intro; cut (v = 2 * a * a - b * b).
  intro; rewrite H4 in H3; rewrite H5 in H3; symmetry;
    apply (Zmult_eq_reg_l 2).
  replace (2 * (n * n)) with (2 * n * n); [ rewrite H3; ring | ring ].
  discriminate.
  apply (Zmult_eq_reg_l 2).
  replace (2 * v) with (u + v - (u - v));
    [ rewrite H2; rewrite H1; ring | ring ].
  discriminate.
  apply (Zmult_eq_reg_l 2).
  replace (2 * u) with (u + v + (u - v));
    [ rewrite H2; rewrite H1; ring | ring ].
  discriminate.
  replace (2 * n * n) with (m * m + n * n + (n * n - m * m));
    [ rewrite H; rewrite H0; ring | ring ].
Qed.

Lemma diophantus20_equiv: forall y z : Z,
  y > 0 -> z > 0 -> y <= z -> rel_prime y z -> distinct_parity y z ->
  ~ is_sqr ((z * z + y * y) * (z * z - y * y)).
Proof.
  intros y z Hy Hz H' H0' H1' H2'; generalize (infinite_descent
    (fun p q : Z => 0 < p /\ 0 < q /\ p <= q /\ rel_prime p q /\
     distinct_parity p q /\ is_sqr (p * (q * (q * q - p * p))))).
  intro H3; cut (forall x1 x2 : Z, 0 <= x1 -> 0 <= x2 -> 0 < x1 /\ 0 < x2 /\
    x1 <= x2 /\ rel_prime x1 x2 /\ distinct_parity x1 x2 /\
    is_sqr (x1 * (x2 * (x2 * x2 - x1 * x1))) ->
    exists y1 : Z, exists y2 : Z, 0 <= y1 /\ 0 <= y2 /\ y1 + y2 < x1 + x2 /\
      0 < y1 /\ 0 < y2 /\ y1 <= y2 /\ rel_prime y1 y2 /\
      distinct_parity y1 y2 /\ is_sqr (y1 * (y2 * (y2 * y2 - y1 * y1)))).
  intro H4; apply (H3 H4) with (y * y) (z * z);
    try (apply Zge_le; apply sqr_pos).
  intuition; try (apply Zgt_lt; apply sqr_spos; auto with zarith).
  cut (y >= 0); auto with zarith.
  apply (prop2 y z H0').
  apply (distp_sqr1 _ _ H1').
  apply is_sqr_mult.
  apply is_sqr_sqr.
  apply is_sqr_mult.
  apply is_sqr_sqr.
  replace (z * z * (z * z) - y * y * (y * y)) with
    ((z * z + y * y) * (z * z - y * y)); [assumption | ring ].
  clear H3; intros p q Hp Hq H; elim H; clear H; intros H0p H; elim H; clear H;
    intros H0q H; elim H; clear H; intros H H0; elim H0; clear H0;
    intros H0 H1; elim H1; clear H1; intros H1 H2.
  elim (prop4b _ _ Hp Hq H H0 H2); intros H3 H4; elim H4; clear H4;
    intros H4 H5; elim H3; intros Hpp H3p; elim H3p; intros m H3'; elim H4;
    intros Hqq H4q; elim H4q; intros n H4'; elim H5; intros Hpq2 H5pq;
    elim H5pq; intros r H5'; elim H3'; clear H3'; intros H3' Hm; elim H4';
    clear H4'; intros H4' Hn; elim H5'; clear H5'; intros H5' Hr;
    generalize H5'; rewrite <- H3'; rewrite <- H4';
    replace (n * n * (n * n) - m * m * (m * m)) with
    ((m * m + n * n) * (n * n - m * m)).
  intro; elim (distp_odd _ _ H1); rewrite <- H3'; rewrite <- H4'; intros;
    symmetry in H3'; symmetry in H4'; cut (rel_prime (m * m) (n * n));
    try (rewrite <- H3'; rewrite <- H4'; assumption); intro;
    generalize (prop3 _ _ H8); clear H8; intro; generalize (prop1 _ _ H0 H1);
    rewrite H3'; rewrite H4'.
  intro; rewrite <- H5' in H5; rewrite H5'0 in H5; cut (0 <= m * m + n * n).
  cut (0 <= n * n - m * m).
  intros Hmn2 Hmn2';
    elim (prop4 (m * m + n * n) (n * n - m * m) Hmn2' Hmn2 H9 H5); intros;
    elim H10; intros Hmn21 Hmn22; clear Hmn21; elim Hmn22; intros u H12;
    elim H11; intros Hmn21' Hmn22'; clear Hmn21'; elim Hmn22'; intros v H13;
    elim H12; clear H12; intros H12 Hu; elim H13; clear H13; intros H13 Hv;
    generalize H6 H7 H9; rewrite <- H12; rewrite <- H13; intros H6' H7' H9';
    intros; generalize (Zodd_sqr2 _ H6'); generalize (Zodd_sqr2 _ H7'); intros;
    generalize (prop3 u v H9'); intro; cut (exists two : Z * Z,
      let (a, b) := two in
        (u - v = 4 * (a * a) /\ u + v = 2 * (b * b) \/
         u - v = 2 * (b * b) /\ u + v = 4 * (a * a))
          /\ 0 < a /\ 0 < b).
  intro; elim H17; clear H17; intro x; elim x; clear x; intros a b H17;
    elim H17; clear H17; intros; elim H18; clear H18; intros Ha Hb;
    cut (is_pytha (b * b) (2 * (a * a)) n); 
      [ intro H19; cut (Zodd (b * b));
        [ intro Hodd; generalize (pytha_thm3 _ _ _ H19 Hodd); clear Hodd H19;
          intro H19; elim H19; clear H19; unfold cond_pq, cond_pqb; intro p';
          intro H19; elim H19; clear H19; intro q'; intro H19; elim H19;
          clear H19; intro k'; intro H19; elim H19; clear H19; intro H21;
          intro H19; elim H19; clear H19; intro H22; intro H19; elim H19;
          clear H19; intro H23; intro H19; elim H19; clear H19; intro H20;
          intro H19; elim H19; clear H19; intro H19; intro H25; elim H19;
          clear H19; intro Hp'; intro H19; elim H19; clear H19; intro Hq';
          intro H19; elim H19; clear H19; intros Hpq' H24
        | elim H17; clear H17; intro H17; elim H17; clear H17; intros H17 H18;
          cut (u = b * b + 2 * (a * a)); auto with zarith; intro;
          rewrite H20 in H15; apply Zodd_sum3 with (b := a * a); assumption ]
      | unfold is_pytha, pos_triple; intuition; (apply Zle_ge; apply sqr_2) ||
        (apply (for_mba_pytha1 m n u v a b); assumption) ||
        (apply (for_mba_pytha2 m n u v a b); assumption) ].
  cut (k' = 1).
  intro Hk'; generalize H21 H22 H23; clear H21 H22 H23; rewrite Hk';
    ring_simplify q' p' (1 * (p' * p' + q' * q')) (1 * (p' * q'));
    intros; cut (0 <= p'); auto with zarith; cut (0 <= q'); auto with zarith;
    intros Hq'4 Hp'4; elim (prop4 p' q' Hp'4 Hq'4 H24).
  intros; generalize (prop1 _ _ H24 H25); intro;
    elim (prop4 (p' + q') (q' - p')); auto with zarith.
  intros; elim H18; rename H18 into H18'; intros Hpp' H18; clear Hpp';
    elim H18; clear H18; intros n' H18; elim H18; clear H18; intros H18 Hn';
    elim H19; rename H19 into H19'; intros Hpp' H19; elim H19; clear H19;
    intros m' H19; elim H19; clear H19; intros H19 Hm';
    cut (m' * m' + n' * n' < m * m + n * n).
  intro; split with (n' * n'); split with (m' * m');
    repeat (match goal with | |- _ /\ _ => split end); auto with zarith;
    try (rewrite H18; replace (2 * 1 * (p' * q')) with (2 * (p' * q')) in H22;
    try ring; cut (2 <> 0); try discriminate; intro h2;
    generalize (Zmult_eq_reg_l 2 (a * a) (p' * q') H22 h2); intro;
    apply (Zmult_lt_0_reg_r q'); auto with zarith; rewrite <- H30;
    apply Zmult_lt_O_compat; assumption); rewrite H18; rewrite H19;
    assumption || (repeat apply is_sqr_mult; try assumption;
    replace (q' * q' - p' * p') with ((p' + q') * (q' - p')); try ring;
    apply is_sqr_mult; assumption).
  rewrite H19; rewrite H18; rewrite H23.
    apply (Zlt_le_trans (q' + p') (q' ^2 + p' ^2)
      (m * m + (q' ^2 + p' ^2) * (q' ^2 + p' ^2))).
  generalize (Zlt_not_eq _ a Ha); intro Han0.
  generalize (Zgt_lt q' _ Hq'); intro Hq'g.
  generalize (Zlt_not_eq _ q' Hq'g); intro Hqn0.
  replace (q' + p') with (p' + q'); try ring;
    replace (q' ^2 + p' ^2) with (p' * p' + q' * q'); try ring.
  cut (p' <> 0); try (intro; cut (q' <> 0); progress auto with zarith).
  intro; rewrite H29 in H22; replace (2 * 1 * (0 * q')) with 0 in H22.
  apply Han0; symmetry; apply sqr_0; auto with zarith.
  ring.
  apply (Zle_trans (q' ^2 + p' ^2)
    ((q' ^2 + p' ^2) * (q' ^2 + p' ^2))
    (m * m + (q' ^2 + p' ^2) * (q' ^2 + p' ^2))); auto with zarith.
  apply sqr_le.
  replace ((p' + q') * (q' - p')) with (q' * q' - p' * p'); try ring;
    generalize H21; replace (1 * (q' * q' - p' * p')) with (q' * q' - p' * p');
    try ring; clear H21; intro H21; rewrite <- H21; generalize sqr_pos; intro.
  apply is_sqr_sqr.
  split.
  apply Zmult_le_0_compat; assumption.
  split with a; split; auto with zarith.
  apply (relp_mult1 (b * b) (2 * (a * a)) (q' * q' - p' * p')
    (2 * (p' * q')) k'); auto with zarith.
  generalize (distp_neq _ _ H25); intro Hneq; generalize (Zge_le _ _ Hp');
    clear Hp'; intro Hp'; cut (p' < q'); auto with zarith.
  rewrite H22; ring.
  apply (relp_sum (b * b) (2 * (a * a))).
  elim H17; clear H17; intro H17; elim H17; clear H17; intros H18 H19.
  cut (v = b * b - 2 * (a * a)).
  intro; cut (u = b * b + 2 * (a * a)).
  intro; rewrite <- H17; rewrite <- H26; auto.
  apply (Zmult_eq_reg_l 2 u (b * b + 2 * (a * a))).
  replace (2 * u) with ((u + v) + (u - v));
    [ rewrite H18; rewrite H19; ring | ring ].
  discriminate.
  apply (Zmult_eq_reg_l 2 v (b * b - 2 * (a * a))).
  replace (2 * v) with ((u + v) - (u - v));
    [ rewrite H18; rewrite H19; ring | ring ].
  discriminate.
  cut ((-v) = b * b - 2 * (a * a)).
  intro; cut (u = b * b + 2 * (a * a)).
  intro; rewrite <- H17; rewrite <- H26.
  apply rel_prime_oppr; auto.
  apply (Zmult_eq_reg_l 2 u (b * b + 2 * (a * a))).
  replace (2 * u) with ((u + v) + (u - v));
    [ rewrite H18; rewrite H19; ring | ring ].
  discriminate.
  apply (Zmult_eq_reg_l 2 (-v) (b * b - 2 * (a * a))).
  replace (2 * (-v)) with ((u - v) - (u + v));
    [ rewrite H18; rewrite H19; ring | ring ].
  discriminate.
  apply (for_exists_ab u v m n); try assumption; rewrite H3' in H0p;
    rewrite H4' in H0q; generalize (sqr_poss n H0q);
    generalize (sqr_poss m H0p); intros Hneqn Hneqm;
    elim (neq_1 u v m n Hneqn Hneqm H12 H13); intros Hu1 Hv1;
    generalize (Zodd_0 _ H15); intro; generalize (Zodd_0 _ H14); intro;
    cut (1 < u); auto with zarith; intro; cut (1 < v); auto with zarith; intro;
    auto with zarith; intros; apply Zle_square_simpl; auto with zarith.
  auto with zarith.
  auto with zarith.
  ring.
Qed.

Lemma diophantus20_refined : forall p q : Z,
  p > 0 -> q > 0 -> p <= q -> rel_prime p q -> distinct_parity p q ->
  ~ is_sqr (p * (q * (q * q - p * p))).
Proof.
  intros p0 q0 Hp0 Hq0 H' H0' H1' H2'.
  cut (0 <= p0).
  intro; cut (0 <= q0).
  intro; elim (prop4b _ _ H H0 H' H0' H2').
  intros; elim H2; clear H2; intros; unfold is_sqr in H3; elim H3; clear H3;
    intros; do 2 (elim H4; clear H4; intros); unfold is_sqr in H1;
    unfold is_sqr in H2; elim H1; clear H1; intros; elim H2; clear H2; intros;
    elim H6; clear H6; intros; elim H7; clear H7; intros; elim H6; clear H6;
    intros; elim H7; clear H7; intros; apply (diophantus20_equiv x0 x1).
  cut (p0 <> 0); auto with zarith; intro; rewrite <- H6 in H10;
    elim (Zmult_neq_0 _ _ H10); auto with zarith.
  cut (q0 <> 0); auto with zarith; intro; rewrite <- H7 in H10;
    elim (Zmult_neq_0 _ _ H10); auto with zarith.
  rewrite <- H6 in H'; rewrite <- H7 in H'; apply Zle_square_simpl; auto.
  apply prop3; rewrite H6; rewrite H7; assumption.
  apply distp_sqr2; rewrite H6; rewrite H7; assumption.
  unfold is_sqr; split.
  rewrite H6; rewrite H7;
    replace ((q0 + p0) * (q0 - p0)) with (q0 * q0 - p0 * p0).
  assumption.
  ring.
  split with x; rewrite H6; rewrite H7; split.
  rewrite H4; ring.
  assumption.
  auto with zarith.
  auto with zarith.
Qed.

Lemma diophantus20 :
  ~ (exists x : Z, exists y : Z, exists z : Z, exists t : Z,
       0 < x /\ 0 < y /\ 0 < z /\ 0 < t /\ x * x + y * y = z * z /\
       x * y = 2 * (t * t)).
Proof.
  intro; elim_hyps; cut (is_pytha x x0 x1); try (unfold is_pytha, pos_triple;
    solve [ intuition ]).
  intro; elim (pytha_thm1 _ _ _ H5); clear H5; unfold cond_pq, cond_pqb;
    intros; elim_hyps;
    (cut (x3 > 0); 
     [ intro; apply (diophantus20_refined x3 x4); try assumption;    
       generalize (Zge_le _ _ H8); intro; (cut (x5 > 0);
       [ intro; apply (is_sqr_compat x5); auto with zarith;
         repeat progress (apply Zmult_le_0_compat; auto with zarith); split;
           [ repeat progress (apply Zmult_le_0_compat; auto with zarith)
           | exists x2; intuition; rewrite H5 in H4; rewrite H13 in H4;
             match goal with
             | id : ?x = 2 * _ |- _ => replace x with
               (2 * (x5 * x5 * (x3 * (x4 * (x4 * x4 - x3 * x3))))) in id
             end; [ auto with zarith | ring ] ]
       | apply Zlt_gt; apply (Zmult_lt_0_reg_r (x3 * x3 + x4 * x4));
         try (apply Zgt_lt; progress auto with zarith); rewrite <- H6; auto ]) 
     | match goal with
       | id : ?x = 2 * _ * (_ * _) |- _ =>
         cut (x <> 0); auto with zarith; intro;
         match goal with
         | id' : _ |- _ => rewrite id in id'
         end
       end;
       repeat
         match goal with
         | id : _ |- _ => elim (Zmult_neq_0 _ _ id); auto with zarith; intros
         end ]).
Qed.
