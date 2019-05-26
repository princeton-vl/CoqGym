(****************************************************************************
                                                                             
          IEEE754  :  Digit                                                  
                                                                             
          Laurent Thery                                                      
                                                                             
  *****************************************************************************
  Gives the number of digits necessary to write a number in a given base *)
Require Export ZArithRing.
Require Export Omega.
Require Export Faux.
Section Pdigit.
(* n is the base *)
Variable n : Z.
(* and it is greater or equal to 2 *)
Hypothesis nMoreThan1 : (1 < n)%Z.
 
Let nMoreThanOne := Zlt_1_O _ (Zlt_le_weak _ _ nMoreThan1).
Hint Resolve nMoreThanOne: zarith.
 
Theorem Zpower_nat_less : forall q : nat, (0 < Zpower_nat n q)%Z.
intros q; elim q; simpl in |- *;
auto with zarith.
Qed.
Hint Resolve Zpower_nat_less: zarith.
 
Theorem Zpower_nat_monotone_S :
 forall p : nat, (Zpower_nat n p < Zpower_nat n (S p))%Z.
intros p; rewrite <- (Zmult_1_l (Zpower_nat n p)); replace (S p) with (1 + p);
 [ rewrite Zpower_nat_is_exp | auto with zarith ].
rewrite Zpower_nat_1; auto with zarith.
apply Zmult_gt_0_lt_compat_r; auto with zarith.
apply Zlt_gt; auto with zarith.
Qed.
 
Theorem Zpower_nat_monotone_lt :
 forall p q : nat, p < q -> (Zpower_nat n p < Zpower_nat n q)%Z.
intros p q H'; elim H'; simpl in |- *; auto.
apply Zpower_nat_monotone_S.
intros m H H0; apply Zlt_trans with (1 := H0).
apply Zpower_nat_monotone_S.
Qed.
Hint Resolve Zpower_nat_monotone_lt: zarith.
 
Theorem Zpower_nat_anti_monotone_lt :
 forall p q : nat, (Zpower_nat n p < Zpower_nat n q)%Z -> p < q.
intros p q H'.
case (le_or_lt q p); auto; (intros H'1; generalize H'; case H'1).
intros H'0; Contradict H'0; auto with zarith.
intros m H'0 H'2; Contradict H'2; auto with zarith.
Qed.
 
Theorem Zpower_nat_monotone_le :
 forall p q : nat, p <= q -> (Zpower_nat n p <= Zpower_nat n q)%Z.
intros p q H'; case (le_lt_or_eq _ _ H'); auto with zarith.
intros H1; rewrite H1; auto with zarith.
Qed.
 
Theorem Zpower_nat_anti_monotone_le :
 forall p q : nat, (Zpower_nat n p <= Zpower_nat n q)%Z -> p <= q.
intros p q H'; case (le_or_lt p q); intros H'0; auto with arith.
Contradict H'; auto with zarith.
Qed.
 
Theorem Zpower_nat_anti_eq :
 forall p q : nat, Zpower_nat n p = Zpower_nat n q -> p = q.
intros p q H'; apply le_antisym; apply Zpower_nat_anti_monotone_le;
 rewrite H'; auto with zarith.
Qed.
(* To compute the number of digits structurally, we suppose that
   we know already an upper bound q. So we start from q down
   to 0 to find the bigger exponent r such that n^(r-1) < v *)
 
Fixpoint digitAux (v r : Z) (q : positive) {struct q} : nat :=
  match q with
  | xH => 0
  | xI q' =>
      match (n * r)%Z with
      | r' =>
          match (r ?= v)%Z with
          | Datatypes.Gt => 0
          | _ => S (digitAux v r' q')
          end
      end
  | xO q' =>
      match (n * r)%Z with
      | r' =>
          match (r ?= v)%Z with
          | Datatypes.Gt => 0
          | _ => S (digitAux v r' q')
          end
      end
  end.
(* As we know that log_n q < log_2 q we can define our function digit*)
 
Definition digit (q : Z) :=
  match q with
  | Z0 => 0
  | Zpos q' => digitAux (Zabs q) 1 (xO q')
  | Zneg q' => digitAux (Zabs q) 1 (xO q')
  end.
Hint Unfold digit.
 
Theorem digitAux1 :
 forall p r, (Zpower_nat n (S p) * r)%Z = (Zpower_nat n p * (n * r))%Z.
intros p r; replace (S p) with (1 + p);
 [ rewrite Zpower_nat_is_exp | auto with arith ].
rewrite Zpower_nat_1; ring.
Qed.
 
Theorem Zcompare_correct :
 forall p q : Z,
 match (p ?= q)%Z with
 | Datatypes.Gt => (q < p)%Z
 | Datatypes.Lt => (p < q)%Z
 | Datatypes.Eq => p = q
 end.
intros p q; unfold Zlt in |- *; generalize (Zcompare_EGAL p q);
 (CaseEq (p ?= q)%Z; simpl in |- *; auto).
intros H H0; case (Zcompare_Gt_Lt_antisym p q); auto.
Qed.
 
Theorem digitAuxLess :
 forall (v r : Z) (q : positive),
 match digitAux v r q with
 | S r' => (Zpower_nat n r' * r <= v)%Z
 | O => True
 end.
intros v r q; generalize r; elim q; clear r q; simpl in |- *; auto.
intros q' Rec r; generalize (Zcompare_correct r v); case (r ?= v)%Z; auto.
intros H1; generalize (Rec (n * r)%Z); case (digitAux v (n * r) q').
intros; rewrite H1; rewrite Zpower_nat_O; auto with zarith.
intros r'; rewrite digitAux1; auto.
intros H1; generalize (Rec (n * r)%Z); case (digitAux v (n * r) q').
intros; rewrite Zpower_nat_O; auto with zarith.
apply Zle_trans with (m := r); auto with zarith.
intros r'; rewrite digitAux1; auto.
intros q' Rec r; generalize (Zcompare_correct r v); case (r ?= v)%Z; auto.
intros H1; generalize (Rec (n * r)%Z); case (digitAux v (n * r) q').
intros; rewrite H1; rewrite Zpower_nat_O; auto with zarith.
intros r'; rewrite digitAux1; auto.
intros H1; generalize (Rec (n * r)%Z); case (digitAux v (n * r) q').
intros; rewrite Zpower_nat_O; auto with zarith.
apply Zle_trans with (m := r); auto with zarith.
intros r'; rewrite digitAux1; auto.
Qed.
(* digit is correct (first part) *)
 
Theorem digitLess :
 forall q : Z, q <> 0%Z -> (Zpower_nat n (pred (digit q)) <= Zabs q)%Z.
intros q; case q.
intros H; Contradict H; auto with zarith.
intros p H; unfold digit in |- *;
 generalize (digitAuxLess (Zabs (Zpos p)) 1 (xO p));
 case (digitAux (Zabs (Zpos p)) 1 (xO p)); simpl in |- *; 
 auto with zarith.
intros p H; unfold digit in |- *;
 generalize (digitAuxLess (Zabs (Zneg p)) 1 (xO p));
 case (digitAux (Zabs (Zneg p)) 1 (xO p)); simpl in |- *; 
 auto with zarith.
Qed.
Hint Resolve digitLess: zarith.
Hint Resolve Zmult_gt_0_lt_compat_r Zmult_gt_0_lt_compat_l: zarith.
 
Fixpoint pos_length (p : positive) : nat :=
  match p with
  | xH => 0
  | xO p' => S (pos_length p')
  | xI p' => S (pos_length p')
  end.
 
Theorem digitAuxMore :
 forall (v r : Z) (q : positive),
 (0 < r)%Z ->
 (v < Zpower_nat n (pos_length q) * r)%Z ->
 (v < Zpower_nat n (digitAux v r q) * r)%Z.
intros v r q; generalize r; elim q; clear r q; simpl in |- *.
intros p Rec r Hr; generalize (Zcompare_correct r v); case (r ?= v)%Z; auto.
intros H1 H2; rewrite <- H1.
apply Zle_lt_trans with (Zpower_nat n 0 * r)%Z; auto with zarith arith.
rewrite Zpower_nat_O; rewrite Zmult_1_l; auto with zarith.
intros H1 H2; rewrite digitAux1.
apply Rec.
apply Zlt_mult_ZERO; auto with zarith.
rewrite <- digitAux1; auto.
rewrite Zpower_nat_O; rewrite Zmult_1_l; auto with zarith.
intros p Rec r Hr; generalize (Zcompare_correct r v); case (r ?= v)%Z; auto.
intros H1 H2; rewrite <- H1.
apply Zle_lt_trans with (Zpower_nat n 0 * r)%Z; auto with zarith arith.
rewrite Zpower_nat_O; rewrite Zmult_1_l; auto with zarith.
intros H1 H2; rewrite digitAux1.
apply Rec.
apply Zlt_mult_ZERO; auto with zarith.
rewrite <- digitAux1; auto.
rewrite Zpower_nat_O; rewrite Zmult_1_l; auto with zarith.
auto.
Qed.
 
Theorem pos_length_pow :
 forall p : positive, (Zpos p < Zpower_nat n (S (pos_length p)))%Z.
intros p; elim p; simpl in |- *; auto.
intros p0 H; rewrite Zpos_xI.
apply Zlt_le_trans with (2 * (n * Zpower_nat n (pos_length p0)))%Z;
auto with zarith.
intros p0 H; rewrite Zpos_xO.
apply Zlt_le_trans with (2 * (n * Zpower_nat n (pos_length p0)))%Z;
auto with zarith.
auto with zarith.
Qed.
(* digit is correct (second part) *)
 
Theorem digitMore : forall q : Z, (Zabs q < Zpower_nat n (digit q))%Z.
intros q; case q.
easy.
intros q'; rewrite <- (Zmult_1_r (Zpower_nat n (digit (Zpos q')))).
unfold digit in |- *; apply digitAuxMore; auto with zarith.
rewrite Zmult_1_r.
simpl in |- *; apply pos_length_pow.
intros q'; rewrite <- (Zmult_1_r (Zpower_nat n (digit (Zneg q')))).
unfold digit in |- *; apply digitAuxMore; auto with zarith.
rewrite Zmult_1_r.
simpl in |- *; apply pos_length_pow.
Qed.
Hint Resolve digitMore: zarith.
(* if we find an r such that n^(r-1) =< q < n^r 
   then r is the number of digits *)
 
Theorem digitInv :
 forall (q : Z) (r : nat),
 (Zpower_nat n (pred r) <= Zabs q)%Z ->
 (Zabs q < Zpower_nat n r)%Z -> digit q = r.
intros q r H' H'0; case (le_or_lt (digit q) r).
intros H'1; case (le_lt_or_eq _ _ H'1); auto; intros H'2.
absurd (Zabs q < Zpower_nat n (digit q))%Z; auto with zarith.
apply Zle_not_lt; auto with zarith.
apply Zle_trans with (m := Zpower_nat n (pred r)); auto with zarith.
apply Zpower_nat_monotone_le.
generalize H'2; case r; auto with arith.
intros H'1.
absurd (Zpower_nat n (pred (digit q)) <= Zabs q)%Z; auto with zarith.
apply Zlt_not_le; auto with zarith.
apply Zlt_le_trans with (m := Zpower_nat n r); auto.
apply Zpower_nat_monotone_le.
generalize H'1; case (digit q); auto with arith.
apply digitLess; auto with zarith.
generalize H'1; case q; unfold digit in |- *; intros tmp; intros; red in |- *;
 intros; try discriminate; Contradict tmp; auto with arith.
Qed.
 
Theorem digitO : digit 0 = 0.
unfold digit in |- *; simpl in |- *; auto with arith.
Qed.
 
Theorem digit1 : digit 1 = 1.
unfold digit in |- *; simpl in |- *; auto.
Qed.
(* digit is monotone *)
 
Theorem digit_monotone :
 forall p q : Z, (Zabs p <= Zabs q)%Z -> digit p <= digit q.
intros p q H; case (le_or_lt (digit p) (digit q)); auto; intros H1;
 Contradict H.
apply Zlt_not_le.
cut (p <> 0%Z); [ intros H2 | idtac ].
apply Zlt_le_trans with (2 := digitLess p H2).
cut (digit q <= pred (digit p)); [ intros H3 | idtac ].
apply Zlt_le_trans with (2 := Zpower_nat_monotone_le _ _ H3);
 auto with zarith.
generalize H1; case (digit p); simpl in |- *; auto with arith.
generalize H1; case p; simpl in |- *; intros tmp; intros; red in |- *; intros;
 try discriminate; Contradict tmp; auto with arith.
Qed.
Hint Resolve digit_monotone: arith.
(* if the number is not null so is the number of digits *)
 
Theorem digitNotZero : forall q : Z, q <> 0%Z -> 0 < digit q.
intros q H'.
apply lt_le_trans with (m := digit 1); auto with zarith.
apply digit_monotone.
generalize H'; case q; simpl in |- *; auto with zarith; intros q'; case q';
 simpl in |- *; auto with zarith arith; intros; red in |- *; 
 simpl in |- *; red in |- *; intros; discriminate.
Qed.
Hint Resolve Zlt_gt: zarith.
 
Theorem digitAdd :
 forall (q : Z) (r : nat),
 q <> 0%Z -> digit (q * Zpower_nat n r) = digit q + r.
intros q r H0.
apply digitInv.
replace (pred (digit q + r)) with (pred (digit q) + r).
rewrite Zpower_nat_is_exp; rewrite Zabs_Zmult;
 rewrite (fun x => Zabs_eq (Zpower_nat n x)); auto with zarith arith.
generalize (digitNotZero _ H0); case (digit q); auto with arith.
intros H'; Contradict H'; auto with arith.
rewrite Zpower_nat_is_exp; rewrite Zabs_Zmult;
 rewrite (fun x => Zabs_eq (Zpower_nat n x)); auto with zarith arith.
Qed.
 
Theorem digit_minus1 : forall p : nat, digit (Zpower_nat n p - 1) = p.
intros p; case p; auto.
intros n0; apply digitInv; auto.
rewrite Zabs_eq.
cut (Zpower_nat n (pred (S n0)) < Zpower_nat n (S n0))%Z; auto with zarith.
cut (0 < Zpower_nat n (S n0))%Z; auto with zarith.
rewrite Zabs_eq; auto with zarith.
Qed.
 
Theorem digit_bound :
 forall (x y z : Z) (n : nat),
 (Zabs x <= Zabs y)%Z ->
 (Zabs y <= Zabs z)%Z -> digit x = n -> digit z = n -> digit y = n.
intros x y z n0 H' H'0 H'1 H'2; apply le_antisym.
rewrite <- H'2; auto with arith.
rewrite <- H'1; auto with arith.
Qed.
 
Theorem digit_abs : forall p : Z, digit (Zabs p) = digit p.
intros p; case p; simpl in |- *; auto.
Qed.
(* Strict comparison on the number of digits gives comparison on the numbers *)
 
Theorem digit_anti_monotone_lt :
 (1 < n)%Z -> forall p q : Z, digit p < digit q -> (Zabs p < Zabs q)%Z.
intros H' p q H'0.
case (Zle_or_lt (Zabs q) (Zabs p)); auto; intros H'1.
Contradict H'0.
case (Zle_lt_or_eq _ _ H'1); intros H'2.
apply le_not_lt; auto with arith.
rewrite <- (digit_abs p); rewrite <- (digit_abs q); rewrite H'2;
 auto with arith.
Qed.
End Pdigit.
Hint Resolve Zpower_nat_less: zarith.
Hint Resolve Zpower_nat_monotone_lt: zarith.
Hint Resolve Zpower_nat_monotone_le: zarith.
Hint Unfold digit.
Hint Resolve digitLess: zarith.
Hint Resolve digitMore: zarith.
Hint Resolve digit_monotone: arith.