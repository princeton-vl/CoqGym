(****************************************************************************
                                                                             
          IEEE754  :  Faux                                                   
                                                                             
          Laurent Thery                                                      
                                                                             
  *****************************************************************************
  Auxillary properties about natural numbers, relative numbers and reals *)
Require Export Min.
Require Export Arith.
Require Export Reals.
Require Export Zpower.
Require Export ZArith.
Require Export Zcomplements.
Require Export sTactic.
Hint Resolve R1_neq_R0: real.
(*Missing rule for nat *)
 
Theorem minus_minus : forall a b : nat, a <= b -> b - (b - a) = a.
intros a b H'.
apply sym_equal.
apply plus_minus; auto.
rewrite plus_comm; apply le_plus_minus; auto.
Qed.
 
Theorem lte_comp_mult :
 forall p q r t : nat, p <= q -> r <= t -> p * r <= q * t.
intros p q r t H'; elim H'; simpl in |- *; auto with arith.
elim p; simpl in |- *; auto with arith.
intros n H m H0 H1 H2; apply plus_le_compat; auto with arith.
apply le_trans with (m := r + n * r); auto with arith.
Qed.
Hint Resolve lte_comp_mult: arith.
 
Theorem le_refl_eq : forall n m : nat, n = m -> n <= m.
intros n m H'; rewrite H'; auto.
Qed.
 
Theorem lt_le_pred : forall n m : nat, n < m -> n <= pred m.
intros n m H'; inversion H'; simpl in |- *; auto.
apply le_trans with (S n); auto.
Qed.
 
Theorem lt_comp_mult_l : forall p q r : nat, 0 < p -> q < r -> p * q < p * r.
intros p; elim p; simpl in |- *.
auto with arith.
intros n0; case n0.
simpl in |- *; auto with arith.
intros n1 H' q r H'0 H'1.
apply lt_trans with (m := q + S n1 * r); auto with arith.
Qed.
Hint Resolve lt_comp_mult_l: arith.
 
Theorem lt_comp_mult_r : forall p q r : nat, 0 < p -> q < r -> q * p < r * p.
intros; repeat rewrite (fun x : nat => mult_comm x p); auto with arith.
Qed.
Hint Resolve lt_comp_mult_r: arith.
 
Theorem lt_comp_mult : forall p q r s : nat, p < q -> r < s -> p * r < q * s.
intros p q r s; case q.
intros H'; inversion H'.
intros q'; case p.
intros H' H'0; simpl in |- *; apply le_lt_trans with (m := r);
 auto with arith.
intros p' H' H'0; apply le_lt_trans with (m := S q' * r); auto with arith.
Qed.
Hint Resolve lt_comp_mult: arith.
 
Theorem mult_eq_inv : forall n m p : nat, 0 < n -> n * m = n * p -> m = p.
intros n m p H' H'0.
apply le_antisym; auto.
case (le_or_lt m p); intros H'1; auto with arith.
absurd (n * p < n * m); auto with arith.
rewrite H'0; auto with arith.
case (le_or_lt p m); intros H'1; auto with arith.
absurd (n * m < n * p); auto with arith.
rewrite H'0; auto with arith.
Qed.
 
Definition natEq : forall n m : nat, {n = m} + {n <> m}.
intros n; elim n.
intros m; case m; auto with arith.
intros n0 H' m; case m; auto with arith.
Defined.
 
Theorem notEqLt : forall n : nat, 0 < n -> n <> 0.
intros n H'; Contradict H'; auto.
rewrite H'; auto with arith.
Qed.
Hint Resolve notEqLt: arith.
 
Theorem lt_next : forall n m : nat, n < m -> m = S n \/ S n < m.
intros n m H'; elim H'; auto with arith.
Qed.
 
Theorem le_next : forall n m : nat, n <= m -> m = n \/ S n <= m.
intros n m H'; case (le_lt_or_eq _ _ H'); auto with arith.
Qed.
 
Theorem min_or :
 forall n m : nat, min n m = n /\ n <= m \/ min n m = m /\ m < n.
intros n; elim n; simpl in |- *; auto with arith.
intros n' Rec m; case m; simpl in |- *; auto with arith.
intros m'; elim (Rec m'); intros H'0; case H'0; clear H'0; intros H'0 H'1;
 rewrite H'0; auto with arith.
Qed.
 
Theorem minus_inv_lt_aux : forall n m : nat, n - m = 0 -> n - S m = 0.
intros n; elim n; simpl in |- *; auto with arith.
intros n0 H' m; case m; auto with arith.
intros H'0; discriminate.
Qed.
 
Theorem minus_inv_lt : forall n m : nat, m <= n -> m - n = 0.
intros n m H'; elim H'; simpl in |- *; auto with arith.
intros m0 H'0 H'1; apply minus_inv_lt_aux; auto.
Qed.
 
Theorem minus_le : forall m n p q : nat, m <= n -> p <= q -> m - q <= n - p.
intros m n p q H' H'0.
case (le_or_lt m q); intros H'1.
rewrite minus_inv_lt with (1 := H'1); auto with arith.
apply (fun p n m : nat => plus_le_reg_l n m p) with (p := q).
rewrite le_plus_minus_r; auto with arith.
rewrite (le_plus_minus p q); auto.
rewrite (plus_comm p).
rewrite plus_assoc_reverse.
rewrite le_plus_minus_r; auto with arith.
apply le_trans with (1 := H'); auto with arith.
apply le_trans with (1 := H'0); auto with arith.
apply le_trans with (2 := H'); auto with arith.
Qed.
 
Theorem lt_minus_inv : forall n m p : nat, n <= p -> m < n -> p - n < p - m.
intros n m p H'; generalize m; clear m; elim H'.
intros m H'0; rewrite <- minus_n_n; elim H'0.
rewrite <- minus_Sn_m; auto with arith.
intros m0 H'1 H'2; rewrite <- minus_Sn_m; auto with arith.
intros m H'0 H'1 m0 H'2; repeat rewrite <- minus_Sn_m; auto with arith.
apply le_trans with n; auto with arith.
Qed.
 
Theorem lt_mult_anti_compatibility :
 forall n n1 n2 : nat, 0 < n -> n * n1 < n * n2 -> n1 < n2.
intros n n1 n2 H' H'0; case (le_or_lt n2 n1); auto.
intros H'1; Contradict H'0; auto.
apply le_not_lt; auto with arith.
Qed.
 
Theorem le_mult_anti_compatibility :
 forall n n1 n2 : nat, 0 < n -> n * n1 <= n * n2 -> n1 <= n2.
intros n n1 n2 H' H'0; case (le_or_lt n1 n2); auto.
intros H'1; Contradict H'0; auto.
apply lt_not_le; auto with arith.
Qed.
 
Theorem min_n_0 : forall n : nat, min n 0 = 0.
intros n; case n; simpl in |- *; auto.
Qed.
(*Simplification rules missing in R *)
Hint Resolve Rabs_pos: real.
 
Theorem Rlt_Rminus_ZERO : forall r1 r2 : R, (r2 < r1)%R -> (0 < r1 - r2)%R.
intros r1 r2 H; replace 0%R with (r1 - r1)%R; unfold Rminus in |- *;
 auto with real.
Qed.
Hint Resolve Rlt_Rminus_ZERO: real.
 
Theorem Rabsolu_left1 : forall a : R, (a <= 0)%R -> Rabs a = (- a)%R.
intros a H; case H; intros H1.
apply Rabs_left; auto.
rewrite H1; simpl in |- *; rewrite Rabs_right; auto with real.
Qed.
 
Theorem RmaxLess1 : forall r1 r2 : R, (r1 <= Rmax r1 r2)%R.
intros r1 r2; unfold Rmax in |- *; case (Rle_dec r1 r2); auto with real.
Qed.
 
Theorem RmaxLess2 : forall r1 r2 : R, (r2 <= Rmax r1 r2)%R.
intros r1 r2; unfold Rmax in |- *; case (Rle_dec r1 r2); auto with real;
 intros; apply Ropp_le_cancel; auto with real.
Qed.
 
Theorem RmaxSym : forall p q : R, Rmax p q = Rmax q p.
intros p q; unfold Rmax in |- *.
case (Rle_dec p q); case (Rle_dec q p); auto; intros H1 H2; apply Rle_antisym;
 auto.
case (Rle_or_lt p q); auto; intros H'0; Contradict H1; apply Rlt_le; auto.
case (Rle_or_lt q p); auto; intros H'0; Contradict H2; apply Rlt_le; auto.
Qed.
 
Theorem RmaxAbs :
 forall p q r : R,
 (p <= q)%R -> (q <= r)%R -> (Rabs q <= Rmax (Rabs p) (Rabs r))%R.
intros p q r H' H'0; case (Rle_or_lt 0 p); intros H'1.
repeat rewrite Rabs_right; auto with real.
apply Rle_trans with r; auto with real.
apply RmaxLess2; auto.
apply Rge_trans with p; auto with real; apply Rge_trans with q;
 auto with real.
apply Rge_trans with p; auto with real.
rewrite (Rabs_left p); auto.
case (Rle_or_lt 0 q); intros H'2.
repeat rewrite Rabs_right; auto with real.
apply Rle_trans with r; auto.
apply RmaxLess2; auto.
apply Rge_trans with q; auto with real.
rewrite (Rabs_left q); auto.
case (Rle_or_lt 0 r); intros H'3.
repeat rewrite Rabs_right; auto with real.
apply Rle_trans with (- p)%R; auto with real.
apply RmaxLess1; auto.
rewrite (Rabs_left r); auto.
apply Rle_trans with (- p)%R; auto with real.
apply RmaxLess1; auto.
Qed.
 
Theorem Rabsolu_Zabs : forall z : Z, Rabs (IZR z) = IZR (Zabs z).
intros z; case z; simpl in |- *; auto with real.
apply Rabs_right; auto with real.
intros p0; apply Rabs_right; auto with real zarith.
intros p0; unfold IZR; rewrite <- INR_IPR; rewrite Rabs_Ropp.
apply Rabs_right; auto with real zarith.
Qed.
 
Theorem RmaxRmult :
 forall p q r : R, (0 <= r)%R -> Rmax (r * p) (r * q) = (r * Rmax p q)%R.
intros p q r H; unfold Rmax in |- *.
case (Rle_dec p q); case (Rle_dec (r * p) (r * q)); auto; intros H1 H2; auto.
case H; intros E1.
case H1; auto with real.
rewrite <- E1; repeat rewrite Rmult_0_l; auto.
case H; intros E1.
case H2; auto with real.
apply Rmult_le_reg_l with (r := r); auto.
rewrite <- E1; repeat rewrite Rmult_0_l; auto.
Qed.
 
Theorem Rle_R0_Ropp : forall p : R, (p <= 0)%R -> (0 <= - p)%R.
intros p H; rewrite <- Ropp_0; auto with real.
Qed.
 
Theorem Rlt_R0_Ropp : forall p : R, (p < 0)%R -> (0 < - p)%R.
intros p H; rewrite <- Ropp_0; auto with real.
Qed.
Hint Resolve Rle_R0_Ropp Rlt_R0_Ropp: real.
(* Properties of Z *)
 
Theorem convert_not_O : forall p : positive, nat_of_P p <> 0.
intros p; elim p.
intros p0 H'; unfold nat_of_P in |- *; simpl in |- *; rewrite ZL6.
generalize H'; case (nat_of_P p0); auto.
intros p0 H'; unfold nat_of_P in |- *; simpl in |- *; rewrite ZL6.
generalize H'; case (nat_of_P p0); simpl in |- *; auto.
unfold nat_of_P in |- *; simpl in |- *; auto with arith.
Qed.
Hint Resolve convert_not_O: zarith arith.
Hint Resolve Zlt_le_weak Zle_not_gt Zgt_irrefl Zlt_irrefl Zle_not_lt
  Zlt_not_le Zlt_asym inj_lt inj_le: zarith.
 
Theorem inj_abs :
 forall x : Z, (0 <= x)%Z -> Z_of_nat (Zabs_nat x) = x.
intros x; elim x; auto.
unfold Zabs_nat in |- *.
intros p.
pattern p at 1 3 in |- *;
 rewrite <- (pred_o_P_of_succ_nat_o_nat_of_P_eq_id p).
generalize (convert_not_O p); case (nat_of_P p); simpl in |- *;
 auto with arith.
intros H'; case H'; auto.
intros n H' H'0; rewrite Ppred_succ; auto.
intros p H'; Contradict H'; auto.
Qed.
 
Theorem inject_nat_convert :
 forall (p : Z) (q : positive),
 p = Zpos q -> Z_of_nat (nat_of_P q) = p.
intros p q H'; rewrite H'.
CaseEq (nat_of_P q); simpl in |- *.
elim q; unfold nat_of_P in |- *; simpl in |- *; intros;
 try discriminate.
absurd (0%Z = Zpos p0); auto.
red in |- *; intros H'0; try discriminate.
apply H; auto.
change (nat_of_P p0 = 0) in |- *.
generalize H0; rewrite ZL6; case (nat_of_P p0); simpl in |- *;
 auto; intros; try discriminate.
intros n; rewrite <- nat_of_P_o_P_of_succ_nat_eq_succ.
intros H'0; apply f_equal with (f := Zpos).
apply nat_of_P_inj; auto.
Qed.
Hint Resolve inj_le inj_lt: zarith.
 
Theorem ZleLe : forall x y : nat, (Z_of_nat x <= Z_of_nat y)%Z -> x <= y.
intros x y H'.
case (le_or_lt x y); auto with arith.
intros H'0; Contradict H'; auto with zarith.
Qed.
 
Theorem inject_nat_eq : forall x y : nat, Z_of_nat x = Z_of_nat y -> x = y.
intros x y H'; apply le_antisym.
apply ZleLe; auto.
idtac; rewrite H'; auto with zarith.
apply ZleLe; auto.
idtac; rewrite H'; auto with zarith.
Qed.
 
Theorem Zcompare_EGAL :
 forall p q : Z, (p ?= q)%Z = Datatypes.Eq -> p = q.
intros p q; case p; case q; simpl in |- *; auto with arith;
 try (intros; discriminate); intros q1 p1.
intros H1; rewrite (Pcompare_Eq_eq p1 q1); auto.
unfold Pos.compare.
generalize (Pcompare_Eq_eq p1 q1);
 case (Pcompare p1 q1 Datatypes.Eq); simpl in |- *; 
 intros H H1; try discriminate; rewrite H; auto.
Qed.
 
Theorem Zlt_Zopp : forall x y : Z, (x < y)%Z -> (- y < - x)%Z.
intros x y; case x; case y; simpl in |- *; auto with zarith; intros p p0;
 unfold Zlt in |- *; simpl in |- *; unfold Pos.compare; rewrite <- ZC4;
 auto.
Qed.
Hint Resolve Zlt_Zopp: zarith.
 
Theorem Zle_Zopp : forall x y : Z, (x <= y)%Z -> (- y <= - x)%Z.
intros x y H'; case (Zle_lt_or_eq _ _ H'); auto with zarith.
Qed.
Hint Resolve Zle_Zopp: zarith.
 
Theorem absolu_INR : forall n : nat, Zabs_nat (Z_of_nat n) = n.
intros n; case n; simpl in |- *; auto with arith.
intros n0; rewrite nat_of_P_o_P_of_succ_nat_eq_succ; auto with arith.
Qed.
 
Theorem absolu_Zopp : forall p : Z, Zabs_nat (- p) = Zabs_nat p.
intros p; case p; simpl in |- *; auto.
Qed.
 
Theorem Zabs_absolu : forall z : Z, Zabs z = Z_of_nat (Zabs_nat z).
intros z; case z; simpl in |- *; auto; intros p; apply sym_equal;
 apply inject_nat_convert; auto.
Qed.
 
Theorem absolu_comp_mult :
 forall p q : Z, Zabs_nat (p * q) = Zabs_nat p * Zabs_nat q.
intros p q; case p; case q; simpl in |- *; auto; intros p0 p1;
 apply
  ((fun (x y : positive) (_ : positive -> positive) =>
    nat_of_P_mult_morphism x y) p1 p0 (fun x => x)).
Qed.
 
Theorem Zmin_sym : forall m n : Z, Zmin n m = Zmin m n.
intros m n; unfold Zmin in |- *.
case n; case m; simpl in |- *; auto; unfold Pos.compare.
intros p p0; rewrite (ZC4 p p0).
generalize (Pcompare_Eq_eq p0 p).
case (Pcompare p0 p Datatypes.Eq); simpl in |- *; auto.
intros H'; rewrite H'; auto.
intros p p0; rewrite (ZC4 p p0).
generalize (Pcompare_Eq_eq p0 p).
case (Pcompare p0 p Datatypes.Eq); simpl in |- *; auto.
intros H'; rewrite H'; auto.
Qed.
 
Theorem Zpower_nat_O : forall z : Z, Zpower_nat z 0 = Z_of_nat 1.
intros z; unfold Zpower_nat in |- *; simpl in |- *; auto.
Qed.
 
Theorem Zpower_nat_1 : forall z : Z, Zpower_nat z 1 = z.
intros z; unfold Zpower_nat in |- *; simpl in |- *; rewrite Zmult_1_r; auto.
Qed.
 
Theorem Zmin_le1 : forall z1 z2 : Z, (z1 <= z2)%Z -> Zmin z1 z2 = z1.
intros z1 z2; unfold Zle, Zmin in |- *; case (z1 ?= z2)%Z; auto; intros H;
 Contradict H; auto.
Qed.
 
Theorem Zmin_le2 : forall z1 z2 : Z, (z2 <= z1)%Z -> Zmin z1 z2 = z2.
intros z1 z2 H; rewrite Zmin_sym; apply Zmin_le1; auto.
Qed.
 
Theorem Zmin_Zle :
 forall z1 z2 z3 : Z,
 (z1 <= z2)%Z -> (z1 <= z3)%Z -> (z1 <= Zmin z2 z3)%Z.
intros z1 z2 z3 H' H'0; unfold Zmin in |- *.
case (z2 ?= z3)%Z; auto.
Qed.
 
Theorem Zminus_n_predm :
 forall n m : Z, Zsucc (n - m) = (n - Zpred m)%Z.
intros n m.
unfold Zpred in |- *; unfold Zsucc in |- *; ring.
Qed.
 
Theorem Zopp_Zpred_Zs : forall z : Z, (- Zpred z)%Z = Zsucc (- z).
intros z; unfold Zpred, Zsucc in |- *; ring.
Qed.
 
Theorem Zle_mult_gen :
 forall x y : Z, (0 <= x)%Z -> (0 <= y)%Z -> (0 <= x * y)%Z.
intros x y H' H'0; case (Zle_lt_or_eq _ _ H').
intros H'1; rewrite Zmult_comm; apply Zmult_gt_0_le_0_compat; auto;
 apply Zlt_gt; auto.
intros H'1; rewrite <- H'1; simpl in |- *; auto with zarith.
Qed.
Hint Resolve Zle_mult_gen: zarith.
 
Definition Zmax : forall x_ x_ : Z, Z :=
  fun n m : Z =>
  match (n ?= m)%Z with
  | Datatypes.Eq => m
  | Datatypes.Lt => m
  | Datatypes.Gt => n
  end.
 
Theorem ZmaxLe1 : forall z1 z2 : Z, (z1 <= Zmax z1 z2)%Z.
intros z1 z2; unfold Zmax in |- *; CaseEq (z1 ?= z2)%Z; simpl in |- *;
 auto with zarith.
unfold Zle in |- *; intros H; rewrite H; red in |- *; intros; discriminate.
Qed.
 
Theorem ZmaxSym : forall z1 z2 : Z, Zmax z1 z2 = Zmax z2 z1.
intros z1 z2; unfold Zmax in |- *; CaseEq (z1 ?= z2)%Z; CaseEq (z2 ?= z1)%Z;
 intros H1 H2; try case (Zcompare_EGAL _ _ H1); auto;
 try case (Zcompare_EGAL _ _ H2); auto; Contradict H1.
case (Zcompare.Zcompare_Gt_Lt_antisym z2 z1); auto.
intros H' H'0; rewrite H'0; auto; red in |- *; intros; discriminate.
case (Zcompare.Zcompare_Gt_Lt_antisym z1 z2); auto.
intros H'; rewrite H'; auto; intros; red in |- *; intros; discriminate.
Qed.
 
Theorem Zmax_le2 : forall z1 z2 : Z, (z1 <= z2)%Z -> Zmax z1 z2 = z2.
intros z1 z2; unfold Zle, Zmax in |- *; case (z1 ?= z2)%Z; auto.
intros H'; case H'; auto.
Qed.
 
Theorem Zmax_le1 : forall z1 z2 : Z, (z2 <= z1)%Z -> Zmax z1 z2 = z1.
intros z1 z2 H'; rewrite ZmaxSym; apply Zmax_le2; auto.
Qed.
 
Theorem ZmaxLe2 : forall z1 z2 : Z, (z2 <= Zmax z1 z2)%Z.
intros z1 z2; rewrite ZmaxSym; apply ZmaxLe1.
Qed.
Hint Resolve ZmaxLe1 ZmaxLe2: zarith.
 
Theorem Zeq_Zs :
 forall p q : Z, (p <= q)%Z -> (q < Zsucc p)%Z -> p = q.
intros p q H' H'0; apply Zle_antisym; auto.
apply Zlt_succ_le; auto.
Qed.
 
Theorem Zmin_Zmax : forall z1 z2 : Z, (Zmin z1 z2 <= Zmax z1 z2)%Z.
intros z1 z2; case (Zle_or_lt z1 z2); unfold Zle, Zlt, Zmin, Zmax in |- *;
 CaseEq (z1 ?= z2)%Z; auto; intros H1 H2; try rewrite H1; 
 try rewrite H2; red in |- *; intros; discriminate.
Qed.
 
Theorem Zabs_Zmult :
 forall z1 z2 : Z, Zabs (z1 * z2) = (Zabs z1 * Zabs z2)%Z.
intros z1 z2; case z1; case z2; simpl in |- *; auto with zarith.
Qed.
 
Theorem Zle_Zmult_comp_r :
 forall x y z : Z, (0 <= z)%Z -> (x <= y)%Z -> (x * z <= y * z)%Z.
intros x y z H' H'0; case (Zle_lt_or_eq _ _ H'); intros Zlt1.
apply Zmult_gt_0_le_compat_r; auto.
apply Zlt_gt; auto.
rewrite <- Zlt1; repeat rewrite <- Zmult_0_r_reverse; auto with zarith.
Qed.
 
Theorem Zle_Zmult_comp_l :
 forall x y z : Z, (0 <= z)%Z -> (x <= y)%Z -> (z * x <= z * y)%Z.
intros x y z H' H'0; repeat rewrite (Zmult_comm z);
 apply Zle_Zmult_comp_r; auto.
Qed.
 
Theorem NotZmultZero :
 forall z1 z2 : Z, z1 <> 0%Z -> z2 <> 0%Z -> (z1 * z2)%Z <> 0%Z.
intros z1 z2; case z1; case z2; simpl in |- *; intros; auto; try discriminate.
Qed.
Hint Resolve NotZmultZero: zarith.
(* Conversions from R <-> Z  <-> N *)
 
Theorem IZR_zero : forall p : Z, p = 0%Z -> IZR p = 0%R.
intros p H'; rewrite H'; auto.
Qed.
Hint Resolve not_O_INR: real.
 
Theorem IZR_zero_r : forall p : Z, IZR p = 0%R -> p = 0%Z.
intros p; case p; simpl in |- *; auto.
intros p1 H'; Contradict H'; auto with real zarith.
intros p1 H'; absurd (INR (nat_of_P p1) = 0%R); auto with real zarith.
rewrite <- (Ropp_involutive (INR (nat_of_P p1))).
unfold IZR in H'; rewrite <- INR_IPR in H'.
rewrite H'; auto with real.
Qed.
 
Theorem INR_lt_nm : forall n m : nat, n < m -> (INR n < INR m)%R.
intros n m H'; elim H'; auto.
replace (INR n) with (INR n + 0)%R; auto with real; rewrite S_INR;
 auto with real.
intros m0 H'0 H'1.
replace (INR n) with (INR n + 0)%R; auto with real; rewrite S_INR;
 auto with real.
Qed.
Hint Resolve INR_lt_nm: real.
 
Theorem Rlt_INR1 : forall n : nat, 1 < n -> (1 < INR n)%R.
replace 1%R with (INR 1); auto with real.
Qed.
Hint Resolve Rlt_INR1: real.
 
Theorem NEq_INR : forall n m : nat, n <> m -> INR n <> INR m.
intros n m H'; (case (le_or_lt n m); intros H'1).
case (le_lt_or_eq _ _ H'1); intros H'2.
apply Rlt_dichotomy_converse; auto with real.
Contradict H'; auto.
apply Compare.not_eq_sym; apply Rlt_dichotomy_converse; auto with real.
Qed.
Hint Resolve NEq_INR: real.
 
Theorem NEq_INRO : forall n : nat, n <> 0 -> INR n <> 0%R.
replace 0%R with (INR 0); auto with real.
Qed.
Hint Resolve NEq_INRO: real.
 
Theorem NEq_INR1 : forall n : nat, n <> 1 -> INR n <> 1%R.
replace 1%R with (INR 1); auto with real.
Qed.
Hint Resolve NEq_INR1: real.
 
Theorem not_O_lt : forall n : nat, n <> 0 -> 0 < n.
intros n; elim n; simpl in |- *; auto with arith.
Qed.
Hint Resolve not_O_lt: arith.
 
Theorem NEq_IZRO : forall n : Z, n <> 0%Z -> IZR n <> 0%R.
intros n H; Contradict H.
apply IZR_zero_r; auto.
Qed.
Hint Resolve NEq_IZRO: real.
 
Theorem Rlt_IZR : forall p q : Z, (p < q)%Z -> (IZR p < IZR q)%R.
intros p q H; case (Rle_or_lt (IZR q) (IZR p)); auto.
intros H1; Contradict H; apply Zle_not_lt.
apply le_IZR; auto.
Qed.
Hint Resolve Rlt_IZR: real.
 
Theorem Rle_IZR : forall x y : Z, (x <= y)%Z -> (IZR x <= IZR y)%R.
intros x y H'.
case (Zle_lt_or_eq _ _ H'); clear H'; intros H'.
apply Rlt_le; auto with real.
rewrite <- H'; auto with real.
Qed.
Hint Resolve Rle_IZR: real.
 
Theorem Rlt_IZRO : forall p : Z, (0 < p)%Z -> (0 < IZR p)%R.
intros p H; replace 0%R with (IZR 0); auto with real.
Qed.
Hint Resolve Rlt_IZRO: real.
 
Theorem Rle_IZRO : forall x y : Z, (0 <= y)%Z -> (0 <= IZR y)%R.
intros; replace 0%R with (IZR 0); auto with real.
Qed.
Hint Resolve Rle_IZRO: real.
 
Theorem Rlt_IZR1 : forall p q : Z, (1 < q)%Z -> (1 < IZR q)%R.
intros; replace 1%R with (IZR 1); auto with real.
Qed.
Hint Resolve Rlt_IZR1: real.
 
Theorem Rle_IZR1 : forall x y : Z, (1 <= y)%Z -> (1 <= IZR y)%R.
intros; replace 1%R with (IZR 1); auto with real.
Qed.
Hint Resolve Rle_IZR1: real.
 
Theorem lt_Rlt : forall n m : nat, (INR n < INR m)%R -> n < m.
intros n m H'; case (le_or_lt m n); auto; intros H0; Contradict H';
 auto with real.
case (le_lt_or_eq _ _ H0); intros H1; auto with real.
rewrite H1; apply Rlt_irrefl.
Qed.
 
Theorem INR_inv : forall n m : nat, INR n = INR m -> n = m.
intros n; elim n; auto; try rewrite S_INR.
intros m; case m; auto.
intros m' H1; Contradict H1; auto.
rewrite S_INR.
apply Rlt_dichotomy_converse; left.
apply Rle_lt_0_plus_1.
apply pos_INR.
intros n' H' m; case m.
intros H'0; Contradict H'0; auto.
rewrite S_INR.
apply Rlt_dichotomy_converse; right.
red in |- *; apply Rle_lt_0_plus_1.
apply pos_INR.
intros m' H'0.
rewrite (H' m'); auto.
repeat rewrite S_INR in H'0.
apply Rplus_eq_reg_l with (r := 1%R); repeat rewrite (Rplus_comm 1);
 auto with real.
Qed.
 
Theorem Rle_INR : forall x y : nat, x <= y -> (INR x <= INR y)%R.
intros x y H; repeat rewrite INR_IZR_INZ.
apply Rle_IZR; auto with zarith.
Qed.
Hint Resolve Rle_INR: real.
 
Theorem le_Rle : forall n m : nat, (INR n <= INR m)%R -> n <= m.
intros n m H'; case H'; auto.
intros H'0; apply lt_le_weak; apply lt_Rlt; auto.
intros H'0; rewrite <- (INR_inv _ _ H'0); auto with arith.
Qed.
 
Theorem Rmult_IZR : forall z t : Z, IZR (z * t) = (IZR z * IZR t)%R.
intros z t; case z; case t; simpl in |- *; auto with real; unfold IZR; intros t1 z1; repeat rewrite <- INR_IPR.
- rewrite nat_of_P_mult_morphism; auto with real.
- rewrite nat_of_P_mult_morphism; auto with real.
  rewrite Rmult_comm.
  rewrite Ropp_mult_distr_l_reverse; auto with real.
  apply Ropp_eq_compat; rewrite mult_comm; auto with real.
- rewrite nat_of_P_mult_morphism; auto with real.
  rewrite Ropp_mult_distr_l_reverse; auto with real.
- rewrite nat_of_P_mult_morphism; auto with real.
  rewrite Rmult_opp_opp; auto with real.
Qed.
 
Theorem absolu_Zs :
 forall z : Z, (0 <= z)%Z -> Zabs_nat (Zsucc z) = S (Zabs_nat z).
intros z; case z.
3: intros p H'; Contradict H'; auto with zarith.
replace (Zsucc 0) with (Z_of_nat 1).
intros H'; rewrite absolu_INR; simpl in |- *; auto.
simpl in |- *; auto.
intros p H'; rewrite <- Zpos_succ_morphism; simpl in |- *; auto with zarith.
unfold nat_of_P in |- *; rewrite Pmult_nat_succ_morphism; auto.
Qed.
Hint Resolve Zlt_le_succ: zarith.
 
Theorem Zlt_next :
 forall n m : Z, (n < m)%Z -> m = Zsucc n \/ (Zsucc n < m)%Z.
intros n m H'; case (Zle_lt_or_eq (Zsucc n) m); auto with zarith.
Qed.
 
Theorem Zle_next :
 forall n m : Z, (n <= m)%Z -> m = n \/ (Zsucc n <= m)%Z.
intros n m H'; case (Zle_lt_or_eq _ _ H'); auto with zarith.
Qed.
 
Theorem Zlt_Zopp_Inv : forall p q : Z, (- p < - q)%Z -> (q < p)%Z.
intros x y H'; case (Zle_or_lt x y); auto with zarith.
Qed.
 
Theorem Zle_Zopp_Inv : forall p q : Z, (- p <= - q)%Z -> (q <= p)%Z.
intros p q H'; case (Zle_lt_or_eq _ _ H'); auto with zarith.
Qed.
 
Theorem absolu_Zs_neg :
 forall z : Z, (z < 0)%Z -> S (Zabs_nat (Zsucc z)) = Zabs_nat z.
intros z H'; apply inject_nat_eq.
rewrite inj_S.
repeat rewrite <- (absolu_Zopp (Zsucc z)).
repeat rewrite <- (absolu_Zopp z).
repeat rewrite inj_abs; replace 0%Z with (- (0))%Z; auto with zarith.
Qed.
 
Theorem Zlt_absolu :
 forall (x : Z) (n : nat), Zabs_nat x < n -> (x < Z_of_nat n)%Z.
intros x n; case x; simpl in |- *; auto with zarith.
replace 0%Z with (Z_of_nat 0); auto with zarith.
intros p; rewrite <- (inject_nat_convert (Zpos p) p); auto with zarith.
case n; simpl in |- *; intros; red in |- *; simpl in |- *; auto.
Qed.
 
Theorem inj_pred :
 forall n : nat, n <> 0 -> Z_of_nat (pred n) = Zpred (Z_of_nat n).
intros n; case n; auto.
intros H'; Contradict H'; auto.
intros n0 H'; rewrite inj_S; rewrite <- Zpred_succ; auto.
Qed.
 
Theorem Zle_abs : forall p : Z, (p <= Z_of_nat (Zabs_nat p))%Z.
intros p; case p; simpl in |- *; auto with zarith; intros q;
 rewrite inject_nat_convert with (p := Zpos q); 
 auto with zarith.
unfold Zle in |- *; red in |- *; intros H'2; discriminate.
Qed.
Hint Resolve Zle_abs: zarith.
 
Theorem ZleAbs :
 forall (z : Z) (n : nat),
 (- Z_of_nat n <= z)%Z -> (z <= Z_of_nat n)%Z -> Zabs_nat z <= n.
intros z n H' H'0; case (le_or_lt (Zabs_nat z) n); auto; intros lt.
case (Zle_or_lt 0 z); intros Zle0.
Contradict H'0.
apply Zlt_not_le; auto.
rewrite <- (inj_abs z); auto with zarith.
Contradict H'.
apply Zlt_not_le; auto.
replace z with (- Z_of_nat (Zabs_nat z))%Z.
apply Zlt_Zopp; auto with zarith.
rewrite <- absolu_Zopp.
rewrite inj_abs; auto with zarith.
Qed.
 
Theorem lt_Zlt_inv : forall n m : nat, (Z_of_nat n < Z_of_nat m)%Z -> n < m.
intros n m H'; case (le_or_lt n m); auto.
intros H'0.
case (le_lt_or_eq _ _ H'0); auto with zarith.
intros H'1.
Contradict H'.
apply Zle_not_lt; auto with zarith.
Qed.
 
Theorem NconvertO : forall p : positive, nat_of_P p <> 0.
intros p; elim p; unfold nat_of_P in |- *; simpl in |- *.
intros p0 H'; red in |- *; intros H'0; discriminate.
intros p0; rewrite ZL6; unfold nat_of_P in |- *.
case (Pmult_nat p0 1); simpl in |- *; auto.
red in |- *; intros H'; discriminate.
Qed.
Hint Resolve NconvertO: zarith.
 
Theorem absolu_lt_nz : forall z : Z, z <> 0%Z -> 0 < Zabs_nat z.
intros z; case z; simpl in |- *; auto; try (intros H'; case H'; auto; fail);
 intros p; generalize (NconvertO p); auto with arith.
Qed.
 
Theorem Rlt2 : (0 < INR 2)%R.
replace 0%R with (INR 0); auto with real arith.
Qed.
Hint Resolve Rlt2: real.
 
Theorem RlIt2 : (0 < / INR 2)%R.
apply Rmult_lt_reg_l with (r := INR 2); auto with real.
Qed.
Hint Resolve RlIt2: real.
 
Theorem Rledouble : forall r : R, (0 <= r)%R -> (r <= INR 2 * r)%R.
intros r H'.
replace (INR 2 * r)%R with (r + r)%R; [ idtac | simpl in |- *; ring ].
pattern r at 1 in |- *; replace r with (r + 0)%R; [ idtac | ring ].
apply Rplus_le_compat_l; auto.
Qed.
 
Theorem Rltdouble : forall r : R, (0 < r)%R -> (r < INR 2 * r)%R.
intros r H'.
pattern r at 1 in |- *; replace r with (r + 0)%R; try ring.
replace (INR 2 * r)%R with (r + r)%R; simpl in |- *; try ring; auto with real.
Qed.
 
Theorem Rlt_RinvDouble : forall r : R, (0 < r)%R -> (/ INR 2 * r < r)%R.
intros r H'.
apply Rmult_lt_reg_l with (r := INR 2); auto with real.
rewrite <- Rmult_assoc; rewrite Rinv_r.
apply Rmult_lt_compat_r; replace 1%R with (INR 1); auto with real arith.
replace 0%R with (INR 0); auto with real arith.
Qed.
Hint Resolve Rledouble: real.
 
Theorem Rle_Rinv : forall x y : R, (0 < x)%R -> (x <= y)%R -> (/ y <= / x)%R.
intros x y H H1; case H1; intros H2.
left; apply Rinv_lt_contravar; auto.
apply Rmult_lt_0_compat; auto.
apply Rlt_trans with (2 := H2); auto.
rewrite H2; auto with real.
Qed.
 
Theorem Int_part_INR : forall n : nat, Int_part (INR n) = Z_of_nat n.
intros n; unfold Int_part in |- *.
cut (up (INR n) = (Z_of_nat n + Z_of_nat 1)%Z).
intros H'; rewrite H'; simpl in |- *; ring.
apply sym_equal; apply tech_up; auto.
replace (Z_of_nat n + Z_of_nat 1)%Z with (Z_of_nat (S n)).
repeat rewrite <- INR_IZR_INZ.
apply INR_lt_nm; auto.
rewrite Zplus_comm; rewrite <- inj_plus; simpl in |- *; auto.
rewrite plus_IZR; simpl in |- *; auto with real.
repeat rewrite <- INR_IZR_INZ; auto with real.
Qed.
 
Theorem Int_part_IZR : forall z : Z, Int_part (IZR z) = z.
intros z; unfold Int_part in |- *.
cut (up (IZR z) = (z + 1)%Z).
intros Z1; rewrite Z1; rewrite Zplus_comm; apply Zminus_plus;
 auto with zarith.
apply sym_equal; apply tech_up; simpl in |- *; auto with real zarith.
replace (IZR z) with (IZR z + IZR 0)%R; try rewrite plus_IZR;
 auto with real zarith.
Qed.
 
Theorem Zlt_Rlt : forall z1 z2 : Z, (IZR z1 < IZR z2)%R -> (z1 < z2)%Z.
intros z1 z2 H; case (Zle_or_lt z2 z1); auto.
intros H1; Contradict H; auto with real zarith.
apply Rle_not_lt; auto with real zarith.
Qed.
 
Theorem Zle_Rle :
 forall z1 z2 : Z, (IZR z1 <= IZR z2)%R -> (z1 <= z2)%Z.
intros z1 z2 H; case (Zle_or_lt z1 z2); auto.
intros H1; Contradict H; auto with real zarith.
apply Rlt_not_le; auto with real zarith.
Qed.
 
Theorem IZR_inv : forall z1 z2 : Z, IZR z1 = IZR z2 :>R -> z1 = z2.
intros z1 z2 H; apply Zle_antisym; apply Zle_Rle; rewrite H; auto with real.
Qed.
 
Theorem Zabs_eq_opp : forall x, (x <= 0)%Z -> Zabs x = (- x)%Z.
intros x; case x; simpl in |- *; auto.
intros p H; Contradict H; auto with zarith.
Qed.
 
Theorem Zabs_Zs : forall z : Z, (Zabs (Zsucc z) <= Zsucc (Zabs z))%Z.
intros z; case z; auto.
simpl in |- *; auto with zarith.
repeat rewrite Zabs_eq; auto with zarith.
intros p; rewrite Zabs_eq_opp; auto with zarith.
2: unfold Zsucc in |- *; replace 0%Z with (-1 + 1)%Z; auto with zarith.
2: case p; simpl in |- *; intros; red in |- *; simpl in |- *; intros;
    red in |- *; intros; discriminate.
replace (- Zsucc (Zneg p))%Z with (Zpos p - 1)%Z.
replace (Zsucc (Zabs (Zneg p))) with (Zpos p + 1)%Z;
 auto with zarith.
unfold Zsucc in |- *; rewrite Zopp_plus_distr.
auto with zarith.
Qed.
Hint Resolve Zabs_Zs: zarith.
 
Theorem Zle_Zpred : forall x y : Z, (x < y)%Z -> (x <= Zpred y)%Z.
intros x y H; apply Zlt_succ_le.
rewrite <- Zsucc_pred; auto.
Qed.
Hint Resolve Zle_Zpred: zarith.
 
Theorem Zabs_Zopp : forall z : Z, Zabs (- z) = Zabs z.
intros z; case z; simpl in |- *; auto.
Qed.
 
Theorem Zle_Zabs : forall z : Z, (z <= Zabs z)%Z.
intros z; case z; simpl in |- *; red in |- *; simpl in |- *; auto;
 try (red in |- *; intros; discriminate; fail).
intros p; elim p; simpl in |- *; auto;
 try (red in |- *; intros; discriminate; fail).
Qed.
Hint Resolve Zle_Zabs: zarith.
 
Theorem Zlt_mult_simpl_l :
 forall a b c : Z, (0 < c)%Z -> (c * a < c * b)%Z -> (a < b)%Z.
intros a b0 c H H0; apply Zgt_lt.
apply Zmult_gt_reg_r with (p := c); try apply Zlt_gt; auto with zarith.
repeat rewrite (fun x => Zmult_comm x c); auto with zarith.
Qed.
(* An equality function on Z that return a bool *)
 
Fixpoint pos_eq_bool (a b : positive) {struct b} : bool :=
  match a, b with
  | xH, xH => true
  | xI a', xI b' => pos_eq_bool a' b'
  | xO a', xO b' => pos_eq_bool a' b'
  | _, _ => false
  end.
 
Theorem pos_eq_bool_correct :
 forall p q : positive,
 match pos_eq_bool p q with
 | true => p = q
 | false => p <> q
 end.
intros p q; generalize p; elim q; simpl in |- *; auto; clear p q.
intros p Rec q; case q; simpl in |- *;
 try (intros; red in |- *; intros; discriminate; fail).
intros q'; generalize (Rec q'); case (pos_eq_bool q' p); simpl in |- *; auto.
intros H1; rewrite H1; auto.
intros H1; Contradict H1; injection H1; auto.
intros p Rec q; case q; simpl in |- *;
 try (intros; red in |- *; intros; discriminate; fail).
intros q'; generalize (Rec q'); case (pos_eq_bool q' p); simpl in |- *; auto.
intros H1; rewrite H1; auto.
intros H1; Contradict H1; injection H1; auto.
intros q; case q; simpl in |- *;
 try (intros; red in |- *; intros; discriminate; fail); 
 auto.
Qed.
 
Theorem Z_O_1 : (0 < 1)%Z.
red in |- *; simpl in |- *; auto; intros; red in |- *; intros; discriminate.
Qed.
Hint Resolve Z_O_1: zarith.
 
Definition Z_eq_bool a b :=
  match a, b with
  | Z0, Z0 => true
  | Zpos a', Zpos b' => pos_eq_bool a' b'
  | Zneg a', Zneg b' => pos_eq_bool a' b'
  | _, _ => false
  end.
 
Theorem Z_eq_bool_correct :
 forall p q : Z,
 match Z_eq_bool p q with
 | true => p = q
 | false => p <> q
 end.
intros p q; case p; case q; simpl in |- *; auto;
 try (intros; red in |- *; intros; discriminate; fail).
intros p' q'; generalize (pos_eq_bool_correct q' p');
 case (pos_eq_bool q' p'); simpl in |- *; auto.
intros H1; rewrite H1; auto.
intros H1; Contradict H1; injection H1; auto.
intros p' q'; generalize (pos_eq_bool_correct q' p');
 case (pos_eq_bool q' p'); simpl in |- *; auto.
intros H1; rewrite H1; auto.
intros H1; Contradict H1; injection H1; auto.
Qed.
 
Theorem Zlt_mult_ZERO :
 forall x y : Z, (0 < x)%Z -> (0 < y)%Z -> (0 < x * y)%Z.
intros x y; case x; case y; unfold Zlt in |- *; simpl in |- *; auto.
Qed.
Hint Resolve Zlt_mult_ZERO: zarith.
 
Theorem Zlt_Zminus_ZERO :
 forall z1 z2 : Z, (z2 < z1)%Z -> (0 < z1 - z2)%Z.
intros z1 z2; rewrite (Zminus_diag_reverse z2); auto with zarith.
Qed.
 
Theorem Zle_Zminus_ZERO :
 forall z1 z2 : Z, (z2 <= z1)%Z -> (0 <= z1 - z2)%Z.
intros z1 z2; rewrite (Zminus_diag_reverse z2); auto with zarith.
Qed.
Hint Resolve Zle_Zminus_ZERO Zlt_Zminus_ZERO: zarith.
 
Theorem Zle_Zpred_Zpred :
 forall z1 z2 : Z, (z1 <= z2)%Z -> (Zpred z1 <= Zpred z2)%Z.
intros z1 z2 H; apply Zsucc_le_reg.
repeat rewrite <- Zsucc_pred; auto.
Qed.
Hint Resolve Zle_Zpred_Zpred: zarith.
 
Theorem Zle_ZERO_Zabs : forall z : Z, (0 <= Zabs z)%Z.
intros z; case z; simpl in |- *; auto with zarith.
Qed.
Hint Resolve Zle_ZERO_Zabs: zarith.
 
Theorem Zlt_Zabs_inv1 :
 forall z1 z2 : Z, (Zabs z1 < z2)%Z -> (- z2 < z1)%Z.
intros z1 z2 H; case (Zle_or_lt 0 z1); intros H1.
apply Zlt_le_trans with (- (0))%Z; auto with zarith.
apply Zlt_Zopp; apply Zle_lt_trans with (2 := H); auto with zarith.
rewrite <- (Zopp_involutive z1); rewrite <- (Zabs_eq_opp z1);
 auto with zarith.
Qed.
 
Theorem Zlt_Zabs_inv2 :
 forall z1 z2 : Z, (Zabs z1 < Zabs z2)%Z -> (z1 < Zabs z2)%Z.
intros z1 z2; case z1; case z2; simpl in |- *; auto with zarith.
Qed.
 
Theorem Zle_Zabs_inv1 :
 forall z1 z2 : Z, (Zabs z1 <= z2)%Z -> (- z2 <= z1)%Z.
intros z1 z2 H; case (Zle_or_lt 0 z1); intros H1.
apply Zle_trans with (- (0))%Z; auto with zarith.
apply Zle_Zopp; apply Zle_trans with (2 := H); auto with zarith.
rewrite <- (Zopp_involutive z1); rewrite <- (Zabs_eq_opp z1);
 auto with zarith.
Qed.
 
Theorem Zle_Zabs_inv2 :
 forall z1 z2 : Z, (Zabs z1 <= z2)%Z -> (z1 <= z2)%Z.
intros z1 z2 H; case (Zle_or_lt 0 z1); intros H1.
rewrite <- (Zabs_eq z1); auto.
apply Zle_trans with (Zabs z1); auto with zarith.
Qed.
 
Theorem Zlt_Zabs_Zpred :
 forall z1 z2 : Z,
 (Zabs z1 < z2)%Z -> z1 <> Zpred z2 -> (Zabs (Zsucc z1) < z2)%Z.
intros z1 z2 H H0; case (Zle_or_lt 0 z1); intros H1.
rewrite Zabs_eq; auto with zarith.
rewrite Zabs_eq in H; auto with zarith.
apply Zlt_trans with (2 := H).
repeat rewrite Zabs_eq_opp; auto with zarith.
Qed.
 
Theorem Zle_n_Zpred :
 forall z1 z2 : Z, (Zpred z1 <= Zpred z2)%Z -> (z1 <= z2)%Z.
intros z1 z2 H; rewrite (Zsucc_pred z1); rewrite (Zsucc_pred z2);
 auto with zarith.
Qed.
 
Theorem Zpred_Zopp_Zs : forall z : Z, Zpred (- z) = (- Zsucc z)%Z.
intros z; unfold Zpred, Zsucc in |- *; ring.
Qed.
 
Theorem Zlt_1_O : forall z : Z, (1 <= z)%Z -> (0 < z)%Z.
intros z H; apply Zsucc_lt_reg; simpl in |- *; auto with zarith.
Qed.
Hint Resolve Zlt_succ Zsucc_lt_compat Zle_lt_succ: zarith.
 
Theorem Zlt_not_eq : forall p q : Z, (p < q)%Z -> p <> q.
intros p q H; Contradict H; rewrite H; auto with zarith.
Qed.
 
Theorem Zlt_not_eq_rev : forall p q : Z, (q < p)%Z -> p <> q.
intros p q H; Contradict H; rewrite H; auto with zarith.
Qed.
Hint Resolve Zlt_not_eq Zlt_not_eq_rev: zarith.
 
Theorem Zle_Zpred_Zlt :
 forall z1 z2 : Z, (z1 <= z2)%Z -> (Zpred z1 < z2)%Z.
intros z1 z2 H; apply Zsucc_lt_reg; rewrite <- Zsucc_pred; auto with zarith.
Qed.
Hint Resolve Zle_Zpred_Zlt: zarith.
 
Theorem Zle_Zpred_inv :
 forall z1 z2 : Z, (z1 <= Zpred z2)%Z -> (z1 < z2)%Z.
intros z1 z2 H; rewrite (Zsucc_pred z2); auto with zarith.
Qed.
 
Theorem Zabs_intro :
 forall (P : Z -> Prop) (z : Z), P (- z)%Z -> P z -> P (Zabs z).
intros P z; case z; simpl in |- *; auto.
Qed.
 
Theorem Zpred_Zle_Zabs_intro :
 forall z1 z2 : Z,
 (- Zpred z2 <= z1)%Z -> (z1 <= Zpred z2)%Z -> (Zabs z1 < z2)%Z.
intros z1 z2 H H0; apply Zle_Zpred_inv.
apply Zabs_intro with (P := fun x => (x <= Zpred z2)%Z); auto with zarith.
Qed.
 
Theorem Zlt_ZERO_Zle_ONE : forall z : Z, (0 < z)%Z -> (1 <= z)%Z.
intros z H; replace 1%Z with (Zsucc 0); auto with zarith; simpl in |- *; auto.
Qed.
Hint Resolve Zlt_ZERO_Zle_ONE: zarith.
 
Theorem ptonat_def1 : forall p q, 1 < Pmult_nat p (S (S q)).
intros p; elim p; simpl in |- *; auto with arith.
Qed.
Hint Resolve ptonat_def1: arith.
 
Theorem lt_S_le : forall p q, p < q -> S p <= q.
intros p q; unfold lt in |- *; simpl in |- *; auto.
Qed.
Hint Resolve lt_S_le: arith.
 
Theorem Zlt_Zabs_intro :
 forall z1 z2 : Z, (- z2 < z1)%Z -> (z1 < z2)%Z -> (Zabs z1 < z2)%Z.
intros z1 z2; case z1; case z2; simpl in |- *; auto with zarith.
intros p p0 H H0; change (- Zneg p0 < - Zneg p)%Z in |- *;
 auto with zarith.
Qed.
