Require Import Arith.
Require Import Wf_nat.
Require Import ZArith.
Require Import Peano_dec.
Require Import ZArith_dec.
From Pocklington Require Import gcd divides natZ prime modprime.
Require Import Max.

Lemma multO : forall a b : nat, a * b = 0 -> a = 0 \/ b = 0.
Proof.
intros.
induction (mult_O_le b a).
auto.
rewrite H in H0.
right.
symmetry  in |- *.
apply le_n_O_eq.
assumption.
Qed.

Definition CoPrime (a b : nat) := gcd (Z_of_nat a) (Z_of_nat b) 1.

Lemma coPrimeSym : forall a b : nat, CoPrime a b -> CoPrime b a.
Proof.
unfold CoPrime in |- *.
intros.
apply gcd_sym.
assumption.
Qed.

Lemma coPrimeMult :
 forall a b c : nat, CoPrime a b -> Divides a (b * c) -> Divides a c.
Proof.
intros.
unfold CoPrime in H.
induction a as [| a Hreca].
induction H0 as (x, H0).
induction (multO _ _ H0).
rewrite H1 in H.
unfold gcd in H.
induction H as (H, H2).
assert (2 <= 1).
apply H2.
split.
simpl in |- *.
exists 0.
rewrite mult_comm.
simpl in |- *.
reflexivity.
exists 0.
rewrite mult_comm.
simpl in |- *.
reflexivity.
elim (le_Sn_n _ H3).
exists 0.
rewrite H1.
auto.
clear Hreca.
assert (S a > 0).
apply gt_Sn_O.
induction (gcd_lincomb_nat _ _ _ H1 H).
induction H2 as (x0, H2).
induction H0 as (x1, H0).
assert
 ((1 * Z_of_nat c)%Z =
  (Z_of_nat (S a) * (x * Z_of_nat c + Z_of_nat x1 * x0))%Z).
rewrite (Zmult_comm (Z_of_nat (S a))).
rewrite Zmult_plus_distr_l.
rewrite (Zmult_comm (x * Z_of_nat c)).
rewrite (Zmult_comm (Z_of_nat x1 * x0)).
repeat rewrite Zmult_assoc.
rewrite <- Znat.inj_mult.
rewrite <- H0.
rewrite Znat.inj_mult.
rewrite (Zmult_comm (Z_of_nat b)).
rewrite (Zmult_assoc_reverse (Z_of_nat c)).
rewrite (Zmult_comm (Z_of_nat c)).
rewrite <- Zmult_plus_distr_l.
rewrite <- H2.
reflexivity.
rewrite Zmult_1_l in H3.
assert (ZDivides (Z_of_nat (S a)) (Z_of_nat c)).
unfold ZDivides in |- *.
exists (x * Z_of_nat c + Z_of_nat x1 * x0)%Z.
assumption.
clear H2 H3 x x0.
rewrite <- (abs_inj (S a)).
rewrite <- (abs_inj c).
apply zdivdiv.
assumption.
Qed.

Lemma coPrimeMult2 :
 forall a b c : nat,
 CoPrime a b -> Divides a c -> Divides b c -> Divides (a * b) c.
Proof.
intros.
induction H1 as (x, H1).
assert (Divides a x).
eapply coPrimeMult.
apply H.
rewrite <- H1.
assumption.
induction H2 as (x0, H2).
exists x0.
rewrite (mult_comm a).
rewrite (mult_assoc_reverse b).
rewrite <- H2.
assumption.
Qed.

Lemma ltgt1 : forall a b : nat, a < b -> b > 0.
Proof.
intros.
unfold gt in |- *.
eapply le_lt_trans.
apply le_O_n.
apply H.
Qed.

Lemma minus_le : forall a b : nat, a - b <= a.
Proof.
intros.
induction b as [| b Hrecb].
rewrite <- minus_n_O.
apply le_n.
induction (le_or_lt (S b) a).
apply lt_le_weak.
apply lt_minus.
assumption.
apply lt_O_Sn.
rewrite not_le_minus_0.
apply le_O_n.
apply lt_not_le.
assumption.
Qed.

Lemma minus1 : forall a b c : Z, (a - c)%Z = (b - c)%Z -> a = b.
Proof.
intros.
rewrite <- (Zminus_plus c b).
rewrite <- (Zminus_plus c a).
unfold Zminus in H.
unfold Zminus in |- *.
rewrite Zplus_assoc_reverse.
rewrite H.
rewrite Zplus_assoc_reverse.
reflexivity.
Qed.

Lemma chRem2 :
 forall b1 r1 b2 r2 q : Z,
 (0 <= r1)%Z ->
 (0 <= r2)%Z ->
 (r1 < q)%Z -> (r2 < q)%Z -> (b1 * q + r1)%Z = (b2 * q + r2)%Z -> r1 = r2.
Proof.
intros.
assert (((b1 - b2) * q)%Z = (r2 - r1)%Z).
rewrite Zmult_minus_distr_r.
apply Zplus_minus_eq.
unfold Zminus in |- *.
rewrite Zplus_assoc.
fold (r1 + b1 * q - b2 * q)%Z in |- *.
apply Zplus_minus_eq.
rewrite Zplus_comm.
assumption.
induction (Zle_or_lt 0 (b1 - b2)).
induction (Zle_lt_or_eq _ _ H5).
assert (1 <= b1 - b2)%Z.
replace 1%Z with (Zsucc 0).
apply Zlt_le_succ.
assumption.
auto.
assert (q <= r2 - r1)%Z.
replace q with (1 * q)%Z.
rewrite <- H4.
apply Zmult_le_compat_r.
assumption.
eapply Zle_trans.
apply H.
apply Zlt_le_weak.
assumption.
apply Zmult_1_l.
set (A1 := Zplus_lt_le_compat r2 q (- r1) 0 H2) in *.
assert (r2 - r1 < q)%Z.
replace q with (q + 0)%Z.
unfold Zminus in |- *.
apply A1.
eapply (fun a b : Z => Zplus_le_reg_l a b r1).
rewrite Zplus_opp_r.
rewrite <- Zplus_0_r_reverse.
assumption.
rewrite <- Zplus_0_r_reverse.
reflexivity.
elim (Zle_not_lt q (r2 - r1)).
assumption.
assumption.
rewrite <- H6 in H4.
rewrite Zmult_comm in H4.
rewrite <- Zmult_0_r_reverse in H4.
rewrite <- (Zplus_opp_r r2) in H4.
unfold Zminus in H4.
apply Zopp_inj.
symmetry  in |- *.
eapply Zplus_reg_l.
apply H4.
assert (1 <= b2 - b1)%Z.
replace 1%Z with (Zsucc 0).
apply Zlt_le_succ.
apply (Zplus_lt_reg_l 0 (b2 - b1) b1).
rewrite Zplus_minus.
rewrite <- Zplus_0_r_reverse.
apply (Zplus_lt_reg_l b1 b2 (- b2)).
rewrite Zplus_opp_l.
rewrite Zplus_comm.
unfold Zminus in H5.
assumption.
auto.
assert (((b2 - b1) * q)%Z = (r1 - r2)%Z).
rewrite Zmult_minus_distr_r.
apply Zplus_minus_eq.
unfold Zminus in |- *.
rewrite Zplus_assoc.
fold (r2 + b2 * q - b1 * q)%Z in |- *.
apply Zplus_minus_eq.
rewrite Zplus_comm.
symmetry  in |- *.
assumption.
assert (q <= r1 - r2)%Z.
replace q with (1 * q)%Z.
rewrite <- H7.
apply Zmult_le_compat_r.
assumption.
eapply Zle_trans.
apply H.
apply Zlt_le_weak.
assumption.
apply Zmult_1_l.
set (A1 := Zplus_lt_le_compat r1 q (- r2) 0 H1) in *.
assert (r1 - r2 < q)%Z.
replace q with (q + 0)%Z.
unfold Zminus in |- *.
apply A1.
eapply (fun a b : Z => Zplus_le_reg_l a b r2).
rewrite Zplus_opp_r.
rewrite <- Zplus_0_r_reverse.
assumption.
rewrite <- Zplus_0_r_reverse.
reflexivity.
elim (Zle_not_lt q (r1 - r2)).
assumption.
assumption.
Qed.

Lemma chRem3 : forall a b : nat, Z_of_nat a = Z_of_nat b -> a = b.
Proof.
double induction a b.
reflexivity.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
repeat rewrite Znat.inj_S in H1.
apply eq_S.
apply H0.
apply Zsucc_inj.
assumption.
Qed.

Lemma uniqueRem :
 forall r1 r2 b : nat,
 b > 0 ->
 forall a : nat,
 (exists q : nat, a = q * b + r1 /\ b > r1) ->
 (exists q : nat, a = q * b + r2 /\ b > r2) -> r1 = r2.
Proof.
intros.
induction H0 as (x, H0); induction H0 as (H0, H2).
induction H1 as (x0, H1); induction H1 as (H1, H3).
apply chRem3.
eapply chRem2.
replace 0%Z with (Z_of_nat 0).
apply Znat.inj_le.
apply le_O_n.
auto.
replace 0%Z with (Z_of_nat 0).
apply Znat.inj_le.
apply le_O_n.
auto.
apply Znat.inj_lt.
apply H2.
apply Znat.inj_lt.
apply H3.
repeat rewrite <- Znat.inj_mult.
repeat rewrite <- Znat.inj_plus.
apply Znat.inj_eq.
transitivity a.
symmetry  in |- *.
apply H0.
apply H1.
Qed.

Lemma modulo :
 forall b : nat,
 b > 0 ->
 forall a : nat, {p : nat * nat | a = fst p * b + snd p /\ b > snd p}.
Proof.
intros.
apply (gt_wf_rec a).
intros.
induction (le_lt_dec b n).
assert (n > n - b).
unfold gt in |- *.
apply lt_minus.
assumption.
assumption.
induction (H0 _ H1).
induction x as (a1, b0).
simpl in p.
exists (S a1, b0).
simpl in |- *.
induction p as (H2, H3).
split.
rewrite plus_assoc_reverse.
rewrite <- H2.
apply le_plus_minus.
assumption.
assumption.
exists (0, n).
simpl in |- *.
split.
reflexivity.
assumption.
Qed.

Lemma chRem1 :
 forall b : nat,
 b > 0 ->
 forall a : Z,
 {p : Z * nat | snd p < b /\ Z_of_nat (snd p) = (fst p * Z_of_nat b + a)%Z}.
Proof.
intros.
assert
 (forall a' : Z,
  (a' >= 0)%Z ->
  {p : Z * nat | snd p < b /\ Z_of_nat (snd p) = (fst p * Z_of_nat b + a')%Z}).
intros.
set (A := Zabs_nat a') in *.
induction (modulo b H A).
induction x as (a0, b0).
exists ((- Z_of_nat a0)%Z, b0).
induction p as (H1, H2).
split.
apply H2.
rewrite <- (inj_abs_pos a').
replace (fst ((- Z_of_nat a0)%Z, b0)) with (- Z_of_nat a0)%Z.
replace (snd ((- Z_of_nat a0)%Z, b0)) with b0.
rewrite Zopp_mult_distr_l_reverse.
rewrite Zplus_comm.
fold (Z_of_nat (Zabs_nat a') - Z_of_nat a0 * Z_of_nat b)%Z in |- *.
apply Zplus_minus_eq.
rewrite <- Znat.inj_mult.
rewrite <- Znat.inj_plus.
apply Znat.inj_eq.
apply H1.
auto.
auto.
assumption.

induction (Z_ge_lt_dec a 0).
apply H0.
assumption.
assert (a + Z_of_nat b * - a >= 0)%Z.
induction b as [| b Hrecb].
elim (lt_irrefl _ H).
rewrite Znat.inj_S.
rewrite Zmult_comm.
rewrite <- Zmult_succ_r_reverse.
fold (- a * Z_of_nat b - a)%Z in |- *.
rewrite Zplus_minus.
replace 0%Z with (0 * Z_of_nat b)%Z.
apply Zmult_ge_compat_r.
rewrite (Zminus_diag_reverse a).
rewrite <- (Zplus_0_l (- a)).
unfold Zminus in |- *.
apply Zle_ge.
apply Zplus_le_compat_r.
apply Zlt_le_weak.
assumption.
replace 0%Z with (Z_of_nat 0).
apply Znat.inj_ge.
unfold ge in |- *.
apply le_O_n.
auto.
auto.
induction (H0 _ H1).
induction p as (H2, H3).
induction x as (a0, b1).
exists ((a0 - a)%Z, b1).
split.
simpl in |- *.
apply H2.
cbv beta iota zeta delta [fst snd] in |- *.
cbv beta iota zeta delta [fst snd] in H3.
rewrite H3.
rewrite (Zplus_comm a).
rewrite Zplus_assoc.
apply Zplus_eq_compat.
rewrite Zmult_minus_distr_r.
unfold Zminus in |- *.
apply Zplus_eq_compat.
reflexivity.
rewrite Zmult_comm.
apply Zopp_mult_distr_l_reverse.
reflexivity.
Qed.

Lemma gcd_lincomb_nat_dec :
 forall x y d : nat,
 x > 0 ->
 gcd (Z_of_nat x) (Z_of_nat y) d ->
 {a : Z * Z | Z_of_nat d = (Z_of_nat x * fst a + Z_of_nat y * snd a)%Z}.
Proof.
   unfold LinComb in |- *. intro x.
   apply (lt_wf_rec x). intros X IH. intros.
   elim (modulo X H y). intro z. 
   elim z.
   intros q r.
   clear z.
   simpl in |- *.   
   case r.

   (* case r = 0 *)

   intros.
   induction p as (H1, H2).
   rewrite <- plus_n_O in H1.
   exists (1%Z, 0%Z).
   replace (fst (1%Z, 0%Z)) with 1%Z.
   replace (snd (1%Z, 0%Z)) with 0%Z.
   rewrite <- Zmult_0_r_reverse. rewrite <- Zplus_0_r_reverse.
   rewrite Zmult_comm. rewrite Zmult_1_l.
   apply Znat.inj_eq.
   apply (euclid_gcd d X (Z_of_nat y) (Z_of_nat X) (Z_of_nat q) 0).
   rewrite <- Zplus_0_r_reverse. rewrite <- Znat.inj_mult. apply Znat.inj_eq. assumption.
   apply gcd_sym. assumption. apply gcd_0_l. assumption.
   auto.
   auto.

   (* case r > 0 *)
   intro r1. intros.
   induction p as (H1, H2).
   elim (IH (S r1) H2 X d).
   intro z.
   elim z.
   intros delta gamma.
   clear z.
   replace (fst (delta, gamma)) with delta.
   replace (snd (delta, gamma)) with gamma.
   intros.
   exists ((gamma - Z_of_nat q * delta)%Z, delta).
   replace (fst ((gamma - Z_of_nat q * delta)%Z, delta)) with
    (gamma - Z_of_nat q * delta)%Z.
   replace (snd ((gamma - Z_of_nat q * delta)%Z, delta)) with delta.
   rewrite p. rewrite H1.
   unfold Zminus in |- *. rewrite Zmult_plus_distr_r.
   rewrite Znat.inj_plus. rewrite Zmult_plus_distr_l.
   rewrite Znat.inj_mult. rewrite <- Zopp_mult_distr_l_reverse.
   rewrite (Zmult_assoc (Z_of_nat X)).
   rewrite (Zmult_comm (Z_of_nat X) (- Z_of_nat q)).
   rewrite Zopp_mult_distr_l_reverse. rewrite Zopp_mult_distr_l_reverse.
   rewrite (Zplus_assoc_reverse (Z_of_nat X * gamma)).
   rewrite <- Znat.inj_mult.
   rewrite (Zplus_assoc (- (Z_of_nat (q * X) * delta))). 
   rewrite Zplus_opp_l. simpl in |- *. apply Zplus_comm.
auto.
auto.
auto.  
auto.
   apply gt_Sn_O.
   apply
    (euclid_gcd1 d (Z_of_nat y) (Z_of_nat X) (Z_of_nat q) (Z_of_nat (S r1))).
   apply gcd_sym. assumption.
   rewrite <- Znat.inj_mult. rewrite <- Znat.inj_plus. apply Znat.inj_eq. assumption.
Qed.

Lemma chineseRemainderTheoremHelp :
 forall x1 x2 : nat,
 CoPrime x1 x2 ->
 forall (a b : nat) (pa : a < x1) (pb : b < x2),
 a <= b ->
 {y : nat |
 y < x1 * x2 /\
 a = snd (proj1_sig (modulo x1 (ltgt1 _ _ pa) y)) /\
 b = snd (proj1_sig (modulo x2 (ltgt1 _ _ pb) y))}.
Proof.
intros.
unfold CoPrime in H.
induction (gcd_lincomb_nat_dec _ _ _ (ltgt1 _ _ pa) H).
induction x as (a0, b0).
set (A := Z_of_nat a) in *.
set (B := Z_of_nat b) in *.
set (X1 := Z_of_nat x1) in *.
set (X2 := Z_of_nat x2) in *.
set (y := (a0 * (B - A))%Z) in *.
set (z := (b0 * (A - B))%Z) in *.
set (d := (A + X1 * y)%Z) in *.
assert (d = (B + X2 * z)%Z).
unfold d in |- *.
simpl in p.
apply minus1 with (X2 * z)%Z.
rewrite (Zplus_comm B).
rewrite Zminus_plus.
unfold z in |- *.
replace (A - B)%Z with (- (B - A))%Z.
unfold Zminus in |- *.
rewrite (Zmult_comm b0).
rewrite Zopp_mult_distr_l_reverse.
rewrite (Zmult_comm X2).
rewrite Zopp_mult_distr_l_reverse.
rewrite Zopp_involutive.
unfold y in |- *.
rewrite (Zmult_assoc_reverse (B + - A)).
rewrite (Zmult_comm (B + - A)).
rewrite (Zmult_assoc X1).
rewrite (Zmult_comm b0).
rewrite Zplus_assoc_reverse.
rewrite <- Zmult_plus_distr_l.
rewrite <- p.
rewrite Zmult_1_l.
fold (B - A)%Z in |- *.
apply Zplus_minus.
unfold Zminus in |- *.
rewrite Zopp_plus_distr.
rewrite Zplus_comm.
rewrite Zopp_involutive.
reflexivity.
assert (x1 * x2 > 0).
replace 0 with (0 * x2).
unfold gt in |- *.
rewrite mult_comm.
rewrite (mult_comm x1).
induction x2 as [| x2 Hrecx2].
elim (lt_n_O _ pb).
apply mult_S_lt_compat_l.
fold (x1 > 0) in |- *.
eapply ltgt1.
apply pa.
auto.
induction (chRem1 _ H2 d).
induction p0 as (H3, H4).
induction x as (a1, b1).
exists b1.
split.
apply H3.
cbv beta iota zeta delta [snd fst] in H4.
cbv beta iota zeta delta [snd fst] in p.
split.
induction (modulo x1 (ltgt1 a x1 pa) b1).
induction x as (a2, b2).
simpl in |- *.
induction p0 as (H5, H6).
cbv beta iota zeta delta [snd fst] in H5.
rewrite H5 in H4.
unfold d in H4.
unfold A, X1 in H4.
apply chRem3. 
eapply chRem2.
replace 0%Z with (Z_of_nat 0).
apply Znat.inj_le.
apply le_O_n.
auto.
replace 0%Z with (Z_of_nat 0).
apply Znat.inj_le.
apply le_O_n.
auto.
apply Znat.inj_lt.
apply pa.
apply Znat.inj_lt.
apply H6.
rewrite Znat.inj_plus in H4.
repeat rewrite Znat.inj_mult in H4.
symmetry  in |- *.
rewrite (Zplus_comm (Z_of_nat a)) in H4.
rewrite Zplus_assoc in H4.
rewrite Zmult_assoc in H4.
rewrite (Zmult_comm a1) in H4.
rewrite (Zmult_assoc_reverse (Z_of_nat x1)) in H4.
rewrite <- Zmult_plus_distr_r in H4.
rewrite (Zmult_comm (Z_of_nat x1)) in H4.
apply H4.
induction (modulo x2 (ltgt1 b x2 pb) b1).
simpl in |- *.
induction x as (a2, b2).
cbv beta iota zeta delta [snd fst] in p0.
induction p0 as (H5, H6).
rewrite H5 in H4.
rewrite H1 in H4.
unfold B, X2 in H4.
apply chRem3. 
eapply chRem2.
replace 0%Z with (Z_of_nat 0).
apply Znat.inj_le.
apply le_O_n.
auto.
replace 0%Z with (Z_of_nat 0).
apply Znat.inj_le.
apply le_O_n.
auto.
apply Znat.inj_lt.
apply pb.
apply Znat.inj_lt.
apply H6.
rewrite Znat.inj_plus in H4.
repeat rewrite Znat.inj_mult in H4.
symmetry  in |- *.
rewrite (Zplus_comm (Z_of_nat b)) in H4.
rewrite Zmult_assoc in H4.
rewrite Zplus_assoc in H4.
rewrite (Zmult_comm a1) in H4.
rewrite (Zmult_comm (Z_of_nat x2)) in H4.
rewrite <- Zmult_plus_distr_l in H4.
apply H4.
Qed.

Lemma chineseRemainderTheorem :
 forall x1 x2 : nat,
 CoPrime x1 x2 ->
 forall (a b : nat) (pa : a < x1) (pb : b < x2),
 {y : nat |
 y < x1 * x2 /\
 a = snd (proj1_sig (modulo x1 (ltgt1 _ _ pa) y)) /\
 b = snd (proj1_sig (modulo x2 (ltgt1 _ _ pb) y))}.
Proof.
intros.
induction (le_lt_dec a b).
apply chineseRemainderTheoremHelp.
assumption.
assumption.
assert (b <= a).
apply lt_le_weak.
assumption.
assert (CoPrime x2 x1).
apply coPrimeSym.
assumption.
induction (chineseRemainderTheoremHelp _ _ H1 b a pb pa H0).
induction p as (H2, H3).
induction H3 as (H3, H4).
exists x.
split.
rewrite mult_comm.
assumption.
split.
assumption.
assumption.
Qed.

Definition prod : forall (n : nat) (x : nat -> nat), nat.
intros.
induction n as [| n Hrecn].
exact 1.
exact (x n * Hrecn).
Defined.

Definition factorial (n : nat) : nat := prod n S.

Lemma coPrime1 : forall a : nat, CoPrime 1 a.
Proof.
intros.
split.
split.
exists 1.
auto.
exists (Zabs_nat (Z_of_nat a)).
rewrite mult_1_l.
reflexivity.
intros.
induction H as (H, H0).
apply div_le1.
apply H.
Qed.

Lemma coPrimeMult3 :
 forall a b c : nat,
 a > 0 -> b > 0 -> c > 0 -> CoPrime a c -> CoPrime b c -> CoPrime (a * b) c.
Proof.
intros.
assert (LinComb (Z_of_nat 1) (Z_of_nat a) (Z_of_nat c)).
apply gcd_lincomb_nat.
assumption.
apply H2.
assert (LinComb (Z_of_nat 1) (Z_of_nat b) (Z_of_nat c)).
apply gcd_lincomb_nat.
assumption.
apply H3.
induction H4 as (x, H4).
induction H4 as (x0, H4).
induction H5 as (x1, H5).
induction H5 as (x2, H5).
split.
split.
exists (Zabs_nat (Z_of_nat (a * b))).
rewrite mult_1_l.
reflexivity.
exists (Zabs_nat (Z_of_nat c)).
rewrite mult_1_l.
reflexivity.
intros.
induction H6 as (H6, H7).
set (A := Z_of_nat a) in *.
set (B := Z_of_nat b) in *.
set (C := Z_of_nat c) in *.
assert
 (1%Z = (A * B * (x * x1) + C * (x0 * B * x1 + x2 * A * x + x0 * x2 * C))%Z).
replace 1%Z with (Z_of_nat 1 * Z_of_nat 1)%Z.
rewrite (Zmult_comm C).
rewrite Zmult_plus_distr_l.
rewrite Zmult_plus_distr_l.
rewrite (Zplus_comm (x0 * B * x1 * C)).
rewrite Zmult_assoc_reverse.
rewrite (Zmult_assoc B).
rewrite (Zmult_comm B).
rewrite (Zmult_assoc_reverse x).
rewrite (Zmult_assoc A).
rewrite (Zmult_assoc_reverse x2).
rewrite (Zmult_comm x2).
rewrite (Zmult_assoc_reverse (A * x) x2).
repeat rewrite Zplus_assoc.
rewrite <- Zmult_plus_distr_r.
rewrite (Zmult_comm (x0 * B * x1)).
repeat rewrite (Zmult_assoc C).
rewrite (Zmult_assoc_reverse (C * x0)).
rewrite (Zmult_comm (x0 * x2)).
repeat rewrite (Zmult_assoc C).
rewrite (Zmult_assoc_reverse (C * x0)).
rewrite Zplus_assoc_reverse.
rewrite <- Zmult_plus_distr_r.
rewrite <- Zmult_plus_distr_l.
rewrite <- H4.
rewrite (Zmult_comm x2).
rewrite <- H5.
reflexivity.
auto.
assert (Divides e 1).
replace 1 with (Zabs_nat 1).
replace e with (Zabs_nat (Z_of_nat e)).
apply zdivdiv.
rewrite H8.
apply zdiv_plus_compat.
apply zdiv_mult_compat_l.
apply divzdiv.
unfold A, B in |- *.
rewrite <- Znat.inj_mult.
rewrite abs_inj.
assumption.
apply zdiv_mult_compat_l.
apply divzdiv.
rewrite abs_inj.
assumption.
apply abs_inj.
auto.
apply div_le.
apply lt_n_Sn.
assumption.
Qed.

Lemma multBig1 : forall a b : nat, a > 0 -> b > 0 -> a * b > 0.
Proof.
intros.
induction a as [| a Hreca].
unfold gt in H.
elim (lt_n_O _ H).
unfold gt in |- *.
apply lt_le_trans with (b * 1).
rewrite mult_1_r.
apply H0.
rewrite (mult_comm (S a)).
apply (fun m n p : nat => mult_le_compat_l p n m).
apply le_n_S.
apply le_O_n.
Qed.

Lemma prodBig1 :
 forall (n : nat) (x : nat -> nat),
 (forall z : nat, z < n -> x z > 0) -> prod n x > 0.
Proof.
intro.
induction n as [| n Hrecn].
intros.
simpl in |- *.
apply gt_Sn_n.
intros.
simpl in |- *.
apply multBig1.
apply H.
apply lt_n_Sn.
apply Hrecn.
intros.
apply H.
apply lt_S.
assumption.
Qed.

Lemma sameProd :
 forall (n : nat) (x1 x2 : nat -> nat),
 (forall z : nat, z < n -> x1 z = x2 z) -> prod n x1 = prod n x2.
Proof.
intro n.
induction n as [| n Hrecn].
intros.
auto.
intros.
simpl in |- *.
replace (x1 n) with (x2 n).
replace (prod n x1) with (prod n x2).
reflexivity.
apply Hrecn.
intros.
symmetry  in |- *.
apply H.
apply lt_S.
assumption.
symmetry  in |- *.
apply H.
apply lt_n_Sn.
Qed.

Lemma coPrimeProd :
 forall (n : nat) (x : nat -> nat),
 (forall z1 z2 : nat,
  z1 < S n -> z2 < S n -> z1 <> z2 -> CoPrime (x z1) (x z2)) ->
 (forall z : nat, z < S n -> x z > 0) -> CoPrime (prod n x) (x n).
Proof.
intro.
induction n as [| n Hrecn].
intros.
simpl in |- *.
apply coPrime1.
intros.
assert
 (forall z1 z2 : nat,
  z1 < S n -> z2 < S n -> z1 <> z2 -> CoPrime (x z1) (x z2)).
intros.
apply H.
apply lt_S.
assumption.
apply lt_S.
assumption.
assumption.
simpl in |- *.
apply coPrimeMult3.
apply H0.
apply lt_S.
apply lt_n_Sn.
apply prodBig1.
intros.
apply H0.
do 2 apply lt_S.
assumption.
apply H0.
apply lt_n_Sn.
apply H.
apply lt_S.
apply lt_n_Sn.
apply lt_n_Sn.
auto.
set
 (A1 :=
  fun a : nat =>
  match eq_nat_dec a n with
  | left _ => x (S n)
  | right _ => x a
  end) in *.
assert (CoPrime (prod n A1) (A1 n)).
apply Hrecn.
intros.
unfold A1 in |- *.
induction (eq_nat_dec z1 n).
induction (eq_nat_dec z2 n).
elim H4.
rewrite a0.
assumption.
apply H.
apply lt_n_Sn.
apply lt_S.
assumption.
unfold not in |- *; intros.
rewrite H5 in H3.
elim (lt_irrefl _ H3).
induction (eq_nat_dec z2 n).
apply H.
apply lt_S.
assumption.
apply lt_n_Sn.
unfold not in |- *; intros.
rewrite H5 in H2.
elim (lt_irrefl _ H2).
apply H.
apply lt_S.
assumption.
apply lt_S.
assumption.
assumption.
intros.
unfold A1 in |- *.
induction (eq_nat_dec z n).
apply H0.
apply lt_n_Sn.
apply H0.
apply lt_S.
assumption.
auto.
replace (x (S n)) with (A1 n).
replace (prod n x) with (prod n A1).
assumption.
apply sameProd.
intros.
unfold A1 in |- *.
induction (eq_nat_dec z n).
rewrite a in H3.
elim (lt_irrefl _ H3).
reflexivity.
unfold A1 in |- *.
induction (eq_nat_dec n n).
reflexivity.
elim b.
reflexivity.
Qed.

Lemma divProd :
 forall (n : nat) (x : nat -> nat) (i : nat),
 i < n -> Divides (x i) (prod n x).
Proof.
intro.
induction n as [| n Hrecn].
intros.
elim (lt_n_O _ H).
intros.
induction (le_lt_or_eq i n).
simpl in |- *.
rewrite mult_comm.
apply div_mult_compat_l.
apply Hrecn.
assumption.
simpl in |- *.
apply div_mult_compat_l.
rewrite H0.
apply div_refl.
apply lt_n_Sm_le.
assumption.
Qed.

Lemma chRem :
 forall (n : nat) (x : nat -> nat),
 (forall z1 z2 : nat, z1 < n -> z2 < n -> z1 <> z2 -> CoPrime (x z1) (x z2)) ->
 forall (y : nat -> nat) (py : forall z : nat, z < n -> y z < x z),
 {a : nat |
 a < prod n x /\
 (forall (z : nat) (pz : z < n),
  y z = snd (proj1_sig (modulo (x z) (ltgt1 _ _ (py z pz)) a)))}. 
Proof.
intro.
induction n as [| n Hrecn].
intros.
exists 0.
split.
simpl in |- *.
apply lt_O_Sn.
intros.
elim (lt_n_O _ pz).
intros.
assert
 (forall z1 z2 : nat, z1 < n -> z2 < n -> z1 <> z2 -> CoPrime (x z1) (x z2)).
intros.
apply H.
apply lt_S.
assumption.
apply lt_S.
assumption.
assumption.
assert (forall z : nat, z < n -> y z < x z).
intros.
apply py.
apply lt_S.
assumption.
induction (Hrecn x H0 y H1).
clear Hrecn.
induction p as (H2, H3).
assert (CoPrime (prod n x) (x n)).
apply coPrimeProd.
apply H.
intros.
eapply ltgt1.
apply py.
assumption.
assert (y n < x n).
apply py.
apply lt_n_Sn.
induction (chineseRemainderTheorem (prod n x) (x n) H4 x0 (y n) H2 H5).
exists x1.
induction p as (H6, H7).
induction H7 as (H7, H8).
split.
simpl in |- *.
rewrite mult_comm.
assumption.
intros.
induction (le_lt_or_eq z n).
assert
 (y z = snd (proj1_sig (modulo (x z) (ltgt1 (y z) (x z) (H1 z H9)) x0))).
apply H3.
induction (modulo (x z) (ltgt1 (y z) (x z) (H1 z H9)) x0).
simpl in H10.
induction (modulo (x z) (ltgt1 (y z) (x z) (py z pz)) x1).
simpl in |- *.
rewrite H10.
induction (modulo (prod n x) (ltgt1 x0 (prod n x) H2) x1).
simpl in H7.
rewrite H7 in p.
induction p1 as (H11, H12).
induction p as (H13, H14).
induction p0 as (H15, H16).
rewrite H13 in H11.
apply uniqueRem with (x z) x1.
apply (ltgt1 (y z) (x z) (py z pz)).
assert (Divides (x z) (prod n x)).
apply divProd.
assumption.
induction H17 as (x5, H17).
rewrite H17 in H11.
rewrite (mult_comm (x z)) in H11.
rewrite mult_assoc in H11.
rewrite plus_assoc in H11.
rewrite <- mult_plus_distr_r in H11.
exists (fst x4 * x5 + fst x2).
split.
apply H11.
assumption.
exists (fst x3).
auto.
induction (modulo (x z) (ltgt1 (y z) (x z) (py z pz)) x1).
induction (modulo (x n) (ltgt1 (y n) (x n) H5) x1).
simpl in H8.
simpl in |- *.
rewrite H9.
rewrite H8.
eapply uniqueRem.
apply (ltgt1 (y n) (x n) H5).
exists (fst x3).
apply p0.
exists (fst x2).
rewrite H9 in p.
assumption.
apply lt_n_Sm_le.
assumption.
Qed.

Lemma minusS : forall a b : nat, b - a = S b - S a.
Proof.
intros.
replace (S b) with (1 + b).
replace (S a) with (1 + a).
rewrite <- minus_plus_simpl_l_reverse.
reflexivity.
auto.
auto.
Qed.

Lemma primeDiv :
 forall a : nat, 1 < a -> exists p : nat, Prime p /\ Divides p a.
intro a.
apply (lt_wf_ind a).
clear a.
intros.
induction (primedec n).
exists n.
split.
assumption.
exists 1.
symmetry  in |- *.
apply mult_1_r.
induction (nonprime_witness _ H0 H1).
induction H2 as (H2, H3).
induction H3 as (H3, H4).
induction (H _ H3 H2).
exists x0.
induction H5 as (H5, H6).
split.
assumption.
eapply div_trans.
apply H6.
assumption.
Qed.

Lemma coPrimePrime :
 forall a b : nat,
 (forall p : nat, Prime p -> ~ Divides p a \/ ~ Divides p b) -> CoPrime a b.
Proof.
intros.
unfold CoPrime in |- *.
split.
split.
exists a.
rewrite mult_1_l.
apply abs_inj.
exists b.
rewrite mult_1_l.
apply abs_inj.
intros.
induction H0 as (H0, H1).
rewrite abs_inj in H0.
rewrite abs_inj in H1.
induction (le_or_lt e 1).
assumption.
induction (primeDiv _ H2).
induction H3 as (H3, H4).
induction (H _ H3).
elim H5.
eapply div_trans.
apply H4.
assumption.
elim H5.
eapply div_trans.
apply H4.
assumption.
Qed.

Lemma coPrimeSeqHelp :
 forall c i j n : nat,
 Divides (factorial n) c ->
 i < j -> i <= n -> j <= n -> CoPrime (S (c * S i)) (S (c * S j)).
Proof.
intros.
apply coPrimePrime.
intros.
induction (divdec (S (c * S i)) p).
assert (~ Divides p c).
unfold not in |- *.
intros.
assert (Divides p 1).
eapply div_plus_r.
apply div_mult_compat_l.
apply H5.
rewrite plus_comm.
simpl in |- *.
apply H4.
induction H3 as (H3, H7).
elim (lt_not_le _ _ H3).
apply div_le.
apply lt_n_Sn.
assumption.
induction (divdec (S (c * S j)) p).
assert (Divides p (c * (j - i))).
rewrite minusS.
rewrite mult_comm.
rewrite mult_minus_distr_r.
rewrite (mult_comm (S j)).
rewrite (mult_comm (S i)).
rewrite minusS.
apply div_minus_compat.
assumption.
assumption.
induction (primedivmult _ _ _ H3 H7).
elim H5.
assumption.
assert (j - i <= n).
eapply le_trans.
apply Minus.le_minus.
assumption.
elim H5.
apply div_trans with (factorial n).
apply div_trans with (j - i).
assumption.
unfold factorial in |- *.
assert (1 <= j - i).
assert (j = i + (j - i)).
apply le_plus_minus.
apply lt_le_weak.
assumption.
rewrite H10 in H0.
apply lt_n_Sm_le.
apply lt_n_S.
apply plus_lt_reg_l with i.
rewrite plus_comm.
apply H0.
replace (j - i) with (S (pred (j - i))).
apply divProd.
rewrite pred_of_minus.
apply lt_S_n.
apply le_lt_n_Sm.
replace (S (j - i - 1)) with (1 + (j - i - 1)).
rewrite <- le_plus_minus.
assumption.
assumption.
auto.
induction (j - i).
elim (le_Sn_n _ H10).
rewrite <- pred_Sn.
reflexivity.
assumption.
auto.
auto.
Qed.

Definition coPrimeBeta (z c : nat) : nat := S (c * S z).

Lemma coPrimeSeq :
 forall c i j n : nat,
 Divides (factorial n) c ->
 i <> j -> i <= n -> j <= n -> CoPrime (coPrimeBeta i c) (coPrimeBeta j c).
Proof.
unfold coPrimeBeta in |- *.
intros.
induction (nat_total_order _ _ H0).
eapply coPrimeSeqHelp.
apply H.
assumption.
assumption.
assumption.
apply coPrimeSym.
eapply coPrimeSeqHelp.
apply H.
assumption.
assumption.
assumption.
Qed.

Lemma gtBeta : forall z c : nat, coPrimeBeta z c > 0.
Proof.
unfold coPrimeBeta in |- *.
intros.
apply gt_Sn_O.
Qed.

Definition maxBeta (n : nat) (x : nat -> nat) : nat.
intros.
induction n as [| n Hrecn].
exact 0.
exact (max (x n) Hrecn).
Defined.

Lemma maxBetaLe :
 forall (n : nat) (x : nat -> nat) (i : nat), i < n -> x i <= maxBeta n x.
Proof.
simple induction n.
intros.
elim (lt_n_O _ H).
intros.
simpl in |- *.
induction (le_lt_or_eq i n0).
eapply le_trans.
apply H.
assumption.
apply le_max_r.
rewrite H1.
apply le_max_l.
apply lt_n_Sm_le.
assumption.
Qed.

Theorem divProd2 :
 forall (n : nat) (x : nat -> nat) (i : nat),
 i <= n -> Divides (prod i x) (prod n x).
Proof.
simple induction n.
intros.
assert (0 = i).
apply le_n_O_eq.
assumption.
rewrite H0.
apply div_refl.
intros.
induction (le_lt_or_eq i (S n0)).
simpl in |- *.
rewrite mult_comm.
apply div_mult_compat_l.
apply H.
apply lt_n_Sm_le.
assumption.
rewrite H1.
apply div_refl.
assumption.
Qed.

Theorem betaTheorem1 :
 forall (n : nat) (y : nat -> nat),
 {a : nat * nat |
 forall z : nat,
 z < n ->
 y z =
 snd (proj1_sig (modulo (coPrimeBeta z (snd a)) (gtBeta z (snd a)) (fst a)))}.
Proof.
intros.
set (c := factorial (max n (maxBeta n y))) in *.
set (x := fun z : nat => coPrimeBeta z c) in *.
assert
 (forall z1 z2 : nat, z1 < n -> z2 < n -> z1 <> z2 -> CoPrime (x z1) (x z2)).
intros.
unfold x in |- *.
eapply coPrimeSeq.
eapply div_trans.
unfold factorial in |- *.
apply divProd2.
apply le_max_l.
unfold c, factorial in |- *.
apply div_refl.
assumption.
apply lt_le_weak.
assumption.
apply lt_le_weak.
assumption.
assert (forall z : nat, z < n -> y z < x z).
intros.
unfold x, coPrimeBeta in |- *.
apply le_lt_n_Sm.
induction (mult_O_le c (S z)).
discriminate H1.
apply le_trans with c.
unfold c in |- *.
apply le_trans with (max n (maxBeta n y)).
apply le_trans with (maxBeta n y).
apply maxBetaLe.
assumption.
apply le_max_r.
generalize (max n (maxBeta n y)).
intros.
induction n0 as [| n0 Hrecn0].
simpl in |- *.
apply le_n_Sn.
induction n0 as [| n0 Hrecn1].
simpl in |- *.
apply le_n.
assert (factorial n0 > 0).
unfold factorial in |- *.
apply prodBig1.
intros.
apply gt_Sn_O.
simpl in |- *.
eapply le_trans with (1 + (1 + n0 * (factorial n0 + n0 * factorial n0))).
simpl in |- *.
repeat apply le_n_S.
induction (mult_O_le n0 (factorial n0 + n0 * factorial n0)).
unfold gt in H2.
assert (factorial n0 = factorial n0 + 0).
rewrite plus_comm.
auto.
assert (0 < factorial n0).
assumption.
rewrite H4 in H2.
set (A1 := factorial n0 + 0) in *.
rewrite <- H3 in H2.
unfold A1 in H2.
clear H4 A1.
assert (n0 * factorial n0 < 0).
eapply plus_lt_reg_l.
apply H2.
elim (lt_n_O _ H4).
rewrite mult_comm.
assumption.
apply plus_le_compat.
apply le_plus_trans.
apply lt_n_Sm_le.
apply lt_n_S.
assumption.
apply plus_le_compat.
apply le_plus_trans.
apply lt_n_Sm_le.
apply lt_n_S.
assumption.
apply le_n.
rewrite mult_comm.
assumption.
induction (chRem _ _ H _ H0).
exists (x0, c).
intros.
induction p as (H2, H3).
rewrite (H3 z H1).
induction (modulo (x z) (ltgt1 (y z) (x z) (H0 z H1)) x0).
replace (snd (x0, c)) with c.
replace (fst (x0, c)) with x0.
induction (modulo (coPrimeBeta z c) (gtBeta z c) x0).
simpl in |- *.
eapply uniqueRem.
apply gtBeta.
unfold x in p.
exists (fst x1).
apply p.
exists (fst x2).
apply p0.
auto.
auto.
Qed.
