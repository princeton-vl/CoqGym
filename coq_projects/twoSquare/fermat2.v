From mathcomp Require Import all_ssreflect all_algebra all_field.
Require Import gauss_int.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory UnityRootTheory.

Open Scope nat_scope.

Definition sum_of_two_square := 
  [qualify a x |
       [exists a : 'I_x.+1, exists b : 'I_x.+1, x == a ^ 2 + b ^ 2]].

Lemma sum2sP x :
  reflect (exists m, exists n, x = m ^ 2 + n ^ 2) 
          (x \is a sum_of_two_square).
Proof.
apply: (iffP existsP) => [[m /existsP[n /eqP->]]|[m [n ->]]].
  by exists m; exists n.
have F1 : m <  (m ^ 2 + n ^ 2).+1.
  rewrite ltnS (leq_trans _ (leq_addr _ _)) //.
  by case: m => [|[|m]] //; rewrite (leq_exp2l 1).
have F2 : n <  (m ^ 2 + n ^ 2).+1.
  rewrite ltnS (leq_trans _ (leq_addl _ _)) //.
  by case: (n) => [|[|n1]] //; rewrite (leq_exp2l 1).
by exists (Ordinal F1); apply/existsP; exists (Ordinal F2).
Qed.

Fact sum2s0 : 0 \is a sum_of_two_square.
Proof. by apply/sum2sP; exists 0; exists 0. Qed.

Fact sum2s1 : 1 \is a sum_of_two_square.
Proof. by apply/sum2sP; exists 0; exists 1. Qed.

Fact sum2s2 : 2 \is a sum_of_two_square.
Proof. by apply/sum2sP; exists 1; exists 1. Qed.

Fact sum2sX_even x n :
 ~~ odd n  -> x ^ n \is  a sum_of_two_square.
Proof.
move=> En; apply/sum2sP; exists (x ^ n./2); exists 0.
by rewrite addn0 -{1}[n]odd_double_half (negPf En) -expnM muln2.
Qed.

Lemma sum2sGP x :
  reflect (exists m : GI, x = normGI m)
          (x \is a sum_of_two_square).
Proof.
apply: (iffP idP) => [/sum2sP[m [n ->]]|[x1->]].
exists (m%:R + iGI * n%:R)%R.
  by rewrite normGIE /= !algGI_nat Re_rect ?Im_rect 
             ?CrealE ?conjC_nat ?natCK // !normr_nat !natCK.
rewrite normGIE; set m := truncC _; set n := truncC _.
by apply/sum2sP; exists m; exists n.
Qed.

Lemma sum2sM x y :
  x \is  a sum_of_two_square ->
  y \is  a sum_of_two_square ->
  x * y \is  a sum_of_two_square.
Proof.
move=> /sum2sGP[x1->] /sum2sGP[y1->]; rewrite -normGIM.
by apply/sum2sGP; exists (x1 * y1)%R.
Qed.

Lemma sum2s_dvd_prime p a b :
  prime p -> coprime a b -> 
  p %| a ^ 2 + b ^ 2 -> p \is  a sum_of_two_square.
Proof.
move=> Pp Cab pDab.
have /dvdGI_norm := pdivGI_dvd (p%:R); set x := pdivGI _.
have Px : primeGI x.
  apply: pdivGI_prime; rewrite normGI_nat.
  by rewrite -{1}(expn0 p) ltn_exp2l // prime_gt1.
rewrite (normGI_nat p)=> /(dvdn_pfactor _ _ Pp)=> [[[|[|[]]]]] _ //.
- by move=> H; case/andP: Px; rewrite H ltnn.
- by rewrite expn1=> H; apply/sum2sGP; exists x.
rewrite -normGI_nat => H1.
have PGIp : primeGI (p%:R).
 apply: eqGI_prime Px.
 by apply: dvdGI_eq_norm (pdivGI_dvd _).
pose z := (a%:R + iGI * b%:R)%R.
have F : ('N z)%GI = a ^ 2 + b ^ 2.
  by rewrite normGIE /= !algGI_nat !(Re_rect, Im_rect)
            ?Creal_Cnat // !normr_nat !natCK.
have F1 : (p%:R %| z * conjGI z)%GI%R.
  rewrite conjGIM_norm F.
  case/dvdnP: pDab => q1 ->.
  by apply/dvdGIP; exists (q1%:R); rewrite natrM.
have []: ~ (p %| gcdn a b).
  by rewrite (eqP Cab) Euclid_dvd1.
rewrite dvdn_gcd.
have [F2|] := boolP (p%:R %| z)%GI.
  have := dvdGI_nat_dvdz_Re F2.
  rewrite Re_rect /= algGI_nat ?Creal_Cnat //=
           (intCK (Posz a)) /= => ->.
  have := dvdGI_nat_dvdz_Im F2.
  by rewrite Im_rect /= algGI_nat ?Creal_Cnat //=
           (intCK (Posz b)).
rewrite -primeGI_coprime // => HH.
have F2 : (p%:R %| conjGI z)%GI.
  by rewrite -(Gauss_dvdGIr _ HH).
have := dvdGI_nat_dvdz_Re F2.
rewrite Re_conj Re_rect /= algGI_nat ?Creal_Cnat //=
           (intCK (Posz a)) => ->.
have := dvdGI_nat_dvdz_Im F2.
rewrite Im_conj Im_rect /= algGI_nat ?Creal_Cnat //=.
by rewrite floorCN ?Cint_Cnat // abszN (intCK (Posz b)).
Qed.

Lemma sum2sX x n :
  x \is  a sum_of_two_square  -> x ^ n \is  a sum_of_two_square.
Proof.
move=>/sum2sGP[x1->]; rewrite -normGIX.
by apply/sum2sGP; exists (x1 ^+ n)%R.
Qed.

Lemma sum2sX_prime x n :
  prime x -> odd n ->
  x ^ n \is  a sum_of_two_square -> x  \is  a sum_of_two_square.
Proof.
move=> Px On /sum2sP[a [b adE]].
pose u := gcdn a b.
have /(dvdn_pfactor _ _ Px)[m] : u ^ 2 %| x ^ n.
  by rewrite adE dvdn_add // dvdn_exp2r ?(dvdn_gcdr, dvdn_gcdl).
rewrite leq_eqVlt => /orP[/eqP->|nLM] uE.
  move: On; have := congr1 (logn x) uE.
  rewrite (pfactorK _ Px) lognX => <-.
  by rewrite mul2n odd_double.
have /(sum2s_dvd_prime _ _)->//: x %| (a %/ u) ^ 2 + (b %/ u) ^ 2.
  apply/dvdnP; exists (x^(n-m).-1); apply/eqP.
    rewrite -expnSr prednK ?subn_gt0 //.
    have/eqn_pmul2r<- : (0 < x ^ m) by rewrite expn_gt0 prime_gt0.
    by rewrite -{1}uE mulnDl -!expnMn -expnD subnK 1?ltnW //
            !divnK ?(adE, dvdn_gcdr, dvdn_gcdl).
rewrite /coprime.
have/eqn_pmul2r<- : (0 < u).
  have: (0 < u ^ 2) by rewrite uE expn_gt0 prime_gt0.
  by case: (u).
by rewrite muln_gcdl mul1n !divnK ?(adE, dvdn_gcdr, dvdn_gcdl).
Qed.

Lemma sum2sM_coprime x y :
  coprime x y ->
  x * y \is  a sum_of_two_square ->  x \is  a sum_of_two_square.
Proof.
move=> Cxy /sum2sGP[z Hz].
pose t := gcdGI (x%:R) z.
apply/sum2sGP; exists t.
apply: eqGI_nat.
rewrite -conjGIM_norm.
apply: eqGI_trans (_ : eqGI (t * gcdGI (x%:R) (conjGI z))%R _).
  apply: gcdGI_mull_equiv (coprimeGI_nat Cxy) _.
  by rewrite -natrM Hz conjGIM_norm.
apply: eqGI_mul (eqGIxx _) _.
by rewrite -conjGI_nat eqGI_sym conjGI_gcd.
Qed.

Lemma modn_prod I r (P : pred I) F d :
  \prod_(i <- r | P i) (F i %% d) = \prod_(i <- r | P i) F i %[mod d].
Proof.
apply/eqP; elim/big_rec2: _ => // i m n _.
by rewrite modnMml -modnMmr => /eqP->; rewrite modnMmr.
Qed.

Lemma sum2sprime p : 
  odd p -> prime p -> p \is a sum_of_two_square = (p %% 4 == 1).
Proof.
move=> Op Pp; apply/idP/idP=>[/sum2sP[a [b H]]|pM4].
  have F c : (c ^ 2 %% 4 == 0) || (c ^ 2 %% 4 == 1).
    rewrite -modnXm expnS expn1.
    by move: (c %% 4) (ltn_pmod c (isT: 0 < 4)); do 4 case => //.
  have : (p %% 4 == 1) || (p %% 4 == 3).
    rewrite -[p]odd_double_half Op -modnDmr -muln2.
    have /(_ _ 2)<- := muln_modl (isT: 0 < 2).
    by move: (_ %% 2) (ltn_pmod p./2 (isT: 0 < 2)); do 2 case => //.
  rewrite H -modnDm.
  by move: (F a) (F b) => /orP[] /eqP-> /orP[] /eqP->.
pose k := p %/ 4.
have p_gt0 := prime_gt0 Pp.
have p_gt1 := prime_gt1 Pp.
have : (p.-1)`!.+1 %% p == 0 by rewrite -[_ == 0]Wilson.
have : \prod_(1 <= i < (k * 2).+1) (p - 1) = 1 %[mod p].
  rewrite prod_nat_const_nat !subn1 /= mulnC expnM.
  rewrite -modnXm expnS expn1.
  rewrite -[_ * _ %% _]modnDr -{3}[p]prednK -addn1 //.
  by rewrite addnA -mulnSr prednK // modnMDl modnXm exp1n.
have pE : p = (k * 4).+1 by rewrite (divn_eq p 4) (eqP pM4) addn1.
rewrite pE => F.
have [/eqP-> _|] := boolP (k == 0); first exact: sum2s1.
rewrite -leqn0 -ltnNge => Pk.
rewrite fact_prod (big_cat_nat _ _ _ (_ : 1 <= (k * 2).+1)) //=; last first.
  by rewrite ltnS leq_mul2l orbT.
set S1 := \prod_(_ <= _ < _ ) _.
rewrite -addn1 -modnDml -modnMmr big_nat_rev /=.
rewrite -[(k * 2).+1]add1n big_addn.
rewrite subSn ?leq_pmul2l // -mulnBr /=.
set S2 := \prod_(_ <= _ < _ ) _.
rewrite -[S2]muln1 -[S2 * 1 %% _]modnMmr -{}F.
rewrite [S2 * _ %% _]modnMmr.
rewrite -[S2 * _]big_split /=.
set S3 := \prod_(_ <= _ < _ ) _.
suff ->: S3 = S1 %[mod (k * 4).+1].
  rewrite modnMmr modnDml -{1}[S1]expn1 -expnSr -[S1]fact_prod.
  rewrite -pE -{3}[1](exp1n 2) => /sum2s_dvd_prime-> //.
  by rewrite coprimen1.
rewrite -modn_prod -[in RHS]modn_prod.
rewrite big_nat_cond [in RHS]big_nat_cond.
congr (_ %% _).
apply: eq_bigr => i /andP[/andP[H1 H2] _].
rewrite add1n addnC -addnS [i + _]addnC subnDA addnK.
have H3 : i <= (k * 4).+1.
  by rewrite ltnW // (leq_trans H2) // ltnS leq_pmul2l.
rewrite -modnDr -{3}(subnK H3) addnA -mulnSr subn1 prednK //.
by rewrite modnMDl.
Qed.

(** Main theorem **)
Lemma sum2stest n :
  reflect
  (forall p,  prime p -> odd p -> p %| n -> odd (logn p n) -> p %% 4 = 1)
  (n \is a sum_of_two_square).
Proof.
apply: (iffP idP) => [Hs p Pp Op Dp OL|HH].
  have Pn : 0 < n by case: (n) OL; rewrite ?logn0.
  have /(pfactor_coprime Pp)[m Cmp mE] := (Pn).
  apply/eqP; rewrite -sum2sprime //.
  apply:  sum2sX_prime OL _ => //.
  rewrite mE mulnC in Hs.
  by apply: sum2sM_coprime Hs; rewrite coprime_pexpl // -pfactor_dvdn.
have [/eqP->|] := boolP (n == 0); first by apply:sum2s0.
rewrite -leqn0 -ltnNge => /prod_prime_decomp->.
rewrite big_seq_cond /=.
elim/big_rec: _ => [|i x /andP[]].
exact: sum2s1.
rewrite prime_decompE => /mapP[p].
rewrite mem_primes => /and3P[Pp Pn pDn] -> _ xS /=.
apply: sum2sM => //.
have [OL|] := boolP (odd (logn p n)); last by exact: sum2sX_even.
apply: sum2sX.
have [Op|/prime_oddPn->//] := boolP (odd p); last by exact: sum2s2.
by rewrite sum2sprime // HH.
Qed.
