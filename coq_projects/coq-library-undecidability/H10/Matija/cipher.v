(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** Sparse ciphers *)

Require Import Arith Nat Omega List Bool Setoid.
Require Import utils_tac gcd sums rel_iter bool_nat power_decomp.

Set Implicit Arguments.

Local Notation power := (mscal mult 1).
Local Notation "∑" := (msum plus 0).
Local Infix "≲" := binary_le (at level 70, no associativity).
Local Infix "⇣" := nat_meet (at level 40, left associativity).
Local Infix "⇡" := nat_join (at level 50, left associativity).

Hint Resolve power2_gt_0.

Section stability_of_power.

  Fact mult_lt_power_2 u v k : u < power k 2 -> v < power k 2 -> u*v < power (2*k) 2.
  Proof.
    intros H1 H2.
    replace (2*k) with (k+k) by omega.
    rewrite power_plus.
    apply lt_le_trans with ((S u)*S v).
    simpl; rewrite (mult_comm _ (S _)); simpl; rewrite mult_comm; omega.
    apply mult_le_compat; auto.
  Qed.

  Fact mult_lt_power_2_4 u v k : u < power k 2 -> v < power k 2 -> u*v < power (4*k) 2.
  Proof.
    intros H1 H2.
    apply lt_le_trans with (1 := mult_lt_power_2 _ H1 H2).
    apply power_mono_l; omega.
  Qed.

  Fact mult_lt_power_2_4' u1 v1 u2 v2 k : 
               u1 < power k 2 
            -> v1 < power k 2
            -> u2 < power k 2
            -> v2 < power k 2
            -> u1*v1+v2*u2 < power (4*k) 2.
  Proof.
    intros H1 H2 H3 H4.
    destruct (eq_nat_dec k 0) as [ ? | Hk ].
    - subst k; simpl.
      rewrite power_0 in *.
      destruct u1; destruct v1; destruct u2; destruct v2; subst; omega.
    - apply lt_le_trans with (power (S (2*k)) 2). 
      + rewrite power_S, <- mult_2_eq_plus.
        apply plus_lt_compat; apply mult_lt_power_2; auto.
      + apply power_mono_l; omega.
  Qed.

End stability_of_power.

Section power_decomp.

  Variable (p : nat) (Hp : 2 <= p).

  Let power_nzero x : power x p <> 0.
  Proof. generalize (@power_ge_1 x p); omega. Qed.

  Fact power_decomp_lt n f a q :  
           (forall i j, i < j < n -> f i < f j)
        -> (forall i, i < n -> f i < q)
        -> (forall i, i < n -> a i < p)
        -> ∑ n (fun i => a i * power (f i) p) < power q p.
  Proof.
    revert q; induction n as [ | n IHn ]; intros q Hf1 Hf2 Ha.
    + rewrite msum_0; apply power_ge_1; omega.
    + rewrite msum_plus1; auto.
      apply lt_le_trans with (1*power (f n) p + a n * power (f n) p).
      * apply plus_lt_le_compat; auto.
        rewrite Nat.mul_1_l.
        apply IHn.
        - intros; apply Hf1; omega.
        - intros; apply Hf1; omega.
        - intros; apply Ha; omega.
      * rewrite <- Nat.mul_add_distr_r.
        replace q with (S (q-1)).
        - rewrite power_S; apply mult_le_compat; auto.
          ++ apply Ha; auto.
          ++ apply power_mono_l; try omega.
             generalize (Hf2 n); intros; omega.
        - generalize (Hf2 0); intros; omega.
  Qed.

  Lemma power_decomp_is_digit n a f : 
           (forall i j, i < j < n -> f i < f j)
        -> (forall i, i < n -> a i < p)
        ->  forall i, i < n -> is_digit (∑ n (fun i => a i * power (f i) p)) p (f i) (a i).
  Proof.
    intros Hf Ha.
    induction n as [ | n IHn ]; intros i Hi.
    + omega.
    + split; auto.
      exists (∑ (n-i) (fun j => a (S i + j) * power (f (S i+j) - f i - 1) p)), 
             (∑ i (fun j => a j * power (f j) p)); split.
      - replace (S n) with (S i + (n-i)) by omega.
        rewrite msum_plus, msum_plus1; auto.
        rewrite <- plus_assoc, plus_comm; f_equal.
        rewrite Nat.mul_add_distr_r, plus_comm; f_equal.
        rewrite <- mult_assoc, mult_comm, <- sum_0n_scal_l.
        apply msum_ext.
        intros j Hj.
        rewrite (mult_comm (_ * _));
        repeat rewrite <- mult_assoc; f_equal.
        rewrite <- power_S, <- power_plus; f_equal.
        generalize (Hf i (S i+j)); intros; omega.
      - apply power_decomp_lt; auto.
        * intros; apply Hf; omega.
        * intros; apply Ha; omega.
  Qed.

  Theorem power_decomp_unique n f a b :
            (forall i j, i < j < n -> f i < f j)
         -> (forall i, i < n -> a i < p)
         -> (forall i, i < n -> b i < p)
         -> ∑ n (fun i => a i * power (f i) p)
          = ∑ n (fun i => b i * power (f i) p)
         -> forall i, i < n -> a i = b i.
  Proof.
    intros Hf Ha Hb E i Hi.
    generalize (power_decomp_is_digit _ _ Hf Ha Hi)
               (power_decomp_is_digit _ _ Hf Hb Hi).
    rewrite E; apply is_digit_fun.
  Qed.

End power_decomp.

Section power_decomp_uniq.

  Variable (p : nat) (Hp : 2 <= p).

  Theorem power_decomp_factor n f a : 
           (forall i, 0 < i < S n -> f 0 < f i)
        -> ∑ (S n) (fun i => a i * power (f i) p) 
         = ∑ n (fun i => a (S i) * power (f (S i) - f 0 - 1) p) * power (S (f 0)) p
         + a 0 * power (f 0) p.
  Proof.
    intros Hf.
    rewrite msum_S, plus_comm; f_equal.
    rewrite <- sum_0n_scal_r.
    apply msum_ext.
    intros i Hi.
    rewrite <- mult_assoc; f_equal.
    rewrite <- power_plus; f_equal.
    generalize (Hf (S i)); intros; omega.
  Qed.

  Let power_nzero x : power x p <> 0.
  Proof.
    generalize (@power_ge_1 x p); omega.
  Qed.

  Let lt_minus_cancel a b c : a < b < c -> b - a - 1 < c - a - 1.
  Proof. intros; omega. Qed. 

  (* Another proof of the above statement *)

  Theorem power_decomp_unique' n f a b :
            (forall i j, i < j < n -> f i < f j)
         -> (forall i, i < n -> a i < p)
         -> (forall i, i < n -> b i < p)
         -> ∑ n (fun i => a i * power (f i) p)
          = ∑ n (fun i => b i * power (f i) p)
         -> forall i, i < n -> a i = b i.
  Proof.
    revert f a b.
    induction n as [ | n IHn ]; intros f a b Hf Ha Hb.
    + intros; omega.
    + assert (forall i, 0 < i < S n -> f 0 < f i)
        by (intros; apply Hf; omega). 
      do 2 (rewrite power_decomp_factor; auto).
      intros E.
      apply div_rem_uniq in E; auto.
      * destruct E as (E1 & E2).
        intros [ | i ] Hi.
        - revert E2; rewrite Nat.mul_cancel_r; auto.
        - apply IHn with (4 := E1); try omega.
          ++ intros u j Hu; apply lt_minus_cancel; split; apply Hf; omega. 
          ++ intros; apply Ha; omega.
          ++ intros; apply Hb; omega.
      * rewrite power_S.
        apply Nat.mul_lt_mono_pos_r.
        - apply power_ge_1; omega.
        - apply Ha; omega.
      * rewrite power_S.
        apply Nat.mul_lt_mono_pos_r.
        - apply power_ge_1; omega.
        - apply Hb; omega.
  Qed.

End power_decomp_uniq.

Fact mult_2_eq_plus x : x + x = 2 *x.
Proof. ring. Qed.

Section power_injective.

  Let power_2_inj_1 i j n : j < i -> 2* power n 2 <> power i 2 + power j 2.
  Proof.
    rewrite <- power_S; intros H4 E.
     generalize (@power_ge_1 j 2); intro C.
     destruct (lt_eq_lt_dec i (S n)) as [ [ H5 | H5 ] | H5 ].
     + apply power_mono_l with (x := 2) in H5; auto.
       rewrite power_S in H5.
       apply power_mono_l with (x := 2) in H4; auto.
       rewrite power_S in H4; omega.
     + subst i; omega.
     + apply power_mono_l with (x := 2) in H5; auto.
      rewrite power_S in H5; omega.
  Qed.

  Fact power_2_n_ij_neq i j n : i <> j -> power (S n) 2 <> power i 2 + power j 2.
  Proof.
    intros H.
    destruct (lt_eq_lt_dec i j) as [ [] | ]; try tauto.
    + rewrite plus_comm; apply power_2_inj_1; auto.
    + apply power_2_inj_1; auto.
  Qed.

  Fact power_2_inj i j : power i 2 = power j 2 -> i = j.
  Proof.
    intros H.
    destruct (lt_eq_lt_dec i j) as [ [ C | C ] | C ]; auto;
      apply power_smono_l with (x := 2) in C; omega.
  Qed.

  Let power_plus_lt a b c : a < b < c -> power a 2 + power b 2 < power c 2.
  Proof.
    intros [ H1 H2 ].
    apply power_mono_l with (x := 2) in H2; auto.
    apply power_smono_l with (x := 2) in H1; auto.
    rewrite power_S in H2; omega.
  Qed.

  Let power_inj_2 i1 j1 i2 j2 : 
             j1 < i1 
          -> j2 < i2 
          -> power i1 2 + power j1 2 = power i2 2 + power j2 2
          -> i1 = i2 /\ j1 = j2.
  Proof.
    intros H1 H2 H3.
    destruct (lt_eq_lt_dec i1 i2) as [ [ C | C ] | C ].
    + generalize (@power_plus_lt j1 i1 i2); intros; omega.
    + split; auto; apply power_2_inj; subst; omega.
    + generalize (@power_plus_lt j2 i2 i1); intros; omega.
  Qed.

  Theorem sum_2_power_2_injective i1 j1 i2 j2 :
              j1 <= i1 
           -> j2 <= i2 
           -> power i1 2 + power j1 2 = power i2 2 + power j2 2 
           -> i1 = i2 /\ j1 = j2.
  Proof.
    intros H1 H2 E.
    destruct (eq_nat_dec i1 j1) as [ H3 | H3 ];
    destruct (eq_nat_dec i2 j2) as [ H4 | H4 ].
    + subst j1 j2.
      assert (i1 = i2); auto.
      do 2 rewrite mult_2_eq_plus, <- power_S in E.
      apply power_2_inj in E; omega.
    + subst j1; rewrite mult_2_eq_plus in E.
      apply power_2_inj_1 in E; omega.
    + subst j2; symmetry in E.
      rewrite mult_2_eq_plus in E.
      apply power_2_inj_1 in E; omega.
    + revert E; apply power_inj_2; omega.
  Qed. 
 
End power_injective.

Fact divides_power p a b : a <= b -> divides (power a p) (power b p).
Proof.
  (* split. *)
  * induction 1 as [ | b H IH ].
    + apply divides_refl.
    + apply divides_trans with (1 := IH).
      rewrite power_S; apply divides_mult, divides_refl.
(*  * intros H.
    apply divides_le in H. *)
Qed.

Fact divides_msum k n f : (forall i, i < n -> divides k (f i)) -> divides k (∑ n f).
Proof.
  revert f; induction n as [ | n IHn ]; intros f Hf.
  + rewrite msum_0; apply divides_0.
  + rewrite msum_S; apply divides_plus.
    * apply Hf; omega.
    * apply IHn; intros; apply Hf; omega.
Qed.

Fact inc_seq_split_lt n f k : 
         (forall i j, i < j < n -> f i < f j) 
      -> { p | p <= n /\ (forall i, i < p -> f i < k) /\ forall i, p <= i < n -> k <= f i }.
Proof.
  revert f; induction n as [ | n IHn ]; intros f Hf.
  + exists 0; split; auto; split; intros; omega.
  + destruct (le_lt_dec k (f 0)) as [ H | H ].
    - exists 0; split; try omega.
      split; intros i Hi; try omega.
      destruct i as [ | i ]; auto.
      apply le_trans with (1 := H), lt_le_weak, Hf; omega.
    - destruct (IHn (fun i => f (S i))) as (p & H1 & H2 & H3).
      * intros; apply Hf; omega.
      * exists (S p); split; try omega; split.
        ++ intros [ | i ] Hi; auto; apply H2; omega.
        ++ intros [ | i ] Hi; try omega; apply H3; omega.
Qed.

Fact inc_seq_split_le n f h : (forall i j, i < j < n -> f i < f j) 
                   -> { q | q <= n 
                         /\ (forall i, i < q      -> f i <= h)
                         /\ (forall i, q <= i < n -> h < f i) }.
Proof.
  intros Hf.
  destruct inc_seq_split_lt with (1 := Hf) (k := S h)
    as (q & H1 & H2 & H3); exists q; split; auto; split.
  + intros i Hi; specialize (H2 _ Hi); omega.
  + intros i Hi; specialize (H3 _ Hi); omega.
Qed.

Fact divides_lt p q : q < p -> divides p q -> q = 0.
Proof.
  intros H1 ([ | k] & H2); auto.
  revert H2; simpl; generalize (k *p); intros; omega.
Qed.

Fact sum_powers_inc_lt_last n f r : 
        2 <= r
     -> (forall i j, i < j <= n -> f i < f j)
     -> ∑ (S n) (fun i => power (f i) r) < power (S (f n)) r.
Proof.
  intros Hr.
  revert f.
  induction n as [ | n IHn ]; intros f Hf.
  + rewrite msum_1; auto; apply power_smono_l; auto.
  + rewrite msum_plus1; auto.
    rewrite power_S.
    apply lt_le_trans with (power (S (f n)) r + power (f (S n)) r).
    * apply plus_lt_compat_r; auto.
      apply IHn; intros; apply Hf; omega.
    * assert (power (S (f n)) r <= power (f (S n)) r) as H.
      { apply power_mono_l; try omega; apply Hf; omega. }
      apply le_trans with (2 * power (f (S n)) r); try omega.
      apply mult_le_compat; auto.
Qed.

Fact sum_powers_inc_lt n f p r : 
        2 <= r
     -> (forall i, i < n -> f i < p)
     -> (forall i j, i < j < n -> f i < f j)
     -> ∑ n (fun i => power (f i) r) < power p r.
Proof.
  destruct n as [ | n ].
  + intros H _ _; rewrite msum_0; apply power_ge_1; omega.
  + intros H1 H2 H3.
    apply lt_le_trans with (power (S (f n)) r).
    * apply sum_powers_inc_lt_last; auto.
      intros; apply H3; omega.
    * apply power_mono_l; try omega.
      apply H2; auto.
Qed.

(* the value r^f1 + ... + f^fn uniquely determines n and f1 < ... < fn  *)

Fact sum_powers_injective r n f m g :
       2 <= r
    -> (forall i j, i < j < n -> f i < f j)
    -> (forall i j, i < j < m -> g i < g j)
    -> ∑ n (fun i => power (f i) r) = ∑ m (fun i => power (g i) r)
    -> n = m /\ forall i, i < n -> f i = g i.
Proof.
  intros Hr; revert m f g.
  induction n as [ | n IHn ]; intros m f g Hf Hg.
  + rewrite msum_0.
    destruct m as [ | m ].
    * rewrite msum_0; split; auto; intros; omega.
    * rewrite msum_S.
      generalize (@power_ge_1 (g 0) r); intros; exfalso; omega.
  + destruct m as [ | m ].
    * rewrite msum_0, msum_S; intros; exfalso.
       generalize (@power_ge_1 (f 0) r); intros; exfalso; omega.
    * destruct (lt_eq_lt_dec (f n) (g m)) as [ [E|E]| E].
      - rewrite msum_plus1 with (n := m); auto. 
        intros; exfalso.
        assert (∑ (S n) (fun i => power (f i) r) < power (g m) r) as C; try omega.
        apply sum_powers_inc_lt; auto.
        intros i Hi.
        destruct (eq_nat_dec i n); subst; auto.
        apply lt_trans with (2 := E), Hf; omega.
      - do 2 (rewrite msum_plus1; auto); intros C.
        destruct (IHn m f g) as (H1 & H2).
        ++ intros; apply Hf; omega.
        ++ intros; apply Hg; omega.
        ++ rewrite E in C; omega.
        ++ split; subst; auto.
           intros i Hi.
           destruct (eq_nat_dec i m); subst; auto.
           apply H2; omega.
      - rewrite msum_plus1 with (n := n); auto. 
        intros; exfalso.
        assert (∑ (S m) (fun i => power (g i) r) < power (f n) r) as C; try omega.
        apply sum_powers_inc_lt; auto.
        intros i Hi.
        destruct (eq_nat_dec i m); subst; auto.
        apply lt_trans with (2 := E), Hg; omega.
Qed.

Fact power_divides_sum_power r p n f :
         2 <= r 
      -> 0 < n
      -> (forall i j, i < j < n -> f i < f j) 
      -> divides (power p r) (∑ n (fun i => power (f i) r)) <-> p <= f 0.
Proof.
  intros Hr Hn Hf.
  split.
  + destruct inc_seq_split_lt with (k := p) (1 := Hf) as (k & H1 & H2 & H3).
    replace n with (k+(n-k)) by omega.
    rewrite msum_plus; auto.
    rewrite plus_comm; intros H.
    apply divides_plus_inv in H.
    2: apply divides_msum; intros; apply divides_power, H3; omega.
    destruct k as [ | k ].
    * apply H3; omega.
    * apply divides_lt in H.
      - rewrite msum_S in H.
        generalize (@power_ge_1 (f 0) r); intros; omega.
      - apply sum_powers_inc_lt; auto.
        intros; apply Hf; omega.
  + intros H.
    apply divides_msum.
    intros i Hi; apply divides_power.
    apply le_trans with (1 := H).
    destruct i; auto. 
    generalize (Hf 0 (S i)); intros; omega.
Qed.

Fact smono_upto_injective n f :
       (forall i j, i < j < n -> f i < f j)
    -> (forall i j, i < n -> j < n -> f i = f j -> i = j).
Proof.
  intros Hf i j Hi Hj E.
  destruct (lt_eq_lt_dec i j) as [ [H|] | H ]; auto.
  + generalize (@Hf i j); intros; omega.
  + generalize (@Hf j i); intros; omega.
Qed.

Fact product_sums n f g : (∑ n f)*(∑ n g) 
                         = ∑ n (fun i => f i*g i) 
                         + ∑ n (fun i => ∑ i (fun j => f i*g j + f j*g i)).
Proof.
  induction n as [ | n IHn ].
  + repeat rewrite msum_0; auto.
  + repeat rewrite msum_plus1; auto.
    repeat rewrite Nat.mul_add_distr_l.
    repeat rewrite Nat.mul_add_distr_r.
    rewrite IHn, msum_sum; auto.
    * rewrite sum_0n_scal_l, sum_0n_scal_r; ring.
    * intros; ring.
Qed.

Section sums.

  Fact square_sum n f : (∑ n f)*(∑ n f) = ∑ n (fun i => f i*f i) + 2*∑ n (fun i => ∑ i (fun j => f i*f j)).
  Proof.
    rewrite product_sums, <- sum_0n_scal_l; f_equal.
    apply msum_ext; intros; rewrite <- sum_0n_scal_l.
    apply msum_ext; intros; ring.
  Qed. 

  Fact sum_regroup r k n f :
          (forall i, i < n -> f i < k) 
       -> (forall i j, i < j < n -> f i < f j)
       -> { g | ∑ n (fun i => power (f i) r) 
              = ∑ k (fun i => g i * power i r) 
             /\ (forall i, i < k  -> g i <= 1) 
             /\ (forall i, k <= i -> g i = 0) }.
  Proof.
    revert k f; induction n as [ | n IHn ]; intros k f Hf1 Hf2.
    + exists (fun _ => 0); split; auto.
      rewrite msum_0, msum_of_unit; auto.
    + destruct (IHn (f n) f) as (g & H1 & H2 & H3).
      * intros; apply Hf2; omega.
      * intros; apply Hf2; omega.
      * exists (fun i => if eq_nat_dec i (f n) then 1 else g i).
        split; [ | split ].
        - rewrite msum_plus1, H1; auto.
          replace k with (f n + S (k - f n -1)).
          2: generalize (Hf1 n); intros; omega.
          rewrite msum_plus; auto; f_equal.
          ++ apply msum_ext.
             intros i He.
             destruct (eq_nat_dec i (f n)); try ring; omega.
          ++ rewrite msum_S, msum_of_unit; auto.
             ** repeat (rewrite plus_comm; simpl). 
                destruct (eq_nat_dec (f n) (f n)); try ring; omega.
             ** intros i Hi.
                destruct (eq_nat_dec (f n+S i) (f n)); try omega.
                rewrite H3; omega.
        - intros i Hi.
          destruct (eq_nat_dec i (f n)); auto.
          destruct (le_lt_dec (f n) i).
          ++ rewrite H3; omega.
          ++ apply H2; omega.
        - intros i Hi.
          generalize (Hf1 n); intros.
          destruct (eq_nat_dec i (f n)); try omega.
          apply H3; omega.
  Qed.
 
  Section sum_sum_regroup.

    Variable (r n k : nat) (f : nat -> nat)
             (Hf1 : forall i, i < n -> f i <= k) 
             (Hf2 : forall i j, i < j < n -> f i < f j).

    Theorem sum_sum_regroup : { g | ∑ n (fun i => ∑ i (fun j => power (f i + f j) r))
                                  = ∑ (2*k) (fun i => g i * power i r) 
                                  /\ forall i, g i <= n }.
    Proof.
      revert n f Hf1 Hf2. 
      induction n as [ | p IHp ]; intros f Hf1 Hf2.
      + exists (fun _ => 0); split; auto.
        rewrite msum_0.
        simpl; rewrite msum_of_unit; auto.
      + destruct (IHp f) as (g & H1 & H2).
        * intros; apply Hf1; omega.
        * intros; apply Hf2; omega.
        * destruct sum_regroup with (r := r) (n := p) (f := fun j => f p + f j) (k := 2*k)
            as (g1 & G1 & G2 & G3).
          - intros i Hi; generalize (@Hf1 p) (@Hf2 i p); intros; omega.
          - intros i j H; generalize (@Hf2 i j); intros; omega.
          - assert (forall i, g1 i <= 1) as G4.
            { intro i; destruct (le_lt_dec (2*k) i); auto; rewrite G3; omega. }
            exists (fun i => g i + g1 i); split.
            ++ rewrite msum_plus1; auto.
               rewrite H1, G1, <- msum_sum; auto.
               2: intros; ring.
               apply msum_ext; intros; ring.
            ++ intros i.
               generalize (H2 i) (G4 i); intros; omega.
    Qed.

  End sum_sum_regroup.

  Section all_ones.

    Let equation_inj x y a b : 1 <= x -> 1+x*a = y -> 1+x*b = y -> a = b.
    Proof.
      intros H1 H2 H3.
      rewrite <- H3 in H2; clear y H3.
      rewrite <- (@Nat.mul_cancel_l _ _ x); omega.
    Qed.

    Variables (r : nat) (Hr : 2 <= r).

    Fact all_ones_equation l : 1+(r-1)*∑ l (fun i => power i r) = power l r.
    Proof.
      induction l as [ | l IHl ].
      * rewrite msum_0, Nat.mul_0_r, power_0; auto.
      * rewrite msum_plus1; auto.
        rewrite Nat.mul_add_distr_l, power_S.
        replace r with (1+(r-1)) at 4 by omega.
        rewrite Nat.mul_add_distr_r.
        rewrite <- IHl at 2; ring.
    Qed.

    Fact all_ones_dio l w : w = ∑ l (fun i => power i r) <-> 1+(r-1)*w = power l r.
    Proof.
      split.
      + intros; subst; apply all_ones_equation.
      + intros H.
        apply equation_inj with (2 := H).
        * omega.
        * apply all_ones_equation.
    Qed.

  End all_ones.

  Section const_1.

    Variable (l q : nat) (Hl : 0 < l) (Hlq : l+1 < q).

    Let Hq : 1 <= q.     Proof. omega. Qed. 
    Let Hq' : 0 < 4*q.   Proof. omega. Qed.
    
    Let r := (power (4*q) 2).

    Let Hr' : 4 <= r.    Proof. apply (@power_mono_l 2 (4*q) 2); omega. Qed.
    Let Hr :  2 <= r.    Proof. omega. Qed.

    Section all_ones.

      Variable (n w : nat) (Hw : w = ∑ n (fun i => power i r)).

      Let Hw_0 : w = ∑ n (fun i => 1*power i r).
      Proof. rewrite Hw; apply msum_ext; intros; ring. Qed.

      Fact all_ones_joins : w = msum nat_join 0 n (fun i => 1*power i r).
      Proof. 
        rewrite Hw_0.
        apply sum_powers_ortho with (q := 4*q); auto; try omega.
      Qed.

      Let Hw_1 : 2*w = ∑ n (fun i => 2*power i r).
      Proof. 
        rewrite Hw_0, <- sum_0n_scal_l.
        apply msum_ext; intros; ring.
      Qed.

      Fact all_ones_2_joins : 2*w = msum nat_join 0 n (fun i => 2*power i r).
      Proof.
        rewrite Hw_1.
        apply sum_powers_ortho with (q := 4*q); auto; try omega.
        intros; omega.
      Qed.

    End all_ones.

    Section increase.
   
      Variable (m k k' u w : nat) (f : nat -> nat) 
               (Hm : 2*m < r) 
               (Hf1 : forall i, i < m -> f i <= k)
               (Hf2 : forall i j, i < j < m  -> f i < f j)
               (Hw : w = ∑ k' (fun i => power i r))
               (Hu : u = ∑ m (fun i => power (f i) r)).

      Let Hf4 : forall i j, i < m -> j < m -> f i = f j -> i = j.
      Proof. apply smono_upto_injective; auto. Qed.

      Let u1 := ∑ m (fun i => power (2*f i) r).
      Let u2 := ∑ m (fun i => ∑ i (fun j => 2*power (f i + f j) r)).

      Fact const_u_square : u * u = u1 + u2.
      Proof.
        unfold u1, u2.
        rewrite Hu, square_sum; f_equal.
        + apply msum_ext; intros; rewrite <- power_plus; f_equal; omega.
        + rewrite <- sum_0n_scal_l; apply msum_ext; intros i Hi.
          rewrite <- sum_0n_scal_l; apply msum_ext; intros j Hj.
          rewrite power_plus; ring.
      Qed.

      Let Hu1_0 : u1 = ∑ m (fun i => 1*power (2*f i) r).
      Proof. apply msum_ext; intros; ring. Qed.

      Let Hseq_u a : a <= m -> ∑ a (fun i => 1*power (2*f i) r) = msum nat_join 0 a (fun i => 1*power (2*f i) r).
      Proof.
        intros Ha.
        apply sum_powers_ortho with (q := 4*q); auto; try omega.
        intros i j Hi Hj ?; apply Hf4; omega.
      Qed.

      Let Hu1 : u1 = msum nat_join 0 m (fun i => 1*power (2*f i) r).
      Proof. 
        rewrite Hu1_0; apply Hseq_u; auto.
      Qed.

      Let Hu2_0 : u2 = 2 * ∑ m (fun i => ∑ i (fun j => power (f i + f j) r)).
      Proof.
        unfold u2; rewrite <- sum_0n_scal_l; apply msum_ext.
        intros; rewrite <- sum_0n_scal_l; apply msum_ext; auto.
      Qed.

      (* MAJOR change in the argumentation ... one cannot show
         in generalize that the powers r^(f i + f j) are distincts
         powers for the values j < i < n, hence it is not correct
         than the sum reduces to a join ... it works when 
         f i = 2^i but not for an arbitrary (increasing function) f 

         So we rewrite ∑ {j < i < n} r^(f i + f j) as
            ∑ {i < k} (g i)*r^i for some small g i <= n
         supposing n is low compared to r *) 
         

      Let g_full : { g | ∑ m (fun i => ∑ i (fun j => power (f i + f j) r))
                      = ∑ (2*k) (fun i : nat => g i * power i r) 
                      /\ forall i : nat, g i <= m }.
      Proof. apply sum_sum_regroup; auto. Qed.
 
      Let g := proj1_sig g_full.
      Let Hg1 : u2 = ∑ (2*k) (fun i => (2*g i) * power i r).
      Proof. 
        rewrite Hu2_0, (proj1 (proj2_sig g_full)), <- sum_0n_scal_l.
        apply msum_ext; unfold g; intros; ring.
      Qed.

      Let Hg2 i : 2*g i <= 2*m.
      Proof. apply mult_le_compat; auto; apply (proj2_sig g_full). Qed.

      Let Hg3 i : 2*g i < r.
      Proof. apply le_lt_trans with (1 := Hg2 _); auto. Qed.

      Let Hu2 : u2 = msum nat_join 0 (2*k) (fun i => (2*g i) * power i r).  
      Proof.
        rewrite Hg1.
        apply sum_powers_ortho with (q := 4*q); auto; omega.
      Qed.
  
      Let Hu1_u2_1 : u1 ⇣ u2 = 0.
      Proof.
        rewrite Hu1, Hu2.
        apply nat_ortho_joins.
        intros i j Hi Hj.
        destruct (eq_nat_dec j (2*f i)) as [ H | H ].
        + unfold r; do 2 rewrite <- power_mult.
          rewrite <- H.
          rewrite nat_meet_mult_power2.
          rewrite nat_meet_12n; auto.
        + rewrite nat_meet_powers_neq with (q := 4*q); auto; omega.
      Qed.

      Let Hu1_u2 : u*u = u1 ⇡ u2.
      Proof.
        rewrite const_u_square.
        apply nat_ortho_plus_join; auto.
      Qed.
   
      Let Hw_1 : w = msum nat_join 0 k' (fun i => 1*power i r).
      Proof. rewrite Hw; apply all_ones_joins; auto. Qed.

      Let H2w_1 : 2*w = msum nat_join 0 k' (fun i => 2*power i r).
      Proof. rewrite Hw; apply all_ones_2_joins; auto. Qed.

      Let Hu2_w : u2 ⇣ w = 0.
      Proof.
        rewrite Hu2, Hw_1.
        destruct (le_lt_dec k' (2*k)) as [ Hk | Hk ].
        2: { apply nat_ortho_joins.
             intros i j Hi Hj.
             rewrite nat_meet_comm.
             destruct (eq_nat_dec i j) as [ H | H ].
             + subst j; rewrite nat_meet_powers_eq with (q := 4*q); auto.
               rewrite nat_meet_12n; auto.
             + apply nat_meet_powers_neq with (q := 4*q); auto; try omega. }
        replace (2*k) with (k'+(2*k-k')) by omega.
        rewrite msum_plus, nat_meet_comm, nat_meet_join_distr_l, nat_join_comm; auto.
        rewrite (proj2 (nat_ortho_joins k' (2*k-k') _ _)), nat_join_0n.
        2: { intros i j H1 H2.
             apply nat_meet_powers_neq with (q := 4*q); auto; try omega. }
        apply nat_ortho_joins.
        intros i j Hi Hj.
        destruct (eq_nat_dec i j) as [ H | H ].
        + subst j; rewrite nat_meet_powers_eq with (q := 4*q); auto.
          rewrite nat_meet_12n; auto.
        + apply nat_meet_powers_neq with (q := 4*q); auto; try omega.
      Qed.

      Fact const_u1_prefix : { q | q <= m /\ u*u ⇣ w = ∑ q (fun i => 1*power (2*f i) r) }.
      Proof.
        destruct inc_seq_split_lt with (n := m) (f := fun i => 2*f i) (k := k') as (a & H1 & H2 & H3).
        + intros i j Hij; apply Hf2 in Hij; omega.
        + exists a; split; auto.
          rewrite Hu1_u2, nat_meet_comm, nat_meet_join_distr_l.
          do 2 rewrite (nat_meet_comm w).
          rewrite Hu2_w, nat_join_n0.
          rewrite Hu1, Hw_1.
          replace m with (a+(m-a)) by omega.
          rewrite msum_plus, nat_meet_comm, nat_meet_join_distr_l.
          rewrite nat_join_comm.
          rewrite (proj2 (nat_ortho_joins k' (m-a) _ _)), nat_join_0n; auto.
          3: apply nat_join_monoid.
          * rewrite Hseq_u; auto.
            rewrite nat_meet_comm.
            apply binary_le_nat_meet.
            apply nat_joins_binary_le.
            intros i Hi.
            exists (2*f i); split; auto.
          * intros; apply  nat_meet_powers_neq with (q := 4*q); auto; try omega.
            generalize (H3 (a + j)); intros; omega.
      Qed. 
         
      Hypothesis (Hk : 2*k < k').

      Let Hu1_w : u1 ⇣ w = u1.
      Proof.
        apply binary_le_nat_meet.
        rewrite Hu1, Hw_1.
        apply nat_joins_binary_le.
        intros i Hi.
        exists (2*f i); split; auto.
        apply le_lt_trans with (2 := Hk), mult_le_compat; auto.
      Qed.

      Let Hu1_2w : u1 ⇣ (2*w) = 0.
      Proof.
        rewrite H2w_1, Hu1, nat_ortho_joins.
        intros i j Hi Hj.
        destruct (eq_nat_dec j (2 * f i)) as [ H | H ].
        + rewrite <- H, nat_meet_powers_eq with (q := 4*q); auto; try omega.
          rewrite nat_meet_12; auto.
        + apply nat_meet_powers_neq with (q := 4*q); auto; try omega.
      Qed.

      Fact const_u1_meet p : p = (u*u) ⇣ w <-> p = u1.
      Proof.
        rewrite Hu1_u2, nat_meet_comm, nat_meet_join_distr_l.
        do 2 rewrite (nat_meet_comm w).
        rewrite Hu1_w, Hu2_w, nat_join_n0; tauto.
      Qed.

      Fact const_u1_eq : (u*u) ⇣ w = u1.
      Proof. apply const_u1_meet; auto. Qed.

      Hypothesis Hf : forall i, i < m -> f i = power (S i) 2.

      Let Hu2_1 : u2 = msum nat_join 0 m (fun i => msum nat_join 0 i (fun j => 2*power (f i + f j) r)).
      Proof.
        unfold u2.
        apply double_sum_powers_ortho with (q := 4*q); auto; try omega.
        + intros; omega.
        + intros ? ? ? ? ? ?; repeat rewrite Hf; try omega.
          intros E.
          apply sum_2_power_2_injective in E; omega.
      Qed.

      (* This cannot be proved anymore without stronger hypothesis on f *) 

      Let Hu2_2w : u2 ⇣ (2*w) = u2.
      Proof.
        apply binary_le_nat_meet.
        rewrite H2w_1, Hu2_1.
        apply nat_double_joins_binary_le.
        intros i j Hij.
        exists (f i + f j); split; auto.
        apply le_lt_trans with (2*f i); auto.
        + apply Hf2 in Hij; omega.
        + apply le_lt_trans with (2 := Hk), mult_le_compat; auto.
          apply Hf1; omega.
      Qed. 

      Fact const_u2_meet p : p = (u*u) ⇣ (2*w) <-> p = u2.
      Proof.
        rewrite Hu1_u2, nat_meet_comm, nat_meet_join_distr_l.
        do 2 rewrite (nat_meet_comm (2*w)).
        rewrite Hu1_2w, Hu2_2w, nat_join_0n; tauto.
      Qed.

    End increase.

    Let Hl'' : 2*l < r.
    Proof.
      unfold r.
      rewrite (mult_comm _ q), power_mult.
      change (power 4 2) with 16.
      apply power_smono_l with (x := 16) in Hlq; try omega.
      apply le_lt_trans with (2 := Hlq).
      rewrite plus_comm; simpl plus; rewrite power_S.
      apply mult_le_compat; try omega.
      apply power_ge_n; omega.
    Qed.

    Section const_1_cn.

      (* Perhaps you should encode the predicate that 
          
           w = ∑ {i=0..2^{l+1}} r^i
           u = ∑ {1..l} r^{2^i} and u1 = u*u ⇣ w

         as diophantine and use that predicate because
         it is used for Const1 and the product and CodeNat *)

      Variable (u u1 : nat) (Hu  : u = ∑ l (fun i => power (power (S i) 2) r))
                            (Hu1 : u1 = ∑ l (fun i => power (power (S (S i)) 2) r)).
 
      Let w  := ∑ (S (power (S l) 2)) (fun i => power i r).
 (*     Let u1 := ∑ l (fun i => power (power (S (S i)) 2) r). *)
      Let u2 := ∑ l (fun i => ∑ i (fun j => 2*power (power (S i) 2 + power (S j) 2) r)).
 
      Let H18 : 1+(r-1)*w = power (S (power (S l) 2)) r.
      Proof. rewrite <- all_ones_dio; auto. Qed.

      Let H19 : u*u = u1 + u2.
      Proof.
        rewrite Hu1. 
        apply const_u_square with (w := w) (2 := eq_refl); auto.
      Qed.

      Let k := S (power (S l) 2).
      Let f i := power (S i) 2.

      Let Hf1 i : i < l -> 2*f i < k.
      Proof.
        unfold k, f.
        intros; rewrite <- power_S; apply le_n_S, power_mono_l; omega.
      Qed.

      Let Hf2 i j : i < j < l -> f i < f j.
      Proof. intros; apply power_smono_l; omega. Qed.

      Let Hf3 i1 j1 i2 j2 : j1 <= i1 < l -> j2 <= i2 < l -> f i1 + f j1 = f i2 + f j2 -> i1 = i2 /\ j1 = j2.
      Proof.
        unfold f; intros H1 H2 E.
        apply sum_2_power_2_injective in E; omega.
      Qed.

      Let H20 : u1 = (u*u) ⇣ w.
      Proof. 
        rewrite const_u1_meet with (k := power l 2) (m := l) (f := f); auto.
        * intros i Hi; specialize (Hf1 Hi).
          revert Hf1; unfold k; rewrite power_S; intros; omega.
        * rewrite <- power_S; auto.
      Qed. 

      Let H21 : u2 = (u*u) ⇣ (2*w).
      Proof. 
        rewrite const_u2_meet with (k := power l 2) (m := l) (f := f); auto.
        * intros i Hi; specialize (Hf1 Hi).
          revert Hf1; unfold k; rewrite power_S; intros; omega.
        * rewrite <- power_S; auto.
     Qed. 
 
      Let H22 : power 2 r + u1 = u + power (power (S l) 2) r.
      Proof.
        rewrite Hu, Hu1.
        destruct l.
        + do 2 rewrite msum_0.
          rewrite power_1; auto.
        + rewrite msum_plus1, msum_S; auto.
          rewrite power_1; ring.
      Qed.
  
      Let H23 : divides (power 4 r) u1.
      Proof.
        rewrite Hu1.
        apply divides_msum.
        intros i _.
        apply divides_power.
        apply (@power_mono_l 2 _ 2); omega.
      Qed.

      Lemma const1_cn : exists w u2,    1+(r-1)*w = power (S (power (S l) 2)) r
                                     /\ u*u = u1 + u2
                                     /\ u1 = (u*u) ⇣ w
                                     /\ u2 = (u*u) ⇣ (2*w)
                                     /\ power 2 r + u1 = u + power (power (S l) 2) r
                                     /\ divides (power 4 r) u1.
      Proof.
        exists w, u2; repeat (split; auto).
      Qed.

    End const_1_cn.

    Section const_1_cs.

      Variable (w u u1 u2 : nat).

      Hypothesis (H18 : 1+(r-1)*w = power (S (power (S l) 2)) r)
                 (H19 : u*u = u1 + u2)
                 (H20 : u1 = (u*u) ⇣ w)
                 (H21 : u2 = (u*u) ⇣ (2*w))
                 (H22 : power 2 r + u1 = u + power (power (S l) 2) r)
                 (H23 : divides (power 4 r) u1).

      Let Hw_0 : w = ∑ (S (power (S l) 2)) (fun i => power i r).
      Proof. apply all_ones_dio; auto. Qed.

      Let Hw_1 : w = ∑ (S (power (S l) 2)) (fun i => 1*power i r).
      Proof. rewrite Hw_0; apply msum_ext; intros; ring. Qed.

      Let Hw : w = msum nat_join 0 (S (power (S l) 2)) (fun i => 1*power i r).
      Proof. apply all_ones_joins; auto. Qed.

      Let H2w : 2*w = msum nat_join 0 (S (power (S l) 2)) (fun i => 2*power i r).
      Proof. apply all_ones_2_joins; auto. Qed.
    
      Let Hu1_0 : u1 ≲ ∑ (S (power (S l) 2)) (fun i => 1*power i r).
      Proof. rewrite H20, <- Hw_1; auto. Qed.

      Let mk_full : { m : nat & { k | u1 = ∑ (S m) (fun i => power (k i) r) 
                                /\ m <= power (S l) 2
                                /\ (forall i, i < S m -> k i <= power (S l) 2) 
                                /\ forall i j, i < j < S m -> k i < k j } }.
      Proof.
        assert ({ k : nat &
                 { g : nat -> nat & 
                 { h | u1 = ∑ k (fun i => g i * power (h i) r)
                     /\ k <= S (power (S l) 2)
                     /\ (forall i, i < k -> g i <> 0 /\ g i ≲ 1)
                     /\ (forall i, i < k -> h i < S (power (S l) 2))
                     /\ (forall i j, i < j < k -> h i < h j) } } }) as H.
        { apply (@sum_powers_binary_le_inv _ Hq' r eq_refl _ (fun _ => _) (fun i => i)); auto.
          intros; omega. }
        destruct H as (m' & g & h & H1 & H2 & H3 & H4 & H5).
        assert (H6 : forall i, i < m' -> g i = 1).
        { intros i Hi; generalize (H3 _ Hi).
          intros (? & G2); apply binary_le_le in G2; omega. }
        assert (H7 : u1 = ∑ m' (fun i => 1 * power (h i) r)).
        { rewrite H1; apply msum_ext; intros; rewrite H6; try ring; omega. }
        assert (H8 : u1 = ∑ m' (fun i => power (h i) r)).
        { rewrite H7; apply msum_ext; intros; ring. }
        assert (H9 : m' <> 0).
        { intros E; rewrite E, msum_0 in H1.
          assert (power 2 r < power (power (S l) 2) r) as C.
          { apply power_smono_l; auto.
            apply (@power_smono_l 1 _ 2); omega. }
          omega. }
        destruct m' as [ | m ]; try omega.
        exists m, h; repeat (split; auto).
        + omega.
        + intros i; generalize (H4 i); intros; omega.
      Qed.

      Let m := projT1 mk_full.
      Let k := proj1_sig (projT2 mk_full).

      Let Hu1 : u1 = ∑ (S m) (fun i => power (k i) r).        Proof. apply (proj2_sig (projT2 mk_full)). Qed.
      Let Hm : m <= (power (S l) 2).                          Proof. apply (proj2_sig (projT2 mk_full)). Qed.
      Let Hk1 : forall i, i < S m -> k i <= power (S l) 2.    Proof. apply (proj2_sig (projT2 mk_full)). Qed.
      Let Hk2 : forall i j, i < j < S m -> k i < k j.         Proof. apply (proj2_sig (projT2 mk_full)). Qed.

      Let Hh_0 : 4 <= k 0.
      Proof.
        rewrite Hu1 in H23.
        apply power_divides_sum_power in H23; auto; try omega.
      Qed.

      Let f1 i := match i with 0 => 2 | S i => k i end.
      Let f2 i := if le_lt_dec i m then power (S l) 2 else k i.

      Let Hf1_0 : forall i, i <= S m -> f1 i < S (power (S l) 2).
      Proof.
        intros [ | i ] Hi; simpl; apply le_n_S.
        + rewrite power_S.
          change 2 with (2*1) at 1.
          apply mult_le_compat; auto.
          apply power_ge_1; omega.
        + apply Hk1; auto.
      Qed.

      Let Hf1_1 : forall i j, i < j <= S m -> f1 i < f1 j.
      Proof.
        intros [ | i ] [ | j ] Hij; simpl; try omega.
        * apply lt_le_trans with (k 0); try omega.
          destruct j; auto; apply lt_le_weak, Hk2; omega.
        * apply Hk2; omega.
      Qed.

      Let Hf1_2 : ∑ (S (S m)) (fun i => power (f1 i) r) = u + power (power (S l) 2) r.
      Proof.
        rewrite msum_S; unfold f1.
        rewrite <- Hu1; auto.
      Qed.

      Let Hh_1 : k m = power (S l) 2.
      Proof.
        destruct (le_lt_dec (power (S l) 2) (k m)) as [ H | H ].
        + apply le_antisym; auto.
        + assert (∑ (S (S m)) (fun i => power (f1 i) r) < power (power (S l) 2) r); try omega.
          apply sum_powers_inc_lt; auto.
          - intros [ | i ] Hi; simpl.
            * apply (@power_smono_l 1 _ 2); omega.
            * apply le_lt_trans with (2 := H).
              destruct (eq_nat_dec i m); subst; auto.
              apply lt_le_weak, Hk2; omega.
          - intros; apply Hf1_1; omega.
      Qed.
 
      Let Hu : u = ∑ (S m) (fun i => power (f1 i) r).
      Proof.
        rewrite msum_plus1 in Hf1_2; auto.
        simpl f1 at 2 in Hf1_2.
        rewrite Hh_1 in Hf1_2.
        omega.
      Qed.
        
      Let Huu : u*u = ∑ (S m) (fun i => power (2*f1 i) r)
                    + ∑ (S m) (fun i => ∑ i (fun j => 2*power (f1 i + f1 j) r)).
      Proof.
        rewrite Hu, square_sum; f_equal.
        + apply msum_ext; intros; rewrite <- power_plus; f_equal; omega.
        + rewrite <- sum_0n_scal_l; apply msum_ext; intros i Hi.
          rewrite <- sum_0n_scal_l; apply msum_ext; intros j Hj.
          rewrite power_plus; ring.
      Qed.

      (* This one should not be that hard given S l < q but to check *)

      Let HSl_q : 2 * S (power (S l) 2) < power (2 * q) 2.
      Proof.
        rewrite <- (mult_2_eq_plus q), power_plus.
        apply le_lt_trans with (2*power q 2).
        + apply mult_le_compat; auto.
          apply power_smono_l; omega.
        + assert (power 1 2 < power q 2) as H.
          { apply power_smono_l; omega. }
          rewrite power_1 in H.
          apply Nat.mul_lt_mono_pos_r; omega.
      Qed.
  
      Let Hu1_1 : { d | d <= S m /\ u1 = ∑ d (fun i => power (2*f1 i) r) }.
      Proof.
        destruct const_u1_prefix with (m := S m) (k := power (S l) 2) (k' := S (power (S l) 2))
           (u := u) (w := w) (f := fun i => f1 i)
           as (d & H1 & H2); auto.
        + unfold r.
          apply le_lt_trans with (2*S (power (S l) 2)); try omega.
          apply le_lt_trans with (power (S (S (S l))) 2).
          do 4 rewrite power_S.
          * generalize (@power_ge_1 l 2); intros; omega.
          * apply power_smono_l; omega.
        + intros i Hi; generalize (@Hf1_0 i); intros; omega.
        + intros; apply Hf1_1; omega.
        + exists d; split; auto.
          rewrite H20, H2.
          apply msum_ext; intros; ring.
      Qed.

      Let Hk_final : k 0 = 4 /\ forall i, i < m -> k (S i) = 2*k i.
      Proof.
        destruct Hu1_1 as (d & Hd1 & E).
        rewrite Hu1 in E.
        apply sum_powers_injective in E; auto.
        + destruct E as (? & E); subst d; split.
          * rewrite E; try omega; auto.
          * intros; rewrite E; auto; omega.
        + intros i j H; specialize (@Hf1_1 i j); intros; omega.
      Qed.

      Let Hk_is_power i : i <= m -> k i = power (S (S i)) 2.
      Proof.
         induction i as [ | i IHi ]; intros Hi.
         + rewrite (proj1 Hk_final); auto.
         + rewrite (proj2 Hk_final), IHi, <- power_S; auto; omega.
      Qed.

      Let Hm_is_l : S m = l.
      Proof.
        rewrite Hk_is_power in Hh_1; auto.
        apply power_2_inj in Hh_1; omega.
      Qed.
        
      Fact obtain_u_u1_value :  u  = ∑ l (fun i => power (power (S i) 2) r)
                             /\ u1 = ∑ l (fun i => power (power (S (S i)) 2) r).
      Proof.
        split.
        + rewrite <- Hm_is_l, Hu.
          apply msum_ext.
          intros [ | i ]; simpl; auto.
          intros; rewrite Hk_is_power; auto; omega.
        + rewrite <- Hm_is_l, Hu1.
          apply msum_ext.
          intros [ | i ]; simpl; auto.
          * rewrite Hk_is_power; auto; omega.
          * intros; rewrite Hk_is_power; auto; omega.
      Qed.

    End const_1_cs.

  End const_1.

  Variable (l q : nat).

  Notation r := (power (4*q) 2).

  Definition seqs_of_ones u u1 :=
                   l+1 < q 
                /\ u  = ∑ l (fun i => power (power (S i) 2) r)
                /\ u1 = ∑ l (fun i => power (power (S (S i)) 2) r).

  (* This lemma shows that seqs_of_ones can be encoded by a diophantine expression *)

  Lemma seqs_of_ones_dio u u1 :
            seqs_of_ones u u1 
        <-> l = 0 /\ u = 0 /\ u1 = 0 /\ 2 <= q
         \/ 0 < l /\ l+1 < q
         /\ exists u2 w r0 r1 p1 p2,
                r0 = r 
             /\ r1+1 = r0
             /\ p1 = power (1+l) 2
             /\ p2 = power p1 r0
             /\ 1+r1*w = r0*p2
             /\ u*u = u1 + u2
             /\ u1 = (u*u) ⇣ w
             /\ u2 = (u*u) ⇣ (2*w)
             /\ r0*r0 + u1 = u + p2
             /\ divides (r0*r0*r0*r0) u1. 
  Proof.
    split.
    + intros (H2 & H3 & H4).
      destruct (le_lt_dec l 0) as [ H1 | H1 ].
      - assert (l=0) by omega; subst l.
        rewrite msum_0 in H3, H4; subst; left; omega.
      - right; split; auto; split; auto.
        destruct (const1_cn H1 H2 H3 H4) as (w & u2 & E1 & E2 & E3 & E4 & E5 & E6).
        exists u2, w, r, (r-1), (power (S l) 2), (power (power (S l) 2) r); repeat (split; auto).
        * generalize (@power_ge_1 (4*q) 2); intros; omega.
        * revert E5; rewrite power_S, power_1; auto.
        * revert E6; do 3 rewrite power_S; rewrite power_1.
          repeat rewrite mult_assoc; auto.
    + intros [ (H1 & H2 & H3 & H4)
             | (H1 & H2 & u2 & w & r0 & r1 & p1 & p2 & ? & H0 & ? & ? & E1 & E2 & E3 & E4 & E5 & E6) ].
      - red; subst; do 2 rewrite msum_0; omega.
      - assert (r1 = r0-1) by omega; clear H0.
        subst r0 r1 p1 p2; split; auto.
        apply obtain_u_u1_value with w u2; auto.
        * rewrite power_S, power_1; auto.
        * do 3 rewrite power_S; rewrite power_1.
          repeat rewrite mult_assoc; auto.
  Qed.

  Definition is_cipher_of f a :=
                 l+1 < q
              /\ (forall i, i < l -> f i < power q 2)
              /\ a = ∑ l (fun i => f i * power (power (S i) 2) r).

  Fact is_cipher_of_0 f a : l = 0 -> is_cipher_of f a <-> 1 < q /\ a = 0.
  Proof.
    intros ?; unfold is_cipher_of; subst l.
    rewrite msum_0; simpl.
    repeat (split; try tauto).
    intros; omega.
  Qed.

  Fact is_cipher_of_inj f1 f2 a : is_cipher_of f1 a -> is_cipher_of f2 a -> forall i, i < l -> f1 i = f2 i.
  Proof.
    intros (H1 & H2 & H3) (_ & H4 & H5).
    rewrite H3 in H5.
    revert H5; apply power_decomp_unique.
    + apply (@power_mono_l 1 _ 2); omega.
    + intros; apply power_smono_l; omega.
    + intros i Hi; apply lt_le_trans with (1 := H2 _ Hi), power_mono_l; omega.
    + intros i Hi; apply lt_le_trans with (1 := H4 _ Hi), power_mono_l; omega.
  Qed.

  Fact is_cipher_of_fun f1 f2 a b : 
          (forall i, i < l -> f1 i = f2 i)
        -> is_cipher_of f1 a 
        -> is_cipher_of f2 b
        -> a = b.
  Proof.
    intros H1 (_ & _ & H2) (_ & _ & H3); subst a b.
    apply msum_ext; intros; f_equal; auto.
  Qed.

  Lemma is_cipher_of_equiv f1 f2 a b : 
           is_cipher_of f1 a 
        -> is_cipher_of f2 b
        -> a = b <-> forall i, i < l -> f1 i = f2 i.
  Proof.
    intros Ha Hb; split.
    + intro; subst; revert Ha Hb; apply is_cipher_of_inj.
    + intro; revert Ha Hb; apply is_cipher_of_fun; auto.
  Qed.

  Lemma is_cipher_of_const_1 u : 0 < l -> is_cipher_of (fun _ => 1) u
                                     <-> l+1 < q /\ exists u1, seqs_of_ones u u1.
  Proof.
    intros Hl.
    split.
    + intros (H1 & H2 & H3); split; auto.
      exists (∑ l (fun i => power (power (S (S i)) 2) r)).
      rewrite H3; split; auto; split; auto.
      apply msum_ext; intros; ring.
    + intros (H1 & u1 & _ & H2).
      apply proj1 in H2.
      repeat (split; auto).
      * intros; apply (@power_smono_l 0); omega.
      * rewrite H2; apply msum_ext; intros; ring.
  Qed.

  Fact is_cipher_of_u : l+1 < q -> is_cipher_of (fun _ => 1) (∑ l (fun i => power (power (S i) 2) r)).
  Proof.
    intros H; split; auto; split.
    + intros; apply (@power_mono_l 1 _ 2); omega.
    + apply msum_ext; intros; omega.
  Qed.
 (*
  Fact is_cipher_of_u1 : l+1 < q -> is_cipher_of (fun _ => 1) (∑ l (fun i => power (power (S (S i)) 2) r)).
  Proof.
    intros H; split; auto; split.
    + intros; apply (@power_mono_l 1 _ 2); omega.
    + apply msum_ext; intros; omega.
  Qed.
 *)

  Definition the_cipher f : l+1 < q -> (forall i, i < l -> f i < power q 2) -> { c | is_cipher_of f c }.
  Proof.
    intros H1 H2.
    exists (∑ l (fun i => f i * power (power (S i) 2) r)); split; auto.
  Qed.

  Definition Code a := exists f, is_cipher_of f a.

  Lemma Code_dio a : Code a <-> l = 0 /\ 1 < q /\ a = 0
                             \/ 0 < l /\ l+1 < q /\ exists p u u1, p+1 = power q 2 /\ seqs_of_ones u u1 /\ a ≲ p*u.
  Proof.
    split.
    + intros (f & H1 & H2 & H3).
      destruct (eq_nat_dec l 0) as [ Hl | Hl ].
      * left; subst l; rewrite msum_0 in H3; omega.
      * right; split; try omega; split; auto.
        exists (power q 2-1), (∑ l (fun i => power (power (S i) 2) r)), (∑ l (fun i => power (power (S (S i)) 2) r)).
        repeat (split; auto).
        - generalize (@power_ge_1 q 2); intros; omega.
        - rewrite H3.
          apply sum_power_binary_lt with (q := 4*q); auto; try omega.
          intros; apply power_smono_l; omega.
    + intros [ (H1 & H2 & H3) | (H1 & H2 & p & u1 & u2 & ? & H3 & H4) ].
      * exists (fun _ => 0); subst a; apply is_cipher_of_0; auto.
      * destruct H3 as (_ & H3 & _).
        assert (p = power q 2 -1) by omega; subst p.
        rewrite H3 in H4. 
        apply sum_power_binary_lt_inv with (q := 4*q) (e := fun i => power (S i) 2) in H4; auto; try omega.
        2,3: intros; apply power_smono_l; omega.
        destruct H4 as (f & H4 & H5).
        exists f; split; auto.
  Qed.

  Definition Const c v := exists f, is_cipher_of f v /\ forall i, i < l -> f i = c.

  Lemma Const_dio c v : Const c v <-> l = 0 /\ 1 < q /\ v = 0
                                   \/ 0 < l /\ l+1 < q /\
                                      exists p u u1, p = power q 2 /\ c < p /\ seqs_of_ones u u1 /\ v = c*u.
  Proof.
    split.
    + intros (f & (H1 & H2 & H3) & H4).
      destruct (eq_nat_dec l 0) as [ Hl | Hl ].
      * left; subst l; rewrite msum_0 in H3; omega.
      * right; split; try omega; split; auto.
        exists (power q 2), (∑ l (fun i => power (power (S i) 2) r)), (∑ l (fun i => power (power (S (S i)) 2) r)).
        repeat (split; auto).
        - rewrite <- (H4 0); try omega; apply H2; omega.
        - rewrite H3, <- sum_0n_scal_l; apply msum_ext.
          intros; f_equal; auto.
    + intros [ (H1 & H2 & H3) | (H1 & H2 & p & u1 & u2 & ? & H3 & H4 & H5) ].
      * exists (fun _ => 0); subst v; split.
        - apply is_cipher_of_0; auto.
        - subst l; intros; omega.
      * destruct H4 as (_ & H4 & _).
        rewrite H4, <- sum_0n_scal_l in H5.
        exists (fun _ => c); split; auto.
        split; auto; split; auto.
        intros; omega.
  Qed.

  Let Hr : 1 < q -> 4 <= r. 
  Proof.
    intros H.
    replace (4*q) with (2*q+2*q) by omega.
    rewrite power_plus.
    change 4 with ((power 1 2)*(power 1 2)); apply mult_le_compat;
    apply power_mono_l; try omega.
  Qed.

  Section plus.

    Variable (a b c : nat-> nat) (ca cb cc : nat) 
             (Ha : is_cipher_of a ca)
             (Hb : is_cipher_of b cb) 
             (Hc : is_cipher_of c cc).

    Definition Code_plus := ca = cb + cc.
 
    Lemma Code_plus_spec : Code_plus <-> forall i, i < l -> a i = b i + c i.
    Proof.
      symmetry; unfold Code_plus.
      destruct Ha as (H & Ha1 & Ha2).
      destruct Hb as (_ & Hb1 & Hb2).
      destruct Hc as (_ & Hc1 & Hc2).
      destruct (eq_nat_dec l 0) as [ | Hl ].
      + subst l; rewrite msum_0 in *; split; intros; omega.
      + rewrite Hc2, Ha2, Hb2, <- sum_0n_distr_in_out.
        split.
        * intros; apply msum_ext; intros; f_equal; auto.
        * intros E i Hi. 
          apply power_decomp_unique with (i := i) in E; auto; try omega; clear i Hi.
          - intros; apply power_smono_l; omega.
          - intros i Hi; apply lt_le_trans with (1 := Ha1 _ Hi), power_mono_l; omega.
          - intros i Hi.
            apply lt_le_trans with (power (S q) 2).
            ++ rewrite power_S, <- mult_2_eq_plus.
               generalize (Hb1 _ Hi) (Hc1 _ Hi); omega.
            ++ apply power_mono_l; omega.
    Qed.

  End plus.

  Notation u := (∑ l (fun i => power (power (S i) 2) r)).
  Notation u1 := (∑ l (fun i => power (power (S (S i)) 2) r)).

  Section mult_utils.
 
    Variable (b c : nat-> nat) (cb cc : nat) 
             (Hb : is_cipher_of b cb) 
             (Hc : is_cipher_of c cc).

    Let eq1 :    cb*cc = ∑ l (fun i => (b i*c i)*power (power (S (S i)) 2) r)
                       + ∑ l (fun i => ∑ i (fun j => (b i*c j + b j*c i)*power (power (S i) 2 + power (S j) 2) r)).
    Proof.
      destruct Hb as (H1 & Hb1 & Hb2).
      destruct Hc as (_ & Hc1 & Hc2).
      rewrite Hb2, Hc2, product_sums; f_equal.
      * apply msum_ext; intros; rewrite (power_S (S _)).
        rewrite <- (mult_2_eq_plus (power _ _)), power_plus; ring.
      * apply msum_ext; intros i Hi.
        apply msum_ext; intros j Hj.
        rewrite power_plus; ring.
    Qed.

    Let Hbc_1 i : i < l -> b i * c i < r.
    Proof.
      destruct Hb as (H1 & Hb1 & Hb2).
      destruct Hc as (_ & Hc1 & Hc2).
      intro; apply mult_lt_power_2_4; auto.
    Qed.
  
    Let Hbc_2 i j : i < l -> j < l -> b i * c j + b j * c i < r.
    Proof.
      destruct Hb as (H1 & Hb1 & Hb2).
      destruct Hc as (_ & Hc1 & Hc2).
      intros; apply mult_lt_power_2_4'; auto.
    Qed.

    Let Hbc_3 : ∑ l (fun i => (b i*c i)*power (power (S (S i)) 2) r) 
              = msum nat_join 0 l (fun i => (b i*c i)*power (power (S (S i)) 2) r).
    Proof.
      destruct Hb as (H1 & Hb1 & Hb2).
      destruct Hc as (_ & Hc1 & Hc2).
      apply sum_powers_ortho with (q := 4*q); try omega; auto.
      intros ? ? ? ? E; apply power_2_inj in E; omega.
    Qed.

    Let Hbc_4 : ∑ l (fun i => ∑ i (fun j => (b i*c j + b j*c i)*power (power (S i) 2 + power (S j) 2) r))
              = msum nat_join 0 l (fun i => 
                           msum nat_join 0 i (fun j => (b i*c j + b j*c i)*power (power (S i) 2 + power (S j) 2) r)).
    Proof.
      destruct Hb as (H1 & Hb1 & Hb2).
      destruct Hc as (_ & Hc1 & Hc2).
      rewrite double_sum_powers_ortho with (q := 4*q); auto; try omega.
      + intros; apply Hbc_2; omega.
      + intros ? ? ? ? ? ? E; apply sum_2_power_2_injective in E; omega.
    Qed.
    
    Let eq2 :   cb*cc = msum nat_join 0 l (fun i => (b i*c i)*power (power (S (S i)) 2) r)
                      ⇡ msum nat_join 0 l (fun i => 
                           msum nat_join 0 i (fun j => (b i*c j + b j*c i)*power (power (S i) 2 + power (S j) 2) r)).
    Proof.
      destruct Hb as (H1 & Hb1 & Hb2).
      rewrite eq1, Hbc_3, Hbc_4.
      apply nat_ortho_plus_join.
      apply nat_ortho_joins.
      intros i j Hi Hj; apply nat_ortho_joins_left.
      intros k Hk.
      apply nat_meet_powers_neq with (q := 4*q); auto; try omega.
      * apply power_2_n_ij_neq; omega.
      * apply Hbc_2; omega.
    Qed.

    Let Hr_1 : (r-1)*u1 = ∑ l (fun i => (r-1)*power (power (S (S i)) 2) r).
    Proof. rewrite sum_0n_scal_l; auto. Qed.

    Let Hr_2 : (r-1)*u1 = msum nat_join 0 l (fun i => (r-1)*power (power (S (S i)) 2) r).
    Proof.
      destruct Hb as (H1 & Hb1 & Hb2).
      destruct Hc as (_ & Hc1 & Hc2).
      rewrite Hr_1.
      apply sum_powers_ortho with (q := 4*q); auto; try omega.
      + intros; omega.
      + intros ? ? ? ? E; apply power_2_inj in E; omega.
    Qed.
   
    Fact cipher_mult_eq : (cb*cc)⇣((r-1)*u1) = ∑ l (fun i => (b i*c i)*power (power (S (S i)) 2) r).
    Proof.
      destruct Hb as (H1 & Hb1 & Hb2).
      destruct Hc as (_ & Hc1 & Hc2).
      rewrite eq2, Hbc_3, Hr_2.
      rewrite nat_meet_comm, nat_meet_join_distr_l.
      rewrite <- Hr_2 at 1; rewrite Hr_1, <- Hbc_3.
      rewrite meet_sum_powers with (q := 4*q); auto; try (intros; omega).
      2: intros; apply power_smono_l; omega.
      rewrite (proj2 (nat_ortho_joins _ _ _ _)), nat_join_n0.
      * apply msum_ext; intros i Hi; f_equal.
        rewrite nat_meet_comm; apply binary_le_nat_meet, power_2_minus_1_gt; auto.
      * intros i j Hi Hj.
        apply nat_ortho_joins_left.
        intros k Hk; apply nat_meet_powers_neq with (q := 4*q); auto; try omega.
        + apply power_2_n_ij_neq; omega.
        + apply Hbc_2; omega.
    Qed.

  End mult_utils.
  
  Section mult.

    Variable (a b c : nat-> nat) (ca cb cc : nat) 
             (Ha : is_cipher_of a ca)
             (Hb : is_cipher_of b cb) 
             (Hc : is_cipher_of c cc).

    Definition Code_mult := 
                l = 0 
             \/ l <> 0 
             /\ exists v v1 r' r'' p, 
                        r'' = r 
                     /\ r'' = r'+1 
                     /\ seqs_of_ones v v1 
                     /\ p = (ca*v)⇣(r'*v1) 
                     /\ p = (cb*cc)⇣(r'*v1).

    Lemma Code_mult_spec : Code_mult <-> forall i, i < l -> a i = b i * c i. 
    Proof.
      unfold Code_mult; symmetry.
      destruct Ha as (Hlq & Ha1 & Ha2).
      destruct Hb as (_ & Hb1 & Hb2).
      destruct Hc as (_ & Hc1 & Hc2).
      destruct (eq_nat_dec l 0) as [ | Hl ].
      + subst l; split; intros; auto; omega.
      + split.
        * intros H; right; split; try omega.
          exists u, u1, (r-1), r, (ca * u ⇣ ((r-1) * u1)).
          split; auto; split; try omega.
          repeat (split; auto).
          generalize (is_cipher_of_u Hlq); intros H2.
          rewrite cipher_mult_eq with (1 := Ha) (2 := H2).
          rewrite cipher_mult_eq with (1 := Hb) (2 := Hc).
          apply msum_ext; intros; rewrite H; try ring; omega.
        * intros [ | (_ & v & v1 & r' & r'' & p & H0 & H1 & H2 & H3 & H4) ]; try (destruct Hl; auto; fail).
          destruct H2 as (_ & ? & ?); subst v v1.
          rewrite H3 in H4.
          revert H4.
          generalize (is_cipher_of_u Hlq); intros H2.
          replace r' with (r-1) by omega.
          rewrite cipher_mult_eq with (1 := Ha) (2 := H2).
          rewrite cipher_mult_eq with (1 := Hb) (2 := Hc).
          intros E.
          intros i Hi. 
          rewrite <- power_decomp_unique with (5 := E); auto; try omega.
          - intros; apply power_smono_l; omega.
          - intros j Hj; rewrite Nat.mul_1_r.
            apply lt_le_trans with (1 := Ha1 _ Hj), power_mono_l; omega.
          - intros; apply mult_lt_power_2_4; auto.
    Qed.

  End mult.

  Section inc_seq.

    Definition CodeNat c := is_cipher_of (fun i => i) c.

    Let IncSeq_dio_priv y : CodeNat y <-> l = 0 /\ 1 < q /\ y = 0 
                                  \/ 0 < l 
                                  /\ exists z v v1, 
                                        seqs_of_ones v v1 
                                     /\ Code y
                                     /\ Code z
                                     /\ y + l*(power (power (S l) 2) r) = (z*v)⇣((r-1) * v1)
                                     /\ y+v1+power (power 1 2) r = z + power (power (S l) 2) r.
    Proof.
      split.
      + intros (H1 & H2 & H3).
        destruct (le_lt_dec l 0) as [ | Hl ].
        - assert (l = 0) by omega; subst l.
          rewrite msum_0 in H3; left; omega.
        - right; split; auto.
          exists (∑ l (fun i => (S i) * power (power (S i) 2) r)), u, u1; split; auto.
          { split; auto. }
          split.
          { rewrite H3; exists (fun i => i); split; auto. }
          split.
          { exists S; repeat (split; auto).
            intros; apply lt_le_trans with q; try omega.
            apply power_ge_n; auto. }
          split.
          { rewrite cipher_mult_eq with (b := S) (c := fun _ => 1).
            * rewrite H3.
              rewrite <- msum_plus1 with (f := fun i => i*power (power (S i) 2) r); auto.
              rewrite msum_S, Nat.mul_0_l, Nat.add_0_l.
              apply msum_ext; intros; ring.
            * repeat split; auto; intros.
              apply lt_le_trans with q; try omega.
              apply power_ge_n; auto.
            * apply is_cipher_of_u; auto. }
          { rewrite H3.
            destruct l as [ | l' ]; try omega.
            rewrite msum_S, Nat.mul_0_l, Nat.add_0_l.
            rewrite msum_plus1; auto.
            rewrite plus_assoc.
            rewrite msum_S.
            rewrite <- msum_sum; auto.
            2: intros; ring.
            rewrite Nat.mul_1_l, plus_comm.
            repeat rewrite <- plus_assoc; do 2 f_equal.
            apply msum_ext; intros; ring. }
      + intros [ (H1 & H2 & H3) | (Hl & z & v & v1 & H1 & H2 & H3 & H4 & H5) ].
        - split; subst; auto; split; intros; try omega.
          rewrite msum_0; auto.
        - destruct H1 as (Hq & ? & ?); subst v v1.
          split; auto; split.
          { intros i Hi; apply lt_le_trans with q; try omega.
            apply power_ge_n; auto. }
          destruct H2 as (f & Hf).
          destruct H3 as (g & Hg).
          generalize (is_cipher_of_u Hq); intros Hu.
          rewrite cipher_mult_eq with (1 := Hg) (2 := Hu) in H4.
          destruct Hf as (_ & Hf & Hy).
          destruct Hg as (_ & Hg & Hz).
          set (h i := if le_lt_dec l i then l else f i).
          assert (y+l*power (power (S l) 2) r = ∑ (S l) (fun i => h i * power (power (S i) 2) r)) as H6.
          { rewrite msum_plus1; auto; f_equal.
            * rewrite Hy; apply msum_ext.
              intros i Hi; unfold h.
              destruct (le_lt_dec l i); try omega.
            * unfold h.
              destruct (le_lt_dec l l); try omega. }
          rewrite H4 in H6.
          set (g' i := match i with 0 => 0 | S i => g i end).
          assert ( ∑ (S l) (fun i => g' i * power (power (S i) 2) r)
                 = ∑ l (fun i : nat => g i * 1 * power (power (S (S i)) 2) r)) as H7.
          { unfold g'; rewrite msum_S; apply msum_ext; intros; ring. }
          rewrite <- H7 in H6.
          assert (forall i, i < S l -> g' i = h i) as H8.
          { apply power_decomp_unique with (5 := H6); try omega. 
            * intros; apply power_smono_l; omega. 
            * unfold g'; intros [ | i ] Hi; try omega.
              apply lt_S_n in Hi.
              apply lt_le_trans with (1 := Hg _ Hi), power_mono_l; omega.
            * intros i Hi; unfold h.
              destruct (le_lt_dec l i) as [ | Hi' ].
              + apply lt_le_trans with (4*q); try omega.
                apply power_ge_n; auto.
              + apply lt_le_trans with (1 := Hf _ Hi'), power_mono_l; omega.  }
          assert (h 0 = 0) as E0.
          { rewrite <- H8; simpl; omega. }
          assert (forall i, i < l -> h (S i) = g i) as E1.
          { intros i Hi; rewrite <- H8; simpl; omega. }
          assert (f 0 = 0) as E3.
          { unfold h in E0; destruct (le_lt_dec l 0); auto; omega. }
          assert (forall i, S i < l -> f (S i) = g i) as E4.
          { intros i Hi; specialize (E1 i); unfold h in E1.
            destruct (le_lt_dec l (S i)); omega. }
          assert (g (l-1) = l) as E5.
          { specialize (E1 (l-1)); unfold h in E1.
            destruct (le_lt_dec l (S (l-1))); omega. }  
          clear H6 H7 g' H8 E0 E1 h H4.
          assert (y + u1 + power (power 1 2) r = 
                  ∑ l (fun i => (1+f i) * power (power (S i) 2) r)
                + power (power (S l) 2) r) as E1.
          { rewrite sum_0n_distr_in_out.
            rewrite <- Hy, sum_0n_scal_l, Nat.mul_1_l.
            destruct l as [ | l' ]; try omega.
            rewrite msum_plus1; auto.
            rewrite msum_S; ring. }
          assert (forall i, i < l -> 1+f i = g i) as E2.
          { apply power_decomp_unique with (f := fun i => power (S i) 2) (p := r); try omega.
            + intros; apply power_smono_l; omega.
            + intros i Hi; apply le_lt_trans with (power q 2); auto.
              * apply Hf; auto.
              * apply power_smono_l; omega. 
            + intros i Hi; apply lt_le_trans with (1 := Hg _ Hi), power_mono_l; omega. } 
          rewrite Hy; apply msum_ext.
          clear Hy Hf Hg Hz H5 E5 E1 Hu.
          intros i Hi; f_equal; revert i Hi.
          induction i as [ | i IHi ]; intros Hi; auto.
          rewrite E4, <- E2; try omega.
          rewrite IHi; omega.
    Qed.

    Lemma CodeNat_dio y : CodeNat y <-> l = 0 /\ 1 < q /\ y = 0 
                                  \/ 0 < l 
                                  /\ exists z v v1 p0 p1 p2 r1,
                                        p0 = r
                                     /\ r1+1 = p0 
                                     /\ p1 = power (1+l) 2
                                     /\ p2 = power p1 p0 
                                     /\ seqs_of_ones v v1 
                                     /\ Code y
                                     /\ Code z
                                     /\ y + l*p2 = (z*v) ⇣ (r1 * v1)
                                     /\ y + v1 + p0*p0 = z + p2.
    Proof.
      rewrite IncSeq_dio_priv; split; (intros [ H | H ]; [ left | right ]); auto; revert H;
        intros (H1 & H); split; auto; clear H1; revert H.
      + intros (z & v & v1 & H1 & H2 & H3 & H4 & H5).
        exists z, v, v1, r, (power (S l) 2), (power (power (S l) 2) r), (r-1); repeat (split; auto).
        * destruct H1; omega.
        * rewrite <- H5; f_equal.
          rewrite power_1, power_S, power_1; auto.
      + intros (z & v & v1 & p0 & p1 & p2 & r1 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
        assert (r1 = r - 1) by omega; clear H2; subst.
        exists z, v, v1; repeat (split; auto).
        simpl in H9 |- *; rewrite <- H9; f_equal.
        rewrite power_1, power_S, power_1; auto.
    Qed.
      
  End inc_seq.

End sums.  

Check Code_plus_spec.
Check Code_mult_spec.
Check CodeNat_dio.
