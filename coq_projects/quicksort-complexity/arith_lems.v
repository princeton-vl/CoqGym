Set Implicit Arguments.
Unset Standard Proposition Elimination Names.

Require Import util.
Require Import Le.
Require Import Lt.
Require Import Rbase.
Require Import Plus.
Require Import Mult.
Require Import Arith.
Require Import Omega.
Require Import Div2.
Require Import Recdef.
Require Import Rbase.
Require Import Morphisms.

(* nat misc *)

Definition ltb (x y: nat): bool := negb (leb y x).
Definition geb (x y: nat): bool := leb y x.

Ltac subst_tac x y z := (* todo: rename *)
  match z with
  | x => y
  | ?l + ?r =>
      let l' := subst_tac x y l in
      let r' := subst_tac x y r in
        constr: (l' + r')
  | ?l * ?r =>
      let l' := subst_tac x y l in
      let r' := subst_tac x y r in
        constr: (l' * r')
  | _ => z
  end.

Ltac deep_le_trans h :=
  match type of h with
  | ?n <= ?u =>
    match goal with
    | |- ?l <= _ =>
      let q := subst_tac n u l
      in apply le_trans with q
    end
  end.

Instance Transitive_le: Transitive le := le_trans.

Lemma minus_plus_same (y x: nat): x <= x - y + y.
Proof. intros. omega. Qed.

Lemma ltb_complete m n: ltb m n = true -> m < n.
Proof with auto.
  unfold ltb.
  intros.
  apply leb_complete_conv.
  apply negb_inv...
Qed.

Lemma ltb_complete_conv m n: ltb m n = false -> n <= m.
Proof. unfold ltb. intros. apply leb_complete. apply negb_inv; auto. Qed.

Lemma lt_0_mult x y: 0 < x -> 0 < y -> 0 < x * y.
Proof with auto.
  destruct x.
    intros.
    inversion H.
  simpl.
  intros.
  apply lt_plus_trans...
Qed.

Lemma mult_ne_0 a b: (a <> 0 -> b <> 0 -> mult a b <> 0)%nat.
Proof with auto with arith.
  destruct a... destruct b...
  intros. simpl. discriminate.
Qed.

Lemma weak_lt_S_n n m: S n < m -> n < m.
Proof with auto with arith.
  intros.
  apply lt_S_n.
  apply lt_trans with m...
Qed.

Lemma le_exists_plus (x y: nat) (p: x <= y): exists d, y = x + d.
Proof with auto.
  induction p.
    exists 0...
  destruct IHp.
  exists (S x0).
  subst...
Qed.

Lemma lt_exists_plus (x y: nat) (p: x < y): exists d, y = S (x + d).
Proof.
  unfold lt in p.
  destruct (le_exists_plus p).
  exists x0.
  assumption.
Qed.

Lemma n_lt_n_plus_Sm n m: n < n + S m.
Proof. intros. omega. Qed.

Lemma ne_le_impl_lt x y: x <> y -> x <= y -> x < y.
Proof. auto with *. Qed.

Hint Rewrite plus_0_r : arith_norm.
Hint Rewrite mult_plus_distr_r mult_plus_distr_l plus_assoc : arith_norm.

Lemma beq_nat_false x y: x <> y -> beq_nat x y = false.
Proof with auto.
  intros.
  case_eq (beq_nat x y)...
  intros.
  elimtype False.
  apply H.
  apply beq_nat_eq...
Qed.

Lemma minus_lt_compat_l x y z: (y <= x -> z < y -> x - y < x - z)%nat.
Proof with auto.
  intros.
  omega.
Qed.

Lemma minus_eq_inv_r d x y: (x <= d -> y <= d -> (d - x = d - y) -> x = y)%nat.
Proof with auto with arith.
  revert x y.
  induction d.
    simpl.
    intros.
    destruct x...
    inversion H.
  simpl.
  intros.
  destruct x.
    destruct y...
    elimtype False.
    apply le_Sn_n with d...
    rewrite H1.
    apply le_minus.
  destruct y.
    elimtype False.
    apply le_Sn_n with d.
    rewrite <- H1.
    apply le_minus.
  apply eq_S.
  apply IHd...
Qed.

Lemma le_ne_lt x y: x <= y -> x <> y -> x < y.
Proof. intros. omega. Qed.

Lemma ne_nlt_lt x y: x <> y -> ~ x < y -> y < x.
Proof with auto.
  intros.
  destruct (le_gt_dec x y)...
  destruct (le_lt_eq_dec _ _ l)...
    elimtype False...
  elimtype False...
Qed.

Lemma lt_not_eq x y: (x < y -> x <> y)%nat.
Proof. intros. omega. Qed.

Lemma lt_not_eq_sym x y: (y < x -> x <> y)%nat.
Proof. intros. omega. Qed.

Hint Resolve lt_not_eq.
Hint Resolve lt_not_eq_sym.

(* sqrd *)

Definition sqrd n := n * n.

Lemma sqrd_S n: sqrd (S n) = sqrd n + n + n + 1.
Proof with auto with arith.
  induction n...
  rewrite IHn.
  clear IHn.
  unfold sqrd.
  ring.
Qed.

Lemma sqrd_plus x y: sqrd x + sqrd y <= sqrd (x + y).
Proof with auto with arith.
  intros.
  unfold sqrd.
  autorewrite with arith_norm...
Qed.

Lemma sqrd_le x y: x <= y -> sqrd x <= sqrd y.
  intros.
  unfold sqrd.
  apply mult_le_compat; auto.
Qed.

Hint Resolve sqrd_plus sqrd_le.

(* div2 properties *)

Lemma div2_preserves_le x y: x <= y -> div2 x <= div2 y.
Proof.
  rewrite !Nat.div2_div. now apply Nat.div_le_mono.
Qed.

Lemma Sdiv2_eq_div2SS x: S (div2 x) = div2 (S (S x)).
Proof. reflexivity. Qed.

Lemma div2S_le_Sdiv2 x: div2 (S x) <= S (div2 x).
Proof with auto with arith.
  destruct x...
  rewrite <- Sdiv2_eq_div2SS.
  apply -> Nat.succ_le_mono. apply div2_preserves_le...
Qed.

Lemma div2_x_plus_Sx b: div2 (b + S b) = b.
Proof with auto with arith.
  induction b...
  rewrite plus_Sn_m.
  rewrite <- plus_Snm_nSm.
  rewrite plus_Sn_m.
  simpl...
Qed.

Lemma div2_x_plus_2y a b: div2 (a + 2 * b) = div2 a + b.
Proof.
  rewrite !Nat.div2_div, Nat.mul_comm. now apply Nat.div_add.
Qed.

Lemma div2_sqrdSn n: div2 (sqrd n) + n <= div2 (sqrd (S n)).
Proof with auto with arith.
  intros.
  unfold sqrd.
  replace (S n * S n) with (n * n + 2 * n + 1) by ring.
  replace (div2 (n * n) + n) with (div2 (n * n + 2 * n)).
    apply div2_preserves_le...
  rewrite div2_x_plus_2y...
Qed.

Lemma le_div2 n: div2 n <= n.
Proof. apply Nat.div2_decr; auto with arith. Qed.

Lemma div2_lt_inv0 x y: div2 x < div2 y -> x < y.
Proof.
  rewrite !Nat.lt_nge. intros H H'. contradict H. now apply div2_preserves_le.
Qed.

Lemma div2_lt_inv x y: div2 x < div2 y -> x <= y.
Proof.
  intros. now apply Nat.lt_le_incl, div2_lt_inv0.
Qed.

Lemma div2_le_div2_inv x y: div2 x <= div2 y -> x <= S y.
Proof with auto with arith.
 destruct x as [|[|x]]...
 simpl. intros H. apply div2_lt_inv0 in H...
Qed.

Lemma div2_cancel n: div2 (2 * n) = n.
Proof with auto.
  induction n...
  simpl mult.
  rewrite <- plus_n_Sm.
  simpl in *...
Qed.

Lemma div2_le_inv x n: div2 x <= n -> x <= S (2 * n).
Proof. intros. rewrite <- (div2_cancel n) in H. apply (div2_le_div2_inv _ _ H). Qed.

(* pow *)

Fixpoint pow (b e: nat) {struct e}: nat :=
  match e with
  | 0 => 1
  | S e' => b * pow b e'
  end.

Lemma pow_S x y: pow x (S y) = x * pow x y.
Proof. auto. Qed.

Lemma pow_min x: x <> 0%nat -> forall y, 0 < pow x y.
Proof with auto with arith.
  intros H.
  induction y...
  simpl.
  apply lt_0_mult...
  destruct x...
Qed.

(* log2 *)

Function ceil_log2_S (n: nat) {wf lt n}: nat :=
  match n with
  | 0 => 0
  | S _ => S (ceil_log2_S (div2 n))
  end.
Proof.
  intros.
  apply lt_div2; auto with arith.
  apply lt_wf.
Defined.

Lemma ceil_log2_S_def n: ceil_log2_S n =
  match n with
  | 0 => 0
  | S _ => S (ceil_log2_S (div2 n))
  end.
Proof. functional induction (ceil_log2_S n); auto. Qed.

Definition log2ceil (n: nat): nat :=
  match n with
  | 0 => 0
  | S n' => ceil_log2_S n'
  end.

Function floor_log2_S (n: nat) {wf lt n}: nat :=
  match n with
  | 0 => 0
  | S n' => S (floor_log2_S (div2 n'))
  end.
Proof.
  intros.
  apply le_lt_trans with n'; auto with arith.
  apply le_div2.
  apply lt_wf.
Defined.

Lemma pow2_ceil_log2: forall n, S n <= pow 2 (ceil_log2_S n).
Proof with auto.
  intro.
  functional induction (ceil_log2_S n).
    simpl...
  rewrite pow_S.
  cset' (pow 2 (ceil_log2_S (div2 (S _x)))).
  destruct H.
    inversion IHn0.
  cset (le_S_n _ _ IHn0).
  cset (div2_le_inv (S _x) H0).
  omega.
Qed.

Lemma ceil_log2_Sn_le_n: forall n, ceil_log2_S n <= n.
Proof with auto with arith.
  intro.
  functional induction (ceil_log2_S n)...
  apply le_n_S.
  apply le_trans with (div2 (S _x))...
  apply lt_n_Sm_le.
  apply lt_div2...
Qed.

Lemma log2ceil_lt: forall n, 0 < n -> log2ceil n < n.
Proof with auto.
  destruct n...
  simpl.
  unfold lt.
  intros.
  apply le_n_S.
  apply ceil_log2_Sn_le_n.
Qed.

Lemma log2ceil_le: forall n, log2ceil n <= n.
Proof with auto with arith.
  destruct n...
  apply lt_le_weak.
  apply log2ceil_lt...
Qed.

Lemma log2ceil_S_preserves_le x y: x <= y -> ceil_log2_S x <= ceil_log2_S y.
Proof with auto with arith.
  revert y.
  functional induction (ceil_log2_S x)...
  intros.
  destruct y.
    inversion H.
  apply le_trans with (S (ceil_log2_S (div2 (S y)))).
    apply le_n_S...
    apply IHn.
    apply div2_preserves_le...
  rewrite (ceil_log2_S_def (S y))...
Qed.

Lemma log2ceil_preserves_le x y: x <= y -> log2ceil x <= log2ceil y.
Proof with auto with arith.
  destruct x.
    destruct y...
  destruct y.
    intros.
    inversion H.
  simpl.
  intros.
  apply log2ceil_S_preserves_le...
Qed.

(* INR comparisons *)

Lemma INR_S_ne_0 n: INR (S n) <> 0%R.
Proof. apply not_O_INR. discriminate. Qed.

Hint Resolve INR_S_ne_0.

Lemma O_le_inv_INR_S n: (0 <= / INR (S n))%R.
Proof. intros. apply Rlt_le. apply Rinv_0_lt_compat. apply lt_INR_0. auto with arith. Qed.

Hint Resolve O_le_inv_INR_S.

Lemma INR_0_inv n: INR n = 0%R -> n = 0.
Proof with auto.
  destruct n...
  intros.
  elimtype False.
  apply (INR_S_ne_0 _ H).
Qed.

Lemma O_lt_INR_S n: (0 < INR (S n))%R.
Proof. intros. apply lt_INR_0. auto with arith. Qed.

Hint Resolve O_lt_INR_S.

Require Import Fourier.

(* R misc *)

Ltac deep_Rle_trans h :=
  match type of h with
  | ?n <= ?u =>
    match goal with
    | |- (?l <= _)%R =>
      let q := subst_tac n u l
      in apply Rle_trans with q
    | _ => assert (False)
    end
  end.

Lemma Rmult_eq_compat_r (r r1 r2: R): (r1 = r2 -> r1 * r = r2 * r)%R.
Proof. intros. subst. reflexivity. Qed.

Lemma Rle_eq_trans x y z: (x <= y -> y = z -> x <= z)%R.
Proof. intros. fourier. Qed.

Lemma Req_ne_dec (x y: R): { x = y } + { x <> y }.
Proof with auto.
  intros.
  destruct (Rlt_le_dec x y).
    right. intro. subst. apply (Rlt_irrefl y)...
  destruct (Rle_lt_or_eq_dec _ _ r); [right | left]...
  intro. subst. apply (Rlt_irrefl y)...
Qed.

Lemma Rmult_0_inv (a b: R): (a * b)%R = 0%R -> (a = 0%R \/ b = 0%R).
Proof with auto with real.
  intros.
  destruct (Req_ne_dec a 0%R)...
    destruct (Req_ne_dec b 0%R).
    right...
  elimtype False.
  apply (prod_neq_R0 a b)...
Qed.

Lemma Req_le_trans x y z: x = y -> y <= z -> x <= z.
Proof. intros. subst. assumption. Qed.

Lemma Rle_plus_trans_l r a b c: a <= r -> r + b <= c -> a + b <= c.
Proof. intros. apply Rle_trans with (r + b); auto with real. Qed.

Lemma Rne_nlt_lt x y: x <> y -> ~ x < y -> y < x.
Proof with auto with real.
  intros.
  destruct (Rlt_le_dec x y)...
    elimtype False...
  destruct (Rle_lt_or_eq_dec y x r)...
  elimtype False...
Qed.

Lemma Rdiv_le_1 a b: 0 < a -> a <= b -> 1 <= b / a.
Proof with auto with real.
  intros.
  unfold Rdiv.
  rewrite <- (Rinv_r a)...
Qed.

Lemma Rdiv_lt_1 n m: 0 <= n -> n < m -> n / m < 1.
Proof with auto with real.
  unfold Rdiv.
  intros.
  rewrite <- (Rinv_r m)...
    apply Rmult_lt_compat_r...
    apply Rinv_0_lt_compat...
    fourier.
  intro.
  subst.
  apply (Rlt_not_le _ _ H0 H).
Qed.

Lemma zero_le_2_div_Sn n: 0 <= (2 * / INR (S n))%R.
Proof with auto with real.
  intros.
  unfold Rdiv...
  apply Rle_mult_inv_pos...
Qed.

Hint Resolve zero_le_2_div_Sn.

Definition bigO (f g: nat -> R): Prop := exists c, exists n, forall x, (n <= x)%nat -> f x <= c * g x.

Definition measured_bigO (X: Set) (m: X -> nat) (f: X -> R) (g: nat -> R): Prop
  := exists c, exists n, forall x, (n <= m x)%nat -> f x <= c * g (m x).

Notation "'over' m , f =O( g )" := (measured_bigO m f g).
