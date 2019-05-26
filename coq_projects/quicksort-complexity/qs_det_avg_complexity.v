Set Implicit Arguments.
Unset Standard Proposition Elimination Names.

Require Import
  Basics List Plus Program Morphisms Wf Wf_nat Omega
  qs_definitions monoid_monad_trans util list_utils sort_order nat_seqs
  insertion_sort arith_lems.
Require qs_det_parts.

(* We take as given an arbitrary decidable order: *)

Variable X: E.

(* The Quicksort we'll use is the monadic determinstic one that uses a partition pass, instantiated with the SimplyProfiled monad: *)

Definition counted_cmp (x y: X): SimplyProfiled comparison := (1%nat, Ecmp _ x y).

Let qs := mon_det_partition.qs _ counted_cmp.
Let part := mon_det_partition.partition _ counted_cmp.

(* By unfolding the (monadic) definition, we can characterize the cost and result of partitioning, and the cost of sorting: *)

Lemma partition_cost p l: cost (part p l) = length l.
Proof with auto.
  unfold cost.
  induction l...
  simpl.
  omega.
Qed.

Lemma partition_result c p l: proj1_sig (result (part p l)) c = filter (fun x => unsumbool (cmp_cmp (Ecmp _ x p) c)) l.
Proof with auto.
  induction l.
    simpl...
  simpl...
  destruct (cmp_cmp (Ecmp _ a p) c)...
  simpl.
  rewrite <- IHl...
Qed.

Lemma cost_qs l: cost (qs l) =
  match l with
  | nil => 0
  | h :: t => length t + cost (qs (filter (Egtb h) t)) + cost (qs (filter (Eltb h) t))
  end.
Proof with auto.
  pattern l, (qs l).
  apply (qs_det_parts.rect counted_cmp SimplyProfiled_ext)...
  intros.
  unfold qs_det_parts.partitionPart.
  rewrite bind_cost.
  rewrite partition_cost.
  unfold qs_det_parts.lowRecPart.
  repeat rewrite bind_cost.
  rewrite return_cost.
  rewrite <- plus_assoc.
  f_equal.
  do 2 rewrite partition_result.
  rewrite plus_0_r.
  unfold qs.
  do 3 f_equal; apply filter_eq_morphism...
    intro...
    rewrite Ecmp_sym.
    unfold Egtb.
    destruct (Ecmp X h a)...
  intro...
  unfold Eltb.
  rewrite Ecmp_sym.
  destruct (Ecmp X h a)...
Qed.

(* Since cost_qs tells us all we need to know about qs (for the purposes of proving its average case complexity),
 we will not need any further monad reasoning. We will need some R stuff: *)

Require Import sums_and_averages Rdefinitions Fourier Exp_prop.
Coercion INR: nat >-> R.
Hint Resolve Rmult_lt_0_compat Rmult_lt_0_compat Rinv_0_lt_compat Rle_Rinv: real.

(* We now define the recurrence relation *)

Inductive CR: nat -> R -> Prop :=
  | C0: CR 0 0
  | Cn n (l: list R): elemsR CR (nats 0 (S n)) l -> CR (S n) (n + 2 * Ravg l).

Hint Constructors CR.

(* .. and note that it is a function: *)

Lemma CRuniq: forall n r, CR n r -> forall r', CR n r' -> r = r'.
Proof with auto.
  intro n. pattern n.
  apply (well_founded_ind lt_wf).
  intros.
  destruct x. inversion_clear H0. inversion_clear H1...
  inversion_clear H0.
  inversion_clear H1.
  rewrite (@elemsRuniq _ _ CR (nats 0 (S x))) with l l0...
  intros.
  apply H with x0...
  destruct (In_nats_inv _ _ _ H1)...
Qed.

(* .. which is even computable: *)

Lemma CRimpl: forall n (a: Acc lt n), sig (CR n).
Proof with eauto.
  refine (fix F n (a: Acc lt n) {struct a} :=
    match a with
    | Acc_intro x =>
      let Re := fun m (p: lt m n) => F m (x m p)  in _
    end).
  clearbody Re. clear F.
  destruct n...
  destruct (elemsRimpl CR (nats 0 (S n)))...
  intros.
  destruct (In_nats_inv _ _ _ H)...
Qed.

Definition C n: R := proj1_sig (CRimpl (lt_wf n)).

(* .. and which satisfies the following recursive equation: *)

Lemma Ceq n: C n =
  match n with
  | 0 => 0
  | _ => pred n + 2 * Ravg (map C (nats 0 n))
  end.
Proof with auto.
  unfold C at 1.
  destruct CRimpl.
  simpl proj1_sig.
  induction c...
  simpl pred.
  f_equal.
  f_equal.
  f_equal.
  generalize H. clear H.
  generalize (nats 0 (S n)). intro.
  generalize l0. clear n l0.
  induction l; intros; inversion_clear H...
  simpl.
  rewrite <- IHl...
  unfold C.
  destruct CRimpl.
  f_equal.
  apply (CRuniq H0 c).
Qed.

(* .. as well as some other properties: *)

Lemma C_nonneg n: 0 <= C n.
Proof with auto with real.
  pattern n.
  apply (well_founded_ind lt_wf).
  intros.
  rewrite Ceq.
  destruct x...
  simpl pred.
  apply Rplus_le_le_0_compat...
  apply Rmult_le_pos...
  apply Rmult_le_pos...
    apply Rsum_nonneg.
    intros.
    apply in_map_iff in H0. destruct H0. destruct H0. subst.
    apply H.
    destruct (In_nats_inv _ _ _ H1)...
  rewrite map_length. rewrite nats_length...
Qed.

Lemma C_S n: C n = 2 * pred n / n + S n / n * C (pred n).
Proof with auto with real.
  assert (forall n, C (S n) = n + 2 * Ravg (map C (nats 0 (S n)))).
    intros.
    rewrite Ceq.
    simpl pred...
  assert (forall n, C n * n = n * pred n + 2 * Rsum (map C (nats 0 n))).
    destruct n0.
      simpl. field.
    rewrite H.
    unfold Ravg.
    rewrite map_length, nats_length.
    unfold Rdiv.
    rewrite Rmult_plus_distr_r.
    rewrite Rmult_assoc.
    rewrite Rmult_assoc.
    rewrite Rinv_l...
    rewrite Rmult_1_r...
  assert (forall n, C (S n) * S n = S n * n + 2 * C n - n * pred n + C n * n).
    intros.
    rewrite H0.
    rewrite H0.
    simpl pred.
    rewrite nats_Sw'.
    rewrite map_app.
    rewrite Rsum_app.
    simpl Rsum at 2.
    rewrite Rplus_0_r.
    rewrite plus_0_r.
    field.
  assert (forall n, C (S n) * S n = (2+n) * C n + 2 * n).
    destruct n0.
      simpl.
      rewrite Ceq.
      simpl.
      rewrite Ravg_single.
      rewrite Ceq.
      field.
    rewrite H1.
    simpl pred.
    repeat rewrite S_INR.
    field.
  destruct n.
    simpl.
    rewrite Ceq.
    repeat rewrite Rmult_0_r.
    unfold Rdiv.
    rewrite Rmult_0_l...
  simpl pred.
  apply Rmult_eq_reg_l with (S n)...
  rewrite Rmult_comm.
  rewrite H2.
  repeat rewrite S_INR.
  field...
Qed. (* todo: get rid of ugly asserts *)

Lemma C_le_compat n m: le n m -> C n <= C m.
Proof with auto with real.
  intros H.
  induction H...
  apply Rle_trans with (C m)...
  rewrite (C_S (S m)).
  simpl pred.
  rewrite <- (Rplus_0_l (C m)) at 1.
  apply Rplus_le_compat.
    unfold Rdiv.
    rewrite S_INR...
    apply Rmult_le_pos...
    apply Rmult_le_pos...
  rewrite <- (Rmult_1_l (C m)) at 1.
  apply Rmult_le_compat_r...
    apply C_nonneg.
  rewrite S_INR.
  apply Rdiv_le_1...
Qed.

(* C is bounded by prefixes of the harmonic series: *)

Hint Resolve Rplus_le_le_0_compat.

Lemma C_bounded_by_harmonic n: C n <= n * 2 * Rsum (map (Rinv ∘ INR) (nats 2 (pred n))).
Proof with try field; auto with real.
  induction n.
    rewrite Ceq...
  apply Rmult_le_reg_l with (/ S n)...
  repeat rewrite <- Rmult_assoc.
  rewrite Rinv_l...
  rewrite Rmult_1_l.
  destruct n.
    simpl.
    rewrite Ceq.
    simpl.
    rewrite Ravg_single.
    rewrite Ceq.
    fourier.
  simpl pred in *.
  rewrite nats_Sw'.
  rewrite map_app, Rsum_app, map_single, Rsum_single.
  set (bla := S n) in *.
  rename n into m. rename bla into n.
  assert (0 < n). subst n. replace 0 with (INR O)...
  apply Rmult_le_reg_l with n...
  rewrite Rmult_plus_distr_l.
  rewrite Rmult_plus_distr_l.
  rewrite plus_comm...
  simpl plus...
  unfold compose at 2.
  rewrite <- (Rmult_assoc n 2).
  fold n.
  apply Rle_trans with (C n + n * (2 * / S n))...
  rewrite (C_S (S n)).
  simpl pred.
  repeat rewrite <- Rmult_assoc.
  rewrite Rmult_plus_distr_l.
  unfold Rdiv.
  repeat rewrite <- Rmult_assoc.
  rewrite Rplus_comm.
  apply Rplus_le_compat.
    rewrite <- (Rmult_1_l (C n)) at 2.
    apply Rmult_le_compat_r...
      apply C_nonneg.
    repeat rewrite S_INR.
    replace (n * / (n + 1) * (n + 1 + 1) * / (n + 1)) with ((n * n + n + n) * / (n * n + n + n + 1)).
      apply Rlt_le.
      apply Rdiv_lt_1...
    field...
    split...
    apply Rgt_not_eq.
    unfold Rgt.
    apply Rle_lt_trans with (n * n + n + n)...
  apply Rmult_le_compat_r...
  rewrite (Rmult_comm n 2).
  apply Rmult_le_compat_r...
  rewrite <- (Rmult_1_l 2) at 2.
  apply Rmult_le_compat_r...
  apply Rlt_le...
  apply Rdiv_lt_1...
Qed.

(* Consequently, we can use an existing result about the harmonic series to get
 the n*log(n) bound for C: *)

Require harmonic.

Lemma C_log_bound n: C n <= n * 2 * log2ceil n.
Proof with auto with real.
  intros.
  apply Rle_trans with (n * 2 * Rsum (map (Rinv ∘ INR) (nats 2 (pred n)))).
    apply C_bounded_by_harmonic.
  apply Rmult_le_compat_l.
    apply Rmult_le_pos...
  destruct n.
    simpl...
  simpl pred.
  replace (Rsum (map (Rinv ∘ INR) (nats 2 n))) with (Rsum (map (Rinv ∘ INR) (nats 1 (S n))) - 1).
    Focus 2.
    simpl.
    unfold compose at 1.
    simpl.
    rewrite Rinv_1.
    field.
  replace (INR (log2ceil (S n))) with (S (log2ceil (S n)) - 1).
    unfold Rminus.
    apply Rplus_le_compat_r.
    apply harmonic.upper_bound.
  rewrite S_INR.
  field.
Qed.

(* What remains is to show that the average cost of qs is bounded by C: *)

Lemma C_bounds_avg_qs_cost: forall l, Ravg (map (INR ∘ cost ∘ qs) (perms l)) <= C (length l).
Proof with auto with real.
  apply (well_founded_induction_type (Wf_nat.well_founded_ltof _ (@length X))).
  intros.
  unfold ltof in H.
  destruct x.
    unfold Basics.compose.
    simpl.
    rewrite Ravg_single...
    rewrite Ceq...
  rewrite (Ravg_Permutation (Permutation.Permutation_map (INR ∘ cost ∘ qs) (perms_alt_perms (e :: x)))).
  unfold alt_perms.
  set (e :: x) in *.
  rename x into t. rename e into h.
  rewrite map_concat.
  rewrite map_map.
  rewrite (@Ravg_concat (fact (pred (length l)))).
    Focus 2.
    intros.
    destruct (fst (conj_prod (in_map_iff _ _ _)) H0).
    destruct H1.
    subst.
    rewrite map_length.
    rewrite map_length.
    rewrite length_perms.
    replace (length (snd x)) with (pred (S (length (snd x))))...
    rewrite (length_in_splits _ _ H2)...
  rewrite map_map.
  replace (map
       (fun x =>
        Ravg (map (INR ∘ cost ∘ qs) (map (cons (fst x)) (perms (snd x)))))
       (splits l))
     with (map (fun x =>
        Ravg (map (INR ∘ @length _) (perms (snd x))) +
        Ravg (map (INR ∘ cost ∘ qs ∘ filter (Egtb (fst x))) (perms (snd x))) +
        Ravg (map (INR ∘ cost ∘ qs ∘ filter (Eltb (fst x))) (perms (snd x)))
         ) (splits l)).
    Focus 2.
    apply map_ext.
    intros.
    rewrite map_map.
    unfold Basics.compose.
    replace (map (fun x => INR (cost (qs (fst a :: x)))) (perms (snd a))) with
     (map (fun x => length x + cost (qs (filter (Egtb (fst a)) x)) + cost (qs (filter (Eltb (fst a)) x))) (perms (snd a))).
      rewrite Ravg_map_plus.
      rewrite Ravg_map_plus...
    apply map_ext. intros.
    rewrite (cost_qs (fst a :: a0)).
    repeat rewrite plus_INR...
  rewrite Ravg_map_plus.
  rewrite Ravg_map_plus.
  setoid_rewrite (avg_filter_perms (cost ∘ qs)).
  replace (Ravg
    (map (fun x => Ravg (map (INR ∘ @length _) (perms (snd x))))
     (splits l))) with (INR (pred (length l))).
    Focus 2.
    symmetry.
    apply Ravg_constant.
      apply length_ne_0_ne_nil.
      rewrite map_length, length_splits.
      discriminate.
    intros.
    destruct (fst (conj_prod (in_map_iff _ _ _)) H0).
    destruct H1.
    subst.
    apply Ravg_constant.
      apply length_ne_0_ne_nil.
      rewrite map_length, length_perms.
      apply fact_neq_0.
    intros.
    destruct (fst (conj_prod (in_map_iff _ _ _)) H1).
    destruct H3. subst.
    unfold Basics.compose.
    rewrite <- (length_in_splits _ _ H2).
    rewrite (perms_are_perms _ _ H4)...
  apply Rle_trans with
     (pred (length l) +
     Ravg (map (fun x => C (length (filter (Egtb (fst x)) (snd x)))) (splits l)) +
     Ravg (map (fun x => C (length (filter (Eltb (fst x)) (snd x)))) (splits l))).
    apply Rplus_le_compat...
      apply Rplus_le_compat...
      apply Ravg_map_le.
      intros.
      apply H...
      apply le_lt_trans with (length (snd x)).
        apply list_utils.length_filter_le.
      rewrite <- (length_in_splits _ _ H0)...
    apply Ravg_map_le.
    intros.
    apply H...
    apply le_lt_trans with (length (snd x)).
      apply list_utils.length_filter_le.
    rewrite <- (length_in_splits _ _ H0)...
  clear H.
  rewrite Rplus_assoc.
  rewrite <- (map_map (fun x => length (filter (Egtb (fst x)) (snd x))) C (splits l)).
  rewrite <- (map_map (fun x => length (filter (Eltb (fst x)) (snd x))) C (splits l)).
  rewrite <- (map_length_filter_permuted_splits (plain.isort_permutes Eleb l)).
  rewrite <- (map_length_filter_permuted_splits (plain.isort_permutes Egeb l)).
  unfold Ravg.
  repeat rewrite map_length.
  repeat rewrite length_splits.
  rewrite (Permutation.Permutation_length (plain.isort_permutes Egeb l)).
  rewrite (Permutation.Permutation_length (plain.isort_permutes Eleb l)).
  unfold Rdiv.
  rewrite <- Rmult_plus_distr_r.
  apply Rle_trans with (pred (length l) +
      (Rsum (map C (nats 0 (length l))) + Rsum (map C (nats 0 (length l)))) / length l).
    apply Rplus_le_compat_l.
    unfold Rdiv.
    apply Rmult_le_compat_r...
      apply Rlt_le, Rinv_0_lt_compat, (lt_INR 0 (S (length t)))...
    apply Rplus_le_compat.
      apply elemsR_le_Rsum.
      apply elemsR_map' with le...
        apply C_le_compat.
      rewrite <- (Permutation.Permutation_length (plain.isort_permutes Eleb l)).
      apply (@filtered_sort X Ele EO).
        unfold Egtb, Ele.
        intros.
        destruct (Ecmp _ y x); try discriminate...
      apply plain.isort_sorts'.
          unfold Eleb. intros. rewrite Ecmp_sym. destruct Ecmp...
        apply Eleb_preorder.
      intros. apply <- (Eleb_true x y)...
    apply elemsR_le_Rsum.
    apply elemsR_map' with le...
      apply C_le_compat.
    rewrite <- (Permutation.Permutation_length (plain.isort_permutes Egeb l)).
    apply (@filtered_sort X Ege Ege_preorder).
      unfold Eltb, Ege.
      intros.
      destruct (Ecmp _ y x); try discriminate...
    apply plain.isort_sorts'.
        unfold Egeb.
        intros. rewrite Ecmp_sym. destruct Ecmp...
      apply Egeb_preorder.
    intros. apply <- (Egeb_true x y)...
  rewrite <- (Rmult_1_l (Rsum (map C (nats 0 (length l))))).
  rewrite <- Rmult_plus_distr_r.
  unfold Rdiv.
  rewrite Rmult_assoc.
  rewrite Ceq.
  destruct (length l).
    simpl.
    rewrite Rmult_0_l.
    fourier.
  simpl pred.
  unfold Rdiv.
  apply Rplus_le_compat_l.
  unfold Ravg. rewrite map_length. rewrite nats_length.
  unfold Rdiv...
Qed.

(* The main result is now just a matter of sequencing the previous two lemmas. *)

Theorem qs_avg l: Ravg (map (INR ∘ cost ∘ qs) (perms l)) <= length l * 2 * log2ceil (length l).
Proof with auto with real.
  intros.
  apply Rle_trans with (C (length l)).
    apply C_bounds_avg_qs_cost.
  apply C_log_bound.
Qed.

Corollary qs_avg_bigO: over (@length (_ : Set)), Ravg ∘ map (INR ∘ cost ∘ qs) ∘ perms =O(fun n => n * log2ceil n).
Proof with auto with real.
  unfold measured_bigO.
  exists 2.
  exists 0%nat.
  intros.
  unfold compose at 1.
  unfold compose at 1.
  apply Rle_trans with (length x * 2 * log2ceil (length x)).
    apply qs_avg.
  rewrite (Rmult_comm (length x))...
Qed.

Print Assumptions qs_avg_bigO.

(* one gotcha: perms [x; x] = [[x; x]; [x; x]] *)
