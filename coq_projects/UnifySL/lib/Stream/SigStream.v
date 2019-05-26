Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Export Coq.Logic.Classical.
Require Export Coq.Logic.Classical_Prop.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Classes.Equivalence.
Require Export Coq.Classes.Morphisms.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.NatChoice.

Definition stream (A: Type): Type := {h: nat -> option A | forall x y, x < y -> h x = None -> h y = None}.

Definition stream_get {A: Type} (h: stream A) (n: nat) := proj1_sig h n.

Coercion stream_get: stream >-> Funclass.

Lemma stream_sound1: forall {A: Type} (h: stream A) (x y: nat), x <= y -> h x = None -> h y = None.
Proof.
  intros ? [h ?] ? ? ?.
  destruct H; auto; simpl.
  apply (e x (S m)).
  omega.
Qed.

Lemma stream_sound2: forall {A: Type} (h: stream A) (x y: nat), x <= y -> (exists a, h y = Some a) -> (exists a, h x = Some a).
Proof.
  intros.
  pose proof stream_sound1 h x y H.
  destruct (h x), (h y), H0; eauto.
  specialize (H1 eq_refl).
  congruence.
Qed.

Lemma stream_extensionality {A: Type}: forall h1 h2: stream A, (forall n, h1 n = h2 n) -> h1 = h2.
Proof.
  intros.
  destruct h1 as [h1 ?H], h2 as [h2 ?H]; simpl in *.
  assert (h1 = h2) by (extensionality n; auto).
  subst h2.
  assert (H0 = H1) by (apply proof_irrelevance).
  subst H1.
  auto.
Qed.

Tactic Notation "stream_extensionality" ident(x) :=
  match goal with
    [ |- ?X = ?Y ] =>
     apply stream_extensionality; intro x
  end.

Definition is_n_stream {A: Type} (n: nat) (h: stream A): Prop :=
  h n = None /\ forall n', n' < n -> h n' <> None.

Definition is_fin_stream {A: Type} (h: stream A): Prop :=
  exists n, h n = None.

Definition is_inf_stream {A: Type} (h: stream A): Prop :=
  forall n, h n <> None.

Definition is_at_least_n_stream {A: Type} (n: nat) (h: stream A): Prop :=
  forall n', n' < n -> h n' <> None.

Definition is_at_most_n_stream {A: Type} (n: nat) (h: stream A): Prop :=
  h n = None.

Definition is_empty_stream {A: Type}: stream A -> Prop :=
  is_n_stream 0.

Lemma n_stream_inf_stream_conflict {A: Type}: forall (h: stream A) (n: nat),
  is_n_stream n h ->
  is_inf_stream h ->
  False.
Proof.
  intros.
  destruct H.
  exact (H0 _ H).
Qed.

Lemma is_n_stream_pf {A: Type}: forall (h: stream A) (n m: nat),
  is_n_stream m h ->
  is_n_stream n h ->
  n = m.
Proof.
  intros ?.
  assert (forall n m, n < m -> is_n_stream m h -> is_n_stream n h -> False).
  Focus 1. {
    intros.
    destruct H0, H1.
    specialize (H2 n H).
    congruence.
  } Unfocus.
  intros; destruct (lt_eq_lt_dec n m) as [[?H | ?H] | ?H].
  + specialize (H _ _ H2 H0 H1); contradiction.
  + auto.
  + specialize (H _ _ H2 H1 H0); contradiction.
Qed.

Lemma at_most_n_stream_Sn {A: Type}: forall (h: stream A) (n: nat),
  is_at_most_n_stream (S n) h <->
  is_at_most_n_stream n h \/ is_n_stream (S n) h.
Proof.
  intros.
  split; [intro | intros [? | ?]].
  + destruct (h n) eqn:?H.
    - right.
      split; auto.
      intros; intro.
      rewrite (stream_sound1 h n' n) in H0 by (auto; omega).
      congruence.
    - left.
      auto.
  + hnf in H |- *.
    rewrite (stream_sound1 h n (S n)) by (auto; omega).
    auto.
  + destruct H; auto.
Qed.

Lemma at_most_n_stream_0 {A: Type}: forall (h: stream A),
  is_at_most_n_stream 0 h <-> is_n_stream 0 h.
Proof.
  intros; split; intros.
  + split; auto.
    intros; omega.
  + destruct H; auto.
Qed.

Lemma at_most_n_stream_spec {A: Type}: forall (h: stream A) (n: nat),
  is_at_most_n_stream n h <->
  exists m, m <= n /\ is_n_stream m h.
Proof.
  intros.
  induction n.
  + rewrite at_most_n_stream_0.
    split; intros.
    - exists 0; split; [omega | auto].
    - destruct H as [m [? ?]].
      replace m with 0 in H0 by omega.
      auto.
  + rewrite at_most_n_stream_Sn.
    rewrite IHn.
    split; intros.
    - destruct H as [[m [? ?]] | ?].
      * exists m; split; [omega | auto].
      * exists (S n); split; [omega | auto].
    - destruct H as [m [? ?]].
      destruct (le_gt_dec m n).
      * left; exists m; split; auto.
      * right.
        replace (S n) with m by omega.
        auto.
Qed.

Lemma is_fin_stream_spec {A}: forall (h: stream A),
  is_fin_stream h <-> exists n, is_n_stream n h.
Proof.
  intros.
  split; intro.
  + destruct H as [n ?].
    apply at_most_n_stream_spec in H.
    destruct H as [m [? ?]].
    exists m; auto.
  + destruct H as [n [? ?]].
    exists n; auto.
Qed.

Lemma at_most_n_stream_mono {A: Type}: forall (h: stream A) (n m: nat),
  n <= m ->
  is_at_most_n_stream n h ->
  is_at_most_n_stream m h.
Proof.
  intros.
  rewrite at_most_n_stream_spec in H0 |- *.
  destruct H0 as [m0 [? ?]].
  exists m0.
  split; [omega | auto].
Qed.

Lemma at_most_n_stream_is_fin_stream {A: Type}: forall (h: stream A) (n: nat),
  is_at_most_n_stream n h ->
  is_fin_stream h.
Proof.
  intros.
  rewrite at_most_n_stream_spec in H.
  rewrite is_fin_stream_spec.
  destruct H as [m [? ?]].
  exists m; auto.
Qed.

Lemma n_stream_or_inf_stream {A: Type}: forall (h: stream A),
  (exists n, is_n_stream n h) \/ is_inf_stream h.
Proof.
  intros.
  destruct (classic (is_fin_stream h)).
  + left.
    rewrite is_fin_stream_spec in H.
    auto.
  + right.
    hnf; intros; intro.
    apply H; clear H.
    exists n; auto.
Qed.

Lemma at_least_n_stream_Sn {A: Type}: forall (h: stream A) (n: nat),
  is_at_least_n_stream (S n) h <->
  is_at_least_n_stream n h /\ ~ is_n_stream n h.
Proof.
  intros.
  split; [intro | intros [? ?]].
  + split.
    - hnf in H |- *.
      intros; apply H; omega.
    - intros [? ?].
      exact (H n (le_n _) H0).
  + hnf in H |- *.
    intros; intro.
    apply H0; clear H0.
    split.
    - specialize ((fun HH => H n' HH H2): ~ n' < n).
      replace n with n' by omega; auto.
    - intros; apply H; auto.
Qed.

Lemma at_least_n_stream_0 {A: Type}: forall (h: stream A),
  is_at_least_n_stream 0 h <-> True.
Proof.
  intros.
  split; auto.
  intros _.
  hnf; intros.
  omega.
Qed.

Lemma at_least_n_stream_spec {A: Type}: forall (h: stream A) (n: nat),
  is_at_least_n_stream n h <->
  (exists m, m >= n /\ is_n_stream m h) \/ is_inf_stream h.
Proof.
  intros.
  induction n.
  + rewrite at_least_n_stream_0.
    split; auto; intros _.
    destruct (n_stream_or_inf_stream h) as [[m ?] | ?].
    - left; exists m; split; [omega | auto].
    - right; auto.
  + rewrite at_least_n_stream_Sn.
    rewrite IHn.
    split; intros.
    - destruct H as [[[m [? ?]] | ?] ?].
      * left; exists m; split; [| auto].
        destruct (Nat.eq_dec m n); [subst; tauto | omega].
      * right; auto.
    - destruct H as [[m [? ?]] | ?].
      * split.
       ++ left; exists m; split; [omega | auto].
       ++ intro.
          pose proof (is_n_stream_pf _ _ _ H0 H1).
          omega.
      * split.
       ++ right; auto.
       ++ intros [? ?].
          exact (H _ H0).
Qed.

Lemma is_inf_stream_spec {A}: forall (h: stream A),
  is_inf_stream h <-> forall n, ~ is_n_stream n h.
Proof.
  intros.
  split; intro.
  + intros.
    intros [? ?].
    exact (H _ H0).
  + destruct (n_stream_or_inf_stream h) as [[m ?] | ?]; [| auto].
    exfalso.
    exact (H _ H0).
Qed.

Lemma at_least_n_stream_mono {A: Type}: forall (h: stream A) (n m: nat),
  n <= m ->
  is_at_least_n_stream m h ->
  is_at_least_n_stream n h.
Proof.
  intros.
  rewrite at_least_n_stream_spec in H0 |- *.
  destruct H0 as [[m0 [? ?]] | ?].
  + left; exists m0.
    split; [omega | auto].
  + right; auto.
Qed.

Lemma inf_stream_is_at_least_n_stream_is_fin_stream {A: Type}: forall (h: stream A) (n: nat),
  is_inf_stream h ->
  is_at_least_n_stream n h.
Proof.
  intros.
  rewrite at_least_n_stream_spec.
  auto.
Qed.

Lemma at_most_n_stream_or_at_least_Sn_stream {A: Type}: forall (h: stream A) (n: nat),
  is_at_most_n_stream n h \/ is_at_least_n_stream (S n) h.
Proof.
  intros.
  destruct (n_stream_or_inf_stream h) as [[m ?] | ?]; [destruct (lt_dec n m) |].
  + right.
    rewrite at_least_n_stream_spec.
    left; exists m.
    split; [omega | tauto].
  + left.
    rewrite at_most_n_stream_spec.
    exists m.
    split; [omega | tauto].
  + right.
    rewrite at_least_n_stream_spec.
    right; auto.
Qed.

Lemma at_most_n_stream_or_at_least_n_stream {A: Type}: forall (h: stream A) (n: nat),
  is_at_most_n_stream n h \/ is_at_least_n_stream n h.
Proof.
  intros.
  destruct (at_most_n_stream_or_at_least_Sn_stream h n).
  + left; auto.
  + right.
    eapply at_least_n_stream_mono; [| eassumption].
    omega.
Qed.

(*
Definition stream_coincide {A: Type} (n: nat) (h1 h2: stream A): Prop :=
  forall m, m < n -> h1 m = h2 m.

Definition stream_app {A: Type} (h1 h2 h: stream A): Prop :=
  exists n,
    h1 n = None /\
    stream_coincide n h1 h /\
    (forall m, h (m + n) = h2 m).

Definition prefix_stream {A: Type} (h1 h2: stream A): Prop :=
  forall n, h1 n = None \/ h1 n = h2 n.

Definition strict_prefix_stream {A: Type} (h1 h2: stream A): Prop :=
  prefix_stream h1 h2 /\ exists n, h1 n <> h2 n.

Definition n_bounded_prefix_stream {A: Type} (m: nat) (h1 h2: stream A): Prop :=
  forall n, (h1 n = None /\ h2 (n + m) = None) \/ h1 n = h2 n.

Lemma stream_coincide_sym {A: Type}: forall (h1 h2: stream A) n,
  stream_coincide n h1 h2 ->
  stream_coincide n h2 h1.
Proof.
  intros.
  hnf; intros.
  specialize (H m H0); congruence.
Qed.

Lemma stream_coincide_trans {A: Type}: forall (h1 h2 h3: stream A) n,
  stream_coincide n h1 h2 ->
  stream_coincide n h2 h3 ->
  stream_coincide n h1 h3.
Proof.
  intros.
  hnf; intros.
  specialize (H m H1);
  specialize (H0 m H1); congruence.
Qed.

Lemma stream_coincide_weaken {A: Type}: forall n m (h1 h2: stream A),
  n <= m ->
  stream_coincide m h1 h2 ->
  stream_coincide n h1 h2.
Proof.
  intros.
  intros n0 ?.
  apply H0.
  omega.
Qed.

Lemma is_n_stream_None {A: Type}: forall n m (h: stream A), n <= m -> is_n_stream n h -> h m = None.
Proof.
  intros.
  destruct H0.
  apply (stream_sound1 h n m); auto.
Qed.

Lemma fstn_stream_coincide {A: Type}: forall n (h: stream A),
  stream_coincide n h (fstn_stream n h).
Proof.
  intros.
  intros m ?.
  rewrite fstn_stream_Some by omega.
  auto.
Qed.

Lemma prefix_stream_refl {A: Type}: forall (h: stream A), prefix_stream h h.
Proof.
  intros.
  hnf; intros.
  right; auto.
Qed.

Lemma prefix_stream_trans {A: Type}: forall (h1 h2 h3: stream A), prefix_stream h1 h2 -> prefix_stream h2 h3 -> prefix_stream h1 h3.
Proof.
  intros.
  hnf in H, H0 |- *; intros.
  specialize (H n); specialize (H0 n).
  destruct H, H0.
  + left; auto.
  + left; auto.
  + left; congruence.
  + right; congruence.
Qed.

Lemma prefix_stream_anti_sym {A: Type}: forall (h1 h2: stream A), prefix_stream h1 h2 -> prefix_stream h2 h1 -> h1 = h2.
Proof.
  intros.
  stream_extensionality n.
  hnf; intros.
  specialize (H n); specialize (H0 n).
  destruct H, H0; congruence.
Qed.

Lemma prefix_stream_comparable {A: Type}: forall (h1 h2 h: stream A), prefix_stream h1 h -> prefix_stream h2 h -> prefix_stream h1 h2 \/ prefix_stream h2 h1.
Proof.
  intros.
  destruct (classic (exists n, h1 n <> h2 n /\ h1 n <> None)); [right | left].
  + hnf; intros.
    destruct H1 as [m [? ?]].
    destruct (H0 n); [auto |].
    destruct (H n); [| right; congruence].
    assert (m < n).
    Focus 1. {
      destruct (le_dec n m); try omega.
      exfalso; apply H2.
      eapply stream_sound1; eauto.
    } Unfocus.
    destruct (H m); [congruence |].
    destruct (H0 m); [| congruence].
    left.
    apply stream_sound1 with m; auto. omega.
  + hnf; intros n.
    destruct (classic (h1 n = None)), (classic (h1 n = h2 n)); try tauto.
    exfalso.
    apply H1.
    eexists; eauto.
Qed.

Lemma fstn_stream_finite {A: Type}: forall n (h: stream A), is_fin_stream (fstn_stream n h).
Proof.
  intros.
  exists n.
  rewrite fstn_stream_None; auto.
Qed.

Lemma fstn_stream_prefix {A: Type}: forall n (h: stream A), prefix_stream (fstn_stream n h) h.
Proof.
  intros.
  hnf; intros m.
  destruct (le_dec n m).
  + rewrite fstn_stream_None; auto.
  + rewrite fstn_stream_Some; auto.
    omega.
Qed.

Lemma prefix_stream_coincide {A: Type}: forall n (h1 h2: stream A),
  prefix_stream h1 h2 ->
  is_at_least_n_stream n h1 ->
  stream_coincide n h1 h2.
Proof.
  intros.
  hnf; intros.
  specialize (H m).
  specialize (H0 m H1).
  tauto.
Qed.

Lemma is_at_least_n_stream_fstn_stream {A: Type}: forall n m (h: stream A), n <= m -> (is_at_least_n_stream n (fstn_stream m h) <-> is_at_least_n_stream n h).
Proof.
  intros.
  split; intros; hnf; intros.
  + specialize (H0 n' H1).
    rewrite fstn_stream_Some in H0 by omega.
    auto.
  + specialize (H0 n' H1).
    rewrite fstn_stream_Some by omega.
    auto.
Qed.

Lemma squeeze_stream_coincide {A: Type}: forall n (h1 h2: stream A),
  prefix_stream (fstn_stream n h1) h2 ->
  prefix_stream h2 h1 ->
  stream_coincide n h1 h2.
Proof.
  intros.
  hnf; intros.
  specialize (H m).
  specialize (H0 m).
  rewrite fstn_stream_Some in H by auto.
  destruct H, H0; congruence.
Qed.

Fixpoint app_fin_inf {A: Type} (l: list A) (f: nat -> A) :=
  match l with
  | nil => f
  | qa :: l0 => fun n => 
                match n with
                | 0 => qa
                | S m => app_fin_inf l0 f m
                end
  end.

Lemma app_fin_inf_list {A: Type}: forall l (h: nat -> A) m, m < length l -> Some (app_fin_inf l h m) = nth_error l m.
Proof.
  intros.
  revert l H; induction m; intros; simpl.
  + destruct l; [simpl in H; omega |].
    simpl; auto.
  + destruct l; [simpl in H; omega |].
    simpl.
    apply IHm.
    simpl in H; omega.
Qed.

Lemma app_fin_inf_fun {A: Type}: forall l (h: nat -> A) m, length l <= m -> app_fin_inf l h m = h (m - length l).
Proof.
  intros.
  revert m H; induction l; intros; simpl.
  + f_equal; omega.
  + destruct m; [simpl in H; omega |].
    rewrite IHl by (simpl in H; omega).
    f_equal.
Qed.

Lemma length_firstn_list_from_fun: forall {A} (f: nat -> A) n, length (fisrtn_list_from_fun f n) = n.
Proof.
  intros.
  induction n; simpl; auto.
  rewrite app_length, IHn.
  simpl.
  omega.
Qed.

Lemma nth_error_firstn_list_from_fun: forall {A} (f: nat -> A) n m, m < n -> nth_error (fisrtn_list_from_fun f n) m = Some (f m).
Proof.
  intros.
  revert m H; induction n; intros; simpl.
  + omega.
  + destruct (le_dec n m).
    - assert (n = m) by omega; subst.
      replace m with (length (fisrtn_list_from_fun f m) + 0) at 3 by (rewrite length_firstn_list_from_fun; omega).
      rewrite nth_error_app.
      simpl; auto.
    - rewrite nth_error_app1 by (rewrite length_firstn_list_from_fun; omega).
      apply IHn; omega.
Qed.

Lemma fstn_app_inf_fin {A: Type}: forall l (h: nat -> A) n,
  n >= length l ->
  fstn_stream n (inf_stream (app_fin_inf l h)) = fin_stream (l ++ fisrtn_list_from_fun h (n - length l)).
Proof.
  intros.
  stream_extensionality m.
  destruct (le_dec n m).
  + rewrite fstn_stream_None by auto.
    simpl.
    symmetry.
    apply nth_error_None_iff.
    rewrite app_length.
    rewrite length_firstn_list_from_fun.
    omega.
  + rewrite fstn_stream_Some by omega.
    simpl.
    destruct (le_dec (length l) m).
    - rewrite app_fin_inf_fun by auto.
      replace m with (length l + (m - length l)) at 2 by omega.
      rewrite nth_error_app.
      rewrite nth_error_firstn_list_from_fun by omega.
      auto.
    - rewrite nth_error_app1 by omega.
      rewrite app_fin_inf_list by omega.
      auto.
Qed.

Lemma inf_stream_construction {A: Type}: forall (P: stream A -> Prop) (init: list A),
  P (fin_stream init) ->
  (forall l, P (fin_stream l) -> exists qa, P (fin_stream (l ++ qa :: nil))) ->
  exists h, is_inf_stream h /\ forall n, n >= length init -> P (fstn_stream n h).
Proof.
  intros.
  pose (Q := fun l => P (fin_stream (init ++ l))).
  destruct (nat_stepwise_choice Q) as [h ?].
  + hnf.
    rewrite app_nil_r; auto.
  + subst Q; simpl; intros.
    specialize (H0 _ H1).
    destruct H0 as [qa ?]; exists qa.
    rewrite app_assoc.
    auto.
  + exists (inf_stream (app_fin_inf init h)).
    split; [apply inf_stream_inf |].
    intros.
    specialize (H1 (n - length init)).
    unfold Q in H1.
    rewrite (fstn_app_inf_fin init h n) by auto.
    auto.
Qed.

*)