(** * Infinite Data Types *)

Require Import Shared.Prelim MarkovPost.

(** ** Definition of infinite and generating types *)

Definition generating X :=
  forall (A : list X), exists x, ~ x el A.

Definition injective X Y (f : X -> Y) :=
  forall x x', f x = f x' -> x = x'.

Definition infinite X :=
  exists (f : nat -> X), injective f.

Section Inf.
  
  Variables (X : Type) (f' : nat -> option X).
  Hypothesis Hf' : forall x, exists n, f' n = Some x.
  Hypothesis HX : eq_dec X.
  
  (** ** Infinite data types are generating *)

  Section Gen.
    
    Variable f : nat -> X.
    Hypothesis Hf : injective f.

    Fixpoint LX n :=
      match n with 
      | 0 => [f 0]
      | S n => f (S n) :: LX n
      end.

    Lemma LX_len n :
      | LX n | = S n.
    Proof.
      induction n; cbn; eauto.
    Qed.

    Lemma LX_el n x :
      x el LX n -> exists n', n' <= n /\ f n' = x.
    Proof.
      induction n.
      - intros [H|[] ]. exists 0. split; auto.
      - intros [H|H]; eauto.
        destruct (IHn H) as [n'[H1 H2] ].
        exists n'. split; auto.
    Qed.

    Lemma LX_NoDup n :
      NoDup (LX n).
    Proof.
      induction n; cbn; repeat constructor; auto.
      intros (n'&H1&H2) % LX_el.
      apply Hf in H2. omega.
    Qed.

    Lemma sub_dec (A B : list X) :
      (A <<= B) + {x | x el A /\ ~ x el B}.
    Proof.
      revert B. induction A; intros B; cbn; auto.
      destruct (IHA B); decide (a el B); auto.
      - right. exists a. split; auto.
      - destruct s as (x&H1&H2). right.
        exists x. split; auto.
      - right. exists a. split; auto.
    Qed.

    Lemma X_gen :
      generating X.
    Proof.
      intros A. destruct (sub_dec (LX (|A|)) A) as [H|H].
      - apply NoDup_incl_length in H; try apply LX_NoDup.
        rewrite LX_len in H. omega.
      - destruct H as [x [_ H] ]. now exists x.
    Qed.

  End Gen.

  (** ** Generating data types are infinite *)

  Hypothesis Hg : generating X.

  Instance el_dec :
    forall (A : list X) x, dec (x el A).
  Proof.
    intros A x. induction A; cbn; auto.
  Qed.

  Definition dummy : X.
  Proof.
    pose (p := fun n => exists x, f' n = Some x).
    destruct (@mu p) as [n Hn].
    - intros n. destruct (f' n) eqn : H.
      + left. now exists x.
      + right. intros [x H']. congruence.
    - destruct (Hg nil) as [x Hx]. destruct (Hf' x) as [n Hn]. now exists n, x.
    - destruct (f' n) eqn : H; trivial.
      exfalso. destruct Hn as [x Hx]. congruence.
  Qed.

  Definition f n :=
    match (f' n) with Some x => x | None => dummy end.

  Lemma f_sur :
    forall x, exists n, f n = x.
  Proof.
    intros x. destruct (Hf' x) as [n Hn]. exists n.
    unfold f. now rewrite Hn.
  Qed.

  Definition le_f x y :=
    exists n, f n = x /\ forall n', f n' = y -> n <= n'.

  Lemma gen (A : list X) :
    { x | ~ x el A /\ forall y, ~ y el A -> le_f x y}.
  Proof.
    pose (p := fun n => ~ f n el A).
    assert (H1 : forall x, dec (p x)).
    { intros n. destruct (el_dec A (f n)) as [H|H].
      - right. intros H'. contradiction.
      - left. assumption. }
    assert (H2 : exists x, p x).
    { destruct (Hg A) as [x Hx]. destruct (f_sur x) as [n <-]. now exists n. }
    exists (f (mu' H1 H2)). split; try apply proj2_sig.
    intros y Hy. exists (mu' H1 H2). split; trivial.
    intros n <-. apply mu_least, Hy.
  Defined.

  Definition gen' A :=
    proj1_sig (gen A).

  Lemma gen_spec A :
    ~ gen' A el A.
  Proof.
    unfold gen'. destruct (gen A); cbn. apply a.
  Qed.

  Lemma gen_le_f A :
    forall x, ~ x el A -> le_f (gen' A) x.
  Proof.
    unfold gen'. destruct (gen A); cbn. apply a.
  Qed.

  Fixpoint LL n :=
    match n with 0 => nil | S n => LL n ++ [gen' (LL n)] end.

  Definition F n :=
    gen' (LL n).

  Lemma LL_cum :
    cumulative LL.
  Proof.
    intros n. now exists [(F n)].
  Qed.

  Lemma F_nel n :
    ~ F n el LL n.
  Proof.
    apply gen_spec.
  Qed.

  Lemma F_el n :
    F n el LL (S n).
  Proof.
    cbn. apply in_app_iff. now right.
  Qed.

  Lemma F_lt n m :
    n < m -> F n el LL m.
  Proof.
    intros H. apply cum_ge' with (n0:=S n).
    - apply LL_cum.
    - apply F_el.
    - omega.
  Qed.

  Lemma F_inj' n m :
    F n = F m -> ~ n < m.
  Proof.
    intros H1 H2 % F_lt. rewrite H1 in H2. apply (F_nel H2).
  Qed.

  Lemma F_inj :
    injective F.
  Proof.
    intros n m Hnm. destruct (Nat.lt_total n m) as [H|[H|H] ]; trivial.
    - contradiction (F_inj' Hnm H).
    - symmetry in Hnm. contradiction (F_inj' Hnm H).
  Qed.

  (** ** Generating data types are in bijection to nat *)

  Lemma lt_acc n :
    Acc lt n.
  Proof.
    induction n.
    - constructor. intros m H. omega.
    - constructor. intros m H.
      destruct (Nat.lt_total n m) as [H'|[->|H'] ].
      + omega.
      + assumption.
      + now apply IHn.
  Qed.

  Lemma LL_f n :
    f n el LL (S n).
  Proof.
    induction (lt_acc n) as [n _ IH].
    decide _; try eassumption. exfalso.
    assert (H : ~ f n el LL n).
    { intros H. apply n0. apply (cum_ge' LL_cum H). auto. }
    apply gen_le_f in H as [n'[H1 H2] ].
    specialize (H2 n eq_refl).
    destruct (Nat.lt_total n' n) as [H3|[->|H3] ].
    - apply (gen_spec (A:=LL n)). rewrite <- H1.
      now apply (cum_ge' LL_cum (IH n' H3)).
    - apply n0. rewrite H1. apply in_app_iff; fold LL.
      right. left. reflexivity.
    - omega.
  Qed.

  Lemma LL_F x n :
    x el LL n -> exists m, F m = x.
  Proof.
    induction n; cbn; auto.
    intros [H|[H|H]] % in_app_iff; auto.
    now exists n.
  Qed.

  Lemma F_sur :
    forall x, exists n, F n = x.
  Proof.
    intros x. destruct (f_sur x) as [n H].
    destruct (LL_F (LL_f n)) as [m H'].
    exists m. congruence.
  Qed.

  Definition G x :=
    mu' _ (F_sur x).

  Lemma FG n :
    F (G n) = n.
  Proof.
    unfold G. apply proj2_sig.
  Qed.
  
  Lemma GF n :
    G (F n) = n.
  Proof.
    apply F_inj. now rewrite FG.
  Qed.

End Inf.
