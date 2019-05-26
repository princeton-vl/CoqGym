From Undecidability.L Require Import Interpreter Encodings.

Definition test (u : term) := forall n, u (enc n) ▷ T \/ u (enc n) ▷ F.
Definition satis u n := u (enc n) ▷ T.

Hint Unfold test.

Section fix_u.

  Variable u : term.
  Hypothesis proc_u : proc u.
  Hypothesis test_u : test u.

  Definition H := rho (.\"H", "n", "u"; "u" "n" (.\ "_"; "n") (.\ "_"; "H" (!Succ "n") "u") !I).
  Hint Unfold H : cbv.

  Lemma H_rec n : H (enc n) u ≻^+ u (enc n) (lambda (enc n)) (lambda (H (Succ (enc n)) u)) I.
  Proof.
    eexists. split; solvered.
  Qed.

  Definition ok n := exists k, H (enc n) u ▷ enc k /\ satis u k.

  Lemma H_ok n : satis u n -> ok n. 
  Proof.
    intros. exists n. rewrite H_rec, H0; eauto. split. solveeq. eauto.
  Qed.

  Lemma H_n_Sn n : ok (S n) -> ok n.
  Proof with eauto.
    intros H_Sk. destruct (test_u n).
    - intros. exists n.
      rewrite H_rec, H0; eauto. split. solveeq. eauto.
    - destruct (H_Sk) as (k & ?). exists k.
      rewrite H_rec, H0; eauto. split. eapply evaluates_equiv. split; value.
      transitivity (H (Succ (enc n)) u). solveeq.
      rewrite Succ_correct. now eapply evaluates_equiv. firstorder.
  Qed.

  Lemma H_0_n n : test u -> ok n -> ok 0.
  Proof.
    induction n; eauto using H_n_Sn. 
  Qed.

  Definition C := lambda (H (enc 0) 0).

  Lemma C_complete n : satis u n -> exists n, C u ▷ enc n /\ satis u n.
  Proof.
    intros sat % H_ok. destruct (H_0_n test_u sat) as [k [H_sat % evaluates_equiv ?]]; eauto. exists k.
    split; eauto.
    eapply evaluates_equiv; split; value. transitivity (H (enc 0) u).
    solveeq. firstorder.
  Qed.

  Lemma H_correct n k v : H (enc n) u ▷^k v -> exists n, satis u n.
  Proof.
    revert n v.
    eapply complete_induction with (x := k). clear k.
    intros k IHn n v He.

    destruct (test_u n).
    - firstorder.
    - assert (H (enc n) u ≻^+ H (enc (S n)) u).
      eapply (stepplus_star_stepplus (H_rec _)).
      eapply evaluates_star in H0 as []. rewrite H0.
      transitivity (H (Succ (enc n)) u). solvered. now rewrite Succ_correct.
      now destruct (triangle He H1) as (? & ? & ? % IHn).
  Qed.

  Lemma C_sound : eva (C u) -> exists n, satis u n.
  Proof with eauto.
    assert (He : C u ≡ H (enc 0) u). solveeq. rewrite He.
    intros [v [[k Hv] % star_stepn lam_v] % evaluates_star].
    eapply H_correct. split...
  Qed.

End fix_u.
