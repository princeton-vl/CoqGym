From Undecidability.L Require Export Enumerable InterpreterResults DecidableRecognisable Rice Por.

(** * Markov's principle *)

Lemma re_exists p : enumerable p -> enumerable (fun t => exists s : term, p (s t)).
Proof.
  intros (u & proc_u & spec_u & corr_u).
  exists (lambda (u 0 (lambda (0 (lambda none) (lambda (lambda (some 0))) (lambda none))) none)).
  repeat split; value.
  - intros n.  destruct (spec_u n).
    + left. solveeq.
    + destruct H as ([] & ? & ?).
      * left; solveeq.
      * right. exists t. split. solveeq. eauto.
      * left; solveeq.
  - intros s [t [n H] % corr_u]. exists n. solveeq.
Qed.

Lemma DA p : recognisable p -> recognisable (fun _ => exists t, p t).
Proof.
  intros. eapply enumerable_recognisable.
  change (enumerable (fun t => exists s, (fun x => match x with app s t => p s | _ => False end) (app s t))).
  eapply re_exists. eapply recognisable_enumerable.
  destruct H as (u & pu & Hu).
  pose (v := (lambda (0 (lambda Omega) (lambda (lambda (u 1))) (lambda Omega)))).
  exists v.
  split. subst v; value. destruct s; unfold pi.
  - assert (v (tenc n) ≡ Omega). solveeq. rewrite H. firstorder using eva_Omega.
  - assert (v (tenc (s1 s2)) ≡ u (tenc s1)). solveeq. now rewrite H, Hu.
  - assert (v (tenc (lambda s)) ≡ Omega). solveeq. rewrite H. firstorder using eva_Omega.
Qed.
  
Definition Markov_Post:= forall p, recognisable p -> recognisable (complement p) -> decidable p.
Definition Markov_Sat := forall p, decidable p -> (~~ exists t, p t) -> exists t, p t.
Definition Markov_Eva := forall s, closed s -> ~~ eva s -> eva s.

Lemma Markov_Post_to_Sat : Markov_Post -> Markov_Sat.
Proof.
  intros post p dec_p H.
  assert (recognisable (fun _ => exists t, p t)). {
    eapply DA. now eapply dec_recognisable. }
  assert (recognisable (fun _ => ~ exists t, p t)). {
    exists D. split; value. intros. firstorder using D_pi. }
  destruct (dec_pdec (post _ H0 H1) I); tauto.
Qed.

Lemma Markov_Sat_to_Eva : Markov_Sat -> Markov_Eva.
Proof.
  intros markov t cls_t Ht.
  pose (q := fun s => exists n, s = var n /\ eval n t <> None).
  
  assert (decp : decidable q). {
    exists (.\ "s" ; "s" (.\ "n" ; !E "n" !(tenc t) !(lambda T) !F) !(lambda (lambda F)) !(lambda F)).
    split; value. intros s.
    cbn. destruct s.
    - destruct (eval n t) eqn:Eq.
      + left. split. exists n; firstorder congruence. eapply evaluates_equiv; split; value.
        transitivity (E (enc n) (tenc t) (lambda T) F). solveeq. rewrite E_correct, Eq. solveeq.
      + right. split. intros (n' & Hn & E'). inv Hn. congruence. eapply evaluates_equiv; split; value.
        transitivity (E (enc n) (tenc t) (lambda T) F). solveeq. rewrite E_correct, Eq. solveeq.
    - right. split. intros (n' & Hn & E'). inv Hn. solveeq.
    - right. split. intros (n' & Hn & E'). inv Hn. solveeq.
  }

  destruct (markov _ decp) as [t' [v H]].
  - assert (forall P Q : Prop, (P -> Q) -> (~~ P -> ~~ Q)) by tauto. eapply H; try eassumption; eauto.
    intros [v [n Hn] % evaluates_eval].
    exists n. exists n. firstorder congruence.
  - destruct H. subst. destruct (eval v t) eqn:Eq; try congruence.
    eapply eval_evaluates in Eq. eauto.
Qed.

Lemma Markov_Eva_to_Post : Markov_Eva -> Markov_Post.
Proof.
  intros H p [u [[lam_u cls_u] Hu]] [v [[lam_v cls_v] Hv]].
  pose (por_u_v := lambda (O ((App (tenc u) (Q 0))) ((App (tenc v) (Q 0))))).
  exists por_u_v.
  split; subst por_u_v; value. intros t. 

  assert (A : eva (O (tenc (u (tenc t))) (tenc (v (tenc t))))). {
    eapply H; value.

    intros A.
    assert (Hnu : ~ eva (u (tenc t))). { intros B. eapply A, O_complete. tauto. }
    assert (Hnv : ~ eva (v (tenc t))). { intros B. eapply A, O_complete. tauto. }
    rewrite <- Hu in Hnu. rewrite <- Hv in Hnv. unfold complement in *. tauto.
  } 

  eapply O_sound in A.

  destruct A as [[A [B ?] %evaluates_equiv] | [A [B ?] %evaluates_equiv]].
  - left; split; eauto. rewrite Hu. tauto. eapply evaluates_equiv; split; value.
    dobeta. now rewrite Q_correct, !App_correct, B.
  - right; split; eauto. unfold complement in *. rewrite Hv. tauto.
    eapply evaluates_equiv; split; value. dobeta; now rewrite Q_correct, !App_correct, B.
Qed.
