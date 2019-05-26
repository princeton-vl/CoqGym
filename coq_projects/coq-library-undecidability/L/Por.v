From Undecidability.L Require Import InterpreterResults.

(** ** Parallel or *)

Definition H (s t : term) : term := Eval cbv in (.\ "z"; !E "z" !s !(lambda T) (!E "z" !t !(lambda T) !F)).
Definition O : term := Eval cbv in .\ "x", "y";
                        (.\ "z"; !E "z" "x" !(lambda T) (!E "z" "y" !(lambda F) !I)) (!C !(H 2 1)).

Lemma H_proc s t : proc (H (tenc s) (tenc t)).
Proof.
  value.
Qed.

Lemma H_rec s t n : (H (tenc s) (tenc t) (enc n) ≡ E (enc n) (tenc s) (lambda T) (E (enc n) (tenc t) (lambda T) F)).
Proof.
  solveeq.
Qed.

Lemma H_test s t : test (H (tenc s) (tenc t)).
Proof.
  intros n. destruct (eval n s) eqn:Eq, (eval n t) eqn:Eq2; rewrite H_rec, !E_correct, Eq, Eq2;
              [ left .. | right]; solveeq.
Qed.

Lemma H_inv n s t : satis ( H (tenc s) (tenc t) ) n <-> eval n s <> None \/ eval n t <> None.
Proof.
  split.
  - intros.
    destruct (eval n s) eqn:Eq, (eval n t) eqn:Eq2; try firstorder congruence.
    exfalso. unfold satis in H0.
    rewrite H_rec, !E_correct, Eq, Eq2 in H0.
    setoid_rewrite none_correct at 2 in H0; value. rewrite none_correct in H0; value. inv H0.
  - intros. destruct (eval n s) eqn:Eq, (eval n t) eqn:Eq2; (try firstorder congruence); unfold satis; rewrite H_rec, !E_correct, Eq, Eq2;  solveeq.
Qed.

Lemma O_rec s t : O (tenc s) (tenc t) ≡ (lambda (E 0 (tenc s) (lambda T) (E 0 (tenc t) (lambda F) I))) (C (H (tenc s) (tenc t))).
Proof.
  solvered.
Qed.

Lemma O_complete s t : eva s \/ eva t -> eva (O (tenc s) (tenc t)).
Proof.
  intros [ [v [n Hv] % evaluates_eval] | [v [n Hv] % evaluates_eval] ];
  rewrite O_rec; edestruct (C_complete (n := n) (H_proc s t) (H_test s t)) as [k []]; unfold satis.
  - rewrite H_rec, !E_correct, Hv.
    destruct (eval n t) eqn:E2; solvered.
  - rewrite H0. eapply H_inv in H1.
    destruct (eval k s) eqn:E1; try firstorder congruence.
    + exists T. eapply evaluates_equiv; split; value.
      transitivity (E (enc k) (tenc s) (lambda T) (E (enc k) (tenc t) (lambda F) I)). solveeq.
      rewrite !E_correct, E1. destruct (eval k t); solveeq.
    + destruct (eval k t) eqn:E2; try firstorder congruence.
      exists F. eapply evaluates_equiv; split; value.
      transitivity (E (enc k) (tenc s) (lambda T) (E (enc k) (tenc t) (lambda F) I)). solveeq.
      rewrite !E_correct, E1, E2. solveeq.
  - rewrite H_rec, !E_correct, Hv.
    destruct (eval n s) eqn:E2; solvered.
  - rewrite H0. eapply H_inv in H1.
    destruct (eval k s) eqn:E1; try firstorder congruence.
    + exists T. eapply evaluates_equiv; split; value.
      transitivity (E (enc k) (tenc s) (lambda T) (E (enc k) (tenc t) (lambda F) I)). solveeq.
      rewrite !E_correct, E1. destruct (eval k t); solveeq.
    + destruct (eval k t) eqn:E2; try firstorder congruence.
      exists F. eapply evaluates_equiv; split; value.
      transitivity (E (enc k) (tenc s) (lambda T) (E (enc k) (tenc t) (lambda F) I)). solveeq.
      rewrite !E_correct, E1, E2. solveeq.
Qed.

Lemma O_sound s t : eva (O (tenc s) (tenc t)) -> eva s /\ O (tenc s) (tenc t) ▷ T \/ eva t /\ O (tenc s) (tenc t) ▷ F.
Proof with eauto.
  rewrite O_rec. intros H0.
  assert (eva (C (H (tenc s) (tenc t)))) by now eapply app_eva in H0.
  eapply C_sound in H1 as [n H1 % H_inv]; value; eauto using H_test.
  assert (H2 := H1). eapply H_inv in H1.
  eapply C_complete in H1 as (k & H1 & sat); value; eauto using H_test.
  eapply H_inv in sat. destruct (eval k s) eqn:Eq; try congruence.
  - left. split. exists t0. eapply eval_evaluates. eauto.
    rewrite H1. eapply evaluates_equiv; split; value.
    transitivity (E (enc k) (tenc s) (lambda T) (E (enc k) (tenc t) (lambda F) I)). solveeq.
    rewrite !E_correct, Eq. destruct (eval k t); solveeq.
  - destruct sat; try congruence.
    destruct (eval k t) eqn:E2; try congruence. right.
    split. exists t0. eapply eval_evaluates. eauto.
    rewrite H1. eapply evaluates_equiv; split; value.
    transitivity (E (enc k) (tenc s) (lambda T) (E (enc k) (tenc t) (lambda F) I)). solveeq.
    rewrite !E_correct, Eq. destruct (eval k t); solveeq.
Qed.

From Undecidability.L Require Import DecidableRecognisable.

(** ** Post's theorem *)

Theorem Post p : (forall x, p x \/ ~ p x) -> recognisable p -> recognisable (complement p) -> decidable p.
Proof.
  intros pdec_p [u [[cls_u lam_u] Hu]] [v [[cls_v lam_v] Hv]].
  pose (por_u_v := lambda (O ((App (tenc u) (Q 0))) ((App (tenc v) (Q 0))))).
  exists por_u_v.
  split; value. intros t.
  unfold complement,pi in *.
  assert (A : eva (O (tenc (u (tenc t))) (tenc (v (tenc t))))). {
    eapply O_complete. now rewrite <-Hu,<-Hv.
  }
  destruct (O_sound A) as [[B [? C]%evaluates_equiv] | [B [? C]%evaluates_equiv]].
  - left; split. now apply Hu.
    eapply evaluates_equiv; split; value.
    transitivity (((O ((App (tenc u) ( Q (tenc t))))) ((App (tenc v) (Q (tenc t)))))). unfold por_u_v. solveeq.
    now rewrite !Q_correct, !App_correct.
  - right; split. now apply Hv. eapply evaluates_equiv; split; value.
    transitivity (((O ((App (tenc u) ( Q (tenc t))))) ((App (tenc v) (Q (tenc t)))))). unfold por_u_v; solveeq.
    now rewrite !Q_correct, !App_correct.
Qed.


(** ** Recognisable classes are closed under union *)

Lemma recognisable_union p q : recognisable p -> recognisable q -> recognisable (union p q).
Proof.
  intros [u [[lam_u cls_u] Hu]] [v [[lam_v cls_v] Hv]].
  unfold recognisable, union.
  exists (lambda (O ((App (tenc u) (Q 0))) ((App (tenc v) (Q 0))))).
  split; value. intros t.

  rewrite Hu, Hv; unfold pi.

  assert (H : (lambda (O ((App (tenc u)) (Q 0)) ((App (tenc v)) (Q 0)))) (tenc t) ≡ O (tenc (u (tenc t))) (tenc (v (tenc t)))). {
  transitivity (((O ((App (tenc u) ( Q (tenc t))))) ((App (tenc v) (Q (tenc t)))))). solveeq.
  now rewrite Q_correct, App_correct, App_correct.
  }
  rewrite H; split.
  - intros [A | A]; eapply O_complete; intuition.
  - intros A. eapply O_sound in A; intuition. 
Qed.
