From Undecidability.L Require Import Tactics Encodings DecidableRecognisable.
Implicit Type p : term -> Prop.
Implicit Types s t u : term.

(** * Reduction lemma and Rice’s theorem *)

(** ** Closedness is decidable *)

Definition Leb := Eval cbn in
      rho (.\ "leb", "m", "n"; "m" !T (.\ "m'"; "n" !F (.\ "n'"; "leb" "m'" "n'"))).

Hint Unfold Leb: cbv.

Lemma Leb_correct m n : Leb (enc m) (enc n) ≡ benc (leb m n).
Proof.
  destruct m.
  - solveeq.
  - revert m; induction n; intros m.
    + solveeq.
    + destruct m. solveeq. specialize (IHn m). solveeq.
Qed.

Hint Rewrite Leb_correct : Lcorrect.

Definition Lt : term := .\ "m", "n"; !Leb (!Succ "m") "n".

Lemma Lt_correct n k : Lt (enc n) (enc k) ≡ benc (Nat.ltb n k).
Proof.
  unfold Nat.ltb. rewrite <- Leb_correct.
  transitivity (Leb (Succ (enc n)) (enc k)). solveeq.
  now rewrite Succ_correct.
Qed.

Definition Bound := Eval cbn in
      rho (.\ "d", "k", "t";
           "t" (.\ "n"; !Lt "n" "k")
               (.\ "s", "t"; ("d" "k" "s") ("d" "k" "t") !F)
               (.\ "s"; "d" (!Succ "k") "s")).

Lemma Bound_correct k s : Bound (enc k) (tenc s) ≡ benc (bound k s).
Proof.
  revert k; induction s; intros k.
  - transitivity (Lt (enc n) (enc k)). solveeq. rewrite Lt_correct. unfold bound.
    destruct (Nat.ltb_spec0 n k); decide (n < k); try now omega. reflexivity. reflexivity.
  - transitivity ((Bound (enc k) (tenc s1)) (Bound (enc k) (tenc s2)) F). solveeq.
    rewrite IHs1, IHs2. cbn.
    destruct (bound _ s1), (bound _ s2); solveeq.
  - transitivity (Bound (Succ (enc k)) (tenc s)). solveeq. now rewrite Succ_correct, IHs.
Qed.

Definition Closed := Bound (enc 0).

Lemma decidable_closed : decidable closed.
Proof.
  exists (lambda (Closed 0)). split; value.
  intros s.
  assert ((lambda (Closed 0)) (tenc s) ≡ benc (bound 0 s)). 
  transitivity (Bound (enc 0) (tenc s)). solveeq. now rewrite Bound_correct.
  rewrite H.
  
  destruct (bound 0 s) eqn:E.
  - firstorder econstructor.
  - right. split. intros C. congruence. econstructor.
Qed.

Definition Lambda := lambda (0 (lambda F) (lambda (lambda F)) (lambda T)).

Hint Unfold Lambda : cbv.

Lemma Lambda_correct s : Lambda (tenc s) ▷ T /\ lam s \/
                         Lambda (tenc s) ▷ F /\ ~ lam s.
Proof.
  destruct s.
  + right. split. solveeq. intros [x H]; inv H.
  + right. split. solveeq. intros [x H]; inv H.
  + left. split. solveeq. value.
Qed.

Lemma decidable_lam : decidable lam.
Proof.
  exists Lambda. split; value. intros s.
  assert (H := Lambda_correct s). firstorder.
Qed.

Lemma decidable_proc : decidable proc.
Proof.
  eapply decidable_intersection.
  - eapply decidable_closed.
  - eapply decidable_lam.
Qed.

(** ** Reduction lemma *)

Notation "s '≈' t" := (forall u v, t (tenc u) ▷ v <-> s (tenc u) ▷ v) (at level 50).

Lemma equiv_semantic s t : s ≡ t -> s ≈ t.
Proof.
  intros H ? ?; now rewrite H.
Qed.

Definition closed_under_proc R p := forall s t , proc s -> proc t -> p s -> R s t -> p t.
Definition semantic p := closed_under_proc (fun s t => s ≈ t) p.

Lemma unrecognisable_russell : ~ recognisable (fun s => closed s /\ ~ eva (s (tenc s))).
Proof.
  intros [u [[cls_u lam_u] H]]. specialize (H u). tauto.
Qed.

Lemma Reduction p f v :
  proc v ->
  (forall s, closed s -> p (f s) <-> ~ eva (s (tenc s))) ->
  (forall s, v (tenc s) ≡ tenc (f s)) ->
  ~ recognisable p.
Proof.
  intros proc_v  spec_f spec_v (u & proc_u & Hu).
  assert (recognisable closed) as (C & proc_C & HC). {
    eapply dec_recognisable. eapply decidable_closed. }
  pose (w := lambda (F (C 0) (u (v 0)))).
  eapply unrecognisable_russell. exists w; split; value. intros s.
  
  assert (w (tenc s) ≡ F (C (tenc s)) (u (tenc (f s)))). {
    transitivity (F (C (tenc s)) (u (v (tenc s)))). solveeq. now rewrite spec_v. }
   intuition; [ | rewrite H, F_eva, <- HC, <- Hu, spec_f in H0; tauto..].
  rewrite H, F_eva, <- HC, <- Hu, spec_f; eauto.
Qed.

(** ** Rice's lemma and Rice's theorem *)

Lemma D_pi u : pi D u <-> False.
Proof.
  unfold pi. firstorder using eva_D.
Qed.

Lemma Rice p N :
  semantic p ->
  proc N -> ~ p N ->
  p D ->
  ~ recognisable p.
Proof with eauto; try now intuition.
  intros p_sem proc_N pN pD [u [[cls_u lam_u] Hu]].
  pose (f := fun s => lambda (F (s (tenc s)) N 0)).
  pose (v := lambda (Lam (App (App (App (tenc F) (App 0 (Q 0))) (tenc N)) (tenc 0)))).

  eapply Reduction with (p := p) (f := f) (v := v).
  - value.    
  - intros. assert (Hf : forall t, f s (tenc t) ≡ F (s (tenc s)) N (tenc t)) by (intros; solvered).
    intuition.
    + eapply p_sem in H0; value. eapply pN, H0. intros t t'. rewrite Hf.
      destruct H1 as (s' & [] % evaluates_equiv). rewrite H1, F_correct; value. tauto.
    + eapply p_sem with (s := D); value. eauto. intros t t'. rewrite Hf.
      intuition.
      * destruct H0. eapply F_eva with (t := N). eapply app_eva with (t := tenc t). firstorder.
      * exfalso. eapply D_pi. exists t'. eassumption.
  - intros. transitivity (Lam ((App ((App ((App (tenc F)) ((App (tenc s)) (Q (tenc s))))) (tenc N))) (tenc 0))). solveeq.
    now rewrite Q_correct, !App_correct, Lam_correct.
  - exists u. firstorder.
Qed.

Lemma Rice_pi p :
  closed_under_proc (fun s t => (forall u, pi s u <-> pi t u)) p ->
 (exists u, proc u /\ ~ p u) -> 
 p (lambda Omega) -> ~ recognisable p.
Proof with eauto; try now intuition.
  intros. destruct H0 as [u [H0 H0']]. eapply Rice.
  - intros. hnf. intuition. eapply H. exact H2. eauto. eauto. split; intros (? & ?); exists x; firstorder.
  - eauto.
  - eauto.
  - firstorder.
Qed.

Lemma rec_total : ~ recognisable (fun s => ~forall t, pi s t).
Proof.
  eapply Rice_pi.
  - hnf; intuition. eapply H1. intros. rewrite H2. eauto.
  - exists (lambda I). repeat split; value. intros H. eapply H. intros t. exists I. solveeq.
  - intros A. eapply (D_pi I); eauto.  
Qed.

Lemma rec_total_cls : ~ recognisable (fun s => closed s /\ ~forall t, pi s t).
Proof.
  eapply Rice_pi.
  - hnf; intuition. eapply H4. intros. rewrite H2. eauto.
  - exists (lambda I). repeat split; value. intros H. eapply H. intros t. exists I. solveeq.
  - split; value. intros A. eapply (D_pi I); eauto.  
Qed.

Lemma rec_total_proc : ~ recognisable (fun s => proc s /\ ~forall t, pi s t).
Proof.
  eapply Rice_pi.
  - hnf; intuition. eapply H4. intros. rewrite H2. eauto.
  - exists (lambda I). repeat split; value. intros H. eapply H. intros t. exists I. solveeq. 
  - split; value. intros A. eapply (D_pi I); eauto.  
Qed.


Theorem Rice_Theorem p :
  closed_under_proc (fun s t => s ≈ t) p ->
 (exists u, proc u /\ ~ p u) -> (exists u, proc u /\ p u) ->
  ~ decidable p.
Proof.
  intros. intros A. assert (B : decidable p) by eassumption. destruct A as [u [proc_u Hu]].
  destruct H0 as (? & ? & ?), H1 as (? & ? & ?).
  destruct (Hu D).
  - eapply Rice. exact H. exact H0. tauto. firstorder. eapply dec_recognisable. exists u; tauto.
  - eapply Rice with (p := complement p).
    + unfold complement. hnf. intuition. eapply H8.  eapply H; eauto. intuition; now eapply H9.
    + exact H1.
    + firstorder.
    + firstorder.
    + now eapply dec_recognisable, decidable_complement.
Qed.

Lemma dec_total : ~ decidable (fun s => proc s /\ forall t, pi s t).
Proof.
  eapply Rice_Theorem.
  - hnf; intuition. destruct (H4 t0). firstorder.
  - exists D. repeat split; value. intros A. eapply (D_pi I); eauto.  firstorder.
  - exists (lambda I). repeat split; value. intros H. exists I. solveeq. 
Qed.
