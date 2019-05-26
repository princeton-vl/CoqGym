Require Import L Encodings DecidableRecognisable Markov Enumerable.

Implicit Types P Q : term -> Prop.

(** * Reducability *)

Definition computable_gen X Y (xenc : X -> term) (yenc : Y -> term) f :=
  exists u, proc u /\ forall s, u (xenc s) ▷ (yenc (f s)).

Definition computable_fun f := computable_gen tenc tenc f.

Record mreducible P Q : Prop :=
  { f : term -> term ;
    f_red : forall s, P s <-> Q (f s) ;
    f_comp : computable_fun f ;
  }.
Notation "P ⪯ Q" := (mreducible P Q) (at level 40, no associativity).

Lemma mreducible_sane P Q :
  mreducible P Q <-> exists u, proc u /\ forall s, exists t, u (tenc s) ▷ tenc t /\ (P s <-> Q t).
Proof.
  split.
  - intros [f ? (u & ? & ?)].
    exists u. split; value.
    intros. exists (f s). split; eauto.
  - intros (u & ? & ?). assert (forall s, exists t, u (tenc s) ▷ tenc t) as [f ?] %  L_computable_computable by firstorder.
    exists f.
    + intros. destruct (H0 s) as (t & ? & ?).
      enough (f s = t) as ->. eassumption.
      specialize (e s). eapply tenc_inj. now rewrite <- e, <- H1. 
    + firstorder.
Qed.  

Instance mreducible_preorder : PreOrder mreducible.
Proof.
  econstructor.
  - exists (fun s => s).
    + firstorder.
    + exists I. split; value. intros. solveeq.
  - intros P Q R [f1 H1 [u1 []]] [f2 H3 [u2 []]].
    exists (fun s => f2 (f1 s)).
    + firstorder.
    + exists (lambda (u2 (u1 0))). split; value.
      intros. eapply evaluates_equiv. split; value.
      specialize (H0 s). specialize (H4 (f1 s)).
      solveeq.
Qed.

Lemma mreducible_ext P Q P' Q' :
  (forall s, P s <-> P' s) -> (forall s, Q s <-> Q' s) -> P ⪯ Q -> P' ⪯ Q'.
Proof.
  intros ? ? [f ? ?]. exists f; firstorder.
Qed.

Lemma mreducible_comp P Q :
  P ⪯ Q -> (fun s => ~ P s) ⪯ (fun s => ~ Q s).
Proof.
  intros [f ? ?]. exists f; firstorder.
Qed.

Lemma mreducible_comp_conv :
  (forall P Q, (fun s => ~ P s) ⪯ (fun s => ~ Q s) -> P ⪯ Q) ->
  Markov_Eva.
Proof.
  intros ? ? ? ?. specialize (H eva (fun s => ~~ eva s)).
  destruct H.
  - eapply mreducible_ext with (P :=  (fun s0 : term => ~ eva s0)) (Q :=  (fun s0 : term => ~ eva s0)); try reflexivity.
    firstorder.      
  - eapply f_red. intros ?. eapply H1. intros ?. now eapply f_red in H2.
Qed.

Lemma mreducible_dec P Q :
  decidable Q -> P ⪯ Q -> decidable P.
Proof.
  intros (u & Hp & H) [f ? (v & ? & ?)].
  exists (lambda (u (v 0))). split; value.
  intros s. assert (lambda (u (v 0)) (tenc s) ≡ u (v (tenc s))) as -> by solveeq.
  rewrite H1. firstorder.
Qed.

Lemma mreducible_red P Q s t :
  Q s -> ~ Q t -> decidable P -> P ⪯ Q.
Proof.
  intros ? ? ?. pose proof (decidable_dec H1) as [f ?].
  destruct H1 as (u & ? & ?).
  exists (fun x => if f x then s else t).
  - intros x. specialize (H2 x). destruct (f x); firstorder congruence.
  - exists (lambda (u 0 (tenc s) (tenc t))). split; value.
    intros x. assert ((lambda (((u 0) (tenc s)) (tenc t))) (tenc x) ≡ u (tenc x) (tenc s) (tenc t)) as -> by solveeq.
    destruct (H3 x) as [ [-> % H2 ->] | [? ->] ].
    + solveeq.
    + rewrite <- H2 in H4. destruct (f x); try congruence. solveeq.
Qed.

Lemma mreducible_recognisable P Q :
  recognisable Q -> P ⪯ Q -> recognisable P.
Proof.
  intros (u & ? & ?) [f ? (v & ? & ?)].
  exists (lambda (u (v 0))). split; value.
  intros s. assert (lambda (u (v 0)) (tenc s) ≡ u (v (tenc s))) as -> by solveeq.
  now rewrite H2, f_red, H0.
Qed.

Lemma mreducible_full P :
  P ⪯ (fun s => True) <-> (forall s, P s).
Proof.
  split. 
  - firstorder.
  - intros. eapply mreducible_ext with (P := fun _ => True) (Q := fun _ => True); firstorder.
Qed.

Lemma mreducible_empty P :
  P ⪯ (fun s => False) <-> (forall s, ~ P s).
Proof.
  split. 
  - firstorder.
  - intros. eapply mreducible_ext with (P := fun _ => False) (Q := fun _ => False); firstorder. exact 0.
Qed.

Lemma eva_red :
  (fun s => eva (s (tenc s))) ⪯ eva.
Proof.
  exists (fun s => app s (tenc s)).
  - firstorder.
  - exists (lambda (App 0 (Q 0))). split; value.
    intros. eapply evaluates_equiv. split; value.
    transitivity (App (tenc s) (Q (tenc s))). solveeq.
    now rewrite Q_correct, App_correct.
Qed.

Lemma recognisable_iff P :
  recognisable P <-> P ⪯ eva.
Proof.
  split.
  - intros (u & ? & ?).
    exists (fun x => u (tenc x)).
    + eassumption. 
    + exists (lambda (App (tenc u) (Q 0))). split; value.
      intros. eapply evaluates_equiv; split; value.
      redL. now rewrite Q_correct, App_correct.
  - intros ?. eapply mreducible_recognisable.
    eapply recognisable_eva. eassumption.
Qed.

Lemma preceq_lub P Q : exists R,
    P ⪯ R /\ Q ⪯ R /\ forall R', P ⪯ R' -> Q ⪯ R' -> R ⪯ R'.
Proof.
  exists (fun s => match s with
             app 0 s => P s
           | app _ s => Q s
           | s => Q s
           end).
  repeat split.
  - {
      exists (fun s => app 0 s).
      - cbn. firstorder.
      - exists (lambda (App (tenc 0) 0)). split; value. intros.
        eapply evaluates_equiv; split; value.
        transitivity (App (tenc 0) (tenc s)). solveeq.
        now rewrite App_correct.
    }
  - {
      exists (fun s => app 1 s).
      - cbn. firstorder.
      - exists (lambda (App (tenc 1) 0)). split; value. intros.
        eapply evaluates_equiv; split; value.
        transitivity (App (tenc 1) (tenc s)). solveeq.
        now rewrite App_correct.
    }
  - intros D [f] [g].
    exists (fun s => match s with
             | app 0 s => f s
             | app _ s => g s
             | _ => g s
             end).
    cbn. intros. destruct s as [ | [[] | | ] |]; cbn; firstorder.
    destruct f_comp as (u & ? & ?), f_comp0 as (v & ? & ?).
    exists (lambda (0 (lambda (v 1)) (lambda (lambda (1 (lambda (0 (u 1) (lambda (v 2)))) (lambda (lambda (v 2))) (lambda (v 1))))) (lambda (v 1)))).
    split; value. intros. eapply evaluates_equiv; split; value.
    destruct s as [ | [ [] | | ] | ] eqn:E.
    + specialize (H2 s). subst. solveeq.
    + specialize (H0 t1). subst. solveeq.
    + specialize (H2 t1). specialize (H0 t1). subst. solveeq.
    + specialize (H2 t2). specialize (H0 t2). solveeq.
    + specialize (H2 t1). solveeq.
    + specialize (H2 s). subst. solveeq.
Qed.

