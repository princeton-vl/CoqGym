From Undecidability.L Require Import Encodings.

Implicit Types s t u v : term.
Implicit Types p q : term -> Prop.

(** * Decidable and recognisable classes *)
(** ** Definition of decidable classes *)

Definition decides u p := forall s, (p s /\ u (tenc s) ▷ T) \/ (~ p s /\ u (tenc s) ▷ F).
Definition decidable p := 
  exists u, proc u /\ decides u p.

Lemma decidable_spec u p : decides u p -> forall s, (p s <-> u (tenc s) ▷ T) /\ (~ p s <-> u (tenc s) ▷ F).
Proof.
  intros; split; destruct (H s); firstorder;
    rewrite H1 in H2; destruct T_equiv_F; now rewrite H2.
Qed.

(** ** Definition of recognisable classes *)

Definition pi s t := eva (s (tenc t)).

Definition recognisable p := 
  exists u, proc u /\ forall s, p s <-> eva (u (tenc s)).

(* * Complement, intersection and union of predicates *)

Definition complement p := fun t => ~ p t.
Definition intersection p q := fun t => p t /\ q t.
Definition union p q := fun t => p t \/ q t.

(** ** Decidable classes are closed under union, intersection and complement *)

Definition tcompl (u : term) : term := .\"x"; (!u "x") !F !T.

Definition tintersection u v : term := .\"x"; (!u "x") (!v "x") !F.

Definition tunion u v : term := .\"x"; (!u "x") !T (!v "x").

Lemma decidable_intersection p q : decidable p -> decidable q -> decidable (intersection p q).
Proof. 
  intros [u [[cls_u lam_u] decp]] [v [[cls_v lam_v] decq]].
  exists (tintersection u v). split; unfold tintersection; value.
  intros s. destruct (decp s) as [[ps Hu ] | [nps Hu]], (decq s) as [[Qs Hv] | [nQs Hv]]; [left| right..]; firstorder; solvered.
Qed.

Lemma decidable_union p q : decidable p -> decidable q -> decidable (union p q).
Proof. 
  intros [u [[cls_u lam_u] Hu]] [v [[cls_v lam_v] Hv]].
  exists (tunion u v). split; unfold tunion; value.
  intros s. destruct (Hu s) as [[A B] | [A B]], (Hv s) as [[C D] | [C D]]; [left ..  | right]; firstorder; solvered.
Qed.

Lemma decidable_complement p : decidable p -> decidable (complement p).
Proof.
  intros [u [[cls_u lam_u] H]].
  exists (tcompl u). split; unfold tcompl; value.
  intros s. destruct (H s) as [[ps A] | [nps A]];  [right | left]; intuition; solveeq.
Qed.

(** ** There is an undecidable class *)

Lemma undecidable_russell : ~ decidable (fun s => ~ s (tenc s) ▷ T).
Proof.
  intros (u & proc_u & Hu).
  destruct (Hu u) as [ | [] ].
  - firstorder.
  - eapply T_equiv_F. rewrite <- H0. exfalso. eapply H. intros H1.
    eapply T_equiv_F. now rewrite <- H0, <- H1.
Qed.

(** ** Recognisable classes are closed under intersection *)

Definition recinter u v : term := .\"x"; !F (!u "x") (!v "x").
Hint Unfold recinter : cbv.

Lemma recinter_correct u v s : closed u -> closed v -> eva (recinter u v (tenc s)) <-> eva ( u (tenc s)) /\ eva (v (tenc s)).
Proof.
  intros cls_u cls_q.
  split.
  - intros H.
    assert (recinter u v (tenc s) ≡ F (u (tenc s)) (v (tenc s))) by solvered. rewrite H0 in H.
    now eapply app_eva in H as [[] % app_eva ].
  - intros [[x [Hx ?] % evaluates_equiv] [y [Hy ?] % evaluates_equiv]]. exists y. eapply evaluates_equiv.
    split. solvered. value.
Qed.

Lemma recognisable_intersection p q : recognisable p -> recognisable q -> recognisable (intersection p q).
Proof.
  intros [u1 [[? ?] Hu1]] [u2 [[? ?] Hu2]].
  exists (recinter u1 u2). split. unfold recinter. value.
  intros; rewrite recinter_correct; firstorder.
Qed.

(** ** Decidable classes are recognisable and coregnisable *)

Lemma dec_recognisable p : decidable p -> recognisable p.
Proof.
  intros [u [[cls_u lam_u] dec_u_p]].
  exists (lambda (u 0 I (lambda Omega) I)); split; value.
    + intros t. specialize (dec_u_p t).
      split; intros H; destruct dec_u_p; try tauto. 
      * destruct H0 as [_ u_T]. eexists; eapply evaluates_equiv; split;[|eexists;reflexivity]. solvered.
      * destruct H. destruct H0.
        assert ((lambda ((((u 0) I) (lambda Omega)) I)) (tenc t) ≡ Omega). clear H. solveeq.
        rewrite H2 in H. destruct (eva_Omega). eexists; eauto.
Qed.

Lemma dec_rec p : decidable p -> recognisable p /\ recognisable (complement p).
Proof.
  intros decp; split.
  - eapply (dec_recognisable decp).
  - eapply decidable_complement in decp. eapply (dec_recognisable decp).
Qed.

(** ** Scott's theorem *)

Theorem SecondFixedPoint (s : term) : closed s -> exists t, closed t /\ s (tenc t) ≡ t.
Proof.
  intros cls_s.
  pose (C := (.\ "x"; !s (!App "x" (!Q "x"))) : term). cbn in C.
  pose (t := C (tenc C)).
  exists t. split; [subst t C; value|].
  symmetry. unfold t, C.
  transitivity (s (App (tenc C) (Q (tenc C)))). solvered.
  rewrite Q_correct, App_correct. reflexivity.
Qed.


Theorem Scott p : 
  (forall s t, closed s -> p s -> closed t -> t ≡ s -> p t) ->
  (exists t1, closed t1 /\ p t1) -> (exists t2, closed t2 /\ ~ p t2) ->
  ~ decidable p.                                                                 
Proof.
  intros p_equiv [s1 [cls_s1 ps1]] [s2 [cls_s2 nps2]] [u [[cls_u lam_u] Hu]].
  pose (x := lambda(u 0 (lambda s2) (lambda s1) I)).
  destruct (SecondFixedPoint (s := x)) as [t [cls_t H]]; subst x; value.
  eapply eqTrans with (s := u (tenc t) (lambda s2) (lambda s1) I) in H.
  destruct (Hu t) as [ [pt Ht] | [npt Ht ]].
  - eapply nps2, p_equiv; eauto.
    rewrite <- H, Ht. symmetry. solvered.
  - eapply npt,p_equiv with (s := s1); eauto.
    rewrite <- H, Ht; solvered.
  -symmetry. now dobeta.
Qed.

Lemma eva_dec : ~ decidable eva.
Proof.
  eapply Scott.
  - intros s t cls_s [x [Hx lx] % evaluates_equiv] cls_t t_e_s.
    exists x; eapply evaluates_equiv; split;[|value]. now rewrite t_e_s.
  - exists I. repeat split. exists I; eapply evaluates_equiv;split.  reflexivity. value. 
  - exists Omega. repeat split. eapply eva_Omega. 
Qed.

Lemma equiv_spec_decidable : forall t, closed t -> ~ decidable (fun x => x ≡ t).
Proof. 
  intros t cls_t H.
  eapply Scott; try eassumption; cbn.
  - intros s t0 cls_s H0 cls_t0 H1. rewrite H1. assumption.
  - exists t. repeat split. value. reflexivity.
  - destruct H as (? & ? & ?). destruct (H0 I) as [ [?  ?] | [ ? ?] ]. exists Omega.
    split. value. intros H3. eapply I_neq_Omega.
    rewrite H1, H3. reflexivity.
    exists I. split. value. eassumption.
Qed.
    
