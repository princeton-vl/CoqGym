Require Export String.
From Undecidability.L Require Export Preliminaries.

(** * Definition of L *)
(** ** Syntax *)

Inductive term : Type :=
| var (n : nat) : term
| app (s : term) (t : term) : term
| lambda (s : term).

Definition lam s := exists t, s = lambda t.
Hint Unfold lam.

Lemma lambda_lam s : lam (lambda s).
Proof.
  now exists s.
Qed.
Hint Resolve lambda_lam.

Fixpoint size t :=
  match t with
  | var n => 1
  | app s t => size s + size t
  | lambda s => 1 + size s
  end.

Coercion app : term >-> Funclass. 
Coercion var : nat >-> term.

Instance term_eq_dec : eq_dec term.
Proof.
  intros ? ?; hnf; repeat decide equality.
Defined.

Hint Resolve term_eq_dec.

(** ** Named abstractions *)

Require Import String.

Inductive bterm : Type :=
| bvar (x : string) : bterm
| bapp (s t : bterm) : bterm
| blambda (x : string) (s : bterm) : bterm
| bter (s : term) : bterm.

Open Scope string_scope.

Instance eq_dec_string : eq_dec string.
Proof.
  eapply string_dec.
Defined.

Fixpoint convert' (F : list string) (s : bterm) : term := match s with
| bvar x => match pos _ x F with None => 100 | Some t =>  t end
| bapp s t => app (convert' F s) (convert' F t)
| blambda x s => lambda (convert' (x:: F) s)
| bter t => t
end.

Coercion bvar : string >-> bterm.
Coercion bapp : bterm >-> Funclass.
Definition convert := convert' [].
Coercion convert : bterm >-> term.

Arguments convert /.

Hint Unfold convert: cbv.

Notation ".\ x , .. , y ; t" := ((blambda x .. (blambda y t) .. )) (at level 100, right associativity).
Notation "'λ'  x , .. , y ; t" := ((blambda x .. (blambda y t) .. )) (at level 100, right associativity).

Notation "'!' s" := (bter s) (at level 0).

Implicit Types s t u v : term.
Implicit Types p q : term -> Prop.
Implicit Types n m k l : nat.

(** ** Substitution and closedness *)

Fixpoint subst s k u :=
  match s with
      | var n => if decision (n = k) then u else (var n)
      | app s t => app (subst s k u) (subst t k u)
      | lambda s => lambda (subst s (S k) u)
  end.
Hint Unfold subst : cbv.

Fixpoint bound (k : nat) (t : term) : bool :=
match t with
| var n => if decision (n < k) then true else false
| app s t => andb (bound k s) (bound k t)
| lambda s => bound (S k) s
end.

Definition closed s := bound 0 s = true.
Definition proc s := closed s /\ lam s.

Lemma bound_ge k s : bound k s = true -> forall m, m >= k -> bound m s = true.
Proof.
  revert k; induction s; cbn; intros.
  - unfold bound in *. decide (n < k); decide (n < m); try congruence. omega.
  - eapply Bool.andb_true_iff in H as []. erewrite IHs1, IHs2; eauto.
  - eapply IHs. eassumption. omega.
Qed.

Lemma bound_closed_k s k n u : bound n s = true -> k >= n -> subst s k u = s.
Proof with eauto.
  revert k n; induction s; intros; cbn.
  - decide (n = k)... subst. unfold bound in H. decide (k < n0). omega. congruence.
  - cbn in H. eapply Bool.andb_true_iff in H as []. erewrite IHs1, IHs2...
  - erewrite IHs... omega.
Qed.

Lemma closed_subst s k u : closed s -> subst s k u = s.
Proof.
  intros. eapply bound_ge in H. eapply bound_closed_k in H; eauto. omega.
Qed.

Lemma closed_app s t : closed (s t) -> closed s /\ closed t.
Proof.
  intros cls. now eapply Bool.andb_true_iff in cls. 
Qed.

Lemma app_closed s t : closed s -> closed t -> closed (s t).
Proof.
  unfold closed. cbn. now intros -> ->.
Qed.

(** ** Named procedures *)

Definition I : term := .\"x"; "x".
Definition T : term := .\"x","y"; "x".
Definition F : term := .\"x","y"; "y".

Definition omega : term := .\"x"; "x" "x".
Definition Omega := omega omega.
Definition D: term := lambda (omega omega).

(** ** Evaluation relation *)

Inductive evaluates : term -> term -> Prop :=
  evaluates_lam s : evaluates (lambda s) (lambda s)
| evaluates_app s t u v w : evaluates s (lambda u) -> evaluates t v -> evaluates (subst u 0 v) w ->
                            evaluates (s t) w.
Hint Constructors evaluates.

Notation "s '▷' t" := (evaluates s t) (at level 50).

Definition eva s := exists t, evaluates s t.
Hint Unfold eva.

Lemma evaluates_abst s t : s ▷ t -> lam t.
Proof.
  induction 1; eauto.
Qed.

Lemma evaluates_functional s t1 t2 :
  s ▷ t1 -> s ▷ t2 -> t1 = t2.
Proof.
  intros H. revert t2. induction H; intros.
  - now inv H.
  - inv H2. eapply IHevaluates3.
    eapply IHevaluates1 in H5. inv H5.
    eapply IHevaluates2 in H6. inv H6.
    eassumption.
Qed.  
      
(* Counterexample to Fact 5.2 *)

Lemma evaluates_bound : ~ forall s t n, s ▷ t -> bound n s = true -> bound n t = true.
Proof.
  intros H. specialize (H ((lambda (lambda 2)) (lambda 1)) (lambda 2) 1).
  cbn in H. eapply Bool.diff_false_true, H; eauto.
  repeat econstructor.
Qed.

Lemma bound_subst s t k : bound (S k) s = true -> bound k t = true -> bound k (subst s k t) = true.
Proof.
  revert k t; induction s; intros k t cls_s cls_t; cbn.
  - decide (n = k). subst. eauto. unfold bound in cls_s.
    decide (n < S k). unfold bound. decide (n < k). reflexivity. omega. congruence.
  - cbn in cls_s. eapply Bool.andb_true_iff in cls_s as []. rewrite IHs1, IHs2; eauto.
  - cbn in cls_s. rewrite IHs; eauto. eapply bound_ge; eauto.
Qed.

Lemma evaluates_closed s t : s ▷ t -> closed s -> closed t.
Proof.
  induction 1; cbn; intros.
  - eauto.
  - unfold closed in H2. cbn in H2. eapply Bool.andb_true_iff in H2 as [].
    firstorder using bound_subst.
Qed.

Lemma app_eva s t : eva (s t) -> eva s /\ eva t.
Proof.
  inversion 1. inv H0. firstorder.
Qed.

Lemma F_eva s t : eva (F s t) <-> eva s /\ eva t.
Proof.
  intuition.
  - now eapply app_eva in H as (H % app_eva & ?).
  - now eapply app_eva in H.
  - destruct H0, H1. exists x0. econstructor. econstructor. econstructor.
    eassumption. econstructor. eassumption. cbn. eapply evaluates_abst in H0. firstorder. subst.
    econstructor.
Qed.

Lemma F_correct s t : lam s -> lam t -> F s t ▷ t.
Proof.
  intros [? ->] [? ->]. repeat econstructor.
Qed.

Lemma eva_Omega : ~ eva Omega.
Proof.
  inversion 1. remember Omega as Om. induction H0; inv HeqOm.
  inv H0_. inv H0_0. cbn in H0_1. eapply IHevaluates3.
  cbn. reflexivity. eassumption.
Qed.

Lemma eva_D s : ~ eva (D s).
Proof.
  inversion 1. inversion H0. inv H3. cbn in H6.
  eapply eva_Omega. exists x. eassumption.
Qed.

Lemma evaluates_D s v : D s ▷ v <-> False.
Proof.
  firstorder using eva_D.
Qed.

(** * Uniformly confluent reduction semantics *)


(** ** One-step reduction *)
Reserved Notation "s '≻' t" (at level 50).

Inductive step : term -> term -> Prop :=
| stepApp  s t     : app (lambda s) (lambda t) ≻ subst s 0 (lambda t)
| stepAppR s t  t' : t ≻ t' -> app s t ≻ app s t'
| stepAppL s s' t  : s ≻ s' -> app s t ≻ app s' t
where "s '≻' t" := (step s t).

Hint Constructors step.

Ltac inv_step :=
  match goal with
  | H : step (app _ _) _ |- _ => inv H
  | H : step (lambda _) _ |- _ => inv H
  | H : step (var _) _ |- _ => inv H
  end.

(** ** Reflexive-transitive closure and step-indexed closure *)

Inductive star : term -> term -> Prop :=
  star_refl s : star s s
| star_step s u t : step s u -> star u t -> star s t.

Inductive stepn : nat -> term -> term -> Prop :=
  stepn_refl s : stepn 0 s s
| stepn_step s u t n : step s u -> stepn n u t -> stepn (S n) s t.

Hint Constructors step star stepn evaluates.

Instance star_trans : Transitive star.
Proof.
  intros s t u H1 H2. induction H1; eauto.
Qed.

Notation "s '≻*' t" := (star s t) (at level 40).
Notation "s '≻^' n t" := (stepn n s t) (at level 40, n at level 5).

Instance star_app : Proper (star ==> star ==> star) app.
Proof.
  intros s s' H t t' H1.
  induction H; intros; eauto.
  induction H1; eauto.
Qed.

Lemma star_stepn s t : s ≻* t <-> exists n, stepn n s t.
Proof.
  split; intros H.
  - induction H; eauto.
    destruct IHstar. eauto.
  - destruct H. induction H; eauto.
Qed.

Lemma evaluates_star s t : s ▷ t -> s ≻* t /\ lam t.
Proof.
  split.
  - induction H; eauto.
    eapply evaluates_abst in H0 as []. subst.
    rewrite star_app; eauto.
  - now eapply evaluates_abst in H.
Qed.

Lemma step_evaluates s s' t : s ≻ s' -> s' ▷ t -> s ▷ t.
Proof.
  intros H; revert t; induction H; intros; try inv H0; eauto.
Qed.

Lemma steps_evaluates s s' t : s ≻* s' -> s' ▷ t -> s ▷ t.
Proof.
  induction 1; eauto using step_evaluates.
Qed.

Lemma star_evaluates s t : s ≻* t -> lam t -> s ▷ t.
Proof.
  induction 1; inversion 1; subst; eauto using step_evaluates.
Qed.

Lemma stepn_plus s s' t n m : s ≻^n s' -> s' ≻^m t -> s ≻^(n+m) t.
Proof.
  induction 1; cbn; intros; eauto.
Qed.


Instance star_PreOrder : PreOrder star.
Proof.
  constructor; hnf; eauto using star_trans.
Qed.

(** ** Recursion operator *)

Definition C := .\ "x", "y"; "y" (.\ "z"; "x" "x" "y" "z").
Definition rho s : term := Eval cbv in .\ "x" ; C C !s "x".

Lemma rho_lam s : lam (rho s).
Proof.
  unfold rho. firstorder.
Qed.

Lemma rho_closed s : closed s -> closed (rho s).
Proof.
  unfold rho, C, closed. cbn. intros. eapply bound_ge in H. now rewrite H. omega.
Qed.

Lemma rho_correct u v : proc u -> proc v -> rho u v ≻^3 u (rho u) v.
Proof.
  intros [? [? H1]] [? [? H2]]; rewrite H1 , H2.
  do 2 econstructor. rewrite <- H1. cbn. rewrite closed_subst; eauto.
  rewrite H1. cbn. eauto.
Qed.

Lemma uniform_confluence s t1 t2 :
  s ≻ t1 -> s ≻ t2 -> t1 = t2 \/ exists u, t1 ≻ u /\ t2 ≻ u.
Proof with try subst; repeat inv_step; eauto 10 using step.
  intros Hst1. revert t2. induction Hst1; intros t2 Ht2...
  - destruct (IHHst1 _ H2)... destruct H as (? & [])...
  - destruct (IHHst1 _ H2)... destruct H as (? & [])...
Qed.

Lemma parametric_semi_confluence s t1 t2 n :
  s ≻ t1 -> s ≻^n t2 -> exists k l u, k <= n /\ l <= 1 /\ t1 ≻^k u /\ t2 ≻^l u /\ 1 + k = n + l.
Proof.
  revert s t1 t2; induction n; intros; inv H0.
  - exists 0, 1, t1; eauto 9.
  - destruct (uniform_confluence H H2) as [-> | (u' & ? & ?) ]; eauto 10.
    destruct (IHn _ _ _ H1 H3) as (k' & l' & u'' & ? & ? & ? & ? & ?).
    exists (S k'), l', u''. repeat split; eauto; omega.
Qed.

Lemma parametric_confluence s t1 t2 m n :
  s ≻^m t1 -> s ≻^n t2 -> exists k l u, k <= n /\ l <= m /\ t1 ≻^k u /\ t2 ≻^l u /\ m + k = n + l.
Proof.
  revert s t1 t2 n; induction m; intros; inv H.
  - exists n, 0, t2. eauto.
  - destruct (parametric_semi_confluence H2 H0) as (k & l & u' & ? & ? & ? & ? & ?).
    destruct (IHm _ _ _ _ H3 H4) as (k' & l' & u'' & ?  & ? & ? & ? & ?).
    exists k', (l + l'), u''. repeat split; eauto using stepn_plus; try omega.
Qed.

Lemma confluence s t1 t2 : s ≻* t1 -> s ≻* t2 -> exists u, t1 ≻*u /\ t2 ≻* u.
Proof.
  intros [] % star_stepn [] % star_stepn.
  edestruct (parametric_confluence H H0) as (k & l & u & ? & ? & ? & ? & ?).
  exists u. split; eapply star_stepn; eauto.
Qed.

Definition evaluatesin n s t := (s ≻^n t /\ lam t).
Notation "s '▷^' n t" := (evaluatesin n s t) (at level 40, n at level 5).

Definition stepplus s t := (exists s', s ≻ s' /\ s' ≻* t).
Notation "s '≻^+' t" := (stepplus s t) (at level 40).

Lemma unique_step_index s m t n : s ▷^m t -> s ▷^n t -> m = n.
Proof.
  intros (? & ? & ->) [].
  destruct (parametric_confluence H H0) as (k & l & u & ? & ? & ? & ? & ?).
  inv H4; inv H5; [ omega | inv_step.. ].
Qed.

Lemma stepplus_stepn s t : s ≻^+ t <-> exists n, s ≻^(S n) t.
Proof.
  intuition.
  - destruct H as ( ? & ? & (? & ?) % star_stepn). eauto.
  - destruct H as (? & ?). inv H. 
    econstructor. split. eassumption. eapply star_stepn. eauto.
Qed.

Lemma triangle s n t s' : s ▷^n t -> s ≻^+ s' -> exists k, k < n /\ s' ▷^k t.
Proof.
  intros (? & ? & ->) [] % stepplus_stepn.
  destruct (parametric_confluence H H0) as (k & l & u & ? & ? & ? & ? & ?).
  inv H3. exists l. firstorder. inv_step.
Qed.

Instance step_star_subrelation : subrelation step star.
Proof.
  cbv. eauto.
Qed.

Instance stepplus_star_subrelation : subrelation stepplus star.
Proof.
  cbv. intros. destruct H as (? & ? & ?). eauto. 
Qed.

(** ** Reduction equivalence *)

Reserved Notation "s '≡' t" (at level 50).

Inductive equiv : term -> term -> Prop :=
  | eqStep s t : step s t -> s ≡ t
  | eqRef s : s ≡ s
  | eqSym s t : t ≡ s -> s ≡ t
  | eqTrans s t u: s ≡ t -> t ≡ u -> s ≡ u
where "s '≡' t" := (equiv s t).

Hint Constructors equiv.

(* *** Properties of the equivalence relation *)

Instance equiv_Equivalence : Equivalence equiv.
Proof.
  constructor; hnf.
  - apply eqRef.
  - intros. eapply eqSym. eassumption.
  - apply eqTrans.
Qed.

Lemma star_equiv s t : s ≻* t -> s ≡ t.
Proof.
  induction 1; eauto.
Qed.

Lemma church_rosser s t : s ≡ t -> exists u, s ≻* u /\ t ≻* u.
Proof.
  induction 1; firstorder eauto. destruct (confluence H1 H4) as (? & ? & ?). eauto using star_trans.
Qed.

Instance app_equiv : Proper (equiv ==> equiv ==> equiv) app.
Proof with eauto.
  intros s s' H.
  induction H; intros ? ??...
  - eapply eqTrans. eapply eqStep. eapply stepAppL. eassumption.
    induction H0...
  - induction H...
Qed.

Lemma equiv_star_lam s t : lam t -> s ≡ t <-> s ≻* t.
Proof.
  intros. split; eauto using star_equiv.
  intros. eapply church_rosser in H0 as (u & H1 & H2). inv H2; eauto.
  inv H. inv_step.
Qed.

Lemma unique_normal_forms (s t : term) : lam s -> lam t ->  s ≡ t -> s = t.
Proof.
  intros ls lt H % equiv_star_lam; eauto. inv ls. inv H. reflexivity. inv H0.
Qed.

Lemma evaluates_equiv s t : s ▷ t <-> s ≡ t /\ lam t.
Proof with eauto using star_equiv, evaluates_abst.
  firstorder...
  - eapply evaluates_star in H as []... 
  - eapply star_evaluates... eapply equiv_star_lam...
Qed.

Lemma equiv_evaluates s t v : s ≡ t -> s ▷ v -> t ▷ v.
Proof.
  intros. eapply evaluates_star in H0 as [].
  eapply church_rosser in H as (? & ? & ?).
  destruct (confluence H0 H) as (? & ? & ?). destruct H1; subst. inv H3.
  eauto using star_evaluates, star_trans. inv H1.
Qed.

Instance evaluates_proper :
  Proper (equiv ==> eq ==> iff) evaluates.
Proof.
  intros ? ? ? ? ? ?. subst. firstorder using equiv_evaluates.
Qed.

Instance eva_proper :
  Proper (equiv ==> iff) eva.
Proof.
  intros ? ? ?. firstorder. rewrite H in H0; firstorder. rewrite <- H in H0; firstorder.
Qed.

Lemma equiv_eva s t : s ≡ t -> eva s <-> eva t.
Proof.
  firstorder using equiv_evaluates; exists x; firstorder using equiv_evaluates.
Qed.

Instance evaluates_equiv_subrelation : subrelation evaluates equiv.
Proof.
  intros ? ? ?. now eapply evaluates_equiv.
Qed.

Instance star_equiv_subrelation : subrelation star equiv.
Proof.
  cbv. apply star_equiv.
Qed.

Instance stepplus_equiv_subrelation : subrelation stepplus equiv.
Proof.
  cbv. intros. eapply star_equiv. eapply stepplus_star_subrelation. eauto.
Qed.

Instance evaluatesin_equiv_subrelation n : subrelation (evaluatesin n) equiv.
Proof.
  intros ? ? ?. destruct H. eapply star_equiv_subrelation.
  eapply star_stepn. firstorder.
Qed.

Lemma stepplus_star_stepplus s s' t : s ≻^+ s' -> s' ≻* t ->  s ≻^+ t.
Proof.
  intros [? []] ?. exists x. eauto using star_trans.
Qed.

Lemma I_neq_Omega : ~ I ≡ Omega.
Proof.
  intros H. eapply eva_Omega. rewrite <- H. cbv. eauto.
Qed.

