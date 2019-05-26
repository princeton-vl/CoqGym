(** * First-Order Logic *)

From Undecidability Require Export Shared.Prelim FOL.Reductions Problems.PCP.

(** ** Syntax *)

Notation var := nat (only parsing).
Notation par := nat (only parsing).

Inductive term : Type :=
  V (v : var) | P (p : par)
| t_f : bool -> term -> term
| t_e : term.

Coercion V : var >-> term.

Inductive logic := frag | full.
Existing Class logic.
Existing Instance full | 1.
Existing Instance frag | 0.

Inductive form : logic -> Type :=
| Pr {b} : term -> term -> form b
| Q {b} : form b
| Fal : form full
| Impl {b} : form b -> form b -> form b
| All {b} : var -> form b -> form b.

Lemma form_frag_ind : forall P : form frag -> Prop,
       (forall (t t0 : term), P (Pr t t0)) ->
       (P Q) ->
       (forall (f3 : form frag),
        P f3 -> forall f4 : form frag, P f4 -> P (Impl f3 f4)) ->
       (forall (n : var) (f6 : form frag), P f6 -> P (All n f6)) ->
       forall (f8 : form frag), P f8.
Proof.
  intros. remember frag as b. induction f8; try now inv Heqb; firstorder.
Qed.

Notation "phi --> psi" := (Impl phi psi) (right associativity, at level 55).
Notation "∀ v ; phi" := (All v phi) (at level 56, right associativity).
Notation "⊥" := (Fal).
Notation "¬ phi" := (phi --> ⊥) (at level 20).

Section fixb. Variable b : logic.
Fixpoint impl (A : list (form b)) phi :=
  match A with
  | [] => phi
  | psi :: A => Impl psi (impl A phi)
  end.
End fixb.

Notation "A ==> phi" := (impl A phi) (right associativity, at level 55).


(** ** Enumerability *)

Fixpoint L_term n : list term :=
  match n with
  | 0 => [t_e]
  | S n => L_term n ++ [V n; P n] ++ [ t_f b t | (b,t) ∈ (L_T bool n × L_term n) ]
  end.

Instance enumT_term : enumT term.
Proof.
  exists L_term.
  - intros ?; cbn; eauto.
  - intros t. induction t.
    + exists (S v); cbn; eauto.
    + exists (S p); cbn; eauto.
    + destruct IHt as [m1], (el_T b) as [m2].
      exists (1 + m1 + m2). cbn. in_app 4. in_collect (b, t); eapply cum_ge'; eauto; omega.
    + exists 0. cbn; eauto.
Qed.

Fixpoint L_form {b} n : list (form b) :=
  match n with
  | 0 => []
  | S n => L_form n
            ++ [Q]
            ++ [ Pr s t | (s,t) ∈ (L_T term n × L_T term n) ]
            ++ [ phi1 --> phi2 | (phi1, phi2) ∈ (L_form n × L_form n) ]
            ++ [ ∀ n; phi | (n,phi) ∈ (L_T nat n × L_form n) ]
            ++ match b with
                 frag => []
               | full => [Fal]
               end
  end.

Instance enumT_form {b} : enumT (form b).
Proof with (try eapply cum_ge'; eauto; omega).
  exists L_form.
  - eauto.
  - intros phi. induction phi.
    + destruct (el_T t) as [m1], (el_T t0) as [m2]. exists (1 + m1 + m2). cbn.
      in_app 3. in_collect (t, t0)...
    + exists 1. cbn; eauto.
    + exists 1; cbn; firstorder.
    + destruct IHphi1 as [m1], IHphi2 as [m2]. exists (1 + m1 + m2). cbn.
      in_app 4. in_collect (phi1, phi2)...
    + destruct IHphi as [m1], (el_T n) as [m2]. exists (1 + m1 + m2). cbn -[L_T].
      in_app 5. in_collect (n, phi)...
Qed.

Instance dec_term : eq_dec term.
Proof.
  intros ? ?; unfold dec; repeat decide equality.
Qed.

Instance dec_logic : eq_dec logic.
Proof.
  intros ? ?; unfold dec; decide equality.
Qed.

Require Import EqdepFacts.

Lemma dec_form {b1 b2} phi1 phi2 : dec (eq_dep logic form b1 phi1 b2 phi2).
Proof.
  unfold dec. revert phi2; induction phi1; intros; try destruct phi2.
  all: try now right; inversion 1.
  all: try decide (b0 = b); subst; try now right; inversion 1; congruence.
  all: try now left.
  - decide (t = t1); decide (t0 = t2); subst; try now right; inversion 1; congruence.
    now left.
  - destruct (IHphi1_1 phi2_1), (IHphi1_2 phi2_2); subst; try firstorder congruence.
    left. eapply Eqdep_dec.eq_dep_eq_dec in e; eapply Eqdep_dec.eq_dep_eq_dec in e0.
    all: try eapply dec_logic.
    subst; econstructor.

    all: right; intros ? % Eqdep_dec.eq_dep_eq_dec; try eapply dec_logic.
    all: eapply n. all: inversion H0; eapply eq_sigT_eq_dep in H2; eapply Eqdep_dec.eq_dep_eq_dec in H2; try eapply dec_logic; subst. econstructor. 
    all: eapply eq_sigT_eq_dep in H1; eapply Eqdep_dec.eq_dep_eq_dec in H1; try eapply dec_logic; subst.
    all: econstructor. 
  - decide (n = n0); destruct (IHphi1 phi2); subst.
    eapply Eqdep_dec.eq_dep_eq_dec in e0; try eapply dec_logic; subst. now left.
    all: right; inversion 1; try eapply eq_sigT_eq_dep in H2; try eapply Eqdep_dec.eq_dep_eq_dec in H2; try eapply dec_logic; subst.
    eapply n1. econstructor. all:congruence.
Qed.

Instance eq_dec_form {b : logic} phi1 phi2 : dec (phi1 = phi2 :> form b).
Proof.
  destruct (dec_form phi1 phi2).
  - eapply Eqdep_dec.eq_dep_eq_dec in e; try eapply dec_logic; subst. now left.
  - right. intros ->. now eapply n.
Qed.
