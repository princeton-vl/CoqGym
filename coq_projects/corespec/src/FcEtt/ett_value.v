Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Require Export FcEtt.tactics.
Require Export FcEtt.imports.
Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_ind.


Require Export FcEtt.ext_context_fv.

Require Import FcEtt.ext_wf.
Import ext_wf.

Require Import FcEtt.utils.
Require Import FcEtt.erase_syntax.
Require Export FcEtt.toplevel.


(* ------------------------------------------ *)

(* Paths *)

Lemma Path_tm_subst_tm_tm : forall T a x b, Path T a -> lc_tm b -> Path T (tm_subst_tm_tm b x a).
Proof. induction 1; try destruct rho; simpl; eauto with lngen.
Qed.

Lemma Path_co_subst_co_tm : forall T a x b, Path T a -> lc_co b -> Path T (co_subst_co_tm b x a).
Proof. induction 1; try destruct rho; simpl; eauto with lngen.
Qed.

Hint Resolve Path_tm_subst_tm_tm Path_co_subst_co_tm : lngen.

Lemma Path_unique : forall T1 T2 a, Path T1 a -> Path T2 a -> T1 = T2.
Proof.
  induction 1; intros P; inversion P; auto.
Qed.

(* DataTy *)

Lemma DataTy_tm_subst_tm_tm : forall b x A,
    DataTy A a_Star -> lc_tm b -> DataTy (tm_subst_tm_tm b x A) a_Star.
Proof.
  intros. dependent induction H; simpl; eauto.
  - pick fresh y and apply DT_Pi.
    eauto with lngen.
    autorewrite with subst_open_var; eauto.
  - pick fresh y and apply DT_CPi.
    eauto with lngen.
    autorewrite with subst_open_var; eauto.
Qed.

Lemma DataTy_co_subst_co_tm : forall b x A,
    DataTy A a_Star -> lc_co b -> DataTy (co_subst_co_tm b x A) a_Star.
Proof.
  intros. dependent induction H; simpl; eauto.
  - pick fresh y and apply DT_Pi.
    eauto with lngen.
    autorewrite with subst_open_var; eauto.
  - pick fresh y and apply DT_CPi.
    eauto with lngen.
    autorewrite with subst_open_var; eauto.
Qed.

Hint Resolve DataTy_tm_subst_tm_tm DataTy_co_subst_co_tm : lngen.

(* ------------------------------------------- *)

Definition decide_Path : forall a, lc_tm a -> (exists T, Path T a) \/ (forall T, not (Path T a)).
Proof.
  induction a; intro lc.
  all: try solve [left; eauto].
  all: try solve [right; move => T h1; inversion h1].
  - lc_inversion c. destruct IHa1 as [[T h0]|n].
    auto.
    left; eauto.
    right. move => T h1. inversion h1.
    subst. unfold not in n. eauto.
  - lc_inversion c. destruct IHa as [[T h0]|n].
    auto.
    left; eauto.
    right. intros T h; inversion h; subst; unfold not in n; eauto.
  - lc_inversion c. destruct IHa as [[T h0]|n].
    auto.
    left. exists T. auto.
    right. intros T h; inversion h; subst; unfold not in n; eauto.
Qed.

(* ------------------------------------------- *)

(* Values and CoercedValues *)

Lemma tm_subst_tm_tm_Value_mutual :
  (forall v,  CoercedValue v -> forall b x,  lc_tm b -> CoercedValue (tm_subst_tm_tm b x v)) /\
  (forall v, Value v -> forall b x,  lc_tm b -> Value (tm_subst_tm_tm b x v)).
Proof.
  apply CoercedValue_Value_mutual; simpl.
  all: try solve [inversion 1 | econstructor; eauto]; eauto.
  all: try solve [intros;
                  eauto using tm_subst_tm_tm_lc_tm,
                  tm_subst_tm_constraint_lc_constraint,
                  tm_subst_tm_co_lc_co,
                  Path_tm_subst_tm_tm].
  all: try solve [intros;
    constructor; eauto using tm_subst_tm_tm_lc_tm,  tm_subst_tm_constraint_lc_constraint;
    match goal with [H: lc_tm (?a1 ?a2), K : lc_tm ?b |- _ ] =>
                    move: (tm_subst_tm_tm_lc_tm _ _ x H K) => h0; auto end].

  - intros L a v H b x H0.
    econstructor; eauto.
    instantiate (1 := L \u singleton x) => x0 h0.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto.
  - intros L A a l c H b x H0.
    econstructor; eauto.
    apply tm_subst_tm_tm_lc_tm; auto.
    instantiate (1 := L \u singleton x) => x0 h0.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto.
Qed.

Lemma Value_tm_subst_tm_tm :
  (forall v b x, Value v -> lc_tm b -> Value (tm_subst_tm_tm b x v)).
Proof.
  intros v b x H H0.
  apply tm_subst_tm_tm_Value_mutual; auto.
Qed.

Lemma CoercedValue_tm_subst_tm_tm :
  (forall v b x, CoercedValue v -> lc_tm b -> CoercedValue (tm_subst_tm_tm b x v)).
Proof.
  intros v b x H H0.
  destruct (tm_subst_tm_tm_Value_mutual); auto.
Qed.

(* ------------------------------------------------- *)

Lemma Value_UAbsIrrel_exists : ∀ x (a : tm),
    x `notin` fv_tm a
    → (Value (open_tm_wrt_tm a (a_Var_f x)))
    → Value (a_UAbs Irrel a).
Proof.
  intros.
  eapply (Value_UAbsIrrel ({{x}})); eauto.
  intros.
  rewrite (tm_subst_tm_tm_intro x); eauto.
  eapply Value_tm_subst_tm_tm; auto.
Qed.

Lemma Value_AbsIrrel_exists : ∀ x (A a : tm),
    x `notin` fv_tm a
    -> lc_tm A
    → (CoercedValue (open_tm_wrt_tm a (a_Var_f x)))
    → Value (a_Abs Irrel A a).
Proof.
  intros.
  eapply (Value_AbsIrrel ({{x}})); eauto.
  intros.
  rewrite (tm_subst_tm_tm_intro x); eauto.
  eapply CoercedValue_tm_subst_tm_tm; auto.
Qed.

(* ----- *)

Lemma co_subst_co_tm_Value_mutual :
  (forall v,  CoercedValue v -> forall b x,  lc_co b -> CoercedValue (co_subst_co_tm b x v)) /\
  (forall v, Value v -> forall b x,  lc_co b -> Value (co_subst_co_tm b x v)).
Proof.
  apply CoercedValue_Value_mutual; simpl.
  all: try solve [inversion 1 | econstructor; eauto]; eauto.
  all: try solve [intros;
                  eauto using co_subst_co_tm_lc_tm,
                  co_subst_co_constraint_lc_constraint,
                  co_subst_co_co_lc_co,
                  Path_co_subst_co_tm].
  all: try solve [intros;
    constructor; eauto using co_subst_co_tm_lc_tm,
                              co_subst_co_constraint_lc_constraint;
    match goal with [H: lc_tm (?a1 ?a2), K : lc_co ?b |- _ ] =>
                    move: (co_subst_co_tm_lc_tm _ _ x H K) => h0; auto end].
  - intros.
    pick fresh y.
    eapply Value_UAbsIrrel_exists with (x:=y).
    eapply fv_tm_tm_tm_co_subst_co_tm_notin; eauto.
    move: (H y ltac:(eauto) b x H0) => h0.
    rewrite co_subst_co_tm_open_tm_wrt_tm in h0.
    simpl in h0. auto. auto.
  - intros.
    pick fresh y.
    eapply Value_AbsIrrel_exists with (x:=y).
    eapply fv_tm_tm_tm_co_subst_co_tm_notin; eauto.
    eapply co_subst_co_tm_lc_tm; eauto.
    move: (H y ltac:(eauto) b x H0) => h0.
    rewrite co_subst_co_tm_open_tm_wrt_tm in h0; auto.
Qed.

Lemma Value_co_subst_co_tm :
  (forall v b x, Value v -> lc_co b -> Value (co_subst_co_tm b x v)).
Proof.
  intros v b x H H0.
  apply co_subst_co_tm_Value_mutual; auto.
Qed.

Lemma CoercedValue_co_subst_co_tm :
  (forall v b x, CoercedValue v -> lc_co b -> CoercedValue (co_subst_co_tm b x v)).
Proof.
  intros v b x H H0.
  destruct (co_subst_co_tm_Value_mutual); auto.
Qed.



(* ------------------------------------------ *)

Lemma decide_Value_mutual : forall a,
    lc_tm a ->
    (Value a \/ not (Value a)) /\ (CoercedValue a \/ (not (CoercedValue a))).
Proof.
  induction 1; try destruct rho.
  all: try solve [split; left; auto].
  all: try solve [split; right; intro h; inversion h; try inversion H;
                  try inversion H1].
  - pick fresh x.
    destruct (H1 x) as [[V|NV][CV|NCV]].
    all: try solve [split; left; eauto using Value_AbsIrrel_exists].
    + split;
      right; intro h; inversion h; try inversion H2; subst;
      apply NCV;
      pick fresh y;
      rewrite (tm_subst_tm_tm_intro y); eauto;
      eapply CoercedValue_tm_subst_tm_tm; eauto.
  - pick fresh x.
    destruct (H0 x) as [[V|NV]_].
    all: try solve [split; left; eauto using Value_UAbsIrrel_exists].
    split.
    all: right; intro h; inversion h; try inversion H1; subst; apply NV;
      pick fresh y;
      rewrite (tm_subst_tm_tm_intro y); eauto;
        eapply Value_tm_subst_tm_tm; eauto.
  - destruct (IHlc_tm1) as [[V|NV][CV|NCV]];
      destruct (decide_Path H) as [[T P]|NP].
    all: split.
    all: try solve [left; eauto].
    all: try solve [right; intro h; inversion h; try inversion H1; eapply NP; eauto].
    all: try solve [right; intro h; inversion h; try inversion H1; done].
  - destruct (IHlc_tm1) as [[V|NV][CV|NCV]];
      destruct (decide_Path H) as [[T P]|NP].
    all: split.
    all: try solve [left; eauto].
    all: try solve [right; intro h; inversion h; try inversion H1; eapply NP; eauto].
    all: try solve [right; intro h; inversion h; try inversion H1; done].
  - destruct (IHlc_tm) as [[V|NV][CV|NCV]].
    all: split.
    all: try solve [left; eauto].
    all: try solve [right; intro h; inversion h].
    right. intro h; inversion h. inversion H1. done.
    right. intro h; inversion h. inversion H1. done.
  - destruct (IHlc_tm) as [[V|NV][CV|NCV]];
      destruct (decide_Path H) as [[T P]|NP].
    all: split.
    all: try solve [left; eauto].
    all: try solve [right; intro h; inversion h; try inversion H1; eapply NP; eauto].
    all: try solve [right; intro h; inversion h; try inversion H1; done].
Qed.


Lemma decide_Value : forall a, lc_tm a -> (Value a \/ not (Value a)).
Proof.
  intros a.
  eapply decide_Value_mutual.
Qed.

Lemma decide_CoercedValue : forall a, lc_tm a -> (CoercedValue a \/ not (CoercedValue a)).
Proof.
  intros a.
  eapply decide_Value_mutual.
Qed.


  (* ------------------------------------------ *)

Lemma DataTy_value_type : forall A, DataTy A a_Star -> value_type A.
Proof.
  intros A H.
  dependent induction H; eauto with lc.
Qed.
