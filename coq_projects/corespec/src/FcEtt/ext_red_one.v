
Require Import FcEtt.sigs.

Require Export FcEtt.imports.
Require Import FcEtt.utils.
Require Export FcEtt.tactics.

Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ind.

Require Export FcEtt.ett_par.
Require Export FcEtt.erase_syntax.


Module ext_red_one (invert : ext_invert_sig).
  Import invert.

Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".



Lemma reduction_in_one_lc : forall a a', reduction_in_one a a' -> lc_tm a -> lc_tm a'.
Proof.
  induction 1; intros; lc_solve.
Unshelve.
  all: try exact nil.
  all: try exact {}.
Qed.

(* ------------------------------------------------------------ *)

(* tactics for substitution proofs. *)

Ltac subst_helper x x0 b0 :=
  replace (a_Var_f x) with (tm_subst_tm_tm b0 x0 (a_Var_f x));
  [idtac| rewrite tm_subst_tm_tm_var_neq; auto];
  replace (g_Var_f x) with (tm_subst_tm_co b0 x0 (g_Var_f x));
  [idtac| simpl; auto];
  try (rewrite <- tm_subst_tm_tm_open_tm_wrt_co; eauto);
  try (rewrite <- tm_subst_tm_tm_open_tm_wrt_co; eauto);
  try (rewrite <- tm_subst_tm_tm_open_tm_wrt_tm; eauto);
  try (rewrite <- tm_subst_tm_tm_open_tm_wrt_tm; eauto);
  eauto using tm_subst_tm_tm_lc_tm.

(* Most of the substitution cases below are about
showing that the term is locally closed after the substiution.
This tactic takes care of that argument.
*)

Ltac lc_subst_case x0 b0  :=
  let x:= fresh in
  lc_inversion x; subst;
  try (rewrite tm_subst_tm_tm_open_tm_wrt_tm; eauto);
  try (rewrite tm_subst_tm_tm_open_tm_wrt_co; eauto);

  econstructor; eauto using Value_lc,
                      tm_subst_tm_tm_lc_tm, tm_subst_tm_co_lc_co,
                tm_subst_tm_constraint_lc_constraint;
    apply_lc_exists x;
      eauto using tm_subst_tm_tm_lc_tm, tm_subst_tm_co_lc_co,
              Value_lc, tm_subst_tm_constraint_lc_constraint;
    subst_helper x x0 b0.

(* ------------------------------------------------- *)

Lemma subst_reduction_in_one : forall a a',
  reduction_in_one a a' -> forall b x, lc_tm b ->
  reduction_in_one (tm_subst_tm_tm b x a)
                   (tm_subst_tm_tm b x a').
Proof.
  intros a a' R. induction R; intros b0 x0 LC;
                   simpl; eauto using tm_subst_tm_tm_lc_tm,
                          tm_subst_tm_co_lc_co.
  - eapply (E_AbsTerm (L \u {{x0}})); eauto. intros x Fr.
    subst_helper x x0 b0.
  - autorewrite with subst_open; eauto.
    econstructor; eauto using tm_subst_tm_tm_lc_tm.
    pick fresh x.
    eapply lc_a_UAbs_exists with (x1:=x).
    inversion H; subst. 
    move: (H2 x) => h0.
    replace (a_Var_f x) with (tm_subst_tm_tm b0 x0 (a_Var_f x)).
    rewrite <- tm_subst_tm_tm_open_tm_wrt_tm; eauto.
    apply tm_subst_tm_tm_lc_tm; eauto. 
    apply tm_subst_tm_tm_var_neq. fsetdec.
  - autorewrite with subst_open; eauto.
    econstructor; eauto using tm_subst_tm_tm_lc_tm.
    match goal with | [ H0 : Value _ |- _ ] =>
    eapply Value_tm_subst_tm_tm in H0; eauto end.
  - lc_subst_case x0 b0.
  - rewrite tm_subst_tm_tm_fresh_eq.
    eapply E_Axiom; eauto.
    match goal with
    | [H : binds ?c ?phi ?G |- _ ] =>
      move:  (toplevel_closed H) => h0
    end.
    move: (Typing_context_fv h0)  => ?. split_hyp.
    fsetdec.
Qed.


Lemma E_AbsTerm_exists : ∀ x (a a' : tm),
    x `notin` (fv_tm a \u fv_tm a') ->
     reduction_in_one (open_tm_wrt_tm a (a_Var_f x))
                       (open_tm_wrt_tm a' (a_Var_f x))
    → reduction_in_one (a_UAbs Irrel a) (a_UAbs Irrel a').
Proof.
  intros.
  eapply (E_AbsTerm ({{x}})).
  intros.
  rewrite (tm_subst_tm_tm_intro x); auto.
  rewrite (tm_subst_tm_tm_intro x a'); auto.
  eapply subst_reduction_in_one; auto.
Qed.


(* Coerced values and values are terminal. *)
Lemma no_Value_reduction :
  (forall a, Value a -> forall b, not (reduction_in_one a b)).
Proof.
  intros a V; induction V.
  all: intros.
  all: intros NH; inversion NH; subst.
  all: try solve [eapply IHV; eauto].

  all: try solve [inversion H0].

  - pick fresh x.
    move: (H0 x ltac:(auto)) => h0.
    move: (H2 x ltac:(auto)) => h5.
    eapply h0; eauto.
Qed.

(* The reduction relation is deterministic *)
Lemma reduction_in_one_deterministic :
  forall a a1, reduction_in_one a a1 -> forall a2, reduction_in_one a a2 -> a1 = a2.
Proof.
  intros a a1 H.
  induction H; intros a2 h0.
  all: inversion h0; subst.
  (* already equal *)
  all: auto.

  (* follows by induction *)
  all: try solve [erewrite IHreduction_in_one; eauto].

  (* impossible case, reduction of value *)
  all: try solve [(have: False by eapply no_Value_reduction; eauto); done].

  all: try ((have: False by eapply (@no_Value_reduction (a_UCAbs b)); eauto); done).

  - pick fresh x.
    move: (H2 x ltac:(auto)) => h7.
    move: (H0 x ltac:(auto)) => h1.
    apply h1 in h7.
    apply open_tm_wrt_tm_inj in h7; eauto. rewrite h7. auto.
  - inversion H0.
  - inversion H5.
  - have: (Ax a A = Ax a2 A0). eapply binds_unique; eauto using uniq_toplevel.
    move => h; inversion h; done.
Qed.


End ext_red_one.
