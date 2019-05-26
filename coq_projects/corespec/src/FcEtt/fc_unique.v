Require Import FcEtt.sigs.

Require Export FcEtt.ett_inf_cs.
Require Export FcEtt.ett_ind.
Require Import FcEtt.imports.
Require Import FcEtt.tactics.

Require Import FcEtt.ett_par.


Module fc_unique (wf : fc_wf_sig) (subst : fc_subst_sig) <: fc_unique_sig.
Import wf subst.

Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

(* The typing relation for FC produces unique types. *)

Hint Resolve AnnCtx_uniq.
Hint Rewrite tm_subst_tm_tm_var co_subst_co_co_var.

(* Automatically apply the IH of typing_unique on the specified tm/coercion *)
Ltac apply_ind a :=
  match goal with
  | H : (forall A2 : tm, AnnTyping ?G a A2 -> ?B = A2), Y : AnnTyping ?G a ?C |- _  =>
    apply H in Y; inversion Y
  | H : forall A B, AnnDefEq ?G ?D a A B -> ?A1 = A /\ ?B1 = B, Y : AnnDefEq ?G ?D a ?A2 ?B2 |- _ =>
    apply H in Y; split_hyp; subst
  | H : ∀ q1 q2 : constraint, AnnIso ?G ?D a q1 q2 → ?phi1 = q1 ∧ ?phi2 = q2,
    Y : AnnIso ?G ?D a ?q1 ?q2 |- _ =>
apply H in Y; split_hyp; subst

end.

(* Apply induction in the case where we need a "fresh" variable. *)
Ltac apply_ind_var c a :=
      match goal with
        | H7 : ∀ c : atom,
            ¬ c `in` ?L0
                   → AnnTyping ?G (open_tm_wrt_co a (g_Var_f c)) ?B,
          H0 : ∀ c : atom,
            ¬ c `in` ?L
             → ∀ A2 : tm,
          AnnTyping ?G (open_tm_wrt_co a (g_Var_f c)) A2 → ?C = A2 |- _ =>
  specialize H7 with c; apply H0 in H7; eauto
       | H8 : ∀ x : atom,
       ¬ x `in` ?L0
       → AnnDefEq ?G ?D (open_co_wrt_tm a (a_Var_f x)) ?B0 ?B5,
        H0 : ∀ x : atom,
       ¬ x `in` ?L
       → ∀ a1 b1 : tm,
         AnnDefEq ?G ?D (open_co_wrt_tm a (a_Var_f x)) a1 b1
         → ?B1 = a1 ∧ ?B2  = b1 |- _ =>
  specialize H8 with c; edestruct (H0 c); eauto
  end.

(* For working with PiCong and AbsCong. Look for hypothses that introduce new
   equations about the bodies of the terms. (Should be used after induction
   hypothesis.  *)
Ltac equate_bodies x :=
      match goal with
        H11 : ∀ x : atom,
          ¬ x `in` ?L0 → open_tm_wrt_tm ?B4 (a_Var_f x) = open_tm_wrt_tm ?B2 ?C,
    e : ∀ x : atom, ¬ x `in` ?L → open_tm_wrt_tm ?B3 (a_Var_f x) =
                                  open_tm_wrt_tm ?B2 ?C
    |- _ =>
        let FR := fresh in
        let FR2 := fresh in
        specialize H11 with x;
        assert (FR: ¬ x `in` L0); eauto; apply H11 in FR;
        specialize e with x;
        assert (FR2 : ¬ x `in` L); eauto; apply e in FR2;
        rewrite -FR in FR2;
        apply open_tm_wrt_tm_inj in FR2; try fsetdec_fast
        end.

(* Find matching assumptions about binds, produce an equality EQ between their sorts. *)
Ltac resolve_binds_unique :=
  let EQ := fresh in
  let h  := fresh in
  match goal with
  |   b : binds ?c ?A ?G,  H4 : binds ?c ?B ?G  |- _  =>
      assert (EQ : uniq G); eauto using AnnCtx_uniq,uniq_an_toplevel;
      move: (binds_unique _ _ _ _ _ b H4 EQ) => h; inversion h
  end.


Lemma unique_mutual :
  (forall G a A1, AnnTyping G a A1 -> forall {A2}, AnnTyping G a A2 -> A1 = A2) /\
  (forall G phi, AnnPropWff G phi -> True) /\
  (forall G D g p1 p2, AnnIso G D g p1 p2 -> forall {q1 q2}, AnnIso G D g q1 q2 -> p1 = q1 /\ p2 = q2) /\
  (forall G D g a b, AnnDefEq G D g a b -> forall {a1 b1}, AnnDefEq G D g a1 b1 -> a = a1 /\ b = b1) /\
  (forall G, AnnCtx G -> True).
Proof.
  apply ann_typing_wff_iso_defeq_mutual.
  all: intros. all: try inversion H1; subst; try solve [try inversion H0; subst; basic_solve'; subst].
  - autotype.
  - autotype. f_equal.
    pick fresh x.
    eapply open_tm_wrt_tm_inj with (x1 := x); auto.
  - apply_ind b. done.
  - autotype.
    apply_ind a. firstorder.
  - f_equal.
    pick fresh c.
    apply_ind_var c a.
    eapply open_tm_wrt_co_inj; autotype.
  - apply_ind a1. done.
  - move: (binds_unique _ _ _ _ _ b H4 uniq_an_toplevel) => E. inversion E. auto.
  - have E: (Ax a A = Ax a2 A2). eapply binds_unique; eauto using uniq_an_toplevel.
    inversion E. auto.
  - autotype; apply_ind g1; apply_ind g2; autotype.
  - autotype; apply_ind g; autotype.
  - ann_invert_clear. apply_ind g. auto.
  - repeat ann_invert_clear. apply_ind g. auto.
  - ann_invert_clear.
    resolve_binds_unique. auto.
  - ann_invert_clear. auto.
  - ann_invert_clear.
    edestruct H2; eauto.
  - ann_invert_clear.
    apply_ind g1. apply_ind g2. apply_ind g2. auto.
  - inversion H4. clear a0.
    apply_ind g1.
    pick fresh x.
    apply_ind_var x g2.
    apply open_tm_wrt_tm_inj in H5.
    apply open_tm_wrt_tm_inj in H6.
    subst.
    equate_bodies x.
    all: fsetdec_fast.

  - (* abs_cong *) (* FIXME: could be prettier *)
    inversion H4.
    apply_ind g1.
    pick fresh x.
    have xL : x `notin` L by fsetdec.
    have xL0 : x `notin` L0 by clear xL; fsetdec.
    move: (H0 x xL _ _ (H9 x xL0)) => [eq1 eq2].
    apply open_tm_wrt_tm_inj in eq1.
    apply open_tm_wrt_tm_inj in eq2.
    split; first by congruence.
    suff: b3 = b5 by move=> ->.
    apply: open_tm_wrt_tm_inj.
    Focus 3.
    erewrite (H10 x xL0).
    erewrite (e x xL).
    congruence.
    all: try fsetdec_fast.
  - repeat ann_invert_clear.
    apply_ind g1.
    apply_ind g2.
    auto.
  - repeat ann_invert_clear.
    apply_ind g.
    split; congruence.
  - repeat ann_invert_clear.
    (* apply_ind seems to have a problem on this one *)
    move: (H0 _ _ H7) => [-> ->].
    move: (H _ _ H6) => [? ?].
    split; congruence.
  - (* ipi_cong *)
    match goal with
      [ H3 : AnnDefEq ?G ?D (g_CPiCong ?g1 ?g3) ?a3 ?b1 |- _ ] => inversion H3
    end.
    match goal with
      [ H : ∀ q1 q2 : constraint, AnnIso ?G ?D ?g1 q1 q2 → ?phi1 = q1 ∧ ?phi2 = q2,
        H7 : AnnIso ?G ?D ?g1 phi0 phi3 |- _ ] =>
      move: (H _ _ H7) => [h0 h1]; subst
    end.
    pick fresh x.
    match goal with
      [ H8 : ∀ c : atom, ¬ c `in` ?L0 → open_tm_wrt_co B4 (g_Var_f c) =
                                        open_tm_wrt_co B5 (g_Cast (g_Var_f c) (g_Sym ?g1)) |- _ ] =>
      move: (H8 x ltac:(auto)) => h0; clear H8
    end.
    match goal with
      [ H0 : ∀ c : atom, ¬ c `in` ?L → ∀ a1 b1 : tm,
              AnnDefEq ([(c, Co ?phi0)] ++ ?G) ?D (open_co_wrt_co ?g3 (g_Var_f c)) a1 b1
              → open_tm_wrt_co B1 (g_Var_f c) = ?a1 ∧ open_tm_wrt_co B2 (g_Var_f c) = ?b1,
       H7 : ∀ c : atom,
       ¬ c `in` ?L0
       → AnnDefEq ([(c, Co ?phi0)] ++ ?G) ?D (open_co_wrt_co ?g3 (g_Var_f c)) (open_tm_wrt_co B0 (g_Var_f c))
           (open_tm_wrt_co B5 (g_Var_f c)) |- _ ] =>
      move: (H0 x ltac:(auto) _ _ (H7 x ltac:(auto))) => [h1 h2]; clear H7
    end.
    move: (e x ltac:(auto)) => h3. clear e.
    split; f_equal.
    apply open_tm_wrt_co_inj with (c1 := x); auto.
    apply open_tm_wrt_co_inj with (c1 := x); auto.
    rewrite h0.
    rewrite h3.
    f_equal.
    apply open_tm_wrt_co_inj with (c1 := x); auto.
  - (* cabs_cong *)
    inversion H5. subst.
    pick fresh x.
    assert (FrL0: x `notin` L0). auto.
    assert (FrL: x `notin` L). auto.
    move: (H11 x FrL0) => h0. clear H11.
    edestruct H. eauto. subst.
    move: (H0 x FrL _ _ (H10 x FrL0)) => [h1 h2].
    split; f_equal; auto.
    eapply open_tm_wrt_co_inj with (c1 := x); auto.
    eapply open_tm_wrt_co_inj with (c1 := x); auto.
    rewrite h0.
    move: (e x FrL) => h3.
    rewrite h3.
    f_equal.
    apply open_tm_wrt_co_inj with (c1 := x); auto.
  - inversion H5. subst.
    edestruct H...
    autotype.
    autotype.
  - inversion H2. subst.
    apply H in H8. destruct H8 as [h0 h1].
    inversion h0. inversion h1...
    autotype.
  - apply H0 in H9.
    split_hyp. invert_syntactic_equality.
    auto.
  - inversion H0. subst. apply H in H4.
    split_hyp. invert_syntactic_equality. auto.
  - ann_invert_clear.
    + apply_ind b1. subst.
      pick fresh x.
      move: (H5 x ltac:(auto)) => h0.
      rewrite -e in h0; auto.
      apply open_tm_wrt_tm_inj in h0; auto.
      subst. auto.
    + apply_ind b1.
  - ann_invert_clear.
    + apply_ind b1.
    + apply_ind b1. subst.
      pick fresh x.
      move: (H5 x ltac:(auto)) => h0.
      rewrite -e in h0; auto.
      apply open_tm_wrt_co_inj in h0; auto.
      subst. auto.
    (* Left/Right
  - ann_invert_clear.
    apply_ind g1. invert_syntactic_equality. auto.
    apply_ind g1. done.
  - ann_invert_clear.
    apply_ind g1. invert_syntactic_equality. auto.
  - repeat ann_invert_clear;
    apply_ind g1;
    apply_ind g2.
    done.
    invert_syntactic_equality. auto.
    *)
Qed.


Definition AnnTyping_unique := first unique_mutual.
Definition AnnDefEq_unique  := fourth unique_mutual.
Definition AnnIso_unique    := third unique_mutual.


(* These two tactics look for terms in the context that
   are typed with two different types and automatically applies
   the uniqueness lemma.

   The first tactic uses subst to resolve the equalities. The second
   tries to only eliminate equations between variables.

 *)


Ltac resolve_unique_subst  :=
  match goal with
  |   _ : AnnTyping ?G ?a ?A,  H :AnnTyping ?G ?a ?B  |- _  =>
      assert (A = B); try (eapply (first unique_mutual); eauto 1); subst; clear H
  |   H1 : AnnDefEq ?G ?D ?g ?A1 ?B1,  H2 :AnnDefEq ?G ?D ?g ?A2 ?B2  |- _  =>
      destruct (fourth unique_mutual _ _ _ _ _ H1 _ _ H2); subst; clear H2
  end.

Ltac resolve_unique_nosubst  :=
  match goal with
  |   H1 : AnnTyping ?G ?a ?A,  H2 :AnnTyping ?G ?a ?B  |- _  =>
      assert (A = B); [ eapply (first unique_mutual);
                          [eapply H1 | eapply H2]|]; subst B; clear H2
  |   H1 : AnnDefEq ?G ?D ?g ?A1 ?B1,  H2 :AnnDefEq ?G ?D ?g ?A2 ?B2  |- _  =>
      destruct (fourth unique_mutual _ _ _ _ _ H1 _ _ H2);
      try subst A2; try subst B2; try subst A1; try subst B1;
      clear H2
  end.

(* Coerced values and values are terminal. *)
Lemma no_reduction_mutual :
  (forall a, CoercedValue a -> forall G b, not (head_reduction G a b)) /\
  (forall a, Value a -> forall G b, not (head_reduction G a b)).
Proof.
  apply CoercedValue_Value_mutual; simpl.
  all: intros.
  all: intros NH; inversion NH; subst.
  all: try solve [eapply H; eauto].
  all: try solve [inversion v].
  all: try solve [inversion p].

  - pick fresh x.
    move: (H x ltac:(auto)) => h0.
    move: (H5 x ltac:(auto)) => h5.
    eapply h0; eauto.
Qed.
Lemma no_Value_reduction : forall a, Value a -> forall G b, not (head_reduction G a b).
Proof. eapply no_reduction_mutual. Qed.
Lemma no_CoercedValue_reduction : forall a, CoercedValue a -> forall G b, not (head_reduction G a b).
Proof. eapply no_reduction_mutual. Qed.

(* The reduction relation is deterministic *)
Lemma head_reduction_deterministic :
  forall G a a1, head_reduction G a a1 -> forall a2, head_reduction G a a2 -> a1 = a2.
Proof.
  intros G a a1 H.
  induction H; intros a2 h0.
  all: inversion h0; subst.
  (* already equal *)
  all: auto.
  (* follows by induction *)
  all: try solve [erewrite IHhead_reduction; eauto].

  (* impossible case, reduction of value *)
  all: try solve [(have: False by eapply no_Value_reduction; eauto); done].

  (* impossible case, reduction of coerced value *)
  all: try match goal with
    [ H4 : Value ?a0, H0: head_reduction _ (a_Conv ?a0 ?g) ?a' |- _ ] =>
    (have CV: CoercedValue (a_Conv a0 g) by eauto using AnnDefEq_lc3);
      (have: False by eapply no_CoercedValue_reduction; eauto); done
  end.

  all: try ((have: False by eapply (@no_Value_reduction (a_CAbs phi b)); eauto); done).

  - pick fresh x.
    move: (H7 x ltac:(auto)) => h7.
    move: (H1 x ltac:(auto)) => h1.
    apply h1 in h7.
    apply open_tm_wrt_tm_inj in h7; eauto. rewrite h7. auto.
  - resolve_binds_unique. auto.
Qed.

End fc_unique.
