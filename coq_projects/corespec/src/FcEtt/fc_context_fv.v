Require Export FcEtt.tactics.
Require Export FcEtt.ett_inf.

Require Import FcEtt.utils.
Require Import FcEtt.imports.

Require Import FcEtt.ett_ind.

Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.


(* --------------------------------------------------------------------------- *)

Hint Resolve AnnCtx_uniq.
Hint Unfold AtomSetImpl.Subset.

Ltac solve_binds :=
  match goal with
    | [ b : binds ?v _ ?G
      , H : forall v' _, binds v' _ ?G -> _ [<=] dom ?G ∧ _ [<=] dom ?G
      |- _ ] =>
      apply H in b; simpl in b; split_hyp; (done || fsetdec)
  end.

Theorem ann_context_fv_mutual :
  (forall G (a : tm) A (H: AnnTyping G a A),
      fv_tm_tm_tm a [<=] dom G /\ fv_co_co_tm a [<=] dom G /\
      fv_tm_tm_tm A [<=] dom G /\ fv_co_co_tm A [<=] dom G)
  /\
  (forall G phi (H : AnnPropWff G phi),
      fv_tm_tm_constraint phi [<=] dom G /\ fv_co_co_constraint phi [<=] dom G)
  /\
  (forall G D g p1 p2 (H : AnnIso G D g p1 p2),
      fv_tm_tm_co         g  [<=] dom G /\ fv_co_co_co         g  [<=] dom G /\
      fv_tm_tm_constraint p1 [<=] dom G /\ fv_co_co_constraint p1 [<=] dom G /\
      fv_tm_tm_constraint p2 [<=] dom G /\ fv_co_co_constraint p2 [<=] dom G)
  /\
  (forall G D g A B (H : AnnDefEq G D g A B),
      fv_tm_tm_co g [<=] dom G /\ fv_co_co_co g [<=] dom G /\
      fv_tm_tm_tm A [<=] dom G /\ fv_co_co_tm A [<=] dom G /\
      fv_tm_tm_tm B [<=] dom G /\ fv_co_co_tm B [<=] dom G)
  /\
  (forall G (H : AnnCtx G),
      (forall x A,
          binds x (Tm A)   G ->
          fv_tm_tm_tm         A   [<=] dom G /\ fv_co_co_tm         A   [<=] dom G) /\
      (forall c phi,
          binds c (Co phi) G ->
          fv_tm_tm_constraint phi [<=] dom G /\ fv_co_co_constraint phi [<=] dom G)).

Proof.
  eapply ann_typing_wff_iso_defeq_mutual.
  all: autounfold.
  (* We can't just use `repeat split` because we don't want to split under foralls *)
  all: intros; repeat match goal with |- _ ∧ _ => split end; split_hyp; simpl.
  all: eauto 1.
  (* split all asummptions about unions *)

  (* Do the cases about the context at the end. *)
  all: try (intros x0 A0 BI).
  all: try solve [inversion BI].
  all: try (match goal with |- _ ∧ _ => split end).
  all: try solve
  [intros y h1; inversion BI; [inversion H5; subst; clear H5; eauto|
                               destruct (H x0 _ H5); eauto]].
  all: try solve
  [intros y h1; inversion BI; [inversion H5; subst; clear H5; eauto|
                              destruct (H4 x0 _ H5); eauto]].
  all: try solve
  [intros y h1; inversion BI; [inversion H3; subst; clear H3; eauto|
                              destruct (H x0 _ H3); eauto]].
  all: try solve
  [intros y h1; inversion BI; [inversion H3; subst; clear H3; eauto|
                               destruct (H2 x0 _ H3); eauto]].

  (* rest of the cases *)
  all: intros y IN.

  (* more splitting, assumption has a union type *)
  all: try match goal with
    [ H7 : ?y `in` union ?A ?B |- _ ] =>
    apply F.union_iff in H7; destruct H7; eauto end.

  all: try solve [ apply notin_empty_1 in IN; contradiction].
  all: try solve [ assert (x = y) by fsetdec; subst; eapply binds_In; eauto ].
  all: try solve [ destruct (H _ _ b); eauto ].

  all: try solve [apply H1; eauto; simpl; auto].
  all: try solve [apply H2; eauto; simpl; auto].
  all: try solve [apply H3; eauto; simpl; auto].
  all: try solve [apply H4; eauto; simpl; auto].


  all: try match goal with
    [ H5 : forall x : atom, (x `in` ?L -> False) -> ( _ /\ _ ) |- _ ] =>
    pick fresh x; destruct (H5 x); eauto; split_hyp
           end.

  all: try match goal with
    [ H4 : ?y `in` fv_tm_tm_tm ?B,
      H5 : ∀ a : atom,
       a `in` fv_tm_tm_tm (open_tm_wrt_tm ?B (a_Var_f ?x))
            → a `in` dom ([(?x, ?s)] ++ ?G) |- _ ] =>
    assert (h0: y `in` dom ([(x,s)] ++ G)) by
    (eapply H5; auto;
    eapply fv_tm_tm_tm_open_tm_wrt_tm_lower; auto);
      simpl in h0; apply F.add_neq_iff in h0; auto
           end.
  all: try match goal with
    [ H4 : ?y `in` fv_co_co_tm ?B,
      H5 : ∀ a : atom,
       a `in` fv_co_co_tm (open_tm_wrt_tm ?B (a_Var_f ?x))
            → a `in` dom ([(?x, ?s)] ++ ?G) |- _ ] =>
    assert (h0: y `in` dom ([(x,s)] ++ G)) by
    (eapply H5; eauto;
    eapply fv_co_co_tm_open_tm_wrt_tm_lower; auto);
      simpl in h0; apply F.add_neq_iff in h0; auto
           end.
  all: try match goal with
    [ H4 : ?y `in` fv_tm_tm_tm ?B,
      H5 : ∀ a : atom,
       a `in` fv_tm_tm_tm (open_tm_wrt_co ?B (g_Var_f ?x))
            → a `in` dom ([(?x, ?s)] ++ ?G) |- _ ] =>
    assert (h0: y `in` dom ([(x,s)] ++ G)) by
    (eapply H5; eauto;
    eapply fv_tm_tm_tm_open_tm_wrt_co_lower; auto);
    simpl in h0; apply F.add_neq_iff in h0; auto
           end.
  all: try match goal with
    [ H4 : ?y `in` fv_co_co_tm ?B,
      H5 : ∀ a : atom,
       a `in` fv_co_co_tm (open_tm_wrt_co ?B (g_Var_f ?x))
            → a `in` dom ([(?x, ?s)] ++ ?G) |- _ ] =>
    assert (h0: y `in` dom ([(x,s)] ++ G)) by
    (eapply H5; eauto;
    eapply fv_co_co_tm_open_tm_wrt_co_lower; auto);
      simpl in h0; apply F.add_neq_iff in h0; auto
           end.

  all: try (simpl in *; eapply fv_tm_tm_tm_open_tm_wrt_tm_upper in IN;
    apply F.union_iff in IN; destruct IN; eauto).
  all: try (simpl in *; eapply fv_co_co_tm_open_tm_wrt_tm_upper in IN;
    apply F.union_iff in IN; destruct IN; eauto).
  all: try (simpl in *; eapply fv_tm_tm_tm_open_tm_wrt_co_upper in IN;
    apply F.union_iff in IN; destruct IN; eauto).
  all: try (simpl in *; eapply fv_co_co_tm_open_tm_wrt_co_upper in IN;
    apply F.union_iff in IN; destruct IN; eauto).

  all: try (apply H0 in IN; apply notin_empty_1 in IN; contradiction).
  all: try (apply H1 in IN; apply notin_empty_1 in IN; contradiction).

  all: try match goal with
    [ H7 : ?y `in` union ?A ?B |- _ ] =>
    apply F.union_iff in H7; destruct H7; eauto end.

  all: try solve [apply H1; eauto; simpl; auto].
  all: try solve [apply H2; eauto; simpl; auto].
  all: try solve [apply H3; eauto; simpl; auto].
  all: try solve [apply H4; eauto; simpl; auto].
  all: try solve [apply H5; eauto; simpl; auto].

  all: try match goal with
    [IN : ?y `in` singleton ?c |- _ ] =>
                assert (c = y) by fsetdec; subst; eapply binds_In; eauto
     end.
  all: try solve [ destruct (H0 _ _ b0); simpl in *; eauto].

  all: try  match goal with
    [ H4 : ?y `in` fv_tm_tm_co ?B,
      H5 : ∀ a : atom,
       a `in` fv_tm_tm_co (open_co_wrt_tm ?B (a_Var_f ?x))
            → a `in` dom ([(?x, ?s)] ++ ?G) |- _ ] =>
    assert (h0: y `in` dom ([(x,s)] ++ G)) by
    (eapply H5; eauto;
    eapply fv_tm_tm_co_open_co_wrt_tm_lower; auto);
      simpl in h0; apply F.add_neq_iff in h0; auto
           end.

  all: try match goal with
    [ H4 : ?y `in` fv_co_co_co ?B,
      H5 : ∀ a : atom,
       a `in` fv_co_co_co (open_co_wrt_tm ?B (a_Var_f ?x))
            → a `in` dom ([(?x, ?s)] ++ ?G) |- _ ] =>
    assert (h0: y `in` dom ([(x,s)] ++ G)) by
    (eapply H5; eauto;
    eapply fv_co_co_co_open_co_wrt_tm_lower; auto);
      simpl in h0; apply F.add_neq_iff in h0; auto
           end.

  all: try match goal with
    [ H4 : ?y `in` fv_tm_tm_co ?B,
      H5 : ∀ a : atom,
       a `in` fv_tm_tm_co (open_co_wrt_co ?B (g_Var_f ?x))
            → a `in` dom ([(?x, ?s)] ++ ?G) |- _ ] =>
    assert (h0: y `in` dom ([(x,s)] ++ G)) by
    (eapply H5; eauto;
    eapply fv_tm_tm_co_open_co_wrt_co_lower; auto);
      simpl in h0; apply F.add_neq_iff in h0; auto
           end.

  all: try match goal with
    [ H4 : ?y `in` fv_co_co_co ?B,
      H5 : ∀ a : atom,
       a `in` fv_co_co_co (open_co_wrt_co ?B (g_Var_f ?x))
            → a `in` dom ([(?x, ?s)] ++ ?G) |- _ ] =>
    assert (h0: y `in` dom ([(x,s)] ++ G)) by
    (eapply H5; eauto;
    eapply fv_co_co_co_open_co_wrt_co_lower; auto);
      simpl in h0; apply F.add_neq_iff in h0; auto
           end.


  (* Eta cases *)

  all: try match goal with 
      [ IN : ?y `in` ?fv_tm_tm_tm ?a, 
        H : ∀ a : atom, a `in` ?fv_tm_tm_tm ?b → a `in` dom ?G,
        e : ∀ x : atom,
            (x `in` ?L → False) → 
            ?open_tm_wrt_tm ?a (a_Var_f x) = ?c
       |- _ ] => 
      eapply H; pick fresh x; move: (e x ltac:(auto)) => h0;
      assert (x <> y); [ fsetdec|];
      clear Fr;
      have h1: y `in` fv_tm_tm_tm (open_tm_wrt_tm a (a_Var_f x));
      [ move: (fv_tm_tm_tm_open_tm_wrt_tm_lower a (a_Var_f x)) => ?;
        move: (fv_co_co_tm_open_tm_wrt_tm_lower a (a_Var_f x)) => ?;
        fsetdec|
      rewrite h0 in h1; 
      simpl in h1;
      fsetdec ]
    end.

  all: try match goal with 
      [ IN : ?y `in` ?fv_tm_tm_tm ?a, 
        H : ∀ a : atom, a `in` ?fv_tm_tm_tm ?b → a `in` dom ?G,
        e : ∀ x : atom,
            (x `in` ?L → False) → 
            ?open_tm_wrt_tm ?a (g_Var_f x) = ?c
       |- _ ] => 
      eapply H; pick fresh x; move: (e x ltac:(auto)) => h0;
      assert (x <> y); [ fsetdec|];
      clear Fr;
      have h1: y `in` fv_tm_tm_tm (open_tm_wrt_tm a (g_Var_f x));
      [ move: (fv_tm_tm_tm_open_tm_wrt_co_lower a (g_Var_f x)) => ?;
        move: (fv_co_co_tm_open_tm_wrt_co_lower a (g_Var_f x)) => ?;
        fsetdec|];
      rewrite h0 in h1; 
      simpl in h1;
      fsetdec
    end.


  (* last hard cases *)
  - assert (FR1 : x `notin` L) by auto. assert (FR2 : x <> y) by auto.
    clear Fr. clear H0. clear r. clear r0.
    clear H19. clear H20. clear H22. clear H24.
    clear H10 H12 H13 H7 H4 H9 H6.
    move: (e x FR1) => EX.
    match goal with
      [H18 :  y `in` fv_tm_tm_tm b3 |- _ ] =>
       erewrite fv_tm_tm_tm_open_tm_wrt_tm_lower  in H18;
       erewrite EX in H18;
       erewrite fv_tm_tm_tm_open_tm_wrt_tm_upper  in H18;
       apply F.union_iff in H18; destruct H18 as [h2 | h3]
       end.
    simpl in h2.
    apply F.union_iff in h2; destruct h2 as [h4 | h5].
    fsetdec.
    eauto.

    assert (y `in` dom ((x ~ Tm A1) ++ G)). eapply H23.
    eapply fv_tm_tm_tm_open_tm_wrt_tm_lower.  auto.
    simpl in H0; apply F.add_neq_iff in H0; auto.
  - assert (FR1 : x `notin` L) by auto. assert (FR2 : x <> y) by auto.
    clear Fr. clear H0. clear r. clear r0.
    move: (e x FR1) => EX.
    match goal with
      [H14 : y `in` fv_co_co_tm b3 |- _ ] =>
      erewrite fv_co_co_tm_open_tm_wrt_tm_lower  in H14;
        erewrite EX in H14;
        erewrite fv_co_co_tm_open_tm_wrt_tm_upper  in H14;
        apply F.union_iff in H14; destruct H14 as [h2 | h3]
    end.
    simpl in h2.
    apply F.union_iff in h2; destruct h2 as [h4 | h5].
    fsetdec.
    eauto.

    assert (y `in` dom ((x ~ Tm A1) ++ G)). eapply H24.
    eapply fv_co_co_tm_open_tm_wrt_tm_lower.  auto.
    simpl in H0; apply F.add_neq_iff in H0; auto.
Qed.

Definition AnnTyping_context_fv  := @first  _ _ _ _ _ ann_context_fv_mutual.
Definition AnnPropWff_context_fv := @second _ _ _ _ _ ann_context_fv_mutual.
Definition AnnIso_context_fv     := @third  _ _ _ _ _ ann_context_fv_mutual.
Definition AnnDefEq_context_fv   := @fourth _ _ _ _ _ ann_context_fv_mutual.
Definition AnnCtx_context_fv     := @fifth  _ _ _ _ _ ann_context_fv_mutual.
