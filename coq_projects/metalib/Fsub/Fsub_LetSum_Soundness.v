(** Type-safety proofs for Fsub.

    Authors: Brian Aydemir and Arthur Chargu\'eraud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    In parentheses are given the label of the corresponding lemma in
    the appendix (informal proofs) of the POPLmark Challenge.

    Table of contents:
      - #<a href="##subtyping">Properties of subtyping</a>#
      - #<a href="##typing">Properties of typing</a>#
      - #<a href="##preservation">Preservation</a>#
      - #<a href="##progress">Progress</a># *)

Require Export Fsub.Fsub_LetSum_Lemmas.


(* ********************************************************************** *)
(** * #<a name="subtyping"></a># Properties of subtyping *)


(* ********************************************************************** *)
(** ** Reflexivity (1) *)

Lemma sub_reflexivity : forall E T,
  wf_env E ->
  wf_typ E T ->
  sub E T T.
Proof with eauto.
  intros E T Ok Wf.
  induction Wf...
  pick fresh Y and apply sub_all...
Qed.


(* ********************************************************************** *)
(** ** Weakening (2) *)

Lemma sub_weakening : forall E F G S T,
  sub (G ++ E) S T ->
  wf_env (G ++ F ++ E) ->
  sub (G ++ F ++ E) S T.
Proof with simpl_env; auto using wf_typ_weakening.
  intros E F G S T Sub Ok.
  remember (G ++ E) as H.
  generalize dependent G.
  induction Sub; intros G Ok EQ; subst...
  Case "sub_trans_tvar".
    apply (sub_trans_tvar U)...
  Case "sub_all".
    pick fresh Y and apply sub_all...
    rewrite <- app_assoc.
    apply H0...
Qed.


(* ********************************************************************** *)
(** ** Narrowing and transitivity (3) *)

Definition transitivity_on Q := forall E S T,
  sub E S Q -> sub E Q T -> sub E S T.

Lemma sub_narrowing_aux : forall Q F E Z P S T,
  transitivity_on Q ->
  sub (F ++ Z ~ bind_sub Q ++ E) S T ->
  sub E P Q ->
  sub (F ++ Z ~ bind_sub P ++ E) S T.
Proof with simpl_env; eauto using wf_typ_narrowing, wf_env_narrowing.
  intros Q F E Z P S T TransQ SsubT PsubQ.
  remember (F ++ Z ~ bind_sub Q ++ E) as G. generalize dependent F.
  induction SsubT; intros F EQ; subst...
  Case "sub_trans_tvar".
    destruct (X == Z); subst.
    SCase "X = Z".
      apply (sub_trans_tvar P); [ eauto using fresh_mid_head | ].
      apply TransQ.
      SSCase "P <: Q".
        rewrite_env (empty ++ (F ++ Z ~ bind_sub P) ++ E).
        apply sub_weakening...
      SSCase "Q <: T".
        analyze_binds_uniq H.
        injection BindsTacVal; intros; subst...
    SCase "X <> Z".
      apply (sub_trans_tvar U)...
  Case "sub_all".
    pick fresh Y and apply sub_all...
    rewrite <- app_assoc.
    apply H0...
Qed.

Lemma sub_transitivity : forall Q,
  transitivity_on Q.
Proof with simpl_env; auto.
  unfold transitivity_on.
  intros Q E S T SsubQ QsubT.
  assert (W : type Q) by auto.
  generalize dependent T.
  generalize dependent S.
  generalize dependent E.
  remember Q as Q' in |- *.
  generalize dependent Q'.
  induction W;
    intros Q' EQ E S SsubQ;
    induction SsubQ; try discriminate; inversion EQ; subst;
    intros T' QsubT;
    inversion QsubT; subst; eauto 4 using sub_trans_tvar.
  Case "sub_all / sub_top".
    assert (sub E (typ_all S1 S2) (typ_all T1 T2)).
      SCase "proof of assertion".
      pick fresh y and apply sub_all...
    auto.
  Case "sub_all / sub_all".
    pick fresh Y and apply sub_all.
    SCase "bounds".
      eauto.
    SCase "bodies".
      lapply (H0 Y); [ intros K | auto ].
      apply (K (open_tt T2 Y))...
      rewrite_env (empty ++ Y ~ bind_sub T0 ++ E).
      apply (sub_narrowing_aux T1)...
      unfold transitivity_on.
      auto using (IHW T1).
Qed.

Lemma sub_narrowing : forall Q E F Z P S T,
  sub E P Q ->
  sub (F ++ Z ~ bind_sub Q ++ E) S T ->
  sub (F ++ Z ~ bind_sub P ++ E) S T.
Proof.
  intros.
  eapply sub_narrowing_aux; eauto.
  apply sub_transitivity.
Qed.


(* ********************************************************************** *)
(** ** Type substitution preserves subtyping (10) *)

Lemma sub_through_subst_tt : forall Q E F Z S T P,
  sub (F ++ Z ~ bind_sub Q ++ E) S T ->
  sub E P Q ->
  sub (map (subst_tb Z P) F ++ E) (subst_tt Z P S) (subst_tt Z P T).
Proof with
      simpl_env;
      eauto 4 using wf_typ_subst_tb, wf_env_subst_tb, wf_typ_weaken_head.
  intros Q E F Z S T P SsubT PsubQ.
  remember (F ++ Z ~ bind_sub Q ++ E) as G.
  generalize dependent F.
  induction SsubT; intros G EQ; subst; simpl subst_tt...
  Case "sub_top".
    apply sub_top...
  Case "sub_refl_tvar".
    destruct (X == Z); subst.
    SCase "X = Z".
      apply sub_reflexivity...
    SCase "X <> Z".
      apply sub_reflexivity...
      inversion H0; subst.
      analyze_binds H3...
      apply (wf_typ_var (subst_tt Z P U))...
  Case "sub_trans_tvar".
    destruct (X == Z); subst.
    SCase "X = Z".
      apply (sub_transitivity Q).
      SSCase "left branch".
        rewrite_env (empty ++ map (subst_tb Z P) G ++ E).
        apply sub_weakening...
      SSCase "right branch".
        rewrite (subst_tt_fresh Z P Q).
          analyze_binds_uniq H.
            inversion BindsTacVal; subst...
          apply (notin_fv_wf E); eauto using fresh_mid_tail.
    SCase "X <> Z".
      apply (sub_trans_tvar (subst_tt Z P U))...
      rewrite (map_subst_tb_id E Z P);
        [ | auto | eapply fresh_mid_tail; eauto ].
      analyze_binds H...
  Case "sub_all".
    pick fresh X and apply sub_all...
    rewrite subst_tt_open_tt_var...
    rewrite subst_tt_open_tt_var...
    rewrite_env (map (subst_tb Z P) (X ~ bind_sub T1 ++ G) ++ E).
    apply H0...
Qed.


(* ********************************************************************** *)
(** * #<a name="typing"></a># Properties of typing *)


(* ********************************************************************** *)
(** ** Weakening (5) *)

Lemma typing_weakening : forall E F G e T,
  typing (G ++ E) e T ->
  wf_env (G ++ F ++ E) ->
  typing (G ++ F ++ E) e T.
Proof with simpl_env;
           eauto using wf_typ_weakening,
                       wf_typ_from_wf_env_typ,
                       wf_typ_from_wf_env_sub,
                       sub_weakening.
  intros E F G e T Typ.
  remember (G ++ E) as H.
  generalize dependent G.
  induction Typ; intros G EQ Ok; subst...
  Case "typing_abs".
    pick fresh x and apply typing_abs.
    lapply (H x); [intros K | auto].
    rewrite <- app_assoc.
    apply (H0 x)...
  Case "typing_tabs".
    pick fresh X and apply typing_tabs.
    lapply (H X); [intros K | auto].
    rewrite <- app_assoc.
    apply (H0 X)...
  Case "typing_let".
    pick fresh x and apply typing_let...
    lapply (H0 x); [intros K | auto].
    rewrite <- app_assoc.
    apply H0...
  Case "typing_case".
    pick fresh x and apply typing_case...
    SCase "inl branch".
      lapply (H0 x); [intros K | auto].
      rewrite <- app_assoc.
      apply H0...
      assert (J : wf_typ (G ++ F ++ E) (typ_sum T1 T2))...
      inversion J...
    SCase "inr branch".
      lapply (H2 x); [intros K | auto].
      rewrite <- app_assoc.
      apply H2...
      assert (J : wf_typ (G ++ F ++ E) (typ_sum T1 T2))...
      inversion J...
Qed.


(* ********************************************************************** *)
(** ** Strengthening (6) *)

Lemma sub_strengthening : forall x U E F S T,
  sub (F ++ x ~ bind_typ U ++ E) S T ->
  sub (F ++ E) S T.
Proof with eauto using wf_typ_strengthening, wf_env_strengthening.
  intros x U E F S T SsubT.
  remember (F ++ x ~ bind_typ U ++ E) as E'.
  generalize dependent F.
  induction SsubT; intros F EQ; subst...
  Case "sub_trans_tvar".
    apply (sub_trans_tvar U0)...
    analyze_binds H...
  Case "sub_all".
    pick fresh X and apply sub_all...
    rewrite <- app_assoc.
    apply H0...
Qed.


(************************************************************************ *)
(** ** Narrowing for typing (7) *)

Lemma typing_narrowing : forall Q E F X P e T,
  sub E P Q ->
  typing (F ++ X ~ bind_sub Q ++ E) e T ->
  typing (F ++ X ~ bind_sub P ++ E) e T.
Proof with eauto 6 using wf_env_narrowing, wf_typ_narrowing, sub_narrowing.
  intros Q E F X P e T PsubQ Typ.
  remember (F ++ X ~ bind_sub Q ++ E) as E'.
  generalize dependent F.
  induction Typ; intros F EQ; subst...
  Case "typing_var".
    analyze_binds H0...
  Case "typing_abs".
    pick fresh y and apply typing_abs.
    rewrite <- app_assoc.
    apply H0...
  Case "typing_tabs".
    pick fresh Y and apply typing_tabs.
    rewrite <- app_assoc.
    apply H0...
  Case "typing_let".
    pick fresh y and apply typing_let...
    rewrite <- app_assoc.
    apply H0...
  Case "typing_case".
    pick fresh y and apply typing_case...
    SCase "inl branch".
      rewrite <- app_assoc.
      apply H0...
    SCase "inr branch".
      rewrite <- app_assoc.
      apply H2...
Qed.


(************************************************************************ *)
(** ** Substitution preserves typing (8) *)

Lemma typing_through_subst_ee : forall U E F x T e u,
  typing (F ++ x ~ bind_typ U ++ E) e T ->
  typing E u U ->
  typing (F ++ E) (subst_ee x u e) T.
(* begin show *)

(** We provide detailed comments for the following proof, mainly to
    point out several useful tactics and proof techniques.

    Starting a proof with "Proof with <some tactic>" allows us to
    specify a default tactic that should be used to solve goals.  To
    invoke this default tactic at the end of a proof step, we signal
    the end of the step with three periods instead of a single one,
    e.g., "apply typing_weakening...". *)

Proof with simpl_env;
           eauto 4 using wf_typ_strengthening,
                         wf_env_strengthening,
                         sub_strengthening.

  (** The proof proceeds by induction on the given typing derivation
      for e.  We use the [remember] tactic, along with [generalize
      dependent], to ensure that the goal is properly strengthened
      before we use induction. *)

  intros U E F x T e u TypT TypU.
  remember (F ++ x ~ bind_typ U ++ E) as E'.
  generalize dependent F.
  induction TypT; intros F EQ; subst; simpl subst_ee...

  (** The [typing_var] case involves a case analysis on whether the
      variable is the same as the one being substituted for. *)

  Case "typing_var".
    destruct (x0 == x); try subst x0.

    (** In the case where [x0=x], we first observe that hypothesis
        [H0] implies that [T=U], since [x] can only be bound once in
        the environment.  The conclusion then follows from hypothesis
        [TypU] and weakening.  We can use the [analyze_binds_uniq]
        tactic, described in the MetatheoryEnv library, with [H0] to
        obtain the fact that [T=U]. *)

    SCase "x0 = x".
      analyze_binds_uniq H0.
        injection BindsTacVal; intros; subst.

        (** In order to apply [typing_weakening], we need to rewrite
            the environment so that it has the right shape.  (We could
            also prove a corollary of typing_weakening.)  The
            [rewrite_env] tactic, described in the Environment
            library, is one way to perform this rewriting. *)

        rewrite_env (empty ++ F ++ E).
        apply typing_weakening...

    (** In the case where [x0<>x], the result follows by an exhaustive
        case analysis on exactly where [x0] is bound in the
        environment.  We perform this case analysis by using the
        [analyze_binds] tactic, described in the MetatheoryEnv
        library. *)

    SCase "x0 <> x".
      analyze_binds H0.
        eauto using wf_env_strengthening.
        eauto using wf_env_strengthening.

  (** Informally, the [typing_abs] case is a straightforward
      application of the induction hypothesis, which is called [H0]
      here. *)

  Case "typing_abs".

    (** We use the "pick fresh and apply" tactic to apply the rule
        [typing_abs] without having to calculate the appropriate
        finite set of atoms. *)

    pick fresh y and apply typing_abs.

    (** We cannot apply [H0] directly here.  The first problem is that
        the induction hypothesis has [(subst_ee open_ee)], whereas in
        the goal we have [(open_ee subst_ee)].  The lemma
        [subst_ee_open_ee_var] lets us swap the order of these two
        operations. *)

    rewrite subst_ee_open_ee_var...

    (** The second problem is how the concatenations are associated in
        the environments.  In the goal, we currently have

<<       (y ~ bind_typ V ++ F ++ E),
>>
        where concatenation associates to the right.  In order to
        apply the induction hypothesis, we need

<<        ((y ~ bind_typ V ++ F) ++ E).
>>
        We can use the [rewrite_env] tactic to perform this rewriting,
        or we can rewrite directly with an appropriate lemma from the
        MetatheoryEnv library. *)

    rewrite <- app_assoc.

    (** Now we can apply the induction hypothesis. *)

    apply H0...

  (** The remaining cases in this proof are straightforward, given
      everything that we have pointed out above. *)

  Case "typing_tabs".
    pick fresh Y and apply typing_tabs.
    rewrite subst_ee_open_te_var...
    rewrite <- app_assoc.
    apply H0...
  Case "typing_let".
    pick fresh y and apply typing_let...
    rewrite subst_ee_open_ee_var...
    rewrite <- app_assoc.
    apply H0...
  Case "typing_case".
    pick fresh y and apply typing_case...
      rewrite subst_ee_open_ee_var...
        rewrite <- app_assoc.
        apply H0...
      rewrite subst_ee_open_ee_var...
        rewrite <- app_assoc.
        apply H2...
Qed.
(* end show *)


(************************************************************************ *)
(** ** Type substitution preserves typing (11) *)

Lemma typing_through_subst_te : forall Q E F Z e T P,
  typing (F ++ Z ~ bind_sub Q ++ E) e T ->
  sub E P Q ->
  typing (map (subst_tb Z P) F ++ E) (subst_te Z P e) (subst_tt Z P T).
Proof with simpl_env;
           eauto 6 using wf_env_subst_tb,
                         wf_typ_subst_tb,
                         sub_through_subst_tt.
  intros Q E F Z e T P Typ PsubQ.
  remember (F ++ Z ~ bind_sub Q ++ E) as G.
  generalize dependent F.
  induction Typ; intros F EQ; subst;
    simpl subst_te in *; simpl subst_tt in *...
  Case "typing_var".
    apply typing_var...
      rewrite (map_subst_tb_id E Z P);
        [ | auto | eapply fresh_mid_tail; eauto ].
      analyze_binds H0...
  Case "typing_abs".
    pick fresh y and apply typing_abs.
    rewrite subst_te_open_ee_var...
    rewrite_env (map (subst_tb Z P) (y ~ bind_typ V ++ F) ++ E).
    apply H0...
  Case "typing_tabs".
    pick fresh Y and apply typing_tabs.
    rewrite subst_te_open_te_var...
    rewrite subst_tt_open_tt_var...
    rewrite_env (map (subst_tb Z P) (Y ~ bind_sub V ++ F) ++ E).
    apply H0...
  Case "typing_tapp".
    rewrite subst_tt_open_tt...
  Case "typing_let".
    pick fresh y and apply typing_let...
    rewrite subst_te_open_ee_var...
    rewrite_env (map (subst_tb Z P) (y ~ bind_typ T1 ++ F) ++ E).
    apply H0...
  Case "typing_case".
    pick fresh y and apply typing_case...
    SCase "inl branch".
      rewrite subst_te_open_ee_var...
      rewrite_env (map (subst_tb Z P) (y ~ bind_typ T1 ++ F) ++ E).
      apply H0...
    SCase "inr branch".
      rewrite subst_te_open_ee_var...
      rewrite_env (map (subst_tb Z P) (y ~ bind_typ T2 ++ F) ++ E).
      apply H2...
Qed.


(* ********************************************************************** *)
(** * #<a name="preservation"></a># Preservation *)


(* ********************************************************************** *)
(** ** Inversion of typing (13) *)

Lemma typing_inv_abs : forall E S1 e1 T,
  typing E (exp_abs S1 e1) T ->
  forall U1 U2, sub E T (typ_arrow U1 U2) ->
     sub E U1 S1
  /\ exists S2, exists L, forall x, x `notin` L ->
     typing (x ~ bind_typ S1 ++ E) (open_ee e1 x) S2 /\ sub E S2 U2.
Proof with auto.
  intros E S1 e1 T Typ.
  remember (exp_abs S1 e1) as e.
  generalize dependent e1.
  generalize dependent S1.
  induction Typ; intros S1 b1 EQ U1 U2 Sub; inversion EQ; subst.
  Case "typing_abs".
    inversion Sub; subst.
    split...
    exists T1. exists L...
  Case "typing_sub".
    auto using (sub_transitivity T).
Qed.

Lemma typing_inv_tabs : forall E S1 e1 T,
  typing E (exp_tabs S1 e1) T ->
  forall U1 U2, sub E T (typ_all U1 U2) ->
     sub E U1 S1
  /\ exists S2, exists L, forall X, X `notin` L ->
     typing (X ~ bind_sub U1 ++ E) (open_te e1 X) (open_tt S2 X)
     /\ sub (X ~ bind_sub U1 ++ E) (open_tt S2 X) (open_tt U2 X).
Proof with simpl_env; auto.
  intros E S1 e1 T Typ.
  remember (exp_tabs S1 e1) as e.
  generalize dependent e1.
  generalize dependent S1.
  induction Typ; intros S1 e0 EQ U1 U2 Sub; inversion EQ; subst.
  Case "typing_tabs".
    inversion Sub; subst.
    split...
    exists T1.
    exists (L0 `union` L).
    intros Y Fr.
    split...
    rewrite_env (empty ++ Y ~ bind_sub U1 ++ E).
    apply (typing_narrowing S1)...
  Case "typing_sub".
    auto using (sub_transitivity T).
Qed.

Lemma typing_inv_inl : forall E e1 T,
  typing E (exp_inl e1) T ->
  forall U1 U2, sub E T (typ_sum U1 U2) ->
  exists S1, typing E e1 S1 /\ sub E S1 U1.
Proof with eauto.
  intros E e1 T Typ.
  remember (exp_inl e1) as e. generalize dependent e1.
  induction Typ; intros e' EQ U1 U2 Sub; inversion EQ; subst.
  Case "typing_sub".
    eauto using (sub_transitivity T).
  Case "typing_inl".
    inversion Sub; subst...
Qed.

Lemma typing_inv_inr : forall E e1 T,
  typing E (exp_inr e1) T ->
  forall U1 U2, sub E T (typ_sum U1 U2) ->
  exists S1, typing E e1 S1 /\ sub E S1 U2.
Proof with eauto.
  intros E e1 T Typ.
  remember (exp_inr e1) as e. generalize dependent e1.
  induction Typ; intros e' EQ U1 U2 Sub; inversion EQ; subst.
  Case "typing_sub".
    eauto using (sub_transitivity T).
  Case "typing_inr".
    inversion Sub; subst...
Qed.


(* ********************************************************************** *)
(** ** Preservation (20) *)

Lemma preservation : forall E e e' T,
  typing E e T ->
  red e e' ->
  typing E e' T.
Proof with simpl_env; eauto.
  intros E e e' T Typ. generalize dependent e'.
  induction Typ; intros e' Red; try solve [ inversion Red; subst; eauto ].
  Case "typing_app".
    inversion Red; subst...
    SCase "red_abs".
      destruct (typing_inv_abs _ _ _ _ Typ1 T1 T2) as [P1 [S2 [L P2]]].
        apply sub_reflexivity...
      pick fresh x.
      destruct (P2 x) as [? ?]...
      rewrite (subst_ee_intro x)...
      rewrite_env (empty ++ E).
      apply (typing_through_subst_ee T).
        apply (typing_sub S2)...
          rewrite_env (empty ++ x ~ bind_typ T ++ E).
          apply sub_weakening...
        eauto.
  Case "typing_tapp".
    inversion Red; subst...
    SCase "red_tabs".
      destruct (typing_inv_tabs _ _ _ _ Typ T1 T2) as [P1 [S2 [L P2]]].
        apply sub_reflexivity...
      pick fresh X.
      destruct (P2 X) as [? ?]...
      rewrite (subst_te_intro X)...
      rewrite (subst_tt_intro X)...
      rewrite_env (map (subst_tb X T) empty ++ E).
      apply (typing_through_subst_te T1)...
  Case "typing_let".
    inversion Red; subst.
      SCase "red_let_1".
        eapply typing_let; eauto.
      SCase "red_let".
        pick fresh x.
        rewrite (subst_ee_intro x)...
        rewrite_env (empty ++ E).
        apply (typing_through_subst_ee T1)...
  Case "typing_case".
    inversion Red; subst.
    SCase "red_case_1".
      eapply typing_case; eauto.
    SCase "red_case_inl".
      destruct (typing_inv_inl _ _ _ Typ T1 T2) as [S1 [J2 J3]].
        apply sub_reflexivity...
      pick fresh x.
      rewrite (subst_ee_intro x)...
      rewrite_env (empty ++ E).
      apply (typing_through_subst_ee T1)...
    SCase "red_case_inr".
      destruct (typing_inv_inr _ _ _ Typ T1 T2) as [S1 [J2 J3]].
        apply sub_reflexivity...
      pick fresh x.
      rewrite (subst_ee_intro x)...
      rewrite_env (empty ++ E).
      apply (typing_through_subst_ee T2)...
Qed.


(* ********************************************************************** *)
(** * #<a name="progress"></a># Progress *)


(* ********************************************************************** *)
(** ** Canonical forms (14) *)

Lemma canonical_form_abs : forall e U1 U2,
  value e ->
  typing empty e (typ_arrow U1 U2) ->
  exists V, exists e1, e = exp_abs V e1.
Proof.
  intros e U1 U2 Val Typ.
  remember empty as E.
  remember (typ_arrow U1 U2) as T.
  revert U1 U2 HeqT HeqE.
  induction Typ; intros U1 U2 EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_sub".
    inversion H; subst; eauto.
    inversion H0.
Qed.

Lemma canonical_form_tabs : forall e U1 U2,
  value e ->
  typing empty e (typ_all U1 U2) ->
  exists V, exists e1, e = exp_tabs V e1.
Proof.
  intros e U1 U2 Val Typ.
  remember empty as E.
  remember (typ_all U1 U2) as T.
  revert U1 U2 HeqT HeqT.
  induction Typ; intros U1 U2 EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_sub".
    inversion H; subst; eauto.
    inversion H0.
Qed.

Lemma canonical_form_sum : forall e T1 T2,
  value e ->
  typing empty e (typ_sum T1 T2) ->
  exists e1, e = exp_inl e1 \/ e = exp_inr e1.
Proof.
  intros e T1 T2 Val Typ.
  remember empty as E.
  remember (typ_sum T1 T2) as T.
  revert T1 T2 HeqE HeqT.
  induction Typ; intros U1 U2 EQE EQT; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_sub".
    inversion H; subst; eauto.
    inversion H0.
Qed.


(* ********************************************************************** *)
(** ** Progress (16) *)

Lemma progress : forall e T,
  typing empty e T ->
  value e \/ exists e', red e e'.
Proof with eauto.
  intros e T Typ.
  remember empty as E. generalize dependent HeqE.
  assert (Typ' : typing E e T)...
  induction Typ; intros EQ; subst...
  Case "typing_var".
    inversion H0.
  Case "typing_app".
    right.
    destruct IHTyp1 as [Val1 | [e1' Rede1']]...
    SCase "Val1".
      destruct IHTyp2 as [Val2 | [e2' Rede2']]...
      SSCase "Val2".
        destruct (canonical_form_abs _ _ _ Val1 Typ1) as [S [e3 EQ]].
        subst.
        exists (open_ee e3 e2)...
  Case "typing_tapp".
    right.
    destruct IHTyp as [Val1 | [e1' Rede1']]...
    SCase "Val1".
      destruct (canonical_form_tabs _ _ _ Val1 Typ) as [S [e3 EQ]].
      subst.
      exists (open_te e3 T)...
  Case "typing_let".
    right.
    destruct IHTyp as [Val1 | [e1' Rede1']]...
  Case "typing_inl".
    destruct (typing_inv_inl _ _ _ Typ' T1 T2) as [S1 [J2 J3]].
    apply sub_reflexivity...
    destruct IHTyp as [J1 | [e' J1]]...
  Case "typing_inr".
    destruct (typing_inv_inr _ _ _ Typ' T1 T2) as [S1 [J2 J3]].
    apply sub_reflexivity...
    destruct IHTyp as [J1 | [e' J1]]...
  Case "typing_case".
    right.
    destruct IHTyp as [Val1 | [e' Rede']]...
    SCase "Val1".
      destruct (canonical_form_sum _ _ _ Val1 Typ) as [e4 [J1 | J1]].
      SSCase "Left J1".
        subst.
        exists (open_ee e2 e4).
        inversion Val1; subst.
        assert (expr (exp_case (exp_inl e4) e2 e3)) by auto.
        inversion H3...
      SSCase "Right J1".
        subst.
        exists (open_ee e3 e4)...
        inversion Val1; subst.
        assert (expr (exp_case (exp_inr e4) e2 e3)) by auto.
        inversion H3...
Qed.
