Require Import FcEtt.sigs.

Require Import FcEtt.tactics.

Require Export FcEtt.imports.
Require Export FcEtt.utils.

Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ind.
Require Export FcEtt.fset_facts.

Require Import FcEtt.erase_syntax.
Require Import FcEtt.ett_par.

Require Import FcEtt.beta.

Require Export FcEtt.fc_wf.

Require Export FcEtt.fc_context_fv.

Import FcEtt.ett_ott.

Module fc_subst (wf : fc_wf_sig) (weak : fc_weak_sig) <: fc_subst_sig.

Export wf.
Export weak.

Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.


(* --------------------------------------- *)


Lemma AnnCtx_strengthen : forall G1 G2, AnnCtx (G2 ++ G1) -> AnnCtx G1.
Proof.
  induction G2; [ | inversion 1]; simpl; auto.
Qed.


Lemma binds_to_AnnTyping :
  forall G x A, AnnCtx G -> binds x (Tm A) G -> AnnTyping G A a_Star.
Proof.
  induction 1; intros.
  + inversion H.
  + simpl in H2.
  destruct (binds_cons_1 _ x x0 (Tm A) (Tm A0) G H2) as [ [EQ Y] | N].
  - inversion Y. subst.
    eapply (AnnTyping_weakening  H0 [(x0, Tm A0)] nil G); eauto.
    simpl. eapply An_ConsTm; eauto.
  - pose K:= IHAnnCtx N.
    eapply (AnnTyping_weakening K [(x0, Tm A0)] nil G); simpl; eauto.
    eapply An_ConsTm; eauto.
    + destruct (binds_cons_1 _ x c (Tm A) (Co phi) G H2) as [ [EQ Y] | N].
      inversion Y.
      pose K := IHAnnCtx N.
      apply (AnnTyping_weakening K [(c, Co phi)] nil G); simpl; eauto.
      eapply An_ConsCo; eauto.
Qed.


Lemma binds_to_AnnPropWff: forall G0 a b A c,
    AnnCtx G0 -> binds c (Co (Eq a b A)) G0 -> AnnPropWff G0 (Eq a b A).
  induction G0; auto; try done.
  destruct a as [x s].
  intros a b A c H H0.
  destruct s; auto; try done.
  case H0; try done.
  + move => h0;
    simpl_env;
    eapply AnnPropWff_weakening with (F:=nil); eauto; simpl_env;
    inversion H; subst;
    apply (IHG0 _ _ _ c); eauto.
  + destruct H0; subst.
    inversion H0; subst.
    inversion H; subst.
    rewrite_env (nil ++ [(c, Co (Eq a b A))] ++ G0).
    eapply AnnPropWff_weakening; eauto.
    rewrite_env (nil ++ [(x, Co phi)] ++ G0).
    eapply AnnPropWff_weakening; eauto.
    simpl.
    inversion H; subst.
    apply (IHG0 _ _ _ c); auto.
Qed.

(* --------------------------------------- *)

Lemma tm_subst_fresh_1 :
forall G a A a0 x s,
  AnnTyping G a A -> AnnCtx ((x ~ s) ++ G) -> tm_subst_tm_tm a0 x A = A.
Proof.
  intros G a A a0 x s H H0.
  destruct s.
  - apply tm_subst_tm_tm_fresh_eq.
    inversion H0; subst; clear H0.
    move => h0.
    pose M1 := AnnTyping_context_fv H.
    clearbody M1.
    destruct M1 as [h2 [h3 [h4 h5]]].
    unfold "[<=]" in h4.
    pose M := h4 x h0; auto.
  - apply tm_subst_tm_tm_fresh_eq.
    inversion H0; subst; clear H0.
    move => h0.
    pose M1 := AnnTyping_context_fv H.
    clearbody M1.
    destruct M1 as [h2 [h3 [h4 h5]]].
    unfold "[<=]" in h4.
    pose M := h4 x h0; auto.
Qed.

Lemma tm_subst_fresh_2 :
forall G a A a0 x s,
  AnnTyping G a A -> AnnCtx ((x ~ s) ++ G) -> tm_subst_tm_tm a0 x a = a.
Proof.
  move=> G a A a' x s typ /= ctx.
  apply tm_subst_tm_tm_fresh_eq.
  apply AnnTyping_context_fv in typ; split_hyp.
  inversion ctx; subst; fsetdec.
Qed.

(*
Lemma co_subst_fresh :
forall G phi a0 x s,
  AnnPropWff G phi -> AnnCtx ((x ~ s) ++ G) -> tm_subst_tm_constraint a0 x phi = phi.
Proof.
  move=> G phi a' x s typ /= ctx.
  apply tm_subst_tm_constraint_fresh_eq.
  apply AnnPropWff_context_fv in typ; split_hyp.
  inversion ctx; subst; fsetdec.
Qed.
 *)

Lemma co_subst_fresh_1 :
  forall G a A g c s,
  AnnTyping G a A -> AnnCtx ((c ~ s) ++ G) -> co_subst_co_tm g c A = A.
Proof.
  intros.
  apply co_subst_co_tm_fresh_eq.
  apply AnnTyping_context_fv in H; split_hyp.
  inversion H0; subst; fsetdec.
Qed.

Lemma co_subst_fresh_2 :
  forall G a A g c s,
  AnnTyping G a A -> AnnCtx ((c ~ s) ++ G) -> co_subst_co_tm g c a = a.
Proof.
  intros.
  apply co_subst_co_tm_fresh_eq.
  apply AnnTyping_context_fv in H; split_hyp.
  inversion H0; subst; fsetdec.
Qed.


(* --------------------------------------- *)

Lemma subst_rho: forall L G a A x y b rho
    (T : AnnTyping G a A)
    (Neq: x <> y)
    (Fr: y `notin` fv_tm_tm_tm (erase_tm a))
    (Fr2: y `notin` L)
    (K : (forall x, x `notin` L -> RhoCheck rho x (erase_tm (open_tm_wrt_tm b (a_Var_f x))))),
    RhoCheck rho y (erase_tm (open_tm_wrt_tm (tm_subst_tm_tm a x b) (a_Var_f y))).
Proof.
  intros.
  rewrite? tm_subst_tm_tm_open_tm_wrt_tm_var; auto;
    try solve [apply (lc_typing T)].
  move: (K y Fr2) => RC.
  destruct rho.
  constructor.
  auto.
(*  autorewcs.
  rewrite -subst_tm_erase_tm.
  apply tm_subst_tm_tm_lc_tm. inversion RC. auto.
  apply lc_erase.
  apply (AnnTyping_lc T). *)
  inversion RC.
  constructor.
  autorewcs.
  rewrite -subst_tm_erase_tm.
  apply fv_tm_tm_tm_tm_subst_tm_tm_notin.
  auto. auto.
  apply (AnnTyping_lc T).
Qed.

Lemma co_subst_rho: forall L x y a rho g
    (LC: lc_co g)
    (Neq: x <> y)
    (Fr2: x `notin` L)
    (K : (forall x, x `notin` L -> RhoCheck rho x (erase_tm (open_tm_wrt_tm a (a_Var_f x))))),
    RhoCheck rho x (erase_tm (open_tm_wrt_tm (co_subst_co_tm g y a) (a_Var_f x))).
Proof.
  intros.
  rewrite? co_subst_co_tm_open_tm_wrt_tm_var; auto.
  move: (K x Fr2) => RC.
  inversion RC. subst.

  constructor.
  auto.
(*  autorewcs.
  rewrite -subst_co_erase_tm. auto.
*)
  constructor.
  autorewcs.
  rewrite -subst_co_erase_tm.
  auto.
Qed.

(* ------------------------------------------- *)




(* In the case of a binding term, prepare the environment in the goal for a use of
   the induction hypothesis *)

Ltac prepare_env :=
  match goal with
    [ |- context[ (?x' ~ (?S (?sub ?a1 ?x ?A))) ++ map (?tm_subst_tm_sort ?a1 ?x) ?F ++ ?G ] ] =>
    rewrite -app_assoc;
    replace (x' ~ (S (sub a1 x A)) ++  map (tm_subst_tm_sort a1 x) F) with
    (map (tm_subst_tm_sort a1 x) (x' ~ S A ++ F)); eauto using map_app
  end.

(* Find a binding for a prop in a well-formed context and invert it. *)
Ltac binds_PropWff_inversion :=
  let wff := fresh in
  match goal with
    [ bind_c : binds ?c (Co (Eq ?a ?b ?A)) ?G0 |- _ ] =>
    move: (@binds_to_AnnPropWff G0 _ _ _ _ ltac:(eauto with ctx_wff) bind_c) => wff;
   inversion wff; subst
  end.



Lemma ann_tm_substitution_mutual :
  (forall G0 b B (H : AnnTyping G0 b B),
      forall G a A, AnnTyping G a A ->
               forall F x, G0 = (F ++ (x ~ Tm A) ++ G) ->
                      AnnTyping (map (tm_subst_tm_sort a x) F ++ G)
                                (tm_subst_tm_tm a x b)
                                (tm_subst_tm_tm a x B)) /\
  (forall G0 phi (H : AnnPropWff G0 phi),
      forall G a A, AnnTyping G a A ->
               forall F x, G0 = (F ++ (x ~ Tm A) ++ G) ->
                      AnnPropWff (map (tm_subst_tm_sort a x) F ++ G)
                                 (tm_subst_tm_constraint a x phi)) /\
  (forall G0 D g p1 p2 (H : AnnIso G0 D g p1 p2),
      forall G a A, AnnTyping G a A ->
               forall F x, G0 = (F ++ (x ~ Tm A) ++ G) ->
                      AnnIso (map (tm_subst_tm_sort a x) F ++ G)
                             D
                             (tm_subst_tm_co a x g)
                             (tm_subst_tm_constraint a x p1)
                             (tm_subst_tm_constraint a x p2)) /\
  (forall  G0 D g A B (H : AnnDefEq G0 D g A B),
      forall G a A0, AnnTyping G a A0 ->
                forall F x, G0 = (F ++ (x ~ Tm A0) ++ G) ->
                       AnnDefEq (map (tm_subst_tm_sort a x) F ++ G)
                                D
                                (tm_subst_tm_co a x g)
                                (tm_subst_tm_tm a x A)
                                (tm_subst_tm_tm a x B)) /\
  (forall G0 (H : AnnCtx G0),
  forall G a A, AnnTyping G a A ->
  forall F x, G0 = (F ++ (x ~ Tm A) ++ G) ->
                AnnCtx (map (tm_subst_tm_sort a x) F ++ G)).

Proof.
  ann_induction CON.

  all: intros; subst.

  all: simpl tm_subst_tm_tm in *;
       simpl tm_subst_tm_co in *;
       simpl tm_subst_tm_constraint in *.

  all: match goal with
         [H1 : AnnTyping ?G0 ?a1 ?A0 |- _ ] => move: (AnnTyping_lc1 H1) => ? end.

  all: try (autorewrite with subst_open; auto).

  (* We do these first because they make eauto *really* slow *)
  (* An_Left *)
  all: try solve [ensure_case An_Left;
                  eapply An_Left with (b := (tm_subst_tm_tm a7 x b))
                                      (b' := (tm_subst_tm_tm a7 x b'));
                  try (autorewrite with open_subst; auto;
                       eapply AnnDefEq_weaken_available; eauto);
                  eauto 2 using Path_tm_subst_tm_tm;
                  eapply AnnDefEq_weaken_available; eauto].
  (* An_Right *)
  all: try solve [ensure_case An_Right;
                  eapply An_Right with (a := (tm_subst_tm_tm a7 x a))
                                       (a' := (tm_subst_tm_tm a7 x a'));
                  try (autorewrite with open_subst; auto;
                       eapply AnnDefEq_weaken_available; eauto);
                  eauto 2 using Path_tm_subst_tm_tm;
                  eapply AnnDefEq_weaken_available; eauto].
  (* An_CLeft *)
  all: try solve [ensure_case An_CLeft;
                  eapply An_CLeft with (g := (tm_subst_tm_co a9 x g))
                                         (g' := (tm_subst_tm_co a9 x g'));
                  try (autorewrite with open_subst; auto;
                       eapply AnnDefEq_weaken_available; eauto);
                  eauto 2 using Path_tm_subst_tm_tm;
                  eapply AnnDefEq_weaken_available; eauto].


  (* Binding cases *)
  all: try (An_pick_fresh x'; eauto; try (have neq: x <> x' by fsetdec_fast)).
  all: (* induction hypothesis *)
       try (prepare_env; repeat autorewrite with subst_open_var => //; eauto).
  all: (* rho check *)
       try (eapply subst_rho; eauto using fv_tm_erase_tm).
  all: (* substitution dance for the body *)
       try (autorewrite with subst_open_var; auto;
            rewrite_body;
            autorewrite with subst_open; auto;
            try (simpl; case: (x' == x) => [?|//]; by subst)).
  all: eauto 3 using AnnDefEq_weaken_available.

  (* Most straightforward cases *)
  all: try solve
           [ eapply CON; eauto 3 using AnnDefEq_weaken_available,
                         erase_subst_constraint, erase_subst_tm ].

  (* information for An_Const *)
  all: try ((have h0: AnnTyping nil A a_Star by eauto using an_toplevel_closed);
            eapply tm_subst_fresh_2 with (x:=x) in h0; eauto).
  (* information for An_Fam *)
  all: try ((have h0: AnnTyping nil a A by eauto using an_toplevel_closed);
            eapply tm_subst_fresh_1 with (x:=x) in h0; eauto).
  (* An_Const and An_Fam *)
  all: try solve [eapply CON; eauto; rewrite h0; eauto].

  (* An_Var *)
  - ensure_case An_Var.
    case: (x == x0) => [?|neq]; first subst x0.
       + have: A = A0 by apply binds_mid_eq in b;
          [move: b => [] | apply AnnCtx_uniq].
        move=> ?; subst A0.
        erewrite tm_subst_fresh_1  => //;
        eauto;
        last by eapply AnnCtx_strengthen; eassumption.
        apply AnnTyping_weakening with (F := nil) (G0 := G0) => //=.
        eauto.
      + eapply CON; eauto.
        * apply binds_remove_mid, binds_app_iff in b => //.
          case: b => [b|b].
          -- apply binds_app_2.
             (* If we had a lemma to rewrite `Tm (tm_subst_tm_tm a0 x0 A)` to and
              from `tm_subst_tm_sort a0 x0 (Tm A)`, this might be easier *)
             apply binds_map with (f := tm_subst_tm_sort a0 x0) in b; simpl in b.
             assumption.
          -- apply binds_app_3.
             erewrite tm_subst_fresh_2; try eauto using AnnCtx_strengthen.
             eapply binds_to_AnnTyping; last by eassumption.
             do 2 eapply AnnCtx_strengthen; eassumption.

    - (* An_Assn *)
      ensure_case An_Assn.
      eapply CON; eauto.
      rename b0 into bind_c.
      have neq: c ≠ x. {
        move=> ?; subst x.
        apply binds_mid_eq in bind_c.
        - discriminate bind_c.
        - by apply AnnCtx_uniq.
      }
      apply binds_remove_mid, binds_app_iff in bind_c => //.
      case: bind_c => [bind_c|bind_c].
      + apply binds_app_2.
      apply binds_map with (f := tm_subst_tm_sort a1 x) in bind_c; simpl in bind_c.
      eassumption.
      + apply binds_app_3.
      binds_PropWff_inversion.
      erewrite (tm_subst_fresh_1 (A := A));
        first repeat erewrite tm_subst_fresh_2;
        eauto using AnnCtx_strengthen.

    - (* An_Beta *)
      ensure_case An_Beta.
      eapply CON; eauto 2 using erase_subst_tm.
      autorewcs. rewrite -!subst_tm_erase_tm.
      eauto using Beta_tm_subst, lc_tm_erase, AnnTyping_lc1.
    - econstructor; eauto.
      intros.
      erewrite tm_subst_tm_tm_open_tm_wrt_co_var; eauto.
      erewrite e; eauto.

    (* context cases *)
    - ensure_case An_Empty.
      by move: H0 => /nil_eq_app [] /=.

    - ensure_case An_ConsTm.
      case: F H2 => [|[x' s] F] /= H2; first by eauto with ctx_wff.
      case: s H2 => [sPhi | sFm]; inversion 1; subst; simpl; econstructor; eauto.

    - ensure_case An_ConsCo.
      case: F H2 => [|[x' s] F] /= H2; first by eauto with ctx_wff.
      case: s H2 => [sPhi | sFm]; inversion 1; subst; simpl; econstructor; eauto.
      Unshelve. all: eauto.
Qed.



Lemma ann_co_substitution_mutual :
  (forall G0 b B, AnnTyping G0 b B ->
             forall G D g A1 A2 A3 F c,
               G0 = (F ++ (c ~ Co (Eq A1 A2 A3)) ++ G)
               -> AnnDefEq G D g A1 A2
               -> AnnTyping (map (co_subst_co_sort g c) F ++ G)
                           (co_subst_co_tm g c b) (co_subst_co_tm g c B)) /\
  (forall  G0 phi (H : AnnPropWff G0 phi),
      forall G D g A1 A2 A3 F c,
        G0 = (F ++ (c ~ Co (Eq A1 A2 A3)) ++ G)
        -> AnnDefEq G D g A1 A2
        -> AnnPropWff (map (co_subst_co_sort g c) F ++ G) (co_subst_co_constraint g c phi)) /\
  (forall G0 D0 g1 p1 p2 (H : AnnIso G0 D0 g1 p1 p2),
      forall G D g A1 A2 A3 F c,
        G0 = (F ++ (c ~ Co (Eq A1 A2 A3)) ++ G)
        -> AnnDefEq G D g A1 A2
        -> AnnIso (map (co_subst_co_sort g c) F ++ G)
                 (union D (remove c D0))
                 (co_subst_co_co g c g1)
                 (co_subst_co_constraint g c p1)
                 (co_subst_co_constraint g c p2)) /\
  (forall G0 D0 g1 A B (H : AnnDefEq G0 D0 g1 A B),
      forall G D g F c A1 A2 A3,
        G0 = (F ++ (c ~ Co (Eq A1 A2 A3)) ++ G)
        -> AnnDefEq G D g A1 A2
        -> AnnDefEq (map (co_subst_co_sort g c) F ++ G) (union D (remove c D0))
                   (co_subst_co_co g c g1)
                   (co_subst_co_tm g c A) (co_subst_co_tm g c B)) /\

  (forall  G0 (H : AnnCtx G0),
      forall G D g F c A1 A2 A3,
        G0 = (F ++ (c ~ Co (Eq A1 A2 A3)) ++ G)
        -> AnnDefEq G D g A1 A2
        -> AnnCtx (map (co_subst_co_sort g c) F ++ G)).
Proof.
  ann_induction CON.

  all: intros; subst.

  all: simpl co_subst_co_tm in *;
       simpl co_subst_co_co in *;
       simpl co_subst_co_constraint in *.

  all: match goal with
         [H1 : AnnDefEq ?G0 ?D ?g ?A1 ?A2 |- _ ] =>
         move: (AnnDefEq_lc H1) => [? [? ?]] end.

  all: try (autorewrite with subst_open; auto).

  (* We do these first because they make eauto *really* slow *)
  (* An_Left *)
  all: try solve [ensure_case An_Left;
                  eapply An_Left with (b := (co_subst_co_tm g c b))
                                      (b' := (co_subst_co_tm g c b'));
                  try (eapply Path_co_subst_co_tm; eauto);
                  eauto 2;
                  try (autorewrite with open_subst; eauto 2);
                  try (eapply AnnDefEq_weaken_available; eauto 2)].

  all: try solve [ensure_case An_Right;
                  eapply An_Right with (a := (co_subst_co_tm g c a))
                                      (a' := (co_subst_co_tm g c a'));
                  try (eapply Path_co_subst_co_tm; eauto);
                  eauto 2;
                  try (autorewrite with open_subst; eauto 2);
                  try (eapply AnnDefEq_weaken_available; eauto 2)].
  all: try solve [ensure_case An_CLeft;
                  eapply An_CLeft with (g := (co_subst_co_co g0 c g))
                                      (g' := (co_subst_co_co g0 c g'));
                  try (eapply Path_co_subst_co_tm; eauto);
                  eauto 2;
                  try (autorewrite with open_subst; eauto 2);
                  try (eapply AnnDefEq_weaken_available; eauto 2)].

  (* Binding cases *)
  all: try (An_pick_fresh x'; eauto; try (have neq: c <> x' by fsetdec_fast)).

  all: (* induction hypothesis *)
    try (prepare_env; repeat autorewrite with subst_open_var => //;
         eauto using app_assoc).
  all: (* rho check *)
       try (eapply co_subst_rho; eauto using fv_tm_erase_tm).
  all: (* substitution dance for the body *)
       try (autorewrite with subst_open_var; auto;
            rewrite_body;
            autorewrite with subst_open; auto;
            try (simpl; case: (x' == c) => [?|//]; by subst)).
  all: eauto 3 using AnnDefEq_weaken_available.


  (* Most straightforward cases *)
  all: try solve
           [ eapply CON; eauto 3 using AnnDefEq_weaken_available,
                         erase_subst_constraint, erase_subst_tm ].
  all: try solve
           [ eapply CON; eauto 3 using AnnDefEq_weaken_available;
             autorewcs; repeat rewrite -subst_co_erase_tm; auto].

  (* information for An_Const *)
  all: try ((have h0: AnnTyping nil A a_Star by eauto using an_toplevel_closed);
            eapply co_subst_fresh_2 with (c:=c) in h0; eauto).
  (* information for An_Fam *)
  all: try ((have h0: AnnTyping nil a A by eauto using an_toplevel_closed);
            eapply co_subst_fresh_1 with (c:=c) in h0; eauto).
  (* An_Const and An_Fam *)
  all: try solve [eapply CON; eauto; rewrite h0; eauto].

  - (* An_Var *)
    apply binds_app_1 in b.
    case:b; try done.
    + move => h0.
      eapply binds_map with (f:= co_subst_co_sort g c) in h0.
      eauto using binds_app_2.
    + intros b.
      apply binds_app_1 in b.
      case:b; try solve [move => h0; inversion h0; inversion H0].
      move => h0.
      rewrite co_subst_co_tm_fresh_eq.
      apply An_Var; auto.
        by eapply H; eauto.
      pose K := AnnCtx_strengthen ([(c, Co (Eq A1 A2 A3) )] ++ G0) _ a.
      clearbody K.
      inversion K; subst.
      have: AnnTyping G0 (a_Var_f x) A; auto => h1.
      pose M := AnnTyping_context_fv h1.
      clearbody M.
      destruct M as [h2 [h6 [h5 h3]]].
      unfold "[<=]" in h3.
      move => h4.
      apply H6.
      pose M := h3 c h4; auto.

  - (* An_Assn *)
    apply binds_app_1 in b0.
    case:b0; try done.
    + move => h0.
      destruct eq_dec; first subst c0.
      * exfalso.
        have: (c `notin` dom F) by eauto using AnnCtx_uniq, fresh_mid_head.
        simpl in h0.
        eapply binds_dom_contradiction; eassumption.
      * eapply An_Assn; eauto.
        apply binds_app_2.
         apply binds_map with (f:= co_subst_co_sort g c0) in h0. simpl in h0.
        eauto.
    + intros b0.
      apply binds_app_1 in b0.
      case:b0.
      -- move => h0; subst.
         inversion h0; try done.
         inversion H0; subst; clear H0.
         have: AnnCtx ([(c, Co (Eq a b A))] ++ G0).
         apply (AnnCtx_strengthen _ F); auto.
         move => Hi2.
         inversion Hi2; subst; clear Hi2.
         inversion H5; subst; clear H5.
         destruct eq_dec; try congruence.
         have DE: AnnDefEq G0 D0 g a b; auto.
         (*eapply (fourth weaken_available_mutual); eauto.
         move => DE.*)
         repeat rewrite co_subst_co_tm_fresh_eq; auto.
         ++ rewrite_env (nil ++(map (co_subst_co_sort g c) F) ++ G0).
            eapply AnnDefEq_weakening in DE.
            eapply (fourth ann_weaken_available_mutual) in DE.
            eapply DE. fsetdec. reflexivity.
            eapply H; eauto 1.
         ++ pose M := AnnTyping_context_fv H9.
            clearbody M.
            destruct M as [h5 [h4 h7]].
            unfold "[<=]" in h4.
            move => h6.
            apply H6; auto.
         ++ pose M := AnnTyping_context_fv H8.
            clearbody M.
            destruct M as [h4 [h5 h7]].
            unfold "[<=]" in h5.
            move => h6.
            apply H6; auto.
      -- move => h0.
         destruct eq_dec; try congruence.
          ++ subst.
             have ctx: AnnCtx ([(c0, Co (Eq A1 A2 A3))] ++ G0) by apply (AnnCtx_strengthen _ F); auto.
             inversion ctx; subst.
             apply binds_In in h0; done.
          ++ eapply An_Assn; eauto.
             have: AnnCtx G0.
             apply (AnnCtx_strengthen _ (F ++ [(c0, Co (Eq A1 A2 A3)) ])); auto.
               by rewrite -List.app_assoc; auto.
             move => Hi2.
             have: AnnPropWff G0 (Eq a b A) by apply (binds_to_AnnPropWff _ _ _ c).
             move => h1.
             inversion h1; subst; clear h1.
             instantiate (1 := (co_subst_co_tm g c0 A)).
             repeat rewrite co_subst_co_tm_fresh_eq.
               by apply binds_app_3.
             ** have h2: AnnCtx ([(c0, Co (Eq A1 A2 A3))] ++ G0) by apply (AnnCtx_strengthen _ F); auto.
                inversion h2; subst.
                pose M := AnnTyping_context_fv H5.
                clearbody M.
                destruct M as [h5 [h7 [_ h4]]].
                unfold "[<=]" in h4.
                move => h6.
                apply H9; auto.
             ** have h2: AnnCtx ([(c0, Co (Eq A1 A2 A3))] ++ G0) by apply (AnnCtx_strengthen _ F); auto.
                inversion h2; subst.
                pose M := AnnTyping_context_fv H6.
                clearbody M.
                destruct M as [_ [h4 _]].
                unfold "[<=]" in h4.
                move => h6.
                apply H9; auto.
             ** have h2: AnnCtx ([(c0, Co (Eq A1 A2 A3))] ++ G0) by apply (AnnCtx_strengthen _ F); auto.
                inversion h2; subst.
                pose M := AnnTyping_context_fv H5.
                clearbody M.
                destruct M as [_ [h4 _]].
                unfold "[<=]" in h4.
                move => h6.
                apply H9; auto.
  - eapply An_EtaC with (L := union L (singleton c)); eauto.
    intros. assert (Q: c0 `notin` L); eauto. eapply e in Q. 
    erewrite co_subst_co_tm_open_tm_wrt_co_var; eauto.
    erewrite e; eauto. assert (W: c0 `notin` singleton c). eauto. 
    apply notin_singleton_1 in W. simpl. 
    assert (X: (if c0 == c then g else g_Var_f c0) = g_Var_f c0).
    destruct (c0 == c). contradict W. auto. auto.
    rewrite X. auto.

  - induction F; done.
  - induction F; try done.

    destruct a1.
    destruct s; try inversion H1; subst.
    + simpl.
      apply An_ConsTm; auto.
      * inversion H1.
        eapply H; eauto.
        instantiate (1:= A3); auto.
      * simpl in H0.
        inversion H1; subst; clear H1.
        eapply H0; eauto.

  - inversion H1; subst; clear H1.
    induction F; try done.
    + inversion H4; subst; clear H4; auto.
    + destruct a1.
      destruct s; try inversion H4.
      simpl; subst.
      apply An_ConsCo; auto.
      * eapply H; eauto.
        instantiate (1:=A3); eauto.
      * inversion H4; subst; clear H4.
        eapply H0; eauto.
        instantiate (1:=A3); eauto.
 Unshelve. all: eauto.
Qed.



(* --------------------------------------- *)

(* Convenience lemmas for working with substitution. *)

Lemma AnnTyping_tm_subst : forall G x A b B (H : AnnTyping ((x ~ Tm A) ++ G) b B),
  forall a, AnnTyping G a A ->
       AnnTyping G (tm_subst_tm_tm a x b) (tm_subst_tm_tm a x B).
Proof.
  intros G x A b B H a H0.
  pose K := @first _ _ _ _ _ ann_tm_substitution_mutual _ b B H G a A H0 nil x.
  clearbody K. simpl in K.
  apply K. auto.
Qed.

Lemma AnnTyping_tm_subst_nondep : forall L G a A b B,
    AnnTyping G a A ->
    (forall x, x `notin` L -> AnnTyping ([(x,Tm A)] ++ G) (open_tm_wrt_tm b (a_Var_f x)) B) ->
    AnnTyping G (open_tm_wrt_tm b a) B.
Proof.
  intros L G a A b B H0 H4.
    pick fresh x. assert (FRL : x `notin` L). eauto.
    pose K := H4 x FRL. clearbody K.
    pose K2 := AnnTyping_tm_subst K H0. clearbody K2.
    simpl in K2.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm in K2; [| eapply (AnnTyping_lc H0)].
    rewrite tm_subst_tm_tm_var in K2.
    rewrite tm_subst_tm_tm_fresh_eq in K2; eauto.
    rewrite tm_subst_tm_tm_fresh_eq in K2; eauto.
Qed.


Lemma AnnTyping_co_subst : forall G x A1 A2 A3 b B (H : AnnTyping ((x ~ Co (Eq A1 A2 A3)) ++ G) b B),
  forall D a, AnnDefEq G D a A1 A2 ->
       AnnTyping G (co_subst_co_tm a x b) (co_subst_co_tm a x B).
Proof.
  intros G x A1 A2 A3 b B H D a H0.
  pose K := @first _ _ _ _ _ ann_co_substitution_mutual _ b B H G D a A1 A2 A3 nil x eq_refl H0.
  clearbody K. simpl in K.
  apply K.
Qed.


Lemma AnnTyping_co_subst_nondep : forall L G D g A1 A2 A3 b B,
    AnnDefEq G D g A1 A2 ->
    (forall x, x `notin` L -> AnnTyping ([(x,Co (Eq A1 A2 A3))] ++ G) (open_tm_wrt_co b (g_Var_f x)) B) ->
    AnnTyping G (open_tm_wrt_co b g) B.
Proof.
  intros L G D g A1 A2 A3 b B H0 H4.
    pick fresh x. assert (FRL : x `notin` L). eauto.
    pose K := H4 x FRL. clearbody K.
    pose K2 := AnnTyping_co_subst K H0. clearbody K2.
    simpl in K2.
    rewrite co_subst_co_tm_open_tm_wrt_co in K2; [| eapply (AnnDefEq_lc H0)].
    rewrite co_subst_co_co_var in K2.
    rewrite co_subst_co_tm_fresh_eq in K2; eauto.
    rewrite co_subst_co_tm_fresh_eq in K2; eauto.
Qed.


(* --------------------------------- *)

(* Convenience tactic for applying the coercion lemma above when there is an
   appropriate hypothesis in the context.

   This tactic is useful when the goal is not in the right form for backwards reasoning
   (i.e. has metavariables in it, doesn't have the substitution at the top.)

*)

Ltac co_subst_hyp :=
  match goal with
  | [a0 : AnnTyping _ (a_Abs ?rho ?A1 ?b) _  |-  AnnTyping _ (a_Abs ?rho (_ ?A1) (_ ?b)) _ ] =>
      eapply (first ann_co_substitution_mutual _ _ _ a0); eauto
  | [a0 :  AnnTyping _ (a_Pi ?rho ?A1 ?B1) _ |- AnnTyping _ (a_Pi ?rho (_ ?A1) (_ ?B1)) _  ] =>
      eapply (first ann_co_substitution_mutual _ _ _ a0); eauto
  | [a0 : AnnTyping _ (a_CAbs ?phi ?B) _  |- AnnTyping _ (a_CAbs (_ ?phi) (_ ?B)) _ ] =>
      eapply (first ann_co_substitution_mutual _ _ _ a0); eauto
  | [a0 : AnnTyping _ (a_CPi ?phi ?B) _ |- AnnTyping _ (a_CPi (_ ?phi) (_ ?B)) _ ] =>
    eapply (first ann_co_substitution_mutual _ _ _ a0); eauto
  | [ a0 : AnnTyping _ (a_App ?a1 ?rho ?a2) _ |- AnnTyping _ (a_App (_ ?a1) ?rho (_ ?a2)) _ ] =>
    eapply (first ann_co_substitution_mutual _ _ _ a0); eauto
  | [ a0 : AnnTyping _ (a_CApp ?a1 ?g2) _ |- AnnTyping _ (a_CApp (_ ?a1) (_ ?g2)) _ ] =>
    eapply (first ann_co_substitution_mutual _ _ _ a0); eauto
  | [a0 : AnnDefEq _  _ _ (a_CPi ?phi1 ?B1) (a_CPi ?phi2 ?B2)  |-
     AnnDefEq _ _ _ (a_CPi (_ ?phi1) _) (a_CPi (_ ?phi2) _) ] =>
    eapply AnnDefEq_weaken_available;
    eapply (fourth ann_co_substitution_mutual _ _ _ _ _ a0);
    eauto
  | [a0 : AnnPropWff _ (Eq ?a ?b ?A) |- AnnPropWff _ (Eq (_ ?a) (_ ?b) (_ ?A)) ] =>
    eapply (second ann_co_substitution_mutual _ _ a0); eauto
  | [ a0 : AnnTyping _ ?a _ |- AnnTyping _ (_ ?a) _ ] =>
    eapply (first ann_co_substitution_mutual _ _ _ a0); eauto
  | [a0 : AnnDefEq _ _ _ ?a _ |- AnnDefEq _ _ _ (_ ?a) _ ] =>
      eapply AnnDefEq_weaken_available;
      eapply (fourth ann_co_substitution_mutual _ _ _ _ _ a0);
      eauto
  | [ a0 : AnnDefEq _ _ ?g _ _ |- AnnDefEq _ _ (_ ?g) _ _ ] =>
      eapply AnnDefEq_weaken_available;
      eapply (fourth ann_co_substitution_mutual _ _ _ _ _ a0);
      eauto
  end.


(*
Ltac expand sub_tm tm :=
  match tm with
  | (a_Abs ?rho (_ ?A1) (_ ?b)) =>
    replace (a_Abs rho (sub_tm A1) (sub_tm b)) with (sub_tm (a_Abs rho A1 b)); auto
  | (a_Pi ?rho (_ ?A1) (_ ?B1)) =>
    replace (a_Pi rho (sub_tm A1) (sub_tm B1)) with (sub_tm (a_Pi rho A1 B1)); auto
  | (a_CAbs (?sc ?phi) (_ ?B)) =>
    replace (a_CAbs (sc phi) (sub_tm B)) with (sub_tm (a_CAbs phi B)); auto
  | (a_CPi (?sc ?phi) (_ ?B)) =>
    replace (a_CPi (sc phi) (sub_tm B)) with (sub_tm (a_CPi phi B)); auto

  | a_Star => replace a_Star with (sub_tm a_Star); auto

  | _ => idtac
  end.

Ltac expand_constraint sub_tm sub_constraint constraint :=
  match constraint with
  | (Eq (_ _ _ ?a) (_ _ _  ?b) (_ _ _ ?A)) =>
    replace (Eq (sub_tm a) (sub_tm b) (sub_tm A)) with
    (sub_constraint (Eq a b A)); auto
  | _ => idtac
  end.

Ltac un_co_subst_co :=
   match goal with
   | [ |- context [co_subst_co_tm ?g ?c _] ] =>
     match goal with
     | [ |- AnnTyping _ ?a ?A ] => expand (co_subst_co_tm g c) a; expand (co_subst_co_tm g c) A
     | [ |- AnnDefEq _ _ ?a ?b ] =>
       expand (co_subst_co_tm g c) a; expand (co_subst_co_tm g c) b
     | [ |- AnnPropWff ?phi ] =>
       expand_constraint (co_subst_co_tm g c) (co_subst_co_constraint g c) phi
     end
   end.
*)


(*
(* Pull a substitution out to prepare for an application of the substution lemma above *)
Ltac un_co_subst_co_tm' C :=
  match goal with
  | [ |- context [co_subst_co_tm ?g ?c ?a] ] =>
    replace C with (co_subst_co_tm g c C); auto
  end.

(* This doesn't work. *)
Ltac un_co_subst_co_tm :=

  match goal with
    | [ |- context [ a_Pi ?rho (co_subst_co_tm ?g ?c ?A1) (co_subst_co_tm ?g ?c ?B1)] ] =>
    replace (a_Pi rho (co_subst_co_tm g c A1) (co_subst_co_tm g c B1))
            with (co_subst_co_tm (a_Pi rho A1 B1)); auto
    | [ |- context[ (Eq (co_subst_co_tm ?g ?c ?a) (co_subst_co_tm ?g ?c ?b)
                     (co_subst_co_tm ?g ?c ?A)) ] ] =>
    replace (Eq (co_subst_co_tm g c a) (co_subst_co_tm g c b)
                (co_subst_co_tm g c A)) with
    (co_subst_co_constraint g c (Eq a b A)); auto

    | [ |- AnnTyping _ _ a_Star ] => un_co_subst_co_tm' a_Star
    | [ |- AnnTyping _ a_Star _ ] => un_co_subst_co_tm' a_Star
    | [ |- AnnDefEq _ _ a_Star _ _ ] => un_co_subst_co_tm' a_Star
    | [ |- AnnDefEq _ _ _ a_Star _ ] => un_co_subst_co_tm' a_Star                                               | [ |- AnnDefEq _ _ _ _ a_Star ] => un_co_subst_co_tm' a_Star

    | [ |- AnnTyping (a_Const ?T) _ ] => un_co_subst_co_tm' (a_Const T)
    | [ |- AnnTyping _ (a_Const ?T) ] => un_co_subst_co_tm' (a_Const T)

    | [ |- AnnTyping (a_Fam ?T) _ ] => un_co_subst_co_tm' (a_Fam T)
    | [ |- AnnTyping _ (a_Fam ?T) ] => un_co_subst_co_tm' (a_Fam T)

  end.
*)


Lemma ann_co_substitution_mutual2 :
    (forall G0 b B, AnnTyping G0 b B -> True) /\
    (forall G0 phi, AnnPropWff G0 phi -> True) /\
    (forall G0 D0 g1 p1 p2 (H : AnnIso G0 D0 g1 p1 p2),
        forall D G g A1 A2 A3 F c, G0 = (F ++ (c ~ Co (Eq A1 A2 A3)) ++ G)
                              -> AnnDefEq G D g A1 A2
                              -> c `notin` D0
                              -> AnnIso (map (co_subst_co_sort g c) F ++ G)
                                       D0
                                       (co_subst_co_co g c g1)
                                       (co_subst_co_constraint g c p1)
                                       (co_subst_co_constraint g c p2)) /\
    (forall G0 D0 g1 A B (H : AnnDefEq G0 D0 g1 A B),
        forall G D g F c A1 A2 A3, G0 = (F ++ (c ~ Co (Eq A1 A2 A3)) ++ G)
                              -> AnnDefEq G D g A1 A2
                              -> c `notin` D0
                              -> AnnDefEq (map (co_subst_co_sort g c) F ++ G) D0
                                         (co_subst_co_co g c g1)
                                         (co_subst_co_tm g c A) (co_subst_co_tm g c B)) /\
    (forall G0, AnnCtx G0 -> True).
Proof.
  ann_induction CON.

  all: intros; subst; auto.

  all: simpl co_subst_co_tm in *;
       simpl co_subst_co_co in *;
       simpl co_subst_co_constraint in *.

  all: match goal with
         [H1 : AnnDefEq ?G0 ?D ?g ?A1 ?A2 |- _ ] =>
         move: (AnnDefEq_lc H1) => [? [? ?]] end.

  all: try (ensure_case An_Left;
            eapply An_Left with (b := (co_subst_co_tm g c b))
                                (b' := (co_subst_co_tm g c b'));
            try (eapply Path_co_subst_co_tm; eauto)).

  all: try (ensure_case An_Right;
            eapply An_Right with (a := (co_subst_co_tm g c a))
                                   (a' := (co_subst_co_tm g c a'));
            try (eapply Path_co_subst_co_tm; eauto)).

  all: try (ensure_case An_CLeft;
            eapply An_CLeft with (g := (co_subst_co_co g0 c g))
                                   (g' := (co_subst_co_co g0 c g'));
            try (eapply Path_co_subst_co_tm; eauto)).



  all: try (An_pick_fresh x'; eauto; try (have neq: c <> x' by fsetdec_fast)).

  all: try co_subst_hyp.

  all: (* rho check *)
      try (eapply co_subst_rho; eauto using fv_tm_erase_tm).

  all: (* substitution dance for the body *)
       try (autorewrite with subst_open_var; auto;
            rewrite_body;
            autorewrite with subst_open; auto;
            try (simpl; case: (x' == c) => [?|//]; by subst)).

  all: try (prepare_env; repeat autorewrite with subst_open_var => //;
       eauto using app_assoc).

  all: try (autorewrite with open_subst; eauto 2; eapply AnnDefEq_weaken_available; eauto 2).

  all: try co_subst_hyp.

  all: try (autorewrite with subst_open; auto).

  all: try solve [eapply CON; eauto 2 using erase_co_subst_constraint, erase_co_subst_tm;
                  try co_subst_hyp].

  - simpl; simpl in H.
    apply binds_app_1 in b0.
    case:b0; try done.
    + move => h0.
      destruct eq_dec; first subst c0.
      * exfalso.
        have: (c `notin` dom F) by eauto using AnnCtx_uniq, fresh_mid_head.
        eapply binds_dom_contradiction; eassumption.
      * eapply An_Assn; eauto.
        eapply (fifth ann_co_substitution_mutual); eauto.
        apply binds_app_2.
        apply binds_map with (f:= co_subst_co_sort g c0) in h0; eauto.
    + intro bnd.
      destruct eq_dec; first subst c0.
      done.
      destruct (binds_app_1 _ c _ _ _ bnd).
      pose K := ( binds_one_1 _ _ _ _ _ H0). done.
      eapply An_Assn; eauto 2.
      eapply (fifth ann_co_substitution_mutual); eauto 1.
      assert (c0 `notin` dom G0).
      eapply fresh_mid_tail. eapply AnnCtx_uniq. eauto 1.
      assert (AnnPropWff G0 (Eq a b A)).
      eapply binds_to_AnnPropWff; eauto 1.
      eapply AnnCtx_strengthen.
      eapply AnnCtx_strengthen. eauto 2.
      inversion H4. subst.
      rewrite co_subst_co_tm_fresh_eq.
      rewrite co_subst_co_tm_fresh_eq.
      apply binds_app_3; eauto.
      destruct (AnnTyping_context_fv H10) as (h0 & h1 & h2 & h3).
      fsetdec.
      destruct (AnnTyping_context_fv H9) as (h0 & h1 & h2 & h3).
      fsetdec.
  - eapply An_Beta; try co_subst_hyp; eauto using erase_co_subst_tm.
    autorewcs.
    rewrite -!subst_co_erase_tm => /=.
    auto.
  - eapply An_EtaC with (L := union L (singleton c)); try co_subst_hyp; 
    eauto using erase_co_subst_tm.
    intros. assert (X: c0 `notin` L). eauto. apply e in X. 
    erewrite co_subst_co_tm_open_tm_wrt_co_var; eauto.
    rewrite X. simpl.
    assert (W: c0 `notin` singleton c). eauto.
    apply notin_singleton_1 in W.
    assert (Q: (if c0 == c then g else g_Var_f c0) = g_Var_f c0). 
    destruct (c0 == c). contradict W. auto. auto. 
    rewrite Q. auto.
Qed.


(* --------------------------------------------------------------------- *)

(* swapping lemmas ---> changing the name that is used to opened terms *)

Lemma AnnTyping_tm_swap : forall c c0 B G a A,
    c `notin` fv_tm_tm_tm A ->
    c `notin` fv_tm_tm_tm a ->
    c0 `notin` dom G \u {{ c }} ->
    AnnTyping ([(c, Tm B)] ++ G) (open_tm_wrt_tm a (a_Var_f c))
         (open_tm_wrt_tm A (a_Var_f c)) ->
    AnnTyping ([(c0, Tm B)] ++ G) (open_tm_wrt_tm a (a_Var_f c0))
                  (open_tm_wrt_tm A (a_Var_f c0)).
  Proof.
    intros c c0 B G a A Fr1 Fr2 Fr3 H.
    assert (AC : AnnCtx ([(c, Tm B)] ++ G)). eauto with ctx_wff.
    inversion AC. subst.
    assert (TV : AnnTyping ([(c0,Tm B)] ++ G)
                          (a_Var_f c0) B).
    eauto.
    assert (CTX : AnnCtx ([(c, Tm B)] ++ [(c0, Tm B)] ++ G)).
    econstructor; eauto with ctx_wff.
    pose M1 := (AnnTyping_weakening H4 [(c0,Tm B)] nil G) eq_refl. simpl_env in M1. eapply M1; eauto.
    pose K1 := AnnTyping_weakening H [(c0,Tm B)] [(c, Tm B)] G eq_refl CTX. clearbody K1.
  pose K2 := AnnTyping_tm_subst K1 TV. clearbody K2.
  repeat rewrite tm_subst_tm_tm_open_tm_wrt_tm in K2; auto.
  repeat rewrite tm_subst_tm_tm_var in K2.
  repeat rewrite tm_subst_tm_tm_fresh_eq in K2; eauto.
  Qed.


  Ltac rename_tm_Typing x0 K2 :=
    let M1 := fresh in
    let K1 := fresh in
    match goal with
      [ H0 : AnnTyping ([(?x, Tm ?A)] ++ ?G) (open_tm_wrt_tm ?B (a_Var_f ?x)) ?C |- _]
        => assert (AC : AnnCtx ([(x, Tm A)] ++ G)); eauto with ctx_wff;
          inversion AC; subst;
          assert (TV : AnnTyping ([(x0,Tm A)] ++ G) (a_Var_f x0) A); eauto;
          assert (CTX : AnnCtx ([(x,Tm A)] ++ [(x0, Tm A)] ++ G));
       [ match goal with
          [ H7 : AnnTyping G A a_Star |- _] =>
        econstructor; auto;
           pose M1 := (AnnTyping_weakening H7 [(x0,Tm A)] nil G);
                      simpl_env in M1; eapply M1; eauto end |
           pose K1 := AnnTyping_weakening H0 [(x0,Tm A)] [(x, Tm A)] G eq_refl CTX;
                      clearbody K1;
          pose K2 := (first ann_tm_substitution_mutual) _ _ _ K1 _ _ _ TV nil x eq_refl;
          clearbody K2; simpl_env in K2;
          repeat rewrite tm_subst_tm_tm_open_tm_wrt_tm in K2; auto;
          rewrite tm_subst_tm_tm_var in K2;
          rewrite tm_subst_tm_tm_fresh_eq in K2]
    end.

 Lemma AnnTyping_co_swap : forall c c0 phi G a A,
    c `notin` fv_co_co_tm A ->
    c `notin` fv_co_co_tm a ->
    c0 `notin` dom G \u {{ c }} ->
    AnnTyping ([(c, Co phi)] ++ G) (open_tm_wrt_co a (g_Var_f c))
         (open_tm_wrt_co A (g_Var_f c)) ->
    AnnTyping ([(c0, Co phi)] ++ G) (open_tm_wrt_co a (g_Var_f c0))
                  (open_tm_wrt_co A (g_Var_f c0)).
  Proof.
    intros c c0 phi G a A Fr1 Fr2 Fr3 H.
    destruct phi as [b0 b1  B].
    assert (AC : AnnCtx ([(c, Co (Eq b0 b1 B))] ++ G)). eauto with ctx_wff.
    inversion AC. subst.
    assert (TV : AnnDefEq ([(c0,Co (Eq b0 b1 B))] ++ G)
                          (singleton c0) (g_Var_f c0) b0 b1).
    eapply An_Assn; eauto.
    assert (CTX : AnnCtx ([(c, Co (Eq b0 b1 B))] ++ [(c0, Co (Eq b0 b1 B))] ++ G)).
    econstructor; eauto with ctx_wff.
    pose M1 := (AnnPropWff_weakening H4 [(c0,Co (Eq b0 b1 B))] nil G) eq_refl. simpl_env in M1. eapply M1; eauto.
    pose K1 := AnnTyping_weakening H [(c0,Co (Eq b0 b1 B))] [(c, Co (Eq b0 b1 B))] G eq_refl CTX. clearbody K1.
  pose K2 := AnnTyping_co_subst K1 TV. clearbody K2. simpl_env in K2.
  repeat rewrite co_subst_co_tm_open_tm_wrt_co in K2; auto.
  repeat rewrite co_subst_co_co_var in K2.
  repeat rewrite co_subst_co_tm_fresh_eq in K2; eauto.
Qed.

Lemma AnnDefEq_tm_swap : forall x1 x G A1 D g2 b1 b2,
   x1 `notin` fv_tm_tm_co g2 \u fv_tm_tm_tm b1 \u fv_tm_tm_tm b2
  -> x `notin` dom G \u {{ x1 }}
  -> AnnDefEq ([(x1, Tm A1)] ++ G) D  (open_co_wrt_tm g2 (a_Var_f x1))
             (open_tm_wrt_tm b1 (a_Var_f x1)) (open_tm_wrt_tm b2 (a_Var_f x1))
  -> AnnDefEq ([(x, Tm A1)] ++ G) D  (open_co_wrt_tm g2 (a_Var_f x))
             (open_tm_wrt_tm b1 (a_Var_f x)) (open_tm_wrt_tm b2 (a_Var_f x)).
Proof.
  intros x1 x G A1 D g2 b1 b2 Fr1 Fr2 H.
  assert (AC : AnnCtx ([(x1, Tm A1)] ++ G)). eauto with ctx_wff.
  inversion AC. subst.
  assert (TV : AnnTyping ([(x,Tm A1)] ++ G) (a_Var_f x) A1); eauto.
  assert (CTX : AnnCtx ([(x1,Tm A1)] ++ [(x, Tm A1)] ++ G)).
  { eapply An_ConsTm; auto.
    pose M1 := (AnnTyping_weakening H4 [(x,Tm A1)] nil G).
    simpl_env in M1. eapply M1; eauto. }
  pose K1 := AnnDefEq_weakening H [(x,Tm A1)] [(x1, Tm A1)] G eq_refl CTX.
  clearbody K1.
  pose K2 := (fourth ann_tm_substitution_mutual) _ _ _ _ _ K1 _ _ _ TV nil x1 eq_refl.
  clearbody K2. simpl_env in K2.
  repeat rewrite tm_subst_tm_co_open_co_wrt_tm in K2; auto.
  repeat rewrite tm_subst_tm_tm_open_tm_wrt_tm in K2; auto.
  rewrite tm_subst_tm_tm_var in K2.
  repeat rewrite tm_subst_tm_tm_fresh_eq in K2; auto.
  rewrite tm_subst_tm_co_fresh_eq in K2; auto.
Qed.

Lemma AnnDefEq_co_swap : forall c1 c phi1 G D g3 B1 B2,
    c1 `notin` D \u fv_co_co_tm B1 \u fv_co_co_tm B2 \u fv_co_co_co g3 ->
    c `notin` dom G \u {{ c1 }} ->
    (AnnDefEq ([(c1, Co phi1)] ++ G) D (open_co_wrt_co g3 (g_Var_f c1))
              (open_tm_wrt_co B1 (g_Var_f c1)) (open_tm_wrt_co B2 (g_Var_f c1)))
    -> (AnnDefEq ([(c, Co phi1)] ++ G) D (open_co_wrt_co g3 (g_Var_f c))
              (open_tm_wrt_co B1 (g_Var_f c)) (open_tm_wrt_co B2 (g_Var_f c))).
Proof.
  intros.
  assert (AC : AnnCtx ([(c1, Co phi1)] ++ G)). eauto with ctx_wff.
    inversion AC. subst.
    destruct phi1 as [A B A1].
    assert (TV : AnnDefEq ([(c,Co (Eq A B A1))] ++ G) (D \u singleton c) (g_Var_f c) A B).
    apply (An_Assn _ _ _ _ _ A1); auto.
    assert (CTX : AnnCtx ([(c1,Co (Eq A B A1))] ++ [(c, Co (Eq A B A1))] ++ G)). eapply An_ConsCo; auto.
    pose M1 := (AnnPropWff_weakening H6 [(c,Co (Eq A B A1))] nil G) eq_refl. simpl_env in M1. eapply M1; eauto.
    apply (fourth ann_remove_available_mutual) in H1.
    pose K1 := AnnDefEq_weakening H1 [(c,Co (Eq A B A1))] [(c1, Co (Eq A B A1))] G eq_refl CTX. clearbody K1.
    pose K2 := (fourth ann_co_substitution_mutual2) _ _ _ _ _ K1 _ _ _ nil c1 _ _ _ eq_refl TV; clearbody K2. simpl in K2.
    simpl_env in K2.
    repeat rewrite co_subst_co_co_open_co_wrt_co in K2; auto.
    repeat rewrite co_subst_co_tm_open_tm_wrt_co in K2; auto.
    repeat rewrite co_subst_co_co_var in K2.
    simpl in K2.
    repeat rewrite co_subst_co_tm_fresh_eq in K2.
    repeat rewrite co_subst_co_co_fresh_eq in K2.
  +  eapply (fourth ann_weaken_available_mutual).
      apply K2.
      apply notin_inter_2.
      fsetdec.
      fsetdec.
    + fsetdec.
    + fsetdec.
    + fsetdec.
Qed.


(* --------------------------------------------------------------------- *)

(* This is the place for "smart constructors" and "smart inversion"
   lemmas. They are especialy useful for constructing derivations from a
   particular variable and avoiding the co-finite quantification stuff.  *)

(* In a locally nameless development, these should be stated and immediately
   proven after substitution. *)



Lemma An_Pi_exists : forall x G rho A B,
    x `notin` dom G \u fv_tm_tm_tm B
  → AnnTyping ([(x, Tm A)] ++ G)
              (open_tm_wrt_tm B (a_Var_f x)) a_Star
  → AnnTyping G A a_Star
  → AnnTyping G (a_Pi rho A B) a_Star.
Proof.
  intros x G rho A B H H0 H1.
  eapply An_Pi with (L := (dom G \u singleton x)); auto.
  intros x0 H2.
  rename_tm_Typing x0 h0.
  eauto.
  eauto.
Qed.

Lemma An_Pi_inversion :
    ∀ (G:context) rho A B T,
      AnnTyping G (a_Pi rho A B) T ->
      T = a_Star /\
      AnnTyping G A a_Star /\
      ∀ x, x \notin dom G -> AnnTyping (( x ~ Tm  A) ++ G) (open_tm_wrt_tm B (a_Var_f x)) a_Star.
Proof.
  intros.
  inversion H. subst.
  do 2 split; auto.
  intros.
  pick fresh y.
  have: AnnTyping ([(y, Tm A)] ++ G) (open_tm_wrt_tm B (a_Var_f y)) a_Star by eapply H5; eauto 1.
  move => Ta.
  rename_tm_Typing x h0.
  auto. auto.
Qed.


Lemma An_Abs_exists :
  ∀ x (G:context) rho (A a B:tm),
    x \notin dom G \u fv_tm_tm_tm a \u fv_tm_tm_tm B ->
      AnnTyping G A a_Star ->
      AnnTyping (( x ~ Tm  A) ++ G)
                (open_tm_wrt_tm a (a_Var_f x))
                (open_tm_wrt_tm B (a_Var_f x))  ->
      RhoCheck rho x (erase_tm (open_tm_wrt_tm a (a_Var_f x))) ->
      AnnTyping G (a_Abs rho A a) (a_Pi rho A B).
Proof.
  intros x G rho A a B H H0 H1 RC.
  eapply An_Abs with (L := (dom G \u singleton x \u fv_tm_tm_tm (erase_tm a))); auto.
  intros x0 H2.
  rename_tm_Typing x0 K2; auto.
  repeat rewrite tm_subst_tm_tm_fresh_eq in K2; auto.
  intros. eapply ann_rho_swap with (x := x); eauto 2.
  eapply fv_tm_erase_tm. auto.
Qed.


Lemma fv_erase_tm_other : forall y G A x a,
    fv_tm_tm_tm (open_tm_wrt_tm a (a_Var_f y)) [<=] dom ([(y, Tm A)] ++ G) ->
    y `notin` {{ x }}  ->
    x `notin` dom G ->
    x `notin` fv_tm_tm_tm (erase_tm a).
    Proof.
      intros y G A x a H Fr Fr1.
    apply fv_tm_erase_tm.
    assert (H1 : fv_tm_tm_tm a [<=] dom ((y ~ Tm A) ++ G)).
    move: (@fv_tm_tm_tm_open_tm_wrt_tm_lower a (a_Var_f y)) => h1.
    fsetdec.
    simpl in H1.
    intros h2.
    apply H1 in h2.
    move: (F.add_iff (dom G) y x) => [h3 h4].
    apply h3 in h2. destruct h2. assert (y <> x). auto. done. done.
    Qed.

Lemma An_Abs_inversion :
  ∀ (G:context) rho (a:tm) A A1,
    AnnTyping G (a_Abs rho A a) A1 ->
    (exists B, A1 = a_Pi rho A B /\
    AnnTyping G A a_Star /\
    ∀ x, x \notin dom G ->
      RhoCheck rho x (erase_tm (open_tm_wrt_tm a (a_Var_f x))) /\
      AnnTyping (( x ~ Tm  A) ++ G)
                (open_tm_wrt_tm a (a_Var_f x))
                (open_tm_wrt_tm B (a_Var_f x))).
Proof.
  intros.
  inversion H. subst.
  exists B. split. auto. split. auto.
  intros.
  pose EA:= erase a.
  pick fresh y.
  have: AnnTyping ([(y, Tm A)] ++ G) (open_tm_wrt_tm a (a_Var_f y))
                  (open_tm_wrt_tm B (a_Var_f y)) by eapply H6; eauto 1.
  move => Ta.
  move: (H7 y ltac:(auto)) => h0.
  rename_tm_Typing x K2.
  repeat rewrite tm_subst_tm_tm_fresh_eq in K2; auto.
  split; last by auto.
  eapply ann_rho_swap with (x:=y); eauto.
  + destruct (AnnTyping_context_fv Ta) as [FV _].
    eapply (fv_erase_tm_other _ FV); eauto.
  + auto.
Qed.

Lemma An_Abs_impossible :   forall x G rho,
     x \notin dom G
   -> forall A a, (forall B, not (AnnTyping ((x ~ Tm A) ++ G) (open_tm_wrt_tm a (a_Var_f x)) B))
   -> forall A1, not (AnnTyping G (a_Abs rho A a) A1).
Proof.
  intros.
  intro TA1.
  inversion TA1. subst.
  destruct (An_Abs_inversion TA1) as (B0 & EQ & TA & ALLx).
  eapply H0.
  eapply ALLx. auto.
Qed.


Lemma An_CPi_exists :
    ∀ c (G : context) (phi : constraint) (B : tm),
      c \notin dom G \u fv_co_co_tm B ->
      AnnPropWff G phi
      → AnnTyping ([(c, Co phi)] ++ G) (open_tm_wrt_co B (g_Var_f c)) a_Star
      → AnnTyping G (a_CPi phi B) a_Star.
Proof.
  intros c G phi B H H0 H1.
  eapply An_CPi with (L := (dom G \u singleton c)); auto.
  intros c0 H2.
  replace a_Star with (open_tm_wrt_co a_Star (g_Var_f c0)); auto.
  eapply AnnTyping_co_swap; eauto.
Qed.



Lemma An_CPi_inversion :
    ∀ (G:context) (phi : constraint) (B T : tm),
      AnnTyping G (a_CPi phi B) T ->
      T = a_Star /\
      AnnPropWff G phi /\
      ∀ c, c \notin dom G
           -> AnnTyping ([(c, Co phi)] ++ G) (open_tm_wrt_co B (g_Var_f c)) a_Star.
Proof.
  intros.
  inversion H. subst.
  do 2 split; auto.
  intros.
  pick fresh c'.
  have: AnnTyping ([(c', Co phi)] ++ G) (open_tm_wrt_co B (g_Var_f c')) a_Star by eapply H5; eauto 1.
  move => Ta.
  replace a_Star with (open_tm_wrt_co a_Star (g_Var_f c)); auto.
  eapply (@AnnTyping_co_swap c'); eauto.
Qed.

Lemma An_CAbs_exists :  ∀ c (G : context) (phi : constraint) (a B : tm),
    c \notin dom G \u fv_co_co_tm a \u fv_co_co_tm B
      ->  AnnPropWff G phi
       → AnnTyping ([(c, Co phi)] ++ G) (open_tm_wrt_co a (g_Var_f c))
              (open_tm_wrt_co B (g_Var_f c))
       → AnnTyping G (a_CAbs phi a) (a_CPi phi B).
Proof.
  intros c G phi a B H H0 H1.
  pick fresh c0 and apply An_CAbs; auto.
  eapply (@AnnTyping_co_swap c); eauto.
Qed.

Lemma An_CAbs_inversion : ∀ (G : context) (phi : constraint) (a A : tm),
    AnnTyping G (a_CAbs phi a) A
    -> exists B, A = (a_CPi phi B) /\
    forall c, c  `notin` dom G
     ->   AnnPropWff G phi /\
       AnnTyping ([(c, Co phi)] ++ G) (open_tm_wrt_co a (g_Var_f c))
                 (open_tm_wrt_co B (g_Var_f c)).
Proof.
  intros G phi a A H.
  inversion H. subst.
  exists B.  do 2 split; auto.
  pick fresh c'.
  have: AnnTyping ([(c', Co phi)] ++ G)
                  (open_tm_wrt_co a (g_Var_f c'))
                  (open_tm_wrt_co B (g_Var_f c'))by eapply H5; eauto 1.
  move => Ta.
  eapply (@AnnTyping_co_swap c'); eauto.
Qed.


Lemma An_AbsCong_exists : ∀ x1 x2 (G : context) D rho (g1 g2 : co) (A1 b1 A2 b3 b2 B : tm),
    x1 `notin` (dom G \u fv_tm_tm_tm b1 \u fv_tm_tm_tm b2 \u  fv_tm_tm_co g2)
    -> x2 `notin` (dom G \u fv_tm_tm_tm b2 \u fv_tm_tm_tm b3 \u  fv_tm_tm_co g1)
    ->  AnnDefEq G D g1 A1 A2
    → (AnnDefEq ([(x1, Tm A1)] ++ G) D  (open_co_wrt_tm g2 (a_Var_f x1))
                (open_tm_wrt_tm b1 (a_Var_f x1)) (open_tm_wrt_tm b2 (a_Var_f x1)))
    → (open_tm_wrt_tm b3 (a_Var_f x2) =
       open_tm_wrt_tm b2 (a_Conv (a_Var_f x2) (g_Sym g1)))
    → AnnTyping G A1 a_Star
    → AnnTyping G A2 a_Star
    → RhoCheck rho x1 (erase_tm (open_tm_wrt_tm b1 (a_Var_f x1)))
    → RhoCheck rho x2 (erase_tm (open_tm_wrt_tm b3 (a_Var_f x2)))
    -> AnnTyping G (a_Abs rho A1 b2) B
    → AnnDefEq G D (g_AbsCong rho g1 g2) (a_Abs rho A1 b1) (a_Abs rho A2 b3).
Proof.
  intros.
  eapply An_AbsCong with (L := (dom G \u singleton x1 \u singleton x2 \u
                                    fv_tm_tm_tm (erase_tm b1) \u fv_tm_tm_tm (erase_tm b3))) (b2 := b2); auto.
  { intros.
    eapply AnnDefEq_tm_swap; eauto.
  }
  { intros x Fr.
    rewrite (tm_subst_tm_tm_intro x2); auto.
    rewrite H3.
    rewrite (tm_subst_tm_tm_open_tm_wrt_tm); auto.
    rewrite (tm_subst_tm_tm_fresh_eq); auto.
    rewrite tm_subst_cast.
    rewrite (tm_subst_tm_co_fresh_eq); auto.
  }
  intros. eapply ann_rho_swap with (x:=x1); eauto.
  eapply fv_tm_erase_tm; eauto.
  intros. eapply ann_rho_swap with (x:=x2); eauto.
  eapply fv_tm_erase_tm; eauto.
  eauto.
Qed.

Lemma An_AbsCong_inversion :
  forall G D rho g1 g2 B1 B2,
    AnnDefEq G D (g_AbsCong rho g1 g2) B1 B2 ->
  exists A1 A2 b1 b2 b3 B,
    B1 = (a_Abs rho A1 b1) /\
    B2 = (a_Abs rho A2 b3) /\
    AnnTyping G A1 a_Star  /\
    AnnTyping G A2 a_Star  /\
    AnnDefEq G D g1 A1 A2  /\
    AnnTyping G (a_Abs rho A1 b2) B /\
    (forall x, x \notin dom G ->
          AnnDefEq  ((x ~ Tm A1) ++  G) D (open_co_wrt_tm g2 (a_Var_f x))
                    (open_tm_wrt_tm b1 (a_Var_f x))
                    ((open_tm_wrt_tm b2 (a_Var_f x))) /\
          (open_tm_wrt_tm b3 (a_Var_f x)) =
          (open_tm_wrt_tm b2 (a_Conv (a_Var_f x) (g_Sym g1))) /\
          (RhoCheck rho x  (erase_tm (open_tm_wrt_tm b1 (a_Var_f x)))) /\
          (RhoCheck rho x  (erase_tm (open_tm_wrt_tm b3 (a_Var_f x))))).
Proof.
  intros G D rho g1 g2 B1 B2 h0.
  inversion h0; subst.
  exists A1, A2, b1, b2, b3, B.
  split; auto; split; auto; split; auto; split; auto; split; auto; split; auto.
  intros x FrX.
  pose EA:= erase b1.
  pose EB:= erase b3.
  pick fresh y.
  have: AnnDefEq ([(y, Tm A1)] ++ G) D (open_co_wrt_tm g2 (a_Var_f y))
                 (open_tm_wrt_tm b1 (a_Var_f y)) (open_tm_wrt_tm b2 (a_Var_f y)) by
      eapply H3; eauto 1.
  move => Da.
  repeat split.
  eapply (@AnnDefEq_tm_swap y); eauto.
  {
    rewrite (tm_subst_tm_tm_intro y); auto.
    rewrite H4.
    rewrite (tm_subst_tm_tm_open_tm_wrt_tm); auto.
    rewrite (tm_subst_tm_tm_fresh_eq); auto.
    rewrite tm_subst_cast.
    rewrite (tm_subst_tm_co_fresh_eq); auto.
    eauto.
  }
  { eapply ann_rho_swap with (x:=y); eauto.
    destruct (AnnDefEq_context_fv Da) as [_ [_ [FV _]]].
    apply (fv_erase_tm_other _ FV); eauto.
  }
  {
    eapply ann_rho_swap with (x:=y); eauto.
    destruct (AnnDefEq_context_fv h0) as [_ [_ [_ [_ [FV _]]]]].
    simpl in FV.
    apply fv_tm_erase_tm.
    intro. apply FrX. fsetdec.
  }
Qed.



Lemma An_CPiCong_exists :  ∀ c1 c2 (G : context) D (g1 g3 : co) (phi1 : constraint)
       (B1 : tm) (phi2 : constraint) (B3 B2 : tm),
    AnnIso G D g1 phi1 phi2
    -> c1 `notin` D \u fv_co_co_tm B2 \u fv_co_co_tm B1 \u fv_co_co_co g3
    -> c2 `notin` fv_co_co_co g1 \u fv_co_co_tm B2 \u fv_co_co_tm B3
    → (AnnDefEq ([(c1, Co phi1)] ++ G) D (open_co_wrt_co g3 (g_Var_f c1))
                (open_tm_wrt_co B1 (g_Var_f c1)) (open_tm_wrt_co B2 (g_Var_f c1)))
    → (open_tm_wrt_co B3 (g_Var_f c2) =
       open_tm_wrt_co B2 (g_Cast (g_Var_f c2) (g_Sym g1)))
    → AnnTyping G (a_CPi phi1 B1) a_Star
    → AnnTyping G (a_CPi phi2 B3) a_Star
    -> AnnTyping G (a_CPi phi1 B2) a_Star
    → AnnDefEq G D (g_CPiCong g1 g3) (a_CPi phi1 B1)
               (a_CPi phi2 B3).
Proof.
  intros.
  eapply An_CPiCong with (L := (dom G \u D \u singleton c1 \u singleton c2)) (B2 := B2); auto.
  - intros c h5.
    eapply AnnDefEq_co_swap with (c1 := c1); eauto.
  - intros c Fr.
    rewrite (co_subst_co_tm_intro c2); auto.
    rewrite H3.
    rewrite (co_subst_co_tm_open_tm_wrt_co); auto.
    rewrite (co_subst_co_tm_fresh_eq); auto.
    simpl.
    destruct eq_dec; try congruence.
    rewrite (co_subst_co_co_fresh_eq); auto.
Qed.


Lemma An_CPiCong_inversion :  ∀ (G : context) D (g1 g3 : co)
                                (A1 A2 : tm),
    AnnDefEq G D (g_CPiCong g1 g3) A1 A2
    -> exists phi1 phi2 B1 B2 B3,
     A1 = (a_CPi phi1 B1) /\
    A2 = (a_CPi phi2 B3) /\
    AnnIso G D g1 phi1 phi2 /\
    AnnTyping G (a_CPi phi1 B1) a_Star /\
    AnnTyping G (a_CPi phi2 B3) a_Star /\
    AnnTyping G (a_CPi phi1 B2) a_Star /\
    (forall c, c  `notin` dom G
    → (AnnDefEq ([(c, Co phi1)] ++ G) D (open_co_wrt_co g3 (g_Var_f c))
                (open_tm_wrt_co B1 (g_Var_f c)) (open_tm_wrt_co B2 (g_Var_f c))) /\
      (open_tm_wrt_co B3 (g_Var_f c) =
       open_tm_wrt_co B2 (g_Cast (g_Var_f c) (g_Sym g1)))).
Proof.
  intros.
  inversion H. subst.
  exists phi1, phi2, B1, B2, B3.
  repeat split; auto.
  + pick fresh c1. eapply (@AnnDefEq_co_swap c1); eauto.
  + pick fresh c1.
    rewrite (co_subst_co_tm_intro c1); auto.
    rewrite H4.
    rewrite (co_subst_co_tm_open_tm_wrt_co); auto.
    rewrite (co_subst_co_tm_fresh_eq); auto.
    simpl.
    destruct eq_dec; try congruence.
    rewrite (co_subst_co_co_fresh_eq); auto.
    eauto.
Qed.


Lemma An_PiCong_exists : forall x1 x2 (G:context) D rho
                           (g1 g2 : co) (A1 B1 A2 B3 B2 : tm),
    x1 `notin` (dom G \u fv_tm_tm_tm B1 \u fv_tm_tm_tm B2 \u  fv_tm_tm_co g2)
    -> x2 `notin` (dom G \u fv_tm_tm_tm B2 \u fv_tm_tm_tm B3 \u  fv_tm_tm_co g1)
    -> AnnDefEq G D g1 A1 A2
    → AnnDefEq ([(x1, Tm A1)] ++ G) D (open_co_wrt_tm g2 (a_Var_f x1))
               (open_tm_wrt_tm B1 (a_Var_f x1)) (open_tm_wrt_tm B2 (a_Var_f x1))
    → (open_tm_wrt_tm B3 (a_Var_f x2) =
       open_tm_wrt_tm B2 (a_Conv (a_Var_f x2) (g_Sym g1)))
    → AnnTyping G (a_Pi rho A1 B1) a_Star
    → AnnTyping G (a_Pi rho A2 B3) a_Star
    → AnnTyping G (a_Pi rho A1 B2) a_Star
    → AnnDefEq G D (g_PiCong rho g1 g2) (a_Pi rho A1 B1) (a_Pi rho A2 B3).
Proof.
  intros.
  eapply An_PiCong with (L := (dom G \u singleton x1 \u singleton x2)) (B2 := B2) ; auto.
  { intros.
    eapply (@AnnDefEq_tm_swap x1); eauto.
  }
  { intros x Fr.
    rewrite (tm_subst_tm_tm_intro x2); auto.
    rewrite H3.
    rewrite (tm_subst_tm_tm_open_tm_wrt_tm); auto.
    rewrite (tm_subst_tm_tm_fresh_eq); auto.
    rewrite tm_subst_cast.
    rewrite (tm_subst_tm_co_fresh_eq); auto.
  }
Qed.

Lemma An_PiCong_inversion : forall (G:context) (D:available_props) (rho:relflag) (g1 g2:co) (C1 C2 :tm),
    AnnDefEq G D (g_PiCong rho g1 g2) C1 C2
  -> exists A1 B1 A2 B2 B3,
    C1 = (a_Pi rho A1 B1) /\
    C2 = (a_Pi rho A2 B3) /\
    AnnTyping G (a_Pi rho A1 B1) a_Star /\
    AnnTyping G (a_Pi rho A2 B3) a_Star /\
    AnnTyping G (a_Pi rho A1 B2) a_Star /\
    AnnDefEq G D g1 A1 A2 /\

    (forall x , x \notin dom G  ->
            AnnDefEq  (( x ~ Tm  A1 ) ++  G )  D  ( open_co_wrt_tm g2 (a_Var_f x) )   ( open_tm_wrt_tm B1 (a_Var_f x) )   (  (open_tm_wrt_tm  B2   (a_Var_f x) )  )  /\
            (open_tm_wrt_tm B3 (a_Var_f x)  = (open_tm_wrt_tm  B2   (a_Conv (a_Var_f x) (g_Sym g1))))).
Proof.
  intros G D rho g1 g2 C1 C2 h0.
  dependent induction h0; eauto.
  exists A1, B1, A2, B2, B3.
  repeat split; eauto.
  + pick fresh x1.
    eapply (@AnnDefEq_tm_swap x1); eauto.
  + pick fresh x1.
    rewrite (tm_subst_tm_tm_intro x1); auto.
    rewrite H1.
    rewrite (tm_subst_tm_tm_open_tm_wrt_tm); auto.
    rewrite (tm_subst_tm_tm_fresh_eq); auto.
    rewrite tm_subst_cast.
    rewrite (tm_subst_tm_co_fresh_eq); auto.
    eauto.
Qed.

Lemma An_CAbsCong_exists :
  forall c1 c2 (G : context) (D : available_props) (g1 g3 g4 : co)
    (phi1 : constraint) (a1 : tm) (phi2 : constraint) (a3 a2 B1 B2 B : tm),
    AnnIso G D g1 phi1 phi2
    -> c1 `notin` D \u fv_co_co_tm a2 \u fv_co_co_tm a1 \u fv_co_co_co g3
    -> c2 `notin` fv_co_co_co g1 \u fv_co_co_tm a2 \u fv_co_co_tm a3
    → (AnnDefEq ([(c1, Co phi1)] ++ G) D (open_co_wrt_co g3 (g_Var_f c1))
                (open_tm_wrt_co a1 (g_Var_f c1)) (open_tm_wrt_co a2 (g_Var_f c1)))
    → (open_tm_wrt_co a3 (g_Var_f c2) =
       open_tm_wrt_co a2 (g_Cast (g_Var_f c2) (g_Sym g1)))
    → AnnTyping G (a_CAbs phi1 a1) (a_CPi phi1 B1)
    → AnnTyping G (a_CAbs phi2 a3) (a_CPi phi2 B2)
    → AnnDefEq G (dom G) g4 (a_CPi phi1 B1) (a_CPi phi2 B2)
    -> AnnTyping G (a_CAbs phi1 a2) B
    → AnnDefEq G D (g_CAbsCong g1 g3 g4) (a_CAbs phi1 a1) (a_CAbs phi2 a3).
Proof.
  intros c1 c2 G D g1 g3 g4 phi1 a1 phi2 a3 a2 B1 B2. intros.
  eapply An_CAbsCong with (a1 := a1) (a2 := a2)
     (L := (dom G \u D \u singleton c1 \u singleton c2)) (B2 := B2); eauto.
  - intros c Fr.
    eapply (@AnnDefEq_co_swap c1); eauto.
  - intros c Fr.
    rewrite (co_subst_co_tm_intro c2); auto.
    rewrite H3.
    rewrite (co_subst_co_tm_open_tm_wrt_co); auto.
    rewrite (co_subst_co_tm_fresh_eq); auto.
    simpl.
    destruct eq_dec; try congruence.
    rewrite (co_subst_co_co_fresh_eq); auto.
Qed.


Lemma An_CAbsCong_inversion :
  forall (G : context) (D : available_props) (g1 g3 g4 : co) A1 A2,
    AnnDefEq G D (g_CAbsCong g1 g3 g4) A1 A2
    -> exists phi1 phi2 a1 a2 a3 B1 B2 B,
      A1 = (a_CAbs phi1 a1) /\
      A2 = (a_CAbs phi2 a3) /\
      AnnIso G D g1 phi1 phi2 /\
      AnnTyping G (a_CAbs phi1 a1) (a_CPi phi1 B1) /\
      AnnTyping G (a_CAbs phi2 a3) (a_CPi phi2 B2) /\
      AnnTyping G (a_CAbs phi1 a2) B /\
      AnnDefEq G (dom G) g4 (a_CPi phi1 B1) (a_CPi phi2 B2) /\
      forall c1,
      c1`notin` dom G
    → (AnnDefEq ([(c1, Co phi1)] ++ G) D (open_co_wrt_co g3 (g_Var_f c1))
                (open_tm_wrt_co a1 (g_Var_f c1)) (open_tm_wrt_co a2 (g_Var_f c1))) /\
      (open_tm_wrt_co a3 (g_Var_f c1) =
       open_tm_wrt_co a2 (g_Cast (g_Var_f c1) (g_Sym g1))).
Proof.
  intros G D g1 g3 g4 A1 A2 h0.
  dependent induction h0; eauto.
  exists phi1, phi2, a1, a2, a3, B1, B2, B.
  repeat split; eauto; try done.
  + pick fresh c.
    eapply (@AnnDefEq_co_swap c); eauto.
  + pick fresh c.
    rewrite (co_subst_co_tm_intro c); auto.
    rewrite H2.
    rewrite (co_subst_co_tm_open_tm_wrt_co); auto.
    rewrite (co_subst_co_tm_fresh_eq); auto.
    simpl.
    destruct eq_dec; try congruence.
    rewrite (co_subst_co_co_fresh_eq); auto.
    eauto.
Qed.

End fc_subst.
