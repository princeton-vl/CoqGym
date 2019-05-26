Require Import FcEtt.sigs.

Require Import FcEtt.imports.
Require Import FcEtt.dep_prog.
Require Export FcEtt.ett_ind.
Require Export FcEtt.ett_par. (* FIXME: the axioms about toplevel shouldn't be there *)
Require Export FcEtt.erase_syntax.  (* lc_erase *)

Module fc_dec_aux (wf : fc_wf_sig) (weak : fc_weak_sig) (subst : fc_subst_sig) (unique: fc_unique_sig).

Import unique.

(**** Decision procedures for a few auxiliary relations ****)

Lemma eq_relflag_dec : forall t1 t2 : relflag, {t1 = t2} +  {~ t1 = t2}.
Proof.
  decide equality.
Defined.

Ltac nosub t2 :=  destruct t2; try solve[ left; auto]; right; done.

Ltac onesub t2 :=
    let h := fresh in
    destruct t2;
    try solve [right; done];
    match goal with
      [
         H0 : ∀ t2, {?B = t2} + {?B ≠ t2} |-
                    { ?C ?B = ?C ?e } + { ?F } ] =>
      destruct (H0 e); subst;
        try solve [left; auto];
        try solve [right; intro h; inversion h; done]
            end.
Ltac twosub t2 :=
    let h := fresh in
    destruct t2;
    try solve [right; done];
    match goal with
      [  H : ∀ t2, {?phi = t2} + {?phi ≠ t2},
         H0 : ∀ t2, {?B = t2} + {?B ≠ t2} |-
                    { ?C ?phi ?B = ?C ?d ?e } + { ?F } ] =>
      destruct (H d); subst; destruct (H0 e); subst;
        try solve [left; auto];
        try solve [right; intro h; inversion h; done]
         end.
Ltac threesub t2 :=
    let h := fresh in
    destruct t2;
    try solve [right; done];
    match goal with
      [  H : ∀ t2, {?phi = t2} + {?phi ≠ t2},
         H1 : ∀ t2, {?A = t2} + {?A ≠ t2},
         H0 : ∀ t2, {?B = t2} + {?B ≠ t2} |-
                    { ?C ?phi ?A ?B = ?C ?d ?e ?f} + { ?F } ] =>
      destruct (H d); subst; destruct (H1 e); subst;
      destruct (H0 f); subst;
        try solve [left; auto];
        try solve [right; intro h; inversion h; done]
         end.

Lemma tm_eq_dec_mutual :
  ((forall t1 t2 : tm, {t1 = t2} +  {~ t1 = t2}) *
   (forall t1 t2 : brs, {t1 = t2} +  {~ t1 = t2}) *
   (forall t1 t2 : co, {t1 = t2} +  {~ t1 = t2}) *
   (forall t1 t2 : constraint, {t1 = t2} +  {~ t1 = t2})).
Proof.
  eapply tm_brs_co_constraint_mutrec.
  all:  try solve [intros; onesub t2].
  all:  try solve [intros; twosub t2].
  all:  try solve [intros; threesub t2].
  all: try solve [intros; nosub t2].
  { intro n. destruct t2.
    all : try solve [right; done].
    edestruct (eq_nat_dec n n0). subst. left. auto. right.
    intro H. inversion H. done. }
  { intro x. destruct t2.
    all : try solve [right; done].
    (* edestruct (eq_atom_dec x x0). subst. left. auto. right.
    intro H. inversion H. done. *)
    edestruct (EqDec_atom x x0). inversion e.
    subst. left. auto. right.
    intro H. inversion H. done. }
  { intros rho A t2 b t3 t0.
    destruct t0.
    all : try solve [right; done].
    destruct (eq_relflag_dec rho rho0). subst.
    destruct (t2 t0_1). subst.
    destruct (t3 t0_2). subst.
    left. auto.
    all: right; intro H; inversion H; done. }
  { intros rho b H2 t2.
    destruct t2.
    all : try solve [right; done].
    destruct (eq_relflag_dec rho rho0). subst.
    destruct (H2 t2). subst.
    left. auto.
    all: right; intro H; inversion H; done. }
  { intros a H2 rho b H3 t2.
    destruct t2.
    all : try solve [right; done].
    destruct (eq_relflag_dec rho rho0). subst.
    destruct (H2 t2_1). subst.
    destruct (H3 t2_2). subst.
    left. auto.
    all: right; intro H; inversion H; done. }
  { intros F t2.
    destruct t2.
    all : try solve [right; done].
    (* destruct (eq_atom_dec F F0). subst.
    left. auto.
    right; intro H; inversion H; done.*)
    destruct (EqDec_atom F F0). inversion e. subst.
    left. auto. right; intro H; inversion H; done. }
  { intros T t2.
    destruct t2.
    all : try solve [right; done].
    (* destruct (eq_atom_dec T T0). subst.
    left. auto.
    right; intro H; inversion H; done. *)
    destruct (EqDec_atom T T0). inversion e. subst.
    left. auto. right; intro H; inversion H; done. }
  { intros.
    destruct t2.
    all : try solve [right; done].
    destruct (eq_relflag_dec rho rho0). subst.
    destruct (H t2_1). subst.
    destruct (H0 t2_2). subst.
    left. auto.
    all: right; intro h; inversion h; done. }
  { intros K t2.
    destruct t2.
    all : try solve [right; done].
    (* edestruct (eq_atom_dec K K0). subst. left. auto. right.
    intro H. inversion H. done. *)
    destruct (EqDec_atom K K0). inversion e. subst.
    left. auto. right; intro H; inversion H; done. }
  { intros.
    destruct t2.
    all : try solve [right; done].
    (* destruct (eq_atom_dec K K0). subst.
    destruct (H a0). subst.
    destruct (H0 t2). subst.
    left. auto.
    all: right; intro h; inversion h; done.*)
    destruct (EqDec_atom K K0). subst.
    destruct (H a0). subst.
    destruct (H0 t2). subst.
    left. inversion e. auto.
    all: right; intro h; inversion h; done. }
  { intro n. destruct t2.
    all : try solve [right; done].
    edestruct (eq_nat_dec n n0). subst. left. auto. right.
    intro H. inversion H. done. }
  { intro x. destruct t2.
    all : try solve [right; done].
    (* edestruct (eq_atom_dec x c). subst. left. auto. right.
    intro H. inversion H. done. *)
    edestruct (EqDec_atom x c). inversion e. subst. left. auto. right.
    intro H. inversion H. done. }
  { intros.
    destruct t2.
    all : try solve [right; done].
    destruct (eq_relflag_dec rho rho0). subst.
    destruct (H t2_1). subst.
    destruct (H0 t2_2). subst.
    left. auto.
    all: right; intro h; inversion h; done. }
  { intros. destruct t2.
    all : try solve [right; done].
    destruct (eq_relflag_dec rho rho0). subst.
    destruct (H t2_1). subst.
    destruct (H0 t2_2). subst.
    left. auto.
    all: right; intro h; inversion h; done. }
  { intros.  destruct t2.
    all : try solve [right; done].
    destruct (eq_relflag_dec rho rho0). subst.
    destruct (H t2_1). subst.
    destruct (H0 t2_2). subst.
    left. auto.
    all: right; intro h; inversion h; done. }
Defined.

Lemma tm_eq_dec : forall t1 t2 : tm, {t1 = t2} + {~ t1 = t2}.
Proof.
  by move: tm_eq_dec_mutual => [[[? _] _]_].
Defined.

Lemma const_eq_dec : forall (phi1 phi2 : constraint), {phi1 = phi2} + {¬ phi1 = phi2}.
Proof.
  by move: tm_eq_dec_mutual => [_ ?].
Defined.

Lemma co_eq_dec : forall g1 g2 : co, {g1 = g2} + {~ g1 = g2}.
Proof.
  by move: tm_eq_dec_mutual => [[_ ?]_].
Defined.


Lemma in_dec : forall x L, {x `in` L} + {¬ x `in` L}.
Proof.
  intros.
  destruct (AtomSetProperties.In_dec x L); auto.
Qed.

Lemma not_in_dec : forall x L, {¬ x `in` L} + {x `in` L}.
Proof.
  intros.
  destruct (AtomSetProperties.In_dec x L); auto.
Qed.

Lemma uniq_binds_dec_tm : forall x G, uniq G -> {A | binds x (Tm A) G} + {(forall A, ¬ binds x (Tm A) G)}.
Proof.
  intros.
  destruct (binds_lookup _ x G).
  destruct s. destruct x0.
  econstructor.
  exists A. auto.
  eapply inright.
  intros A b0.
  assert (Co phi = Tm A). eapply binds_unique; eauto. inversion H0.
  eapply inright.
  intro A.
  eapply (n (Tm A)).
Qed.


Lemma binds_dec_tm : forall x G, {A | binds x (Tm A) G} + {(forall A, ¬ binds x (Tm A) G)}.
Proof.
  intros x G.
  induction G.
  - eapply inright.
    intros A I. inversion I.
  - destruct IHG.
    { eapply inleft.
      destruct s. exists x0. destruct a. auto. }
    { destruct a.
      destruct (x == a).
      destruct s.
      eapply inleft. exists A. auto.
      eapply inright. intros A H.
      apply binds_cons_1 in H. destruct H as [ [h0 h1]|b0].
      inversion h1. apply n in b0. done.
      eapply inright. intros A H.
      apply binds_cons_1 in H. destruct H as [ [h0 h1]|b0].
      done. apply n in b0. done. }
Qed.


Lemma binds_dec_co : forall x G, {AB, K | binds x (Co (Eq (fst AB) (snd AB) K)) G} + {(forall A B K, ¬ binds x (Co (Eq A B K)) G)}.
Proof.
  intros x G.
  induction G.
  - eapply inright.
    intros A B K I. inversion I.
  - destruct IHG.
    { eapply inleft.
    destruct s. exists x0 y. destruct a. auto. }
    { destruct a.
    destruct (x == a). subst.
    destruct s.

    eapply inright. intros A1 B K H.
    apply binds_cons_1 in H. destruct H as [ [h0 h1]|b0].
    inversion h1. apply n in b0. done.
    destruct phi.
    eapply inleft. exists (a0,b) A. auto.
    eapply inright. intros A B K H.
    apply binds_cons_1 in H. destruct H as [ [h0 h1]|b0].
    done. apply n in b0. done.
    }
Qed.



Lemma binds_dec_cs : forall x G, {C | binds x (Cs  C) G} + {(forall C, ¬ binds x (Cs  C) G)}.
Proof.
  intros x G.
  induction G.
  - eapply inright.
    intros C I. inversion I.
  - destruct IHG.
    { eapply inleft.
    destruct s. exists x0. destruct a. auto. }
    { destruct a.
    destruct (x == a). subst.
    destruct s.
    eapply inleft. exists A. auto.

    eapply inright. intros C H.
    apply binds_cons_1 in H. destruct H as [ [h0 h1]|b0].
    inversion h1. apply n in b0. done.

    eapply inright. intros C H.
    apply binds_cons_1 in H. destruct H as [ [h0 h1]|b0].
    done. apply n in b0. done.
    }
Qed.

Lemma Path_dec : forall a, lc_tm a -> { T | Path T a } + { (forall T, not (Path T a)) }.
Proof.
  induction a; intros LC.
  all: try solve [apply inleft; eauto].
  all: try solve [apply inright; move => T h1; inversion h1].
  - destruct IHa1 as [[T h0]|n].
    { inversion LC. auto. }
    apply inleft. eexists.
    { inversion LC. eauto. }
    apply inright. move => T h1. inversion h1.
    subst. unfold not in n. eauto.
  - destruct IHa as [[T h0]|n].
    { inversion LC. auto. }
    apply inleft. eexists.
    { inversion LC. eauto. }
    apply inright. intros T h; inversion h; subst; unfold not in n; eauto.
  - destruct IHa as [[T h0]|n].
    { inversion LC. eauto. }
    apply inleft. exists T.
    { inversion LC. eauto. }
    apply inright. intros T h; inversion h; subst; unfold not in n; eauto.
Qed.

Lemma Value_AbsIrrel_inversion : forall A a,
    Value (a_Abs Irrel A a)
    -> lc_tm A /\ forall x, x `notin` fv_tm a -> CoercedValue (open_tm_wrt_tm a (a_Var_f x)).
Proof.
  intros. inversion H. split. auto.
  intros x Fr.
  pick fresh y.
  rewrite (tm_subst_tm_tm_intro y); eauto.
  eapply CoercedValue_tm_subst_tm_tm; auto.
Qed.

Lemma Value_UAbsIrrel_inversion : forall a,
    Value (a_UAbs Irrel a)
    -> forall x, x `notin` fv_tm a -> Value (open_tm_wrt_tm a (a_Var_f x)).
Proof.
  intros. inversion H.
  pick fresh y.
  rewrite (tm_subst_tm_tm_intro y); eauto.
  eapply Value_tm_subst_tm_tm; auto.
Qed.

Ltac eauto_lc :=
  eauto using lc_tm_of_lc_set_tm,
  lc_co_of_lc_set_co,
  lc_constraint_of_lc_set_constraint.


Lemma decide_Value_mutual : forall a, lc_set_tm a -> ({ Value a } + { not (Value a) }) * ({ CoercedValue a } + { not (CoercedValue a) }).
Proof.
  intros a LC; induction LC.
  all: try destruct rho1.
  all: split; subst.

  all: try solve [apply left; econstructor; eauto_lc].
  all: try solve [apply right; move => h; inversion h;
           try inversion H].

  (* application cases *)
  all: try solve [try destruct IHLC as [[V|NV] [C|NC]];
                  try destruct IHLC1 as [[V|NV] [C|NC]];
                  try destruct (@Path_dec a1) as [[T P]|NP]; eauto_lc;
                  try solve [apply left; econstructor; eauto_lc];
                  try solve [apply right; move => h; inversion h;
                             try inversion H; unfold not in NP; eauto];
                  try solve [apply right; move => h; inversion h;
                             try inversion H; try done]].

  (* Only binding cases left *)
  all: pick fresh x; destruct (H x) as [[V |NV] [C | NC]].
  all: try solve [apply left; try apply CV; eapply (@Value_AbsIrrel_exists x);
                  eauto_lc].
  all: try solve [apply left; try apply CV; eapply (@Value_UAbsIrrel_exists x);
                  eauto_lc].

  all: try solve [apply right; move => h;
                  destruct (Value_AbsIrrel_inversion h) as [? ?];
                  apply NC; eauto].
  all: try solve [apply right; move => h; inversion h;
                  destruct (Value_AbsIrrel_inversion H0) as [? ?];
                  apply NC; eauto].
  all: try solve [apply right; move => h;
                  eapply Value_UAbsIrrel_inversion with (x:=x) in h; auto].
  all: try solve [apply right; move => h; inversion h;
                  eapply Value_UAbsIrrel_inversion with (x:=x) in H0; auto].
Qed.

Lemma Value_dec :  forall a, lc_tm a -> ({ Value a } + { not (Value a) }).
Proof.
  intros.
  apply decide_Value_mutual.
  apply lc_set_tm_of_lc_tm.
  auto.
Qed.

Lemma DataTy_Star_dec : forall A, lc_set_tm A -> { DataTy A a_Star } + { not (DataTy A a_Star) }.
Proof.
  intros A LC.
  induction LC.
  all: try solve [apply right; move => h; inversion h].
  all: try solve [apply left; eauto].
  + pick fresh x.
    move: (H x) => [D | ND].
    - left. pick fresh y and apply DT_Pi; eauto_lc.
      rewrite (tm_subst_tm_tm_intro x); auto.
      eapply DataTy_tm_subst_tm_tm; eauto_lc.
    - right. move => h; inversion h; subst.
      eapply ND.
      pick fresh y.
      rewrite (tm_subst_tm_tm_intro y); auto.
      eapply DataTy_tm_subst_tm_tm; eauto_lc.
  + pick fresh x.
    move: (H x) => [D | ND].
    - left. pick fresh y and apply DT_CPi; eauto_lc.
      rewrite (co_subst_co_tm_intro x); auto.
      eapply DataTy_co_subst_co_tm; eauto_lc.
    - right. move => h; inversion h; subst.
      eapply ND.
      pick fresh y.
      rewrite (co_subst_co_tm_intro y); auto.
      eapply DataTy_co_subst_co_tm; eauto_lc.
Qed.

Lemma binds_dec_ax : forall x G, {A, B | binds x (Ax A B) G} + {(forall A B, ¬ binds x (Ax A B) G)}.
Proof.
  intros x G.
  induction G.
  - eapply inright.
    intros A B I. inversion I.
  - destruct IHG.
    { eapply inleft.
    destruct s. exists x0 y. destruct a. auto. }
    { destruct a.
    destruct (x == a). subst.
    destruct s.

    eapply inright. intros A0 B H.
    apply binds_cons_1 in H. destruct H as [ [h0 h1]|b0].
    inversion h1. apply n in b0. done.

    eapply inleft. exists a0 A. auto.

    eapply inright. intros A0 B H.
    apply binds_cons_1 in H. destruct H as [ [h0 h1]|b0].
    done. apply n in b0. done.
    }
Qed.


Definition rho_eq_dec : forall rho rho' : relflag, {rho = rho'} + {rho <> rho'}.
Proof. decide equality. Defined.


Lemma beta_dec : forall a1 a2, lc_tm a1 -> {Beta a1 a2} + {¬ Beta a1 a2}.
Proof.
  intros a1 a2 LC1.
  destruct a1.
  all: try solve [right; move=> h; inversion h].
  { destruct a1_1.
    all: try solve [right; move=> h; inversion h].
    destruct (rho_eq_dec rho0 rho).
    destruct (tm_eq_dec a2 (open_tm_wrt_tm a1_1 a1_2)).
    destruct (@Value_dec (a_UAbs rho0 a1_1)).
    { inversion LC1. auto. }
    { destruct rho. subst. left.
      eapply Beta_AppAbs; eauto; inversion LC1; auto.
      subst.
      destruct a1_2;
        try solve [right; move => h; inversion h].
      left. eapply Beta_AppAbsIrrel; eauto. }
    { right. move => h. inversion h. subst. ok. ok. }
    { right; move => h; inversion h. subst. ok. ok. }
    { right; move => h; inversion h. subst. ok. ok. }

  }
  {
    move: uniq_toplevel => h0.
    destruct (binds_lookup _ F toplevel) as [ [ss b] | h1].
    destruct ss.
    { right; move=>h; inversion h.
      apply (binds_unique _ _ _ _ _ b H0) in h0. inversion h0. }
    destruct (tm_eq_dec a2 a).
    { subst. left. eauto. }
    { right; move=>h; inversion h.
      apply (binds_unique _ _ _ _ _ b H0) in h0. inversion h0. ok. }
    { right; move=>h; inversion h.
      unfold not in h1. eapply h1. eauto.
    }
  }
  {
    destruct a1.
    all: try solve [right; move=> h; inversion h].
    destruct (co_eq_dec g g_Triv).
    destruct (tm_eq_dec a2 (open_tm_wrt_co a1 g_Triv)).
    { subst. left. eapply Beta_CAppCAbs. inversion LC1. auto. }
    { right; move=>h; inversion h. ok. }
    { right; move=>h; inversion h. ok. }
  }
Qed.

Unset Implicit Arguments.

Program Fixpoint RhoCheck_erase_dec rho x a (_ : lc_tm a) : {RhoCheck rho x (erase_tm a)} + {¬ RhoCheck rho x (erase_tm a)} :=
  let a' := erase a in
  match rho with
    | Rel => yeah
    | Irrel =>  not_in_dec x (fv_tm_tm_tm a') >--> yeah
  end.

Next Obligation.
  clear Heq_anonymous.
  subst.
  inversion 1.
  ok.
Defined.



End fc_dec_aux.
