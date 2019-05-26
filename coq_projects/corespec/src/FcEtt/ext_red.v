Require Import FcEtt.sigs.
Require Import FcEtt.imports.
Require Import FcEtt.ett_ott.

Require Import FcEtt.ett_inf.
Require Import FcEtt.ett_par.

Require Import FcEtt.ett_ind.

Require Import FcEtt.ext_wf.

Require Import FcEtt.ext_red_one.

Require Import FcEtt.tactics.


Module ext_red (invert : ext_invert_sig).

  Export invert.

Module red_one := ext_red_one invert.
Export red_one.


Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Lemma Beta_preservation : forall a b, Beta a b -> forall G A, Typing G a A -> Typing G b A.
Proof.
  intros a b B. destruct B; intros G A0 TH.
  - have CT: Ctx G by eauto.
    have RA: Typing G A0 a_Star by eauto using Typing_regularity.

     destruct (invert_a_App_Rel TH) as (A & B & TB & Tb & DE).
      destruct (invert_a_UAbs TB) as (A1 & B1 & DE2 & [L TB1] & TA1).
      eapply E_Conv with (A := (open_tm_wrt_tm B1 b)); eauto 2.
      pick fresh x.
      move: (TB1 x ltac:(auto)) =>  [T1 [T2 RC]].
      rewrite (tm_subst_tm_tm_intro x v); eauto.
      rewrite (tm_subst_tm_tm_intro x B1); eauto.
      eapply Typing_tm_subst with (A:=A1); eauto 2.
      eapply E_Conv with (A := A); eauto 2 using E_PiFst.
      eapply E_Trans with (a1:= open_tm_wrt_tm B b); eauto using E_PiSnd, E_Refl, E_Sym.
  - have CT: Ctx G by eauto.
    have RA: Typing G A0 a_Star by eauto using Typing_regularity.
    destruct (invert_a_App_Irrel TH) as (A & B & b0 & Tb & Tb2 & DE).
      destruct (invert_a_UAbs Tb) as (A1 & B1 & DE2 & [L TB1] & TA1).
      eapply E_Conv with (A := (open_tm_wrt_tm B1 b0)); eauto 2.
      pick fresh x.
      move: (TB1 x ltac:(auto)) =>  [T1 [T2 RC]].
      inversion RC. subst.
      rewrite (tm_subst_tm_tm_intro x v); eauto.
      rewrite (tm_subst_tm_tm_intro x B1); eauto.
      rewrite (tm_subst_tm_tm_fresh_eq _ _ _ H0).
      rewrite - (tm_subst_tm_tm_fresh_eq _ b0 x H0).
      eapply Typing_tm_subst with (A:=A1); eauto 2.
      eapply E_Conv with (A:=A); eauto using E_PiFst.
      eapply E_Sym.
      eapply E_Trans with (a1 := open_tm_wrt_tm B b0). auto.
      eapply E_PiSnd; eauto using E_Refl.
   - have CT: Ctx G by eauto.
     have RA: Typing G A0 a_Star by eauto using Typing_regularity.
     destruct (invert_a_CApp TH) as (eq & a1 & b1 & A1 & B1 & h0 & h1 & h2).
     destruct (invert_a_UCAbs h0) as (a2 & b2 & A2 & B2 & h3 & h4 & [L h5]).
     pick fresh c.
     move: (h5 c ltac:(auto)) => [T1 T2].
     have? : DefEq G (dom G) a2 b2 A2. eauto using E_CPiFst, E_Cast.

     eapply E_Conv with (A:= (open_tm_wrt_co B2 g_Triv)); eauto 2.
     rewrite (co_subst_co_tm_intro c a'); eauto.
     rewrite (co_subst_co_tm_intro c B2); eauto.
     eapply Typing_co_subst; eauto.
     eapply E_Sym.
     eapply E_Trans with (a1 := open_tm_wrt_co B1 g_Triv). auto.
     eapply E_CPiSnd; eauto 2.
   - destruct (invert_a_Fam TH) as (b & B & h0 & h1 & h2).
     assert (Ax a A = Ax b B). eapply binds_unique; eauto using uniq_toplevel.
     inversion H0. subst.
     eapply E_Conv with (A := B).
     eapply toplevel_closed in h1.
     eapply Typing_weakening with (F:=nil)(G:=nil)(E:=G) in h1.
     simpl_env in h1.
     auto. auto. simpl_env.
     eauto.
     eapply E_Sym. eauto.
     move: (DefEq_regularity h0) => h3.
     inversion h3.
     auto.
Qed.

Lemma E_Beta2 :  ∀ (G : context) (D : available_props) (a1 a2 B : tm),
       Typing G a1 B → Beta a1 a2 → DefEq G D a1 a2 B.
Proof.
  intros; eapply E_Beta; eauto.
  eapply Beta_preservation; eauto.
Qed.

(*
Lemma Par_fv_preservation: forall G D x a b, Par G D a b ->
                                        x `notin` fv_tm_tm_tm a ->
                                        x `notin` fv_tm_tm_tm b.
Proof.
  intros.
  induction H; eauto 2; simpl.
  all: simpl in H0.
  all: try solve [move => h0; apply AtomSetFacts.union_iff in h0; case: h0 => h0; eauto; apply IHreduction_in_one; auto].
  all: try auto.
  - simpl in *.
    have: x `notin` fv_tm_tm_tm (open_tm_wrt_tm a' b') => h0.
    apply fv_tm_tm_tm_open_tm_wrt_tm_upper in h0.
    apply AtomSetFacts.union_iff in h0.
    case:h0; eauto => h0.
    fsetdec_fast.
    fsetdec_fast.
    auto.
  - rewrite fv_tm_tm_tm_open_tm_wrt_tm_upper.
    fsetdec.
  - have: x `notin` fv_tm_tm_tm (open_tm_wrt_co a' g_Triv) => h0.
    apply fv_tm_tm_tm_open_tm_wrt_co_upper in h0.
    apply AtomSetFacts.union_iff in h0.
    case:h0; eauto => h0.
    fsetdec.
    auto.
  - pick fresh x0.
    assert (Fl : x0 `notin` L). auto.
    assert (Fa : x `notin` fv_tm_tm_tm (open_tm_wrt_tm a (a_Var_f x0))).
    rewrite fv_tm_tm_tm_open_tm_wrt_tm_upper. auto.
    move: (H1 x0 Fl Fa) => h0.
    rewrite fv_tm_tm_tm_open_tm_wrt_tm_lower. eauto. 
  - pick fresh x0.
    have na': x `notin` fv_tm_tm_tm A'. eauto.
    have nb: x `notin` fv_tm_tm_tm (open_tm_wrt_tm B (a_Var_f x0)).
    rewrite fv_tm_tm_tm_open_tm_wrt_tm_upper. eauto.
    have nob': x `notin` fv_tm_tm_tm (open_tm_wrt_tm B' (a_Var_f x0)). eauto.
    have nb': x `notin` fv_tm_tm_tm B'.
    rewrite fv_tm_tm_tm_open_tm_wrt_tm_lower. eauto.
    eauto.
  - pick_fresh c0.
    have: x `notin` fv_tm_tm_tm (open_tm_wrt_co a (g_Var_f c0)) => h0.
    apply fv_tm_tm_tm_open_tm_wrt_co_upper in h0.
    apply AtomSetFacts.union_iff in h0.
    case:h0; eauto => h0.
    simpl in h0.
    fsetdec.
    have K:= H1 c0 ltac:(auto) h0.
    move => h1.
    apply K. auto.
    apply fv_tm_tm_tm_open_tm_wrt_co_lower; auto.
  - pick fresh c0 for L.
    have: x `notin` fv_tm_tm_tm (open_tm_wrt_co a (g_Var_f c0)) => h0.
    apply fv_tm_tm_tm_open_tm_wrt_co_upper in h0.
    apply AtomSetFacts.union_iff in h0.
    case:h0; eauto => h0.
    simpl in h0.
    fsetdec.
    have h2: x `notin` fv_tm_tm_tm (open_tm_wrt_co a' (g_Var_f c0)). eauto.
    move: (fv_tm_tm_tm_open_tm_wrt_co_lower a' (g_Var_f c0)) => h3.
    have h4: x `notin` fv_tm_tm_tm a'. fsetdec.

    move => h1.
    apply AtomSetFacts.union_iff in h1.
    case: h1 => h1; eauto.
    apply AtomSetFacts.union_iff in h1.
    case: h1 => h1; eauto.
    fsetdec.
    fsetdec.
  - apply toplevel_closed in H.
    move: (Typing_context_fv H) => ?. split_hyp.
    simpl in *.
    fsetdec.
  -
    apply IHPar.
    pick fresh y.
    move: (H1 y ltac:(auto)) => h0.
    apply (fun_cong fv_tm_tm_tm) in h0.
    simpl in h0.
    move: (@fv_tm_tm_tm_open_tm_wrt_tm_lower a (a_Var_f y) x) => h1.
    move: (@fv_tm_tm_tm_open_tm_wrt_tm_upper a (a_Var_f y) x) => h2.
    unfold not. intro IN.
    assert (h3: x `in` (union (fv_tm_tm_tm b) (singleton y))). auto.
    rewrite -h0 in h3.
    apply h2 in h3.
    simpl in h3.
    destruct (AtomSetImpl.union_1 h3).
    assert (x `notin` singleton y). auto. done.
    done.
  - apply IHPar.
    pick fresh y.
    move: (H1 y ltac:(auto)) => h0.
    apply (fun_cong fv_tm_tm_tm) in h0.
    simpl in h0.
    move: (@fv_tm_tm_tm_open_tm_wrt_tm_lower a (a_Var_f y) x) => h1.
    move: (@fv_tm_tm_tm_open_tm_wrt_tm_upper a (a_Var_f y) x) => h2.
    unfold not. intro IN.
    assert (h3: x `in` (union (fv_tm_tm_tm b) empty)). auto.
    rewrite -h0 in h3.
    apply h2 in h3.
    simpl in h3.
    destruct (AtomSetImpl.union_1 h3).
    assert (x `notin` singleton y). auto. done.
    done.
  - apply IHPar.
    pick fresh y.
    move: (H1 y ltac:(auto)) => h0.
    apply (fun_cong fv_tm_tm_tm) in h0.
    simpl in h0.
    move: (@fv_tm_tm_tm_open_tm_wrt_co_lower a (g_Var_f y) x) => h1.
    move: (@fv_tm_tm_tm_open_tm_wrt_co_upper a (g_Var_f y) x) => h2.
    unfold not. intro IN.
    assert (h3: x `in` (union (fv_tm_tm_tm b) empty)). auto.
    rewrite -h0 in h3.
    apply h2 in h3.
    simpl in h3.
    destruct H0. 
    apply AtomSetProperties.empty_union_1 in h3.
    auto. done.
Qed.
*)

Lemma reduction_in_Par : forall a a', reduction_in_one a a' -> forall G D, Par G D a a'.
Proof.
  induction 1; intros; try eauto using Value_lc.
Qed.




(*
See: reduction_in_one_lc in ext_red_one.

Lemma reduction_lc : forall a a', reduction_in_one a a' -> lc_tm a -> lc_tm a'.
*)


Lemma reduction_in_one_fv_preservation: forall x a b, reduction_in_one a b ->
                                        x `notin` fv_tm_tm_tm a ->
                                        x `notin` fv_tm_tm_tm b.
Proof.
  intros.
  eapply Par_fv_preservation; eauto.
  eapply reduction_in_Par; eauto.
  Unshelve. exact nil. exact {}.
Qed.

Lemma reduction_rhocheck : forall a a' rho x, reduction_in_one a a' -> RhoCheck rho x a -> RhoCheck rho x a'.
Proof.
  move=> a a' [] x Red RC.
  - inversion RC.  eauto using reduction_in_one_lc.
  - inversion RC.  eauto using reduction_in_one_fv_preservation.
Qed.

Lemma reduction_preservation : forall a a', reduction_in_one a a' -> forall G A, Typing G a A -> Typing G a' A.
Proof.
  (* TODO: clean and make more robust *)
  move=> a a' r.
  induction r.
  all: move=> G A_ tpga.
  - depind tpga; try eauto.
    + eapply E_Abs with (L := L `union` L0); try eassumption.
      all: move=> x xLL0.
      all: autofresh_fixed x.
      all: eauto using reduction_rhocheck.
  - depind tpga; subst; eauto.
  - depind tpga; subst; eauto.
  - depind tpga; subst; eauto.
  - apply invert_a_App_Rel in tpga.
      pcess_hyps.
      apply invert_a_UAbs in H1. pcess_hyps.
      autofresh. pcess_hyps.
      move: (E_PiFst _ _ _ _ _ _ _ H1) => xx1.
      eapply E_Conv; try eapply (E_Sym _ _ _ _ _ H3).
      rewrite  (tm_subst_tm_tm_intro x4); try fsetdec_fast.
      rewrite (tm_subst_tm_tm_intro x4 x0); try fsetdec_fast.
      eapply Typing_tm_subst.
      have x4_refl : DefEq ([(x4, Tm x1)] ++ G) (dom G) (a_Var_f x4) (a_Var_f x4) x.
      {
        eapply E_Refl; eapply E_Conv.
        - eauto.
        - eapply E_Sym in xx1.
          eapply DefEq_weaken_available.
          rewrite <- (app_nil_l [(x4, Tm x1)]).
          rewrite app_assoc.
          eapply DefEq_weakening; try reflexivity.
          + rewrite app_nil_l. eassumption.
          + simpl. eauto.
        - apply DefEq_regularity in xx1.
          apply PropWff_regularity in xx1.
          destruct xx1.
          rewrite <- (app_nil_l [(x4, Tm x1)]).
          rewrite app_assoc.
          eapply Typing_weakening; eauto.
      }
      have x4G: (Ctx (nil ++ [(x4, Tm x1)] ++ G)) by eauto.
      move: (DefEq_weakening H1 [(x4, Tm x1)] nil G eq_refl x4G) => H1w.
      rewrite app_nil_l in H1w.
      move: (E_PiSnd _ _ _ _ _ _ _ _ _ H1w x4_refl) => x0x2.
      eapply E_Conv.
      * eapply H4.
      * eapply DefEq_weaken_available.
        eapply (E_Sym _ _ _ _ _ x0x2).
      * apply DefEq_regularity in x0x2. by inversion x0x2.
      * eauto.
      * (* TODO: autoreg. *)
        apply DefEq_regularity in H3.
        by inversion H3.

  - apply invert_a_App_Irrel in tpga.
      pcess_hyps.
      apply invert_a_UAbs in H0; pcess_hyps.
      autofresh. pcess_hyps.
      move: (E_PiFst _ _ _ _ _ _ _ H0) => xx2.
      eapply E_Conv; try eapply (E_Sym _ _ _ _ _ H3).
      rewrite  (tm_subst_tm_tm_intro x5); try fsetdec_fast.
      rewrite tm_subst_tm_tm_fresh_eq; try done.
      rewrite -(tm_subst_tm_tm_fresh_eq (open_tm_wrt_tm v (a_Var_f x5)) x1 x5); try done.
      (*rewrite (tm_subst_tm_tm_intro x5); try fsetdec_fast.*)
      eapply Typing_tm_subst.
      have x5_refl : DefEq ([(x5, Tm x2)] ++ G) (dom G) (a_Var_f x5) (a_Var_f x5) x.
      {
        eapply E_Refl; eapply E_Conv.
        - eauto.
        - eapply E_Sym in xx2.
          eapply DefEq_weaken_available.
          rewrite <- (app_nil_l [(x5, Tm x2)]).
          rewrite app_assoc.
          eapply DefEq_weakening; try reflexivity.
          + rewrite app_nil_l. eassumption.
          + simpl. eauto.
        - apply DefEq_regularity in xx2.
          apply PropWff_regularity in xx2.
          destruct xx2.
          rewrite <- (app_nil_l [(x5, Tm x2)]).
          rewrite app_assoc.
          eapply Typing_weakening; eauto.
      }
      have x5G: (Ctx (nil ++ [(x5, Tm x2)] ++ G)) by eauto.
      move: (DefEq_weakening H0 [(x5, Tm x2)] nil G eq_refl x5G) => H1w.
      rewrite app_nil_l in H1w.
      move: (E_PiSnd _ _ _ _ _ _ _ _ _ H1w x5_refl) => x0x3.
      eapply E_Conv.
      * eassumption. 
      * eapply DefEq_weaken_available.
        eapply (E_Sym _ _ _ _ _ x0x3).
      * apply DefEq_regularity in x0x3. by inversion x0x3.
      * eauto.
      * (* TODO: autoreg. *) inversion H6. assumption.
      * inversion H6. assumption.
      * erewrite <- tm_subst_tm_tm_intro. eauto. fsetdec.
      * apply DefEq_regularity in H2. by inversion H2.
  - apply invert_a_CApp in tpga; pcess_hyps.
    apply invert_a_UCAbs in H1; pcess_hyps.
    eapply E_Conv; try eapply (E_Sym _ _ _ _ _ H2). (* TODO: declare E_Sym's (and others') arguments implicit *)
    autofresh; pcess_hyps.
    move: (E_CPiFst _ _ _ _ _ _ H1) => iso.
    move: (E_Cast _ _ _ _ _ _ _ _ H2 iso) => x34.
    move: (E_CPiSnd _ _ _ _ _ _ _ _ _ _ H1 H2 x34) => x26.
    eapply E_Conv; try eapply (E_Sym _ _ _ _ _ x26). 
    all: try (apply DefEq_regularity in H3; inversion H3; done).
    rewrite  (co_subst_co_tm_intro x8); try fsetdec_fast.
    rewrite (co_subst_co_tm_intro x8 x6); try fsetdec_fast.
    eapply Typing_co_subst.
    all: eauto. 
  - apply invert_a_Fam in tpga; pcess_hyps.
    move: (binds_unique _ _ _ _ _ H H1 uniq_toplevel). inversion 1. subst x0 x.
    apply toplevel_closed in H.
    eapply E_Sym in H0.
    move: (DefEq_regularity H0) => reg; inversion reg.
    eapply Typing_Ctx in H7.
    eapply E_Conv; eauto.
    move: (Typing_weakening H G nil nil eq_refl).
    rewrite app_nil_l app_nil_r.
    by apply.
Qed.

(* ---- helper tactics for lemma below. -------------- *)

(* Convert a goal of the form  Par (XX ++ G) dom(XX ++ G) a b ==> Par G D a b *)
Ltac par_with_context_tail :=
  match goal with
  | _ : _ |- Par ([?s] ++ ?G ) (dom ([?s] ++ ?G)) ?a ?b =>
    eapply context_Par_irrelevance with (G1 := G) (D1 := dom G); eauto
  end.

Ltac ind_hyp a k1 k2 :=
  match goal with
    [ H : ∀ a' : tm, Ctx ?G → Par ?G ?D a a' → Typing ?G a' ?A ∧ DefEq ?G empty a a' ?A,
        H1 : Par ?G ?D a ?a',
        H2 : Ctx ?G |- _ ] =>
    move: (@H a' H2 H1) => [k1 k2]


  end.

Ltac ind_hyp_open x B k1 k2 :=
  match goal with
    [ H : forall x, x `notin` ?L -> forall a', Ctx ([(x, ?s)] ++ ?G) -> Par ([(x, ?s)] ++ ?G) ?D (open_tm_wrt_tm B (a_Var_f x)) a' -> ?P,
        H1 : Ctx ?G,
        H10 :  forall x : atom, x `notin` ?L0 → Par ?G ?D0 (open_tm_wrt_tm B (a_Var_f x)) (open_tm_wrt_tm ?B' (a_Var_f x))
                          |- _ ] =>
    move: (H x ltac:(auto) (open_tm_wrt_tm B' (a_Var_f x)) ltac:(auto)
                (context_Par_irrelevance ([(x, s)] ++ G) (dom ([(x,s)] ++ G)) (H10 x ltac:(auto)))) => [k0 k1]
      end.


(*

This lemma is not true in the presence of Eta-reduction in Par.
Instead, we should prove preservation for the head_reduction relation that
does not include eta.


(* Extend to D insteadn of just dom G??? *)
Lemma type_reduction_mutual:
  (forall G a A,     Typing G a A    ->
                forall a', Ctx G -> Par G (dom G) a a'-> Typing G a' A /\ DefEq G empty a a' A) /\
  (forall G phi,     PropWff G phi   -> forall A B T, Ctx G -> phi = Eq A B T ->
                                       (forall A' B' T', Par G (dom G) A A' -> Par G (dom G) B B' -> Par G (dom G) T T' ->
                                                    PropWff G (Eq A' B' T') /\ Iso G empty phi (Eq A' B' T'))) /\
  (forall G D p1 p2, Iso G D p1 p2   -> True) /\
  (forall G D A B T, DefEq G D A B T -> True) /\
  (forall G1,        Ctx G1 -> True).
*)



End  ext_red.
