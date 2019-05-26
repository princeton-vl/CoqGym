Require Import FcEtt.sigs.

Require Export FcEtt.tactics.
Require Export FcEtt.imports.
Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_ind.
Require Export FcEtt.ext_wf.
Require Export FcEtt.ett_par.
Require Export FcEtt.ett_inf_cs.

Require Import FcEtt.erase_syntax.
Require Import FcEtt.fc_invert.
Require Import FcEtt.ext_consist.
Require Import FcEtt.erase.
Require Import FcEtt.fc_head_reduction.

(* Needed for annotation lemma at end. *)
Require Import FcEtt.fc_preservation.
Require Import FcEtt.ext_subst.

Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".


Module fc_consist (wf : fc_wf_sig) (weak : fc_weak_sig) (subst : fc_subst_sig)
                  (e_invert : ext_invert_sig)(e_subst : ext_subst_sig).

Import wf weak.

Export subst.


Module invert := fc_invert wf weak subst.
Export invert.


Module consist := ext_consist e_invert wf.
Export consist.


Module erase' := erase wf weak subst e_invert.
Export erase'.


Module head := fc_head_reduction  e_invert weak wf subst.
Export head.

Module pres := fc_preservation wf weak subst e_subst.
Import pres.
(* Why does this cause so many messages? *)


Lemma erased_tm_erase_mutual :
  (forall G0 a B (H : AnnTyping G0 a B),
     erased_tm (erase a) /\ erased_tm (erase B)) /\
  (forall G0 phi (H : AnnPropWff G0 phi),
      forall a b A, phi = (Eq a b A) ->
                                         erased_tm (erase a) /\ erased_tm (erase b)
                                         /\ erased_tm (erase A)) /\
  (forall G0 D g p1 p2 (H : AnnIso G0 D g p1 p2),
     True) /\
  (forall  G0 D g A B (H : AnnDefEq G0 D g A B),
      True) /\
  (forall G0 (H : AnnCtx G0),
     forall x A, binds x (Tm A) G0 -> erased_tm (erase_tm A)
  ).
Proof.
 apply ann_typing_wff_iso_defeq_mutual; intros; simpl; repeat split; eauto.
 all: try solve [inversion H; eauto].
 all: try solve [inversion H1; eauto].
 all: try solve [inversion H0; eauto].
   (* all: try solve [ try (destruct rho); simpl; eauto]. *)
  - (* a_Pi rho *)
    erased_pick_fresh y. inversion H0. eauto using lc_erase.
    move: (H y) => h0. assert (W: y `notin` L). eauto.
    apply h0 in W. inversion W. rewrite <- open_tm_erase_tm in H1. eauto.
  - (* a_UAbs rho *)
    destruct rho; eauto. 
    (* rel *)
    pick fresh x and apply erased_a_Abs. 
    replace (a_Var_f x) with (erase (a_Var_f x)); eauto.
    rewrite open_tm_erase_tm. assert (W: x `notin` L). auto. apply H0 in W.
    inversion W. auto. auto.
    (*irrel*)
    pick fresh x and apply erased_a_Abs.
    replace (a_Var_f x) with (erase (a_Var_f x)); eauto.
    rewrite open_tm_erase_tm. assert (W: x `notin` L). auto. apply H0 in W.
    inversion W. auto.
    econstructor.
    assert (W: x `notin` L). auto.
    apply r in W. inversion W. simpl. 
    rewrite Rew.r_erase_tm.
    rewrite Rew.r_erase_tm in H1. rewrite -open_tm_erase_tm in H1.
    simpl in H1. auto.
  - (* a_Pi type *)
    erased_pick_fresh y. inversion H. eauto using lc_erase.
    move: (H0 y) => h0. assert (W: y `notin` L). eauto.
    apply h0 in W. inversion W. clear h0 W. 
    rewrite <- open_tm_erase_tm in H2. eauto.
  - inversion H. inversion H0. destruct rho; simpl; eauto.
  - rewrite <- open_tm_erase_tm.
    set M := erase_tm B.
    inversion H. inversion H2; subst.
    pick fresh x.
    unfold M in Fr.
    rewrite (tm_subst_tm_tm_intro x); eauto.
    eapply subst_tm_erased. inversion H0. auto.
    eapply H7. fsetdec.
  - (* a_CPi erase constraint *)
    destruct phi. destruct (H _ _ _ eq_refl) as (h0 & h1 & h2). simpl.
    eauto. erased_pick_fresh y; eauto using lc_erase.
    assert (W: y `notin` L). auto. apply H0 in W.
    rewrite Rew.r_erase_tm.
    erewrite open_co_erase_tm2. inversion W. apply H1.
  - (* a_UCAbs *)
    pick fresh y and apply erased_a_CAbs.
    assert (W: y `notin` L). auto. apply H0 in W.
    rewrite Rew.r_erase_tm.
    erewrite open_co_erase_tm2. inversion W. apply H1.
  - (* a_CPi type *)
    destruct phi. destruct (H _ _ _ eq_refl) as (h0 & h1 & h2). simpl.
    eauto. erased_pick_fresh y; eauto using lc_erase.
    assert (W: y `notin` L). auto. apply H0 in W.
    rewrite Rew.r_erase_tm.
    erewrite open_co_erase_tm2. inversion W. apply H2.
  - rewrite <- open_co_erase_tm.
    set M := erase_tm B.
    inversion H. inversion H2; subst.
    pick fresh x.
    unfold M in Fr.
    assert (W: x `notin` L). fsetdec. apply H10 in W.
    erewrite open_co_erase_tm with (a := (g_Var_f x)).
    erewrite open_co_erase_tm2 in W. apply W.
  - inversion H1. subst. inversion H. auto.
  - inversion H1. subst. inversion H0. auto.
  - inversion H1. subst. inversion H. auto.
  - simpl in H1.
    apply binds_cons_iff in H1.
    inversion H1. inversion H2.
    + inversion H4; subst; auto.
      inversion H0; auto.
    + apply H in H2; auto.
  - simpl in H1.
    apply binds_cons_iff in H1.
    inversion H1. destruct phi.
    inversion H2. inversion H4. 
    apply H in H2; auto.
Qed.

Lemma erased_tm_erase : forall G0 a B, AnnTyping G0 a B -> erased_tm (erase a).
Proof.
  intros.
  destruct erased_tm_erase_mutual.
  apply H0 in H. inversion H. auto.
Qed.

Lemma erased_tm_erase_type : forall G0 a B, AnnTyping G0 a B -> erased_tm (erase B).
Proof.
  intros.
  destruct erased_tm_erase_mutual.
  apply H0 in H. inversion H. auto.
Qed.

Hint Resolve erased_tm_erase : erased.


Definition AnnGood G D := Good (erase_context G) D.

Lemma AnnGoodIsGood : forall G D, AnnGood G D -> Good (erase_context G) D.
Proof. intros. auto.
Qed.

Lemma AnnGoodnil : AnnGood nil AtomSetImpl.empty.
  unfold AnnGood. simpl. unfold Good. unfold erased_context.
  split. auto.
  intros.
  unfold binds in H. inversion H.
Qed.

Lemma AnnDefEq_consistent : forall S D g A B, AnnDefEq S D g A B -> AnnGood S D -> consistent (erase A) (erase B).
Proof.
  intros S D g A B H H0.
  pose S' := AnnGoodIsGood H0.
  destruct (AnnDefEq_regularity H) as (S1 & S2 & gs & TS1 & TS2 & ES).
  assert (DefEq (erase_context S) D (erase A) (erase B) (erase S1)).
  { apply (AnnDefEq_erase H).
    auto.
  }
  assert (C : consistent (erase A) (erase B)).
  eapply join_consistent.
  eapply consistent_defeq. eauto. eauto.
  inversion C; subst; auto.
Qed.


Lemma Paths_are_DataTy : forall T a,
    Path T a -> Value a -> forall G A, AnnTyping G a A -> DataTy A a_Star.
Proof.
  induction 1; intros.
  - inversion H0. subst.
    eapply (binds_to_type _ _ AnnSig_an_toplevel); eauto.
  - inversion H1. inversion H2. subst.
    move: (IHPath H8 _ _ H14) => h0.
    inversion h0. subst.
    pick fresh x.
    rewrite (tm_subst_tm_tm_intro x); eauto with lngen.
  - inversion H1. inversion H2. subst.
    move: (IHPath H7 _ _ H11) => h0.
    inversion h0. subst.
    pick fresh x.
    rewrite (co_subst_co_tm_intro x); eauto with lngen.
  - inversion H1.
Qed.



Lemma Paths_have_value_types : forall T a,
    Path T a -> Value a -> forall G A, AnnTyping G a A -> value_type A.
Proof. intros.
       eapply DataTy_value_type; eauto.
       eapply Paths_are_DataTy; eauto.
Qed.

Lemma values_have_value_types :
  forall G D a A, AnnGood G D ->  AnnTyping G a A -> Value a -> value_type A.
Proof.
  intros G D a A AN H V.
  move: (AnnTyping_regularity H) => h0.
  inversion H; subst; auto.
  all: try solve [inversion V; inversion H2].
  all: match goal with
  | [H : AnnTyping ?G ?b ?A |- value_type ?b] =>
    apply AnnTyping_lc in H; split_hyp; lc_inversion c;  eauto
       end.
  + inversion V.
    eapply (@Paths_have_value_types T (a_App b rho a0)); eauto.
  + inversion V.
    eapply (@Paths_have_value_types T (a_CApp a1 g)); eauto.
  + eapply DataTy_value_type.
    eapply (binds_to_type _ _ AnnSig_an_toplevel); eauto.
Qed.


(* --------- Paths infect the cannonical forms lemmas for functions --------- *)

Lemma canonical_forms_a_Pi :
  forall G D a rho A B, AnnGood G D ->
                   AnnTyping G a (a_Pi rho A B) -> Value a ->
                   (exists a', a = a_Abs rho A a') \/ (exists T, Path T a).
Proof.
  intros G D a rho A B AN H V.
  inversion V; subst; inversion H; subst; try solve [inversion H0].
  all: try solve [left; exists a0; auto].
  all: try solve [right; exists T; auto].
Qed.

Lemma canonical_forms_a_CPi :
  forall G D a phi B, AnnGood G D ->
                 AnnTyping G a (a_CPi phi B) -> Value a ->
                 (exists a', a = a_CAbs phi a') \/ (exists T, Path T a).
Proof.
  intros G D a phi B AN H V.
  inversion V; subst; inversion H; subst; try solve [inversion H0].
  all: try solve [left; exists a0; auto].
  all: try solve [right; exists T; auto].
Qed.

Lemma consistent_a_Pi :
  forall G A B C g rho,
    AnnGood G (dom G) -> value_type C ->
    AnnDefEq G (dom G) g C (a_Pi rho A B) -> exists A' B', C = a_Pi rho A' B'.
Proof.
  intros G A B C g rho AN VT DE.
  move: (AnnDefEq_consistent DE AN) => K;  simpl in K.
  inversion K.
  destruct C; destruct rho0; try destruct rho1; simpl in H; inversion H.
  - exists C1. exists C2. subst. auto.
  - subst. exists C1. exists C2. auto.
  - inversion VT.
  - inversion VT.
  - inversion H0.
  - assert False.
    apply AnnDefEq_lc in DE. split_hyp.
    match goal with
      [ H0 : ¬ value_type (a_Pi rho (erase_tm A) (erase_tm B)),
        H4 : lc_tm (a_Pi rho A B) |- _ ] =>
    apply H0; econstructor;
      pose M := H4; clearbody M; inversion M;
      eauto using lc_tm_erase;
      move: (lc_erase) => [h0 _]; apply h0 in H4; auto end.
    done.
  - subst.
    apply value_type_erase in VT. done.
Qed.

Lemma consistent_a_CPi :
  forall G phi B C g,
    AnnGood G (dom G) -> value_type C -> AnnDefEq G (dom G) g C (a_CPi phi B) -> exists phi' B', C = a_CPi phi' B'.
Proof.
  intros G phi B C g AN VT DE.
  move: (AnnDefEq_consistent DE AN) => K;  simpl in K.
  inversion K.
  destruct C; try destruct rho; simpl in H; inversion H;
  try solve [inversion VT; inversion H1].
  - subst. exists phi0. exists C.  auto.
  - inversion H0.
  - assert False.
    apply AnnDefEq_lc in DE. split_hyp.
    apply H0. econstructor.
    pose M := H4. inversion M.
    apply lc_erase. auto.
    move: (lc_erase) => [h0 _]. apply h0 in H4. apply H4.
    done.
  - subst.
    apply value_type_erase in VT. done.
Qed.


Definition irrelevant G D (a : tm) :=
  (forall x A, binds x (Tm A) G -> x `notin` fv_tm (erase a)) /\ AnnGood G D.


(* Other statement?
Lemma progress : forall a A G D, AnnGood G D -> AnnTyping G a A -> CoercedValue a \/ exists a', head_reduction G a a'.
*)
Lemma progress : forall G a A, irrelevant G (dom G) a -> AnnTyping G a A -> CoercedValue a \/ exists a', head_reduction G a a'.
Proof.
  intros G a A AN H.
  destruct AN as [IR AN].
  assert (M : AnnTyping G a A); auto.
  dependent induction H; destruct (AnnTyping_lc M) as [LCa LCA]; inversion LCa.
  - left; auto.
  - apply IR in H0. simpl in H0. fsetdec.
  - left; eauto.
  - destruct rho; try solve [left; eauto].
    pick fresh x.
    have: x `notin` L; auto => h0.
    move: (H2 x h0) => h1.
    inversion h1. subst. clear H2.
    destruct (H1 x h0) as [V | [a' R]].
    { move: (H0 x h0) => h2.
      have ctx: (AnnCtx ([(x, Tm A)] ++ G)) by eauto with ctx_wff.
      move: (AnnCtx_uniq ctx) => u. inversion u. subst.
      intros x0 A0 b0.
      apply binds_cons_uniq_1 in b0. destruct b0; split_hyp.
      ++ subst. auto.
      ++ move: (IR _ _ H2) => fr. simpl in fr.
         rewrite <- open_tm_erase_tm.
         eapply notin_sub; [idtac| eapply fv_tm_tm_tm_open_tm_wrt_tm_upper].
         simpl.
         fsetdec.
      ++ eauto. }
    { unfold AnnGood. simpl. eapply Good_add_tm_2; eauto.
      rewrite <- erase_dom. auto.
      eapply Typing_erased. eapply (AnnTyping_erase). eauto. }
    { eauto. }
    -- inversion V. subst.
       ++ left.
       econstructor.
       eapply Value_AbsIrrel_exists with (x := x); eauto.
       ++ resolve_open a.
       left. eapply CV.
       eapply Value_AbsIrrel_exists with (x:=x); eauto.
    -- right. exists (a_Abs Irrel A (close_tm_wrt_tm x a')).
       eapply An_AbsTerm_exists with (x := x).
         { eapply notin_union; auto.
           simpl. rewrite fv_tm_tm_tm_close_tm_wrt_tm. auto. }
         auto.
         rewrite open_tm_wrt_tm_close_tm_wrt_tm. auto.
  - destruct IHAnnTyping1; auto.
    + intros. move: (IR x A0 H6) => h0. destruct rho; simpl in h0. fsetdec. fsetdec.
    + inversion M. subst.
      match goal with
        H: CoercedValue b |- _ => inversion H
      end.
      -- (* application of a value *)
        edestruct canonical_forms_a_Pi as [[ a1 EQ] | [T P]] ; eauto; subst.
        (* path case solved automatically *)
        ++ right. (* a lambda, do a beta reduction *)
           exists (open_tm_wrt_tm a1 a). eapply An_AppAbs; eauto.
      -- right. (* push/pull rule *)
         subst.
         inversion H.
         subst.
         have VT: value_type A1. eapply values_have_value_types; eauto.
         edestruct consistent_a_Pi as (A' & B' & EQ); eauto. subst.
         edestruct canonical_forms_a_Pi as [[ a0' EQ] | [T P]]; eauto; subst.
    + subst.
      match goal with H : exists a' : tm, head_reduction G b a' |- _ => destruct H end.
      right. eexists. eapply An_AppLeft; eauto.
  - (* cast *)
    subst. destruct IHAnnTyping1; auto.
    inversion H2.
    + subst. left; auto.
    + subst. right. inversion H4.
      eexists.  eapply An_Combine; eauto.
    + destruct H2. right. eexists. eapply An_ConvTerm; eauto.
  - left; auto.
  - left; auto.
  - destruct IHAnnTyping; auto.
    + intros. move: (IR x A H5) => h0. simpl in h0. fsetdec.
    + inversion M. subst.
      match goal with
        H : CoercedValue ?a1 |- _ => inversion H
      end.
      -- edestruct canonical_forms_a_CPi as [[a2 EQ]|[T p]]; eauto; subst.
         right. exists (open_tm_wrt_co a2 g). eapply An_CAppCAbs; eauto.
         destruct (AnnTyping_lc H) as [h0 h1]. inversion h0; auto.
      -- subst.  inversion H. subst.
         have VT: value_type A. eapply values_have_value_types; eauto.
        edestruct consistent_a_CPi as (A' & a2 & EQ); eauto. subst.
        edestruct canonical_forms_a_CPi as [[a0' EQ]|[T p]]; eauto; subst.
    + destruct H5. right. eexists. eapply An_CAppLeft. eauto. eauto.
  - left. eauto.
  - right. exists a. eauto.
Qed.


(* ------------------------------------- *)

(* This is proved in the preservation file.
Lemma reduction_erasure : forall G a a',
    head_reduction G a a' ->
    reduction_in_one (erase a) (erase a') \/ erase a = erase a'. *)


(* ------------------------------------- *)
Inductive multi (rel : tm -> tm -> Prop) : tm -> tm -> Prop :=
| multi_refl : forall a, lc_tm a -> multi rel a a
| multi_step : forall a b c, rel a b -> multi rel b c -> multi rel a c.

Lemma multi_trans : forall r a b, multi r a b -> forall c, multi r b c -> multi r a c.
Proof.
  intros.
  dependent induction H. auto.
  eapply multi_step. eauto. auto.
Qed.

(* ------------------------------------- *)

Lemma multi_An_AbsTerm_exists : ∀ (G : list (atom * sort)) (x : atom) (A a a' : tm),
       x `notin` union (fv_tm a) (union (fv_tm a') (dom G))
       → AnnTyping G A a_Star
         → multi (head_reduction ([(x, Tm A)] ++ G)) (open_tm_wrt_tm a (a_Var_f x))
             (open_tm_wrt_tm a' (a_Var_f x))
           → multi (head_reduction G) (a_Abs Irrel A a) (a_Abs Irrel A a').
Proof.
  intros.
  dependent induction H1.
  + apply open_tm_wrt_tm_inj in x; auto.
    subst.
    eapply multi_refl; eauto using AnnTyping_lc1.
  + eapply multi_step with (b := a_Abs Irrel A (close_tm_wrt_tm x b)); eauto.
    eapply An_AbsTerm_exists with (x:=x); auto.
    autorewrite with lngen. auto.
    autorewrite with lngen. auto.
    eapply IHmulti with (x0:=x); auto.
    autorewrite with lngen. auto.
    autorewrite with lngen. auto.
Qed.

Lemma multi_An_ConvTerm : ∀ (G : context) (a : tm) (g : co) (a' : tm),
    lc_co g → multi (head_reduction G) a a'
    → multi (head_reduction G) (a_Conv a g) (a_Conv a' g).
Proof.
  intros.
  dependent induction H0.
  - eapply multi_refl; eauto.
  - eapply multi_step with (b:= (a_Conv b g)); auto.
Qed.

Lemma multi_An_AppLeft : ∀ (G : context) (a b: tm) rho (a' : tm),
    lc_tm b → multi (head_reduction G) a a'
    → multi (head_reduction G) (a_App a rho b) (a_App a' rho b).
Proof.
  intros.
  dependent induction H0.
  - eapply multi_refl; eauto.
  - eapply multi_step with (b:= (a_App b0 rho b)); auto.
Qed.

Lemma multi_An_CAppLeft : ∀ (G : context) (a: tm) (g:co) (a' : tm),
    lc_co g → multi (head_reduction G) a a'
    → multi (head_reduction G) (a_CApp a g) (a_CApp a' g).
Proof.
  intros.
  dependent induction H0.
  - eapply multi_refl; eauto.
  - eapply multi_step with (b:= (a_CApp b g)); auto.
Qed.


(* ------------------------------------- *)

Lemma multi_preservation : forall G a b A, multi (head_reduction G) a b ->
                                      AnnTyping G a A ->
                                      AnnTyping G b A.
Proof.
  induction 1.
  intros. auto.
  intros.
  eapply IHmulti.
  eapply preservation; eauto.
Qed.


(* ------------------------------------- *)

(* TODO: move elsewhere?  ext_consist for the first two? *)

Lemma erased_constraint_erase :
  forall G a b A, AnnPropWff G (Eq a b A) -> erased_tm (erase a) /\ erased_tm (erase b)
                                      /\ erased_tm (erase A).
Proof.
  move: erased_tm_erase_mutual => [_ [h [_ _]]].
  eauto.
Qed.

Lemma erased_context_erase :
  forall G, AnnCtx G -> erased_context (erase_context G).
       Proof.
         induction 1; simpl; unfold erased_context; rewrite Forall_forall.
         - intros. inversion H.
         - intros. destruct x0. inversion H2.
           -- inversion H3. destruct s. inversion H6. subst. 
              econstructor. eapply erased_tm_erase. eauto.
              inversion H6.
           -- unfold erased_context in IHAnnCtx.
              move: (Forall_forall (λ p : atom * sort, let (_, s) := p in erased_sort s) (erase_context G)) => [h0 h1].
              move: (h0 IHAnnCtx) => h2.
              eapply (h2 (a,s)). auto.
         - intros. destruct x. inversion H2.
           -- inversion H3. destruct s. inversion H6.
              inversion H6. subst.
              destruct phi.
              inversion H0.
              econstructor. 
              + eapply erased_tm_erase. eauto using AnnTyping_lc1.
              + eapply erased_tm_erase. eauto using AnnTyping_lc2.
              + eapply erased_tm_erase_type. eauto.
           -- unfold erased_context in IHAnnCtx.
              move: (Forall_forall (λ p : atom * sort, let (_, s) := p in erased_sort s) (erase_context G)) => [h0 h1].
              move: (h0 IHAnnCtx) => h2.
              eapply (h2 (a,s)). auto.
       Qed.

Lemma AnnGood_add_tm :
  forall G x A,  x `notin` dom G -> AnnTyping G A a_Star -> AnnGood G (dom G) -> AnnGood (x ~ Tm A ++ G) (dom (x ~ Tm A ++ G)).
Proof.
  intros G x A Fr AT GG.
  inversion GG.  econstructor. eapply erased_context_erase; eauto using AnnTyping_AnnCtx.
  intros.
  simpl in H1.
  apply binds_cons_1 in H1.
  destruct H1 as [[_ EQ] | BI1]. inversion EQ.
  edestruct (H0 c1) as (C & P1 & P2); eauto.
  move: (binds_In _ c1 _ _ BI1) => b0.
  unfold erase_context in b0. move: (dom_map _ _ erase_sort G) => DM. fsetdec.
  exists C. repeat split;
         eapply context_Par_irrelevance; eauto.
Qed.

(* ------------------------------------- *)

(* A specialized version of eauto that only uses the most common
   lc lemmas to cut down the search space. *)
Ltac eauto_lc := simpl; eauto using AnnTyping_lc1, Value_lc,
                        AnnDefEq_lc3, AnnPropWff_lc.


(* If an annotated term erases to a value, then it evaluates to a coerced value. *)
Lemma erased_Value_reduces_to_CoercedValue :
  forall G a0 A,
    AnnTyping G a0 A
    -> AnnGood G (dom G) -> forall a, erase a0 = a -> Value a
           -> exists av, multi (head_reduction G) a0 av /\ CoercedValue av /\ erase av = a.
Proof.
  intros G a0 A H. induction H.
  all: intros GG aa E V; simpl in E; inversion E; subst.
  all: try solve [inversion V].
  all: try solve [eexists; repeat split;
                  try eapply multi_refl; eauto_lc].
  + exists (a_Pi rho A B).
    have ?: lc_tm (a_Pi rho A B) by eauto_lc.
    repeat split; try eapply multi_refl; eauto_lc.

  + have ?: lc_tm (a_Abs rho A a) by eauto_lc.
    destruct rho.
    ++ exists (a_Abs Rel A a).
       repeat split; try eapply multi_refl; eauto_lc.
    ++ (* irrelevant abstraction case *)
      inversion V. subst.
      match goal with
        [H5 : forall x, x `notin` ?L -> Value _ |- _ ] =>
        pick_fresh y; move: (H5 y ltac:(auto)) => Va; clear H5 end.

      have EE: erase (open_tm_wrt_tm a (a_Var_f y)) = open_tm_wrt_tm (erase_tm a) (a_Var_f y)
        by simpl_erase; auto.

       have G1 : AnnGood (y ~ Tm A ++ G) (dom (y ~ Tm A ++ G)) by  eapply AnnGood_add_tm; eauto.

       match goal with
         [ H1 : ∀ x : atom, x `notin` ?L → AnnGood _ _ -> _ |- _ ] =>
         move: (H1 y ltac:(auto) G1 _ EE Va) => [av [MS [VV EV]]] end.

       exists (a_Abs Irrel A (close_tm_wrt_tm y av)).
       repeat split.
       +++ eapply multi_An_AbsTerm_exists with (x:=y);
            autorewrite with lngen; eauto.
       +++ econstructor.
           eapply Value_AbsIrrel_exists with (x:=y); autorewrite with lngen; eauto_lc.
       +++ simpl_erase. rewrite EV.
           simpl. rewrite close_tm_wrt_tm_open_tm_wrt_tm; eauto using fv_tm_erase_tm.

  + destruct rho; simpl in V; inversion V; subst;
    move: (IHAnnTyping1 GG (erase b) eq_refl ltac:(auto)) => [av [MS [CV EE]]];
    inversion CV; subst.
    ++ exists (a_App av Rel a).
       repeat split. eapply multi_An_AppLeft; eauto_lc.
       repeat econstructor; eauto_lc.
       eapply Path_to_Path; eauto_lc.
       simpl. autorewcs. congruence.
    ++ move: (multi_preservation MS H) => TC. inversion TC.
       move: (values_have_value_types GG H9 H3) => VT.
       move: (consistent_a_Pi GG VT H11) => [A' [B' EQ]]. subst.
       pose VV := H3. clearbody VV.
       eapply An_Push with (b:=a) in H3; try eapply H11; try reflexivity.
       eexists.
       split. eapply multi_trans.
       eapply multi_An_AppLeft; eauto_lc.
       eapply multi_step; eauto_lc.
       eapply multi_refl; eauto_lc.
       repeat econstructor; eauto_lc.
       split.
       eapply CC; econstructor; eauto_lc.
       econstructor; eauto_lc.
       eapply Path_to_Path; eauto_lc.
       simpl in EE. simpl. congruence.
    ++ exists (a_App av Irrel a).
       repeat split. eapply multi_An_AppLeft; eauto_lc.
       repeat econstructor; eauto_lc.
       eapply Path_to_Path; eauto_lc.
       simpl. autorewcs. congruence.
    ++ move: (multi_preservation MS H) => TC. inversion TC.
       move: (values_have_value_types GG H9 H3) => VT.
       move: (consistent_a_Pi GG VT H11) => [A' [B' EQ]]. subst.
       pose VV := H3. clearbody VV.
       eapply An_Push with (b:=a) in H3; try eapply H11; try reflexivity.
       eexists.
       split. eapply multi_trans.
       eapply multi_An_AppLeft; eauto_lc.
       eapply multi_step; eauto_lc.
       eapply multi_refl; eauto_lc.
       repeat econstructor; eauto_lc.
       split.
       eapply CC; econstructor; eauto_lc.
       econstructor; eauto_lc.
       eapply Path_to_Path; eauto_lc.
       simpl in EE. simpl. congruence.

  + move: (IHAnnTyping1 GG _ eq_refl V) => [av [MS [CV EE]]].
    inversion CV.
    ++ subst.
      exists (a_Conv av g).
      repeat split.
      eapply multi_An_ConvTerm; eauto using AnnDefEq_lc3.
      eapply CC; eauto using AnnDefEq_lc3.
      simpl. autorewcs. auto.
    ++ subst.
      have ?: lc_tm a0 by eauto using Value_lc.
      have ?: lc_co g by eauto using AnnDefEq_lc3.
      exists (a_Conv a0 (g_Trans g0 g)).
      split.
      eapply multi_trans.
      eapply multi_An_ConvTerm; eauto.
      eapply multi_step.
      eapply An_Combine; eauto.
      eapply multi_refl; eauto.
      split. eapply CC; eauto.
      simpl. simpl in EE. auto.
  + exists (a_CPi phi B).
    have ?: lc_tm (a_CPi phi B) by eapply AnnTyping_lc1; eauto.
    repeat split; try eapply multi_refl; eauto using Value_lc;
      simpl; auto.
    econstructor; eauto using AnnTyping_lc1, AnnPropWff_lc.
  + exists (a_CAbs phi a).
    have ?: lc_tm (a_CAbs phi a). eapply AnnTyping_lc1; eauto.
    repeat split; try eapply multi_refl; eauto using Value_lc;
      simpl; auto.
    econstructor; eauto using AnnTyping_lc1, AnnPropWff_lc.
  + (* CApp case (for paths) *)
    simpl in V; inversion V; subst;
    move: (IHAnnTyping GG (erase a1) eq_refl ltac:(auto)) => [av [MS [CV EE]]];
    inversion CV; subst.
    ++ exists (a_CApp av g).
       repeat split.
       eapply multi_An_CAppLeft; eauto_lc.
       repeat econstructor; eauto_lc.
       eapply Path_to_Path; eauto_lc.
       simpl. autorewcs. congruence.
    ++ move: (multi_preservation MS H) => TC. inversion TC.
       move: (values_have_value_types GG H9 H3) => VT.
       move: (consistent_a_CPi GG VT H11) => [A' [B' EQ]]. subst.
       pose VV := H3. clearbody VV.
       eapply An_CPush with (g:=g0) in H3; try eapply H11; try reflexivity.
       eexists.
       split.
       eapply multi_trans.
       eapply multi_An_CAppLeft; eauto_lc.
       eapply multi_step; eauto_lc.
       eapply multi_refl; eauto_lc.
       repeat econstructor; eauto_lc.
       split.
       eapply CC; econstructor; eauto_lc.
       eapply Path_to_Path; eauto_lc.
       simpl in EE. simpl. congruence.
Qed.


(* simple solver for irrelevant goals *)
(* TODO replace args y AA b0 h0 with "fresh" *)
Ltac solve_irrelevant y AA b0 h0 :=
  match goal with
    [ H1 : irrelevant _ _ _ |- _ ] => inversion H1 end;
  match goal with
    [ H4 : forall x A, binds x _ _ -> x `notin` _ |- _ ] =>
    simpl in H4; econstructor; eauto;
    try (intros y AA b0; move: (H4 y AA b0) => h0; fsetdec) end.


(* paths are not (erased) abstractions. *)
Lemma paths_arent_abs :
  forall a T, Path T a -> forall rho b, a = a_UAbs rho b -> False.
Proof.
  intros a T P.
  induction P; intros r b0 EQ;
    try  destruct rho; simpl in *; inversion EQ.
Qed.

Ltac no_paths:=
  match goal with
    [ EE : erase (a_App ?b0 ?rho ?a) = a_UAbs _ ?b, H : Path ?T ?b0 |- _ ] =>
    destruct rho; simpl in EE;
    match goal with
      [ FF : ?a = a_UAbs _ ?b |- _ ] =>
      have P: (Path T a); by eauto using lc_tm_erase end end.

(* Each of the subcases are by induction on a0 to account for top-level coercions on the term.
   This tactic handles all of the inductive cases. *)
Ltac induction_a0 :=
  let IR := fresh  in
  let a0' := fresh in
  let y := fresh in
  let AA := fresh in
  let b0 := fresh in
  let h0 := fresh in
  match goal with
    [ IHa0 : ∀ A0 : tm, irrelevant ?G (dom ?G) ?a0 → _,
        H1 : irrelevant ?G _ (a_Conv ?a0 ?g),
        H2 : AnnTyping ?G (a_Conv ?a0 ?g) ?A0 |- _ ] =>
    inversion H2; subst;
    (have IR: irrelevant G (dom G) a0 by solve_irrelevant y AA b0 h0);
    move: (IHa0 _ IR ltac:(eauto) ltac:(auto)) =>
    [a0' [? ?]];
    exists (a_Conv a0' g);
    split; [ eapply multi_An_ConvTerm; eauto with lc | simpl; auto ]
  end.

Lemma reduction_annotation : forall a a',
    reduction_in_one a a' ->
    forall G a0 A0, irrelevant G (dom G) a0 -> AnnTyping G a0 A0 -> erase a0 = a ->
    exists a0', multi (head_reduction G) a0 a0' /\ erase a0' = a'.
Proof.
  intros a a' H.
  induction H.
  - (* E_AbsTerm. Body of irrelevant abs takes a step. *)
    intros.
    dependent induction a0; try destruct rho; simpl in H3; inversion H3; subst.
    + inversion H2. subst.
      pick fresh x for (L \u L0 \u (fv_tm a0_2) \u dom G \u fv_tm a').
      move: (H11 x ltac:(auto)) => RC. inversion RC. subst. clear H11.
      move: (H10 x ltac:(auto)) => T2. clear H10.
      inversion H1.
      have IR: irrelevant ((x ~ Tm a0_1) ++ G) (dom (x ~ Tm a0_1 ++ G))
                       (open_tm_wrt_tm a0_2 (a_Var_f x)).
      econstructor; eauto.
      { intros x0 A0 b0.
        destruct (binds_cons_1 _ x0 x _ _ _ b0).
        + split_hyp.
          inversion H9. subst.
          autorewcshyp H4.  auto.
        + move: (binds_In _ _ _ _ H7) => h0.
          have NE: x0 <> x. fsetdec.
          move: (H5 _ _ H7) => NI. simpl in NI.
          simpl_erase.
          move: (fv_tm_tm_tm_open_tm_wrt_tm_upper (erase a0_2) (a_Var_f x)) => h1.
          simpl in h1. fsetdec.
      }
      { eapply AnnGood_add_tm; eauto. }
      have h1: erase (open_tm_wrt_tm a0_2 (a_Var_f x)) =
               open_tm_wrt_tm (erase_tm a0_2) (a_Var_f x).
      simpl_erase. auto.
      move: (H0 x ltac:(auto) _ _ _ IR T2 h1) => [a0' [ms ee]].
      exists (a_Abs Irrel a0_1 (close_tm_wrt_tm x a0')).
      split.
      eapply multi_An_AbsTerm_exists with (x:=x);
        autorewrite with lngen; auto.
      simpl_erase. rewrite ee.
      simpl. autorewrite with lngen. auto.
    + inversion H2.
    + induction_a0.
  - (* E_AppRel *) 
    intros.
    dependent induction a0; try destruct rho; simpl in H3; inversion H3; subst.
    + inversion H1. simpl in H4.
      inversion H2. subst.
      have I1: irrelevant G (dom G) a0_1.
      solve_irrelevant y AA b0 h0.
      move: (IHreduction_in_one _ _ _ I1 H11 eq_refl) => [a0_1' [MS E']].
      exists (a_App a0_1' Rel a0_2).
      split.
      eapply multi_An_AppLeft; eauto using AnnTyping_lc1.
      simpl. autorewcs. congruence.
    + induction_a0.
  - (* E_AppIrrel *) 
    intros.
    dependent induction a0; try destruct rho; simpl in H2; inversion H2; subst.
    + inversion H1. simpl in H4.
      inversion H2. subst.
      have I1: irrelevant G (dom G) a0_1.
      solve_irrelevant y AA b0 h0.
      move: (IHreduction_in_one _ _ _ I1 H8 eq_refl) => [a0_1' [MS E']].
      exists (a_App a0_1' Irrel a0_2).
      split.
      eapply multi_An_AppLeft; eauto using AnnTyping_lc1.
      simpl. autorewcs. congruence.
    + induction_a0.
  - (* E_CAppLeft. *) 
    intros.
    match goal with
      [ H2 : erase ?a0 = _ |- _ ] =>
      dependent induction a0; try destruct rho; simpl in H2; inversion H2; subst
    end.
    + induction_a0.
    + ann_invert_clear.
      have I: irrelevant G (dom G) a0. solve_irrelevant y AA b0 h0.
      match goal with
        [ H7 : AnnTyping ?G a0 ?A |- _ ] =>
        move: (IHreduction_in_one _ _ _ I H7 eq_refl) => [a0_1' [MS E']]
      end.
      exists (a_CApp a0_1' g).
      split. eapply multi_An_CAppLeft; eauto with lc.
      simpl. autorewcs. congruence.
  - (* E_AppAbs *)
    intros.
    (* Need induction on a0 for the coercions around the application. *)
    dependent induction a0; try destruct rho; simpl in H3; inversion H3; subst.
    + (* No coercions. a0 is a direct (Rel) application of
      a0_1, which erases to an abstraction. *)
      ann_invert_clear.
      inversion H1.
      have ?: Value (a_UAbs Rel v) by eauto.
      move: (erased_Value_reduces_to_CoercedValue H10 H4 H5 ltac:(auto)) =>
      [av ?]. split_hyp.
      move: (multi_preservation H6 H10) => Tav.
      (* Check if there is a coercion at the top of av *)
      match goal with [ H : CoercedValue av |- _ ] => inversion H; subst end.
      ++ (* Value av *)
         match goal with [ H10 : Value av , H9 : erase av = _ |- _ ] =>
            inversion Tav; subst; inversion H10; subst; simpl in H9; inversion H9 end.
         exists (open_tm_wrt_tm a a0_2).
         split.
         eapply multi_trans with (b:= a_App (a_Abs Rel A a) Rel a0_2).
         eapply multi_An_AppLeft; eauto_lc.
         eapply multi_step; eauto_lc.
         eapply multi_refl; eauto.
         { lc_inversion c. subst.
           pick fresh y.
           rewrite (tm_subst_tm_tm_intro y); auto.
           eapply tm_subst_tm_tm_lc_tm; eauto using AnnTyping_lc1. }
         rewrite open_tm_erase_tm. auto.
         (* prove that paths don't erase to abstractions. *)
         no_paths.
      ++ (* av = (a |> g) *)
         have LC: lc_tm a0_1 by eauto using AnnTyping_lc1.
         (* Push rule *)
         inversion H1.
         ann_invert_clear.
         match goal with
           [ H4 : AnnGood _ _,  H20 : AnnDefEq G (dom G) g A0 (a_Pi Rel A B),
             H18 : AnnTyping G a A0, H11: Value a |- _ ] =>
         move: (values_have_value_types H4 H18 H11) => VT;
         move: (consistent_a_Pi H4 VT H20) => [A' [B' EQ]]; subst;
         move: (An_Push _ _ _ _ a0_2 _ _ _ _ _ _ H11 H20 eq_refl eq_refl)=> RED end.
         have TA': AnnTyping G A' a_Star.
           { move: (AnnTyping_regularity H17) => T1. inversion T1. auto. }
         have Tb': AnnTyping G (a_Conv a0_2 (g_Sym (g_PiFst g))) A'.
           { eapply An_Conv; eauto.
             eapply An_Sym.  eauto. eauto using AnnTyping_regularity.
             eapply An_Refl; eauto. eauto with ctx_wff.
             eapply An_PiFst; eauto. }

         (* Now Beta *)
         simpl in *.
         match goal with
           [ H10: Value ?a, H9 : erase_tm ?a = _ , Ta : AnnTyping G ?a _ |- _ ] =>
           inversion Ta; subst; inversion H10; subst; simpl in H9; inversion H9 end.

         eexists.
         split.
         (* evaluate to application of coerced value *)
         eapply multi_trans with (b:= a_App (a_Conv (a_Abs Rel A' a0) g) Rel a0_2).
         eapply multi_An_AppLeft; eauto_lc.

         (* do push rule, lifting coercion to outside. *)
         eapply (multi_step _ RED).

         (* do beta reduction inside coercion *)
         eapply multi_step.
         eapply An_ConvTerm. eauto using AnnTyping_lc1, AnnDefEq_lc3.
         eapply An_AppAbs; eauto using AnnTyping_lc1.

         (* stop *)
         eapply multi_refl.
         { lc_inversion c. repeat econstructor; eauto_lc. }

         (* erasure property *)
         simpl_erase. auto.

         destruct rho.
         +++ have P: Path T (a_App (erase v) Rel (erase a0)); by eauto
                                                                    using lc_tm_erase.
         +++ have P: Path T (a_App (erase v) Irrel a_Bullet); by eauto using lc_tm_erase.
    + (* induction step for top-level coercions (Rel) *)
      induction_a0.
  - (* E_AppAbs Irrel*)
    intros.
    dependent induction a0; try destruct rho; simpl in H2; inversion H2; subst.
    + (* No coercions. a0 is a direct (Irrel) application of
        a0_1, which erases to an abstraction. *)
      ann_invert_clear.
      inversion H0.
      match goal with [H12 : AnnTyping G a0_1 (a_Pi Irrel A B),
                       H4  : AnnGood G (dom G),
                       H6  : erase_tm a0_1 = a_UAbs Irrel v |- _ ] =>
      move: H12 => Ta01;
      move: (erased_Value_reduces_to_CoercedValue Ta01 H4 H6
             ltac:(auto)) => [av [RE ?]];
      split_hyp end.
      move: (multi_preservation RE Ta01) => Tav.
      (* Check if there is a coercion at the top of av *)
      match goal with [ H : CoercedValue av |- _ ] => inversion H; subst end.
      ++ (* Value av *)
         match goal with [ H10 : Value av , H9 : erase av = _ |- _ ] =>
            inversion Tav; subst; inversion H10; subst; simpl in H9; inversion H9 end.
         exists (open_tm_wrt_tm a a0_2).
         split.
         eapply multi_trans with (b:= a_App (a_Abs Irrel A a) Irrel a0_2).
         eapply multi_An_AppLeft; eauto_lc.
         eapply multi_step; eauto_lc.
         eapply multi_refl; eauto.
         { lc_inversion c. subst.
           pick fresh y.
           rewrite (tm_subst_tm_tm_intro y); auto.
           eapply tm_subst_tm_tm_lc_tm; eauto using AnnTyping_lc1. }
         {
         (* argument really is irelevant. *)
           simpl_erase.
           pick fresh x.
           move: (H16 x ltac:(auto)) => RC. inversion RC.
           rewrite (tm_subst_tm_tm_intro x (erase a)).
           replace (a_Var_f x) with (erase (a_Var_f x)); auto.
           rewrite open_tm_erase_tm.
           rewrite tm_subst_tm_tm_fresh_eq; auto.
           rewrite (tm_subst_tm_tm_intro x (erase a)).
           replace (a_Var_f x) with (erase (a_Var_f x)); auto.
           rewrite open_tm_erase_tm.
           rewrite tm_subst_tm_tm_fresh_eq; auto.
           apply fv_tm_erase_tm; auto.
           apply fv_tm_erase_tm; auto.
         }

         no_paths.
      ++ (* av = (a |> g) *)
         have LC: lc_tm a0_1 by eauto using AnnTyping_lc1.
         (* Push rule *)
         inversion H0.
         ann_invert_clear.
         match goal with
           [ H4 : AnnGood _ _,  H20 : AnnDefEq G (dom G) g A0 (a_Pi Irrel A B),
             H18 : AnnTyping G a A0, H11: Value a |- _ ] =>
         move: (values_have_value_types H4 H18 H11) => VT;
         move: (consistent_a_Pi H4 VT H20) => [A' [B' EQ]]; subst;
         move: (An_Push _ _ _ _ a0_2 _ _ _ _ _ _ H11 H20 eq_refl eq_refl)=> RED;
         have TA': AnnTyping G A' a_Star by
           (move: (AnnTyping_regularity H18) => T1; inversion T1; auto)
         end.
         have Tb': AnnTyping G (a_Conv a0_2 (g_Sym (g_PiFst g))) A'.
           { eapply An_Conv; eauto.
             eapply An_Sym.  eauto. eauto using AnnTyping_regularity.
             eapply An_Refl; eauto. eauto with ctx_wff.
             eapply An_PiFst; eauto. }

         (* Now Beta *)
         simpl in *.
         match goal with
           [ H10: Value ?a, H9 : erase_tm ?a = _ , Ta : AnnTyping G ?a _ |- _ ] =>
           inversion Ta; subst; inversion H10; subst; simpl in H9; inversion H9 end.

         eexists.
         split.
         (* evaluate to application of coerced value *)
         eapply multi_trans with (b:= a_App (a_Conv (a_Abs Irrel A' a0) g) Irrel a0_2).
         eapply multi_An_AppLeft; eauto_lc.

         (* do push rule, lifting coercion to outside. *)
         eapply (multi_step _ RED).

         (* do beta reduction inside coercion *)
         eapply multi_step.
         eapply An_ConvTerm. eauto using AnnTyping_lc1, AnnDefEq_lc3.
         eapply An_AppAbs; eauto using AnnTyping_lc1.

         (* stop *)
         eapply multi_refl.

         { lc_inversion c. repeat econstructor; eauto_lc.
           pick fresh y.
           move: (H22 y ltac:(auto)) => h0.
           rewrite (tm_subst_tm_tm_intro y); auto.
           apply tm_subst_tm_tm_lc_tm; eauto_lc.
         }

         (* erasure property *)
         {
           simpl_erase.
           pick fresh x.
           move: (H22 x ltac:(auto)) => RC. inversion RC.
           rewrite (tm_subst_tm_tm_intro x (erase a0)).
           replace (a_Var_f x) with (erase (a_Var_f x)); auto.
           rewrite open_tm_erase_tm.
           rewrite tm_subst_tm_tm_fresh_eq; auto.
           rewrite (tm_subst_tm_tm_intro x (erase a0)).
           replace (a_Var_f x) with (erase (a_Var_f x)); auto.
           rewrite open_tm_erase_tm.
           rewrite tm_subst_tm_tm_fresh_eq; auto.
           apply fv_tm_erase_tm; auto.
           apply fv_tm_erase_tm; auto.
         }

         destruct rho.
         +++ have P: Path T (a_App (erase v) Rel (erase a0)); by eauto
                                                                    using lc_tm_erase.
         +++ have P: Path T (a_App (erase v) Irrel a_Bullet); by eauto using lc_tm_erase.
    + (* induction step for top-level coercions (irrel) *)
      induction_a0.
  - (* E_CAbsCApp *)
    intros.
    match goal with
      [ H3 : erase a0 = _ |- _ ] =>
    dependent induction a0; try destruct rho; simpl in H3; inversion H3; subst
    end.
    +  (* induction step *)
      induction_a0.

    + (* no coercion on top. *)
      clear IHa0.
      ann_invert_clear.
      match goal with
        [ H0 : irrelevant _ _ _ |- _ ] => inversion H0
      end.
      have ?: Value (a_UCAbs b) by eauto.
      match goal with
        [ H8 : AnnTyping G a0 _,
          H4 : AnnGood G (dom G),
          H5 : erase_tm a0 = _ |- _ ] =>
        move: (erased_Value_reduces_to_CoercedValue H8 H4 H5 ltac:(auto)) =>
        [av ?] ;  split_hyp end.
      match goal with
        [ H6 : multi (head_reduction G) a0 ?av,
          H8 : AnnTyping G a0 _ |- _ ] =>
        move: (multi_preservation H6 H8) => Tav
      end.
      (* Check if there is a coercion at the top of av *)
      match goal with [ H : CoercedValue av |- _ ] => inversion H; subst end.
      ++ (* Value av *)
        match goal with [ H10 : Value av , H9 : erase av = _ |- _ ] =>
        inversion Tav; subst; inversion H10; subst; try destruct rho;
        simpl in H9; inversion H9 end.
        subst.

        exists (open_tm_wrt_co a1 g).
        split.
        eapply multi_trans with (b := a_CApp (a_CAbs (Eq a b0 A1) a1) g).
        eapply multi_An_CAppLeft; eauto_lc.
        eapply multi_step.
        eapply An_CAppCAbs; eauto_lc.
        eapply multi_refl; eauto_lc.

        { invert_lc.
          eapply lc_body_tm_wrt_co; eauto_lc. }

        rewrite <- open_co_erase_tm2 with (g := g_Triv).
        auto.

      ++ (* av = (a |> g0) *)
         have LC: lc_tm a1 by eauto using Value_lc.
         (* Push rule *)
         match goal with
           [ H0 : irrelevant _ _ _ |- _ ] => inversion H0
         end.
         ann_invert_clear.
         match goal with
           [ H4 : AnnGood _ _,  H20 : AnnDefEq G (dom G) ?g0 A (a_CPi _ _),
             H18 : AnnTyping G a1 A, H11: Value a1 |- _ ] =>
         move: (values_have_value_types H4 H18 H11) => VT;
         move: (consistent_a_CPi H4 VT H20) => [phi' [B' EQ]]; subst;
         move : (An_CPush G a1 g0 g _ _ _ _ _ _ H11 H20 eq_refl eq_refl) => RED
         end.
         destruct phi' as [a' b' A'].
         have Tb':
           AnnDefEq G (dom G) (g_Cast g (g_Sym (g_CPiFst g0))) a' b'.
           { eapply An_Cast; eauto. }

         (* Now CBeta *)
         simpl in *.
         match goal with
           [ H10: Value ?a, H9 : erase_tm ?a = _ , Ta : AnnTyping G ?a _ |- _ ] =>
           inversion Ta; subst; inversion H10; subst; try destruct rho;
           simpl in H9; inversion H9 end.

         eexists.
         split.
         (* evaluate to application of coerced value *)
         eapply multi_trans.

         eapply multi_An_CAppLeft; eauto_lc.

         (* do push rule, lifting coercion to outside. *)
         eapply (multi_step _ RED).

         (* do beta reduction inside coercion *)
         eapply multi_step.
         eapply An_ConvTerm. eauto using AnnTyping_lc1, AnnDefEq_lc3.
         eapply An_CAppCAbs; eauto_lc.

         (* stop *)
         eapply multi_refl.

         { lc_inversion c. repeat econstructor; eauto_lc. }

         simpl_erase.
         rewrite <- open_co_erase_tm2 with (g := g_Triv).
         auto.

  - (* E_Axiom *)
    intros.
    dependent induction a0; try destruct rho; simpl in H2; inversion H2; subst.

    + unfold toplevel in H. unfold erase_sig in H.
      destruct (@binds_map_3 _ _ erase_csort F (Ax a A) an_toplevel H).
      split_hyp. destruct x; inversion H3. subst.

      exists a0. repeat split.
      eapply multi_step. eauto.
      eapply multi_refl.
      eauto using AnnTyping_lc1, an_toplevel_closed.

    + (* induction step *)
      induction_a0.

Unshelve. all: auto.
Qed.

End fc_consist.
