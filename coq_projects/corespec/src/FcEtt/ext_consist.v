
Require Import FcEtt.sigs.

Require Import Omega.

Require Export FcEtt.imports.
Require Import FcEtt.utils.
Require Export FcEtt.tactics.
Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ind.
Require Export FcEtt.ett_par.
Require Export FcEtt.erase_syntax.
Require Import FcEtt.ext_red_one.
Require Import FcEtt.ext_red.

Require Import FcEtt.ext_wf.

Module ext_consist (invert : ext_invert_sig)(fc_wf: fc_wf_sig).
Import invert.
Import fc_wf.

Module red_one := ext_red_one invert.
Export red_one.

Module red := ext_red invert.
Export red.

Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".


Definition Good (G : context) (D : available_props):=
  erased_context G /\
  forall c1 A B1 T1,
    binds c1 (Co (Eq A B1 T1)) G
    -> c1 `in` D
    -> exists C, Par G D A C /\ Par G D B1 C.

(* ---------------------------------------- *)

Lemma open2 :
  forall x b b' S D a a',
    x `notin` fv_tm_tm_tm a' \u fv_tm_tm_tm a ->
    erased_tm b ->
    erased_tm (open_tm_wrt_tm a (a_Var_f x)) ->
    Par S D (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm a' (a_Var_f x)) ->
    Par S D b b' ->
    Par S D (open_tm_wrt_tm a b) (open_tm_wrt_tm a' b').
Proof.
  intros x b b'. intros.
  rewrite (tm_subst_tm_tm_intro x); auto.
  rewrite [(_ _ b')] (tm_subst_tm_tm_intro x); auto.
  apply subst3; auto.
Qed.


Lemma a_Pi_head : forall S G b A rho B,
    Par S G (a_Pi rho A B) b -> exists A' B' L,
      b = a_Pi rho A' B' /\ Par S G A A' /\
      (forall x, x `notin` L -> Par S G (open_tm_wrt_tm B (a_Var_f x)) (open_tm_wrt_tm B' (a_Var_f x))).
Proof.
  intros. inversion H. subst. inversion H0.  exists A , B, empty. split; auto.
  subst.
  exists A', B', L.  split; auto.
Qed.

Lemma Par_Abs_inversion : forall G D a b rho,
    Par G D (a_UAbs rho a) b ->
    (exists a', b = (a_UAbs rho a') /\
          forall x, x `notin` fv_tm_tm_tm a \u fv_tm_tm_tm a' ->
               Par G D (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm a' (a_Var_f x)))
    \/
    (exists a', Par G D a' b /\ (forall x, x `notin`  fv_tm_tm_tm a ->
          open_tm_wrt_tm a (a_Var_f x) = a_App a' rho (a_Var_f x)) /\ rho = Rel)
    \/ (exists a', Par G D a' b /\ (forall x, x `notin`  fv_tm_tm_tm a ->
          open_tm_wrt_tm a (a_Var_f x) = a_App a' rho a_Bullet) /\ rho = Irrel). 

Proof.
  intros G D a a' rho P.
  inversion P; subst.
  + left. exists a. inversion H; eauto.
  + left. exists a'0. split. auto.
    intros x Fr.
    pick fresh y.
    rewrite (tm_subst_tm_tm_intro y); eauto.
    rewrite (tm_subst_tm_tm_intro y a'0); eauto.
    apply subst2; eauto.
  + right. left. 
    exists b. split. auto.
    split; eauto.
    intros x Fr.
    pick fresh y.
    rewrite (tm_subst_tm_tm_intro y); eauto.
    rewrite H5; eauto.
    simpl.
    rewrite tm_subst_tm_tm_fresh_eq; auto.
    destruct eq_dec. auto.
    done. 
  + right. right.
    exists b. split. auto.
    split; eauto.
    intros x Fr.
    pick fresh y.
    rewrite (tm_subst_tm_tm_intro y); eauto.
    rewrite H5; eauto.
    simpl.
    rewrite tm_subst_tm_tm_fresh_eq; auto. 
Qed.

Lemma Par_Abs_inversion_Rel : forall G D a b,
    Par G D (a_UAbs Rel a) b ->
    (exists a', b = (a_UAbs Rel a') /\
          forall x, x `notin` fv_tm_tm_tm a \u fv_tm_tm_tm a' ->
               Par G D (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm a' (a_Var_f x)))
    \/
    (exists a', Par G D a' b /\ (forall x, x `notin`  fv_tm_tm_tm a ->
          open_tm_wrt_tm a (a_Var_f x) = a_App a' Rel (a_Var_f x))).
Proof.
  intros G D a b H. eapply Par_Abs_inversion in H. inversion H; eauto.
  inversion H0; eauto.
  - right. inversion H1. inversion H2. inversion H4. eauto.
  - inversion H1. inversion H2. inversion H4. inversion H6.
Qed. 

Lemma Par_Abs_inversion_Irrel : forall G D a b,
    Par G D (a_UAbs Irrel a) b ->
    (exists a', b = (a_UAbs Irrel a') /\
          forall x, x `notin` fv_tm_tm_tm a \u fv_tm_tm_tm a' ->
               Par G D (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm a' (a_Var_f x)))
    \/ (exists a', Par G D a' b /\ (forall x, x `notin`  fv_tm_tm_tm a ->
          open_tm_wrt_tm a (a_Var_f x) = a_App a' Irrel a_Bullet)). 
Proof.
  intros G D a b H. eapply Par_Abs_inversion in H. inversion H; eauto.
  inversion H0; eauto.
  - right. inversion H1. inversion H2. inversion H4. inversion H6.
  - right. inversion H1. inversion H2. inversion H4. eauto.
Qed.


(*
Lemma Par_Abs_inversion_Irrel_2: forall G D a b,
    Par G D (a_UAbs Irrel a) b ->
    (exists a', b = (a_UAbs Irrel a') /\
               Par G D (open_tm_wrt_tm a (a_Bullet)) (open_tm_wrt_tm a' (a_Bullet)))
    \/ (exists a', Par G D a' b /\ (forall x, x `notin`  fv_tm_tm_tm a ->
          open_tm_wrt_tm a (a_Var_f x) = a_App a' Irrel a_Bullet)). 
Proof. 
  intros G D a b H. eapply Par_Abs_inversion in H. inversion H; eauto.
  inversion H0; eauto.
  - right. inversion H1. inversion H2. inversion H4. inversion H6.
  - right. inversion H1. inversion H2. inversion H4. eauto.
Qed. *)


Lemma Par_CAbs_inversion : forall G D a b,
    Par G D (a_UCAbs a) b ->
    (exists a', b = (a_UCAbs a') /\
          forall c, c `notin` fv_co_co_tm a \u fv_co_co_tm a' ->
               Par G D (open_tm_wrt_co a (g_Var_f c)) (open_tm_wrt_co a' (g_Var_f c)))
    \/ (exists a', Par G D a' b /\ (forall c, c `notin`  fv_co_co_tm a ->
          open_tm_wrt_co a (g_Var_f c) = a_CApp a' g_Triv)). 
Proof.
  intros G D a b H. inversion H; subst.
  - left. exists a. inversion H0; eauto.
  - left. exists a'. split. auto.
    intros c Fr. 
    pick fresh y.
    rewrite (co_subst_co_tm_intro y); eauto.
    rewrite (co_subst_co_tm_intro y a'); eauto.
    apply subst4; eauto.
  - right. exists b0. split; auto.
    intros c Fr. pick fresh y. 
    rewrite (co_subst_co_tm_intro y); eauto.
    rewrite H4; eauto. simpl. 
    rewrite co_subst_co_tm_fresh_eq; auto.
Qed.


Lemma copen2 :
  forall c (b: co) S D a a',
    lc_co b ->
    c `notin` fv_co_co_tm a' \u fv_co_co_tm a ->
    Par S D (open_tm_wrt_co a (g_Var_f c)) (open_tm_wrt_co a' (g_Var_f c)) ->
    Par S D (open_tm_wrt_co a b) (open_tm_wrt_co a' b).
Proof.
  intros x b b'. intros.
  rewrite (co_subst_co_tm_intro x); auto.
  rewrite [(_ _ b)] (co_subst_co_tm_intro x); auto.
  apply subst4; auto.
Qed.

(* -------------------------------------------------------------------------------- *)

Ltac try_refl :=
  try match goal with
      | [ P2 : Par _ _ _ ?b |- _ ] =>
        exists b; assert (lc_tm b); try eapply Par_lc2; eauto; try split; eauto; fail
      end.

(*
Ltac invert_syntactic_equality :=
  match goal with
      | [ H : a_UAbs _ _ = a_UAbs _ _ |- _ ] =>
        inversion H; subst; clear H
      | [ H : a_Pi _ _ _ = a_Pi _ _ _ |- _ ] =>
        inversion H; subst; clear H
      | [ H : a_UCAbs _ = a_UCAbs _ |- _ ] =>
        inversion H; subst; clear H
      | [ H : a_App _ _ _ = _ _ _ |- _ ] =>
        inversion H; subst; clear H
      | [ H : a_CApp _ _  = a_CApp _ _ |- _ ] =>
        inversion H; subst; clear H
      | [ H : a_Fam _ = a_Fam _ |- _ ] =>
        inversion H; subst; clear H
      | [ H : a_CPi _ _ = a_CPi _ _ |- _ ] =>
        inversion H; subst; clear H
  end.
*)
Ltac invert_equality :=
  match goal with
  | [ H : _ = _ |- _ ] =>
    inversion H
  end.

  Ltac try_refl_left :=
  try match goal with
      | [ P2 : Par _ _ ?b ?b |- exists cc:tm, Par ?S ?D ?b cc /\ Par ?S ?D ?a2 cc ] =>
        exists a2; assert (lc_tm a2); try eapply Par_lc2; eauto; try split; eauto; fail
      end.
  Ltac try_refl_right :=
  try match goal with
      | [ P2 : Par _ _ ?b ?b |- exists cc:tm, Par ?S ?D ?a2 cc /\ Par ?S ?D ?b cc ] =>
        exists a2; assert (lc_tm a2); try eapply Par_lc2; eauto; try split; eauto; fail
      end.

  Ltac invert_erased :=
    match goal with
    | [ H : erased_tm ?a |- _ ] => inversion H; subst; clear H
    end.

  (* Find prove that the result of Par is erased, and then invert that *)
  Ltac invert_erased_tm b :=
        let h0 := fresh in
        match goal with
          [ h : Par ?G ?D ?a b, h1: erased_tm ?a |- _ ] =>
          assert (h0 : erased_tm b);
          [ eapply (Par_erased_tm h); eauto | inversion h0; subst]
        end.


        (*    If we know that (a ^ x) == (App b rho x), replace
             (a ^ b0) with (App b rho b0)
            The tactic only succeeds if there is only 1 equality in
            the context.
       *)
      Ltac eta_expand x :=
        let h1 := fresh in
      match goal with
       | [ H18 : ∀ x : atom,
              x `notin` ?L0
              → open_tm_wrt_tm ?a (a_Var_f x) = a_App ?b0 ?rho (a_Var_f x)
              |- _ ] =>
        pick fresh x for (L0 \u  fv_tm_tm_tm a \u fv_tm_tm_tm b0);
        move: (H18 x ltac:(auto)) => h1; clear H18;
        rewrite (@tm_subst_tm_tm_intro x a); auto; rewrite h1;
        simpl; destruct (@eq_dec tmvar _ x x); try done;
        rewrite tm_subst_tm_tm_fresh_eq; auto
       | [ H18 : ∀ x : atom,
              x `notin` ?L0
              → open_tm_wrt_tm ?a (a_Var_f x) = a_App ?b0 ?rho a_Bullet
              |- _ ] =>
        pick fresh x for (L0 \u  fv_tm_tm_tm a \u fv_tm_tm_tm b0);
        move: (H18 x ltac:(auto)) => h1; clear H18;
        rewrite (@tm_subst_tm_tm_intro x a); auto; rewrite h1;
        simpl; destruct (@eq_dec tmvar _ x x); try done;
        rewrite tm_subst_tm_tm_fresh_eq; auto
       | [ H18 : ∀ x : atom,
              x `notin` ?L0
              → open_tm_wrt_co ?a (g_Var_f x) = a_CApp ?b0 g_Triv
              |- _ ] =>
        pick fresh x for (L0 \u  fv_co_co_tm a \u fv_co_co_tm b0);
        move: (H18 x ltac:(auto)) => h1; clear H18;
        rewrite (@co_subst_co_tm_intro x a); auto; rewrite h1;
        simpl; destruct (@eq_dec tmvar _ x x); try done;
        rewrite co_subst_co_tm_fresh_eq; auto
      end.


       (* Rewrite a goal of the form
            ... (a'0 ^ b'0) ...
          To
            ... (b . b'0) ...
          and try to solve it, give eta-assn Y2 *)
      Ltac eta_case a'0 Y2 :=
         let x:= fresh in
         pick fresh x;
         rewrite (tm_subst_tm_tm_intro x a'0); auto;
         rewrite Y2; auto; simpl;
         rewrite (tm_subst_tm_tm_fresh_eq); auto;
         destruct eq_dec; try done;
         eauto; clear x.



Ltac invert_lc :=
  match goal with
    | [ H : lc_tm ?a |- _ ] => inversion H; subst; clear H
  end.

  Ltac use_size_induction a ac Par1 Par2 :=
  match goal with
  | [   IH : forall y: nat, ?T,
        H2 : Good ?G ?D,
        H3 : erased_tm a,
        H : Par ?G ?D a ?b0,
        H4 : Par ?G ?D a ?b1 |- _ ] =>
      move: (@IH (size_tm a) ltac:(omega) a ltac:(auto) _ _ _ H2 H3 H _ H4) => [ ac [Par1 Par2]]
  end.


  Ltac use_size_induction_open a0 x ac Par1 Par2 :=
      let h0 := fresh in
      let h1 := fresh in
      let h2 := fresh in
      let EQ1 := fresh in
      let EQ2 := fresh in
      match goal with
        | [  H : ∀ x : atom,
              x `notin` ?L
              → Par ?S ?D (?open_tm_wrt_tm a0 (?a_Var_f x)) ?b,
             H4: ∀ x : atom,
                 x `notin` ?L0
                 → Par ?S ?D (?open_tm_wrt_tm a0 (?a_Var_f x)) ?c,
             H1 : ∀ x : atom, x `notin` ?L1 →
    erased_tm (?open_tm_wrt_tm a0 (?a_Var_f x)) |- _ ] =>
    move: (H x ltac:(auto)) => h0; clear H;
    move: (H4 x ltac:(auto)) => h1; clear H4;
                               move: (H1 x ltac:(auto)) => h2; clear H1;
    move: (size_tm_open_tm_wrt_tm_var a0 x) => EQ1;
    move: (size_tm_open_tm_wrt_co_var a0 x) => EQ2;

    use_size_induction (open_tm_wrt_tm a0 (a_Var_f x)) ac Par1 Par2;
    clear h0; clear h1; clear h2; clear EQ1; clear EQ2
    end.

(*
Ltac use_induction a ac Par1 Par2 :=
  match goal with
  | [ IHPar1 : Good ?G ?D -> erased_tm a → ∀ a2 : tm, Par ?G ?D ?a a2 → ?T ,
        H2 : Good ?G ?D,
        H3 : erased_tm a,
        H4 : Par ?G ?D a ?b |- _ ] =>
    destruct (IHPar1 H2 H3 _ H4) as [ac [Par1 Par2]]
  end.

Ltac use_induction_on a b ac Par1 Par2 :=
  match goal with
  | [ IHPar1 : Good ?G ?D -> erased_tm a → ∀ a2 : tm, Par ?G ?D ?a a2 → ?T ,
        H2 : Good ?G ?D,
        H3 : erased_tm a,
        H4 : Par ?G ?D a b |- _ ] =>
    destruct (IHPar1 H2 H3 _ H4) as [ac [Par1 Par2]]
  end.
*)

Ltac par_erased_open x J Par4 :=
  let K := fresh in
  let KK := fresh in
  let h0 := fresh in
  match goal with
  | [H13 : ∀ x : atom, x `notin` ?L →
                       Par ?G ?D (open_tm_wrt_tm ?a (a_Var_f x)) ?b,
     H4 : ∀ x : atom, x `notin` ?L1 → erased_tm  (open_tm_wrt_tm ?a (a_Var_f x))
       |- _ ] =>
    have: x `notin` L; auto => h0;
    pose K:= H13 x h0; clearbody K; clear h0;
    have: x `notin` L1; auto => h0;
    pose KK := H4 x h0; clearbody KK;
    pose J := subst3 x Par4 KK K;
    clearbody J;
    repeat rewrite tm_subst_tm_tm_open_tm_wrt_tm in J; [auto;
    simpl in J;
    destruct eq_dec; try congruence;
    repeat rewrite tm_subst_tm_tm_fresh_eq in J; auto
    | try apply (Par_lc2 Par4); auto
    | apply (Par_lc1 Par4); auto]
  end.

      Ltac finish_open_co a'0 :=
        let K := fresh in
        let J := fresh in
        let h0 := fresh in
      match goal with
      | H12 : forall c, c `notin` ?L -> Par ?G ?D (open_tm_wrt_co a'0 (g_Var_f c)) (open_tm_wrt_co ?b (g_Var_f c)) |- _ =>
        pick_fresh c;
        have: c `notin` L; auto => h0;
        pose K := H12 c h0; clearbody K;
        pose J := subst4 c lc_g_Triv K;
        clearbody J;
        repeat rewrite co_subst_co_tm_open_tm_wrt_co in J; eauto;
        simpl in J;
        destruct eq_dec; try congruence;
        repeat rewrite co_subst_co_tm_fresh_eq in J; eauto with lc

      end.


Lemma open_tm_wrt_tm_bullet_var_eq: forall a x, 
    x `notin` fv_tm_tm_tm (open_tm_wrt_tm a (a_Var_f x)) ->
    open_tm_wrt_tm a (a_Bullet) = open_tm_wrt_tm a (a_Var_f x).
Proof.
  intros.  
  rewrite (tm_subst_tm_tm_intro x a a_Bullet); auto.
  rewrite tm_subst_tm_tm_fresh_eq. auto.
  auto.
  rewrite fv_tm_tm_tm_open_tm_wrt_tm_lower.
  eauto.
Qed.


Lemma open_tm_wrt_tm_inj_irrel: forall(a2 a1 : tm) (x1 : atom),
x1 `notin` fv_tm_tm_tm (open_tm_wrt_tm a2 (a_Var_f x1)) 
-> x1 `notin` fv_tm_tm_tm (open_tm_wrt_tm a1 (a_Var_f x1))
  -> open_tm_wrt_tm a2 a_Bullet = open_tm_wrt_tm a1 (a_Var_f x1)
    -> a2 = a1.
Proof. 
  intros. erewrite open_tm_wrt_tm_bullet_var_eq in H1; eauto.
  eapply open_tm_wrt_tm_inj; eauto. rewrite fv_tm_tm_tm_open_tm_wrt_tm_lower. eauto. 
  rewrite fv_tm_tm_tm_open_tm_wrt_tm_lower. eauto. 
Qed.

Lemma open_tm_wrt_co_triv_var_eq: forall a c, 
    c `notin` fv_co_co_tm (open_tm_wrt_co a (g_Var_f c)) ->
    open_tm_wrt_co a g_Triv = open_tm_wrt_co a (g_Var_f c).
Proof.
  intros.  
  rewrite (co_subst_co_tm_intro c a g_Triv); auto.
  rewrite co_subst_co_tm_fresh_eq. auto.
  auto.
  rewrite fv_co_co_tm_open_tm_wrt_co_lower.
  eauto.
Qed.

Lemma open_tm_wrt_co_inj: forall(a2 a1 : tm) (c : atom),
c `notin` fv_co_co_tm (open_tm_wrt_co a2 (g_Var_f c)) 
-> c `notin` fv_co_co_tm (open_tm_wrt_co a1 (g_Var_f c))
  -> open_tm_wrt_co a2 g_Triv = open_tm_wrt_co a1 (g_Var_f c)
    -> a2 = a1.
Proof.
  intros. erewrite open_tm_wrt_co_triv_var_eq in H1; eauto.
  eapply open_tm_wrt_co_inj; eauto. rewrite fv_co_co_tm_open_tm_wrt_co_lower. eauto. 
  rewrite fv_co_co_tm_open_tm_wrt_co_lower. eauto.
Qed.

Lemma erased_fv_co: forall a x, erased_tm a -> x `notin` fv_co_co_tm a.
Proof. 
  intros. induction H. all: simpl. all: try fsetdec.
  - pick fresh y. move: (H0 y ltac:(auto)) =>  h1.
    rewrite fv_co_co_tm_open_tm_wrt_tm_lower. eauto.
  - pick fresh y. move: (H1 y ltac:(auto)) => h1.
    apply union_notin_iff. split; eauto.
    rewrite fv_co_co_tm_open_tm_wrt_tm_lower. eauto.
  - pick fresh y. move: (H3 y ltac:(auto)) => h1.
    apply union_notin_iff. split. clear Fr. fsetdec.
    rewrite fv_co_co_tm_open_tm_wrt_co_lower. eauto.
  - pick fresh y. move: (H0 y ltac:(auto)) =>  h1.
    rewrite fv_co_co_tm_open_tm_wrt_co_lower. eauto.
Qed.

Lemma confluence_size : forall n a, size_tm a <= n ->  forall S D a1, Good S D -> erased_tm a -> Par S D a a1 -> forall a2, Par S D a a2 -> exists b, Par S D a1 b /\ Par S D a2 b.
Proof.
  pose confluence_size_def n :=
      forall a, size_tm a <= n ->  forall S D a1, Good S D -> erased_tm a -> Par S D a a1 -> forall a2, Par S D a a2 -> exists b, Par S D a1 b /\ Par S D a2 b.
  intro n. fold (confluence_size_def n).  eapply (well_founded_induction_type lt_wf).
  clear n. intros n IH. unfold confluence_size_def in *. clear confluence_size_def.
  intros a SZ S D a1 Gs Ea P1 a2 P2.
  inversion P1; inversion P2; subst.
  all: try solve [invert_equality].
  (* 37 subgoals *)

  all: try_refl_left.
  all: try_refl_right.
  all: try invert_syntactic_equality.
  all: simpl in SZ; destruct n; try solve [ inversion SZ ].
  all: invert_erased; inversion Gs.

  - (* two rel betas *)
    use_size_induction a0 ac Par1 Par2.
    use_size_induction b bc Par3 Par4.
    destruct (Par_Abs_inversion_Rel Par1) as [[a'' [EQ h0]] | [X1]]; subst;
    destruct (Par_Abs_inversion_Rel Par2) as [[a''' [EQ2 h1]]| [Y1]]; subst.
    -- inversion EQ2. subst.
       exists (open_tm_wrt_tm a''' bc).
       split. pick fresh x; eapply open2; eauto using Par_erased_tm.
       pick fresh x; eapply open2; eauto using Par_erased_tm.
    -- exists (open_tm_wrt_tm a'' bc).
       split. pick fresh x; eapply open2; eauto using Par_erased_tm.
       inversion H7.
       eta_expand x.
    -- exists (open_tm_wrt_tm a''' bc).
       split. inversion H7. eta_expand x. 
       pick fresh x; eapply open2; eauto using Par_erased_tm.
    -- exists (a_App ac Rel bc).
       split. inversion H7. eta_expand x0.
       inversion H8. eta_expand x0.
  - (* rel app beta / app cong *)
    use_size_induction a0 ac Par1 Par2.
    use_size_induction b bc Par3 Par4.
    invert_erased_tm (a_UAbs Rel a').
    inversion Par1; subst; clear Par1.
    -- exists (open_tm_wrt_tm a' bc); auto.
      split; eauto.
      apply open1 with (L:=L); eauto.
    -- exists (open_tm_wrt_tm a'1 bc); auto.
      split; eauto.
      pick_fresh x.
      par_erased_open x J Par3.
    -- exists (a_App ac Rel bc).
      split.
      eta_expand x. 
      eauto.
  - (* two irrel betas *)
    use_size_induction a0 ac Par1 Par2.
    invert_erased_tm (a_UAbs Irrel a');
    invert_erased_tm (a_UAbs Irrel a'0).
    destruct (Par_Abs_inversion_Irrel Par1) as [ [a'' [EQ X]] | W ];
    destruct (Par_Abs_inversion_Irrel Par2) as [ [a''' [EQ' X']] | W'].
    * subst.
      exists (open_tm_wrt_tm a''' a_Bullet).
      split; eauto. 
      pick fresh x; eapply open2; eauto. inversion EQ'; subst.
      apply X. fsetdec. 
      pick fresh x; eapply open2; eauto.
    * subst. 
      exists (open_tm_wrt_tm a'' a_Bullet). 
      split. pick fresh x; eapply open2; eauto.
      destruct W' as [ax [Par5 K]].
      eta_expand x.
    * exists (open_tm_wrt_tm a''' a_Bullet). split. 
      destruct W as [ax [Par5 K]]. 
      inversion EQ'; subst. eta_expand x. 
      pick fresh x; eapply open2; eauto.
    * exists (a_App ac Irrel a_Bullet). split.
      destruct W as [ax [Par5 K]].
      eta_expand x. destruct W' as [z [Par5 K]].
      eta_expand x.
  (* Irrel app beta / app cong *)
   - use_size_induction a0 ac Par1 Par2.
    invert_erased_tm (a_UAbs Irrel a').
    inversion Par1; subst; clear Par1.
    -- exists (open_tm_wrt_tm a' a_Bullet); auto.
      split; eauto.
      apply open1 with (L:=L); eauto.
    -- exists (open_tm_wrt_tm a'1 a_Bullet); auto.
      split; eauto.
      pick_fresh x; eapply open2; eauto.
    -- exists (a_App ac Irrel a_Bullet).
      split. eta_expand x. 
      eauto.
   (* rel app cong / app beta *)
  - use_size_induction a0 ac Par1 Par2.
    use_size_induction b bc Par3 Par4.
    invert_erased_tm (a_UAbs Rel a'0).
    inversion Par2; subst; clear Par2.
    -- exists (open_tm_wrt_tm a'0 bc); auto.
      split; eauto.
      apply open1 with (L:=L); eauto.
    -- exists (open_tm_wrt_tm a'1 bc); auto.
      split; eauto.
      pick_fresh x.
      par_erased_open x J Par4.
    -- exists (a_App ac Rel bc).
      split. eauto.
      eta_expand x.
  - (* rel app cong / app cong *)
    use_size_induction a0 ac Par1 Par2.
    use_size_induction b bc Par3 Par4.
    exists (a_App ac Rel bc).
    split. eauto. eauto.
  - (* Irrel app cong / app beta *)
    use_size_induction a0 ac Par1 Par2.
    invert_erased_tm (a_UAbs Irrel a'0).
    inversion Par2; subst; clear Par2.
    -- exists (open_tm_wrt_tm a'0 a_Bullet); auto.
      split; eauto.
      apply open1 with (L:=L); eauto.
    -- exists (open_tm_wrt_tm a'1 a_Bullet); auto.
      split; eauto. pick_fresh x; eapply open2; eauto.
    -- exists (a_App ac Irrel a_Bullet).
      split. eauto.
      eta_expand x.
  - (* Irrel app cong / app cong *)
    use_size_induction a0 ac Par1 Par2.
    exists (a_App ac Irrel a_Bullet).
    split. eauto. eauto.
  - (* two cbetas *)
    use_size_induction a0 ac Par1 Par2.
    invert_erased_tm (a_UCAbs a').
    invert_erased_tm (a_UCAbs a'0).
    destruct (Par_CAbs_inversion Par1) as [ [a'' [EQ X]] | W ];
    destruct (Par_CAbs_inversion Par2) as [ [a''' [EQ' X']] | W']. 
    -- subst.
      exists (open_tm_wrt_co a''' g_Triv).
      split; eauto. pick fresh x; eapply copen2; eauto.
      inversion EQ'; subst.
      apply X. fsetdec.
      pick fresh x; eapply copen2; eauto.
    -- subst. 
      exists (open_tm_wrt_co a'' g_Triv). 
      split. pick fresh x; eapply copen2; eauto.
      destruct W' as [ax [Par5 K]].
      eta_expand c.
    -- exists (open_tm_wrt_co a''' g_Triv). split. 
      destruct W as [ax [Par5 K]]. 
      inversion EQ'; subst. eta_expand c. 
      pick fresh x; eapply copen2; eauto.
    -- exists (a_CApp ac g_Triv). split.
      destruct W as [ax [Par5 K]].
      eta_expand c. destruct W' as [z [Par5 K]].
      eta_expand c.
  - (* cbeta / capp cong *)
    use_size_induction a0 ac Par1 Par2.
    destruct (Par_CAbs_inversion Par1) as [ [a'' [EQ X]] | W ].
    inversion P2; subst; clear P2.
    + exists (open_tm_wrt_co a'' g_Triv).
      split; eauto. pick fresh x; eapply copen2; eauto.
    + exists (open_tm_wrt_co a'' g_Triv).
      split; eauto. pick fresh x; eapply copen2; eauto.
      rewrite H7. eauto.
    + exists (open_tm_wrt_co a'' g_Triv).
      split; eauto. pick fresh x; eapply copen2; eauto.
    + exists (a_CApp ac g_Triv). split; eauto.
      destruct W as [ax [Par5 K]]. eta_expand c.
  - (* capp cong / cbeta *)
    use_size_induction a0 ac Par1 Par2.
    destruct (Par_CAbs_inversion Par2) as [ [a'' [EQ X]] | W ].
    inversion P2; subst; eauto; clear P2.
    + exists (open_tm_wrt_co a'' g_Triv).
      split; eauto. rewrite H3. pick fresh x; eapply copen2; eauto.
    + exists (open_tm_wrt_co a'' g_Triv).
      split; eauto. rewrite H7. pick fresh x; eapply copen2; eauto.
    + exists (open_tm_wrt_co a'' g_Triv).
      split; eauto. rewrite H7. pick fresh x; eapply copen2; eauto.
    + exists (a_CApp ac g_Triv). split; eauto.
      destruct W as [ax [Par5 K]]. eta_expand c.
  - (* capp cong / capp cong *)
    use_size_induction a0 ac Par1 Par2.
    exists (a_CApp ac g_Triv). auto.
  - (* abs cong / abs cong *)
    pick fresh x.
    use_size_induction_open a0 x ac Par1 Par2.
    exists (a_UAbs rho (close_tm_wrt_tm x ac)).
    split; eauto; try solve [apply (@Par_Abs_exists x); eauto].
  - (* abs cong rel / eta rel *)
    pick fresh x.
    move: (H x ltac:(auto)) => h1. clear H. rewrite H5 in h1.
    (* h1 : b x => a' *)
    inversion h1.
    + subst. (* refl b x => b x *)
      exists a2. split.
            pick fresh y and apply Par_Eta; eauto.
      apply eta_swap with (x:=x); eauto.
      eauto using Par_lc2.
    + subst. (* b x => a' ^ x  where b => \a' *)
      inversion H11. subst.
      apply open_tm_wrt_tm_inj in H9; auto. subst. 
      move: (H5 x ltac:(auto)) => h2.
      match goal with
        [ H : ?a = ?b |- _ ] =>
        assert (h3 : size_tm a = size_tm b) end.
      rewrite h2; auto.
      simpl in h3.
      rewrite size_tm_open_tm_wrt_tm_var in h3.
      assert (size_tm b <= size_tm a0). omega.
      move: (H2 x ltac:(auto)) => h4. rewrite h2 in h4. inversion h4.
      use_size_induction b bb Par1 Par2.
      exists bb. eauto.
      eapply Par_fv_preservation in H10. simpl in H10. eauto. eauto.
    + subst. (* b x => a'0 x where b => a'0 *)
      rewrite -H9 in h1.
      inversion H11. subst. clear H11.
      move: (H5 x ltac:(auto)) =>  h2.
      move: (H2 x ltac:(auto)) => h3.
      rewrite h2 in h3. inversion h3. subst.
      match goal with
        [ H : ?a = a_App ?b ?rho ?x |- _ ] =>
        assert (h4 : size_tm a = size_tm (a_App b rho x)) end.
      rewrite h2; auto.
      simpl in h4.
      rewrite size_tm_open_tm_wrt_tm_var in h4.
      assert (size_tm b <= size_tm a0). omega.
      use_size_induction b bb Par1 Par2.
      move: (@Par_fv_preservation _ _ x _ _ H10 ltac:(eauto)) => h5.
      exists bb.
      split.
      pick fresh y and apply Par_Eta. eapply Par2.
      eapply eta_swap with (x:=x); eauto.
      eauto.
    + eauto.
  - (* abs cong irrel / eta irrel *)
    pick fresh x. move: (H3 x ltac:(auto)) => h5. inversion h5; subst.
    move: (H x ltac:(auto)) => h1. rewrite H5 in h1.
    (* h1 : b x => a' *)
    inversion h1.
    + subst. (* refl b x => b x *)
      exists a2. split.
            pick fresh y and apply Par_EtaIrrel; eauto.
      apply eta_swap_irrel with (x:=x); eauto.
      eauto using Par_lc2.
    + subst.
      move: (H2 x ltac:(auto)) => k1.
      rewrite H5 in k1.
      inversion k1.
      assert (erased_tm (a_UAbs Irrel a'0)). eapply Par_erased_tm. eauto. auto.
      eapply erased_a_Abs_inversion in H9.
      inversion H9; clear H9.
      assert (x `notin` fv_tm_tm_tm (open_tm_wrt_tm a'0 (a_Var_f x))).
      inversion H13; eauto.
      apply open_tm_wrt_tm_inj_irrel in H10; subst.
      move: (H5 x ltac:(auto)) => h2.
      match goal with
        [ H : ?a = ?b |- _ ] =>
        assert (h3 : size_tm a = size_tm b) end.
      rewrite h2; auto.
      simpl in h3.
      rewrite size_tm_open_tm_wrt_tm_var in h3.
      assert (size_tm b <= size_tm a0). omega.
      move: (H2 x ltac:(auto)) => h4. rewrite h2 in h4. inversion h4.
      use_size_induction b bb Par1 Par2.
      exists bb. split; eauto. auto.
      move: (@Par_fv_preservation _ _ x _ _ h1 ltac:(eauto)) => h6. eauto.
      move: (@Par_fv_preservation _ _ _ _ _ H11 ltac:(eauto)) => h7. eauto.
      (*helping fsetdec a bit*) apply union_notin_iff in Fr. fsetdec.
    + subst. (* b x => a'0 x where b => a'0 *)
      rewrite -H10 in h1.
      move: (H5 x ltac:(auto)) =>  h2.
      move: (H2 x ltac:(auto)) => h3.
      rewrite h2 in h3. inversion h3. subst.
      match goal with
        [ H : ?a = a_App ?b ?rho ?x |- _ ] =>
        assert (h4 : size_tm a = size_tm (a_App b rho x)) end.
      rewrite h2; auto.
      simpl in h4.
      rewrite size_tm_open_tm_wrt_tm_var in h4.
      assert (size_tm b <= size_tm a0). omega.
      use_size_induction b bb Par1 Par2.
      move: (@Par_fv_preservation _ _ x _ _ h1 ltac:(eauto)) => h6.
      exists bb.
      split. 
      pick fresh y and apply Par_EtaIrrel. eapply Par2.
      eapply eta_swap_irrel with (x:=x); eauto.
      eapply Par_erased_tm in h1; eauto. simpl in h6.
      (*helping fsetdec a bit*) apply union_notin_iff in Fr.
      inversion Fr. clear Fr.  clear Fr0. fsetdec.
      eauto.
    + eauto.
  - (* pi cong / pi cong *)
    pick fresh x.
    use_size_induction A ac Par1 Par2.
    use_size_induction_open B x bc Par3 Par4.
    exists (a_Pi rho ac (close_tm_wrt_tm x bc)).
    split; eauto; try solve [apply (@Par_Pi_exists x); eauto].
  - (* cabs cong / cabs cong *)
    pick fresh c.
    use_size_induction_open a0 c ac Par1 Par2.
    exists (a_UCAbs (close_tm_wrt_co c ac)).
    split; eauto; try solve [apply (@Par_CAbs_exists c); eauto].
  - (* cabs / eta c *)
    pick fresh x.
    move: (H x ltac:(auto)) => h1. clear H. rewrite H5 in h1.
    (* h1 : b x => a' *)
    inversion h1.
    + subst. (* refl b x => b x *)
      exists a2. split.
            pick fresh y and apply Par_EtaC; eauto.
      apply eta_swap_c with (x:=x); eauto.
      eauto using Par_lc2.
    + subst.
      move: (H5 x ltac:(auto)) => h2.
      match goal with
        [ H : ?a = ?b |- _ ] =>
        assert (h3 : size_tm a = size_tm b) end.
      rewrite h2; auto.
      simpl in h3.
      rewrite size_tm_open_tm_wrt_co_var in h3.
      assert (size_tm b <= size_tm a0). omega.
      move: (H1 x ltac:(auto)) => h4. rewrite h2 in h4. inversion h4.
      use_size_induction b bb Par1 Par2.
      exists bb. 
      split; eauto.
      eapply open_tm_wrt_co_inj in H7. subst; auto.
      Focus 2. move: (@Par_fv_co_preservation _ _ x _ _ h1 ltac:(eauto)) => h5. eauto.
      apply erased_fv_co. eapply erased_a_CAbs_inversion.
      move: (@Par_erased_tm _ _ _ _ H8 ltac:(eauto)) => h6; eauto.
      move: (@Par_fv_co_preservation _ _ x _ _ H8 ltac:(eauto)) => h5. 
      simpl in h5; eauto.
    + subst. (* b x => a'0 x where b => a'0 *)
      rewrite -H7 in h1.
      (*inversion H8. subst. clear H10.*)
      move: (H5 x ltac:(auto)) =>  h2.
      move: (H1 x ltac:(auto)) => h3.
      rewrite h2 in h3. inversion h3. subst.
      match goal with
        [ H : ?a = a_CApp ?b ?x |- _ ] =>
        assert (h4 : size_tm a = size_tm (a_CApp b x)) end.
      rewrite h2; auto.
      simpl in h4.
      rewrite size_tm_open_tm_wrt_co_var in h4.
      assert (size_tm b <= size_tm a0). omega.
      use_size_induction b bb Par1 Par2.
      move: (@Par_fv_preservation _ _ x _ _ H8 ltac:(eauto)) => h5.
      exists bb.
      split; eauto.
      pick fresh y and apply Par_EtaC; eauto.
      eapply eta_swap_c with (x:=x); eauto. clear Fr0.
      move: (@Par_fv_co_preservation _ _ x _ _ h1 ltac:(eauto)) => h6.
      simpl in h6. rewrite union_notin_iff. split. 
      apply union_notin_iff in Fr. inversion Fr. clear Fr. fsetdec.
      clear Fr. fsetdec.
    + eauto.
  - (* cpi cong / cpi cong *)
    use_size_induction A AC Par1 Par2.
    use_size_induction B BC Par3 Par4.
    use_size_induction A1 AC1 Par5 Par6.
    pick fresh c.
    use_size_induction_open a0 c ac Par7 Par8.
    exists (a_CPi (Eq AC BC AC1) (close_tm_wrt_co c ac)).
    split; eauto; try solve [apply (@Par_CPi_exists c); eauto].
  - (* fam / fam *)
    have E: (Ax a1 A = Ax a2 A0). eapply binds_unique; eauto using uniq_toplevel.
    inversion E. subst. clear E.
    have LC: lc_tm a2. apply Toplevel_lc in H. inversion H. auto.
    exists a2. split; eauto.
  - (* eta rel / abs cong rel *)
    pick fresh x.
    match goal with
      [ H5 : ∀ x : atom,
            x `notin` ?L0
            → Par ?S ?D (open_tm_wrt_tm ?a0 (a_Var_f x))
                  (open_tm_wrt_tm ?a' (a_Var_f x)),
        H :  ∀ x : atom,
            x `notin` ?L → open_tm_wrt_tm ?a0 (a_Var_f x) = a_App ?b ?rho (a_Var_f x)
            |- _ ] =>
      move: (H x ltac:(auto)) => h0;
      move: (H5 x ltac:(auto)) => h1; clear H5; rewrite h0 in h1
    end.
  (* h1 : b x => a' x *)
    inversion h1; subst.
    + exists a1. split. eauto using Par_lc2.
       pick fresh y and apply Par_Eta; eauto.
       apply eta_swap with (x:=x); eauto.
    + (* b x => a' ^ x  where b => \a' *)
      match goal with
        [  H8 : Par ?S ?D ?b (a_UAbs ?rho ?a'0),
          H11 : Par ?S ?D (a_Var_f x) ?b',
          H10 : open_tm_wrt_tm a'0 ?b' = open_tm_wrt_tm ?a' (a_Var_f x)
          |- _ ] =>
        inversion H11; subst;
          move: (@Par_fv_preservation S D x _ _ H8 ltac:(auto)) => h2; simpl in h2; eauto;
          apply open_tm_wrt_tm_inj in H10; auto; subst; clear H11
      end.
      match goal with
        [ H : ?a = ?b |- _ ] =>
        assert (h3 : size_tm a = size_tm b) end.
      rewrite h0; auto.
      simpl in h3.
      rewrite size_tm_open_tm_wrt_tm_var in h3.
      assert (size_tm b <= size_tm a0). omega.
      let h4 := fresh in
      match goal with
        [ H2 :  ∀ x : atom, x `notin` ?L1 → erased_tm (open_tm_wrt_tm ?a0 (a_Var_f x)) |- _ ] =>
        move: (H2 x ltac:(auto)) => h4; rewrite h0 in h4; inversion h4; subst
      end.
      use_size_induction b bb Par1 Par2.
      exists bb. eauto.
    + subst. (* b x => a'0 x where b => a'0 *)
      rewrite -H9 in h1.
      inversion H11. subst. clear H11.
      move: (H0 x ltac:(auto)) =>  h2.
      move: (H3 x ltac:(auto)) => h3.
      rewrite h2 in h3. inversion h3. subst.
      match goal with
        [ H : ?a = a_App ?b ?rho ?x |- _ ] =>
        assert (h4 : size_tm a = size_tm (a_App b rho x)) end.
      rewrite h2; auto.
      simpl in h4.
      rewrite size_tm_open_tm_wrt_tm_var in h4.
      assert (size_tm b <= size_tm a0). omega.
      use_size_induction b bb Par1 Par2.
      move: (@Par_fv_preservation _ _ x _ _ H10 ltac:(eauto)) => h5.
      exists bb.
      split.
      eauto.
      pick fresh y and apply Par_Eta. eapply Par2.
      eapply eta_swap with (x:=x); eauto.
  - (* eta rel / eta rel *)
    pick fresh x for (L \u L0 \u L1).
    move: (H0 x ltac:(auto)) => E1.
    move: (H6 x ltac:(auto)) => E2.
    move: (H3 x ltac:(auto)) => Eb.
    rewrite E2 in E1.
    inversion E1. subst.
    rewrite E2 in Eb. inversion Eb. subst.
    move: (size_tm_open_tm_wrt_tm_var a0 x) => Sb.
    match goal with
      [ H : open_tm_wrt_tm ?a ?x = ?b |- _ ] =>
      assert (K : size_tm (open_tm_wrt_tm a x) = size_tm b);
        [rewrite H; auto| simpl in K]
    end.
    use_size_induction b ac Par1 Par2.
    exists ac. auto.
  - (* eta irrel / abs cong irrel*)
    pick fresh x.
    match goal with
      [ H5 : ∀ x : atom,
            x `notin` ?L0
            → Par ?S ?D (open_tm_wrt_tm ?a0 (a_Var_f x))
                  (open_tm_wrt_tm ?a' (a_Var_f x)),
        H :  ∀ x : atom,
            x `notin` ?L → open_tm_wrt_tm ?a0 (a_Var_f x) = a_App ?b ?rho a_Bullet
            |- _ ] =>
      move: (H x ltac:(auto)) => h0;
      move: (H5 x ltac:(auto)) => h1; clear H5; rewrite h0 in h1
    end.
  (* h1 : b x => a' x *)
    inversion h1; subst.
    + exists a1. split. eauto using Par_lc2.
       pick fresh y and apply Par_EtaIrrel; eauto.
       apply eta_swap_irrel with (x:=x); eauto.
    + (* b x => a' ^ x  where b => \a' *)
      assert (h3: size_tm (open_tm_wrt_tm a0 (a_Var_f x)) 
              = size_tm (a_App b Irrel a_Bullet)). rewrite h0; auto.
      rewrite size_tm_open_tm_wrt_tm_var in h3.
      simpl in h3.
      assert (size_tm b <= size_tm a0). omega.
      let h4 := fresh in
      match goal with
        [ H2 :  ∀ x : atom, x `notin` ?L1 → erased_tm (open_tm_wrt_tm ?a0 (a_Var_f x)) |- _ ] =>
        move: (H2 x ltac:(auto)) => h4; rewrite h0 in h4; inversion h4; subst
      end.
      use_size_induction b bb Par1 Par2.
      exists bb. split; eauto.
      apply open_tm_wrt_tm_inj_irrel in H8; subst; eauto.
      Focus 2. move: (@Par_fv_preservation _ _ x _ _ h1 ltac:(eauto)) => h5.
      auto.
      assert (erased_tm (a_UAbs Irrel a'0)). eapply Par_erased_tm. eauto. auto.
      eapply erased_a_Abs_inversion in H7.
      inversion H7; clear H7.
      assert (x `notin` fv_tm_tm_tm (open_tm_wrt_tm a'0 (a_Var_f x))).
      inversion H12; eauto. auto.
      move: (@Par_fv_preservation _ _ x _ _ H9 ltac:(eauto)) => h6.
      simpl in h6. auto.
    + subst. (* b x => a'0 x where b => a'0 *)
      rewrite -H8 in h1.
      move: (H0 x ltac:(auto)) =>  h2.
      move: (H3 x ltac:(auto)) => h3.
      rewrite h2 in h3. inversion h3. subst.
      match goal with
        [ H : ?a = a_App ?b ?rho ?x |- _ ] =>
        assert (h4 : size_tm a = size_tm (a_App b rho x)) end.
      rewrite h2; auto.
      simpl in h4.
      rewrite size_tm_open_tm_wrt_tm_var in h4.
      assert (size_tm b <= size_tm a0). omega.
      use_size_induction b bb Par1 Par2.
      exists bb.
      split.
      eauto.
      pick fresh y and apply Par_EtaIrrel. eapply Par2.
      eapply eta_swap_irrel with (x:=x); eauto.
      move: (@Par_fv_preservation _ _ x _ _ h1 ltac:(eauto)) => h5.
      simpl in h5. clear Fr0. apply union_notin_iff in Fr. 
      inversion Fr. rewrite union_notin_iff. split; auto.
  - (* eta irrel / eta irrel *) 
    pick fresh x for (L \u L0 \u L1).
    move: (H0 x ltac:(auto)) => E1.
    move: (H6 x ltac:(auto)) => E2.
    move: (H3 x ltac:(auto)) => Eb.
    rewrite E2 in E1.
    inversion E1. subst.
    rewrite E2 in Eb. inversion Eb. subst.
    move: (size_tm_open_tm_wrt_tm_var a0 x) => Sb.
    match goal with
      [ H : open_tm_wrt_tm ?a ?x = ?b |- _ ] =>
      assert (K : size_tm (open_tm_wrt_tm a x) = size_tm b);
        [rewrite H; auto| simpl in K]
    end.
    use_size_induction b ac Par1 Par2.
    exists ac. auto.
  - (* eta c / cabs *)
    pick fresh x.
    match goal with
      [ H5 : ∀ c : atom,
            c `notin` ?L0
            → Par ?S ?D (open_tm_wrt_co ?a0 (g_Var_f c))
                  (open_tm_wrt_co ?a' (g_Var_f c)),
        H :  ∀ c : atom,
            c `notin` ?L → open_tm_wrt_co ?a0 (g_Var_f c) = a_CApp ?b g_Triv
            |- _ ] =>
      move: (H x ltac:(auto)) => h0;
      move: (H5 x ltac:(auto)) => h1; clear H5; rewrite h0 in h1
    end.
  (* h1 : b x => a' x *)
    inversion h1; subst.
    + exists a1. split. eauto using Par_lc2.
       pick fresh y and apply Par_EtaC; eauto.
       apply eta_swap_c with (x:=x); eauto.
    + (* b x => a' ^ x  where b => \a' *)
      subst.
      move: (H2 x ltac:(auto)) => h2.
      assert (h3 : size_tm (open_tm_wrt_co a0 (g_Var_f x)) = size_tm (a_CApp b g_Triv)).
      rewrite h0; auto.
      simpl in h3.
      rewrite size_tm_open_tm_wrt_co_var in h3.
      assert (size_tm b <= size_tm a0). omega.
      move: (H0 x ltac:(auto)) => h4. rewrite h4 in h2. inversion h2.
      use_size_induction b bb Par1 Par2.
      exists bb. 
      split; eauto.
      eapply open_tm_wrt_co_inj in H7. subst; auto.
      Focus 2. move: (@Par_fv_co_preservation _ _ x _ _ h1 ltac:(eauto)) => h5. eauto.
      apply erased_fv_co. eapply erased_a_CAbs_inversion.
      move: (@Par_erased_tm _ _ _ _ H8 ltac:(eauto)) => h6; eauto.
      move: (@Par_fv_co_preservation _ _ x _ _ H8 ltac:(eauto)) => h5. 
      simpl in h5; eauto.
    + subst. (* b x => a'0 x where b => a'0 *)
      rewrite -H7 in h1.
      (*inversion H8. subst. clear H10.*)
      move: (H2 x ltac:(auto)) =>  h2.
      move: (H0 x ltac:(auto)) => h3.
      rewrite h3 in h2. inversion h2. subst.
      match goal with
        [ H : ?a = a_CApp ?b ?x |- _ ] =>
        assert (h4 : size_tm a = size_tm (a_CApp b x)) end.
      rewrite h3; auto.
      simpl in h4.
      rewrite size_tm_open_tm_wrt_co_var in h4.
      assert (size_tm b <= size_tm a0). omega.
      use_size_induction b bb Par1 Par2.
      exists bb.
      split; eauto.
      pick fresh y and apply Par_EtaC; eauto.
      eapply eta_swap_c with (x:=x); eauto. clear Fr0.
      move: (@Par_fv_co_preservation _ _ x _ _ h1 ltac:(eauto)) => h6.
      simpl in h6. rewrite union_notin_iff. split. 
      apply union_notin_iff in Fr. inversion Fr. clear Fr. fsetdec.
      clear Fr. fsetdec.
  - (* eta c / eta c *)
    pick fresh x for (L \u L0 \u L1).
    move: (H0 x ltac:(auto)) => E1.
    move: (H6 x ltac:(auto)) => E2.
    move: (H2 x ltac:(auto)) => Eb.
    rewrite E2 in E1.
    inversion E1. subst.
    rewrite E2 in Eb. inversion Eb. subst.
    move: (size_tm_open_tm_wrt_co_var a0 x) => Sb.
    match goal with
      [ H : open_tm_wrt_co ?a ?x = ?b |- _ ] =>
      assert (K : size_tm (open_tm_wrt_co a x) = size_tm b);
        [rewrite H; auto| simpl in K]
    end. 
    use_size_induction b ac Par1 Par2.
    exists ac. auto.
Qed.


(* Extra tactic? There's the same one above confluenze size.

Ltac use_size_induction b ac Par1 Par2 :=
  match goal with
  | [   IH : forall y: nat, ?T,
        H2 : Good S D,
        H3 : erased_tm b,
        H : Par S D b ?b0,
        H4 : Par S D b ?b1 |- _ ] =>
      move: (@IH (size_tm b) ltac:(omega) b ltac:(auto) _ _ _ H2 H3 H _ H4) => [ ac [Par1 Par2]]
  end.
*)

Lemma confluence : forall S D a a1, Good S D -> erased_tm a -> Par S D a a1 -> forall a2, Par S D a a2 -> exists b, Par S D a1 b /\ Par S D a2 b.
Proof.
  intros.
  eapply confluence_size; eauto.
Qed.


(* ---------------------------------------------------------------------- *)

Lemma multipar_Star : forall S D A B, multipar S D A B -> A = a_Star -> B = a_Star.
Proof.
  intros S D A B H. induction H. auto.
  inversion H; intro K; auto; try inversion K.
Qed.

Lemma multipar_Bullet : forall S D B, multipar S D a_Bullet B -> B = a_Bullet.
Proof.
  intros S D B H. dependent induction H. auto.
  inversion H; auto; try inversion K.
Qed.

(* OLD
Inductive Path_consistent : const -> tm -> tm -> Prop :=
  PC_Const : forall T, Path_consistent T (a_Const T) (a_Const T)
| PC_App   : forall T a1 rho a2 b1 b2,
    erased_tm a2 -> erased_tm b2 ->
    Path_consistent T a1 b1 ->
    Path_consistent T (a_App a1 rho a2) (a_App b1 rho b2)
| PC_CApp  : forall T a1 b1,
    Path_consistent T a1 b1 ->
    Path_consistent T (a_CApp a1 g_Triv) (a_CApp b1 g_Triv).
Hint Constructors Path_consistent. *)

Inductive Path_consistent : const -> tm -> tm -> Prop :=
  PC_Const : forall T, Path_consistent T (a_Const T) (a_Const T)
| PC_App   : forall T a1 a2 b1 b2,
    erased_tm a2 -> erased_tm b2 ->
    Path_consistent T a1 b1 ->
    Path_consistent T (a_App a1 Rel a2) (a_App b1 Rel b2)
| PC_AppIrrel : forall T a1 b1,
    Path_consistent T a1 b1 ->
    Path_consistent T (a_App a1 Irrel a_Bullet) (a_App b1 Irrel a_Bullet)
| PC_CApp  : forall T a1 b1,
    Path_consistent T a1 b1 ->
    Path_consistent T (a_CApp a1 g_Triv) (a_CApp b1 g_Triv).
Hint Constructors Path_consistent.

Lemma Path_consistent_Path1 : forall T a b, Path_consistent T a b -> Path T a.
Proof. induction 1; eauto using erased_lc. Qed.
Lemma Path_consistent_Path2 : forall T a b, Path_consistent T a b -> Path T b.
Proof. induction 1; eauto using erased_lc. Qed.

Lemma Path_consistent_erased1 : forall T a b, Path_consistent T a b -> erased_tm a.
Proof. induction 1; eauto. Qed.
Lemma Path_consistent_erased2 : forall T a b, Path_consistent T a b -> erased_tm b.
Proof. induction 1; auto. Qed.
Hint Resolve Path_consistent_erased1 Path_consistent_erased2 : erased.

Lemma Path_consistent_Refl :
  forall a T, Path T a -> erased_tm a -> Path_consistent T a a.
Proof. induction 1; intro h; inversion h; auto. Qed.

Lemma Path_consistent_Trans_aux :
  forall b T,  Path T b -> forall a c, Path_consistent T a b -> Path_consistent T b c -> Path_consistent T a c.
Proof. induction 1.
       all: intros a0 c0 h1 h2.
       all: inversion h1; inversion h2; subst; auto.
    - inversion h1; inversion h2; subst; auto.
    - inversion h1; inversion h2; subst; auto.
Qed.

Lemma Path_consistent_Trans : forall T a b c,
  Path_consistent T a b -> Path_consistent T b c -> Path_consistent T a c.
Proof. intros. eapply Path_consistent_Trans_aux with (b:=b). eapply Path_consistent_Path2; auto.
       eauto. eauto. eauto.
Qed.


Lemma Path_consistent_Sym :
  forall T a b, Path_consistent T a b -> Path_consistent T b a.
Proof.
  induction 1; eauto.
Qed.

Lemma Par_Path_consistent :
  forall S D a b T, Par S D a b -> Path T a -> erased_tm a -> Path_consistent T a b.
Proof.
  induction 1; intros P E; inversion E; inversion P; subst; eauto with lc;
    eauto using Path_consistent_Refl with erased.
  - move: (IHPar1 H10 H3) => h0.
    inversion h0.
  - move: (IHPar H7 H1) => h0.
    inversion h0.
  - move: (IHPar H6 H1) => h0.
    inversion h0.
Qed.

Lemma multipar_Path_consistent :
  forall S D a b T, multipar S D a b -> Path T a -> erased_tm a -> Path_consistent T a b.
Proof.
  intros S D a b T H. induction H.
  eauto using Path_consistent_Refl.
  intros h0 e0.
  move: (Par_Path_consistent H h0 e0) => h1.
  eapply Path_consistent_Trans with (b:=b); eauto;
  eauto using Path_consistent_Path2 with erased.
Qed.


Lemma Par_Path :
  forall S D a b T, Par S D a b -> Path T a -> Path T b.
Proof.
  induction 1; intros P; inversion P; subst; eauto with lc.
  - move: (IHPar1 H6) => h0.
    inversion h0.
  - move: (IHPar H5) => h0.
    inversion h0.
  - move: (IHPar H4) => h0.
    inversion h0.
Qed.

Lemma multipar_Path : forall S D a b T ,
    multipar S D a b -> Path T a -> Path T b.
Proof.
  intros S D a b T H. induction H. induction 1; intros; eauto.
  intros. eauto using Par_Path.
Qed.


    Lemma Par_Path_consistent_App : forall T G D a1 a2 b1 b2,
        Path_consistent T (a_App a1 Rel a2) (a_App b1 Rel b2) ->
        Par G D (a_App a1 Rel a2) ( a_App b1 Rel b2) ->
        Par G D a1 b1.
    Proof.
      intros. inversion H. subst.
      inversion H0; subst.
      - lc_inversion c. auto.
      - move: (Par_Path_consistent H9 (Path_consistent_Path1 H8) ltac: (eauto with erased)) => h0.
        inversion h0.
      - auto.
    Qed.

    Lemma Par_Path_consistent_AppIrrel : forall T G D a1 b1,
        Path_consistent T (a_App a1 Irrel a_Bullet) (a_App b1 Irrel a_Bullet) ->
        Par G D (a_App a1 Irrel a_Bullet) ( a_App b1 Irrel a_Bullet) ->
        Par G D a1 b1.
    Proof.
      intros. inversion H. subst.
      inversion H0; subst.
      - lc_inversion c. auto.
      - move: (Par_Path_consistent H6 (Path_consistent_Path1 H4) ltac: (eauto with erased)) => h0.
        inversion h0.
      - auto.
    Qed.

    Lemma Par_Path_consistent_CApp : forall T G D a1 b1,
        Path_consistent T (a_CApp a1 g_Triv) (a_CApp b1 g_Triv) ->
        Par G D (a_CApp a1 g_Triv) (a_CApp b1 g_Triv) ->
        Par G D a1 b1.
    Proof.
      intros. inversion H. subst.
      inversion H0; subst.
      - lc_inversion c. auto.
      - move: (Par_Path_consistent H6 (Path_consistent_Path1 H4) ltac: (eauto with erased)) => h0.
        inversion h0.
      - auto.
    Qed.

    Lemma Par_Path_consistent_App2 : forall T G D a1 a2 b1 b2,
        Path_consistent T (a_App a1 Rel a2) (a_App b1 Rel b2) ->
        Par G D (a_App a1 Rel a2) (a_App b1 Rel b2) ->
        Par G D a2 b2.
    Proof.
      intros. inversion H. subst.
      inversion H0; subst.
      - lc_inversion c. auto.
      - move: (Par_Path_consistent H9 (Path_consistent_Path1 H8) ltac: (eauto with erased)) => h0.
        inversion h0.
      - auto.
    Qed.


    Lemma multipar_Path_consistent_App : forall G D a1 a2 b1 b2 T,
      multipar G D (a_App a1 Rel a2) (a_App b1 Rel b2) ->
      Path_consistent T (a_App a1 Rel a2) (a_App b1 Rel b2) ->
      multipar G D a1 b1.
    Proof.
      intros.
      dependent induction H.
      - eauto.
      - move: (Par_Path_consistent H (Path_consistent_Path1 H1) ltac:(eauto 2 with erased)) => h0.
        inversion h0. subst.
        move: (Par_Path_consistent_App h0 H) => h1.
        eapply mp_step with (b:= b0). auto.
        eapply IHmultipar; eauto 2.
        eapply Path_consistent_Trans with (b := a_App a1 Rel a2).
        eapply Path_consistent_Sym; auto.
        auto.
    Qed.

    Lemma multipar_Path_consistent_AppIrrel : forall G D a1 b1 T,
      multipar G D (a_App a1 Irrel a_Bullet) (a_App b1 Irrel a_Bullet) ->
      Path_consistent T (a_App a1 Irrel a_Bullet) (a_App b1 Irrel a_Bullet) ->
      multipar G D a1 b1.
    Proof.
      intros.
      dependent induction H.
      - eauto.
      - move: (Par_Path_consistent H (Path_consistent_Path1 H1) ltac:(eauto 2 with erased)) => h0.
        inversion h0. subst.
        move: (Par_Path_consistent_AppIrrel h0 H) => h1.
        eapply mp_step with (b:= b0). auto.
        eapply IHmultipar; eauto 2.
        eapply Path_consistent_Trans with (b := a_App a1 Irrel a_Bullet).
        eapply Path_consistent_Sym; auto.
        auto.
    Qed.

     Lemma multipar_Path_consistent_App2 : forall G D a1 a2 b1 b2 T,
      multipar G D (a_App a1 Rel a2) (a_App b1 Rel b2) ->
      Path_consistent T (a_App a1 Rel a2) (a_App b1 Rel b2) ->
      multipar G D a2 b2.
    Proof.
      intros.
      dependent induction H.
      - eauto.
      - move: (Par_Path_consistent H (Path_consistent_Path1 H1) ltac:(eauto 2 with erased)) => h0.
        inversion h0. subst.
        move: (Par_Path_consistent_App2 h0 H) => h1.
        eapply mp_step with (b:= b3). auto.
        eapply IHmultipar; eauto 2.
        eapply Path_consistent_Trans with (b := a_App a1 Rel a2).
        eapply Path_consistent_Sym; auto.
        auto.
    Qed.

    Lemma multipar_Path_consistent_CApp : forall G D a1 b1 T,
      multipar G D (a_CApp a1 g_Triv) (a_CApp b1 g_Triv) ->
      Path_consistent T (a_CApp a1 g_Triv) (a_CApp b1 g_Triv) ->
      multipar G D a1 b1.
    Proof.
      intros.
      dependent induction H.
      - eauto.
      - move: (Par_Path_consistent H (Path_consistent_Path1 H1) ltac:(eauto 2 with erased)) => h0.
        inversion h0. subst.
        move: (Par_Path_consistent_CApp h0 H) => h1.
        eapply mp_step with (b:= b0). auto.
        eapply IHmultipar; eauto 2.
        eapply Path_consistent_Trans with (b := a_CApp a1 g_Triv).
        eapply Path_consistent_Sym; auto.
        auto.
    Qed.




Ltac binds_notbinds :=
    match goal with
    [ H0 : binds ?c (Ax ?T ?a) toplevel,
      H5 : forall (c : atom) a, not (binds c (Ax ?T a) an_toplevel) |- _  ] =>
      unfold not in H5; unfold toplevel in H0; unfold erase_sig in H0;
      apply binds_map_3 in H0; destruct H0 as (s' & EQ & B);
      destruct s'; simpl in EQ; inversion EQ; subst;
      apply H5 in B; contradiction
      end.


Lemma Par_Const : forall S D T b,
    Par S D (a_Const T) b -> b = a_Const T.
Proof.
  intros. dependent induction H; eauto.
Qed.

Lemma multipar_Const : forall S D T b,
    multipar S D (a_Const T) b ->
    (b = a_Const T).
Proof.
  intros S D T b H. dependent induction H; eauto using Par_Const.
Qed.


Lemma multipar_Pi : forall S D rho A B, multipar S D A B -> forall A1 A2,
      A = a_Pi rho A1 A2 -> exists B1 B2, B = (a_Pi rho B1 B2).
intros S D rho A B H. induction H. intros. subst. exists A1, A2. auto.
intros. subst.
inversion H; subst; destruct (IHmultipar _ _ eq_refl) as [B1 [B2 EQ]]; auto;
exists B1, B2; auto.
Qed.

Lemma multipar_CPi : forall S D A C, multipar S D A C -> forall A1 A2 A3 B, A = a_CPi (Eq A1 A2 A3) B -> exists B1 B2 B3 C2,
        C = (a_CPi (Eq B1 B2 B3) C2).
Proof.
  intros S D A C H. induction H; intros; subst.
  exists A1, A2, A3, B. auto.
  inversion H; subst; destruct (IHmultipar _ _ _ _ eq_refl) as [B1 [B2 [C2 EQ]]];
    auto; exists B1, B2, C2; auto.
Qed.


Lemma multipar_UAbs_Rel : forall S D a b x,
    x `notin` fv_tm_tm_tm a \u fv_tm_tm_tm b ->
    multipar S D (a_UAbs Rel a) b ->
    (exists b2, b = (a_UAbs Rel b2))
    \/ (exists a1, exists a2, multipar S D (a_UAbs Rel a) (a_UAbs Rel a1) /\
               open_tm_wrt_tm a1 (a_Var_f x) = a_App a2 Rel (a_Var_f x)).
Proof.
    intros S D a b x Fr H. dependent induction H.
    - left. exists a. auto.
    - destruct (Par_Abs_inversion_Rel H); subst.
      + destruct H1 as [ a' [K W]]. rewrite K in H.
      assert (h0 : x `notin` fv_tm_tm_tm (a_UAbs Rel a')). eapply Par_fv_preservation; eauto.
      simpl in h0.
      destruct (IHmultipar a' ltac:(eauto)) as [ [b2 EQ2] | [a1 [a2 [mp1 F2]]] ]; subst; clear IHmultipar.
      auto. left. exists b2. auto. right. exists a1, a2. split. eauto. auto.
      + destruct H1 as [ a' [K W]]. right. exists a, a'. split; eauto.
Qed.

Lemma multipar_UAbs_Irrel : forall S D a b x,
    x `notin` fv_tm_tm_tm a \u fv_tm_tm_tm b ->
    multipar S D (a_UAbs Irrel a) b ->
    (exists b2, b = (a_UAbs Irrel b2))
    \/ (exists a1, exists a2, multipar S D (a_UAbs Irrel a) (a_UAbs Irrel a1) /\
               open_tm_wrt_tm a1 (a_Var_f x) = a_App a2 Irrel a_Bullet).
Proof.
    intros S D a b x Fr H. dependent induction H.
    - left. exists a. auto.
    - destruct (Par_Abs_inversion_Irrel H); subst.
      + destruct H1 as [ a' [K W]]. rewrite K in H.
      assert (h0 : x `notin` fv_tm_tm_tm (a_UAbs Rel a')). eapply Par_fv_preservation; eauto.
      simpl in h0.
      destruct (IHmultipar a' ltac:(eauto)) as [ [b2 EQ2] | [a1 [a2 [mp1 F2]]] ]; subst; clear IHmultipar.
      auto. left. exists b2. auto. right. exists a1, a2. split. eauto. auto.
      + destruct H1 as [ a' [K W]]. right. exists a, a'. split; eauto.
Qed.

Lemma multipar_CAbs : forall S D A C, multipar S D A C -> forall A1 A2 A3 B, A = a_CAbs (Eq A1 A2 A3) B -> exists B1 B2 B3 C2,
        C = (a_CAbs (Eq B1 B2 B3) C2).
Proof.
  intros S D A C H. induction H; intros; subst.
  exists A1, A2, A3, B. auto.
  inversion H; subst; destruct (IHmultipar _ _ _ _ eq_refl) as [B1 [B2 [C2 EQ]]];
    auto; exists B1, B2, C2; auto.
Qed.

(* --------------------------------------------------- *)

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

(* --------------------------------------------------- *)


(* Proof that joinability implies consistency. *)

Ltac step_left := apply consistent_a_Step_R; [auto |intro N; inversion N; inversion H0]; fail.
Ltac step_right := apply consistent_a_Step_L; [auto | intro N; inversion N; inversion H0]; fail.

(* look for a multipar involvong a head form and apply the appropriate lemma for that
   head form. Note: for paths, the lemma has already been applied so we only need
   to look for a hypothesis about path consistency. *)
Ltac multipar_step SIDE EQ :=
  match goal with
  | [ SIDE : multipar _ _ a_Star _ |- _ ] =>
    apply multipar_Star in SIDE; auto; rename SIDE into EQ
  | [ SIDE : multipar _ _ (a_Pi _ _ _) _ |- _ ] =>
    destruct (multipar_Pi SIDE eq_refl) as [b1' [b2' EQ]]
  | [ SIDE : multipar _ _ (a_CPi ?phi _) _ |- _ ] =>
    try (destruct phi); destruct (multipar_CPi SIDE eq_refl)
      as (B1' & B2' & C1' & C2' &  EQ)
  | [ SIDE : multipar _ _ (a_Const ?T) _ |- _ ] =>
    apply multipar_Const in SIDE; auto; rename SIDE into EQ
  | [ SIDE : Path_consistent _ _ _ |- _ ] =>
    rename SIDE into EQ
  end.



Lemma join_consistent : forall S D a b, joins S D a b -> consistent a b.
Proof.
  intros.
  all: destruct H as (TT & Es & Ea & Eb & MSL & MSR).
  all: move: (erased_lc Ea) => lc_a.
  all: move: (erased_lc Eb) => lc_b.
  destruct a; try step_right; destruct b; try step_left; auto.
  (* 35 subgoals *)
  all: repeat
         let T  := fresh in
         let h0 := fresh in
         match goal with
           [ SIDE : multipar _ _ (a_App ?b1 ?rho ?b2) _,
               Eb : erased_tm (a_App ?b1 ?rho ?b2)  |- _ ] =>
           destruct (decide_Path (erased_lc Eb)) as [ [T h0] | NP ];
             [ eapply multipar_Path_consistent in SIDE; eauto | idtac ];
             clear Eb end.
    all: repeat
         let T  := fresh in
         let h0 := fresh in
         match goal with
           [ SIDE : multipar _ _ (a_CApp ?b1 ?b2) _, Eb: erased_tm (a_CApp ?b1 ?b2)  |- _ ] =>
           destruct (decide_Path (erased_lc Eb)) as [ [T h0] | NP ];
             [ eapply multipar_Path_consistent in SIDE; eauto | idtac ];
             clear Eb
         end.
  all: try solve [inversion Ea].
  all: try solve [inversion Eb].

  all: try multipar_step MSL EQ1.
  all: try multipar_step MSR EQ2.
  all: try solve [rewrite EQ1 in EQ2; inversion EQ2; try inversion H; auto].
  all: try solve [eapply consistent_a_Step_R; [auto | intros h0; inversion h0; unfold not in NP; eauto]].
  all: try solve [eapply consistent_a_Step_L; [auto | intros h0; inversion h0; unfold not in NP; eauto]].

  all: try match goal with
             [ H1: Path_consistent ?T1 ?a ?c, H2: Path_consistent ?T2 ?b ?c |- _ ] =>
             move: (Path_consistent_Path2 H1) => h0;
             move: (Path_consistent_Path2 H2) => h1;
    have EQ3: (T1 = T2); eauto using Path_unique; subst; eauto
  end.
  - rewrite EQ1 in EQ2; inversion EQ2. eauto.

  - destruct (multipar_Pi MSL eq_refl) as (B1 & B2 & EQ).
    destruct (multipar_Pi MSR eq_refl) as (B1' & B2' & EQ').
    subst.
    inversion EQ. inversion EQ'.
    subst. econstructor; eauto.
    inversion lc_a. auto.
    inversion lc_b. auto.
  - destruct phi.
    destruct (multipar_CPi MSL eq_refl) as (B1 & B2 & EQ).
    destruct (multipar_CPi MSR eq_refl) as (B1'' & B2'' & EQ').
    subst.
    inversion EQ. inversion EQ'.
    subst. econstructor; eauto.
    inversion lc_a. auto.
    inversion lc_b. auto.

Qed.

(*

a  -> b -->* c      d - by confluence
|     |      |      e - by induction
v     v      v
a2 -> d -->* e
*)

Lemma multipar_confluence_helper : forall S D a a1, Good S D -> erased_tm a -> multipar S D a a1
-> forall a2, Par S D a a2 -> exists e, Par S D a1 e /\ multipar S D a2 e.
Proof.
  intros S D a a1 Es E H. induction H.
  - intros. exists a2. split; eauto.
  - intros. destruct (confluence Es E H H1) as [d [L R]].
      inversion Es.
      assert (erased_tm b). eapply Par_erased_tm; eauto.
      destruct (IHmultipar H4 d) as [e [LL RR]]; auto.
      exists e. split; eauto.
Qed.

(*

a -->  b -->* c    d - by prior lemma
|      |      |    e - by induction.
v      v      v
*      *      *
a2 --> d -->* e

*)

Lemma multipar_confluence : forall S D a a1, Good S D -> erased_tm a -> multipar S D a a1
-> forall a2, multipar S D a a2 -> exists b, multipar S D a1 b /\ multipar S D a2 b.
Proof.
  intros S D a a1 Es Ea MP. induction MP.
intros.
 - exists a2. split. eauto. eauto.
 - intros.
   destruct (multipar_confluence_helper Es Ea H0 H) as [d [L R]].
   inversion Es.
   assert (Eb : erased_tm b). eapply Par_erased_tm; eauto.
   destruct (IHMP Eb d) as [e [LL RR]]; auto.
   exists e. split; eauto.
Qed.

Lemma multipar_append : forall S D a b c, multipar S D a b -> multipar S D b c -> multipar S D a c.
Proof.
  intros.
  induction H. auto.
  eauto.
Qed.

(*
    a   b   c
     \ / \ /
      ab  bc
       \ /
        d
 *)


Lemma join_transitive : forall S D a b, Good S D -> joins S D a b -> forall c, joins S D b c -> joins S D a c.
Proof.
  intros S D a b G H. destruct H as [ab [ES [Ea [Eb [Aab Bab]]]]].
  intros c H. destruct H as [bc [_ [_ [Ec [Bbc Cbc]]]]].
  destruct (multipar_confluence G Eb Bab Bbc) as [d [Babd Bbcd]].
  unfold joins.
  exists d. split. eauto. split. auto.
  split. auto. split; eapply multipar_append; eauto.
Qed.

Lemma join_symmetry: forall S D a b, joins S D a b -> joins S D b a.
Proof.
  intros S D a b H.
  destruct H as [ac h0].
  split_hyp.
  exists ac; eauto.
Qed.


Definition extends (G G2 : context) := exists G1, G = G1 ++ G2.

Lemma multipar_lc2: forall G D a1 a2, lc_tm a1 -> multipar G D a1 a2 -> lc_tm a2.
  induction 2; eauto.
  apply IHmultipar.
  eapply Par_lc2; apply H0.
Qed.


Hint Resolve multipar_context_independent : DB.

Lemma join_context_independent: forall G1 G2 D A B, erased_context G2 ->
                                             joins G1 D A B -> joins G2 D A B.
Proof.
  intros G1 G2 D A B E H.
  destruct H.
  split_hyp.
  unfold joins.
  exists x.
  repeat split; eauto with DB.
Qed.


Lemma Good_NoAssn: forall c G D phi, erased_sort (Co phi) -> Good G D -> c `notin` D -> Good ((c, Co phi) :: G) D.
Proof.
  intros c G D phi E H Fr.
  unfold Good in *.
  destruct H as (Es & M).
  split.
  + unfold erased_context in *.
    apply Forall_forall.
    intros x0 IN. destruct x0 as (y, s).
    inversion IN.
    - destruct phi. inversion H. subst. auto.
    - eapply Forall_forall in H; eauto.
      simpl in H. auto.
  + intros c1 c2. intros.
    assert (c <> c1). fsetdec.
    apply binds_cons_1 in H.
    destruct H as [[EQ _] | BI1]. fsetdec.
    edestruct (M c1) as (C & P1 & P2); eauto.
    exists C.
    repeat split;
      apply context_Par_irrelevance with (G1 := G)(D1 := D)(D2 := D); auto; try fsetdec;
        unfold sub_Axiom;
        intros;
        apply binds_cons; auto.
Qed.

Hint Resolve Good_NoAssn.

Hint Resolve multipar_context_independent.

Lemma Good_add_tm: forall G D x A,
    erased_tm A -> Good G D -> Good ((x, Tm A)::G ) D.
Proof.
  intros G D x A E H.
  unfold Good in *.
  split.
  + unfold erased_context in *.
    apply Forall_forall.
    intros x0 IN. destruct x0 as (y, s).
    inversion IN.
    - inversion H0. subst. apply erased_Tm. auto.
    - split_hyp.
      eapply Forall_forall in H; eauto.
      simpl in H. auto.
  + intros c1 A1 B1 T1 BI1 I1.
  destruct H as (Es & M).
  apply binds_cons_1 in BI1.
  destruct BI1 as [[_ EQ] | BI1]. inversion EQ.
  edestruct (M c1) as (C & P1 & P2); eauto.
  exists C. repeat split;
    apply context_Par_irrelevance with (G1 := G)(D1 := D); auto; try fsetdec;
    unfold sub_Axiom;
    intros;
    apply binds_cons; auto.
Qed.

Lemma Good_add_tm_2: forall G D x A, x `notin` dom G -> erased_tm A -> Good G D -> Good ((x, Tm A)::G ) (add x D).
Proof.
  intros G D x A FR E H.
  unfold Good in *.
  split.
  + unfold erased_context in *.
    apply Forall_forall.
    intros x0 IN. destruct x0 as (y, s).
    inversion IN.
    - inversion H0. subst. apply erased_Tm. auto.
    - split_hyp.
      eapply Forall_forall in H; eauto.
      simpl in H. auto.
  + intros c1 A1 B1 T1 BI1 I1.
  destruct H as (Es & M).
  apply binds_cons_1 in BI1.
  destruct BI1 as [[_ EQ] | BI1]. inversion EQ.
  edestruct (M c1) as (C & P1 & P2); eauto.
  move: (binds_In _ c1 _ _ BI1) => b0. fsetdec.
  exists C. repeat split;
    apply context_Par_irrelevance with (G1 := G)(D1 := D); auto; try fsetdec;
    unfold sub_Axiom;
    intros;
    apply binds_cons; auto.
Qed.


Lemma multipar_app_left_Rel:
  forall a a' c' S D, lc_tm a -> multipar S D a' c' -> multipar S D (a_App a Rel a') (a_App a Rel c').
Proof.
  induction 2; eauto; try done.
Qed.

Lemma multipar_capp_left: forall a a' S D, multipar S D a a' -> multipar S D (a_CApp a g_Triv) (a_CApp a' g_Triv).
Proof.
  induction 1; eauto; try done.
  Unshelve. auto.
Qed.

Lemma join_capp: forall a a' S D, joins S D a a' -> joins S D (a_CApp a g_Triv) (a_CApp a' g_Triv).
Proof.
  unfold joins.
  intros a a' S D H.
  destruct H as [ac h0].
  split_hyp.
  exists (a_CApp ac g_Triv).
  repeat split; eauto.
  apply multipar_capp_left; auto.
  apply multipar_capp_left; auto.
Qed.

Lemma multipar_app_lr_Rel: forall a a' c c' S D, lc_tm a -> lc_tm a' -> multipar S D a c -> multipar S D a' c' -> multipar S D (a_App a Rel a') (a_App c Rel c').
Proof.
  induction 3; eauto; try done.
  intros H1.
  apply multipar_app_left_Rel; auto.
  intros H3.
  apply (@mp_step S D _ (a_App b Rel a')); eauto.
  (have: lc_tm b by eapply Par_lc2; eauto); eauto.
  Unshelve. auto. auto.
Qed.

Lemma multipar_app_lr_Irrel: forall a c S D, lc_tm a -> multipar S D a c -> multipar S D (a_App a Irrel a_Bullet) (a_App c Irrel a_Bullet).
Proof.
  induction 2; eauto; try done.
  apply (@mp_step S D _ (a_App b Irrel a_Bullet)); eauto.
  (have: lc_tm b by eapply Par_lc2; eauto); eauto.
Qed.


Lemma join_app_Rel: forall a a' b b' S D, joins S D a b -> joins S D a' b' -> joins S D (a_App a Rel a') (a_App b Rel b').
Proof.
  unfold joins.
  intros a a' b b' S D H H0.
  destruct H as [ac h0].
  destruct H0 as [ac' h1].
  split_hyp.
  exists (a_App ac Rel ac').
  repeat split; eauto.
  apply multipar_app_lr_Rel; auto; try solve [eapply erased_lc; eauto].
  apply multipar_app_lr_Rel; auto; try solve [eapply erased_lc; eauto].
Qed.

Lemma join_app_Irrel: forall a b S D, joins S D a b -> joins S D (a_App a Irrel a_Bullet) (a_App b Irrel a_Bullet).
Proof.
  unfold joins.
  intros a b S D H.
  destruct H as [ac h0].
  split_hyp.
  exists (a_App ac Irrel a_Bullet).
  repeat split; eauto.
  apply multipar_app_lr_Irrel; auto; try solve [eapply erased_lc; eauto].
  apply multipar_app_lr_Irrel; auto; try solve [eapply erased_lc; eauto].
Qed.

(*
Lemma Par_iapp : forall G D a c y L,
    y `notin` fv_tm_tm_tm a \u L ->
    (forall x, x `notin` L -> RhoCheck Irrel x (open_tm_wrt_tm a (a_Var_f x))) ->
    Par G D (open_tm_wrt_tm a a_Bullet) c ->
    Par G D (a_UAbs Irrel a) (a_UAbs Irrel (close_tm_wrt_tm y c)).
Proof.
  intros.
  eapply (Par_Abs_exists); eauto.
  move: (H0 y ltac:(auto)) => h0.
  inversion h0.
  rewrite -(tm_subst_tm_tm_fresh_eq (open_tm_wrt_tm a (a_Var_f y)) a_Bullet y); eauto.
  rewrite - tm_subst_tm_tm_intro; eauto.
Qed.
 *)

Lemma multipar_UAbs_exists :  ∀ (x : atom) (G : context) (D : available_props)
       (rho : relflag) (a a' : tm),
    x `notin` fv_tm_tm_tm a
       → multipar G D (open_tm_wrt_tm a (a_Var_f x)) a'
         → multipar G D (a_UAbs rho a) (a_UAbs rho (close_tm_wrt_tm x a')).
Proof.
  intros.
  dependent induction H0.
  autorewrite with lngen. auto.
  eapply mp_step.
  eapply Par_Abs_exists with (x:=x); eauto.
  eapply IHmultipar; eauto. autorewrite with lngen. auto.
  autorewrite with lngen. auto.
Qed.

Lemma multipar_iapp : forall G D a c y L,
    y `notin` fv_tm_tm_tm a \u L ->
    (forall x, x `notin` L -> RhoCheck Irrel x (open_tm_wrt_tm a (a_Var_f x))) ->
    multipar G D (open_tm_wrt_tm a a_Bullet) c ->
    multipar G D (a_UAbs Irrel a) (a_UAbs Irrel (close_tm_wrt_tm y c)).
Proof.
  intros.
  eapply multipar_UAbs_exists; auto.
  move: (H0 y ltac:(auto)) => h0.
  inversion h0.
  rewrite -(tm_subst_tm_tm_fresh_eq (open_tm_wrt_tm a (a_Var_f y)) a_Bullet y); eauto.
  rewrite - tm_subst_tm_tm_intro; eauto.
Qed.

Lemma joins_iapp : forall S D a1 a2 L1 L2,
    (forall x, x `notin` L1 -> RhoCheck Irrel x (open_tm_wrt_tm a1 (a_Var_f x))) ->
    (forall x, x `notin` L2 -> RhoCheck Irrel x (open_tm_wrt_tm a2 (a_Var_f x))) ->
    joins S D (open_tm_wrt_tm a1 a_Bullet) (open_tm_wrt_tm a2 a_Bullet) ->
    joins S D (a_UAbs Irrel a1) (a_UAbs Irrel a2).
Proof.
  intros.
  destruct H1 as (C & ES & T1 & T2 & P1 & P2).
  unfold joins.
  pick fresh y.
  exists (a_UAbs Irrel (close_tm_wrt_tm y C)).
  repeat split; eauto.
  eapply (@erased_a_Abs L1).
  intros.
  move: (H x H1) => RC. inversion RC.
  rewrite -(tm_subst_tm_tm_fresh_eq (open_tm_wrt_tm a1 (a_Var_f x)) a_Bullet x); eauto.
  rewrite - tm_subst_tm_tm_intro; eauto.
  move: (fv_tm_tm_tm_open_tm_wrt_tm_lower a1 (a_Var_f x)) => h0. fsetdec. auto.
  eapply (@erased_a_Abs L2).
  intros.
  move: (H0 x H1) => RC. inversion RC.
  rewrite -(tm_subst_tm_tm_fresh_eq (open_tm_wrt_tm a2 (a_Var_f x)) a_Bullet x); eauto.
  rewrite - tm_subst_tm_tm_intro; eauto.
  move: (fv_tm_tm_tm_open_tm_wrt_tm_lower a2 (a_Var_f x)) => h0. fsetdec.
  auto.
  eapply (multipar_iapp _ _ H). eauto.
  eapply (multipar_iapp _ _ H0). eauto.
  Unshelve. eauto. eauto.
Qed.

Lemma multipar_App_destruct_Rel : forall S D a1 a2 c,
    multipar S D (a_App a1 Rel a2) c ->
    (exists a1' a2',
        multipar S D (a_App a1 Rel a2) (a_App (a_UAbs Rel a1') Rel a2') /\
        multipar S D a1 (a_UAbs Rel a1') /\
        multipar S D a2 a2' /\
        multipar S D (open_tm_wrt_tm a1' a2') c) \/
    (exists a1' a2',
        multipar S D (a_App a1 Rel a2) (a_App a1' Rel a2') /\
        multipar S D a1 a1' /\
        multipar S D a2 a2').
Proof.
  intros. dependent induction H.
  right.
  exists a1, a2. split; auto.
  inversion H.
  + subst. eauto.
  + subst. left.
    exists a', b'. split; auto.
    assert (lc_tm a1). eapply Par_lc1. eauto.
    assert (lc_tm a2). eapply Par_lc1. eauto.
    eapply multipar_app_lr_Rel; eauto.
    split.
    eapply mp_step; eauto.
    split; eauto.
  +
    assert (lc_tm a1). eapply Par_lc1. eauto.
    assert (lc_tm a2). eapply Par_lc1. eauto.
    subst. destruct (IHmultipar a' b') as [[a1' [a2' [P1 [P2 [P3 P4]]]]] |
                                                [a1' [a2' [P1 [P2 P3]]]]] ; auto.
    ++ clear IHmultipar. left.
       exists a1', a2'.
       repeat split; eauto.
    ++ clear IHmultipar. right.

       exists a1', a2'.
       repeat split; eauto.
Unshelve.
all: exact S.
Qed.

Lemma multipar_App_destruct_Irrel : forall S D a1 c,
    multipar S D (a_App a1 Irrel a_Bullet) c ->
    (exists a1',
        multipar S D (a_App a1 Irrel a_Bullet) (a_App (a_UAbs Irrel a1') Irrel a_Bullet) /\
        multipar S D a1 (a_UAbs Irrel a1') /\ multipar S D (open_tm_wrt_tm a1' a_Bullet) c) \/
    (exists a1',
        multipar S D (a_App a1 Irrel a_Bullet) (a_App a1' Irrel a_Bullet) /\
        multipar S D a1 a1').
Proof.
  intros. dependent induction H.
  right.
  exists a1. split; auto.
  inversion H.
  + subst. eauto.
  + subst. left.
    exists a'. split; auto.
    assert (lc_tm a1). eapply Par_lc1. eauto.
    eapply multipar_app_lr_Irrel; eauto.
    split.
    eapply mp_step; eauto.
    eauto.
  +
    assert (lc_tm a1). eapply Par_lc1. eauto.
    subst. edestruct (IHmultipar a'); auto.
    ++ clear IHmultipar. left. destruct H1 as [a1' K].
       exists a1'. inversion K. clear K. inversion H2. clear H2.
       repeat split; eauto.
    ++ clear IHmultipar. right. destruct H1 as [a1' K].
       exists a1'. inversion K. clear K.
       repeat split; eauto.
Unshelve.
all: exact S.
Qed.

Lemma consistent_mutual:
  (forall S a A,   Typing S a A -> True) /\
  (forall S phi,   PropWff S phi -> True) /\
  (forall S D p1 p2, Iso S D p1 p2 -> Good S D -> (forall A1 B1 T1 A2 B2 T2, p1 = Eq A1 B1 T1 -> p2 = Eq A2 B2 T2-> (joins S D A1 A2 /\ joins S D B1 B2 /\ joins S D T1 T2))) /\
  (forall S D A B T,   DefEq S D A B T -> Good S D -> joins S D A B) /\
  (forall S,       Ctx S -> True).
Proof.
  apply typing_wff_iso_defeq_mutual; eauto; try done.
  - intros G D A1 B1 A A2 B2 d H d0 H0 H1 A0 B0 T1 A3 B3 T2 H2 H3.
    inversion H2; subst; clear H2.
    inversion H3; subst; clear H3.
    repeat split; eauto.
    exists T2; eauto.
    have et: erased_tm T2.
    apply DefEq_regularity in d.
    pose K := (second typing_erased_mutual) _ _ d A0 A3 T2.
    apply K; auto.
    repeat split; auto.
    have C: Ctx G by eauto.
    unfold erased_context.
    apply Forall_forall.
    intros. destruct x. destruct s.
    apply binds_to_Typing in H2.
    apply Typing_erased in H2.
    eapply erased_Tm. auto. auto.
    destruct phi. apply binds_to_PropWff in H2.
    inversion H2.
    eapply erased_Co; eauto using Typing_erased. auto.
  - intros G D A1 A2 A B d H p H0 p0 H1 H2 A0 B1 T1 A3 B2 T2 H3 H4.
    inversion H4; subst; clear H4.
    inversion H3; subst; clear H3.
    inversion p; subst.
    inversion H2.
    have lc1: lc_tm A0 by eapply Typing_lc in H7; split_hyp; eauto.
    have lc2: lc_tm B1 by eapply Typing_lc in H8; split_hyp; eauto.
    repeat split; eauto.
    + exists A0.
      repeat split; eauto; try solve [eapply (Typing_erased); eauto]; eauto.
    + exists B1.
      repeat split; eauto; try solve [eapply (Typing_erased); eauto]; eauto.
  - intros G D5 phi1 phi2 B1 B2 d H H0 A1 B0 T1 A2 B3 T2 H1 H2.
    destruct phi1.
    destruct phi2.
    inversion H1; subst; clear H1.
    inversion H2; subst; clear H2.
    destruct H as [Bc h0]; auto.
    split_hyp.
    pose K1 := multipar_CPi H3 eq_refl.
    destruct K1 as [B1' [B2' [B3' [Bc' h0]]]].
    subst.
    pose K1 := multipar_CPi_phi_proj H3.
    pose K2 := multipar_CPi_phi_proj H4.
    split_hyp.
    repeat split; eauto.
    + exists B1'.
      inversion H2; subst; clear H2.
      inversion H1; subst; clear H1.
      repeat split; eauto.
    + exists B2'.
      inversion H2; subst; clear H2.
      inversion H1; subst; clear H1.
      repeat split; eauto.
    + exists B3'.
      inversion H2; subst; clear H2.
      inversion H1; subst; clear H1.
      repeat split; eauto.
  - (* assn *)
    intros G D a b A c c0 H b0 i H0.
    destruct H0 as (Es & M).
    edestruct (M c); eauto.
    split_hyp.
    unfold erased_context in Es.
    move:
      (@Forall_forall _ (λ (p : (atom*sort)), let (_, s) := p in erased_sort s) G) => [h0 _].
    move: (h0 Es _ b0) => h1.
    inversion h1.
    unfold joins. exists x. repeat split; eauto.
  - (* refl *)
    intros G D a A t H H0.
    inversion H0.
    unfold joins. exists a.
    repeat split; try solve [eapply (Typing_erased); eauto]; eauto.
  - (* symmetry *)
    intros G D a b A d H H0.
    unfold joins in *. destruct H as [c [L R]]; auto.
    exists c. tauto.
  - (* transitivity *)
    intros. eapply join_transitive; auto.
  - (* confluence *)
    intros G. intros.
    inversion H1.
    unfold joins in *. subst.
    have p: Par G D a1 a2.
    { inversion b.
      eapply Par_Beta; eauto 2. eauto using Value_lc.
      eapply Par_CBeta; eauto 2.
      eapply Par_Axiom; eauto 2.
      }
    destruct (confluence H1 (Typing_erased t) p p) as [ac [h0 h1]].
    exists ac; eauto.
    pose K2 := Typing_erased t0.
    repeat split; eauto.
    eapply Typing_erased; eauto.
  - (* pi-cong *)
    intros L G D rho A1 B1 A2 B2 d H d0 H0 _ _ t H1 t0 H2 H3.
    inversion H3.
    have e0: erased_tm (a_Pi rho A1 B1). eapply Typing_erased; eauto.
    inversion e0. subst.
    pose Ih1 := H H3.
    pick fresh x for (L \u (fv_tm_tm_tm B1) \u (fv_tm_tm_tm B2) \u dom G).
    assert (G' : Good ([(x, Tm A1)] ++ G) D).
    { apply Good_add_tm; auto. }
    have: x `notin` L; auto => fr.
    pose Ih2 := H0 x fr G'.
    destruct H as [A'' h1]; auto; subst.
    destruct Ih2 as [B'' h2].
    split_hyp.
    exists (a_Pi rho A'' (close_tm_wrt_tm x B'')); eauto.
    repeat split; eauto 1.
    + apply (@erased_a_Pi L); try solve [apply h2; auto]; try solve [apply h1; auto]; eauto.
      intros x0 h4.
      assert (G'' : Good ([(x0, Tm A1)] ++ G) D).
      apply Good_add_tm; auto.
      pose Ih2 := H0 x0 h4 G''.
      destruct Ih2 as [C'' h3]; eauto.
      apply h3.
    + apply multipar_Pi_exists; auto.
      apply (lc_a_Pi_exists x); apply erased_lc; auto.
      eapply multipar_context_independent; eauto.
    + apply multipar_Pi_exists; auto.
      apply (lc_a_Pi_exists x); apply erased_lc; auto.
      eapply multipar_context_independent; eauto.
  - (* abs-cong *)
    intros L G D rho b1 b2 A1 B IHDefEq H1 t _ RC1 RC2 GOOD.
    inversion GOOD.
    have e0: erased_tm A1. eapply Typing_erased; eauto.
    pick fresh x for (L \u (fv_tm_tm_tm b1) \u (fv_tm_tm_tm b2)).
    assert (G' : Good ([(x, Tm A1)] ++ G) D).
    apply Good_add_tm; auto.
    have: x `notin` L; auto => fr.
    pose Ih2 := H1 x fr G'.
    destruct Ih2 as [B'' h2].
    split_hyp.
    exists (a_UAbs rho (close_tm_wrt_tm x B'')); eauto.
    repeat split; eauto 1.
    + apply (@erased_a_Abs L); try solve [apply h2; auto]; try solve [apply h1; auto]; eauto.
      intros x0 h4.
      assert (G'' : Good ([(x0, Tm A1)] ++ G) D).
      apply Good_add_tm; auto.
      pose Ih2 := H1 x0 h4 G''.
      destruct Ih2 as [C'' h3]; eauto.
      apply h3.
    + apply (@erased_a_Abs L); try solve [apply h2; auto]; try solve [apply h1; auto]; eauto.
      intros x0 h4.
      assert (G'' : Good ([(x0, Tm A1)] ++ G) D).
      apply Good_add_tm; auto.
      pose Ih2 := H1 x0 h4 G''.
      destruct Ih2 as [C'' h3]; eauto.
      apply h3.
    + apply multipar_Abs_exists; auto.
      apply (lc_a_UAbs_exists x); apply erased_lc; auto.
      eapply multipar_context_independent; eauto.
    + apply multipar_Abs_exists; auto.
      apply (lc_a_UAbs_exists x); apply erased_lc; auto.
      eapply multipar_context_independent; eauto.
  - intros G D a1 a2 b1 b2 d H d0 H0 p H1 H2.
    apply join_app_Rel; auto.
  - intros G D a1 b1 B a A d H t H0 H1.
    inversion H1.
    apply join_app_Irrel; auto.
  - intros G D A1 A2 rho B1 B2 H IHDefEq GOOD.
    inversion GOOD.
    destruct IHDefEq; auto.
    split_hyp.
    pose K1 := multipar_Pi H5 eq_refl.
    destruct K1 as [A' [B' h0]].
    subst.
    inversion H3; inversion H4; subst.
    apply multipar_Pi_A_proj in H5.
    apply multipar_Pi_A_proj in H6.
    exists A'; eauto.
    apply erased_lc; eauto.
    apply erased_lc; eauto.
  - intros G D B1 a1 B2 a2 rho A1 A2 H IHDefEq1 H0 IHDefEq2 GOOD.
    inversion GOOD.
    destruct IHDefEq1; auto.
    destruct IHDefEq2 as [ac h0]; auto.
    split_hyp.
    pose K1 := multipar_Pi H11 eq_refl.
    destruct K1 as [A' [B' h0]].
    subst.
    inversion H9.
    inversion H10; subst.
    apply (multipar_Pi_B_proj) in H11.
    apply (multipar_Pi_B_proj) in H12.
    destruct H11 as [L1 h9].
    destruct H12 as [L2 h10].
    pick_fresh x.
    exists (open_tm_wrt_tm B' ac).


Ltac subst_tm_erased_open x :=
  let K := fresh in
  let h0 := fresh in
  match goal with
  | [H16 : ∀ x : atom, x `notin` ?L0 →
                       erased_tm  (open_tm_wrt_tm ?B (a_Var_f x)),
     H2 : erased_tm ?a
     |- erased_tm (open_tm_wrt_tm ?B ?a) ] =>
    have: x `notin` L0; auto => h0;
    pose K := subst_tm_erased x H2 (H16 x h0);
    clearbody K;
    repeat rewrite tm_subst_tm_tm_open_tm_wrt_tm in K; auto; try solve [apply erased_lc; auto];
    simpl in K;
    destruct eq_dec; try congruence;
    rewrite tm_subst_tm_tm_fresh_eq in K; auto
  end.

Ltac multipar_subst_open x :=
  let K := fresh in
  let h1 := fresh in
  let h0 := fresh in
  let h2 := fresh in
  let lc1 := fresh in
  match goal with
    [
      H2 : erased_tm ?a1,
      H4 : multipar ?G ?D ?a1 ?ac,
      H18: ∀ x : atom, x `notin` ?L0 → erased_tm (open_tm_wrt_tm ?B1 (a_Var_f x)),
      H9 : ∀ x : atom,
       x `notin` ?L1
       → multipar ?G ?D (open_tm_wrt_tm ?B1 (a_Var_f x)) (open_tm_wrt_tm ?B' (a_Var_f x))
    |-
    multipar ?G ?D (open_tm_wrt_tm ?B1 ?a1) (open_tm_wrt_tm ?B' ?ac) ] =>
      have: x `notin` L0; auto => h0;
      have: x `notin` L1; auto => h1;

      pose K := multipar_subst3 x H2 H4 (H18 x h0) (H9 x h1);
      clearbody K;
      (have: lc_tm a1 by eapply erased_lc; eauto) => lc1;
      repeat rewrite tm_subst_tm_tm_open_tm_wrt_tm in K;
      eauto;try solve [eapply multipar_lc2; eauto | eapply multipar_lc2; eauto];
      simpl in K;
      destruct eq_dec; try congruence;
      repeat rewrite tm_subst_tm_tm_fresh_eq in K; auto
   end.


  repeat split; eauto.
    + subst_tm_erased_open x.
    + subst_tm_erased_open x.
    + multipar_subst_open x.
    + multipar_subst_open x.
  - (* cpi-cong *)
    intros L G D phi1 A phi2 B H hi0 H1 IHDefEq H2 _ _ t _ _ GOOD .
    destruct phi1.
    destruct phi2.
    pick_fresh c.
    match goal with
      | [ H : Iso G D (Eq a b A0) (Eq a0 b0 A1) |- _ ] =>
        destruct (hi0 GOOD a b A0 a0 b0 A1) as [hi1 [hi2 hi3]]; auto
    end.
    have EC : erased_sort (Co (Eq a b A0)).
    { inversion H2. apply erased_Co; eapply Typing_erased; eauto. }
    destruct (IHDefEq c) as [Ac h1]; eauto.
    + apply Good_NoAssn; auto.
    + split_hyp.
      unfold joins in *.
      destruct hi1 as [Aco h0'].
      destruct hi2 as [Bco h1'].
      destruct hi3 as [Tco h2'].
      split_hyp.
      exists (a_CPi (Eq Aco Bco Tco) (close_tm_wrt_co c Ac)); eauto.
      repeat split; eauto 1.
      * apply (@erased_a_CPi (L \u D)); eauto.
        intros c0 Hi5.
        destruct (IHDefEq c0) as [Ac' h2']; auto; subst.
        apply Good_NoAssn; auto.
        apply h2'.
      * apply (@erased_a_CPi (L \u D)); eauto.
        intros c0 Hi5.
        destruct (IHDefEq c0) as [Ac' h2']; auto; subst.
        apply Good_NoAssn; auto.
        apply h2'.
      * (* Ltac context_independence c := *)
(*        eapply multipar_context_independent; eauto.
        intros x; intros; assert (x <> c); [fsetdec|
        match goal with
          [ H23 : binds ?x (Co (Eq (a_Const ?F) ?a ?A4)) ([(c, Co (Eq ?A0 ?B0 ?A1))] ++ ?G) |- _ ] =>
              simpl in H23;
              edestruct (binds_cons_1 _ x c _ _ G H23) as [[h0 h1] | h2];
              [contradiction| auto]
        end].   *)
        Ltac multipar_CPi c :=
        apply multipar_CPi_exists; auto;
        [ apply (lc_a_CPi_exists c); try constructor; apply erased_lc; auto |
          eapply multipar_context_independent; eauto].
        multipar_CPi c.
      * multipar_CPi c.
  - intros L G D a b phi1 B hi0 IHDefEq H1 _ GOOD.
    destruct phi1.
    pick_fresh c.
    have EC : erased_sort (Co (Eq a0 b0 A)).
    { inversion H1. apply erased_Co; eapply Typing_erased; eauto. }
    inversion GOOD.
    destruct (IHDefEq c) as [Ac h1]; auto.
    + apply Good_NoAssn; auto.
    + split_hyp.
      unfold joins in *.
      exists (a_UCAbs (close_tm_wrt_co c Ac)); eauto.
      split_hyp.
      repeat split; eauto 1.
      * apply (@erased_a_CAbs (L \u D)); eauto.
        intros c0 Hi6.
        destruct (IHDefEq c0) as [Ac' h2']; auto; subst.
        apply Good_NoAssn; auto.
        apply h2'.
      * apply (@erased_a_CAbs (L \u D)); eauto.
        intros c0 Hi5.
        destruct (IHDefEq c0) as [Ac' h2']; auto; subst.
        apply Good_NoAssn; auto.
        apply h2'.
      * apply multipar_CAbs_exists; auto.
        apply (lc_a_UCAbs_exists c); try constructor; apply erased_lc; auto.
        eapply multipar_context_independent; eauto.
      * apply multipar_CAbs_exists; auto.
        apply (lc_a_UCAbs_exists c); try constructor; apply erased_lc; auto.
        eapply multipar_context_independent; eauto.
  - intros G D a1 b1 B a b A d H p H0 H1.
    apply join_capp; auto.
  - intros G D B1 B2 A1 A2 A A1' A2' A' H0 IHDefEq hi1 IHDefEq2 hi0 IHDefEq3 GOOD.
    destruct IHDefEq as [Ac h0]; eauto.
    split_hyp.
    inversion GOOD.
    match goal with
      [ H1 : erased_tm (a_CPi (Eq A1 A2 A) B1),
        H2 : erased_tm (a_CPi (Eq A1' A2' A') B2),
        H3 :  multipar G D (a_CPi (Eq A1 A2 A) B1) Ac,
        H4 : multipar G D (a_CPi (Eq A1' A2' A') B2) Ac |- _ ] =>
      pose K1 := multipar_CPi H3 eq_refl;
      destruct K1 as [B1' [B2' [B3' [Bc' h0]]]];
      subst;
      inversion H1;
      inversion H2; subst;
      apply multipar_CPi_B_proj in H3;
      apply multipar_CPi_B_proj in H4;
      destruct H3 as [L1 H3];
      destruct H4 as [L2 H4]
    end.
    pick_fresh c.
    exists (open_tm_wrt_co Bc' g_Triv).
    have: c `notin` L; auto => h.
    have: c `notin` L0; auto => h0.
    repeat split; eauto 1.
    + Ltac erased_open_tm_wrt_co c B1 :=
        let K:= fresh in
        match goal with
        [ h : c `notin` ?L, H11 :  ∀ c : atom, c `notin` ?L → erased_tm (open_tm_wrt_co B1 (g_Var_f c)) |- _ ] =>
        pose K := subst_co_erased c lc_g_Triv (H11 c h);
        clearbody K;
        repeat rewrite co_subst_co_tm_open_tm_wrt_co in K; auto;
        simpl in K;
        destruct eq_dec; try congruence;
        rewrite co_subst_co_tm_fresh_eq in K; auto
        end.
      erased_open_tm_wrt_co c B1.
    + erased_open_tm_wrt_co c B2.
    + Ltac multipar_open_tm_wrt_co c B1 :=
        let K:= fresh in
        let h1:= fresh in
        match goal with
        [ H3 : ∀ c : atom, c `notin` ?L1 →
                           multipar ?G ?D (open_tm_wrt_co B1 (g_Var_f c)) (open_tm_wrt_co ?Bc' (g_Var_f c))
          |- _ ] =>
        have: c `notin` L1; auto => h1;
        pose K := multipar_subst4 c lc_g_Triv (H3 c h1);
        clearbody K;
        repeat rewrite co_subst_co_tm_open_tm_wrt_co in K; eauto;
        simpl in K;
        destruct eq_dec; try congruence;
          repeat rewrite co_subst_co_tm_fresh_eq in K; auto
        end.
      multipar_open_tm_wrt_co c B1.
    + multipar_open_tm_wrt_co c B2.
  - intros G D A' B' a' A B a d H i H0 H1.
    destruct (H0 H1 A B a A' B' a'); auto.
    move: (H H1) => h0.
    split_hyp.
    have h1 : joins G D A' B; eauto.
    apply join_transitive with (b := A); eauto.
    apply join_symmetry; auto.
    apply join_transitive with (b := B); eauto.
  - intros G D A A' a b a' b' i H H0.
    destruct (H H0 a b A a' b' A'); auto.
    destruct H2; auto.
    Unshelve. all: auto.
  - intros.
    inversion H0.
    unfold joins.
    have: Par G D b b. eauto using Typing_lc1. move => Pb.
    exists b. repeat split; eauto 2 using Typing_erased.
    + pick fresh x and apply erased_a_Abs.
      rewrite e; auto. eauto 3 using Typing_erased. eauto.
    + eapply mp_step with (b := b); eauto.
  - intros.
    inversion H0.
    unfold joins.
    have: Par G D b b. eauto using Typing_lc1. move => Pb.
    exists b. repeat split; eauto 2 using Typing_erased.
    + pick fresh x and apply erased_a_Abs.
      rewrite e; auto. eauto 3 using Typing_erased. erewrite e.
      constructor. simpl. fsetdec. fsetdec.
    + eapply mp_step with (b := b); eauto.
  - intros.
    inversion H0.
    unfold joins.
    have: Par G D b b. eauto using Typing_lc1. move => Pb.
    exists b. repeat split; eauto 2 using Typing_erased.
    + pick fresh x and apply erased_a_CAbs.
      rewrite e; auto. eauto 3 using Typing_erased.
    + eapply mp_step with (b := b); eauto.

(* Left/Right
  - intros.
    move: (H3 ltac:(auto)) => [ c hyp ]. split_hyp.
    match goal with
      [ H9 : multipar G D (a_App a Rel b) c |- _ ] =>
      have P : Path T (a_App a Rel b); eauto using Typing_lc1;
      move: (multipar_Path_consistent H9 P ltac:(eauto with erased)) => Pc;
      inversion Pc; subst;
      move: (multipar_Path_consistent_App H9 Pc) => P1 end.
    match goal with
      [ H10 : multipar G D (a_App a' Rel b') ?c |- _ ] =>
      have P' : Path T (a_App a' Rel b'); eauto using Typing_lc1;
      move: (multipar_Path_consistent H10 P' ltac:(eauto with erased)) => Pc';
      inversion Pc'; subst;
        move: (multipar_Path_consistent_App H10 Pc') => P2
    end.
    unfold joins.
    exists b1. repeat split; eauto 2 with erased.
  - intros.
    move: (H3 ltac:(auto)) => [ c hyp ]. split_hyp.
    match goal with
      [ H9 : multipar G D (a_App a ?r ?b) c |- _ ] =>
      have P : Path T (a_App a r b); eauto using Typing_lc1;
      move: (multipar_Path_consistent H9 P ltac:(eauto with erased)) => Pc;
      inversion Pc; subst;
      move: (multipar_Path_consistent_App H9 Pc) => P1 end.
    match goal with
      [ H10 : multipar G D (a_App a' ?r ?b') ?c |- _ ] =>
      have P' : Path T (a_App a' r b'); eauto using Typing_lc1;
      move: (multipar_Path_consistent H10 P' ltac:(eauto with erased)) => Pc';
      inversion Pc'; subst;
        move: (multipar_Path_consistent_App H10 Pc') => P2
    end.
    unfold joins.
    exists b1. repeat split; eauto 2 with erased.
  - intros.
    move: (H3 ltac:(auto)) => [ c hyp ]. split_hyp.
    match goal with
      [ H9 : multipar G D (a_App a ?r ?b) c |- _ ] =>
      have P : Path T (a_App a r b); eauto using Typing_lc1;
      move: (multipar_Path_consistent H9 P ltac:(eauto with erased)) => Pc;
      inversion Pc; subst;
      move: (multipar_Path_consistent_App2 H9 Pc) => P1 end.
    match goal with
      [ H10 : multipar G D (a_App a' ?r ?b') ?c |- _ ] =>
      have P' : Path T (a_App a' r b'); eauto using Typing_lc1;
      move: (multipar_Path_consistent H10 P' ltac:(eauto with erased)) => Pc';
      inversion Pc'; subst;
        move: (multipar_Path_consistent_App2 H10 Pc') => P2
    end.
    unfold joins.
    exists b2. repeat split; eauto 2 with erased.
  - intros.
    move: (H2 ltac:(auto)) => [ c hyp ]. split_hyp.
    match goal with
      [ H9 : multipar G D (a_CApp a ?b) c |- _ ] =>
      have P : Path T (a_CApp a b); eauto using Typing_lc1;
      move: (multipar_Path_consistent H9 P ltac:(eauto with erased)) => Pc;
      inversion Pc; subst;
      move: (multipar_Path_consistent_CApp H9 Pc) => P1 end.
    match goal with
      [ H10 : multipar G D (a_CApp a' ?b') ?c |- _ ] =>
      have P' : Path T (a_CApp a' b'); eauto using Typing_lc1;
      move: (multipar_Path_consistent H10 P' ltac:(eauto with erased)) => Pc';
      inversion Pc'; subst;
        move: (multipar_Path_consistent_CApp H10 Pc') => P2
    end.
    unfold joins.
    exists b1. repeat split; eauto 2 with erased.  *)
Qed.


Lemma consistent_defeq: forall S D A B T,   DefEq S D A B T -> Good S D -> joins S D A B.
Proof.
  apply consistent_mutual.
Qed.

(* ------------------------------------------------------- *)

Lemma no_aAbs : forall G rho A' a A, Typing G (a_Abs rho A' a) A -> False.
Proof.
  intros. dependent induction H. by apply: IHTyping1.
Qed.

Lemma no_aCAbs : forall G A' a A, Typing G (a_CAbs A' a) A -> False.
Proof.
  intros. dependent induction H; by apply: IHTyping1.
Qed.



Lemma Good_nil : forall D, Good nil D.
Proof.
  intro D.
  unfold Good. split.  done.
  intros. inversion H.
Qed.

Lemma consistent_Star : forall A0,
    consistent a_Star A0 -> value_type A0 -> A0 = a_Star.
Proof.
  intros A0 C V.
  destruct A0; try destruct rho;
    simpl in *; inversion C; inversion V.
  all: subst; auto.
  all: try solve [inversion H].
  all: try solve [inversion H2].
  all: done.
Qed.


Definition irrelevant G D (a : tm) :=
  (forall x A, binds x (Tm A) G -> x `notin` fv_tm a) /\ Good G D.

Lemma irrelevant_Good : forall G D a, irrelevant G D a -> Good G D.
intros. inversion H.
auto.
Qed.
(*
Ltac impossible_defeq A B :=
  match goal with
  | h0 : DefEq G A B a_Star =>
    apply consistent_defeq in h0; eauto;
    apply join_consistent in h0;
 *)

Ltac impossible_Path :=
  match goal with
     [H : Path ?T (a_Pi _ _ _) |- _] => inversion H
   | [H : Path ?T a_Star |- _] => inversion H
   | [H : Path ?T (a_CPi _ _) |- _] => inversion H
  end.


(* When we have a defeq in the context between two value types, show that it
   can't happen. *)
Ltac impossible_defeq :=
  let h0 := fresh in
  let VT := fresh in
  let VT2 := fresh in
  match goal with
  | [ H : DefEq ?G (dom ?G) ?B ?A ?C |- _ ] =>
    pose h0:= H; clearbody h0;
    apply consistent_defeq in h0; eauto;
    [apply join_consistent in h0;
     destruct (DefEq_lc H) as (l0 & l1 & l2); inversion l0; inversion l1; subst;
     have VT: value_type A; eauto;
     have VT2 : value_type B; eauto;
     inversion h0; subst; try impossible_Path;
     eauto; try done | eapply irrelevant_Good; eauto]
  end.


Lemma canonical_forms_Star : forall G a, irrelevant G (dom G) a ->
    Typing G a a_Star -> Value a -> value_type a.
Proof.
  intros G a IR H V. induction V; auto.
  - subst. assert False. eapply no_aAbs. eauto 2. done.
  - subst. apply invert_a_UAbs in H; eauto.
    destruct H as [A1 [B2 [H _]]].
    impossible_defeq.
  - subst. apply invert_a_UAbs in H; eauto.
    destruct H as (A1 & A2 & DE & TA1 & TA2).
    impossible_defeq.
  - subst. assert False. eapply  no_aAbs. eauto 2. done.
  - subst.  assert False. eapply no_aCAbs. eauto 2. done.
  - subst. apply invert_a_UCAbs in H; eauto.
    destruct H as [a0 [b [T [B1 [_ [H _]]]]]].
    impossible_defeq.
  - eauto.
  - eauto.
Qed.



Lemma DefEq_Star: forall A G D, Good G D -> value_type A -> DefEq G D A a_Star a_Star -> A = a_Star.
Proof.
  intros A G D Good H0 H.
  apply consistent_defeq in H; eauto.
  apply join_consistent in H.
  inversion H;  eauto; subst; try done.
  impossible_Path.
Qed.

Lemma canonical_forms_Pi : forall G rho a A B, irrelevant G (dom G) a ->
    Typing G a (a_Pi rho A B) -> Value a ->
    (exists a1, a = a_UAbs rho a1) \/ (exists T, Path T a).
Proof.
  intros G rho a A B IR H H0.
  inversion H0; subst; eauto.
  - apply invert_a_Star in H; eauto.
    impossible_defeq.
  - eapply invert_a_Pi in H; eauto.
    destruct H as [H _]; eauto.
    impossible_defeq.
  - eapply invert_a_CPi in H; eauto.
    destruct H as [H _].
    impossible_defeq.
  - assert False. eapply no_aAbs. eauto 2. done.
  - eapply invert_a_UAbs in H; eauto.
    destruct H as (A1 & A2 & H & _); eauto.
    impossible_defeq.
  - eapply invert_a_UAbs in H; eauto.
    destruct H as (A1 & B1 & H & _); eauto.
    impossible_defeq.
  - assert False. eapply no_aAbs. eauto 2. done.
  - assert False. eapply no_aCAbs. eauto 2. done.
  - eapply invert_a_UCAbs in H; eauto.
    destruct H as [a [b [T [B1 [_ [H _]]]]]]; eauto.
    impossible_defeq.
Qed.

Lemma canonical_forms_CPi : forall G a phi B, irrelevant G (dom G) a ->
    Typing G a (a_CPi phi B) -> Value a ->
    (exists a1, a = a_UCAbs a1) \/ (exists T, Path T a).
Proof.
  intros G a phi B IR H H0.
  inversion H0; subst; eauto.
  - apply invert_a_Star in H; eauto.
    impossible_defeq.
  - eapply invert_a_Pi in H; eauto.
    destruct H as [H _]; eauto.
    impossible_defeq.
  - eapply invert_a_CPi in H; eauto.
    destruct H as [H _].
    impossible_defeq.
  - assert False. eapply no_aAbs. eauto 2. done.
  - eapply invert_a_UAbs in H; eauto.
    destruct H as [A1 [A2 [H _]]]; eauto.
    impossible_defeq.
  - eapply invert_a_UAbs in H; eauto.
    destruct H as [A1 [A2 [H _]]]; eauto.
    impossible_defeq.
  - assert False. eapply no_aAbs. eauto 2. done.
  - assert False. eapply no_aCAbs. eauto 2. done.
Qed.




(* helper tactic for progress lemma below. Dispatches goals of the form
   "irrelevant G a " by inversion on IR, a similar assumption in the context *)
Ltac show_irrelevant IR :=
        let x := fresh in
        let A0 := fresh in
        let B0 := fresh in
        let h0 := fresh in
        let h1 := fresh in
        unfold irrelevant in *;
        move: IR => [h0 h1]; split; auto;
        intros x A0 B0;  apply h0 in B0; simpl in B0; fsetdec.

Lemma notin_sub : forall x a b, x `notin` a -> b [<=] a -> x `notin` b.
  intros. fsetdec.
Qed.



(*
   The progress lemma is stated in terms of the reduction_in_one relation.
*)

Lemma progress : forall G a A, Typing G a A ->
                          irrelevant G (dom G) a ->
                          Value a \/ exists a', reduction_in_one a a'.
  induction 1; intros IR; subst; eauto; try done.
  - unfold irrelevant in *.
    move: IR => [H1 _].
    apply H1 in H0. simpl in H0. fsetdec.
  - left; eauto.
    constructor.
    apply (Typing_lc H1); eauto.
    pick_fresh x.
    have: x `notin` L; auto => h0.
    apply (lc_a_Pi_exists x).
    apply (Typing_lc H1); eauto.
    apply (Typing_lc (H x h0)); eauto.
  - destruct rho.
    + left.
    constructor; eauto.
    pick_fresh x.
    have: x `notin` L; auto => h0.
    apply (lc_a_UAbs_exists x).
    apply (Typing_lc (H x h0)); eauto.
    + pick fresh x.
      assert (x `notin` L). auto.
      move: (H2 x H3) => h0.
      inversion h0. subst.
      destruct (H0 x H3) as [V | [a' R]].
      { move: (H x H3) => h1.
      unfold irrelevant in *.
      destruct IR as [h2 h3].
      have ctx: (Ctx ([(x, Tm A)] ++ G)) by eauto.
      move: (Ctx_uniq ctx) => u. inversion u. subst.
      split. intros x0 A0 b0.
      apply binds_cons_uniq_1 in b0. destruct b0.
      ++ split_hyp. subst. auto.
      ++ split_hyp.
         move: (h2 _ _ H5) => fr. simpl in fr.
         eapply notin_sub; [idtac|eapply fv_tm_tm_tm_open_tm_wrt_tm_upper].
         simpl.
         fsetdec.
      ++ eauto.
      ++ simpl. eapply Good_add_tm_2; eauto using Typing_erased. }
      -- left.
         eapply Value_UAbsIrrel_exists with (x := x); eauto.
      -- right. exists (a_UAbs Irrel (close_tm_wrt_tm x a')).
         eapply E_AbsTerm_exists with (x := x).
         { eapply notin_union; auto.
           simpl. rewrite fv_tm_tm_tm_close_tm_wrt_tm. auto. }
         rewrite open_tm_wrt_tm_close_tm_wrt_tm. auto.
  - destruct IHTyping1 as [V | [b' h0]].
    + show_irrelevant IR.
    + apply canonical_forms_Pi in H; auto.
      destruct H as [[a1 e1]|[T P]]; subst.
      ++ right.
         exists (open_tm_wrt_tm a1 a); eauto.
         apply E_AppAbs; eauto.
         eauto using Value_lc.
         apply (Typing_lc H0); eauto.
      ++ left. eauto with lc.
      ++ show_irrelevant IR.
    + right.
      exists (a_App b' Rel a); eauto.
      apply E_AppLeft; eauto.
      apply (Typing_lc H0); eauto.
  - case IHTyping1; auto.
    + show_irrelevant IR.
    + move => h1.
      apply canonical_forms_Pi in H; auto.
      destruct H as [[a1 e1]|[T P]]; subst.
      ++ right.
      exists (open_tm_wrt_tm a1 a_Bullet); eauto.
      ++ left. eauto with lc.
      ++ show_irrelevant IR.
    + move => h1.
      destruct h1 as [b' h0].
      right.
      exists (a_App b' Irrel a_Bullet); eauto.
  - left.
    constructor; eauto.
    apply (PropWff_lc H1); eauto.
    pick_fresh c.
    have: c `notin` L; auto => h0.
    apply (lc_a_CPi_exists c); eauto 1.
    apply (PropWff_lc H1); eauto.
    apply (Typing_lc (H c h0)); eauto.
  - left.
    constructor; eauto.
    pick_fresh c.
    have h0: c `notin` L; auto.
    apply (lc_a_UCAbs_exists c); eauto 0.
    apply (Typing_lc (H c h0)); eauto.
  - case IHTyping; auto.
    + show_irrelevant IR.
    + move => h1.
      apply canonical_forms_CPi in H; auto.
      destruct H as [[a2 e1]|[T P]]; subst.
      ++
        right. exists (open_tm_wrt_co a2 g_Triv); eauto.
        eapply E_CAppCAbs; eauto.
        eauto using Value_lc.
      ++ left. eauto with lc.
      ++ show_irrelevant IR.
    + intros H1.
      destruct H1 as [a' h0].
      right.
      exists (a_CApp a' g_Triv); eauto.
Qed.




End ext_consist.
