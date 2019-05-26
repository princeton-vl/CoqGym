Require Import FcEtt.sigs.
Require Import FcEtt.imports.
Require Import FcEtt.ett_ott.
Require Import FcEtt.ett_inf.
Require Import FcEtt.ett_ind.

Require Import FcEtt.ett_par.
Require Import FcEtt.ext_wf.

Require Import FcEtt.utils.

Module ext_invert (subst : ext_subst_sig) <: ext_invert_sig.

  Include subst.


Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.


Lemma binds_to_Typing: forall G T A, Ctx G -> binds T (Tm A) G -> Typing G A a_Star.
Proof.
  induction G; try done.
  intros T A H H0.
  rewrite_env ([a] ++ G).
  destruct a.
  induction s; subst.
  - inversion H0; eauto.
    + inversion H1; subst; clear H1.
      inversion H; subst; eauto.
      all: eapply Typing_weakening with (F:=nil); eauto.
    + eapply Typing_weakening with (F:=nil); eauto 2.
      rewrite_env G.
      eapply IHG; eauto 2.
      inversion H; auto.
  - inversion H0; try done.
    eapply Typing_weakening with (F:=nil); eauto 2.
    rewrite_env G.
    eapply IHG; eauto 2.
    inversion H; auto.
Qed.


Lemma invert_a_Pi:
  forall G rho A0 A B0,
    Typing G (a_Pi rho A0 B0) A
    -> DefEq G (dom G) A a_Star a_Star
      /\ (exists L, forall x,
              x `notin` L
              -> Typing ([(x, Tm A0)] ++ G) (open_tm_wrt_tm B0 (a_Var_f x)) a_Star)
      /\ Typing G A0 a_Star.
Proof.
  intros G rho A0 A B0 h1.
  dependent induction h1; auto; try done.
  - repeat split; eauto using Typing_Ctx.
  - destruct (IHh1_1 rho A0 B0) as (h1 & h2 & h3); try reflexivity.
    repeat split; eauto.
Qed.

Lemma invert_a_CPi: forall G phi A B0,
    Typing G (a_CPi phi B0) A ->
    DefEq G (dom G) A a_Star a_Star /\ (exists L, forall c, c `notin` L -> Typing ([(c, Co phi)] ++ G) (open_tm_wrt_co B0 (g_Var_f c) ) a_Star) /\ PropWff G phi.
Proof.
  intros G phi A B0 h1.
  dependent induction h1; eauto 2; try done.
  destruct (IHh1_1 phi B0) as [h2 [L h3]]; first by done.
  repeat split; eauto using Typing_Ctx.
  repeat split; eauto using Typing_Ctx.
Qed.


Lemma invert_a_Const : forall G T A,
    Typing G (a_Const T) A ->
    exists B, DataTy B a_Star /\ DefEq G (dom G) A B  a_Star
         /\ binds T (Cs B) toplevel.
Proof.
  intros G T A H.
  remember (a_Const T) as a.
  generalize dependent T. induction H; intros U EQ; inversion EQ.
  - subst.
    move: (IHTyping1 U eq_refl) => [B0 h]. split_hyp.
    exists B0.
    repeat split; eauto.
  - subst.
    exists A. repeat split; auto.
    induction H0.
    + inversion H0.
    + inversion H0.
    + eapply E_Refl.
      move: (Typing_weakening H1 G nil nil ltac:(auto)) => h0.
      simpl_env in h0. auto.
Qed.


Lemma invert_a_Fam : forall G F A,
    Typing G (a_Fam F) A ->
    exists a B, DefEq G (dom G) A B a_Star /\
           binds F (Ax a B) toplevel /\ Typing nil B a_Star.
Proof.
  intros G F A H. dependent induction H.
  - destruct (IHTyping1 F) as (a & B1 & h0 & h1 & h3); try done.
    exists a, B1 . repeat split; eauto 2.
    eapply E_Trans with (a1 := A).
    eapply E_Sym. auto. auto.
  - exists a, A.
    repeat split; eauto 2.
    eapply E_Refl.
    eapply Typing_weakening with (F:=nil)(E:=G)(G:=nil) in H1.
    simpl_env in H1. auto. auto. simpl_env. auto.
Qed.


Lemma invert_a_Star: forall A G, Typing G a_Star A -> DefEq G (dom G) A a_Star a_Star.
Proof.
  intros A G H.
  dependent induction H; subst; eauto 2; try done.
  eauto.
  eauto 4.
Qed.


Lemma invert_a_Var :
  forall G x A, Typing G (a_Var_f x) A -> exists A', binds x (Tm A') G /\ DefEq G (dom G) A A' a_Star.
Proof.
  intros G x A H. dependent induction H.
  exists A. split. auto.
  move: (binds_to_Typing x _ H H0) => h0.
  eapply E_Refl; eauto.
  destruct (IHTyping1 x eq_refl) as [A' [bi D]].
  exists A'. split. auto. eapply E_Trans with (a1:= A).
  eapply E_Sym; eauto.
  auto.
Qed.


(* -------------------------------
   Find a better place for these tactics
*)
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

Ltac un_subst_tm :=
   match goal with
   | [ |- context [tm_subst_tm_tm ?g ?c _] ] =>
     match goal with
     | [ |- Typing _ ?a ?A ] => expand (tm_subst_tm_tm g c) a; expand (tm_subst_tm_tm g c) A
     | [ |- DefEq _ _ ?a ?b ] => expand (tm_subst_tm_tm g c) a; expand (tm_subst_tm_tm g c) b
     | [ |- PropWff ?phi ] => expand_constraint (tm_subst_tm_tm g c) (tm_subst_tm_constraint g c) phi
     end
   | [ |- context [co_subst_co_tm ?g ?c _] ] =>
     match goal with
     | [ |- Typing _ ?a ?A ] => expand (co_subst_co_tm g c) a; expand (co_subst_co_tm g c) A
     | [ |- DefEq _ _ ?a ?b ] => expand (co_subst_co_tm g c) a; expand (co_subst_co_tm g c) b
     | [ |- PropWff ?phi ] => expand_constraint (co_subst_co_tm g c) (co_subst_co_constraint g c) phi
     end
   end.




(* --------------------------------------------------------------- *)

Lemma Typing_regularity : forall e A G, Typing G e A -> Typing G A a_Star.
Proof.
  intros e A G H1.
  induction H1; intros; eauto.
  - eapply binds_to_Typing; eauto.
  - apply invert_a_Pi in IHTyping1; eauto.
    destruct IHTyping1 as [h2 [[L h3] h4]].
    pick_fresh x.
    rewrite (tm_subst_tm_tm_intro x); auto.
    un_subst_tm.
    eapply Typing_tm_subst; eauto.
  - apply invert_a_Pi in IHTyping1; eauto.
    destruct IHTyping1 as [h2 [[L h3] h4]].
    pick_fresh x.
    rewrite (tm_subst_tm_tm_intro x); auto.
    un_subst_tm.
    eapply Typing_tm_subst; eauto.
  - apply invert_a_CPi in IHTyping; eauto using Typing_Ctx.
    destruct IHTyping as [h2 [[L h3] _]].
    pick_fresh c.
    rewrite (co_subst_co_tm_intro c); auto.
    un_subst_tm.
    eapply Typing_co_subst; eauto.
  - eapply Typing_weakening with (F:=nil)(G := nil) in H1.
    simpl_env in H1. eauto. auto. simpl_env. auto.
  - eapply Typing_weakening with (F:=nil)(G := nil) in H1.
    simpl_env in H1. eauto. auto. simpl_env. auto.
Qed.

(* --------------------------------------------------- *)

Lemma refl_iso: forall G D phi, PropWff G phi -> Iso G D phi phi.
Proof.
  intros G D phi H.
  destruct phi.
  inversion H.
  assert (Ctx G). eauto.
  assert (Typing G A a_Star). { eapply Typing_regularity; eauto. }
  apply E_PropCong; eauto.
Qed.


Lemma sym_iso: forall G D phi1 phi2, Iso G D phi1 phi2 -> Iso G D phi2 phi1.
Proof.
  intros G D phi1 phi2 H.
  induction H.
  - assert (Ctx G). eauto.
    apply E_PropCong; apply E_Sym; auto.
  - eapply E_IsoConv; eauto.
  - apply (E_CPiFst _ _ _ _ B2 B1); auto.
Qed.

(* --------------------------------------------------- *)


Lemma invert_a_UAbs:
  forall G rho A b0,
   Typing G (a_UAbs rho b0) A
    -> exists A1 B1, DefEq G (dom G) A (a_Pi rho A1 B1) a_Star
               /\ (exists L, forall x, x `notin` L ->
                            Typing ([(x, Tm A1)] ++ G)
                                   (open_tm_wrt_tm b0 (a_Var_f x))
                                   (open_tm_wrt_tm B1 (a_Var_f x))
                            /\ Typing ([(x, Tm A1)] ++ G)
                                     (open_tm_wrt_tm B1 (a_Var_f x)) a_Star
                            /\ RhoCheck rho x (open_tm_wrt_tm b0 (a_Var_f x)))
               /\ Typing G A1 a_Star.
Proof.
  intros G rho A b0.
  move e: (a_UAbs rho b0) => t1.
  move => h0.
  induction h0; auto; try done.
  inversion e; subst.
  - exists A, B.
    split.
    + apply (E_Refl _ _ _ a_Star); auto.
      apply (E_Pi (L \u (dom G))); auto.
      intros x HH.
      apply (@Typing_regularity (open_tm_wrt_tm a (a_Var_f x))); auto.
    + split; auto.
      exists (L \u (dom G)).
      inversion e; subst; clear e.
      intros x HH.
      repeat split; auto.
      apply (@Typing_regularity (open_tm_wrt_tm a (a_Var_f x))); auto.
  -  destruct IHh0_1 as [A1 [B1 [h3 [L h2]]]]; auto.
     subst.
     exists A1, B1.
     split.
     + apply (@E_Trans _ _ _ _ _ A); auto.
     + split; auto.
Qed.


Lemma invert_a_UCAbs: forall G A b0,
    Typing G (a_UCAbs b0) A ->
    exists a b T B1, PropWff G (Eq a b T) /\ DefEq G (dom G) A (a_CPi (Eq a b T) B1) a_Star
                /\ (exists L, forall c, c `notin` L ->
                             Typing ([(c, Co (Eq a b T))] ++ G)
                                    (open_tm_wrt_co b0 (g_Var_f c)) (open_tm_wrt_co B1 (g_Var_f c))
                             /\ Typing ([(c, Co (Eq a b T))] ++ G) (open_tm_wrt_co B1 (g_Var_f c)) a_Star).
Proof.
  intros G A b0.
  move e: (a_UCAbs b0) => t1.
  move => h0.
  induction h0; auto; try done.
  - destruct IHh0_1 as [a' [b' [T [B2 [h3 [h4 [L h5]]]]]]]; auto.
    exists a', b', T, B2.
    split; auto.
    split.
    + apply (E_Trans _ _ _ _ _ A); auto.
    + exists L; auto.
  - induction phi.
    exists a0, b, A, B.
    split; auto.
    split.
    + apply (E_Refl _ _ _ a_Star); auto.
      apply (E_CPi (L \u (dom G))); auto.
      intros c H2.
      apply (@Typing_regularity (open_tm_wrt_co a (g_Var_f c))); auto.
    + exists (L \u (dom G)).
      inversion e; subst; clear e.
      intros c H2.
      split; auto.
      apply (@Typing_regularity (open_tm_wrt_co a (g_Var_f c))); auto.
Qed.


Lemma invert_a_App_Rel : forall G a b C,
    Typing G (a_App a Rel b) C ->
    exists A B, Typing G a (a_Pi Rel A B) /\
           Typing G b A /\
           DefEq G (dom G) C (open_tm_wrt_tm B b) a_Star.
Proof.
  intros G a b C.
  move e : (a_App a Rel b) => t1.
  move => h1.
  induction h1; auto; try done.
  - exists A, B. inversion e; subst.
    assert (h2 : Typing G (open_tm_wrt_tm B a0) a_Star).
    + (have: Typing G (a_Pi Rel A B) a_Star by apply (Typing_regularity h1_1)) => h3.
      destruct (invert_a_Pi h3) as [_ [[L h4] h5]].
      pick fresh x.
      rewrite (tm_subst_tm_tm_intro x); auto.
      replace a_Star with (tm_subst_tm_tm a0 x a_Star); auto.
      apply Typing_tm_subst with (A := A); auto.
    + repeat split; auto.
  - destruct (IHh1_1 e) as [A0 [B0 [h3 [h2 e2]]]].
    exists A0, B0.
    repeat split; auto.
    apply (E_Trans _ _ _ _ _ A); auto.
Qed.


Lemma invert_a_App_Irrel : forall G a b C,
    Typing G (a_App a Irrel b) C ->
    exists A B b0, Typing G a (a_Pi Irrel A B) /\
              Typing G b0 A /\
              DefEq G (dom G) C (open_tm_wrt_tm B b0) a_Star.
Proof.
  intros G a b C.
  move e : (a_App a Irrel b) => t1.
  move => h1.
  induction h1; auto; try done.
  - exists A, B, a0. inversion e; subst.
    assert (h2 : Typing G (open_tm_wrt_tm B a0) a_Star).
    + (have: Typing G (a_Pi Irrel A B) a_Star by apply (Typing_regularity h1_1)) => h3.
      destruct (invert_a_Pi h3) as [_ [[L h4] h5]].
      pick fresh x.
      rewrite (tm_subst_tm_tm_intro x); auto.
      replace a_Star with (tm_subst_tm_tm a0 x a_Star); auto.
      apply Typing_tm_subst with (A := A); auto.
    + repeat split; auto.
  - destruct (IHh1_1 e) as [A0 [B0 [b0 [h3 [h2 h4]]]]].
    exists A0, B0, b0.
    repeat split; auto.
    apply (E_Trans _ _ _ _ _ A); auto.
Qed.

Lemma invert_a_CApp : forall G a g A,
    Typing G (a_CApp a g) A ->
    g = g_Triv /\
    exists a1 b1 A1 B, Typing G a (a_CPi (Eq a1 b1 A1) B) /\
             DefEq G (dom G) a1 b1 A1 /\
             DefEq G (dom G) A (open_tm_wrt_co B g_Triv) a_Star.
Proof.
  intros G a g A H.
  dependent induction H.
  - destruct (IHTyping1 a g) as (p & a1 & b1 & A1 & BB & Ta & Dab & DAB); first by done.
    split; first by done.
    exists a1, b1, A1, BB.
    repeat split; auto.
    apply E_Trans with (a1 := A); auto.
  - split; first by done.
    exists a0, b, A, B1.
    repeat split; auto.
    eapply E_Refl.
    have CTX: Ctx G by eauto.
    have TC: Typing G (a_CPi (Eq a0 b A) B1) a_Star. eapply Typing_regularity; eauto.
    destruct (invert_a_CPi TC) as [_ [[L h4] h5]].
    pick fresh x.
    move: (h4 x ltac:(auto)) => h6.
    eapply Typing_co_subst  in h6. simpl in h6.
    rewrite (co_subst_co_tm_intro x); eauto.
    simpl; eauto.
Qed.


(* --------------------------------------------------- *)

Inductive context_DefEq : available_props -> context -> context -> Prop :=
| Nul_Eqcontext: forall D, context_DefEq D nil nil
| Factor_Eqcontext_tm: forall G1 G2 D A A' x,
    context_DefEq D G1 G2 ->
    DefEq G1 D A A' a_Star ->
    DefEq G2 D A A' a_Star ->
    context_DefEq D ([(x, Tm A)] ++ G1) ([(x, Tm A')] ++ G2)
| Factor_Eqcontext_co: forall D G1 G2 Phi1 Phi2 c,
    context_DefEq D G1 G2 ->
    Iso G1 D Phi1 Phi2 ->
    Iso G2 D Phi1 Phi2 ->
    context_DefEq D ([(c, Co Phi1)] ++ G1) ([(c, Co Phi2)] ++ G2).

Hint Constructors context_DefEq.

Lemma context_tm_binding_defeq: forall D (G1 G2: context) A x,
    Ctx G1 -> Ctx G2 -> context_DefEq D G1 G2 ->
    binds x (Tm A) G1 -> exists A', (binds x (Tm A') G2) /\ DefEq G2 D A A' a_Star.
Proof.
  intros D G1 G2 A x H1 h0 H H0.
  induction H; try done.
  - case H0; simpl.
    + intros M4.
      exists A'.
      * split; auto.
         -- left.
            inversion M4; auto.
         -- inversion M4; subst; clear M4.
            rewrite_env (nil ++ [(x, Tm A')] ++ G2).
            pose K := DefEq_weakening.
            inversion h0; subst.
            inversion H1; subst.
            eapply K with (G0 := G2).
            all: eauto.
    + intros M4.
      case IHcontext_DefEq; auto; try done.
      * by inversion H1.
      * by inversion h0.
      * intros A2 [h1 h2].
         exists A2.
         split; auto.
         rewrite_env (nil ++ [(x0, Tm A')] ++ G2).
         pose K := DefEq_weakening.
         eapply K; eauto.
  - case H0; try done; simpl.
    move => h1.
    case IHcontext_DefEq; auto.
    + by inversion H1.
    + by inversion h0.
    + intros A2 [h2 h3].
       exists A2.
       split; auto.
       rewrite_env (nil ++ [(c, Co Phi2)] ++ G2).
       pose K := DefEq_weakening.
       eapply K; eauto.
Qed.

Lemma context_co_binding_defeq:
  forall D (G1 G2: context) phi1 c,
    Ctx G1 ->
    Ctx G2 -> context_DefEq D G1 G2 ->
    binds c (Co phi1) G1 ->
    exists phi2, (binds c (Co phi2) G2) /\ Iso G2 D phi1 phi2.
Proof.
  intros G1 G2 phi1 c m H Hip H0 H1.
  induction H0; auto; try done.
  - case H1; move => h0.
    inversion h0.
    destruct IHcontext_DefEq as [phi2 [h1 h2 ]]; auto.
    + inversion H; auto.
    + by inversion Hip.
    + exists phi2.
      split.
      * right; auto.
      * eapply Iso_weakening with (F := nil); eauto.
  - case H1; move => h0.
    + inversion h0; subst; clear h0.
      exists Phi2.
      split.
      * auto.
      * eapply Iso_weakening with (F:=nil) (G0 := G2); eauto.
    + destruct IHcontext_DefEq as [phi2 [h1 h2]]; auto.
      * inversion H; auto.
      * by inversion Hip.
      * exists phi2.
        split; auto.
        eapply Iso_weakening with (F:=nil); eauto.
Qed.


Lemma context_DefEq_sub :
  forall D G1 G2, context_DefEq D G1 G2 -> forall D', D [<=] D' -> context_DefEq D' G1 G2.
Proof.
  induction 1.
  eauto.
  intros D' Sub.
  pose K := (fourth weaken_available_mutual _ _ _ _ _ _ D' Sub). clearbody K.
  econstructor; eauto.
  intros D' Sub.
  pose K := (third weaken_available_mutual _ _ _ _ _ D' Sub). clearbody K.
  eauto.
Qed.

Lemma same_dom : forall D (G1 : context) G2,
    context_DefEq D G1 G2 -> (@dom ett_ott.sort G1) = (@dom ett_ott.sort G2).
Proof.
  induction 1; auto.
  simpl. rewrite IHcontext_DefEq. auto.
  simpl. rewrite IHcontext_DefEq. auto.
Qed.


Lemma context_DefEq_weaken_available :
  forall D G1 G2, context_DefEq D G1 G2 -> context_DefEq (dom G1) G1 G2.
Proof.
  induction 1.
  eauto.
  assert (SUB : (dom G1) [<=] (dom ([(x,Tm A)] ++ G1))). simpl. fsetdec.
  econstructor; auto.
  apply (context_DefEq_sub IHcontext_DefEq SUB).
  eapply (fourth weaken_available_mutual G1).
  eapply DefEq_weaken_available. eauto. auto.
  eapply (fourth weaken_available_mutual G2).
  eapply DefEq_weaken_available. eauto.
  erewrite <- (@same_dom _ G1 G2). auto. eauto.
  assert (SUB : (dom G1) [<=] (dom ([(c,Co Phi1)] ++ G1))). simpl. fsetdec.
  econstructor; auto.
  apply (context_DefEq_sub IHcontext_DefEq SUB).
  eapply (third weaken_available_mutual G1).
  eapply Iso_weaken_available. eauto. auto.
  eapply (third weaken_available_mutual G2).
  eapply Iso_weaken_available. eauto.
  erewrite <- (@same_dom _ G1 G2). auto. eauto.
Qed.


Lemma context_DefEq_mutual:
  (forall G1  a A,   Typing G1 a A -> forall D G2,
        Ctx G2 -> context_DefEq D G1 G2 -> Typing G2 a A) /\
  (forall G1  phi,   PropWff G1 phi -> forall D G2,
        Ctx G2 -> context_DefEq D G1 G2 -> PropWff G2 phi) /\
  (forall G1 D p1 p2, Iso G1 D p1 p2 ->
                  forall G2, Ctx G2 -> context_DefEq D G1 G2 -> Iso G2 D p1 p2) /\
  (forall G1 D1 A B T,   DefEq G1 D1 A B T -> forall G2, Ctx G2 -> context_DefEq D1 G1 G2 ->
                                          DefEq G2 D1 A B T) /\
  (forall G1 ,       Ctx G1 -> forall G2 D x A, Ctx G2 -> context_DefEq D G1 G2
                                   -> binds x (Tm A) G1 -> Typing G2 A a_Star).
Proof.
  apply typing_wff_iso_defeq_mutual; eauto 3; try done.
  - intros G1 x A c H b D G2 H0 H1.
    case (@context_tm_binding_defeq D G1 G2 A x); auto.
    intros A2 [h0 h1].
    apply (E_Conv _ _ _ A2); auto.
    eapply DefEq_weaken_available; eauto.
    eapply H; eauto.
  - intros L G1 rho A B t H t0 H0 D G2 H1 H2.
    apply (E_Pi (L \u (dom G2))); auto.
    intros x H3.
    eapply H; auto.
    eapply E_ConsTm; eauto.
    apply Factor_Eqcontext_tm; eauto 2.
    eapply E_Refl; eauto.
    eapply H0; eauto.
  - intros L G1 rho A a B t H t0 H0 r D G2 H1 H2.
    apply (E_Abs (L \u (dom G2))); auto.
    intros x H3.
    eapply H; auto.
    eapply E_ConsTm; eauto.
    eapply Factor_Eqcontext_tm; eauto 3.
    eapply H0; eauto.
  - intros. eauto 4.
  - intros. eauto 4.
  - intros G a B A t H d H0 d0 t0 D G2 H1 H2.
    apply (E_Conv _ _ _ A); auto. eapply H; eauto.
    rewrite <- (same_dom H2).
    eapply H0; eauto.
    eapply context_DefEq_weaken_available. eauto.
    eapply t0; eauto.
  - intros L G1 phi B t H p H0 D G2 H1 H2.
    apply (E_CPi (L \u (dom G2))); eauto.
    intros c H3.
    eapply H; eauto.
    apply Factor_Eqcontext_co; eauto 2.
    eapply refl_iso; auto.
    eapply refl_iso; auto.
    eauto.
  - intros L G1 phi a B t H p H0 D G2 H1 H2.
    apply (E_CAbs (L \u (dom G2))); auto.
    intros c H3.
    eapply H; eauto.
    eapply Factor_Eqcontext_co; eauto 2.
    eapply refl_iso; eauto.
    eapply refl_iso; eauto.
    eauto.
  - intros G a1 B1 a b A t H d H0 D G2 H1 H2.
    apply (E_CApp _ _ _ a b A); auto. eauto.
    rewrite <- (same_dom H2).
    eapply H0. auto.
    eapply context_DefEq_weaken_available. eauto.
  - (* intros G T A c H b D G2 H0 H1.
    have K := @context_tm_binding_defeq D G G2 A T.
    case K; auto => A' [h0 h1].
    apply (E_Conv _ _ _ A'); eauto 2.
    apply E_Sym.
    eapply DefEq_weaken_available; eauto.
  - *) intros G a b A t H t0 H0 t1 H1 D G2 H2 H3.
    apply E_Wff; eauto.
  (*- intros G D A1 B1 A A2 B2 B d H d0 H0 d1 H1 G2 H2 H3.
    apply E_PropCong; auto.
    rewrite <- (same_dom H3).
    eapply H1; auto.
    eapply context_DefEq_weaken_available. eauto.*)
  - intros. eauto 4.
  - intros G D A1 A2 A B d H p H0 p0 H1 G2 H2 H3.
    eapply E_IsoConv; eauto.
  - intros G D a b A c c0 H b0 i G2 H0 H1.
    case (@context_co_binding_defeq D G G2 (Eq a b A) c); auto.
    intros phi' [h0 h1].
    destruct phi' as [A' B'].
    eapply (E_Assn _ D) in h0; auto.
    eapply sym_iso in h1.
    eapply E_Cast; eauto.
  - intros. eauto 4.
  - intros. eauto 4.
  - intros L. intros.
    pick fresh x and apply E_PiCong; eauto 2.
    eapply H0; eauto.
  - intros.
    pick fresh x and apply E_AbsCong; eauto 2.
    eapply H; eauto.
  - intros. eauto 4.
  - intros. eauto 4.
  - intros. eauto 4.
  - intros.
    pick fresh x and apply E_CPiCong; eauto 2.
    eapply H0; eauto.
    econstructor; eauto.
  - intros.
    pick fresh c and apply E_CAbsCong; eauto 2.
    destruct phi1.
    eapply H; eauto.
    econstructor; eauto using refl_iso.
  - intros G D a1 b1 B a b A d H d0 H0 G2 H1 H2.
    eapply E_CAppCong; eauto 2.
    rewrite <- (same_dom H2).
    apply H0; eauto.
    eapply context_DefEq_weaken_available. eauto.
  - intros G D B1 B2 a1 a2 A a1' a2' A' d H d0 H0 d1 H1 G2 H2 H3.
    eapply E_CPiSnd; eauto 2. eapply DefEq_weaken_available.
    eapply H0; eauto 2.
    eapply context_DefEq_weaken_available. eauto 2.
    eapply DefEq_weaken_available; eauto 2.
    eapply H1; eauto 2.
    eapply context_DefEq_weaken_available; eauto 2.
  - intros. eauto 4.
  - intros G D a b B A d H d0 H0 G2 H1 H2.
    apply (E_EqConv _ _ _ _ _ A); auto.
    rewrite <- (same_dom H2).
    apply H0; auto.
    eapply context_DefEq_weaken_available; eauto.
(*  - intros.
    eapply E_LeftRel with (b:=b)(b':=b'); eauto 2.
    erewrite <- same_dom; eauto 2.
    eauto using context_DefEq_weaken_available.
  - intros.
    eapply E_LeftIrrel with (b:=b)(b':=b'); eauto 2.
    erewrite <- same_dom; eauto 2.
    eauto using context_DefEq_weaken_available.
  - intros.
    eapply E_Right with (a:=a)(a':=a'); eauto 2.
    erewrite <- same_dom; eauto 2.
    eauto using context_DefEq_weaken_available.
  - intros.
    eapply E_CLeft; eauto 2.
    erewrite <- same_dom; eauto 2.
    eauto using context_DefEq_weaken_available. *)
  - intros G x A c H t H0 n G2 D x0 A0 H1 H2 H3.
    inversion H3; subst.
    + inversion H4; subst.
      inversion H2; subst.
      have: Typing G0 A0 a_Star; auto.
      * eapply H0; eauto.
      * move => h0.
        pose K := Typing_weakening.
        rewrite_env (nil ++ [(x0, Tm A')] ++ G0).
        apply (K _ _ _ h0); auto.
    + inversion H2; subst.
      have: Typing G0 A0 a_Star; auto.
      * apply (H _ D x0); auto.
          by inversion H1; auto.
      * move => h0.
        pose K := Typing_weakening.
        rewrite_env (nil ++ [(x, Tm A')] ++ G0).
        apply (K _ _ _ h0); auto.
  - intros G c phi c0 H p H0 n G2 D x A H1 H2 H3.
    inversion H3; try done.
    inversion H2; subst.
    have: Typing G0 A a_Star.
    + apply (H _ D x); auto.
        by inversion H1.
    + move => h0.
      pose K := Typing_weakening.
      rewrite_env (nil ++ [(c, Co Phi2) ] ++ G0).
      apply (K _ _ _ h0); auto.
Qed.

Lemma context_DefEq_typing:
  forall G1  a A,
    Typing G1 a A -> forall D G2, Ctx G2 -> context_DefEq D G1 G2 -> Typing G2 a A.
Proof.
  apply context_DefEq_mutual.
Qed.


Lemma refl_context_defeq: forall G D, Ctx G -> context_DefEq D G G.
Proof.
  move => G; induction G.
  - intros D H.
    eapply Nul_Eqcontext.
  - intros D H. destruct a.
    inversion H; subst.
    + apply Factor_Eqcontext_tm; eauto.
    + apply Factor_Eqcontext_co; eauto 2.
      eapply refl_iso; done.
      eapply refl_iso; done.
Qed.


Lemma co_subst_co_tm_var_eq : forall a g c,
  lc_co g ->
  erased_tm a -> 
  co_subst_co_tm g_Triv c a = co_subst_co_tm g c a.
Proof.
  intros. induction H0; eauto.
  - pick fresh x. assert (X: x `notin` L). fsetdec. apply H1 in X. simpl in X.
    erewrite co_subst_co_tm_a_UAbs; eauto. erewrite co_subst_co_tm_a_UAbs; eauto.
    rewrite X; auto.
  - simpl. rewrite IHerased_tm1. rewrite IHerased_tm2. auto.
  - simpl. rewrite IHerased_tm. auto.
  - simpl. rewrite IHerased_tm. pick fresh x.
    assert (X: x `notin` L). fsetdec. apply H2 in X.
    rewrite co_subst_co_tm_open_tm_wrt_tm in X; eauto.
    rewrite co_subst_co_tm_open_tm_wrt_tm in X; eauto. simpl in X.
    eapply open_tm_wrt_tm_inj in X. rewrite X; auto.
    rewrite fv_tm_tm_tm_co_subst_co_tm_upper. fsetdec.
    rewrite fv_tm_tm_tm_co_subst_co_tm_upper. fsetdec.
  - simpl. rewrite IHerased_tm1. rewrite IHerased_tm2. rewrite IHerased_tm3.
    pick fresh x.
    assert (X: x `notin` L). fsetdec. apply H1 in X.
    assert (Q: x <> c). fsetdec.
    rewrite co_subst_co_tm_open_tm_wrt_co in X; eauto.
    rewrite co_subst_co_tm_open_tm_wrt_co in X; eauto. simpl in X.
    assert (W: (if x == c then g_Triv else g_Var_f x) = g_Var_f x).
    destruct (x == c). contradiction. auto.
    rewrite W in X.
    assert (W': (if x == c then g else g_Var_f x) = g_Var_f x).
    destruct (x == c). contradiction. auto.
    rewrite W' in X.
    eapply open_tm_wrt_co_inj in X. rewrite X; auto.
    rewrite fv_co_co_tm_co_subst_co_tm_upper. fsetdec.
    rewrite fv_co_co_tm_co_subst_co_tm_upper. fsetdec.
  - pick fresh x. assert (X: x `notin` L). fsetdec. apply H1 in X. simpl in X.
    erewrite co_subst_co_tm_a_UCAbs; eauto. erewrite co_subst_co_tm_a_UCAbs; eauto.
    rewrite X; auto.
  - simpl. rewrite IHerased_tm. auto.
Qed.


Lemma Typing_swap_co : forall x1 x G a A B,
      x1 `notin` fv_co_co_tm a \u fv_co_co_tm B
    -> x `notin` dom G \u {{ x1 }}
    -> Typing ([(x1, Co A)] ++ G) (open_tm_wrt_co a (g_Var_f x1))
             (open_tm_wrt_co B (g_Var_f x1))
    -> Typing ([(x, Co A)] ++ G) (open_tm_wrt_co a (g_Var_f x))
             (open_tm_wrt_co B (g_Var_f x)).
Proof.
  intros.
  assert (AC: Ctx ((x1 ~ Co A) ++ G)). eauto.
  inversion AC; subst. destruct A. 
  assert (TV : DefEq ([(x,Co (Eq a0 b A))] ++ G) {{x}} a0 b A).
  apply E_Assn with (c:=x); eauto.
  assert (CTX : Ctx ([(x1,Co (Eq a0 b A))] ++ [(x, Co (Eq a0 b A))] ++ G)).
  econstructor; auto.
  pose M1 := (PropWff_weakening H6 [(x,Co (Eq a0 b A))] nil G).
  simpl_env in M1; eapply M1; eauto.
  pose K1 := Typing_weakening H1 [(x,Co (Eq a0 b A))] [(x1, Co (Eq a0 b A))] G eq_refl CTX;
               clearbody K1. simpl in K1.
  pose K2 := Typing_co_subst K1 TV.
  clearbody K2.
  repeat rewrite co_subst_co_tm_open_tm_wrt_co in K2; auto.
  rewrite co_subst_co_co_var in K2;
  repeat rewrite co_subst_co_tm_fresh_eq in K2.
  rewrite (co_subst_co_tm_intro x1).
  rewrite (co_subst_co_tm_intro x1 B).
  rewrite -co_subst_co_tm_var_eq. rewrite -co_subst_co_tm_var_eq.
  rewrite -co_subst_co_tm_intro. rewrite -co_subst_co_tm_intro. 
  auto. fsetdec. fsetdec. eauto. eapply Typing_erased. eapply Typing_regularity. eauto.
  eauto. eapply Typing_erased. eauto. fsetdec. fsetdec. fsetdec. fsetdec.
Qed.

Lemma E_CAbs_exists :  forall c (G : context) (phi : constraint) (a B : tm),
    c `notin` fv_co_co_tm a \u fv_co_co_tm B
    -> Typing ([(c, Co phi)] ++ G) (open_tm_wrt_co a (g_Var_f c))
       (open_tm_wrt_co B (g_Var_f c))
    -> PropWff G phi
    -> Typing G (a_UCAbs a) (a_CPi phi B).
Proof.
  intros.
  pick fresh y and apply E_CAbs; auto.
  eapply (@Typing_swap_co c); eauto. 
Qed.


Lemma DefEqIso_regularity :
  (forall G0 a A, Typing G0 a A -> True ) /\
  (forall G0 phi,  PropWff G0 phi -> True ) /\
  (forall G D p1 p2, Iso G D p1 p2 ->
                 PropWff G p1 /\ PropWff G p2) /\
  (forall G D A B T,   DefEq G D A B T ->
                  Typing G A T /\ Typing G B T) /\
  (forall G0, Ctx G0 -> True).
Proof.
  apply typing_wff_iso_defeq_mutual; eauto; try done.
  - intros G D A1 B1 A A2 B2 d H d0 H0.
    split_hyp.
    split; apply E_Wff; solve [auto | eapply Typing_regularity; eauto].
  - intros G D phi1 phi2 B1 B2 d H.
    split_hyp.
    have CTX: Ctx G by eauto.
    split; solve [eapply invert_a_CPi; eauto].
  - intros G D a0 b0 A c c0 H b i.
    apply binds_to_PropWff in b; auto.
    inversion b; subst.
    split; auto.
  -  intros G D a b A d H.
    split_hyp; auto.
  - intros G D a b A a1 H1 H hi0 hi1.
    destruct H as [h0 h1]; auto.
    split_hyp; auto.
  - intros L G D rho b1 b2 A2 B d H0 t H1 r1 r2 .
    split_hyp.
    repeat split; auto.
    + apply (E_Abs (L \u (dom G))); eauto.
      intros x H4.
      apply H0; auto.
    + (have: Ctx G by eauto) => CTX.
      apply (E_Conv _ _ _ ((a_Pi rho A2 B))); auto.
      -- apply (E_Abs (L \u dom G)); eauto.
         intros x H4.
         eapply (@context_DefEq_typing ([(x, Tm A2)] ++ G)); eauto.
         apply H0; auto.
         apply Factor_Eqcontext_tm; eauto.
         apply refl_context_defeq; auto.
      -- apply (E_PiCong (L \u (dom G))); auto.
         ++ intros x H4.
            apply E_Refl; eauto.
            eapply (@context_DefEq_typing ([(x, Tm A2)] ++ G)); eauto.
            eapply Typing_regularity; eauto 2.
            apply H0; auto.
            apply Factor_Eqcontext_tm; eauto.
            apply refl_context_defeq; auto.
         ++ apply (E_Pi (L \u (dom G))); eauto.
            intros x H4.
            have: x `notin` L; auto => h0.
            destruct (H0 x h0).
            eapply Typing_regularity; eauto 2.
         ++ apply (E_Pi (L \u (dom G))); eauto.
            intros x H4.
            eapply Typing_regularity; eauto 2.
            apply H0; eauto.
      -- apply (E_Pi (L \u (dom G))); eauto.
         intros x H4.
         eapply Typing_regularity; eauto 2.
         apply H0; eauto.
  - intros G D a1 a2 b1 b2 B A d H d0 H0.
    split_hyp.
    (have: Ctx G by eauto) => CTX.
    split; eauto.
    apply (E_Conv _ _ _ (open_tm_wrt_tm B b2)); auto.
    eapply (E_App); eauto.
    apply (E_PiSnd _ _ _ _ _ _ Rel A A); auto.
    apply E_Refl; auto.
    eapply Typing_regularity; eauto.
    apply E_Sym.
    eapply DefEq_weaken_available; eauto.
    apply Typing_regularity in H; auto.
    apply invert_a_Pi in H; eauto.
    destruct H as [_ [[L h0] _]].
    pick_fresh x.
    have: x `notin` L; auto => h1.
    pose K := Typing_tm_subst (h0 x h1) H0.
    clearbody K.
    repeat rewrite tm_subst_tm_tm_open_tm_wrt_tm in K; try solve [apply (Typing_lc H0); eauto].
    simpl in K.
    destruct eq_dec; try congruence.
    rewrite tm_subst_tm_tm_fresh_eq in K; auto.
  - intros G D A1 A2 B1 B2 d H h0 h1 _.
    split_hyp.
    (have: Ctx G by eauto) => CTX.
    split; eauto.
  - intros G D A1 A2 rho B1 B2 d H.
    split_hyp.
    (have: Ctx G by eauto) => CTX.
    apply invert_a_Pi in H; eauto.
    apply invert_a_Pi in H0; eauto.
    split_hyp.
    split; eauto.
  - intros G D B1 a1 B2 a2 rho A1 A2 d H d0 H0.
    split_hyp.
    (have: Ctx G by eauto) => CTX.
    repeat split.
    + apply invert_a_Pi in H; eauto.
      destruct H as [_ [[L h0] _]].
      pick_fresh x.
      have: x `notin` L; auto => h1.
      pose K := Typing_tm_subst (h0 x h1) H0.
      clearbody K.
      repeat rewrite tm_subst_tm_tm_open_tm_wrt_tm in K; try solve [apply (Typing_lc H0); eauto].
      simpl in K.
      destruct eq_dec; try congruence.
      rewrite tm_subst_tm_tm_fresh_eq in K; auto.
    + apply invert_a_Pi in H2; eauto.
      destruct H2 as [_ [[L h0] hi1]].
      pick_fresh x.
      have: x `notin` L; auto => h1.
      apply (E_Conv _ _ A2) in H1; auto.
      pose K := Typing_tm_subst (h0 x h1) H1.
      clearbody K.
      repeat rewrite tm_subst_tm_tm_open_tm_wrt_tm in K; try solve [apply (Typing_lc H1); eauto].
      simpl in K.
      destruct eq_dec; try congruence.
      rewrite tm_subst_tm_tm_fresh_eq in K; auto.
      apply E_PiFst in d; auto.
      eapply DefEq_weaken_available; eauto.
  - intros L G D a b phi1 B d H p H0.
    split_hyp.
    have CTX: Ctx G by eauto.
    repeat split; eauto.
    + apply (E_CAbs (L \u (dom G))); eauto.
      intros c H3.
      apply H; eauto.
    + apply (E_Conv _ _ _ ((a_CPi phi1 B))); auto.
      * apply (E_CAbs (L \u (dom G))); eauto.
        intros c H3.
        eapply (@context_DefEq_typing ([(c, Co phi1)] ++ G)); eauto.
        apply H; eauto.
        apply Factor_Eqcontext_co; eauto 2.
        apply refl_context_defeq; eauto.
        all: apply refl_iso; eauto.
      * apply (E_CPiCong (L \u (dom G))); auto.
        -- apply refl_iso; auto.
        -- intros c H3.
           apply E_Refl; eauto.
           eapply (@context_DefEq_typing ([(c, Co phi1)] ++ G)); eauto.
           eapply Typing_regularity; eauto 2.
           apply H; eauto 4.
           apply Factor_Eqcontext_co; eauto 4.
           apply refl_context_defeq; eauto 4.
           all: apply refl_iso; eauto 4.
        -- apply (E_CPi (L \u dom G)); eauto.
           intros c H3.
           eapply (@context_DefEq_typing ([(c, Co phi1)] ++ G)); eauto.
           eapply Typing_regularity; eauto 2.
           apply H; eauto.
           apply Factor_Eqcontext_co; eauto 4.
           apply refl_context_defeq; eauto 4.
           all: apply refl_iso; eauto.
        -- apply (E_CPi (L \u dom G)); eauto.
           intros c H3.
           eapply Typing_regularity; eauto 2.
           apply H; auto.
      * apply (E_CPi (L \u (dom G))); eauto.
        intros c H3.
        destruct (H c); auto.
        eapply Typing_regularity; eauto.
  - intros L G D phi1 a phi2 b B i H d H0.
    split_hyp.
    split.
    eapply E_CApp; eauto.
    eapply E_CApp; eauto.
  - intros G D B1 B2 a1 a2 A a1' a2' A' d H d0 H0 d1 H1.
    split_hyp.
    (have: Ctx G by eauto) => CTX.
    apply invert_a_CPi in H; auto.
    apply invert_a_CPi in H4; auto.
    destruct H as [_ [[L0 ty0] _]].
    destruct H4 as [_ [[L1 ty1] _]].
    pick_fresh c.
    repeat split; eauto.
    + have: c `notin` L0; auto => h0.
      pose K := Typing_co_subst (ty0 c h0) d0.
      clearbody K.
      repeat rewrite co_subst_co_tm_open_tm_wrt_co in K; auto.
      simpl in K.
      destruct eq_dec; try congruence.
      rewrite co_subst_co_tm_fresh_eq in K; auto.
    + have: c `notin` L1; auto => h0.
      pose K := Typing_co_subst (ty1 c h0) d1.
      clearbody K.
      repeat rewrite co_subst_co_tm_open_tm_wrt_co in K; auto.
      simpl in K.
      destruct eq_dec; try congruence.
      rewrite co_subst_co_tm_fresh_eq in K; auto.
  - intros G D a' b' A' a b A d H i H0.
    split_hyp.
    inversion H1; subst.
    (have: Ctx G by eauto) => h0.
    eauto.
  - intros G D a b B A d H d0 H0.
    split_hyp; auto.
    split; eapply E_Conv; eauto.
  - intros G D A A' a b a' b' i H.
    split_hyp; eauto.
    inversion H0; subst.
    inversion H; subst.
    split; auto.
    Unshelve. exact (dom G). exact (dom G). exact (dom G). exact (dom G). exact (dom G).
  - intros. split; auto.
    have h0: Ctx G by eauto.
    move: (Typing_regularity t) => h1.
    move: (invert_a_Pi h1) => [DE [[L1 h2] h3]].
    pick fresh x.
    eapply (@E_Abs_exists x); try econstructor; eauto;
    rewrite e; eauto.
    eapply E_App.
    eapply Typing_weakening with (F:=nil); simpl; eauto 4.
    econstructor; eauto.
    econstructor; eauto using Typing_lc1.
  - intros. split; auto.
    have h0: Ctx G by eauto.
    move: (Typing_regularity t) => h1.
    move: (invert_a_Pi h1) => [DE [[L1 h2] h3]].
    pick fresh x.
    eapply (@E_Abs_exists x); try econstructor; eauto;
    rewrite e; eauto.
    econstructor; eauto.
    eapply Typing_weakening with (F:=nil); simpl; eauto 4. 
    econstructor; eauto.
  - intros. split; auto.
    have h0: Ctx G by eauto.
    move: (Typing_regularity t) => h1.
    move: (invert_a_CPi h1) => [DE [[L1 h2] h3]].
    pick fresh x. 
    eapply (@E_CAbs_exists x); try econstructor; eauto;
    rewrite e; eauto.
    erewrite co_subst_co_tm_intro; eauto.
    rewrite -co_subst_co_tm_var_eq; eauto.
    rewrite -co_subst_co_tm_intro; eauto.
    destruct phi. eapply E_CApp.
    eapply Typing_weakening with (F:=nil); simpl; eauto 4.
    econstructor; eauto.
    econstructor; eauto.
    assert (Q: x `notin` L1). fsetdec. apply h2 in Q. 
    apply Typing_erased in Q. auto.
Qed.

Lemma DefEq_regularity :
  forall G D A B T, DefEq G D A B T -> PropWff G (Eq A B T).
Proof.
  intros G D A B T H.
  apply DefEqIso_regularity in H.
  split_hyp.
  apply E_Wff; auto.
  eapply Typing_regularity; eauto.
Qed.

Lemma Iso_regularity :
  forall G D phi1 phi2, Iso G D phi1 phi2 -> PropWff G phi1 /\ PropWff G phi2.
Proof.
  intros G D phi1 phi2 H.
  eapply (third DefEqIso_regularity); eauto.
Qed.


Lemma PropWff_regularity :
  forall G A B T, PropWff G (Eq A B T) ->  Typing G A T /\ Typing  G B T.
Proof.
  intros G A B T H.
  inversion H; subst.
  repeat split; auto.
Qed.

(* -------------------------------------------------------------- *)

Lemma DefEq_conv : forall G D a b A B, DefEq G D a b A ->
                                  DefEq G (dom G) A B a_Star -> DefEq G D a b B.
Proof.
  intros. eauto.
Qed.


Lemma trans_iso : forall G D phi1 phi2 phi3,
    Iso G D phi1 phi2 -> Iso G D phi2 phi3 -> Iso G D phi1 phi3.
Proof.
  intros G D phi1 phi2 phi3 H1 H2.
  destruct (Iso_regularity H1) as (WFF1 & WFF2).
  inversion WFF1. inversion WFF2. subst.
  destruct (Iso_regularity H2) as (WFF3 & WFF4).
  inversion WFF3. inversion WFF4. subst.

  have CTX: Ctx G by eauto 2.

  have DE1: DefEq G D (a_CPi (Eq a b A) a_Star) (a_CPi (Eq a0 b0 A0) a_Star) a_Star.
  { pick fresh x and apply E_CPiCong; eauto 2.
    unfold open_tm_wrt_co. simpl.
    constructor. constructor. constructor; auto.

    pick fresh x and apply E_CPi; eauto 2.
    unfold open_tm_wrt_co. simpl.
    constructor. constructor; auto.

    pick fresh x and apply E_CPi; eauto 2.
    unfold open_tm_wrt_co. simpl.
    constructor. constructor; auto.
  }

  have DE2: DefEq G D (a_CPi (Eq a0 b0 A0) a_Star) (a_CPi (Eq a2 b2 A2) a_Star) a_Star.
  { pick fresh x and apply E_CPiCong; eauto 2.
    unfold open_tm_wrt_co. simpl.
    constructor. constructor. constructor; auto.

    pick fresh x and apply E_CPi; eauto 2.
    unfold open_tm_wrt_co. simpl.
    constructor. constructor; auto.

    pick fresh x and apply E_CPi; eauto 2.
    unfold open_tm_wrt_co. simpl.
    constructor. constructor; auto.
  }

  move: (E_Trans _ _ _ _ _ _ DE1 DE2) => DE3.

  eapply E_CPiFst. eauto.
Qed.

Lemma iso_cong : forall G D A A' B B' T T',
    DefEq G D A A' T -> DefEq G D B B' T -> DefEq G D T T' a_Star ->
    Iso G D (Eq A B T) (Eq A' B' T').
    Proof.
      intros.
      move: (DefEq_regularity H) => p0. inversion p0.
      move: (DefEq_regularity H0) => p1. inversion p1.
      move: (DefEq_regularity H1) => p2. inversion p2.
      subst.
      have AT: Typing G A T'.
      eapply E_Conv; eauto using DefEq_weaken_available.
      have AT': Typing G A' T'.
      eapply E_Conv; eauto using DefEq_weaken_available.
      have BT: Typing G B T'.
      eapply E_Conv; eauto using DefEq_weaken_available.
      have BT': Typing G B' T'.
      eapply E_Conv; eauto using DefEq_weaken_available.
      have IA: Iso G D (Eq A A' T) (Eq A A' T').
      eapply E_IsoConv; eauto 2.
      have IB: Iso G D (Eq B B' T) (Eq B B' T').
      eapply E_IsoConv; eauto 2.
      eapply trans_iso with (phi2 := Eq A B T').
      eapply E_IsoConv; eauto.
      eapply E_PropCong; eauto 2.
    Qed.


(* ----------------------------------------------------------------------------- *)

Lemma E_PiCong2 :  ∀ (L : atoms) (G : context) (D : available_props) rho (A1 B1 A2 B2 : tm),
    DefEq G D A1 A2 a_Star
    → (∀ x : atom,
          x `notin` L
          → DefEq ([(x, Tm A1)] ++ G) D (open_tm_wrt_tm B1 (a_Var_f x))
                  (open_tm_wrt_tm B2 (a_Var_f x)) a_Star)
    → DefEq G D (a_Pi rho A1 B1) (a_Pi rho A2 B2) a_Star.
Proof.
  intros.
  move: (DefEq_regularity H) => WFF.
  inversion WFF. subst.
  assert (Typing G A1 a_Star). eauto 1.
  assert (Typing G (a_Pi rho A1 B1) a_Star).
  {  eapply (E_Pi L); eauto 1. intros x Fr.
     move: (DefEq_regularity (H0 x Fr)) => WFF2.
     inversion WFF2. subst. eauto 1. }
  assert (Typing G (a_Pi rho A2 B2) a_Star).
  {
     eapply (E_Pi L); eauto 1. intros x Fr.
     move: (DefEq_regularity (H0 x Fr)) => WFF2.
     inversion WFF2. subst.
     have CTX: Ctx (x ~ Tm A1 ++ G) by eauto.
     inversion CTX. subst.
     eapply context_DefEq_typing; eauto 1.
     eapply E_ConsTm; eauto 1.
     econstructor; eauto 1.
     apply refl_context_defeq. eauto 1. }
  eapply E_PiCong; eauto 1.
Qed.

Lemma E_CPiCong2  : ∀ (L : atoms) (G : context) (D : available_props) (phi1 : constraint)
                      (A : tm) (phi2 : constraint) (B : tm),
    Iso G D phi1 phi2
    → (∀ c : atom,
          c `notin` L
              → DefEq ([(c, Co phi1)] ++ G) D (open_tm_wrt_co A (g_Var_f c))
                      (open_tm_wrt_co B (g_Var_f c)) a_Star)

    → DefEq G D (a_CPi phi1 A) (a_CPi phi2 B) a_Star.
Proof.
  intros.
  move: (Iso_regularity H) => [h0 h1].
  inversion h0. inversion h1. subst.
  assert (Typing G (a_CPi (Eq a b A0) A) a_Star).
  { eapply (E_CPi L); eauto 1. intros x Fr.
    move: (DefEq_regularity (H0 x Fr)) => WFF2.
    inversion WFF2. subst. eauto 1. }
  assert (Typing G (a_CPi (Eq a0 b0 A1) B) a_Star).
  { eapply (E_CPi L); eauto 1. intros x Fr.
    move: (DefEq_regularity (H0 x Fr)) => WFF2.
    inversion WFF2. subst.
    have CTX: Ctx (x ~ Co (Eq a b A0) ++ G) by eauto.
    inversion CTX. subst.
    eapply context_DefEq_typing; eauto 1.
    econstructor; eauto 1.
    econstructor; eauto 1.
     apply refl_context_defeq. eauto 1.
  }
  eapply E_CPiCong; eauto 1.
Qed.


(* could also be an exists form *)
Lemma E_Pi2 : forall L G rho A B,
    (∀ x : atom, x `notin` L → Typing ([(x, Tm A)] ++ G) (open_tm_wrt_tm B (a_Var_f x)) a_Star) ->
    Typing G (a_Pi rho A B) a_Star.
Proof.
  intros.
  eapply E_Pi; eauto.
  pick fresh x.
  move: (H x ltac:(auto)) => h0.
  have h1: Ctx (x ~ Tm A ++ G) by eauto.
  inversion h1. auto.
Qed.

Lemma E_Abs2 : ∀ (L : atoms) (G : context) (rho : relflag) (a A B : tm),
    (∀ x : atom,
        x `notin` L → Typing ([(x, Tm A)] ++ G) (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x)))
    → (∀ x : atom, x `notin` L → RhoCheck rho x (open_tm_wrt_tm a (a_Var_f x)))
    → Typing G (a_UAbs rho a) (a_Pi rho A B).
Proof.
  intros.
  eapply E_Abs; eauto.
  pick fresh x.
  move: (H x ltac:(auto)) => h0.
  have h1: Ctx (x ~ Tm A ++ G) by eauto.
  inversion h1. auto.
Qed.

Lemma E_Conv2 : ∀ (G : context) (a B A : tm),
    Typing G a A → DefEq G (dom G) A B a_Star →
    Typing G a B.
Proof.
  intros.
  eapply E_Conv; eauto.
  eapply DefEq_regularity in H0.
  inversion H0.
  auto.
Qed.

Lemma E_CPi2 :  ∀ (L : atoms) (G : context) (phi : constraint) (B : tm),
    (∀ c : atom, c `notin` L → Typing ([(c, Co phi)] ++ G) (open_tm_wrt_co B (g_Var_f c)) a_Star) ->
    Typing G (a_CPi phi B) a_Star.
Proof.
  intros.
  eapply E_CPi; eauto.
  pick fresh x.
  move: (H x ltac:(auto)) => h0.
  have h1: Ctx (x ~ Co phi ++ G); eauto.
  inversion h1. auto.
Qed.

Lemma E_CAbs2 : ∀ (L : atoms) (G : context) (a : tm) (phi : constraint) (B : tm),
       (∀ c : atom,
        c `notin` L → Typing ([(c, Co phi)] ++ G) (open_tm_wrt_co a (g_Var_f c)) (open_tm_wrt_co B (g_Var_f c)))
       → Typing G (a_UCAbs a) (a_CPi phi B).
Proof.
  intros.
  eapply E_CAbs; eauto.
  pick fresh x.
  move: (H x ltac:(auto)) => h0.
  have h1: Ctx (x ~ Co phi ++ G); eauto.
  inversion h1. auto.
Qed.


Lemma E_AbsCong2
     : ∀ (L : atoms) (G : context) (D : available_props) (rho : relflag) (b1 b2 A1 B : tm),
       (∀ x : atom,
        x `notin` L
        → DefEq ([(x, Tm A1)] ++ G) D (open_tm_wrt_tm b1 (a_Var_f x)) (open_tm_wrt_tm b2 (a_Var_f x))
            (open_tm_wrt_tm B (a_Var_f x)))
       → (∀ x : atom, x `notin` L → RhoCheck rho x (open_tm_wrt_tm b1 (a_Var_f x)))
       → (∀ x : atom, x `notin` L → RhoCheck rho x (open_tm_wrt_tm b2 (a_Var_f x)))
       → DefEq G D (a_UAbs rho b1) (a_UAbs rho b2) (a_Pi rho A1 B).
Proof.
  intros.
  eapply E_AbsCong; eauto.
  pick fresh x.
  move: (H x ltac:(auto)) => h0.
  have h1: Ctx (x ~ Tm A1 ++ G) by eauto.
  inversion h1; auto.
Qed.

Lemma E_CAbsCong2
     : ∀ (L : atoms) (G : context) (D : available_props) (a b : tm) (phi1 : constraint)
       (B : tm),
       (∀ c : atom,
        c `notin` L
        → DefEq ([(c, Co phi1)] ++ G) D (open_tm_wrt_co a (g_Var_f c)) (open_tm_wrt_co b (g_Var_f c))
                (open_tm_wrt_co B (g_Var_f c))) → DefEq G D (a_UCAbs a) (a_UCAbs b) (a_CPi phi1 B).
Proof.
  intros.
  eapply E_CAbsCong; eauto.
  pick fresh x.
  move: (H x ltac:(auto)) => h0.
  have h1: Ctx (x ~ Co phi1 ++ G) by eauto.
  inversion h1. auto.
Qed.

Lemma E_Fam2 : ∀ (G : context) (F : tyfam) (A a : tm),
       Ctx G
       → binds F (Ax a A) toplevel → Typing G (a_Fam F) A.
Proof.
  intros.
  eapply E_Fam; eauto.
  move: (toplevel_closed H0) => h0.
  eapply Typing_regularity. eauto.
Qed.


Lemma E_Wff2 : ∀ (G : context) (a b A : tm), Typing G a A → Typing G b A → PropWff G (Eq a b A).
Proof.
  intros.
  eapply E_Wff; eauto.
  eapply Typing_regularity. eauto.
Qed.

End ext_invert.
