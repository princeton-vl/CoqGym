
Require Import FcEtt.fc_invert.
Require Import Omega.
Require Import Coq.Arith.Wf_nat.
Require Import FcEtt.toplevel.

Require Import FcEtt.erase_syntax.
Require Import FcEtt.sigs.
Require Import FcEtt.fc_unique.
Require Import FcEtt.fc_invert.
Require Import FcEtt.fc_context_fv.

Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.


Module fc_get (wf : fc_wf_sig) (weak : fc_weak_sig) (subst : fc_subst_sig) (unique: fc_unique_sig).
Import wf weak subst.

Module invert := fc_invert wf weak subst.
Import invert.

(* -------------------------------------------------------------------------------------- *)

(* This function looks at an annotated term and returns its type.
*)

Fixpoint get_tpg_n (n : nat) (G : context) (a : tm) { struct n } : tm :=
match n with
| 0 => a_Star
| S m =>
  match a with
  | a_Star => a_Star
  | a_Var_f x =>
    match binds_lookup _ x G with
    | inl (exist (Tm A) _) => A
    | _ => a_Star
    end
  | a_Pi  rho A B => a_Star
  | a_Abs rho A a =>
    let (x,_) := atom_fresh (dom G) in
    a_Pi rho A (close_tm_wrt_tm x (get_tpg_n m ((x,Tm A)::G) (open_tm_wrt_tm a (a_Var_f x))))
  | a_App a1 rho a2 =>
    match get_tpg_n m G a1 with
      | a_Pi rho A B => open_tm_wrt_tm B a2
      | _ => a_Star
    end
  | a_Conv a g => let (_,b) := get_deq_n m G g in b
  | a_CPi phi B => a_Star
  | a_CAbs phi a => let (x,_) := atom_fresh (dom G) in
                   a_CPi phi (close_tm_wrt_co x (get_tpg_n m ((x,Co phi)::G) (open_tm_wrt_co a (g_Var_f x))))
  | a_Fam F =>
    match binds_lookup _ F an_toplevel with
    | inl (exist (Ax a A) _) => A
    | _ => a_Star
    end
  | a_CApp a1 g2 =>
    match get_tpg_n m G a1 with
      | a_CPi phi B => open_tm_wrt_co B g2
      | _ => a_Star
    end
  | a_Const T =>
     match binds_lookup _ T an_toplevel with
    | inl (exist (Cs A) _) => A
    | _ => a_Star
    end
  | _ => a_Star
  end
end
with
get_iso_n (n : nat) (G : context) (g : co) : (constraint * constraint) :=
  match n with
  | 0 => (Eq a_Star a_Star a_Star,Eq a_Star a_Star a_Star)
  | S m =>
    match g with
    | (g_EqCong g1 A g2) =>
      let (A1, A2) := get_deq_n m G g1 in
      let (B1, B2) := get_deq_n m G g2 in
      (Eq A1 B1 A, Eq A2 B2 A)
    | g_CPiFst g =>
      let (T1,T2) := get_deq_n m G g in
      match (T1, T2) with
      | (a_CPi phi1 A2, a_CPi phi2 B2) => (phi1, phi2)
      | _ => (Eq a_Star a_Star a_Star,Eq a_Star a_Star a_Star)
      end
    | g_Sym g =>
      let (phi2, phi1) := get_iso_n m G g in
      (phi1, phi2)
    | g_IsoConv (Eq a1 a2 A) (Eq a1' a2' B) g =>
      (Eq a1 a2 A, Eq a1' a2' B)
    | _ => (Eq a_Star a_Star a_Star,Eq a_Star a_Star a_Star)
    end
  end
with
get_deq_n (n : nat) (G : context) (g : co) : (tm * tm) :=
  match n with
  | 0 => (a_Star, a_Star)
  | S m =>
    match g with
    | g_Var_f c => match binds_lookup _ c G with
                  | inl (exist (Co (Eq a b A)) _) => (a,b)
                  | _ => (a_Star, a_Star)
                  end
    | g_Refl a => (a,a)
    | g_Refl2 a b g => (a,b)
    | g_Beta a b => (a,b)
    | g_Sym g => let (a,b) := get_deq_n m G g in
                (b,a)
    | g_Trans g1 g2 =>
      let (a,c1) := get_deq_n m G g1 in
      let (c2, b) := get_deq_n m G g2 in
      (a,b)
    | g_PiCong rho g1 g2 =>
      let (x,_) := atom_fresh (dom G) in
      let (A1,A2) := get_deq_n m G g1 in
      let (B1,B2) := get_deq_n m ([(x, Tm A1)] ++ G) (open_co_wrt_tm g2 (a_Var_f x)) in
      let B3 := tm_subst_tm_tm (a_Conv (a_Var_f x) (g_Sym g1)) x B2 in
      (a_Pi rho A1 (close_tm_wrt_tm x B1), a_Pi rho A2 (close_tm_wrt_tm x B3))
    | g_AbsCong rho g1 g2 =>
      let (x,_) := atom_fresh (dom G) in
      let (A1,A2) := get_deq_n m G g1 in
      let (b1,b2) := get_deq_n m ([(x,Tm A1)] ++ G) (open_co_wrt_tm g2 (a_Var_f x)) in
      let b3 := tm_subst_tm_tm (a_Conv (a_Var_f x) (g_Sym g1)) x b2 in
      (a_Abs rho A1 (close_tm_wrt_tm x b1), a_Abs rho A2 (close_tm_wrt_tm x b3))
    | g_AppCong g1 rho g2 =>
      let (a1, b1) := get_deq_n m G g1 in
      let (a2, b2) := get_deq_n m G g2 in
      (a_App a1 rho a2, a_App b1 rho b2)
    | g_PiFst g =>
      let (a,b) := get_deq_n m G g in
      match (a,b) with
      | (a_Pi rho1 A1 B1, a_Pi rho2 A2 B2) => (A1, A2)
      | (_,_) => (a_Star, a_Star)
      end
    | g_PiSnd g1 g2 =>
      let (T1,T2) := get_deq_n m G g1 in
      let (a1,a2) := get_deq_n m G g2 in
      match (T1,T2) with
      | (a_Pi rho1 A1 B1, a_Pi rho2 A2 B2) =>
        (open_tm_wrt_tm B1 a1, open_tm_wrt_tm B2 a2)
      | (_,_) => (a_Star, a_Star)
      end
    | g_CPiCong g1 g3 =>
      let (phi1,phi2) := get_iso_n m G g1 in
      let (x,_) := atom_fresh (dom G) in
      let (B1,B2) := get_deq_n m ([(x,Co phi1)] ++ G)
                               (open_co_wrt_co g3 (g_Var_f x)) in
      let B3 := co_subst_co_tm (g_Cast (g_Var_f x) (g_Sym g1)) x B2 in
      (a_CPi phi1 (close_tm_wrt_co x B1), a_CPi phi2 (close_tm_wrt_co x B3))
    | g_CAbsCong g1 g2 g3 =>
      let (phi1,phi2) := get_iso_n m G g1 in
      let (x,_) := atom_fresh (dom G) in
      let (b1,b2) := get_deq_n m ([(x,Co phi1)] ++ G)
                               (open_co_wrt_co g2 (g_Var_f x)) in
      let b3 := co_subst_co_tm (g_Cast (g_Var_f x) (g_Sym g1)) x b2 in
      (a_CAbs phi1 (close_tm_wrt_co x b1), a_CAbs phi2 (close_tm_wrt_co x b3))

    | (g_CAppCong g1 g2 g3) =>
      let (a1, b1) := get_deq_n m G g1 in
      (a_CApp a1 g2,a_CApp b1 g3)
    | (g_CPiSnd g1 g2 g3) =>
      match get_deq_n m G g1 with
      | (a_CPi (Eq a a' A) B1, a_CPi (Eq b b' B) B2) =>
         (open_tm_wrt_co  B1   g2, open_tm_wrt_co  B2   g3 )
      | (_,_) => (a_Star, a_Star)
      end
    | (g_Cast g1 g2) =>
      match get_iso_n m G g2 with
      | (Eq a a' A, Eq b b' B) => (b,b')
      end
    |  (g_IsoSnd g) =>
       match get_iso_n m G g with
       | (Eq a a' A, Eq b b' B) => (A, B)
       end
    | (g_Eta b) =>
      let (x,_) := atom_fresh (dom G) in
      match get_tpg_n m G b with
      | (a_Pi rho A B) => (a_Abs rho A (close_tm_wrt_tm x (a_App b rho (a_Var_f x))), b)
      | (a_CPi phi _) =>  (a_CAbs phi (close_tm_wrt_co x (a_CApp b (g_Var_f x))), b)
      | _ => (a_Star, a_Star)
      end
     (* Left/Right
    | (g_Left g1 g2) =>
      match get_deq_n m G g1 with
      | (a_App a _ _, a_App a' _ _) => (a,a')
      | (a_CApp a _, a_CApp a' _) => (a,a')
      | (_,_) => (a_Star, a_Star)
      end
    | (g_Right g1 g2) =>
      match get_deq_n m G g1 with
      | (a_App _ _ a, a_App _ _ a') => (a,a')
      | (_,_) => (a_Star, a_Star)
      end
     *)
    | _ => (a_Star, a_Star)
    end
  end.

Definition get_tpg (G : context) (a:tm) : tm :=
  get_tpg_n (size_tm a) G a.
Definition get_deq (G : context) (g:co) : (tm*tm) :=
  get_deq_n (size_co g) G g.
Definition get_iso (G : context) (g:co) : (constraint*constraint) :=
  get_iso_n (size_co g) G g.


Lemma get_n_correct : forall n,
    (forall G a A B, size_tm a <= n -> AnnTyping G a A -> get_tpg_n n G a = B -> A = B) /\
    (forall G D g A B A' B', size_co g <= n -> AnnDefEq G D g A B ->
                        get_deq_n n G g = (A',B') -> A = A' /\ B = B') /\
    (forall G D g A B A' B', size_co g <= n -> AnnIso G D g A B ->
                        get_iso_n n G g = (A',B') -> A = A' /\ B = B').

Proof.
  intro n.
  eapply (lt_wf_ind n). clear n. intros.
  split.
  { intros G a A B HS HT GT.
    destruct a; simpl in *; try  (destruct n; [inversion HS | try solve [inversion HT; subst;  auto]]).
    - inversion HT. subst. simpl.
      assert (U : uniq G). { eapply AnnCtx_uniq. eauto. }
      destruct (binds_lookup _ x G) as [ [ [A0 | phi] P] | NB].
      move: (binds_unique _ _ _ _ _ H3 P U) => h0. inversion h0. auto.
      move: (binds_unique _ _ _ _ _ H3 P U) => h0. inversion h0.
      eapply NB in H3. done.
    - destruct (An_Abs_inversion HT) as (B1 & EQ & T1 & HB1). subst.
      simpl.
      destruct (atom_fresh (dom G)).
      f_equal.
      move: (HB1 x n0) => [R1 TB1]. clear HB1.
      move: (H n ltac:(omega)) => [h0 _].
      assert (size_tm (open_tm_wrt_tm a2 (a_Var_f x)) = size_tm a2). eauto with lngen.
      move: (h0 ((x, Tm a1) :: G) (open_tm_wrt_tm a2 (a_Var_f x)) (open_tm_wrt_tm B1 (a_Var_f x))
                (get_tpg_n n ((x, Tm a1) :: G) (open_tm_wrt_tm a2 (a_Var_f x)))
            ltac:(omega) TB1 ltac:(auto))
      => h1.
      rewrite <- h1.
      rewrite close_tm_wrt_tm_open_tm_wrt_tm; eauto.
      move: (AnnTyping_context_fv HT) => [_ [_ [f1 _]]]. simpl in f1.
      fsetdec.
    - inversion HT. subst. simpl.
      move: (H n ltac:(omega)) => [h0 _].
      move: (@h0 G a1 (a_Pi rho A0 B0) (get_tpg_n n G a1) ltac:(omega) H5 eq_refl) => h1.
      rewrite <- h1.
      auto.
    - inversion HT. subst.
      Opaque an_toplevel.
      simpl.
      destruct (binds_lookup _ F an_toplevel) as [[ [A0 | phi] P] | NB].
      move: (binds_unique _ _ _ _ _ H2 P uniq_an_toplevel) => h0. inversion h0.
      move: (binds_unique _ _ _ _ _ H2 P uniq_an_toplevel) => h0. inversion h0. auto.
      eapply NB in H2. done.
    - inversion HT. subst. Opaque an_toplevel.
      simpl.
      destruct (binds_lookup _ T an_toplevel) as [ [ [A0 | phi] P] | NB].
      move: (binds_unique _ _ _ _ _ H2 P uniq_an_toplevel) => h0. inversion h0. auto.
      move: (binds_unique _ _ _ _ _ H2 P uniq_an_toplevel) => h0. inversion h0.
      eapply NB in H2. done.
    - inversion HT. subst. simpl.
      remember (get_deq_n n G g) as GD. destruct GD as [A' B'].
      move: (H n ltac:(omega)) => [_ [h0 _]].
      destruct (h0 _ _ g _ _ A' B' ltac:(omega) H4).
      auto. subst. auto.
    - destruct (An_CAbs_inversion HT) as (B1 & EQ & HT1). subst. simpl.
      destruct (atom_fresh (dom G)). f_equal. simpl_env.
      move: (HT1 x n0) => [R1 TB1]. clear HT1.
      move: (H n ltac:(omega)) => [h0 _].
      assert (size_tm (open_tm_wrt_co a (g_Var_f x)) = size_tm a). eauto with lngen.
      move: (h0 _ (open_tm_wrt_co a (g_Var_f x)) _ _  ltac:(omega) TB1 eq_refl) => h1.
      rewrite <- h1.
      rewrite close_tm_wrt_co_open_tm_wrt_co; eauto.
      move: (AnnTyping_context_fv HT) => [_ [_ [_ f1]]]. simpl in f1.
      fsetdec.
   - inversion HT. subst. simpl.
     move: (H n ltac:(omega)) => [h0 _].
     move: (@h0 G a (a_CPi (Eq a0 b A1) B0) (get_tpg_n n G a)
                 ltac:(omega) H3 eq_refl) => h1.
     rewrite <- h1.
     auto.
  } split. {
    intros G D g A B A' B' SZ DE GET.
    destruct g; simpl in *; (destruct n; [inversion SZ| try solve [inversion DE; subst; simpl;  auto]]).
    - inversion DE. subst. simpl in GET.
      assert (U : uniq G). { eapply AnnCtx_uniq. eauto. }
      destruct (binds_lookup _ c G) as [[ [ A1 | phi] P] | NB].
      move: (binds_unique _ _ _ _ _ H2 P U) => h0. inversion h0. destruct phi. inversion GET. subst.
      move: (binds_unique _ _ _ _ _ H2 P U) => h0. inversion h0. auto.
      eapply NB in H2. done.
    - inversion DE. subst.  simpl in GET. inversion GET. auto.
    - inversion DE. subst. simpl in GET. inversion GET. auto.
    - inversion DE. subst. simpl in GET. inversion GET. auto.
    - inversion DE. subst. simpl in GET.
      remember (get_deq_n n G g) as GG.
      destruct GG. inversion GET. subst. clear GET.
      move: (H n ltac:(omega)) => [_ [h0 _]].
      move: (h0 G D g _ _ B' A' ltac:(omega) H6 ltac:(auto)) => [h1 h2]. subst.
      auto.
    - inversion DE. subst. simpl in GET.
      remember (get_deq_n n G g1) as GG1. destruct GG1.
      remember (get_deq_n n G g2) as GG2. destruct GG2.
      inversion GET. subst.
      move: (H n ltac:(omega)) => [_ [h0 _]].
      move: (h0 G D g1 _ _ A' t0 ltac:(omega) H2 ltac:(auto)) => [h1 h2]. subst.
      move: (h0 G D g2 _ _ t1 B' ltac:(omega) H3 ltac:(auto)) => [h1 h2]. subst.
      auto.
    - destruct (An_PiCong_inversion DE) as (A1 & B1 & A2 & B2 & B3 &
                                             E1 & E2 & T1 & T2 & T3 & DE1 & DE2).
      simpl in GET.
      destruct (atom_fresh (dom G)).
      remember (get_deq_n n G g1) as GET1.
      destruct GET1 as [A1' A2'].
      remember (get_deq_n n ((x, Tm A1') :: G) (open_co_wrt_tm g2 (a_Var_f x))) as GET2.
      destruct GET2 as [B1' B2'].
      inversion GET. subst. clear GET.
      move: (H n ltac:(omega)) => [_ [h1 _]].
      move: (h1 G D g1 A1 A2 A1' A2' ltac:(omega) DE1 ltac:(auto)) => [E1 E2].
      subst.
      assert (SS : size_co (open_co_wrt_tm g2 (a_Var_f x)) = size_co g2).
      auto with lngen.
      move: (DE2 x ltac:(auto)) => [DEx E3].
      move: (h1 ([(x, Tm A1')] ++ G) D
                (open_co_wrt_tm g2 (a_Var_f x))
                (open_tm_wrt_tm B1 (a_Var_f x))
                (open_tm_wrt_tm B2 (a_Var_f x))
                B1' B2' ltac:(omega) ltac:(auto) ltac:(auto)) => [E1 E2].
      subst.
      move: (AnnTyping_context_fv T1) => [f1 [_ _]]. simpl in f1.
      move: (AnnTyping_context_fv T2) => [f2 [_ _]]. simpl in f2.
      move: (AnnTyping_context_fv T3) => [f3 [_ _]]. simpl in f3.
      assert (x `notin` fv_tm_tm_tm B2 \u fv_tm_tm_tm B1 \u fv_tm_tm_tm B3). fsetdec.
      split. f_equal. rewrite close_tm_wrt_tm_open_tm_wrt_tm. auto. auto.
      f_equal.
      rewrite tm_subst_tm_tm_open_tm_wrt_tm.
      rewrite tm_subst_tm_tm_var.
      rewrite tm_subst_tm_tm_fresh_eq; auto.
      rewrite <- E3.
      rewrite close_tm_wrt_tm_open_tm_wrt_tm. auto.
      auto.
      econstructor; eauto.
      econstructor. eapply AnnDefEq_lc; eauto.
    - destruct (An_AbsCong_inversion DE) as (A1 & A2 & b1 & b2 & b3 & C2 &
                                             E1 & E2 & T1 & T2 & DE1 & T3 & DE2).
      simpl in GET.
      destruct (atom_fresh (dom G)).
      remember (get_deq_n n G g1) as GET1.
      destruct GET1 as [A1' A2'].
      remember (get_deq_n n ((x, Tm A1') :: G) (open_co_wrt_tm g2 (a_Var_f x))) as GET2.
      destruct GET2 as [b1' b2'].
      inversion GET. subst. clear GET.
      move: (H n ltac:(omega)) => [_ [h1 _]].
      move: (h1 G D g1 A1 A2 A1' A2' ltac:(omega) DE1 ltac:(auto)) => [E1 E2]. subst.
      assert (SS : size_co (open_co_wrt_tm g2 (a_Var_f x)) = size_co g2). auto with lngen.
      move: (DE2 x ltac:(auto)) => [DEx [E3 [RC1 RC2]]].
      move: (h1 ([(x, Tm A1')] ++ G) D
                (open_co_wrt_tm g2 (a_Var_f x))
                (open_tm_wrt_tm b1 (a_Var_f x))
                (open_tm_wrt_tm b2 (a_Var_f x))
                b1' b2' ltac:(omega) ltac:(auto) ltac:(auto)) => [E1 E2].
      subst.
      move: (AnnDefEq_context_fv DE) => [_ [_ [f1 [_ [f2 _]]]]]. simpl in f1. simpl in f2.
      move: (AnnTyping_context_fv T3) => [f3 [_ _]]. simpl in f3.
      assert (x `notin` fv_tm_tm_tm b2 \u fv_tm_tm_tm b1 \u fv_tm_tm_tm b3). fsetdec.
      split. f_equal.
      rewrite close_tm_wrt_tm_open_tm_wrt_tm. auto. auto.
      f_equal.
      rewrite tm_subst_tm_tm_open_tm_wrt_tm.
      rewrite tm_subst_tm_tm_var.
      rewrite tm_subst_tm_tm_fresh_eq; auto.
      rewrite <- E3.
      rewrite close_tm_wrt_tm_open_tm_wrt_tm. auto.
      auto.
      econstructor; eauto.
      econstructor. eapply AnnDefEq_lc; eauto.
    - inversion DE. simpl in *. subst.
      remember (get_deq_n n G g1) as GG1. destruct GG1.
      remember (get_deq_n n G g2) as GG2. destruct GG2.
      inversion GET.
      move: (H n ltac:(omega)) => [_ [h0 _]].
      move: (h0 _ _ g1 _ _ t t0 ltac:(omega) H3 ltac:(auto)) => [E1 E2]. subst.
      move: (h0 _ _ g2 _ _ t1 t2 ltac:(omega) H4 ltac:(auto)) => [E1 E2]. subst.
      auto.
    - inversion DE. simpl in *. subst.
      remember (get_deq_n n G g) as GG. destruct GG.
      move: (H n ltac:(omega)) => [_ [h0 _]].
      move: (h0 _ _ g _ _ t t0 ltac:(omega) H3 ltac:(auto)) => [E1 E2]. subst.
      inversion GET. auto.
    - inversion DE. simpl in *. subst.
      remember (get_iso_n n G g) as GG. destruct GG.
      move: (H n ltac:(omega)) => [_ [_ h0]].
      move: (h0 _ _ g _ _ c c0 ltac:(omega) H3 ltac:(auto)) => [E1 E2]. subst.
      inversion GET. auto.
    - inversion DE. simpl in *. subst.
      remember (get_deq_n n G g1) as GG1. destruct GG1.
      remember (get_deq_n n G g2) as GG2. destruct GG2.
      move: (H n ltac:(omega)) => [_ [h0 _]].
      move: (h0 _ _ g1 _ _ t t0 ltac:(omega) H2 ltac:(auto)) => [E1 E2]. subst.
      move: (h0 _ _ g2 _ _ t1 t2 ltac:(omega) H3 ltac:(auto)) => [E1 E2]. subst.
      inversion GET. auto.
    - destruct (An_CPiCong_inversion DE) as (phi1 & phi2 & b1 & b2 & b3 &
                                             E1 & E2 & I1 & T1 & T2 & T3 & DE2).
      simpl in *.
      remember (get_iso_n n G g1) as GG1. destruct GG1 as [phi1' phi2'].
      destruct (atom_fresh (dom G)) as [x Fr].
      remember (get_deq_n n ((x, Co phi1') :: G) (open_co_wrt_co g2 (g_Var_f x))) as GG2. destruct GG2.
      move: (H n ltac:(omega)) => [_ [h0 h1]].
      move: (h1 _ _ g1 _ _ phi1' phi2' ltac:(omega) I1 ltac:(auto)) => [E1' E2']. subst.
      assert (SS : size_co (open_co_wrt_co g2 (g_Var_f x)) = size_co g2). auto with lngen.
      move: (DE2 x Fr) => [DE2' EQ].
      inversion GET. clear GET.
      move: (h0 _ _ (open_co_wrt_co g2 (g_Var_f x)) _ _ t t0 ltac:(omega) DE2' ltac:(auto)) => [E1' E2']. subst.
      move: (AnnDefEq_context_fv DE) => [_ [_ [f1' [f1 [f2' f2]]]]]. simpl in *.
      move: (AnnTyping_context_fv T3) => [f3' [f3 _]]. simpl in *.
      split.
      + f_equal. rewrite close_tm_wrt_co_open_tm_wrt_co. auto. auto.
      + f_equal.
        rewrite co_subst_co_tm_open_tm_wrt_co.
        rewrite co_subst_co_co_var.
        rewrite co_subst_co_tm_fresh_eq; auto.
        rewrite <- EQ.
        rewrite close_tm_wrt_co_open_tm_wrt_co. auto.
        auto.
        econstructor; eauto.
        econstructor. eapply AnnIso_lc; eauto.
    - destruct (An_CAbsCong_inversion DE) as (phi1 & phi2 & b1 & b2 & b3
                                              & B1 & B2 & B3 &
                                              E1 & E2 & I1 & T1 & T2 & T3
                                              & DE1 & DE2).
      simpl in *.

            remember (get_iso_n n G g1) as GG1. destruct GG1 as [phi1' phi2'].
      destruct (atom_fresh (dom G)) as [x Fr].
      remember (get_deq_n n ((x, Co phi1') :: G) (open_co_wrt_co g2 (g_Var_f x))) as GG2. destruct GG2.
      move: (H n ltac:(omega)) => [_ [h0 h1]].
      move: (h1 _ _ g1 _ _ phi1' phi2' ltac:(omega) I1 ltac:(auto)) => [E1' E2']. subst.
      assert (SS : size_co (open_co_wrt_co g2 (g_Var_f x)) = size_co g2). auto with lngen.
      move: (DE2 x Fr) => [DE2' EQ].
      inversion GET. clear GET.
      move: (h0 _ _ (open_co_wrt_co g2 (g_Var_f x)) _ _ t t0 ltac:(omega) DE2' ltac:(auto)) => [E1' E2']. subst.
      move: (AnnDefEq_context_fv DE) => [_ [_ [f1' [f1 [f2' f2]]]]]. simpl in *.
      move: (AnnTyping_context_fv T3) => [f3' [f3 _]]. simpl in *.
      split.
      + f_equal. rewrite close_tm_wrt_co_open_tm_wrt_co. auto. auto.
      + f_equal.
        rewrite co_subst_co_tm_open_tm_wrt_co.
        rewrite co_subst_co_co_var.
        rewrite co_subst_co_tm_fresh_eq; auto.
        rewrite <- EQ.
        rewrite close_tm_wrt_co_open_tm_wrt_co. auto.
        auto.
        econstructor; eauto.
        econstructor. eapply AnnIso_lc; eauto.
    - inversion DE. simpl in *. subst.
      remember (get_deq_n n G g1) as GG1. destruct GG1.
      remember (get_deq_n n G g2) as GG2. destruct GG2.
      move: (H n ltac:(omega)) => [_ [h0 _]].
      move: (h0 _ _ g1 _ _ t t0 ltac:(omega) H3 ltac:(auto)) => [E1 E2]. subst.
      inversion GET. auto.
    - inversion DE. simpl in *. subst.
      remember (get_deq_n n G g1) as GG1. destruct GG1.
      move: (H n ltac:(omega)) => [_ [h0 _]].
      move: (h0 _ _ g1 _ _ t t0 ltac:(omega) H5 ltac:(auto)) => [E1 E2]. subst.
      inversion GET. auto.
    - inversion DE. simpl in *. subst.
      remember (get_deq_n n G g1) as GG1. destruct GG1.
      remember (get_iso_n n G g2) as GG2. destruct GG2.
      move: (H n ltac:(omega)) => [_ [h0 h1]].
      move: (h0 _ _ g1 _ _ t t0 ltac:(omega) H4 ltac:(auto)) => [E1 E2]. subst.
      move: (h1 _ _ g2 _ _ c c0 ltac:(omega) H7 ltac:(auto)) => [E1 E2]. subst.
      inversion GET. auto.
    - inversion DE. simpl in *. subst.
      move: (H n ltac:(omega)) => [h0 _].
      move: (h0  _ B _ _ ltac:(omega) H1 eq_refl) => EQ.
      remember (get_tpg_n n G B) as pi. destruct pi; inversion EQ. subst.
      destruct (atom_fresh (dom G)) as [x Fr].
      inversion GET. subst.
      split; auto.
      f_equal.
      pick fresh y.
      rewrite -(@close_tm_wrt_tm_open_tm_wrt_tm a0 y); auto.
      rewrite H4; auto.
      unfold close_tm_wrt_tm. simpl.
      edestruct eq_dec; try done.
      edestruct eq_dec; try done. 
      f_equal.
      replace (close_tm_wrt_tm_rec 0 y B') with (close_tm_wrt_tm y B'); simpl; auto.
      replace (close_tm_wrt_tm_rec 0 x B') with (close_tm_wrt_tm x B'); simpl; auto.
      pick fresh z for (fv_tm_tm_tm (close_tm_wrt_tm y B') \u fv_tm_tm_tm (close_tm_wrt_tm x B')).
      eapply open_tm_wrt_tm_inj with (x1 := z); auto.
      rewrite -tm_subst_tm_tm_spec.
      rewrite -tm_subst_tm_tm_spec.
      rewrite tm_subst_tm_tm_fresh_eq; auto.
      rewrite tm_subst_tm_tm_fresh_eq; auto.
      destruct (AnnDefEq_context_fv DE) as (_ & _ & _ & _ & h4 & _).
      fsetdec.
      assert (K: (if y == y then a_Var_b 0 else a_Var_f y) = a_Var_b 0).
      destruct (y == y); auto. contradiction.
      assert (K': (if x == x then a_Var_b 0 else a_Var_f x) = a_Var_b 0).
      destruct (x == x); auto. contradiction. rewrite K. rewrite K'. auto.
      
      simpl in *. subst.
      move: (H n ltac:(omega)) => [h0 _].
      assert (EQ: size_tm B <= n). omega. 
      eapply h0 with (G:= G) (A:= (a_CPi phi B0)) in EQ; auto.
      remember (get_tpg_n n G B) as pi. destruct pi; inversion EQ. subst.
      destruct (atom_fresh (dom G)) as [x Fr].
      inversion GET. subst.
      split; auto.
      f_equal.
      pick fresh y.
      rewrite -(@close_tm_wrt_co_open_tm_wrt_co a0 y); auto.
      rewrite H4; auto.
      unfold close_tm_wrt_co. simpl.
      edestruct eq_dec; try done.
      edestruct eq_dec; try done. 
      f_equal.
      replace (close_tm_wrt_co_rec 0 y B') with (close_tm_wrt_co y B'); simpl; auto.
      pick fresh z for (fv_co_co_tm (close_tm_wrt_co y B') \u fv_co_co_tm (close_tm_wrt_co_rec 0 x B')).
      eapply open_tm_wrt_co_inj with (c1 := z); auto.
      rewrite -co_subst_co_tm_spec.
      rewrite -co_subst_co_tm_spec.
      rewrite co_subst_co_tm_fresh_eq; auto.
      rewrite co_subst_co_tm_fresh_eq; auto.
      destruct (AnnDefEq_context_fv DE) as (_ & _ & _ & _ & _ & h4).
      fsetdec.
      assert (K: (if y == y then g_Var_b 0 else g_Var_f y) = g_Var_b 0).
      destruct (y == y); auto. contradiction.
      assert (K': (if x == x then g_Var_b 0 else g_Var_f x) = g_Var_b 0).
      destruct (x == x); auto. contradiction. rewrite K. rewrite K'. auto.
   (* - inversion DE; simpl in *; subst.
      + move: (H n ltac:(omega)) => [h0 [h1 h2]].
        remember (get_deq_n n G g1) as GG1. destruct GG1.
        move: (h1  _ _ g1 _ _ _ _ ltac:(omega) H8 ltac:(eauto)) => [ EQ1 EQ2 ].
        subst.
        inversion GET. auto.
      + move: (H n ltac:(omega)) => [h0 [h1 h2]].
      remember (get_deq_n n G g1) as GG1. destruct GG1.
      move: (h1  _ _ g1 _ _ _ _ ltac:(omega) H8 ltac:(eauto)) => [ EQ1 EQ2 ].
      subst.
      inversion GET. auto.
    - inversion DE; simpl in *; subst.
      move: (H n ltac:(omega)) => [h0 [h1 h2]].
      remember (get_deq_n n G g1) as GG1. destruct GG1.
      move: (h1  _ _ g1 _ _ _ _ ltac:(omega) H8 ltac:(eauto)) => [ EQ1 EQ2 ].
      subst.
      inversion GET. auto. *)
     }
      { intros G D g A B A' B' SZ H1 GET.
      destruct g; (destruct n; [inversion SZ|idtac]); inversion H1;
        simpl in *; subst.
      -  remember (get_iso_n n G g) as GG. destruct GG.
         move: (H n ltac:(omega)) => [_ [h0 h1]].
         move: (h1 _ _ g _ _ c c0 ltac:(omega) H4 ltac:(auto)) => [E1 E2]. subst.
         inversion GET. subst. auto.
      -  remember (get_deq_n n G g) as GG. destruct GG.
         move: (H n ltac:(omega)) => [_ [h0 h1]].
         move: (h0 _ _ g _ _ t t0 ltac:(omega) H4 ltac:(auto)) => [E1 E2]. subst.
         inversion GET. subst. auto.
      - remember (get_deq_n n G g1) as GG. destruct GG.
        remember (get_deq_n n G g2) as GG. destruct GG.
        move: (H n ltac:(omega)) => [_ [h0 h1]].
        move: (h0 _ _ g1 _ _ t t0 ltac:(omega) H4 ltac:(auto)) => [E1 E2]. subst.              move: (h0 _ _ g2 _ _ t1 t2 ltac:(omega) H7 ltac:(auto)) => [E1 E2]. subst.             inversion GET. auto.
      - inversion GET. auto.
    } Unshelve. auto. auto. auto. auto.
Qed.


Lemma get_tpg_correct : (forall G a A B, AnnTyping G a A -> get_tpg G a = B -> A = B).
Proof.
  intros. unfold get_tpg in *.
  move: (get_n_correct (size_tm a)) => [h0 _].
  eapply h0; eauto.
Qed.

Lemma get_deq_correct: (forall G D g A B A' B',  AnnDefEq G D g A B ->
                                            get_deq G g = (A',B') -> A = A' /\ B = B').
Proof.
  intros. unfold get_deq in *.
  move: (get_n_correct (size_co g)) => [_ [h0 _]
                                       ].
  eapply h0; eauto.
Qed.

Lemma get_iso_correct: (forall G D g A B A' B',  AnnIso G D g A B ->
                                            get_iso G g = (A',B') -> A = A' /\ B = B').
Proof.
  intros. unfold get_deq in *.
  move: (get_n_correct (size_co g)) => [_ [_ h0]].
  eapply h0; eauto.
Qed.


Lemma An_PiCong_exists2: forall x1 x2 (G:context) D rho
                           (g1 g2 : co) (A1 B1 A2 B3 B2 : tm),
    x1 `notin` (dom G \u fv_tm_tm_tm B1 \u fv_tm_tm_tm B2 \u  fv_tm_tm_co g2)
    -> x2 `notin` (dom G \u singleton x1 \u fv_tm_tm_tm B2 \u fv_tm_tm_tm B3 \u  fv_tm_tm_co g1)
    -> AnnDefEq G D g1 A1 A2
    → AnnDefEq ([(x1, Tm A1)] ++ G) D (open_co_wrt_tm g2 (a_Var_f x1))
               (open_tm_wrt_tm B1 (a_Var_f x1)) (open_tm_wrt_tm B2 (a_Var_f x1))
    → (open_tm_wrt_tm B3 (a_Var_f x2) =
       open_tm_wrt_tm B2 (a_Conv (a_Var_f x2) (g_Sym g1)))
    → get_tpg G A1 = a_Star
    → get_tpg ([(x1,Tm A1)] ++ G) (open_tm_wrt_tm B1 (a_Var_f x1)) = a_Star
    → get_tpg ([(x1,Tm A1)] ++ G) (open_tm_wrt_tm B2 (a_Var_f x1)) = a_Star
    → get_tpg G A2 = a_Star
    → get_tpg ([(x1,Tm A2)] ++ G) (open_tm_wrt_tm B3 (a_Var_f x1)) = a_Star
    → AnnDefEq G D (g_PiCong rho g1 g2) (a_Pi rho A1 B1) (a_Pi rho A2 B3).
Proof.
intros.
destruct (AnnDefEq_regularity H1) as (C1 & C2 & g' & T1 & T2 & _).
destruct (AnnDefEq_regularity H2) as (C3 & C4 & g'' & T3 & T4 & _).
move: (get_tpg_correct T3 H5) => EQ. subst.
move: (get_tpg_correct T4 H6) => EQ. subst.
move: (get_tpg_correct T1 H4) => EQ. subst.
move: (get_tpg_correct T2 H7) => EQ. subst.
eapply (@An_PiCong_exists x1 x2); eauto.
+ eapply (@An_Pi_exists2 x1); eauto.
+ eapply (@An_Pi_exists2 x2); eauto.
rewrite H3.
rewrite (tm_subst_tm_tm_intro x1); eauto.
replace a_Star with  (tm_subst_tm_tm (a_Conv (a_Var_f x2) (g_Sym g1)) x1 a_Star); auto.
have t1: AnnCtx G by eauto with ctx_wff.
move: (AnnTyping_weakening T2 [(x1,Tm A1)] nil G eq_refl) => t2. simpl_env in t2.
move: (AnnTyping_weakening T1 [(x2,Tm A2)] nil G eq_refl) => t3. simpl_env in t3.
eapply AnnTyping_tm_subst with (A:= A1).
eapply AnnTyping_weakening with (F:=[(x1,Tm A1)]); eauto 4.
econstructor; eauto.
econstructor; eauto.
econstructor; eauto.
eapply AnnTyping_weakening with (F:=nil) (E:=[(x2,Tm A2)]); eauto.
simpl_env. eauto.
eapply AnnDefEq_weakening with (F:=nil) (E:=[(x2,Tm A2)]); simpl_env; eauto.
simpl_env.
eapply (fourth ann_weaken_available_mutual) with (D := dom G).
eapply AnnDefEq_weaken_available. eauto. simpl. fsetdec.
+ eapply (@An_Pi_exists2 x1); eauto.
Qed.

Lemma An_PiCong_exists3: forall x (G:context) D rho
                           (g1 g2 : co) (A1 B1 A2 B3 B2 : tm),
    x `notin` (dom G \u fv_tm_tm_co g2 \u fv_tm_tm_co g1)
    -> AnnDefEq G D g1 A1 A2
    → AnnDefEq ([(x, Tm A1)] ++ G) D (open_co_wrt_tm g2 (a_Var_f x)) B1 B2
    → B3 = tm_subst_tm_tm (a_Conv (a_Var_f x) (g_Sym g1)) x B2
    → get_tpg G A1 = a_Star
    → get_tpg ([(x,Tm A1)] ++ G) B1 = a_Star
    → get_tpg ([(x,Tm A1)] ++ G) B2 = a_Star
    → get_tpg G A2 = a_Star
    → get_tpg ([(x,Tm A2)] ++ G) B3 = a_Star
    → AnnDefEq G D (g_PiCong rho g1 g2) (a_Pi rho A1 (close_tm_wrt_tm x B1)) (a_Pi rho A2 (close_tm_wrt_tm x B3)).
Proof.
intros.
destruct (AnnDefEq_regularity H0) as (C1 & C2 & g' & T1 & T2 & _).
destruct (AnnDefEq_regularity H1) as (C3 & C4 & g'' & T3 & T4 & _).
move: (get_tpg_correct T3 H4) => EQ. subst.
move: (get_tpg_correct T4 H5) => EQ. subst.
move: (get_tpg_correct T1 H3) => EQ. subst.
move: (get_tpg_correct T2 H6) => EQ. subst.
eapply (@An_PiCong_exists x x) with (B2 := close_tm_wrt_tm x B2); eauto.
+ autorewrite with lngen. fsetdec.
+ autorewrite with lngen. fsetdec.
+ autorewrite with lngen. eauto.
+ autorewrite with lngen. rewrite (@tm_subst_tm_tm_intro x).
  autorewrite with lngen. auto. autorewrite with lngen. auto.
+ eapply (@An_Pi_exists2 x); eauto.
  autorewrite with lngen. auto.
  autorewrite with lngen. auto.
+ pick fresh y.
  rewrite (tm_subst_tm_tm_spec _ _ x); auto.
  rewrite (tm_subst_tm_tm_intro y); auto.
  eapply (@An_Pi_exists2 x); eauto.
  autorewrite with lngen. auto.
  autorewrite with lngen. auto.
  replace a_Star with
     (tm_subst_tm_tm (a_Conv (a_Var_f x) (g_Sym g1)) y a_Star); auto.

  replace B2 with (open_tm_wrt_tm (close_tm_wrt_tm x B2) (a_Var_f x)) in T4; autorewrite with lngen; auto.
  replace a_Star with (open_tm_wrt_tm a_Star (a_Var_f x)) in T4; auto.
  apply (@AnnTyping_tm_swap x y) in T4; autorewrite with lngen; eauto.
  replace (open_tm_wrt_tm a_Star (a_Var_f y)) with a_Star in T4; auto.

  have t1: AnnCtx G by eauto with ctx_wff.
  move: (AnnTyping_weakening T2 [(x,Tm A1)] nil G eq_refl) => t2. simpl_env in t2.
  move: (AnnTyping_weakening T1 [(x,Tm A2)] nil G eq_refl) => t3. simpl_env in t3.
  move: (AnnTyping_weakening T1 [(x,Tm A1)] nil G eq_refl) => t4. simpl_env in t4.
  move: (AnnTyping_weakening T2 [(x,Tm A2)] nil G eq_refl) => t5. simpl_env in t5.

  eapply AnnTyping_tm_subst with (A:= A1).
  eapply AnnTyping_weakening with (F:=[(y,Tm A1)]); eauto 4.
  econstructor; eauto.
  econstructor; eauto.
  eapply AnnDefEq_weakening with (F:=nil) (E:=[(x,Tm A2)]); simpl_env; eauto.
  simpl_env.
  eapply (fourth ann_weaken_available_mutual) with (D := dom G).
  eapply AnnDefEq_weaken_available. eauto. simpl. fsetdec.

  autorewrite with lngen. fsetdec.

+ eapply (@An_Pi_exists2 x); eauto.
   autorewrite with lngen. auto.
  autorewrite with lngen. auto.
Qed.

Lemma An_AbsCong_exists3: forall x (G:context) D rho
                           (g1 g2 : co) (A1 B1 A2 B3 B2 B: tm),
    x `notin` (dom G \u fv_tm_tm_co g2 \u fv_tm_tm_co g1)
    -> AnnDefEq G D g1 A1 A2
    → AnnDefEq ([(x, Tm A1)] ++ G) D (open_co_wrt_tm g2 (a_Var_f x)) B1 B2
    → B3 = tm_subst_tm_tm (a_Conv (a_Var_f x) (g_Sym g1)) x B2
    → get_tpg G A1 = a_Star
    → get_tpg ([(x,Tm A1)] ++ G) B2 = B (* FIXME: isn't this assumption useless? (B seems to only occur here) *)
    → get_tpg G A2 = a_Star
    → RhoCheck rho x (erase_tm B1)
    → RhoCheck rho x (erase_tm B3)
    → AnnDefEq G D (g_AbsCong rho g1 g2)
               (a_Abs rho A1 (close_tm_wrt_tm x B1))
               (a_Abs rho A2 (close_tm_wrt_tm x B3)).
Proof.
intros.
destruct (AnnDefEq_regularity H0) as (C1 & C2 & g' & T1 & T2 & _).
destruct (AnnDefEq_regularity H1) as (C3 & C4 & g'' & T3 & T4 & _).
move: (get_tpg_correct T4 H4) => EQ. subst.
move: (get_tpg_correct T1 H3) => EQ. subst.
move: (get_tpg_correct T2 H5) => EQ. subst.
eapply (@An_AbsCong_exists x x) with (b2 := close_tm_wrt_tm x B2)
(b1 := close_tm_wrt_tm x B1)
(b3 := close_tm_wrt_tm x (tm_subst_tm_tm (a_Conv (a_Var_f x) (g_Sym g1)) x B2))
(B := a_Pi rho A1 (close_tm_wrt_tm x (get_tpg ([(x, Tm A1)] ++ G) B2)));
  eauto.
+ autorewrite with lngen. fsetdec.
+ autorewrite with lngen. fsetdec.
+ autorewrite with lngen. eauto.
+ autorewrite with lngen. rewrite (@tm_subst_tm_tm_intro x).
  autorewrite with lngen. auto. autorewrite with lngen. auto.
+ autorewrite with lngen. auto.
+ autorewrite with lngen. auto.
+ eapply (@An_Abs_exists x); eauto.
  autorewrite with lngen. auto.
  autorewrite with lngen. auto.
  autorewrite with lngen.
  rewrite <- subst_tm_erase_tm in H7.
  simpl in H7.
  rewrite tm_subst_tm_tm_spec in H7.
  autorewrite with lngen in H7. auto.
Qed.


Lemma An_CPiCong_exists_3 :  ∀ c (G : context) D (g1 g3 : co) (phi1 : constraint)
       (B1 : tm) (phi2 : constraint) (B3 B2 : tm),
     c `notin` dom G \u D \u fv_co_co_co g3 \u fv_co_co_co g1
    -> AnnIso G D g1 phi1 phi2
    → AnnDefEq ([(c, Co phi1)] ++ G) D (open_co_wrt_co g3 (g_Var_f c)) B1 B2
    → B3 = co_subst_co_tm (g_Cast (g_Var_f c) (g_Sym g1)) c B2
    -> get_tpg ([(c,Co phi1)] ++ G) B1 = a_Star
    -> get_tpg ([(c,Co phi2)] ++ G) B3 = a_Star
    -> get_tpg ([(c,Co phi1)] ++ G) B2 = a_Star
    → AnnDefEq G D (g_CPiCong g1 g3) (a_CPi phi1 (close_tm_wrt_co c B1))
               (a_CPi phi2 (close_tm_wrt_co c B3)).
Proof.
intros.
destruct (AnnIso_regularity H0).
destruct (AnnDefEq_regularity H1) as (C3 & C4 & g'' & T3 & T4 & _).
move: (get_tpg_correct T3 H3) => EQ. subst.
move: (get_tpg_correct T4 H5) => EQ. subst.
eapply (@An_CPiCong_exists c c) with
(B2 := close_tm_wrt_co c B2); eauto.
+ autorewrite with lngen. fsetdec.
+ autorewrite with lngen. fsetdec.
+ autorewrite with lngen. eauto.
+ autorewrite with lngen. rewrite (@co_subst_co_tm_intro c).
  autorewrite with lngen. auto. autorewrite with lngen. auto.
+ eapply (@An_CPi_exists c); eauto.
  autorewrite with lngen. auto.
  autorewrite with lngen. auto.
+ pick fresh y.
  rewrite (co_subst_co_tm_spec _ _ c); auto.
  rewrite (co_subst_co_tm_intro y); auto.
  eapply (@An_CPi_exists c); eauto.
  autorewrite with lngen. auto.
  autorewrite with lngen.
  replace a_Star with
     (co_subst_co_tm (g_Cast (g_Var_f c) (g_Sym g1)) y a_Star); auto.
  replace B2 with
    (open_tm_wrt_co (close_tm_wrt_co c B2) (g_Var_f c)) in T4; autorewrite with lngen; auto.
  replace a_Star with (open_tm_wrt_co a_Star (g_Var_f c)) in T4; auto.
  apply (@AnnTyping_co_swap c y) in T4; autorewrite with lngen; eauto.
  replace (open_tm_wrt_co a_Star (g_Var_f y)) with a_Star in T4; auto.
  have t1: AnnCtx G by eauto with ctx_wff.
  move: (AnnPropWff_weakening H6 [(c,Co phi1)] nil G eq_refl) => t2. simpl_env in t2.
  move: (AnnPropWff_weakening H7 [(c,Co phi2)] nil G eq_refl) => t3. simpl_env in t3.
  move: (AnnPropWff_weakening H6 [(c,Co phi1)] nil G eq_refl) => t4. simpl_env in t4.
  move: (AnnPropWff_weakening H7 [(c,Co phi2)] nil G eq_refl) => t5. simpl_env in t5.
  destruct phi1 as [a b A].
  inversion H6. subst.
  eapply AnnTyping_co_subst with (A1 := a) (A2:=b) (A3:=A)
              (D := dom ([(c,Co phi2)] ++ G)).
  { eapply AnnTyping_weakening with (F:=[(y,Co (Eq a b A))]); eauto.
    econstructor; eauto.
    econstructor; eauto.
    eapply AnnTyping_weakening with (F:=nil)(E:=[(c,Co phi2)]); eauto with ctx_wff.
    eapply AnnTyping_weakening with (F:=nil)(E:=[(c,Co phi2)]); eauto with ctx_wff.
  }
  {
    destruct phi2.
    eapply An_Cast.
    eapply An_Assn.
    econstructor.  eauto.
    eauto. eauto.
    eauto.
    rewrite dom_app. simpl. auto.
    econstructor.
    eapply AnnIso_weakening with (F:=nil) (E:=[(c,Co (Eq a0 b0 A0))]) (G:=G);
      simpl_env; eauto.
  simpl_env.
  eapply (third ann_weaken_available_mutual) with (D := dom G).
  eapply AnnIso_weaken_available. eauto. simpl. fsetdec.
  }
  autorewrite with lngen. fsetdec.
+ eapply (@An_CPi_exists c); eauto.
   autorewrite with lngen. auto.
  autorewrite with lngen. auto.
Qed.

Lemma An_CAbsCong_exists3 :
        ∀ (c : atom) (G : context) (D : available_props)
           (g1 g3 g4 : co) (phi1 : constraint) (a1 : tm)
           (phi2 : constraint) (a3 a2 B1 B3 : tm),
    AnnIso G D g1 phi1 phi2
    → c `notin` dom G \u D \u (fv_co_co_co g3) \u (fv_co_co_co g1)
        \u fv_co_co_co g4
    → AnnDefEq ([(c, Co phi1)] ++ G) D (open_co_wrt_co g3 (g_Var_f c)) a1 a2
    → a3 = co_subst_co_tm (g_Cast (g_Var_f c) (g_Sym g1)) c a2
    → get_tpg ([(c, Co phi1)] ++ G) a1 = B1
    -> get_tpg ([(c, Co phi2)] ++ G) a3 = B3
    → AnnDefEq G (dom G) g4 (a_CPi phi1 (close_tm_wrt_co c B1))
               (a_CPi phi2 (close_tm_wrt_co c B3))
    → AnnDefEq G D (g_CAbsCong g1 g3 g4)
               (a_CAbs phi1 (close_tm_wrt_co c a1))
               (a_CAbs phi2 (close_tm_wrt_co c a3))
                             .
Proof.
intros.
destruct (AnnIso_regularity H) as (T1 & T2).
destruct (AnnDefEq_regularity H1) as (C3 & C4 & g'' & T3 & T4 & _).
move: (get_tpg_correct T3 H3) => EQ2. subst C3.
assert (AnnTyping ([(c,Co phi2)] ++ G)
                  (co_subst_co_tm (g_Cast (g_Var_f c) (g_Sym g1)) c a2)
                  (co_subst_co_tm (g_Cast (g_Var_f c) (g_Sym g1)) c C4)).
{
  pick fresh y.
  replace C4 with
  (open_tm_wrt_co (close_tm_wrt_co c C4) (g_Var_f c)) in T4;
    autorewrite with lngen; auto.
  replace a2 with
  (open_tm_wrt_co (close_tm_wrt_co c a2) (g_Var_f c)) in T4;
    autorewrite with lngen; auto.
  apply (@AnnTyping_co_swap c y) in T4; autorewrite with lngen; eauto.

  (*
  rewrite (co_subst_co_tm_spec _ _ c); auto.
  rewrite (co_subst_co_tm_intro y); auto. *)


  (* move: (ann_ctx_wff_PropWff T1) => t1. *)
  move: (AnnPropWff_weakening T1 [(c,Co phi1)] nil G eq_refl) => t2. simpl_env in t2.
  move: (AnnPropWff_weakening T2 [(c,Co phi2)] nil G eq_refl) => t3. simpl_env in t3.
  move: (AnnPropWff_weakening T1 [(c,Co phi1)] nil G eq_refl) => t4. simpl_env in t4.
  move: (AnnPropWff_weakening T2 [(c,Co phi2)] nil G eq_refl) => t5. simpl_env in t5.
  destruct phi1 as [a b A].
  inversion T1. subst.

  rewrite (co_subst_co_tm_spec a2 _ c); auto.
  rewrite (co_subst_co_tm_intro y); auto.

  rewrite (co_subst_co_tm_spec C4 _ c); auto.
  rewrite (co_subst_co_tm_intro y (close_tm_wrt_co c C4) ); auto.

  eapply AnnTyping_co_subst with (A1 := a) (A2:=b) (A3:=A)
              (D := dom ([(c,Co phi2)] ++ G)).
  { eapply AnnTyping_weakening with (F:=[(y,Co (Eq a b A))]); eauto 3 with ctx_wff.
    econstructor; eauto with ctx_wff.
    econstructor; eauto.
    eapply AnnTyping_weakening with (F:=nil)(E:=[(c,Co phi2)]); eauto with ctx_wff.
    eapply AnnTyping_weakening with (F:=nil)(E:=[(c,Co phi2)]); eauto with ctx_wff.
  }
  {
    destruct phi2.
    eapply An_Cast.
    eapply An_Assn.
    econstructor.  eauto with ctx_wff.
    eauto. eauto.
    eauto.
    rewrite dom_app. simpl. auto.
    econstructor.
    eapply AnnIso_weakening with (F:=nil) (E:=[(c,Co (Eq a0 b0 A0))]) (G:=G);
      simpl_env; eauto with ctx_wff.
  simpl_env.
  eapply (third ann_weaken_available_mutual) with (D := dom G).
  eapply AnnIso_weaken_available. eauto. simpl. clear Fr. fsetdec.
  }
  autorewrite with lngen. fsetdec.
  autorewrite with lngen. fsetdec.
}
rewrite H2 in H4.
move: (get_tpg_correct H6 H4) => EQ3.
eapply (@An_CAbsCong_exists c c) with
(a2 := close_tm_wrt_co c a2)
  (B := a_CPi phi1 (close_tm_wrt_co c C4)); eauto.
+ autorewrite with lngen. fsetdec.
+ autorewrite with lngen. fsetdec.
+ autorewrite with lngen. eauto.
+ autorewrite with lngen. rewrite (@co_subst_co_tm_intro c).
  autorewrite with lngen. auto. autorewrite with lngen. auto.
+ eapply (@An_CAbs_exists c); eauto.
  autorewrite with lngen. auto.
  autorewrite with lngen. auto.
+ rewrite <- EQ3.
  rewrite H2.
  eapply (@An_CAbs_exists c); eauto.
  autorewrite with lngen. auto.
  autorewrite with lngen. auto.
+ eapply (@An_CAbs_exists c); eauto.
  autorewrite with lngen. auto.
  autorewrite with lngen. auto.
Qed.

End fc_get.
