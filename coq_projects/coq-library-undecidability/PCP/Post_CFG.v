Require Import PCP.Definitions Shared.Prelim.

(** * Post grammars are context-free *)

Hint Rewrite concat_app map_app map_map : list.
Hint Rewrite <- map_rev  : list.

Lemma nil_app_nil X (A : list X) :
  A = [] ++ A ++ [].
Proof.
  now autorewrite with list.
Qed.

Definition gamma (A : SRS) := map (fun '(x,y) => (x, rev y)) A.

Lemma sigma_eq  s A :
  sigma s A = tau1 A ++ [s] ++ rev (tau2 (gamma A)).
Proof.
  induction A  as [ | [u v] ].
  - reflexivity.
  - cbn. rewrite IHA. now simpl_list. 
Qed.

Lemma tau2_gamma s A :
  s el rev (tau2 (gamma A)) <-> s el tau2 A.
Proof.
  induction A as [ | [u v] ]; cbn.
  - reflexivity.
  - simpl_list. rewrite !in_app_iff, IHA. firstorder.
Qed.

Lemma sigma_inv A s1 s x y :
  sigma s1 A = x ++ [s] ++ y -> ~ s el x -> ~ s el y -> ~ s el sym A ->
  s1 = s.
Proof.
  rewrite sigma_eq. intros.
  cbn in H. assert (s el  tau1 A ++ s1 :: rev (tau2 (gamma A))) by (rewrite H; eauto).
  eapply in_app_iff in H3 as [ | [ | ? % tau2_gamma]]; try firstorder using tau1_sym, tau2_sym.
Qed.

Lemma sigma_snoc A x y u v s s' :
  sigma s A = x ++ [s] ++ y -> ~ s el x -> ~ s el y ->
  sigma s' (A ++ [u/v]) = x ++ u ++ s' ++ v ++ y.
Proof.
  rewrite !sigma_eq. unfold gamma. cbn. simpl_list. cbn. simpl_list. cbn.
  intros. eapply list_prefix_inv in H as [-> <-]; eauto.
  eapply notInZero.
  eapply (f_equal (fun a => count a s)) in H. rewrite <- !countSplit in H. cbn in H.
  rewrite !Nat.eqb_refl in H. eapply notInZero in H0. eapply notInZero in H1.
  rewrite H0, H1 in *. omega.
Qed.

Section CFGs.

  Notation sig := nat.
  Definition rule : Type := sig * list sig.
  Definition cfg : Type := sig * list rule.

  Definition rules (G : cfg) := snd G.
  Definition startsym (G : cfg) := fst G.

  Inductive rew_cfg : cfg -> list sig -> list sig -> Prop:=
  |rewR R x a y v : (a,v) el rules R -> rew_cfg R (x++[a]++y) (x++v++y).
  Hint Constructors rew_cfg.

  Lemma rewrite_sing R a x :
    (a, x) el rules R -> rew_cfg R [a] x.
  Proof.
    intros. rewrite nil_app_nil, (nil_app_nil [a]). now econstructor.
  Qed.
  
  Inductive rewt (S: cfg) (x: list sig) : list sig -> Prop :=
  |rewtRefl : rewt S x x
  |rewtRule y z : rewt S x y -> rew_cfg S y z -> rewt S x z.
  Hint Constructors rewt.

  Global Instance rewtTrans R :
    PreOrder (rewt R).
  Proof.
    split.
    - hnf. econstructor.
    - induction 2; eauto.
  Qed.

  Global Instance rewrite_proper R :
    Proper (rewt R ==> rewt R ==> rewt R) (@app sig).
  Proof.
    intros x1 y1 H1 x2 y2 H2.
    induction H1.
    - induction H2.
      + reflexivity.
      + rewrite IHrewt. inv H. eapply rewtRule.
        replace (x1 ++ x ++ [a] ++ y0) with ( (x1 ++ x) ++ [a] ++ y0) by now autorewrite with list.
        eauto. replace (x1 ++ x ++ v ++ y0) with ( (x1 ++ x) ++ v ++ y0) by now autorewrite with list. eauto.
    - rewrite IHrewt. inv H. autorewrite with list. eauto.
  Qed.

  Global Instance subrel R :
    subrelation (rew_cfg R) (rewt R).
  Proof.
    intros x y H. econstructor. reflexivity. eassumption.
  Qed.
    
  Definition terminal G x := ~ exists y, rew_cfg G x y.

  Lemma terminal_iff G x :
    terminal G x <-> forall s y, s el x -> ~ (s, y) el rules G.
  Proof.
    split.
    - intros H s y A B. apply H. destruct (@in_split _ _ _ A) as (l1 & l2 & ->).
      exists (l1 ++ y ++ l2). change (s :: l2) with ([s] ++ l2). now econstructor.
    - intros H1 [y H2]. inv H2. eapply (H1 _ v); eauto.
  Qed.

  Definition L (G : cfg) x := rewt G [startsym G] x /\ terminal G x.

  Definition sym_G (G : cfg) :=
    startsym G :: flat_map (fun '(a, x) => a :: x) (rules G).
  
  Lemma sym_G_rewt x G y :
    x <<= sym_G G -> rewt G x y -> y <<= sym_G G.
  Proof.
    intros. induction H0.
    - eauto.
    - destruct H1. destruct R. cbn in *.
      eapply incl_app; eauto.  eapply incl_app; eauto.
      unfold sym_G. intros ? ?.
      right. eapply in_flat_map.  exists (a / v). eauto.
  Qed.
  
End CFGs.

Definition CFP' (G : cfg) := exists x, L G x /\ x = List.rev x.

Definition CFI' '(G1, G2) :=
  exists x, L G1 x /\ L G2 x.

Section Post_CFG.

  Variable R : SRS.
  Variable a : symbol.

  Definition Sigma := sym R ++ [a].
  Definition S : symbol := fresh Sigma.

  Definition G := (S, (S,[S]) :: map (fun '(u / v) => (S, u ++ [S] ++ v)) R ++ map (fun '(u / v) => (S, u ++ [a] ++ v)) R).

  Lemma terminal_iff_G y :
    terminal G y <-> ~ S el y.
  Proof.
    unfold terminal.
    enough ((exists y0, rew_cfg G y y0) <-> S el y). firstorder. split.
    - intros [y0 ?]. inv H. cbn in H0.
      destruct H0 as [ | [ [[] []] % in_map_iff | [[] []] % in_map_iff ] % in_app_iff]; inv H; eauto.
    - intros (u' & v' & ?) % List.in_split.
      subst. exists (u' ++ [S] ++ v'). econstructor. cbn. eauto.
  Qed.

  Lemma rewt_count x :
    rewt G [S] x -> count x S <= 1.
  Proof.
    induction 1.
    - cbn. now rewrite Nat.eqb_refl.
    - inv H0. destruct H1 as [ | [ [[] []] % in_map_iff | [[] []] % in_map_iff ] % in_app_iff]; inv H0.
      + eauto.
      + unfold Sigma. simpl_list. rewrite <- !countSplit in *. cbn in *.
        rewrite Nat.eqb_refl in *.
        enough (count l S = 0) as ->. enough (count l0 S = 0) as ->. omega.
        * eapply notInZero. intros D.
          edestruct (fresh_spec) with (l := Sigma); try reflexivity.
          eapply sym_word_R in H1. unfold Sigma. eauto. 
        * eapply notInZero. intros D.
          edestruct (fresh_spec) with (l := Sigma); try reflexivity.
          eapply sym_word_l in H1. unfold Sigma. eauto. 
      + unfold Sigma. simpl_list. rewrite <- !countSplit in *. cbn in *.
        rewrite Nat.eqb_refl in *.
        assert (S =? a = false) as ->. eapply Nat.eqb_neq. intros D.
        edestruct fresh_spec with (l := Sigma); try reflexivity.
        unfold S in *. rewrite D. unfold Sigma; eauto.
        enough (count l S = 0) as ->. enough (count l0 S = 0) as ->. omega.
        * eapply notInZero. intros D.
          edestruct (fresh_spec) with (l := Sigma); try reflexivity.
          eapply sym_word_R in H1. unfold Sigma. eauto. 
        * eapply notInZero. intros D.
          edestruct (fresh_spec) with (l := Sigma); try reflexivity.
          eapply sym_word_l in H1. unfold Sigma. eauto. 
  Qed.
  
  Lemma Post_CFG_1' A :
    A <<= R -> A = [] \/ rewt G [S] (sigma a A).
  Proof.
    induction A.
    - cbn. eauto.
    - intros.  assert (A <<= R) by eauto. eapply IHA in H0.
      destruct a0 as [u v]. destruct H0.
      + subst. right. erewrite rewrite_sing with (x := u ++ [a] ++ v). reflexivity.
        right. eapply in_app_iff. right. eapply in_map_iff. exists (u,v); eauto.
      + right. erewrite rewrite_sing with (x := u ++ [S] ++ v). 
        now rewrite H0. right. eapply in_app_iff. left. eapply in_map_iff. exists (u,v); eauto.
  Qed.

  Lemma Post_CFG_2 x :
    rewt G [S] x ->
    exists A m, A <<= R /\ sigma m A = x /\ (m = S \/ m = a /\ A <> []).
  Proof.
    intros. induction H.
    - cbn.  exists [], S. eauto.
    - inv H0. destruct H1 as [ | [(? & ? & ?) % in_map_iff | (? & ? & ?) % in_map_iff] % in_app_iff]; inv H0.
      + eassumption.
      + destruct x0 as [u' v']. inv H3.
        destruct IHrewt as (A & m & HA & IHA & Hm).
        exists (A ++ [u'/v']), S. repeat split.
        * eauto.
        * simpl_list. cbn.
          enough (~ S el x). enough (~ S el y0).
          eapply sigma_snoc with (s := S); eauto.
          -- assert (IH2 := IHA).
          eapply sigma_inv in IHA; eauto. subst. eauto.
          intros D. 
          edestruct fresh_spec with (l := sym R ++ [a]); try reflexivity.
          eapply in_app_iff. left. eapply sym_mono. eauto. eauto.
          -- eapply rewt_count in H. rewrite <- !countSplit in H. cbn in H.
             rewrite Nat.eqb_refl in H. eapply notInZero. omega.
          -- eapply rewt_count in H. rewrite <- !countSplit in H. cbn in H.
             rewrite Nat.eqb_refl in H. eapply notInZero. omega.
        * eauto.
      + destruct x0 as [u' v']. inv H3.
        destruct IHrewt as (A & m & HA & IHA & Hm).
        exists (A ++ [u'/v']), a. repeat split.
        * eauto.
        * simpl_list. cbn.
          enough (~ S el x). enough (~ S el y0).
          eapply sigma_snoc with (s := S); eauto.
          -- assert (IH2 := IHA).
          eapply sigma_inv in IHA; eauto. subst. eauto.
          intros D. 
          edestruct fresh_spec with (l := sym R ++ [a]); try reflexivity.
          eapply in_app_iff. left. eapply sym_mono. eauto. eauto.
          -- eapply rewt_count in H. rewrite <- !countSplit in H. cbn in H.
             rewrite Nat.eqb_refl in H. eapply notInZero. omega.
          -- eapply rewt_count in H. rewrite <- !countSplit in H. cbn in H.
             rewrite Nat.eqb_refl in H. eapply notInZero. omega.
        * destruct A; firstorder.
  Qed.

  Lemma reduction_full x :
    (exists A, A <<= R /\ A <> [] /\ sigma a A = x) <->  L G x.
  Proof.
    split.
    - intros (A & ? & ? & ?). subst. destruct Post_CFG_1' with (A := A); intuition.
      split.
      + eassumption.
      + eapply terminal_iff_G. rewrite sigma_eq. intros E.
        edestruct fresh_spec with (l := sym R ++ [a]); try reflexivity.        
        eapply in_app_iff in E as [ | [ | ? % tau2_gamma ] % in_app_iff].
        * eapply in_app_iff. left. eapply sym_mono; eauto. now eapply tau1_sym.
        * eapply in_app_iff. right. eauto.
        * eapply in_app_iff. left. eapply sym_mono; eauto. now eapply tau2_sym.
    - intros [(A & m & HA & HE & Hm) % Post_CFG_2 ?].
      subst. destruct Hm as [-> | [-> ?]].
      + eapply terminal_iff_G in H.  exfalso. rewrite sigma_eq in H.
        eapply H. eauto.        
      + exists A. eauto.
  Qed.
  
End Post_CFG.

Definition Post_G '(R, a, x) := exists A, A <<= R /\ A <> [] /\ sigma a A = x.
Definition CFG '(G, x) := L G x.

Lemma reduce_grammars :
  Post_G ⪯ CFG.
Proof.
  exists (fun '(R, a, x) => (G R a, x)). intros ((? & ?) & ?). cbn. eapply reduction_full.
Qed.

Lemma reduce_CFP :
  CFP ⪯ CFP'.
Proof.
  exists (fun '(R, a) => (G R a)). intros [R a].
  intuition; cbn in *.
  - destruct H as (A & HR & HA & H).
    exists (sigma a A). split. eapply reduction_full; eauto.
    eauto.
  - destruct H as (x & Hx & H).
    eapply reduction_full in Hx as (A & HR & HA & H1).
    exists A. subst; eauto.
Qed.

Lemma reduce_CFI :
  CFI ⪯ CFI'.
Proof.
  exists (fun '(R1, R2, a) => (G R1 a, G R2 a)). intros [[R1 R2] a].
  intuition; cbn in *.
  - destruct H as (A1 & A2 & HR1 & HR2 & HA1 & HA2 & H).
    exists (sigma a A1). split; eapply reduction_full; eauto.
  - destruct H as (x & HR1 & HR2).
    eapply reduction_full in HR1 as (A1 & HR1 & HA1 & H1).
    eapply reduction_full in HR2 as (A2 & HR2 & HA2 & H2).
    exists A1, A2. subst; eauto.
Qed.
