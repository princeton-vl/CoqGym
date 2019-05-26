Require Import Undecidability.PCP.Definitions.

(** * PCP to CFI *)

Section PCP_CFI.

  Variable P : SRS.

  Definition Sigma := sym P.
  Notation "#" := (fresh Sigma).
  
  Definition gamma1 (A : SRS) :=
    map (fun '(x,y) => x / (x ++ [#] ++ y ++ [#])) A.
  Definition gamma2 (A : SRS) :=
    map (fun '(x,y) => y / (x ++ [#] ++ y ++ [#])) A.
  Fixpoint gamma (A : SRS) :=
    match A with
    | [] => []
    | x/y :: A => gamma A ++ x ++ [#] ++ y ++ [#]
    end.

  Lemma sigma_gamma1 A :
    sigma # (gamma1 A) = tau1 A ++ [#] ++ gamma A.
  Proof.
    induction A as [ | (x,y) ] ; cbn.
    - reflexivity.
    - unfold gamma1 in IHA. cbn in *.
      rewrite IHA. now simpl_list.
  Qed.
  
  Lemma sigma_gamma2 A :
    sigma # (gamma2 A) = tau2 A ++ [#] ++ gamma A.
  Proof.
    induction A as [ | (x,y) ] ; cbn.
    - reflexivity.
    - unfold gamma2 in IHA. cbn in *.
      rewrite IHA. now simpl_list.
  Qed.

  Lemma gamma1_spec B C :
    B <<= gamma1 C ->
    exists A, A <<= C /\ gamma1 A = B.
  Proof.
    induction B as [ | (x,y)]; cbn; intros.
    - eauto.
    - assert (x/y el gamma1 C) by firstorder. unfold gamma1 in H0.
      eapply in_map_iff in H0 as ((x',y') & ? & ?). inv H0.
      assert (B <<= gamma1 C) as (A & Hi & He) % IHB by firstorder.
      exists (x/y' :: A). split.
      + intuition.
      + now subst.
  Qed.

  
  Lemma gamma2_spec B C :
    B <<= gamma2 C ->
    exists A, A <<= C /\ gamma2 A = B.
  Proof.
    induction B as [ | (x,y)]; cbn; intros.
    - eauto.
    - assert (x/y el gamma2 C) by firstorder. unfold gamma2 in H0.
      eapply in_map_iff in H0 as ((x',y') & ? & ?). inv H0.
      assert (B <<= gamma2 C) as (A & Hi & He) % IHB by firstorder.
      exists (x'/x :: A). split.
      + intuition.
      + now subst.
  Qed.

  Lemma gamma_inj A1 A2 :
    ~ # el sym A1 -> ~ # el sym A2 ->
    gamma A1 = gamma A2 -> A1 = A2.
  Proof.
    intros H.
    revert A2. induction A1 as [ | (x,y) ]; cbn; intros.
    - destruct A2; inv H1. reflexivity.
      destruct c, (gamma A2), s; cbn in *; inv H3.
    - destruct A2 as [ | (x',y')]; cbn in H1.
      + destruct (gamma A1), x; inv H1.
      + eapply rev_eq in H1. repeat (autorewrite with list in H1; cbn in H1). inv H1.
        eapply list_prefix_inv in H3 as [].
        rewrite rev_eq in H1. subst. assert (x = x').
        * destruct A1 as [ | (x1, y1)], A2 as [ | (x2, y2)]; repeat (cbn in *; autorewrite with list in H2).
          -- rewrite rev_eq in H2. congruence.
          -- exfalso. enough (~ # el rev x). eapply H1. rewrite H2.
             cbn. simpl_list. cbn. eauto. intros ? % In_rev; eauto.
          -- exfalso. enough (~ # el rev x'). eapply H1. rewrite <- H2.
             cbn. simpl_list. cbn. eauto. intros ? % In_rev; eauto.
          -- eapply list_prefix_inv in H2 as []. rewrite rev_eq in H1. congruence.
             intros ? % In_rev; eauto. intros ? % In_rev; eauto.
        * subst. f_equal. eapply app_inv_head in H2. rewrite rev_eq in H2.
          eapply IHA1 in H2; eauto.
          intros ?. eapply H. cbn. eauto.
          intros ?. eapply H0. cbn. eauto.
        * intros ? % In_rev. eapply H. cbn. eauto.
        * intros ? % In_rev. eapply H0. cbn. eauto.
  Qed.  

End PCP_CFI.


Lemma reduction :
  PCP ⪯ CFI. 
Proof.
  exists (fun P => (gamma1 P P, gamma2 P P, fresh (sym P))). intros P.
  split.
  - intros (A & Hi & He & H). exists (gamma1 P A), (gamma2 P A). repeat split.
    + clear He H. induction A as [ | [] ]. firstorder. intros ? [ <- | ].
      unfold gamma1. eapply in_map_iff. exists (s,s0). firstorder. firstorder.
    + clear He H. induction A as [ | [] ]. firstorder. intros ? [ <- | ].
      unfold gamma2. eapply in_map_iff. exists (s,s0). firstorder. firstorder.
    + destruct A; cbn in *; congruence.
    + destruct A; cbn in *; congruence.
    + now rewrite sigma_gamma1, sigma_gamma2, H.
  - intros (B1 & B2 & (A1 & Hi1 & <-) % gamma1_spec & (A2 & Hi2 & <-) % gamma2_spec & He1 & He2 & H).
    rewrite sigma_gamma1, sigma_gamma2 in H.
    eapply list_prefix_inv in H as [H1 <- % gamma_inj].
    + exists A1. firstorder. destruct A1; cbn in *; firstorder congruence.
    + intros ?. eapply sym_mono in Hi1. eapply Hi1 in H0 as ? % fresh_spec. now apply H2.
    + intros ?. eapply sym_mono in Hi2. eapply Hi2 in H0 as ? % fresh_spec. now apply H2.        
    + intros ? % tau1_sym. eapply sym_mono in Hi1. eapply Hi1 in H1 as ? % fresh_spec. now apply H0.
    + intros ? % tau2_sym. eapply sym_mono in Hi2. eapply Hi2 in H1 as ? % fresh_spec. now apply H0.
Qed.
