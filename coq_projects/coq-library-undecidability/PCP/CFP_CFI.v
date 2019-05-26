Require Import PCP.Definitions Post_CFG.

(** * CFP to CFI *)

Section Palindrome.

  Variable Sigma : list symbol.

  Notation StartG := (fresh Sigma).
  
  Definition palin_G : cfg :=
    (StartG, (StartG, []) ::
                          flat_map (fun g => [ (StartG, [g]);  (StartG, [g; StartG; g]) ]) Sigma).

  Lemma notInZero  (x: nat) A :
    not (x el A) <-> count A x = 0.
  Proof.
    split; induction A.
    -  reflexivity.
    - intros H. cbn in *. destruct (Nat.eqb_spec x a).
      + exfalso. apply H. left. congruence.
      + apply IHA. intros F. apply H. now right.
    - tauto.
    - cbn. destruct (Nat.eqb_spec x a).
      + subst a. omega.
      + intros H [E | E].
        * now symmetry in E.
        * tauto.
  Qed.

  Lemma G_left x : 
    rewt palin_G [StartG] x -> rev x = x /\ count x StartG <= 1.
  Proof.
    induction 1.
    - cbn. rewrite (Nat.eqb_refl StartG). intuition.
    - destruct IHrewt as [IH Eq].
      + inv H0. cbn in H1. destruct H1.
        * inv H0. rewrite <- !countSplit in *. autorewrite with list in *. cbn in *. split; try omega.
          rewrite Nat.eqb_refl in *.
          assert (count x StartG = 0) as H1 % notInZero by omega.
          assert (count y0 StartG = 0) as H2 % notInZero by omega.
          eapply list_prefix_inv in IH as [<- _]; try rewrite <- in_rev; eauto.
          now rewrite rev_involutive.
        * eapply in_flat_map in H0 as (? & ? & [ | [ | [] ]]).
          -- inv H1. rewrite <- !countSplit in *. autorewrite with list in *. cbn in *. 
             rewrite Nat.eqb_refl in *. split; try omega.
             assert (count x StartG = 0) as H1 % notInZero by omega.
             assert (count y0 StartG = 0) as H2 % notInZero by omega.
             eapply list_prefix_inv in IH as [ <- _]; try rewrite <- in_rev; eauto.
             now rewrite rev_involutive.
             destruct _; omega. 
          -- inv H1. rewrite <- !countSplit in *. autorewrite with list in *. cbn in *.
             rewrite Nat.eqb_refl in *. split; try omega.
             assert (count x StartG = 0) as H1 % notInZero by omega.
             assert (count y0 StartG = 0) as H2 % notInZero by omega.
             eapply list_prefix_inv in IH as [<- _]; try rewrite <- in_rev; eauto.
             now rewrite rev_involutive.
             destruct (Nat.eqb_spec StartG x0). subst. edestruct fresh_spec; eauto.
             omega.
  Qed.

  Lemma listI : forall (A : Type) (P : list A -> Prop), P [] -> (forall x, P [x]) -> (forall (x : A) (y : A) (l : list A), P l -> P (x :: l ++ [y])) -> forall l : list A, P l.
  Proof.
    intros. pattern l. revert l. apply size_induction with (f := @length _). intros.
    destruct x.
    - auto.
    - revert H2. pattern x. revert x. apply rev_ind. auto.
      intros. apply H1. apply H3. cbn. rewrite app_length. omega.
  Qed.

  Lemma rev_palin x : x <<= StartG :: Sigma ->
    x = rev x -> count x StartG <= 1 -> rewt palin_G [StartG] x.
  Proof.
    pattern x. revert x. apply listI; intros.
    - rewrite rewrite_sing. reflexivity. now left.
    - destruct (Nat.eqb_spec x StartG).
      subst. reflexivity. rewrite rewrite_sing. reflexivity. right. eapply in_flat_map.
      exists x. split. assert (x el StartG :: Sigma) by firstorder. destruct H2; eauto. congruence.
      now left.
    - cbn in H1. autorewrite with  list in *. inv H1.
      cbn in H2. rewrite <- countSplit in H2.
      destruct (Nat.eqb_spec StartG y); subst.
      + cbn in *. rewrite (Nat.eqb_refl) in *. omega.
      + rewrite rewrite_sing with (x := [y] ++ [StartG] ++ [y]).
        rewrite H.
        * cbn. reflexivity.
        * eauto.
        * now eapply app_inv_tail in H5.
        * cbn in *; omega.
        * right. eapply in_flat_map. cbn. firstorder.
  Qed.

  Lemma Start_fresh x :
    x <<= Sigma -> ~ StartG el x.
  Proof.
    intros ? ?. edestruct fresh_spec with (l := Sigma); eauto.
  Qed.
  
  Lemma G_char x : x <<= Sigma ->
    x = rev x <-> L palin_G x.
  Proof.
    intros Hx. split.
    - intros H. split.
      + eapply rev_palin in H; eauto.
        enough (count x StartG = 0) by omega.
        eapply notInZero. eauto using Start_fresh.
      + intros [y Hy].
        inv Hy. destruct H0. inv H0.
        eapply Start_fresh. eauto. eauto. 
        eapply in_flat_map in H0 as (? & ? & [ | [ | [] ]]).
        * inv H1. eapply Start_fresh. eauto. rewrite H. simpl_list. cbn. eauto. 
        * inv H1. eapply Start_fresh. eauto. rewrite H. simpl_list. cbn. eauto. 
    - intros [[] % G_left Ht]. eauto.
  Qed.
  
End Palindrome.

Theorem CFP_CFI :
  CFP' ⪯ CFI'.
Proof.
  exists (fun G => (palin_G (sym_G G), G)). intros G. split; intros (? & ? & ?).
  - exists x. rewrite <- G_char. intuition. destruct H. eapply sym_G_rewt; try eassumption.
    destruct G. unfold sym_G; cbn; eauto.
  - destruct H. eapply G_left in H.
    exists x. intuition.
Qed.
