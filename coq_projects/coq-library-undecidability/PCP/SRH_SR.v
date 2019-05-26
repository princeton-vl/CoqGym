Require Import Undecidability.PCP.Definitions.

(** * SRH to SR *)

Section SRH_SR.

  Variables (R : SRS) (x0 : string) (a0 : symbol).
  Notation Sigma :=  (a0 :: x0 ++ sym R).

  Definition P :=
    R ++ map (fun a => [a; a0] / [a0]) Sigma ++ map (fun a => [a0; a] / [a0]) Sigma.
  
  Lemma sym_P :
    sym P <<= Sigma.
  Proof.
    unfold P. rewrite !sym_app. eapply incl_app; [ | eapply incl_app].
    - eauto.
    - eapply sym_map. cbn. intros ? [-> | [ | ] % in_app_iff] ? [ | [ | ]]; subst; eauto.
      inv H. eauto. inv H0. inv H0. eauto. eauto. inv H0. eauto. inv H1.
    - eapply sym_map. cbn. intros ? [-> | [ | ] % in_app_iff] ? [ | [ | ]]; subst; eauto.
      inv H. eauto. inv H0. inv H0. eauto. eauto. inv H0. eauto. inv H1.
  Qed.

  Lemma rewt_a0_L x :
    x <<= Sigma -> rewt P (a0 :: x) [a0].
  Proof.
    intros. induction x.
    - reflexivity.
    - econstructor.
      replace (a0 :: a :: x) with ([] ++ [a0;a] ++ x) by now simpl_list. econstructor.
      unfold P. rewrite !in_app_iff, !in_map_iff. eauto 9. firstorder.
  Qed.

  Lemma rewt_a0_R x :
    x <<= Sigma -> rewt P (x ++ [a0]) [a0].
  Proof.
    induction x using rev_ind.
    - econstructor.
    - econstructor. replace ((x1 ++ [x]) ++ [a0]) with (x1 ++ ([x] ++ [a0]) ++ []). econstructor.
      cbn. unfold P. rewrite !in_app_iff, !in_map_iff. eauto 9. now simpl_list.
      rewrite app_nil_r. firstorder.
  Qed.

  Lemma x_rewt_a0 x :
    a0 el x -> x <<= Sigma -> rewt P x [a0].
  Proof.
    intros (y & z & ->) % in_split ?.
    transitivity (y ++ [a0]).
    eapply rewt_app_L, rewt_a0_L. eauto.
    eapply rewt_a0_R. eauto.
  Qed.
  
  Lemma SR_SRH x :
    x <<= Sigma ->
    rewt P x [a0] -> exists y, rewt R x y /\ a0 el y.
  Proof.
    intros. pattern x; refine (rewt_induct _ _ H0).
    + exists [a0]. split. reflexivity. eauto.
    + clear H H0. intros. inv H. destruct H1 as [y []].
      unfold P in H2. eapply in_app_iff in H2 as [ | [ (? & ? & ?) % in_map_iff | (? & ? & ?) % in_map_iff ] % in_app_iff].
      * exists y. eauto using rewt, rew.
      * inv H2. eauto 9 using rewt.
      * inv H2. eauto 9 using rewt.
  Qed.

  Lemma equi :
    SRH (R, x0, a0) <-> SR (P, x0, [a0]).
  Proof.
    split.
    - intros (y & H & Hi).
      unfold SR. transitivity y. eapply (rewt_subset H). unfold P. eauto.
      eapply x_rewt_a0. firstorder. eapply rewt_sym with (x := x0); eauto.
    - intros H. unfold SRH, SR in *.
      eapply SR_SRH in H; eauto.
  Qed.
          
End SRH_SR.

Theorem reduction :
  SRH ⪯ SR.
Proof.
  exists (fun '(R, x, a) => (P R x a, x, [a])). intros [[R x0] a0].
  now eapply equi.
Qed.
