(** * Post Correspondence Problem *)

Require Export Reductions Problems.PCP.

Lemma stack_discrete :
  discrete (stack bool).
Proof.
  eapply discrete_iff; econstructor. intros ? ?. hnf. repeat decide equality.
Qed.

Lemma stack_enum :
  enumerable__T (stack bool).
Proof.
  apply enumerable__T_list, enumerable__T_prod;
  apply enumerable__T_list, count_bool.
Qed.

(** ** Enumerability *)

Fixpoint L_PCP n : list (BSRS * (string bool * string bool)) :=
  match n with
  | 0 => []
  | S n => L_PCP n
              ++ [ (C, (x, y)) | (C, x, y) ∈ (L_T BSRS n × L_T (string bool) n × L_T (string bool) n), (x/y) el C ]
              ++ [ (C, (x ++ u, y ++ v)) | ( (C, (u,v)), x, y) ∈ (L_PCP n × L_T (string bool) n × L_T (string bool) n), (x,y) el C ]
  end.

Lemma enum_PCP' :
  enum (fun '(C, (u, v)) => @derivable bool C u v) L_PCP.
Proof.
  split.
  - eauto.
  - intros ( C & u & v ). split.
    + induction 1.
      * destruct (el_T C) as [m1], (el_T x) as [m2], (el_T y) as [m3].
        exists (1 + m1 + m2 + m3). cbn. in_app 2.
        in_collect (C, x, y); eapply cum_ge'; eauto; omega.
      * destruct IHderivable as [m1], (el_T x) as [m2], (el_T y) as [m3]. 
        exists (1 + m1 + m2 + m3). cbn. in_app 3.
        in_collect ( (C, (u, v), x, y)); eapply cum_ge'; eauto; try omega.
    + intros [m]. revert C u v H. induction m; intros.
      * inv H.
      * cbn in H. inv_collect; inv H; eauto using derivable.
Qed.

Lemma enumerable_derivable : enumerable (fun '(C, (u, v)) => @derivable bool C u v).
Proof.
  eapply enum_count. intros; repeat decide equality. eapply enum_PCP'.
Qed.

Lemma enumerable_PCP : enumerable BPCP'.
Proof.
  pose proof enumerable_derivable. 
  assert (enumerable (X := (stack bool * (string bool * string bool))) (fun '(C, (s, t)) => s = t)). {
    eapply dec_count_enum.
    - eapply decidable_iff. econstructor. intros (? & ? & ?). exact _.
    - eapply enum_enumT. econstructor. exact _.
  }
  unshelve epose proof (enumerable_conj _ H H0).
  - eapply discrete_iff. econstructor. exact _.
  - eapply projection in H1 as [f]. exists f.
    intros. rewrite <- H1. intuition.
    + destruct H2 as [u]. exists (u,u). eauto.
    + destruct H2 as [[u v] [? ->]]. exists v. eauto.
Qed.
