(** * Many-One Reductions *)

Require Export Problems.Reduction DecidableEnumerable.

Lemma dec_red X (p : X -> Prop) Y (q : Y -> Prop) :
  p ⪯ q -> decidable q -> decidable p.
Proof.
  intros [f] [d]. exists (fun x => d (f x)). intros x. rewrite H. eapply H0.
Qed.

Lemma red_comp X (p : X -> Prop) Y (q : Y -> Prop) :
  p ⪯ q -> (fun x => ~ p x) ⪯ (fun y => ~ q y).
Proof.
  intros [f]. exists f. intros x. now rewrite H.
Qed.

Section enum_red.

  Variables (X Y : Type) (p : X -> Prop) (q : Y -> Prop).
  Variables (f : X -> Y) (Hf : forall x, p x <-> q (f x)).

  Variables (Lq : _) (qe : enum q Lq).

  Variables (x0 : X).
  
  Variables (d : eq_dec Y).
  
  Fixpoint L (LX : enumT X) n :=
    match n with
    | 0 => []
    | S n => L LX n ++ [ x | x ∈ L_T X n , f x el Lq n ]
    end.

  Lemma enum_red LX :
    enum p (L LX).
  Proof.    
    split.
    - intros ?. cbn; eauto. 
    - split.
      + intros H.
        eapply Hf in H. eapply qe in H as [m1]. destruct (el_T x) as [m2 ?]. 
        exists (1 + m1 + m2). cbn. in_app 2.
        in_collect x; eapply cum_ge'; eauto; try omega.
        eapply qe.
      + intros [m H]. induction m.
        * inv H.
        * cbn in H. inv_collect. 
          eapply Hf. eapply qe. eauto.
  Qed.

End enum_red.

Lemma enumerable_red X Y (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ q -> enumerable__T X -> discrete Y -> enumerable q -> enumerable p.
Proof.
  intros [f] [] % enum_enumT [] % discrete_iff [L] % enumerable_enum.
  eapply enum_count, enum_red with (Y := Y); eauto.
Qed.

Theorem not_decidable X Y (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ q -> enumerable__T X -> ~ enumerable (compl p) ->
  ~ decidable q /\ ~ decidable (compl q).
Proof.
  intros. split; intros ?.
  - eapply H1. eapply dec_red in H2; eauto.
    eapply dec_compl in H2. eapply dec_count_enum; eauto.
  - eapply H1. eapply dec_red in H2; eauto.
    eapply dec_count_enum; eauto. now eapply red_comp.
Qed.

Theorem not_coenumerable X Y (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ q -> enumerable__T X -> ~ enumerable (compl p) -> discrete Y ->
  ~ enumerable (compl q).
Proof.
  intros. intros ?. eapply H1. eapply enumerable_red in H3; eauto.
  now eapply red_comp.
Qed.

