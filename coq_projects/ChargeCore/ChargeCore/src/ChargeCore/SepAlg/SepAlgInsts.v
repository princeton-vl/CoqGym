Require Import ChargeCore.SepAlg.UUSepAlg.
Require Import ChargeCore.SepAlg.SepAlg.

Require Import Relation_Definitions CRelationClasses Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section RelProducts.
  Context {A B : Type} {relA : relation A} {relB : relation B}.
  Context {HA: Equivalence relA}.
  Context {HB: Equivalence relB}.

  Definition rel_prod : relation (A * B) :=
    fun p1 p2 => (relA (fst p1) (fst p2) /\ relB (snd p1) (snd p2)).

  Global Instance prod_proper : Proper (relA ==> relB ==> rel_prod) (@pair A B).
  Proof.
    intros a a' Ha b b' Hb; split; assumption.
  Qed.

  Global Instance equiv_prod : Equivalence rel_prod.
  Proof.
    split.
      intros [a b]; split; reflexivity.
      intros [a1 b1] [a2 b2] [Ha Hb]; split; symmetry; assumption.
    intros [a1 b1] [a2 b2] [a3 b3] [Ha12 Hb12] [Ha23 Hb23];
      split; etransitivity; eassumption.
  Qed.

End RelProducts.

Section SAProd.
  Context A B `{HA: SepAlg A} `{HB: SepAlg B}.

  Instance SepAlgOps_prod: SepAlgOps (A * B) :=
  { sa_unit ab := sa_unit (fst ab) /\ sa_unit (snd ab)
  ; sa_mul a b c :=
      sa_mul (fst a) (fst b) (fst c) /\
      sa_mul (snd a) (snd b) (snd c)
  }.

  Definition SepAlg_prod: SepAlg (rel := rel_prod (relA := rel) (relB := rel0)) (A * B).
  Proof.
    esplit.
    - eapply equiv_prod.
    - intros * [Hab Hab']. split; apply sa_mulC; assumption.
    - intros * [Habc Habc'] [Hbc Hbc'].
      destruct (sa_mulA Habc Hbc) as [exA []].
      destruct (sa_mulA Habc' Hbc') as [exB []].
      exists (exA, exB). split; split; assumption.
    - intros [a b].
      destruct (sa_unit_ex a) as [ea [Hea Hmulea]].
      destruct (sa_unit_ex b) as [eb [Heb Hmuleb]].
      exists (ea,eb). split; split; assumption.
    - intros * [Hunita Hunitb] [Hmula Hmulb].
      split; eapply sa_unit_eq; eassumption.
    - intros ab ab' [Hab Hab']. simpl. rewrite Hab, Hab'. reflexivity.
    - intros [a1 a2] [b1 b2] [c1 c2] [d1 d2] Heq [H1 H2].
      unfold Equivalence.equiv in Heq; destruct Heq; simpl in *.
      rewrite <- H, <- H0; intuition.
  Qed.

  Lemma subheap_prod (a a' : A) (b b' : B)
  : subheap (a, b) (a', b') <-> subheap a a' /\ subheap b b'.
  Proof.
    split; [intros [c [H1 H2]]| intros [[c H1] [d H2]]]; simpl in *.
    + destruct c as [c d]; simpl in *; split.
      * exists c. apply H1.
      * exists d. apply H2.
    + exists (c, d); simpl; split.
      * apply H1.
      * apply H2.
  Qed.

  Lemma sa_mul_split (a b c : A) (a' b' c' : B)
  : sa_mul (a, a') (b, b') (c, c') <-> sa_mul a b c /\ sa_mul a' b' c'.
  Proof.
    split; intros; simpl in *; auto.
  Qed.

End SAProd.

Section UUSAProd.
  Context A B `{HA : UUSepAlg A} `{HB: UUSepAlg B}.

  Local Existing Instance SepAlgOps_prod.
  Local Existing Instance SepAlg_prod.

  Instance UUSepAlg_prod : UUSepAlg (rel := rel_prod (relA := rel) (relB := rel0)) (A * B).
  Proof.
    split.
    + apply _.
    + intros. destruct H as [H1 H2]. destruct u; simpl in *.
      split; apply uusa_unit; assumption.
  Qed.

End UUSAProd.

Section SASum.
  Context A B `{HA: SepAlg A} `{HB: SepAlg B}.

  Global Instance SepAlgOps_sum: SepAlgOps (A + B) := {|
    sa_unit ab :=
      match ab with
      | inl a => sa_unit a
      | inr b => sa_unit b
      end;
    sa_mul a b c :=
      match a , b , c with
      | inl a , inl b , inl c => sa_mul a b c
      | inr a , inr b , inr c => sa_mul a b c
      | _ , _ , _ => False
      end
   |}.

  Variant sum_eq : A + B -> A + B -> Prop :=
  | sum_eq_L {a a'} (_ : rel a a')
    : sum_eq (inl a) (inl a')
  | sum_eq_R {b b'} (_ : rel0 b b')
    : sum_eq (inr b) (inr b').

  Global Instance SepAlg_sum: @SepAlg _ sum_eq _.
  Proof.
    econstructor.
    { constructor.
      { compute. destruct x; constructor; reflexivity. }
      { compute. inversion 1; constructor; subst; symmetry; eauto. }
      { compute. inversion 1; subst; inversion 1; subst; constructor; subst; etransitivity; eauto. } }
    { destruct a; simpl; try destruct b; try destruct c; simpl; eauto.
      eapply sa_mulC.
      destruct b0; auto.
      eapply sa_mulC. }
    { intros [] [] [] [] [];  simpl;
          try solve [ eauto | intros ; contradiction ].
      { intros H H'. destruct (@sa_mulA _ _ _ _ _ _ _ _ _ H H').
        exists (inl x); eauto. }
      { intros H H'. destruct (@sa_mulA _ _ _ _ _ _ _ _ _ H H').
        exists (inr x); eauto. } }
    { intros [].
      { destruct (sa_unit_ex a). 
        exists (inl x). auto. }
      { destruct (sa_unit_ex b). 
        exists (inr x). auto. } }
    { intros [] [] []; simpl; intros; try contradiction; constructor.
      eapply sa_unit_eq; eauto.
      eapply sa_unit_eq; eauto. }
    { constructor.
      { inversion H; subst; simpl; eauto using sa_unit_proper.
        eapply sa_unit_proper; symmetry; eauto.
        eapply sa_unit_proper; symmetry; eauto. }
      { inversion H; subst; simpl; eauto using sa_unit_proper.
        eapply sa_unit_proper; eauto.
        eapply sa_unit_proper; eauto. } }
    { inversion 1; subst; simpl; eauto.
      { destruct c; destruct d; eauto.
        eapply sa_mul_mon; eauto. }
      { destruct c; destruct d; eauto.
        eapply sa_mul_mon; eauto. } }
  Qed.
End SASum.
