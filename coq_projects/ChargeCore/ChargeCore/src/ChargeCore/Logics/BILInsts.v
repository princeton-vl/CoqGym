Require Import Setoid Morphisms RelationClasses Program.Basics.
From ChargeCore.Logics Require Import ILogic BILogic ILInsts Pure.
From ChargeCore.SepAlg Require Import SepAlg.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section BISepAlg.
  Context {A} `{sa : SepAlg A}.
  Context {B : Type} `{IL: ILogic B}.
  Context {HPre : PreOrder rel}.

  Open Scope sa_scope.

  Local Transparent ILPre_Ops.

  Global Program Instance SABIOps: BILogicOps (ILPreFrm rel B) := {
    empSP := mkILPreFrm (fun x => Exists a : (sa_unit x), ltrue) _;
    sepSP P Q :=  mkILPreFrm (fun x => Exists x1, Exists x2, Exists H : sa_mul x1 x2 x,
                                                (ILPreFrm_pred P) x1 //\\ (ILPreFrm_pred Q) x2) _;
    wandSP P Q := mkILPreFrm (fun x => Forall x1, Forall x2, Forall H : sa_mul x x1 x2,
                                                 (ILPreFrm_pred P) x1 -->> (ILPreFrm_pred Q) x2) _
  }.
  Next Obligation.
  	apply lexistsL; intro H1. eapply lexistsR. rewrite <- H. assumption. apply ltrueR.
  Qed.
  Next Obligation.
  	apply lexistsL; intro a; apply lexistsL; intro b; apply lexistsL; intro Hab.
  	apply lexistsR with a; apply lexistsR with b. eapply lexistsR. eapply sa_mul_monR; eassumption. reflexivity.
  Qed.
  Next Obligation.
	apply lforallR; intro a; apply lforallR; intro b; apply lforallR; intro Hab.
	apply lforallL with a; apply lforallL with b. apply lforallL. eapply sa_mul_mon; [symmetry|]; eassumption.
	reflexivity.
  Qed.

  Instance SABILogic : BILogic (ILPreFrm rel B).
    split.
    + apply _.
    + intros P Q x; simpl.
      apply lexistsL; intro x1; apply lexistsL; intro x2; apply lexistsL; intro H'; apply sa_mulC in H'.
      apply lexistsR with x2; apply lexistsR with x1; apply lexistsR with H'; apply landC.
    + intros P Q R x; simpl.
      apply lexistsL; intro x1; apply lexistsL; intro x2; apply lexistsL; intro Hx.
      repeat setoid_rewrite landexistsD1.
      apply lexistsL; intro x3. apply lexistsL; intro x4; apply lexistsL; intro Hx1.
      destruct (sa_mulA Hx1 Hx) as [x5 [Hx2 Hx5]].
      apply lexistsR with x3; apply lexistsR with x5; apply lexistsR with Hx5.
      rewrite landA. apply landR; [apply landL1; reflexivity| apply landL2].
      apply lexistsR with x4. apply lexistsR with x2; apply lexistsR with Hx2.
      reflexivity.
    + intros P Q R; split; intros H x; simpl.
      - apply lforallR; intro x1; apply lforallR; intro x2; apply lforallR; intro Hx1.
        apply limplAdj.
        specialize (H x2); simpl in H.
        rewrite <- H.
        apply lexistsR with x; apply lexistsR with x1; apply lexistsR with Hx1. reflexivity.
      - apply lexistsL; intro x1; apply lexistsL; intro x2; apply lexistsL; intro Hx.
        specialize (H x1); simpl in H.
        rewrite H.
		apply landAdj.
        apply lforallL with x2; apply lforallL with x; apply lforallL with Hx.
        reflexivity.
    + intros P Q R H x; simpl.
      apply lexistsL; intro x1; apply lexistsL; intro x2; apply lexistsL; intro Hx.
      repeat eapply lexistsR; [eassumption|].
      rewrite H. reflexivity.
    + intros P; split; intros x; simpl.
      - apply lexistsL; intro x1; apply lexistsL; intro x2; apply lexistsL; intro Hx.
        rewrite landC, landexistsD1. apply lexistsL; intro Horg.
        apply landL2.
        apply sa_unit_eq in Hx. rewrite <- Hx. reflexivity. assumption.
      - destruct (sa_unit_ex x) as [u [H1 H2]].
        apply lexistsR with x; apply lexistsR with u; apply lexistsR with H2.
        apply landR; [reflexivity| apply lexistsR; [assumption | apply ltrueR]].
  Qed.

  Global Instance pureop_bi_sepalg : PureOp _ := {
    pure := fun (P : ILPreFrm rel B) => forall h h', (ILPreFrm_pred P) h |-- (ILPreFrm_pred P) h'
  }.

  Global Instance pure_bi_sepalg : Pure pureop_bi_sepalg.
  Proof.
    constructor.
    { unfold pure; simpl; constructor.
      { unfold sepSP; simpl; intros.
        destruct (sa_unit_ex t).
        apply lexistsR with x.
        apply lexistsR with t.
        destruct H0.
        apply sa_mulC in H1.
        eapply lexistsR; eauto.
        rewrite H. reflexivity. }
      constructor.
      { unfold sepSP; simpl; intros.
        repeat (eapply lexistsL; intros).
        rewrite H. rewrite H0. reflexivity. }
      constructor.
      { split; intros; unfold sepSP; simpl; intros.
        { repeat (eapply lexistsL; intros).
          apply landR. do 2 apply landL1. auto.
          eapply lexistsR.
          eapply lexistsR.
          eapply lexistsR. eassumption.
          eapply landR. apply landL1. apply landL2. reflexivity.
          apply landL2. reflexivity. }
        { rewrite landC.
          rewrite landexistsDL1.
          repeat (eapply lexistsL; intros).
          rewrite landexistsDL1.
          repeat (eapply lexistsL; intros).
          rewrite landexistsDL1.
          repeat (eapply lexistsL; intros).
          do 3 eapply lexistsR.
          eassumption.
          rewrite H.
          rewrite landC. rewrite landA. reflexivity. } }
      constructor.
      { unfold wandSP; simpl; intros.
        repeat (eapply lforallR; intros).
        destruct (sa_unit_ex x).
        destruct H0.
        eapply lforallL with x1.
        apply lforallL with x.
        eapply lforallL.
        rewrite x0. auto.
        apply limplAdj. apply limplL. apply H. apply landL1. reflexivity. }
      { unfold wandSP; simpl; intros.
        repeat (eapply lforallR; intros).
        eapply lforallL. eapply lforallL. reflexivity.
        apply limplAdj. apply limplL; auto. apply landL1. auto. } }
    { red. red. unfold pure; simpl.
      intros. setoid_rewrite H.
      reflexivity. }
  Qed.

End BISepAlg.

Section BISepAlg2.
  Context {A} `{sa : SepAlg A}.
  Context {B} `{BIL: BILogic B}.
  Context {HPre : PreOrder rel}.
  Context {HIL : ILogic B}.

  Open Scope sa_scope.

  Local Transparent ILPre_Ops.

  Global Program Instance SABIOps2: BILogicOps (ILPreFrm rel B) :=
  { empSP := mkILPreFrm (fun x => Exists a : (sa_unit x), empSP) _
  ; sepSP P Q :=  mkILPreFrm (fun x => Exists x1, Exists x2, Exists H : sa_mul x1 x2 x,
                                                (ILPreFrm_pred P) x1 ** (ILPreFrm_pred Q) x2) _
  ; wandSP P Q := mkILPreFrm (fun x => Forall x1, Forall x2, Forall H : sa_mul x x1 x2,
                                                 (ILPreFrm_pred P) x1 -* (ILPreFrm_pred Q) x2) _
  }.
  Next Obligation.
  	apply lexistsL; intro H1. eapply lexistsR. rewrite <- H. assumption. reflexivity.
  Qed.
  Next Obligation.
  	apply lexistsL; intro a; apply lexistsL; intro b; apply lexistsL; intro Hab.
  	apply lexistsR with a; apply lexistsR with b. eapply lexistsR. eapply sa_mul_monR; eassumption. reflexivity.
  Qed.
  Next Obligation.
	apply lforallR; intro a; apply lforallR; intro b; apply lforallR; intro Hab.
	apply lforallL with a; apply lforallL with b. apply lforallL. eapply sa_mul_mon; [symmetry|]; eassumption.
	reflexivity.
  Qed.

  Global Instance SABILogic2 : BILogic (ILPreFrm rel B).
    split.
    + apply _.
    + intros P Q x; simpl.
      apply lexistsL; intro x1; apply lexistsL; intro x2; apply lexistsL; intro H'; apply sa_mulC in H'.
      apply lexistsR with x2; apply lexistsR with x1; apply lexistsR with H'. apply sepSPC.
    + intros P Q R x; simpl.
      apply lexistsL; intro x1; apply lexistsL; intro x2; apply lexistsL; intro Hx.
      rewrite sepSPC. do 3 setoid_rewrite <- bilexistssc.
      apply lexistsL; intro x3; apply lexistsL; intro x4; apply lexistsL; intro Hx1.
      destruct (sa_mulA Hx1 Hx) as [x5 [Hx2 Hx5]].
      apply lexistsR with x3; apply lexistsR with x5; apply lexistsR with Hx5; apply lexistsR with x4;
      apply lexistsR with x2; apply lexistsR with Hx2.
      rewrite sepSPC, sepSPA. reflexivity.
    + intros P Q R; split; intros H x; simpl.
      - apply lforallR; intro x1; apply lforallR; intro x2; apply lforallR; intro Hx1.
        apply wandSepSPAdj.
        specialize (H x2); simpl in H.
        rewrite <- H.
        apply lexistsR with x; apply lexistsR with x1; apply lexistsR with Hx1. reflexivity.
      - apply lexistsL; intro x1. apply lexistsL; intro x2; apply lexistsL; intro Hx.
        specialize (H x1); simpl in H.
        setoid_rewrite H.
        rewrite sepSPC. do 3 setoid_rewrite bilforallscR.
        apply lforallL with x2; apply lforallL with x; apply lforallL with Hx.
        rewrite sepSPC.
        apply wandSepSPAdj. reflexivity.
    + intros P Q R H x; simpl.
      apply lexistsL; intro x1; apply lexistsL; intro x2; apply lexistsL; intro Hx.
      apply lexistsR with x1; apply lexistsR with x2; apply lexistsR with Hx.
      rewrite H. reflexivity.
    + intros P; split; intros x; simpl.
      - setoid_rewrite <- bilexistssc.
        apply lexistsL; intro x1; apply lexistsL; intro x2; apply lexistsL; intro Hx; apply lexistsL; intro H2.
        rewrite empSPR.
        apply sa_unit_eq in Hx. rewrite <- Hx. reflexivity. assumption.
      - destruct (sa_unit_ex x) as [u [H1 H2]].
        setoid_rewrite <- bilexistssc.
        apply lexistsR with x; apply lexistsR with u; apply lexistsR with H2; apply lexistsR with H1.
        rewrite empSPR. reflexivity.
  Qed.

  Context {POB : @PureOp B}.
  Context {PureB : Pure POB}.

  Global Instance pureop_bi_sepalg2 : PureOp (ILPreFrm rel B) := {
    pure := fun (P : ILPreFrm rel B) =>
        (forall h, pure ((ILPreFrm_pred P) h)) /\
    	(forall h h', (ILPreFrm_pred P) h |-- (ILPreFrm_pred P) h')
  }.

  Global Instance pure_bi_sepalg2 : Pure pureop_bi_sepalg2.
  Proof.
    constructor.
    { unfold pure; simpl; intros; constructor.
      { unfold sepSP; simpl; intros.
        destruct H as [H H1].
        pose proof (@pure_axiom B _ _ _ PureB _ (H t)) as H2.
        destruct H2 as [H2 _].
        destruct (sa_unit_ex t) as [x [Hx Htx]].
        apply lexistsR with x.
        apply lexistsR with t.
        apply sa_mulC in Htx.
        eapply lexistsR with Htx.
        rewrite H2, (H1 t x); reflexivity. }
      constructor.
      { unfold sepSP; simpl; intros.
        repeat (eapply lexistsL; intros).
        destruct H as [H1 H2]; destruct H0 as [H3 H4].
        rewrite (H2 x t), (H4 x0 t).
        specialize (H1 t). specialize (H3 t).
        pose proof (@pure_axiom B _ _ _ PureB _ H1).
        destruct H as [_ [H _]].
        rewrite H. reflexivity. assumption. }
      constructor.
      { split; intros; unfold sepSP; simpl; intros.
        { repeat (eapply lexistsL; intros).
          destruct H as [H H1].
          pose proof (@pure_axiom B _ _ _ PureB) _ (H x) as H2.
          destruct H2 as [_ [_ [H2 _]]].
          rewrite H2.
          apply landR; [apply landL1; auto | apply landL2].
          do 3 eapply lexistsR; [eassumption|reflexivity]. }
        { rewrite landC.
          rewrite landexistsDL1.
          repeat (eapply lexistsL; intros).
          rewrite landexistsDL1.
          repeat (eapply lexistsL; intros).
          rewrite landexistsDL1.
          repeat (eapply lexistsL; intros).
          do 3 eapply lexistsR.
          eassumption. destruct H as [H H1].
          rewrite (H1 t x).
          pose proof (@pure_axiom B _ _ _ PureB) _ (H x) as H2.
          destruct H2 as [_ [_ [H2 _]]].
          destruct (H2 (Q x) (R x0)) as [_ H3].
          rewrite landC. assumption.
	   } }
      constructor.
      { unfold wandSP; simpl; intros.
        repeat (eapply lforallR; intros).
        destruct (sa_unit_ex x).
        destruct H0.
        eapply lforallL with x1.
        apply lforallL with x.
        eapply lforallL.
        rewrite x0. auto.
        destruct H as [H H2].
        pose proof (@pure_axiom B _ _ _ PureB) _ (H x1) as H3.
        destruct H3 as [_ [_ [_ [H3 _]]]].
        rewrite H3.
        apply limplAdj. apply limplL. apply H2. apply landL1. reflexivity. }
      { unfold wandSP; simpl; intros.
        repeat (eapply lforallR; intros).
        eapply lforallL. eapply lforallL. reflexivity.
        destruct H as [H H2].
        pose proof (@pure_axiom B _ _ _ PureB) _ (H x) as H3.
        destruct H3 as [_ [_ [_ [_ H3]]]].
        destruct H0 as [H4 H5].
        rewrite <- H3; [|auto].
        apply limplAdj. apply limplL; auto. apply landL1; auto. } }
    { red. red. unfold pure; simpl; intros.
      destruct PureB. repeat setoid_rewrite H; reflexivity. }
  Qed.

End BISepAlg2.

Section BILPre.
  Context T (ord: relation T) {HPre: PreOrder ord}.
  Context {A : Type} `{HBI: BILogic A}.
  Context {HIL : ILogic A}.

  Program Instance BILPre_Ops : BILogicOps (ILPreFrm ord A) := {|
    empSP      := mkILPreFrm (fun t => empSP) _;
    sepSP  P Q := mkILPreFrm (fun t => (ILPreFrm_pred P) t ** (ILPreFrm_pred Q) t) _;
    wandSP P Q := mkILPreFrm (fun t => Forall t', Forall H : ord t t', (ILPreFrm_pred P) t' -* (ILPreFrm_pred Q) t') _
  |}.
  Next Obligation.
    intros; rewrite H; reflexivity.
  Qed.
  Next Obligation.
    intros.
    apply lforallR; intro x; apply lforallR; intro Hx. rewrite <- H in Hx.
    apply lforallL with x; apply lforallL with Hx; reflexivity.
  Qed.

  Local Existing Instance ILPre_Ops.
  Local Existing Instance ILPre_ILogic.

  Local Transparent ILPre_Ops.

  Instance BILPreLogic : BILogic (ILPreFrm ord A).
  Proof.
    split.
    + apply _.
    + intros P Q x; simpl; apply sepSPC.
    + intros P Q R x; simpl; apply sepSPA.
    + intros P Q R; split; intros H t; simpl.
      * apply lforallR; intro t'; apply lforallR; intro H1.
        transitivity ((ILPreFrm_pred P) t'); [apply ILPreFrm_closed; assumption|].
        apply wandSepSPAdj; apply H.
      *  apply wandSepSPAdj; specialize (H t); unfold wandSP in H; simpl in H.
         rewrite H. apply lforallL with t; apply lforallL; reflexivity.
    + intros P Q R H x; simpl; apply bilsep; apply H.
    + intros P; split; intros x; simpl; apply empSPR.
  Qed.

  Context {POA : @PureOp A} {PA : Pure POA}.

  Instance PureBILPreOp : @PureOp (ILPreFrm ord A) := {
    pure := fun a => forall t, pure ((ILPreFrm_pred a) t)
  }.

  Instance PureBILPre : Pure (PureBILPreOp).
  Proof.
    constructor.
    { repeat split; intros; intro t; simpl.
      * eapply pureandsc; eauto.
      * eapply purescand; eauto.
      * eapply pureandscD; eauto.
      * eapply pureandscD; eauto.
      * apply lforallR; intro t'; apply lforallR; intro Ht.
        apply lforallL with t'; apply lforallL with Ht.
        eapply puresiimpl; eauto.
      * apply lforallR; intro t'; apply lforallR; intro Ht.
        apply lforallL with t'; apply lforallL with Ht.
        eapply pureimplsi; eauto. }
    { do 2 red. unfold pure; simpl. intros.
      split.
      { intros. eapply pure_proper. 2: eapply H0. symmetry.
        instantiate (1 := t).
        red in H. red. unfold lentails in H. simpl in H.
        intuition. }
      { intros. eapply pure_proper. 2: eapply H0. symmetry.
        instantiate (1 := t).
        red in H. red. unfold lentails in H. simpl in H.
        intuition. } }
  Qed.

  Instance pureBILPre (a : ILPreFrm ord A) (H : forall t, pure ((ILPreFrm_pred a) t)) : pure a.
  Proof.
    simpl; apply H.
  Qed.

End BILPre.

Section BILogic_Fun.
  Context (T: Type).
  Context {A : Type} `{BIL: BILogic A}.
  Context {HIL : ILogic A}.

  Local Transparent ILFun_Ops.

  Program Definition BILFun_Ops : BILogicOps ((fun x y => x -> y) T A) := {|
    empSP         := fun t => empSP;
    sepSP     P Q := fun t => P t ** Q t;
    wandSP    P Q := fun t => P t -* Q t
  |}.

  Local Existing Instance ILFun_Ops.
  Local Existing Instance ILFun_ILogic.
  Local Existing Instance BILFun_Ops.

  Program Definition BILFunLogic : @BILogic ((fun x y => x -> y) T A) (@ILFun_Ops T A _) BILFun_Ops.
  Proof.
    split.
    + apply _.
    + intros P Q x; simpl; apply sepSPC1.
    + intros P Q R x; simpl; apply sepSPA.
    + intros P Q R; split; intros H x; simpl;
      apply wandSepSPAdj; apply H.
    + intros P Q R H x; simpl; apply bilsep; apply H.
    + intros P; split; intros x; simpl; apply empSPR.
  Qed.

  Context {POA : @PureOp A} {PA : Pure POA}.

  Instance PureBILFunOp : @PureOp ((fun x y => x -> y) T A) := {
    pure := fun a => forall t, pure (a t)
  }.

  Instance PureBILFun : Pure (PureBILFunOp).
  Proof.
    constructor.
    { intros. repeat split; intros; intro t; simpl.
      * eapply pureandsc; eauto.
      * eapply purescand; eauto.
      * eapply pureandscD; eauto.
      * eapply pureandscD; eauto.
      * eapply puresiimpl; eauto.
      * eapply pureimplsi; eauto. }
    { do 2 red; simpl; intros.
      red in H. simpl in H.
      split.
      { intros. eapply pure_proper.
        2: eapply H0. split. intuition. intuition. }
      { intros. eapply pure_proper.
        2: eapply H0. split. intuition. intuition. } }
  Qed.

  Instance pureBILFun (a : (fun x y => x -> y) T A) (H : forall t, pure (a t)) : @pure _ PureBILFunOp a.
  Proof.
    simpl; apply H.
  Qed.

End BILogic_Fun.

Global Opaque BILPre_Ops.
Global Opaque BILFun_Ops.
Global Opaque SABIOps.
Global Opaque SABIOps2.
