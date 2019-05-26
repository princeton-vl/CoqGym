Require Import Setoid Morphisms RelationClasses Program.Basics.
From ChargeCore.Logics Require Import ILogic IBILogic BILogic BILInsts ILInsts Pure ILEmbed.
From ChargeCore.SepAlg Require Import SepAlg.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section PureBIInsts.
  Context {A} `{sa : SepAlg A}.
  Context {B} `{IL: ILogic B}.
  Context {HPre : PreOrder rel}.

  Existing Instance SABIOps.
  Existing Instance SABILogic.
  Existing Instance pureop_bi_sepalg.
  Existing Instance pure_bi_sepalg.
  Existing Instance ILPre_Ops.
  Existing Instance ILPre_ILogic.

  Transparent ILPre_Ops.
  Transparent SABIOps.

  Instance pure_ltrue : pure ltrue.
  Proof.
    intros h h'; reflexivity.
  Qed.

  Instance pure_lfalse : pure lfalse.
  Proof.
    intros h h'; reflexivity.
  Qed.

  Instance pure_land p q (Hp : pure p) (Hq : pure q) : pure (p //\\ q).
  Proof.
    intros h h'; simpl.
    specialize (Hp h h'); specialize (Hq h h').
    rewrite Hp, Hq; reflexivity.
  Qed.

  Instance pure_lor p q (Hp : pure p) (Hq : pure q) : pure (p \\// q).
  Proof.
    intros h h'; simpl.
    specialize (Hp h h'); specialize (Hq h h').
    rewrite Hp, Hq; reflexivity.
  Qed.

  Instance pure_limpl p q (Hp : pure p) (Hq : pure q) : pure (p -->> q).
  Proof.
    intros h h'; simpl.
    apply lforallR; intro h''; apply lforallR; intro H.
    apply lforallL with h. apply lforallL; [reflexivity|].
    specialize (Hp h'' h); specialize (Hq h h'').
    rewrite Hp, Hq; reflexivity.
  Qed.

  Instance pure_lsc p q (Hp : pure p) (Hq : pure q) : pure (p ** q).
  Proof.
    intros h h'; simpl.
    apply lexistsL; intro h''; apply lexistsL; intro h'''; apply lexistsL; intro H.
    destruct (sa_unit_ex h') as [u [Ha H1]].
    apply lexistsR with h'; apply lexistsR with u. apply lexistsR with H1.
    specialize (Hp h'' h'); specialize (Hq h''' u).
    rewrite Hp, Hq; reflexivity.
  Qed.

  Instance pure_lsi p q (Hp : pure p) (Hq : pure q) : pure (p -* q).
  Proof.
    intros h h'; simpl.
    apply lforallR; intro h''; apply lforallR; intro h'''; apply lforallR; intro H.
    destruct (sa_unit_ex h) as [u [Ha H1]].
    apply lforallL with u; apply lforallL with h; apply lforallL with H1.
    specialize (Hp h'' u); specialize (Hq h h''').
    rewrite Hp, Hq; reflexivity.
  Qed.


  Context {C : Type} {ILC : ILogicOps C} {HCOp: EmbedOp C B} {HC: Embed C B}.

  Local Existing Instance EmbedILPreDropOp.
  Local Existing Instance EmbedILPreOp.
  Transparent EmbedILPreDropOp.
  Transparent EmbedILPreOp.

  Instance pure_bi_embed_drop (p : C) : pure (@embed C (ILPreFrm rel B) _ p).
  Proof.
    intros h h'; simpl; reflexivity.
  Qed.

  Instance pure_bi_embed (p : ILPreFrm rel C) (H : pure p) :
    pure (@embed (ILPreFrm rel C) (ILPreFrm rel B) _ p).
  Proof.
    intros h h'; simpl.
    specialize (H h h'). rewrite H. reflexivity.
  Qed.

End PureBIInsts.

Section PureIBIInsts.
  Context {A} `{sa : SepAlg A}.
  Context {B} `{IL: ILogic B}.
  Context {HPre : PreOrder rel}.

  Existing Instance SAIBIOps.
  Existing Instance SAIBILogic.
  Existing Instance pureop_pure_ibi_sepalg.
  Existing Instance pure_ibi_sepalg.
  Existing Instance ILPre_Ops.
  Existing Instance ILPre_ILogic.

  Transparent ILPre_Ops.
  Transparent SAIBIOps.

  Instance ibi_pure_ltrue : pure ltrue.
  Proof.
    intros h h'; reflexivity.
  Qed.

  Instance ibi_pure_lfalse : pure lfalse.
  Proof.
    intros h h'; reflexivity.
  Qed.

  Instance ibi_pure_emp : pure empSP.
  Proof.
    intros h h'; simpl; apply ltrueR.
  Qed.

  Instance ibi_pure_land p q (Hp : pure p) (Hq : pure q) : pure (p //\\ q).
  Proof.
    intros h h'; simpl.
    specialize (Hp h h'); specialize (Hq h h').
    rewrite Hp, Hq; reflexivity.
  Qed.

  Instance ibi_pure_lor p q (Hp : pure p) (Hq : pure q) : pure (p \\// q).
  Proof.
    intros h h'; simpl.
    specialize (Hp h h'); specialize (Hq h h').
    rewrite Hp, Hq; reflexivity.
  Qed.

  Instance ibi_pure_limpl p q (Hp : pure p) (Hq : pure q) : pure (p -->> q).
  Proof.
    intros h h'; simpl.
    apply lforallR; intro h''; apply lforallR; intro H.
    apply lforallL with h. apply lforallL; [reflexivity|].
    specialize (Hp h'' h); specialize (Hq h h'').
    rewrite Hp, Hq; reflexivity.
  Qed.

  Instance ibi_pure_lsc p q (Hp : pure p) (Hq : pure q) : pure (p ** q).
  Proof.
    intros h h'; simpl.
    apply lexistsL; intro h''; apply lexistsL; intro h'''; apply lexistsL; intro H.
    destruct (sa_unit_ex h') as [u [Ha H1]].
    apply lexistsR with h'; apply lexistsR with u. apply lexistsR with H1.
    specialize (Hp h'' h'); specialize (Hq h''' u).
    rewrite Hp, Hq; reflexivity.
  Qed.

  Instance ibi_pure_lsi p q (Hp : pure p) (Hq : pure q) : pure (p -* q).
  Proof.
    intros h h'; simpl.
    apply lforallR; intro h''; apply lforallR; intro h'''; apply lforallR; intro H.
    destruct (sa_unit_ex h) as [u [Ha H1]].
    apply lforallL with u; apply lforallL with h; apply lforallL with H1.
    specialize (Hp h'' u); specialize (Hq h h''').
    rewrite Hp, Hq; reflexivity.
  Qed.

  Context {C : Type} {ILC : ILogicOps C} {HCOp: EmbedOp C B} {HC: Embed C B}.

  Local Existing Instance EmbedILPreDropOp.
  Local Existing Instance EmbedILPreOp.

  Transparent EmbedILPreDropOp.
  Transparent EmbedILPreOp.


  Instance pure_ibi_embed_drop (p : C) : pure (@embed C (ILPreFrm subheap B) _ p).
  Proof.
    intros h h'; simpl; reflexivity.
  Qed.

  Instance pure_ibi_embed (p : ILPreFrm subheap C) (H : pure p) :
    pure (@embed (ILPreFrm subheap C) (ILPreFrm subheap B) _ p).
  Proof.
    intros h h'; simpl.
    specialize (H h h'). rewrite H. reflexivity.
  Qed.

End PureIBIInsts.

Section PureEmbedFun.
  Context (T: Type).
  Context {A : Type} `{BIL: BILogic A}.
  Context {HIL : ILogic A}.
  Context {B : Type} {ILX : ILogicOps B} {HBOp: EmbedOp B A} {HB : Embed B A}.
  Context {POA : @PureOp A} {PA : Pure POA}.

  Existing Instance PureBILFunOp.
  Existing Instance PureBILFun.
  Existing Instance ILFun_Ops.
  Existing Instance ILFun_ILogic.
  Existing Instance BILFun_Ops.
  Existing Instance BILFunLogic.
  Existing Instance EmbedILFunDropOp.
  Existing Instance EmbedILFunDrop.
  Existing Instance EmbedILFunOp.
  Existing Instance EmbedILFun.

  Transparent EmbedILFunDropOp.
  Transparent EmbedILFunOp.

  Instance pure_embed_fun_drop (p : B) (H : pure (@embed B A _ p)) :
    pure (@embed B (T -> A) _ p).
  Proof.
    intros t; simpl; apply H.
  Qed.

  Instance pure_embed_fun (p : T -> B) (H : forall t, pure (@embed B A _ (p t))) :
    pure (@embed (T -> B) (T -> A) _ p).
  Proof.
    intros t; simpl; apply H.
  Qed.

End PureEmbedFun.

Section PureEmbedPre.
  Context T (ord: relation T) {HPre: PreOrder ord}.
  Context {A : Type} `{HBI: BILogic A}.
  Context {HIL : ILogic A}.
  Context {B : Type} {ILX : ILogicOps B} {HBOp: EmbedOp B A} {HB : Embed B A}.
  Context {POA : @PureOp A} {PA : Pure POA}.

  Existing Instance PureBILPreOp.
  Existing Instance PureBILPre.
  Existing Instance ILPre_Ops.
  Existing Instance ILPre_ILogic.
  Existing Instance BILPre_Ops.
  Existing Instance BILPreLogic.
  Existing Instance EmbedILPreDropOp.
  Existing Instance EmbedILPreDrop.
  Existing Instance EmbedILPreOp.
  Existing Instance EmbedILPre.

  Transparent EmbedILPreDropOp.
  Transparent EmbedILPreOp.

  Instance pure_embed_pre_drop (p : B) (H : pure (@embed B A _ p)) :
    pure (PureOp := PureBILPreOp ord) (@embed B (ILPreFrm ord A) _ p).
  Proof.
    intros t. apply H.
  Qed.

  Instance pure_embed_pre (p : ILPreFrm ord B) (H : forall t, pure (@embed B A _ (ILPreFrm_pred p t))) :
    pure (PureOp := PureBILPreOp ord) (@embed (ILPreFrm ord B) (ILPreFrm ord A) _ p).
  Proof.
    intro t; apply H.
  Qed.

End PureEmbedPre.
