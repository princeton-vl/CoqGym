Require Import Setoid Morphisms RelationClasses Omega.
From ChargeCore.Logics Require Import ILogic ILInsts ILEmbed.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section LaterSect.
  Context {A : Type}.
  Context `{ILOps: ILogicOps A}.

Class ILLOperators (A : Type) : Type := {
  illater : A -> A
}.

Class ILLater {ILLOps: ILLOperators A} : Type := {
  illogic :> ILogic A;
  spec_lob P : illater P |-- P -> |-- P;
  spec_later_weaken P : P |-- illater P;
  spec_later_impl P Q : illater (P -->> Q) -|- (illater P) -->> (illater Q);
  spec_later_forall {T} (F : T -> A) : illater (Forall x:T, F x) -|- Forall x:T, illater (F x);
  spec_later_exists {T} (F : T -> A) : Exists x : T, illater (F x) |-- illater (Exists x : T, F x);
  spec_later_exists_inhabited {T} (F : T -> A) : inhabited T -> illater (Exists x : T, F x) |-- Exists x : T, illater (F x)
}.
End LaterSect.

Arguments ILLater _ _ _ : clear implicits.
Arguments ILLater _ {ILLOps ILOps} : rename.
Notation "'|>' a"  := (illater a) (at level 71).

Section ILogicLaterCoreRules.
  Context {A} `{IL: ILLater A}.

  Global Instance spec_later_entails:
    Proper (lentails ==> lentails) illater.
  Proof.
    intros P P' HP.
    rewrite <- limplValid, <- spec_later_impl, <- spec_later_weaken, limplValid.
    assumption.
  Qed.

  Global Instance spec_later_equiv:
    Proper (lequiv ==> lequiv) illater.
  Proof.
    intros P P' HP. split; cancel1; rewrite HP; reflexivity.
  Qed.

  Lemma spec_later_and P P': |>(P //\\ P') -|- |>P //\\ |>P'.
  Proof.
    do 2 rewrite land_is_forall; rewrite spec_later_forall;
    split; apply lforallR; intro x; apply lforallL with x;
    destruct x; reflexivity.
  Qed.

  Lemma spec_later_or P P': |>(P \\// P') -|- |>P \\// |>P'.
  Proof.
    do 2 rewrite lor_is_exists; split;
    [rewrite spec_later_exists_inhabited; [|firstorder]| rewrite <- spec_later_exists];
    apply lexistsL; intro x; apply lexistsR with x; destruct x; reflexivity.
  Qed.

  Lemma spec_later_true : |>ltrue -|- ltrue.
  Proof.
    split; [intuition|].
    rewrite ltrue_is_forall, spec_later_forall.
    apply lforallR; intro x; destruct x.
  Qed.

End ILogicLaterCoreRules.

Hint Rewrite
  @spec_later_and
  @spec_later_impl
  @spec_later_true
  @spec_later_forall
  : push_later.

Section ILogic_nat.
  Context {A : Type}.
  Context `{IL: ILogic A}.

  Global Program Instance ILLaterNatOps : ILLOperators (ILPreFrm ge A)  :=
    {|
      illater P := mkILPreFrm (fun x => Forall y : nat, Forall H : y < x, (ILPreFrm_pred P) y) _
    |}.
  Next Obligation.
    intros.
    apply lforallR; intro x; apply lforallR; intro Hx; apply lforallL with x.
    apply lforallL; [omega | reflexivity].
  Qed.

Local Transparent ILPre_Ops.

  Global Instance ILLaterNat : ILLater (ILPreFrm ge A).
  Proof.
    split.
    + apply _.
    + intros P H x; induction x.
      - rewrite <- H; simpl; apply lforallR; intro y;
        apply lforallR; intro Hy; omega.
      - rewrite <- H; simpl; apply lforallR; intro y; apply lforallR; intro Hy.
        assert (x >= y) by omega.
        rewrite <- ILPreFrm_closed; eassumption.
    + intros P x; simpl; apply lforallR; intro y; apply lforallR; intro Hyx.
      apply ILPreFrm_closed; simpl. omega.
    + intros P Q; split; intros x; simpl.
      - apply lforallR; intro y; apply lforallR; intro Hxy.
        apply limplAdj.
        apply lforallR; intro z; apply lforallR; intro Hzy.
        rewrite landC, landforallD; [|apply _].
        apply lforallL with z.
        rewrite landforallD; [|repeat split; assumption].
        apply lforallL with Hzy.
        rewrite landC. apply landAdj.
        apply lforallL with z. apply lforallL; [omega|].
        apply lforallL with z. apply lforallL; [omega|].
	    reflexivity.
      - apply lforallR; intro y; apply lforallR; intro Hyx; apply lforallR; intro z; apply lforallR; intro Hyz.
        apply lforallL with (z + 1).
        apply lforallL. omega.
        apply limplAdj.
        apply limplL.
        apply lforallR; intro a; apply lforallR; intro Ha.
        apply ILPreFrm_closed. omega.
        apply landL1.
        apply lforallL with z; apply lforallL; [omega | reflexivity].
    + intros T F; split; simpl; intros x.
      - apply lforallR; intro a; apply lforallR; intro y; apply lforallR; intro Hyx.
        apply lforallL with y; apply lforallL with Hyx; apply lforallL with a.
        reflexivity.
      - apply lforallR; intro y; apply lforallR; intro Hyx; apply lforallR; intro a.
        apply lforallL with a; apply lforallL with y; apply lforallL with Hyx.
        reflexivity.
    + intros T F x; simpl.
      apply lexistsL; intro a; apply lforallR; intro y; apply lforallR; intro H.
      apply lforallL with y; apply lforallL with H; apply lexistsR with a.
      reflexivity.
    + intros T F Hin x; simpl.
      inversion Hin as [a]; destruct x.
      - apply lexistsR with a; apply lforallR; intro y; apply lforallR; intro H; omega.
      - apply lforallL with x. apply lforallL; [omega|].
        apply lexistsL; intro b; apply lexistsR with b.
        apply lforallR; intro y; apply lforallR; intro H.
        apply ILPreFrm_closed; omega.
  Qed.

End ILogic_nat.

Section IBILPre.
  Context T (ord: relation T) {ord_Pre: PreOrder ord}.
  Context {A : Type} `{HBI: ILLater A}.
  Context {IL : ILogic A}.

  Local Existing Instance ILPre_Ops.
  Local Existing Instance ILPre_ILogic.

  Local Transparent ILPre_Ops.

  Global Program Instance ILLaterPreOps : ILLOperators (ILPreFrm ord A) := {|
    illater P := mkILPreFrm (fun t => |>((ILPreFrm_pred P) t)) _
  |}.
  Next Obligation.
    rewrite H. reflexivity.
  Qed.

  Program Definition ILLaterPre : ILLater (ILPreFrm ord A).
  Proof.
    split.
    + apply _.
    + intros P HP x. apply spec_lob. apply HP.
    + intros P x. apply spec_later_weaken.
    + intros P Q; split; intros x; simpl;
        setoid_rewrite <- spec_later_impl;
        do 2 setoid_rewrite spec_later_forall; reflexivity.
    + intros B F; split; intros x; simpl; apply spec_later_forall.
    + intros B F x; simpl; apply spec_later_exists.
    + intros B F I x; simpl; apply spec_later_exists_inhabited; apply I.
  Qed.

  Global Existing Instance ILLaterPre.

End IBILPre.

Section IBILogic_Fun.
  Context (T: Type).
  Context {A : Type} `{ILL: ILLater A}.

  Local Existing Instance ILFun_Ops.
  Local Existing Instance ILFun_ILogic.

  Local Transparent ILFun_Ops.

  Program Instance ILLaterFunOps : ILLOperators (Fun T A) := {|
    illater P := fun t => |>(P t)
  |}.

  Program Definition ILLaterFun : ILLater (Fun T A).
  Proof.
    split.
    + apply _.
    + intros P HP x. apply spec_lob. apply HP.
    + intros P x. apply spec_later_weaken.
    + intros P Q; split; intros x; simpl;
      apply spec_later_impl.
    + intros B F; split; intros x; simpl; apply spec_later_forall.
    + intros B F x; simpl; apply spec_later_exists.
    + intros B F I x; simpl; apply spec_later_exists_inhabited; apply I.
  Qed.

  Global Existing Instance ILLaterFun.

End IBILogic_Fun.

Global Opaque ILLaterPreOps.
Global Opaque ILLaterNatOps.
Global Opaque ILLaterFunOps.
