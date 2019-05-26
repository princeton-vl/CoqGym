From ChargeCore.Logics Require Import ILogic ILInsts BILogic ILEmbed.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section Pure.

  Context {A : Type} {ILOPs : ILogicOps A} {BILOps : BILogicOps A}.

  Class PureOp := {
    pure : A -> Prop
  }.

  Definition parameter_pure (pure : A -> Prop) (P : A) : Prop :=
    (forall Q, P //\\ Q |-- P ** Q) /\
    (forall Q, pure Q -> P ** Q |-- P //\\ Q) /\
    (forall Q R, (P //\\ Q) ** R -|- P //\\ (Q ** R)) /\
    (forall Q, P -* Q |-- P -->> Q) /\
    (forall Q, pure Q -> P -->> Q |-- P -* Q).


  Class Pure {HP : PureOp} :=
  { pure_axiom : forall p, pure p -> parameter_pure pure p
  ; pure_proper : Proper (lequiv ==> iff) pure
  }.

  Existing Class pure.

  Context (IL : ILogic A) (BIL : BILogic A) (po : PureOp) (p : @Pure po).

  Lemma pureandsc P Q : pure P -> P //\\ Q |-- P ** Q.
  Proof.
    intros. eapply pure_axiom in H. destruct H. intuition.
  Qed.

  Lemma purescand  P Q : pure P -> pure Q -> P ** Q |-- P //\\ Q.
  Proof.
    intros. eapply pure_axiom in H. destruct H. intuition.
  Qed.

  Lemma pureandscD P Q R : pure P -> (P //\\ Q) ** R -|- P //\\ (Q ** R).
  Proof.
    intros. eapply pure_axiom in H; destruct H; intuition.
  Qed.

  Lemma puresiimpl P Q : pure P -> P -* Q |-- P -->> Q.
  Proof.
    intros. eapply pure_axiom in H; destruct H; intuition.
  Qed.

  Lemma pureimplsi P Q : pure P -> pure Q -> P -->> Q |-- P -* Q.
  Proof.
    intros. eapply pure_axiom in H; destruct H; intuition.
  Qed.

(*
  Instance pure_ltrue : pure ltrue.
  Proof.
    eapply pure_axiom.
    repeat constructor.
    { intros. rewrite <- (empSPL (ltrue //\\ Q)).
      etransitivity. 2: eapply bilsep.
      rewrite sepSPC. erewrite (sepSPC _ Q). eapply bilsep.
      eapply landL2. reflexivity. eapply ltrueR. }
    { intros.
      rewrite sepSPC.
      rewrite <- (landtrueR Q) at 1.
      rewrite pureandscD by auto.
      eapply landR. eapply ltrueR. eapply landL1. reflexivity. }
    { eapply landR. eapply ltrueR.
      eapply bilsep. eapply landL2. reflexivity. }
    { eapply landL2. eapply bilsep. eapply landR. eapply ltrueR. reflexivity. }
    { intros. eapply limplAdj. eapply landL1.
      rewrite septrue. eapply wandSPL; auto. }
    { intros. eapply wandSepSPAdj.
      rewrite limplTrue.
      rewrite <- (landtrueR Q) at 1.
      rewrite pureandscD; auto. apply landL1. reflexivity. }
  Qed.

  Instance pure_land x y : pure x -> pure y ->  pure (x //\\ y).
  Proof.
    intros.
    eapply pure_axiom.
    constructor.
    { intros. rewrite landA.
      rewrite pureandscD; auto.
      apply landR. apply landL1. reflexivity.
      apply landL2. apply pureandsc; auto. }
    constructor.
    { intros.
      rewrite pureandscD by auto.
      rewrite landA. apply landR. apply landL1. reflexivity.
      apply landL2. apply purescand; auto. }
    constructor.
    { intros.
      rewrite landA. rewrite pureandscD by auto.
      rewrite landA. rewrite pureandscD by auto.
      reflexivity. }
    constructor.
    { intros.
      eapply limplAdj. rewrite landC.
      rewrite landA.
      rewrite pureandsc by auto.
      rewrite pureandsc by auto.
      rewrite <- sepSPA.
      rewrite (@purescand x y) by auto.
      rewrite sepSPC. apply wandSPL; reflexivity. }
    { intros.
      rewrite landC at 1.
      rewrite curry.
      rewrite pureandsc by auto.
      rewrite wand_curry.
      eapply wandSPAdj.
      rewrite <- pureimplsi by auto.
      apply limplAdj.
      rewrite landC.
      rewrite <- pureandscD by auto.
      eapply sepSPAdj.
      rewrite landC.
      eapply limplL. reflexivity.
      apply landL1.
      eapply pureimplsi; auto. }
  Qed.

  Instance pure_sc x y (Hx : pure x) (Hy : pure y) : pure (x ** y).
  Proof.
    eapply pure_axiom; repeat split; intros.
    + rewrite sepSPA. 
      do 2 (etransitivity; [|rewrite <- pureandsc; eauto]).
      rewrite purescand by auto. apply landA.
    + etransitivity; [|rewrite <- pureandsc; eauto].
      rewrite landA. rewrite <- purescand by auto using pure_land.
      rewrite <- purescand by auto.
      apply sepSPA.
    + etransitivity; [rewrite (purescand Hx Hy); reflexivity|].
      etransitivity; [|rewrite <- pureandsc by auto; reflexivity].
      rewrite <- pureandscD by eauto using pure_land. reflexivity.
    + etransitivity; [|rewrite <- (@pureandsc x y) by auto; reflexivity].
      rewrite purescand by auto.
      rewrite pureandscD by auto using pure_land; reflexivity.
    + etransitivity; [|rewrite purescand by auto; reflexivity].
      etransitivity; [rewrite <- pureandsc by auto; reflexivity|].
      rewrite puresiimpl by auto using pure_land; reflexivity.
    + etransitivity; [|rewrite purescand by auto; reflexivity].
      etransitivity; [rewrite <- pureandsc by auto; reflexivity|].
      rewrite pureimplsi by auto using pure_land; reflexivity.
  Qed.

  Instance pure_limpl x y (Hx : pure x) (Hy : pure y) : pure (x -->> y).

  Instance pure_lor x y : pure x -> pure y ->  pure (x \\// y).
*)

End Pure.

Arguments Pure {A ILOPs BILOps} HP : rename.
Arguments PureOp _ : rename, clear implicits.