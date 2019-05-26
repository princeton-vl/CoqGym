Require Import Coq.Classes.RelationClasses.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
From ChargeCore.Logics Require Import ILogic ILEmbed.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Definition Fun (A B : Type) := A -> B.

Section ILogic_Pre.
  Context T (ord: relation T) {HPre : PreOrder ord}.
  Context {A : Type} `{IL: ILogic A}.

  Record ILPreFrm := mkILPreFrm {
    ILPreFrm_pred :> T -> A;
    ILPreFrm_closed: forall t t': T, ord t t' ->
      ILPreFrm_pred t |-- ILPreFrm_pred t'
  }.

  Notation "'mk'" := @mkILPreFrm.

  Global Instance ILPreFrm_m (P: ILPreFrm): Proper (ord ++> lentails) (ILPreFrm_pred P).
  Proof.
    intros t t' Ht. apply ILPreFrm_closed; assumption.
  Qed.

  Program Definition ILPreFrm_atom (a : A) := mk (fun t => a) _.

  Local Obligation Tactic :=
    repeat match goal with
    | |- ord _ _ -> _ => intros Hord; try setoid_rewrite Hord; reflexivity
    | |- _ => intro
    end.

  Global Program Instance ILPre_Ops : ILogicOps ILPreFrm := {|
    lentails P Q := forall t:T, (ILPreFrm_pred P) t |-- (ILPreFrm_pred Q) t;
    ltrue        := mk (fun t => ltrue) _;
    lfalse       := mk (fun t => lfalse) _;
    limpl    P Q := mk (fun t => Forall t', Forall Ht' : ord t t', (ILPreFrm_pred P) t' -->> (ILPreFrm_pred Q) t') _;
    land     P Q := mk (fun t => (ILPreFrm_pred P) t //\\ (ILPreFrm_pred Q) t) _;
    lor      P Q := mk (fun t => (ILPreFrm_pred P) t \\// (ILPreFrm_pred Q) t) _;
    lforall  A P := mk (fun t => Forall a, (ILPreFrm_pred (P a)) t) _;
    lexists  A P := mk (fun t => Exists a, (ILPreFrm_pred (P a)) t) _
  |}.
  Next Obligation.
    apply lforallR; intro t''.
    apply lforallR; intro Ht'.
    apply lforallL with t''.
    assert (ord t t'') as Ht'' by (transitivity t'; assumption).
    apply lforallL with Ht''; reflexivity.
  Defined.
  Next Obligation.
    simpl; rewrite H; reflexivity.
  Defined.
  Next Obligation.
    simpl; rewrite H; reflexivity.
  Defined.
  Next Obligation.
    simpl; setoid_rewrite H; reflexivity.
  Defined.
  Next Obligation.
    simpl; setoid_rewrite H; reflexivity.
  Defined.

  Program Definition ILPre_ILogic : ILogic ILPreFrm.
  Proof.
   split; unfold lentails; simpl; intros.
    - split; red; [reflexivity|].
      intros P Q R HPQ HQR t.
      transitivity ((ILPreFrm_pred Q) t); [apply HPQ | apply HQR].
    - apply ltrueR.
    - apply lfalseL.
    - apply lforallL with x; apply H.
    - apply lforallR; intro x; apply H.
    - apply lexistsL; intro x; apply H.
    - apply lexistsR with x; apply H.
    - apply landL1; eapply H; assumption.
    - apply landL2; eapply H; assumption.
    - apply lorR1; eapply H; assumption.
    - apply lorR2; eapply H; assumption.
    - apply landR; [eapply H | eapply H0]; assumption.
    - apply lorL; [eapply H | eapply H0]; assumption.
    - apply landAdj.
      etransitivity; [apply H|]. apply lforallL with t.
      apply lforallL; reflexivity.
    - apply lforallR; intro t'; apply lforallR; intro Hord. apply limplAdj.
      rewrite ->Hord; eapply H; assumption.
  Qed.

  Global Existing Instance ILPre_ILogic.

  Global Instance ILPreFrm_pred_m {H : PreOrder ord}:
    Proper (lentails ++> ord ++> lentails) ILPreFrm_pred.
  Proof.
    intros P P' HPt t t' Ht. rewrite ->Ht. apply HPt.
  Qed.

  Global Instance ILPreFrm_pred_equiv_m:
    Equivalence ord ->
    Proper (lequiv ==> ord ==> lequiv) ILPreFrm_pred.
  Proof.
    intros Hord P P' HPt t t' Ht. split.
    - rewrite ->Ht. apply HPt.
    - symmetry in Ht. rewrite <-Ht. apply HPt.
  Qed.

  Global Instance ILPreFrm_pred_entails_eq_m:
    Proper (lentails ++> eq ++> lentails) ILPreFrm_pred.
  Proof.
    intros P P' HPt t t' Ht. subst; apply HPt.
  Qed.

  Global Instance ILPreFrm_pred_equiv_eq_m:
    Proper (lequiv ==> eq ==> lequiv) ILPreFrm_pred.
  Proof.
    intros P P' HPt t t' Ht. split; subst; apply HPt.
  Qed.

  Program Definition ILPreAtom {HPre : PreOrder ord} (t: T) :=
    mk (fun t' => Exists x : ord t t', ltrue) _.
  Next Obligation.
    apply lexistsL; intro H1.
    apply lexistsR; [transitivity t0; assumption | apply ltrueR].
  Qed.

End ILogic_Pre.

Arguments ILPreFrm [T] _ _ {ILOps} : rename.
Arguments mkILPreFrm {T} [ord] [A] {ILOps} _ _ : rename.

Section Embed_ILogic_Pre.
  Context T (ord: relation T) {HPre : PreOrder ord}.
  Context {A : Type} `{ILA: ILogic A}.
  Context {B : Type} `{ILB: ILogic B}.
  Context {HEmbOp : EmbedOp A B} {HEmb : Embed A B}.

(*
  Program Instance EmbedILPreDropOpEq : EmbedOp A (ILPreFrm ord A) := {
     embed := fun a => mkILPreFrm (fun x => a) _
  }.

  Instance EmbedILPreDropEq : Embed A (ILPreFrm ord A).
  Proof.
    split; intros.
    + simpl; intros. assumption.
    + split; intros t; simpl; reflexivity.
    + split; intros t; simpl; reflexivity.
    + split; intros t; simpl.
      * lforallL t. apply lforallL; reflexivity.
      * lforallR x H; reflexivity.
  Qed.
 *)
   Global Program Instance EmbedILPreDropOp : EmbedOp A (ILPreFrm ord B) := {
     embed := fun a => mkILPreFrm (fun x => embed a) _
  }.

  Global Instance EmbedILPreDrop : Embed A (ILPreFrm ord B).
  Proof.
    split; intros.
    + simpl; intros. apply embed_sound; assumption.
    + split; intros t; simpl; apply embedlforall.
    + split; intros t; simpl; apply embedlexists.
    + split; intros t; simpl.
      * apply lforallL with t. apply lforallL; [reflexivity | apply embedImpl].
      * apply lforallR; intro x; apply lforallR; intro H. apply embedImpl.
  Qed.

  Global Program Instance EmbedILPreOp : EmbedOp (ILPreFrm ord A) (ILPreFrm ord B) := {
     embed := fun a => mkILPreFrm (fun x => embed ((ILPreFrm_pred a) x)) _
  }.
  Next Obligation.
  	rewrite H. reflexivity.
  Defined.

  Global Instance EmbedILPre : Embed (ILPreFrm ord A) (ILPreFrm ord B).
  Proof.
    split; intros.
    + simpl; intros. apply embed_sound; apply H.
    + split; intros t; simpl; apply embedlforall.
    + split; intros t; simpl; apply embedlexists.
    + split; intros t; simpl;
      do 2 setoid_rewrite <- embedlforall;
      apply lforallR; intro t'; apply lforallR; intro H;
      apply lforallL with t'; apply lforallL with H; apply embedImpl.
  Qed.

End Embed_ILogic_Pre.

(** If [Frm] is a ILogic, then the function space [T -> Frm] is also an ilogic,
    for any type [T]. All connectives are just pointwise liftings. *)

Section ILogic_Fun.
  Context (T: Type).
  Context {A : Type} `{IL: ILogic A}.

  Global Program Instance ILFun_Ops : ILogicOps ((fun x y => x -> y) T A) := {|
    lentails P Q := forall t:T, P t |-- Q t;
    ltrue        := fun t => ltrue;
    lfalse       := fun t => lfalse;
    limpl    P Q := fun t => P t -->> Q t;
    land     P Q := fun t => P t //\\ Q t;
    lor      P Q := fun t => P t \\// Q t;
    lforall  A P := fun t => Forall a, P a t;
    lexists  A P := fun t => Exists a, P a t
  |}.

  Program Definition ILFun_ILogic : @ILogic _ ILFun_Ops.
  Proof.
    split; unfold lentails; simpl; intros.
    - split; red; [reflexivity|].
      intros P Q R HPQ HQR t. transitivity (Q t); [apply HPQ | apply HQR].
    - apply ltrueR.
    - apply lfalseL.
    - apply lforallL with x; apply H.
    - apply lforallR; intros; apply H.
    - apply lexistsL; intros; apply H.
    - apply lexistsR with x; apply H.
    - apply landL1; intuition.
    - apply landL2; intuition.
    - apply lorR1; intuition.
    - apply lorR2; intuition.
    - apply landR; intuition.
    - apply lorL; intuition.
    - apply landAdj; intuition.
    - apply limplAdj; intuition.
  Qed.

  Global Existing Instance ILFun_ILogic.

End ILogic_Fun.

Section ILogic_Option.
  Context {A : Type} `{IL: ILogic A}.

  Definition toProp (P : option A) :=
    match P with
    | Some P => P
    | None => lfalse
    end.

  Global Program Instance ILOption_Ops : ILogicOps (option A) :=
  {| lentails P Q := toProp P |-- toProp Q
   ; ltrue        := Some ltrue
   ; lfalse       := Some lfalse
   ; limpl    P Q := Some (toProp P -->> toProp Q)
   ; land     P Q := Some (toProp P //\\ toProp Q)
   ; lor      P Q := Some (toProp P \\// toProp Q)
   ; lforall  A P := Some (Forall a, toProp (P a))
   ; lexists  A P := Some (Exists a, toProp (P a))
   |}.

  Program Definition ILOption_ILogic : ILogic (option A).
  Proof.
    split; unfold lentails; simpl; intros.
    - split; red; [reflexivity|].
      intros P Q R HPQ HQR. transitivity (toProp Q); [apply HPQ | apply HQR].
    - apply ltrueR.
    - apply lfalseL.
    - apply lforallL with x; apply H.
    - apply lforallR; intros; apply H.
    - apply lexistsL; intros; apply H.
    - apply lexistsR with x; apply H.
    - apply landL1; intuition.
    - apply landL2; intuition.
    - apply lorR1; intuition.
    - apply lorR2; intuition.
    - apply landR; intuition.
    - apply lorL; intuition.
    - apply landAdj; intuition.
    - apply limplAdj; intuition.
  Qed.

End ILogic_Option.

Section Embed_ILogic_Fun.
  Context {A : Type} `{ILA: ILogic A}.
  Context {B : Type} `{ILB: ILogic B}.
  Context {HEmbOp : EmbedOp A B} {HEmb : Embed A B}.

  Program Instance EmbedILFunDropOp {T} : EmbedOp A (T -> B) :=
  { embed := fun a t => embed a }.

  Local Existing Instance ILFun_Ops.

  Instance EmbedILFunDrop {T} : Embed A (T -> B).
  Proof.
    split; intros.
    + simpl; intros. apply embed_sound; assumption.
    + split; intros t; simpl; apply embedlforall.
    + split; intros t; simpl; apply embedlexists.
    + split; intros t; simpl; apply embedImpl.
  Qed.

  Program Instance EmbedILFunOp {T} : EmbedOp (T -> A) (T -> B) :=
  { embed := fun a x => embed (a x) }.

  Instance EmbedILFun {T} : Embed (T -> A) (T -> B).
  Proof.
    split; intros.
    + simpl; intros. apply embed_sound; apply H.
    + split; intros t; simpl; apply embedlforall.
    + split; intros t; simpl; apply embedlexists.
    + split; intros t; simpl; apply embedImpl.
  Qed.

End Embed_ILogic_Fun.
(*
Section ILogicFunInv.

	Context {A B} `{IL : ILogic (A -> B)}.

  Program Definition ILFun_Ops : ILogicOps (T -> A) := {|
    lentails P Q := forall t:T, P t |-- Q t;
    ltrue        := fun t => ltrue;
    lfalse       := fun t => lfalse;
    limpl    P Q := fun t => P t -->> Q t;
    land     P Q := fun t => P t //\\ Q t;
    lor      P Q := fun t => P t \\// Q t;
    lforall  A P := fun t => Forall a, P a t;
    lexists  A P := fun t => Exists a, P a t
  |}.


End ILogicFunInv.
*)
Global Opaque ILOption_Ops.
Global Opaque ILFun_Ops.
Global Opaque ILPre_Ops.
