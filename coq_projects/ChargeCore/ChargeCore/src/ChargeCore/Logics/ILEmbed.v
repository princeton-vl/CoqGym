Require Import ChargeCore.Logics.ILogic.
Require Import Setoid Morphisms RelationClasses Program.Basics Omega.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section ILogicEmbed.
  Context {A} `{ILOpsA: ILogicOps A}.
  Context {B} `{ILOpsB: ILogicOps B}.

  Class EmbedOp : Type := { embed : A -> B }.

  Class Embed {EmbOp: EmbedOp} : Type := {
     embed_sound p q : p |-- q -> embed p |-- embed q;

     embedlforall T f : Forall x : T, embed (f x) -|- embed (Forall x : T, f x);
     embedlexists T f : Exists x : T, embed (f x) -|- embed (Exists x : T, f x);
     embedImpl a b : (embed a) -->> (embed b) -|- embed (a -->> b)
  }.
End ILogicEmbed.

Arguments EmbedOp _ _ : clear implicits.
Arguments Embed _ {ILOpsA} _ {ILOpsB EmbOp} : rename.

Section ILogicEmbedOps.
  Context {A B} `{HAB: Embed A B} {ILA: ILogic A} {ILB: ILogic B}.

  Definition lembedand (a : A) (b : B) := (embed a) //\\ b.
  Definition lembedimpl (a : A) (b : B) := (embed a) -->> b.

End ILogicEmbedOps.


Section ILEmbedId.

  Context {A : Type} `{ILA : ILogic A}.

  Instance EmbedOpId : EmbedOp A A := { embed := id }.
  Global Instance EmbedId : Embed A A.
  Proof.
    split; firstorder.
  Qed.

End ILEmbedId.

Section ILogicEmbedCompose.
  Context {A B} `{HAB: Embed A B} {ILA: ILogic A} {ILB: ILogic B}.
  Context {C} {HC: ILogicOps C} {HE: EmbedOp B C} {HBC : Embed B C} {ILC: ILogic C}.

  Instance embedOpCompose : EmbedOp A C := { embed := fun x => embed (embed x) }.

  Program Instance embedCompose : Embed A C.
  Next Obligation.
  	do 2 apply embed_sound; assumption.
  Qed.
  Next Obligation.
  	split;
  	rewrite embedlforall; apply embed_sound; rewrite embedlforall; reflexivity.
  Qed.
  Next Obligation.
  	split;
  	rewrite embedlexists; apply embed_sound; rewrite embedlexists; reflexivity.
  Qed.
  Next Obligation.
  	split;
  	rewrite embedImpl; apply embed_sound; rewrite embedImpl; reflexivity.
  Qed.

End ILogicEmbedCompose.

Infix "/\\" := lembedand (at level 75, right associativity).
Infix "->>" := lembedimpl (at level 77, right associativity).

Section ILogicEmbedFacts.
  Context {A B} `{HAB: Embed A B} {ILA: ILogic A} {ILB: ILogic B}.

  Global Instance embed_lentails_m :
    Proper (lentails ==> lentails) embed.
  Proof.
    intros a b Hab; apply embed_sound; assumption.
  Qed.

  Global Instance embed_lequiv_m :
    Proper (lequiv ==> lequiv) embed.
  Proof.
    intros a b Hab; split; destruct Hab; apply embed_sound; assumption.
  Qed.

  Global Instance lembedimpl_lentails_m:
    Proper (lentails --> lentails ++> lentails) lembedimpl.
  Proof.
    intros P P' HP Q Q' HQ; red in HP.
    unfold lembedimpl. rewrite <- HP, HQ; reflexivity.
  Qed.

  Global Instance lembedimpl_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) lembedimpl.
  Proof.
    intros P P' HP Q Q' HQ.
    split; apply lembedimpl_lentails_m; (apply HP || apply HQ).
  Qed.

  Global Instance lembedand_lentails_m:
    Proper (lentails ==> lentails ==> lentails) lembedand.
  Proof.
    intros P P' HP Q Q' HQ.
    unfold lembedand. rewrite HP, HQ. reflexivity.
  Qed.

  Global Instance lembedand_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) lembedand.
  Proof.
    intros P P' HP Q Q' HQ.
    split; apply lembedand_lentails_m; (apply HP || apply HQ).
  Qed.

  Lemma embedland a b : embed a //\\ embed b -|- embed (a //\\ b).
  Proof.
    do 2 rewrite land_is_forall; rewrite <- embedlforall; split;
    apply lforallR; intro x; apply lforallL with x;
    destruct x; reflexivity.
  Qed.

  Lemma embedlor a b : embed a \\// embed b -|- embed (a \\// b).
  Proof.
    do 2 rewrite lor_is_exists; erewrite <- embedlexists; split;
    apply lexistsL; intro x; apply lexistsR with x;
    destruct x; reflexivity.
  Qed.

  Lemma embedlfalse : embed lfalse -|- lfalse.
  Proof.
    rewrite lfalse_is_exists; erewrite <- embedlexists; split;
    [apply lexistsL; intro x; destruct x | apply lfalseL].
  Qed.

  Lemma embedltrue : embed ltrue -|- ltrue.
  Proof.
    rewrite ltrue_is_forall; rewrite <- embedlforall; split;
    [apply ltrueR | apply lforallR; intro x; destruct x].
  Qed.

  Lemma embedlandC (P R : B) (Q : A) : P //\\ Q /\\ R -|- Q /\\ P //\\ R.
  Proof.
  	unfold lembedand; rewrite <- landA, (landC P), landA; reflexivity.
  Qed.

  Lemma embedlimplC (P R : B) (Q : A) : P -->> Q ->> R -|- Q ->> P -->> R.
  Proof.
    unfold lembedimpl. do 2 rewrite limplAdj2.
    rewrite landC. reflexivity.
  Qed.

  Lemma limpllandC (P Q R : B) : P //\\ (Q -->> R) |-- Q -->> P //\\ R.
  Proof.
  	apply limplAdj; rewrite landA; apply landR.
  	+ apply landL1. reflexivity.
  	+ apply landL2. apply limplL; [reflexivity | apply landL1; reflexivity].
  Qed.

  Lemma embed_existsL (P : A) : Exists x : |-- P, ltrue |-- embed P.
  Proof.
  	apply lexistsL; intro H.
  	rewrite <- H. rewrite embedltrue. apply ltrueR.
  Qed.

End ILogicEmbedFacts.

Section EmbedProp.
  Context {A : Type} `{HIL: ILogic A} {HPropOp: EmbedOp Prop A} {HProp: Embed Prop A}.

  Lemma embedPropExists (p : Prop) : embed p |-- Exists x : p, ltrue.
  Proof.
    assert (p |-- Exists x : p, (|-- ltrue)). {
      intros Hp. exists Hp. apply ltrueR.
    } etransitivity.
    rewrite H. reflexivity.
    rewrite <- embedlexists. apply lexistsL. intros Hp.
    apply lexistsR with Hp. apply ltrueR.
  Qed.

  Lemma embedPropExistsL (p : Prop) (P : A) : Exists x : p, P |-- embed p.
  Proof.
    assert (Exists x : p, ltrue |-- p). {
      intros HP. destruct HP as [HP _]. apply HP.
    }
    etransitivity; [|rewrite <- H]; [reflexivity|].
    rewrite <- embedlexists. apply lexistsL; intro Hp.
    apply lexistsR with Hp. rewrite embedltrue. apply ltrueR.
  Qed.

  (* TODO rename embedPropExists to embedPropExistsR *)
  Lemma embedPropExists' (p : Prop) : Exists x : p, ltrue -|- embed p.
  Proof.
  	split; [apply embedPropExistsL | apply embedPropExists].
  Qed.

  Lemma embedPropL (p : Prop) C (H: p -> |-- C) :
    embed p |-- C.
  Proof.
  	rewrite embedPropExists.
  	apply lexistsL; intro Hp.
  	apply H; apply Hp.
  Qed.

  Lemma embedPropR (p : Prop) (P : A) (H : p) : P |-- embed p.
  Proof.
    assert (ltrue |-- p) by (intros _; assumption).
    rewrite <- H0, embedltrue; apply ltrueR.
  Qed.

  Lemma lpropandL (p: Prop) Q C (H: p -> Q |-- C) :
    p /\\ Q |-- C.
  Proof.
    unfold lembedand.
    apply landAdj.
    apply embedPropL.
    intros Hp.
    apply limplAdj.
    apply landL2.
    apply H. assumption.
  Qed.

  Lemma lpropandR C (p: Prop) Q (Hp: p) (HQ: C |-- Q) :
    C |-- p /\\ Q.
  Proof.
    unfold lembedand.
    apply landR; [|assumption].
    rewrite <- embedPropR. apply ltrueR. assumption.
  Qed.

  Lemma lpropimplL (p: Prop) (Q C: A) (Hp: p) (HQ: Q |-- C) :
    p ->> Q |-- C.
  Proof.
    unfold lembedimpl.
    rewrite <- embedPropR, limplTrue; assumption.
  Qed.

  Lemma lpropimplR C (p: Prop) Q (H: p -> C |-- Q) :
    C |-- p ->> Q.
  Proof.
    unfold lembedimpl.
    apply limplAdj. rewrite landC. apply lpropandL. assumption.
  Qed.

  (* Derivable but useful *)
  Lemma lpropandTrue P : True /\\ P -|- P.
  Proof.
    split.
    + apply lpropandL; intros _; reflexivity.
    + apply landR.
      * replace True with (@ltrue Prop _) by reflexivity.
        rewrite embedltrue. apply ltrueR.
      * reflexivity.
  Qed.

  Lemma lpropandFalse P : False /\\ P -|- lfalse.
  Proof.
    split.
    + apply lpropandL; intros H; destruct H.
    + apply lfalseL.
  Qed.


End EmbedProp.


Section EmbedProp'.
  Context {A : Type} `{HILA: ILogic A} {HPropOpA: EmbedOp Prop A} {HPropA: Embed Prop A}.
  Context {B : Type} `{HILB: ILogic B} {HPropOpB: EmbedOp Prop B} {HPropB: Embed Prop B}.
  Context {HEmbOp : EmbedOp B A} {Hemb: Embed B A}.

  Lemma lpropandAL (p : B) (q : A) (P : Prop) : P /\\ p /\\ q |-- (P /\\ p) /\\ q.
  Proof.
    apply lpropandL; intros HP; apply landR.
    + apply landL1; apply embed_sound; apply landR.
      * apply embedPropR. assumption.
      * reflexivity.
    + apply landL2; reflexivity.
  Qed.

  Lemma lpropandAC (p : B) (q : A) (P : Prop) : p /\\ P /\\ q -|- P /\\ p /\\ q.
  Proof.
  	unfold lembedand. do 2 rewrite <- landA; rewrite (landC (embed p)); reflexivity.
  Qed.

  Lemma lpropandAR (p : B) (q : A) (P : Prop) : (P /\\ p) /\\ q |-- P /\\ p /\\ q.
  Proof.
  	apply landR.
  	+ apply landL1.
  	  unfold lembedand; rewrite <- embedland; apply landL1.
  	  rewrite embedPropExists, <- embedlexists.
  	  apply lexistsL; intro Hp.
  	  apply embedPropR; apply Hp.
  	+ unfold lembedand; rewrite <- embedland; apply landR.
  	  * apply landL1; apply landL2. reflexivity.
  	  * apply landL2; reflexivity.
 Qed.

 Lemma lpropimplAL (p : B) (q : A) (P : Prop) : (P ->> p) /\\ q |-- P ->> (p /\\ q).
 Proof.
    unfold lembedimpl, lembedand. apply limplAdj. rewrite landA.
    rewrite <- embedImpl. apply limplL. apply landL2.
    rewrite embedPropExists. apply lexistsL; intro Hp.
    rewrite <- (embedPropR ltrue); [apply embedltrue | apply Hp].
    apply landR; [apply landL1|apply landL2; apply landL1]; reflexivity.
 Qed.

 Lemma lpropimplAR (p : B) (q : A) (P : Prop) : p /\\ (P ->> q) |-- P ->> (p /\\ q).
 Proof.
    unfold lembedimpl, lembedand. rewrite landC. apply limplAdj. rewrite landA.
    apply limplL. apply landL2; reflexivity.
    apply landR; [apply landL2; apply landL1|apply landL1]; reflexivity.
 Qed.


  Lemma embedPropR2 (p : Prop) (P : A) (H : p) : P |-- embed (embed p).
  Proof.
    assert (ltrue |-- p) by (intros _; assumption).
    rewrite <- H0. do 2 rewrite embedltrue. apply ltrueR.
  Qed.

  Lemma embedPropL2 (p : Prop) (C : A) (H: p -> |-- C) :
    embed (embed p) |-- C.
  Proof.
  	rewrite embedPropExists, <- embedlexists.
  	apply lexistsL; intro Hp. rewrite embedltrue.
  	apply H; apply Hp.
  Qed.

End EmbedProp'.

Section EmbedPropProp.

Instance EmbedOpPropProp : EmbedOp Prop Prop := { embed := fun P => P }.
Instance EmbedPropProp : Embed Prop Prop.
Proof.
  split; firstorder.
Qed.

End EmbedPropProp.

Section EmbedPropInj.
  Context {A : Type} `{ILA : ILogic A}.
  Context {EmbOp1 : EmbedOp Prop A} {Emb1 : Embed Prop A}.
  Context {EmbOp2 : EmbedOp Prop A} {Emb2 : Embed Prop A}.

  Lemma emb_prop_eq (P : Prop) : @embed _ _ EmbOp1 P -|- @embed _ _ EmbOp2 P.
  Proof.
    split; rewrite embedPropExists; apply lexistsL; intro Hp;
      (rewrite <- (embedPropR ltrue); [apply ltrueR | apply Hp]).
  Qed.

End EmbedPropInj.
