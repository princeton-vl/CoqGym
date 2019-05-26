Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
From ChargeCore.Logics Require Import ILogic ILEmbed.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section BILogic.
  Definition BILogicType := Type.

  Context {A : BILogicType}.
  Context {HILOp: ILogicOps A}.

  Class BILogicOps (A : BILogicType) : Type := {
    empSP  : A;
    sepSP  : A -> A -> A;
    wandSP : A -> A -> A
  }.

  Class BILogic {BILOp: BILogicOps A} : Type := {
    bilil :> ILogic A;
    sepSPC1 P Q : sepSP P Q |-- sepSP Q P;
    sepSPA1 P Q R : sepSP (sepSP P Q) R |-- sepSP P (sepSP Q R);
    wandSepSPAdj P Q R : sepSP P Q |-- R <-> P |-- wandSP Q R;
    bilsep P Q R : P |-- Q -> sepSP P R |-- sepSP Q R;
    empSPR P : sepSP P empSP -|- P
  }.

End BILogic.

Arguments BILogic _ {BILOp HILOp} : rename.

Notation "a '**' b"  := (sepSP a b)
  (at level 58, right associativity).
Notation "a '-*' b"  := (wandSP a b)
  (at level 60, right associativity).

Section CoreInferenceRules.

  Context {A T : Type} `{HBIL: BILogic A}.

  Lemma wandSPAdj P Q C (HSep: C ** P |-- Q) : C |-- P -* Q.
  Proof.
    apply wandSepSPAdj; assumption.
  Qed.

  Lemma wandSPAdj' P Q C (HSep: P ** C |-- Q) : C |-- P -* Q.
  Proof.
    apply wandSepSPAdj. etransitivity; [apply sepSPC1|]. assumption.
  Qed.

  Lemma sepSPAdj P Q C (HWand: C |-- P -* Q) : C ** P |-- Q.
  Proof.
    apply wandSepSPAdj; assumption.
  Qed.

  Lemma sepSPAdj' P Q C (HWand: C |-- P -* Q) : P ** C |-- Q.
  Proof.
    etransitivity; [apply sepSPC1|]. apply wandSepSPAdj. assumption.
  Qed.

  Lemma sepSPC (P Q : A) : P ** Q -|- Q ** P.
  Proof.
    split; apply sepSPC1.
  Qed.

  Lemma sepSPA2 (P Q R : A) : P ** (Q ** R) |-- (P ** Q) ** R.
  Proof.
    rewrite sepSPC.
    etransitivity; [apply sepSPA1|].
    rewrite sepSPC.
    etransitivity; [apply sepSPA1|].
    rewrite sepSPC.
    reflexivity.
  Qed.

  Lemma sepSPA (P Q R : A) : (P ** Q) ** R -|- P ** (Q ** R).
  Proof.
    split; [apply sepSPA1 | apply sepSPA2].
  Qed.

  Lemma wandSPI (P Q R : A) (HQ : P ** Q |-- R) : (P |-- Q -* R).
  Proof.
    apply wandSPAdj; assumption.
  Qed.

  Lemma wandSPE (P Q R S : A) (HQR: Q |-- S -* R) (HP : P |-- Q ** S) : P |-- R.
  Proof.
    apply sepSPAdj in HQR.
    rewrite <- HQR, HP. reflexivity.
  Qed.

  Lemma empSPL P : empSP ** P -|- P.
  Proof.
    rewrite sepSPC; apply empSPR.
  Qed.

  Lemma bilexistsscR1 (P : A) (f : T -> A):
    Exists x : T, P ** f x |-- P ** lexists f.
  Proof.
  	apply lexistsL; intro x.
    rewrite sepSPC. etransitivity; [|rewrite <- sepSPC; reflexivity].
    apply bilsep. eapply lexistsR; reflexivity.
  Qed.

  Lemma bilexistsscR2 (P : A) (f : T -> A):
    Exists x : T, f x ** P |-- lexists f ** P.
  Proof.
    rewrite sepSPC, <- bilexistsscR1.
    setoid_rewrite sepSPC at 1.
    reflexivity.
  Qed.

    Lemma bilexistsscL1 (P : A) (f : T -> A) :
    P ** lexists f |-- Exists x : T, P ** f x.
  Proof.
    rewrite sepSPC; rewrite wandSepSPAdj.
    apply lexistsL; intro x; erewrite <- wandSPAdj. reflexivity.
    eapply lexistsR; rewrite sepSPC; reflexivity.
  Qed.

  Lemma bilexistsscL2 (P : A) (f : T -> A) :
    lexists f ** P |-- Exists x : T, f x ** P.
  Proof.
    rewrite sepSPC, bilexistsscL1.
    setoid_rewrite sepSPC at 1.
    reflexivity.
  Qed.

    Lemma bilexistssc (P : A) (Q : T -> A) :
    Exists x : T, P ** Q x -|- P ** lexists Q.
  Proof.
    split; [apply bilexistsscR1 | apply bilexistsscL1].
  Qed.

  Lemma bilforallscR (P : A) (Q : T -> A) :
    P ** lforall Q |-- Forall x : T, P ** Q x.
  Proof.
    apply lforallR; intro x.
    rewrite sepSPC; etransitivity; [|rewrite <- sepSPC; reflexivity].
    apply bilsep. apply lforallL with x; reflexivity.
  Qed.

  Lemma bilandscDL (P Q R : A) : (P //\\ Q) ** R |-- (P ** R) //\\ (Q ** R).
  Proof.
  	apply landR.
  	+ apply wandSepSPAdj; apply landL1; apply wandSepSPAdj; reflexivity.
  	+ apply wandSepSPAdj; apply landL2; apply wandSepSPAdj; reflexivity.
  Qed.

  Lemma bilorscDL (P Q R : A) : (P \\// Q) ** R -|- (P ** R) \\// (Q ** R).
  Proof.
  	split.
  	+ apply wandSepSPAdj; apply lorL; apply wandSepSPAdj;
  	  [apply lorR1 | apply lorR2]; reflexivity.
  	+ apply lorL; apply bilsep; [apply lorR1 | apply lorR2]; reflexivity.
  Qed.

End CoreInferenceRules.

Section BILogicMorphisms.
  Context {A : BILogicType} `{BIL: BILogic A}.

  Global Instance sepSP_lentails_m:
    Proper (lentails ++> lentails ++> lentails) sepSP.
  Proof.
    intros P P' HP Q Q' HQ.
    etransitivity; [eapply bilsep; exact HP|].
    rewrite -> sepSPC.
    etransitivity; [eapply bilsep; exact HQ|].
    rewrite -> sepSPC. reflexivity.
  Qed.

  Global Instance sepSP_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) sepSP.
  Proof.
    intros P P' HP Q Q' HQ.
    split; apply sepSP_lentails_m; (apply HP || apply HQ).
  Qed.

  Global Instance wandSP_lentails_m:
    Proper (lentails --> lentails ++> lentails) wandSP.
  Proof.
    intros P P' HP Q Q' HQ. red in HP.
    apply wandSPAdj. rewrite <- HQ, -> HP.
    apply sepSPAdj. reflexivity.
  Qed.

  Global Instance wandSP_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) wandSP.
  Proof.
    intros P P' HP Q Q' HQ.
    split; apply wandSP_lentails_m; (apply HP || apply HQ).
  Qed.

End BILogicMorphisms.

Section DerivedInferenceRules.

  Context {A : BILogicType} `{BILogic A}.

  Lemma sepSP_falseR P : P ** lfalse -|- lfalse.
  Proof.
    rewrite lfalse_is_exists, <- bilexistssc.
    split; apply lexistsL; intro x; destruct x.
  Qed.

  Lemma sepSP_falseL P : lfalse ** P -|- lfalse.
  Proof.
    rewrite -> sepSPC; apply sepSP_falseR.
  Qed.

  Lemma scME (P Q R S : A) (HPR: P |-- R) (HQS: Q |-- S) :
    P ** Q |-- R ** S.
  Proof.
    rewrite HPR, HQS; reflexivity.
  Qed.

  Lemma wandSPL P Q CL CR (HP: CL |-- P) (HR: Q |-- CR) :
    (P -* Q) ** CL |-- CR.
  Proof.
    rewrite <-HR, <-HP. apply sepSPAdj. reflexivity.
  Qed.


  Lemma siexistsE {T : Type} (P : T -> A) (Q : A) :
    lexists P -* Q -|- Forall x, (P x -* Q).
  Proof.
    split.
	+ apply lforallR; intro x. apply wandSepSPAdj; eapply wandSPL; [|reflexivity].
	  apply lexistsR with x. reflexivity.
	+ apply wandSepSPAdj. rewrite bilexistsscL1. apply lexistsL; intro x.
	  rewrite sepSPC, bilforallscR. apply lforallL with x. rewrite sepSPC.
	  apply wandSPL; reflexivity.
  Qed.

  Lemma septrue : forall p, p |-- p ** ltrue.
  Proof.
    intros. rewrite <- empSPR at 1.
    rewrite sepSPC. rewrite (sepSPC p).
    apply bilsep. apply ltrueR.
  Qed.

  Lemma wand_curry : forall a b c, (a ** b) -* c -|- a -* (b -* c).
  Proof.
    intros; split.
    { eapply wandSPAdj.
      eapply wandSPAdj.
      rewrite sepSPA.
      eapply sepSPAdj.
      reflexivity. }
    { eapply wandSPAdj.
      rewrite <- sepSPA.
      eapply sepSPAdj.
      eapply sepSPAdj. reflexivity. }
  Qed.

End DerivedInferenceRules.