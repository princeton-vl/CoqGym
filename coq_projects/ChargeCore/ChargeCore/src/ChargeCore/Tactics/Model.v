Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Logics.ILInsts.
Require Import ChargeCore.Logics.BILInsts.
Require Import ChargeCore.Logics.Later.

Require Import Setoid.
Require Import Omega.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Local Existing Instance ILPre_Ops.
Local Existing Instance ILPre_ILogic.
Local Existing Instance ILFun_Ops.
Local Existing Instance ILFun_ILogic.
(*Local Existing Instance EquivPreorder.*)

Local Transparent ILPre_Ops.
Local Transparent ILFun_Ops.
Local Transparent BILPre_Ops.
Local Transparent BILFun_Ops.
Local Transparent ILLaterPreOps.
Local Transparent ILLaterNatOps.

Section ILogic_Pre.
  Context T (ord: relation T) {HPre : PreOrder ord}.
  Context {A : Type} `{IL: ILogic A}.

  Lemma ILPreFrm_fold_entails x y (P Q : ILPreFrm ord _) (Hord : ord x y) (H : P |-- Q) : 
    P x |-- Q y.
  Proof.
    etransitivity.
    apply ILPreFrm_closed.
    eassumption.
    apply H.
  Qed.
  
  Lemma ILPreFrm_intro (P Q : ILPreFrm ord _) (H : forall x, P x |-- Q x) :
  	P |-- Q.
  Proof.
    intros x; apply H.
  Qed.
  
  Lemma ILPreFrm_apply {P Q : ILPreFrm ord _} (x : T) (H : P |-- Q) : P x |-- Q x.
  Proof.
    apply H.
  Qed.
  
End ILogic_Pre.

Section ILogic_Fun.
  Context (T: Type).
  Context {A : Type} {IL: ILogicOps A}.

  Lemma ILFun_fold_entails x y (P Q : Fun T A) (Hxy : x = y) (HPQ : P |-- Q) :
    P x |-- Q y.
  Proof.
    rewrite Hxy; apply HPQ.
  Qed.
  
  Lemma ILFun_intro (P Q : Fun T A) (H : forall x, P x |-- Q x) :
    P |-- Q.
  Proof.
    intros x; apply H.
  Qed.
  
  Lemma ILFun_apply {P Q : Fun T A} (x : T) (H : P |-- Q) : P x |-- Q x.
  Proof.
    apply H.
  Qed.
  
End ILogic_Fun.

Ltac solve_atom :=
	match goal with 
		| |- ?P => first [has_evar P | reflexivity | omega | assumption | idtac]
	end.
    
Ltac solve_model_aux := 
	match goal with
		| |- ?P ?a |-- ?Q ?b =>
			 first [apply ILPreFrm_fold_entails; [solve_atom|solve_model_aux] | 
			        apply ILFun_fold_entails; [solve_atom|solve_model_aux]]
	    | |- ?P |-- ?Q => try reflexivity
	end.

Ltac solve_model x :=
	let H := fresh "H" in
	match goal with 
		| |- ?Q => let P := type of x in
						assert (P |-- Q) as H; [solve_model_aux|apply H; apply x]
						
    end.

Ltac ilapply_aux t H :=
	match t with
    	| ?f ?x => ilapply_aux f H; first [apply (ILPreFrm_apply x) in H | 
    	                                   apply (ILFun_apply x) in H]
    	| _ => idtac
    end.

Ltac ilapply H :=
	let H1 := fresh "H" in
	  pose proof H as H1;
	  match goal with 
	  	| |- ?f ?x => ilapply_aux (f x) H1; apply H1; clear H1
	  end.

Ltac lintros_aux n := first [apply ILPreFrm_intro | apply ILFun_intro]; intro n.

Tactic Notation "lintros" ident(n) := lintros_aux n.
Tactic Notation "lintros" ident(n1) ident(n2) := lintros n1; lintros n2.
Tactic Notation "lintros" ident(n1) ident(n2) ident(n3) := lintros n1 n2; lintros n3.
Tactic Notation "lintros" ident(n1) ident(n2) ident(n3) ident(n4) := 
	lintros n1 n2 n3; lintros n4.
Tactic Notation "lintros" ident(n1) ident(n2) ident(n3) ident(n4) ident(n5) := 
	lintros n1 n2 n3 n4; lintros n5.
Tactic Notation "lintros" ident(n1) ident(n2) ident(n3) ident(n4) ident(n5) 
                          ident(n6) := 
	lintros n1 n2 n3 n4 n5; lintros n6.
Tactic Notation "lintros" ident(n1) ident(n2) ident(n3) ident(n4) ident(n5) 
                          ident(n6) ident(n7) := 
	lintros n1 n2 n3 n4 n5 n6; lintros n7.
Tactic Notation "lintros" ident(n1) ident(n2) ident(n3) ident(n4) ident(n5) 
                          ident(n6) ident(n7) ident(n8) := 
	lintros n1 n2 n3 n4 n5 n6 n7; lintros n8.
Tactic Notation "lintros" ident(n1) ident(n2) ident(n3) ident(n4) ident(n5) 
                          ident(n6) ident(n7) ident(n8) ident(n9) := 
	lintros n1 n2 n3 n4 n5 n6 n7 n8; lintros n9.
Tactic Notation "lintros" ident(n1) ident(n2) ident(n3) ident(n4) ident(n5) 
                          ident(n6) ident(n7) ident(n8) ident(n9) ident(n10) := 
	lintros n1 n2 n3 n4 n5 n6 n7 n8 n9; lintros n10.
