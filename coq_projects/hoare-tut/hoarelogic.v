(** 

 This file is part of the "Tutorial on Hoare Logic".
 For an introduction to this Coq library,
 see README #or <a href=index.html>index.html</a>#.

 This file is mainly verbous. It defines a functor
 "[HoareLogic: ExprLang -> HoareLogicSem]".
 It is almost a copy/paste of definitions found in 
 #<a href=hoarelogicsemantics.html># 
 [hoarelogicsemantics]#</a>#. 
 (This is due to the lack of inheritance in the module system of Coq).


*)
  
Set Implicit Arguments.

Require Export hoarelogicsemantics.
Require Import partialhoarelogic.
Require Import totalhoarelogic.

Module HoareLogic(Ex: ExprLang)<: HoareLogicSem with Module E:=Ex.

Module E:=Ex.

Module HLD <: HoareLogicDefs with Module E:=E.

Module E:=E.

Inductive ImpProg: Type := 
  | Iskip: ImpProg
  | Iset (A:Type) (v:E.Var A) (expr:E.Expr A): ImpProg
  | Iif (cond:E.Expr bool) (p1 p2:ImpProg): ImpProg
  | Iseq (p1 p2:ImpProg): ImpProg
  | Iwhile (cond:E.Expr bool) (p:ImpProg): ImpProg.

Inductive exec: E.Env -> ImpProg -> E.Env -> Prop :=
 | exec_Iskip: 
    forall e, (exec e Iskip e)
 | exec_Iset:
    forall (A:Type) e x (expr: E.Expr A), 
     (exec e (Iset x expr) (E.upd x (E.eval expr e) e))
 | exec_Iif:
    forall e (cond: E.Expr bool) p1 p2 e', 
      (exec e (if (E.eval cond e) then p1 else p2) e') 
         -> (exec e (Iif cond p1 p2) e')
 | exec_Iseq:
    forall e p1 p2 e' e'',
      (exec e p1 e') 
       -> (exec e' p2 e'')    
         -> (exec e (Iseq p1 p2) e'')
 | exec_Iwhile:
    forall e cond p e', 
     (exec e (Iif cond (Iseq p (Iwhile cond p)) Iskip) e')
        -> (exec e (Iwhile cond p) e').

Lemma exec_Iif_true:
  forall e cond p1 p2 e', 
     (E.eval cond e)=true
      -> (exec e p1 e') 
         -> (exec e (Iif cond p1 p2) e').
Proof.
  intros e cond p1 p2 e' H1 H2.
  apply exec_Iif.
  rewrite H1; auto.
Qed.  

Lemma exec_Iif_false:
  forall e cond p1 p2 e', 
     (E.eval cond e)=false
      -> (exec e p2 e') 
         -> (exec e (Iif cond p1 p2) e').
Proof.
  intros e cond p1 p2 e' H1 H2.
  apply exec_Iif.
  rewrite H1; auto.
Qed.  

Definition Pred := E.Env -> Prop.

Definition wlp: ImpProg -> Pred -> Pred
 := fun prog post e => (forall e', (exec e prog e') -> (post e')).

Definition wp: ImpProg -> Pred -> Pred
 := fun prog post e => exists e', (exec e prog e') /\ (post e').


Notation "p |= q" := (forall e, (p e) -> (q e)) (at level 80, no associativity).
Notation "p {= post =}" := (wlp p post) (at level 70).
Notation "p [= post =]" := (wp p post) (at level 70).

End HLD.

Export HLD.

Module PHL<: HoareProofSystem := PartialHoareLogic(HLD). 
Module THL<: HoareProofSystem := TotalHoareLogic(HLD). 

Import THL.

Lemma wp_entails_wlp: forall prog post, prog [= post =] |= prog {= post =}.
Proof.
  unfold wp, wlp. intros prog post e H e' H'.
  dec2 e0 H.
  dec2 H0 H.
  rewrite (exec_deterministic H' H0).
  auto.
Qed.

End HoareLogic.

(** "Tutorial on Hoare Logic" Library. Copyright 2007 Sylvain Boulme.

This file is distributed under the terms of the 
 "GNU LESSER GENERAL PUBLIC LICENSE" version 3.  
*)
