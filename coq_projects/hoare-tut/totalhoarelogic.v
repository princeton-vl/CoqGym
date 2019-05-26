(** * Generation of Hoare proof obligations in total correctness

 This file is part of the "Tutorial on Hoare Logic".
 For an introduction to this Coq library,
 see README #or <a href=index.html>index.html</a>#.

 This file gives a syntactic definition of the weakest precondition [wp]
 introduced in #<a href=hoarelogicsemantics.html>#[hoarelogicsemantics]#</a>#.
 We refine here the approach of  #<a href=partialhoarelogic.html>#[partialhoarelogic]#</a>#.
*)

Global Set Asymmetric Patterns.
Set Implicit Arguments.
Require Export hoarelogicsemantics.
Require Wf.

Module TotalHoareLogic (HD: HoareLogicDefs).

Export HD.
Module HLD:=HD.

Definition sem_wp := wp.

Export Wf.

(** * Syntactic definition of the weakest precondition.

 In the following, we show that this definition is logically
 equivalent to [wp].
 *)
Fixpoint synt_wp (prog: ImpProg) : Pred -> Pred 
 := fun post e =>
  match prog with
  | Iskip => post e
  | (Iset A x expr) => post (E.upd x (E.eval expr e) e)
  | (Iif cond p1 p2) =>
          ((E.eval cond e)=true -> (synt_wp p1 post e))
       /\ ((E.eval cond e)=false -> (synt_wp p2 post e))
  | (Iseq p1 p2) => synt_wp p1 (synt_wp p2 post) e
  | (Iwhile cond p) =>  
        exists inv:Pred,
        exists R:E.Env -> E.Env -> Prop,
             (well_founded R)
          /\ (inv e)
          /\ (forall e', (inv e') 
                  -> (E.eval cond e')=false -> post e')
          /\ (forall e', (inv e') 
                  -> (E.eval cond e')=true -> synt_wp p inv e')
          /\ (forall e0, (inv e0)
                  -> (E.eval cond e0)=true -> synt_wp p (fun e1 => R e1 e0) e0)
  end.

(** * Soundness *)

(** Monotonicity is also trivially satisfied by [wp].
    We need it here to prove the soundness.
*)
Lemma synt_wp_monotonic: 
  forall (p: ImpProg) (post1 post2: Pred),
   (forall e, post1 e -> post2 e)
    -> forall e, (synt_wp p post1 e) -> (synt_wp p post2 e).
Proof.
  induction p; simpl; firstorder eauto.
Qed.

Hint Resolve synt_wp_monotonic: hoare.

(** Below, a little tactic to decompose a pair in hypothesis [H]
    by giving the name [n] to the first component. 
 *)
Ltac dec2 n H := case H; clear H; intros n H.

(** The property below is also satisfied by [wp] (using the fact that 
    the language is deterministic).
    We need it here to prove the soundness.
*)
Lemma synt_wp_conj:
 forall (p: ImpProg) (post1 post2: Pred) e,
   (synt_wp p post1 e) -> (synt_wp p post2 e) 
     -> (synt_wp p (fun e => post1 e /\ post2 e) e).
Proof.
  induction p; simpl; try ((intuition auto); fail).
  (* Iseq *)
  intros post1 post2 e H1 H2. 
  intros; eapply synt_wp_monotonic.
  2: apply (IHp1 _ _ _ H1 H2).
  simpl; intuition auto.
  (* Iwhile *)
  intros post1 post2 e H1 H2. 
  dec2 inv1 H1. 
  dec2 R1 H1.
  dec2 inv2 H2.
  intros;
  constructor 1 with (x:=fun e => inv1 e /\ inv2 e).
  constructor 1 with (x:=R1).
  firstorder auto.
Qed.


(** The proof of soundness proceeds by induction over [prog].
*)
Lemma wp_sound: forall prog post, synt_wp prog post |= prog [=post=].
Proof.
 unfold wp.
 induction prog; simpl; try ((intuition eauto with hoare); fail). 
 (* - case [Iif] *)
 intros post e.
 set (b:=E.eval cond e).
 cut (E.eval cond e=b); auto.
 case b; firstorder eauto with hoare.
 (* - case [Iseq] *)
 intros post e H; case (IHprog1 _ _ H).
 intros e0 H0; case (IHprog2 post e0); firstorder eauto with hoare.
 (* - case [Iwhile] *)
 intros post e H.
 dec2 inv H.
 dec2 R H.
 dec2 Rwf H.
 dec2 Hinv H.
 dec2 H1 H.
 dec2 H2 H.
 generalize Hinv.
 pattern e.
 (* -- here the proof proceeds by induction on the well-founded relation *)
 eapply well_founded_ind; eauto.
 clear Hinv e.
 intros e' X H'.
 set (b:=E.eval cond e').
 cut (E.eval cond e'=b); auto.
 case b; [ idtac | firstorder eauto with hoare ].
 intros H5.
 case (IHprog (wp (Iwhile cond prog) post) e');
 [ idtac | (unfold wp; firstorder eauto with hoare) ].
 eapply synt_wp_monotonic.
 2:apply (synt_wp_conj _ _ _ _ (H2 _ H' H5) (H _ H' H5)).
 simpl; unfold wp; intuition auto.
Qed.

(** * Auxiliary lemmas for completeness

   The proof of completeness requires to exhibit a variant. 
   The purpose of the following lemmas is to build this variant.
*)

(** ** A technical issue: the inversion of [exec]

   If your are not interested in Coq details, you may skip this part
   which only explains how to avoid the assumption of a (consistent
   and standard) axiom to prove the completeness.

   Because the use of dependent types in constructor [exec_Iset], the
   standard inversion of Coq may fail on [exec] (see
   [exec_test_inversion] below).

   This comes from the fact the following property is not provable in
   the core theory of Coq (although it is consistent with it) :

   [forall A (x1 x2:E.Var A) e1 e2, (Iset x1 e1)=(Iset x2 e2) -> x1=x2 /\ e1=e2.]

   To deal with this problem, we may assume a (consistent) axiom given
   in #<a href=http://coq.inria.fr/V8.1/stdlib/Coq.Logic.EqdepFacts.html>#
      [EqdepFacts]#</a>#.
   But here, we can avoid this axiom.

   Indeed, I define an ad-hoc inversion lemma for [exec] called
   [exec_inversion] below. This lemma is directly derived from the
   notion of weakest liberal precondition: [aux_wlp] is an other
   alternative definition of [wlp].

*)
Definition aux_wlp (prog: ImpProg) : Pred -> Pred 
 := fun post e =>
  match prog with
  | Iskip => post e
  | (Iset A x expr) => post (E.upd x (E.eval expr e) e)
  | (Iif cond p1 p2) =>
       forall e', exec e (if E.eval cond e then p1 else p2) e' 
          -> post e'
  | (Iseq p1 p2) => forall e1 e2, exec e p1 e1 -> exec e1 p2 e2 -> post e2
  | (Iwhile cond p) => forall e', exec e (Iif cond (Iseq p (Iwhile cond p)) Iskip) e' -> post e'
  end.

(** This lemma is my inversion lemma of [exec]. It expresses the "soundness" of [aux_wlp]. *)
Lemma exec_inversion:
  forall prog e e', (exec e prog e') -> forall post, (aux_wlp prog post e) -> post e'.
Proof.
  induction 1; simpl;
  try ((firstorder eauto with hoare); fail).
Qed.

(** Here is the case, where the previous lemma is better than the standard inversion of Coq. *)
Lemma exec_test_inversion:
  forall A (x:E.Var A) expr e e',
     (exec e (Iset x expr) e') -> e'=(E.upd x (E.eval expr e) e).
Proof.
  intros A x expr e e' H.
  (** Here, try "[inversion H]" instead the tactic below. 
      The generated goal is not directly provable. *)
  pattern e'; apply (exec_inversion H); simpl; auto.
Qed.
 
(** Below, a little tactic to helps in applying [exec_inversion]. *)
Ltac exec_inversion H :=
  match type of H with
  | (exec ?e ?p ?e') => pattern e'; apply (exec_inversion H); simpl; clear H
  end.

(** ** The programming language is deterministic

This property is probably not necessary to prove the correctness of my
variant, but it simplifies the proof a lot.

This lemma is a trivial induction over the first [exec] derivation, 
provided the ad-hoc inversion tactic on the second [exec] derivation.
*)
Lemma exec_deterministic: forall ei p ef,
  (exec ei p ef) -> forall ef', (exec ei p ef') -> ef=ef'.
Proof.
  induction 1; intros ef' X; exec_inversion X; eauto.
  (* - case [Iseq] *)
  intros e1 e2 X1 X2; assert (X3: e'=e1); auto.
  subst; auto.
Qed.

(** ** Definition of the variant 
  Given a program [p] and a boolean expression [cond], the relation on environment 
  "[reduces cond p]" is the variant required by "[synt_wp (Iwhile cond p)]".

  I prove below that this relation is well-founded.
*) 
Definition reduces cond p e1 e0 :=
  (E.eval cond e0)=true /\ (exec e0 p e1) /\ exists ef, (exec e1 (Iwhile cond p) ef).

(** To prove that "[reduces cond p]" is well-founded, I want to count  
    the number of execution of [p] in the computation of "[Iwhile cond p]".
    Indeed, as the language is deterministic, this number is unique.

    Hence, "[execn n e (Iwhile cond p) e']" means that "[exec e (Iwhile cond p) e']" 
    in a sequence of [n] execution of [p]. 
 *)
Inductive execn: nat -> E.Env -> ImpProg -> E.Env -> Prop :=
 | execn_Iskip:
    forall e, (execn 0 e Iskip e)
 | execn_Iset:
    forall (A:Type) e x (expr: E.Expr A),
     (execn 0 e (Iset x expr) (E.upd x (E.eval expr e) e))
 | execn_Iif:
    forall n e (cond: E.Expr bool) p1 p2 e',
       (execn n e (if (E.eval cond e) then p1 else p2) e')
         -> (execn n e (Iif cond p1 p2) e')
 | execn_Iseq:
    forall n e p1 p2 e' e'',
      (exec e p1 e')
       -> (execn n e' p2 e'')
         -> (execn n e (Iseq p1 p2) e'')
 | execn_Iwhile:
    forall n e cond p e',
     (execn n e (Iif cond (Iseq p (Iwhile cond p)) Iskip) e')
        -> (execn (S n) e (Iwhile cond p) e').

Hint Resolve execn_Iskip execn_Iset execn_Iif execn_Iseq execn_Iwhile: hoare.

Lemma exec_execn: forall ei p ef,
  (exec ei p ef) -> (exists n, execn n ei p ef).
Proof.
  induction 1; firstorder (eauto with hoare).
Qed.


(** In the proof below, I mainly use that "[reduces cond p e1 e0]"
    implies that there exists [n] and [ef] such that "[execn (S n) e0 (Iwhile cond p) ef]"
    and "[execn n e1 (Iwhile cond p) ef]".
*)
Lemma reduces_wf: forall cond p, well_founded (reduces cond p).
Proof.
  unfold well_founded.
  intros cond p e0; apply Acc_intro.
  intros e1 H; unfold reduces in H.
  decompose [ex and] H; clear H.
  clear H2 H0 e0.
  case (exec_execn H1).  
  intros n.
  generalize cond p e1 x; clear cond p e1 x H1.
  elim n.
  (* case 0 *)
  intros cond p e0 e1 H; inversion_clear H.
  (* recursive case *)
  clear n; intros n HR cond p e0 e1 H.
  inversion_clear H.
  inversion_clear H0.
  set (b:=E.eval cond e0) in * |-.
  cut (E.eval cond e0=b); auto.   
  generalize H; clear H; case b; simpl.
  (* case cond=true *)
    intros H; 
    inversion_clear H.
    intros; 
    apply Acc_intro.
    intros e2 H3; unfold reduces in H3.
    intuition.
    rewrite (exec_deterministic H3 H0); eauto.
    (* case cond=false *)
    intros H H0; apply Acc_intro.
    unfold reduces; rewrite H0.
    intuition.
    discriminate.
Qed.
Hint Resolve reduces_wf: hoare.

(** * Completeness

    The proof of completeness proceeds by induction over [prog] syntax.

*)
Lemma wp_complete: forall prog post, prog [= post =] |= (synt_wp prog post).
Proof.
 unfold wp.
  intros prog post e H; case H; clear H.
  intros e' H; case H; clear H.
  generalize post e e'; clear post e e'; elim prog; clear prog; simpl.
  (* - case [Iskip] *)
  intros post e e' H; exec_inversion H; auto.
  (* - case [Iset] *)
  intros A v expr post e e' H; exec_inversion H; auto.
  (* - case [Iif] *)
  intros cond p1 Hp1 p2 Hp2 post e e' H; exec_inversion H.
  case (E.eval cond e); simpl; firstorder auto || discriminate.
  (* - case [Iseq] *)
  intros p1 Hp1 p2 Hp2 post e e' H.
  exec_inversion H.
  eauto.
  (* - case [Iwhile] *)
  intros cond p Hp post e e' H H0.
  constructor 1 with (x:=wp (Iwhile cond p) post).
  constructor 1 with (x:=reduces cond p).
  unfold wp; (intuition eauto with hoare);
    dec2 e1 H1;
    case H1; clear H1; intros H1;
    exec_inversion H1;
    intros e2 H1; exec_inversion H1;
    rewrite H2; intros e3 H1; exec_inversion H1;
    unfold reduces; eauto with hoare.
Qed.

(** * Combining the previous results with transitivity of [ |= ] *)

Hint Resolve wp_complete wp_sound: hoare.

Theorem soundness: forall pre p post, pre |= (synt_wp p post) -> pre |= p [=post=].
Proof.
 auto with hoare.
Qed.

Theorem completeness: forall pre p post, pre |= p [=post=] -> pre |= (synt_wp p post).
Proof.
  intuition auto with hoare.
Qed.


End TotalHoareLogic.

(** "Tutorial on Hoare Logic" Library. Copyright 2007 Sylvain Boulme.

This file is distributed under the terms of the 
 "GNU LESSER GENERAL PUBLIC LICENSE" version 3.  
*)
