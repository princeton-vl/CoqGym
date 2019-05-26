(** * Generation of Hoare proof obligations in partial correctness

 This file is part of the "Tutorial on Hoare Logic".
 For an introduction to this Coq library,
 see README #or <a href=index.html>index.html</a>#.

 This file gives a syntactic definition of the weakest liberal precondition [wlp]
 introduced in #<a href=hoarelogicsemantics.html>#[hoarelogicsemantics]#</a>#.
*)

Global Set Asymmetric Patterns.
Set Implicit Arguments.
Require Export hoarelogicsemantics.

Module PartialHoareLogic (HD: HoareLogicDefs).

Export HD.
Module HLD:=HD.

Definition sem_wp := wlp.

(** * Syntactic definition of the weakest liberal precondition.

 In the following, we show that this definition is logically 
 equivalent to [wlp].
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
             (inv e)
          /\ (forall e', (inv e') 
                  -> (E.eval cond e')=false -> (post e'))
          /\ (forall e', (inv e') 
                  -> (E.eval cond e')=true -> (synt_wp p inv e'))
  end.

(** This property is also trivially satisfied by [wlp]. 
    We need it here to prove the soundness.
*)
Lemma synt_wp_monotonic: 
  forall (p: ImpProg) (post1 post2: Pred),
   (post1 |= post2) -> (synt_wp p post1) |= (synt_wp p post2).
Proof.
  induction p; simpl; firstorder eauto with hoare.
Qed.

Hint Resolve synt_wp_monotonic: hoare.

(** * Soundness
  
    The proof of soundness proceeds by induction over the derivation
    [exec ... prog ...] in implicit hypothesis induced by [wlp] definition.

    Please, notice that coq performs the [exec_Iwhile] case alone (that's where 
    monotonicity is used). Unfortunately, the case [exec_Iif] which seems
    trivial to a human is not discharged by Coq.
*)
Lemma wp_sound: forall prog post, synt_wp prog post |= prog{=post=}.
Proof.
 intros prog post e H0 e' H; generalize post H0; clear H0 post.
 elim H; clear H e' e prog; simpl; try ((firstorder eauto 20 with hoare); fail).
 (** - case [exec_Iif] *)
 intros e cond p1 p2 e'.
 case (E.eval cond e); simpl; firstorder auto.
Qed.

(** * Completeness
 
    The proof of completeness proceeds by induction over [prog] syntax.

    Please, notice that coq performs this proof almost alone. The only
    hint given here is the invariant.
*)
Lemma wp_complete: forall prog post, prog{=post=} |= (synt_wp prog post).
Proof.
 unfold wlp; intros prog; elim prog; clear prog; simpl;
 try ((firstorder auto with hoare); fail).
 (** - case [Iseq] *)
 eauto with hoare.
 (** - case [Iwhile]: I provide the invariant below *)
  intros.
  constructor 1 with (x:=wlp (Iwhile cond p) post).
  unfold wlp; intuition eauto 20 with hoare.
Qed.

(** * Combining the previous results with transitivity of [ |= ] *)

Hint Resolve wp_complete wp_sound: hoare.

Theorem soundness: forall pre p post, pre |= (synt_wp p post) -> pre |= p {=post=}.
Proof.
 auto with hoare.
Qed.

Theorem completeness: forall pre p post, pre |= p {=post=} -> pre |= (synt_wp p post).
Proof.
  intuition auto with hoare.
Qed.


End PartialHoareLogic.

(** "Tutorial on Hoare Logic" Library. Copyright 2007 Sylvain Boulme.

This file is distributed under the terms of the 
 "GNU LESSER GENERAL PUBLIC LICENSE" version 3.  
*)
