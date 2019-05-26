(** * Semantics of my Hoare Logic

 This file is part of the "Tutorial on Hoare Logic". 
 For an introduction to this Coq library, 
 see README #or <a href=index.html>index.html</a>#.
 
*)

Set Implicit Arguments.

(** * Expression Language 

  My Hoare logic is parametrized by the expression language. 
  The language is here assumed to have global variables. 
  Furthermore, expressions are purely functional (they terminates 
  and have no side effects). However, expressions and variables are 
  strongly-typed. Here, this typing is directly performed by Coq.
  - "[Var A]" is the type of variables storing values of type [A]
  - "[Expr A]" is the type of expressions return values of type [A]
  - [Env] is the type of environment. An environment is a mapping from variables into values.
  - "[upd x v e]" sets [v] as the new value of [x] from environment [e]
  - [eval] evaluates an expression in a given environment.

  See the file #<a href="exgcd.html">#[exgcd]#</a># to get a simple example
  of how such a language can be instantiated.  
*)

Module Type ExprLang.

  Parameter Var: Type -> Type. 
  Parameter Expr: Type -> Type. 
  Parameter Env: Type.

  Parameter upd: forall (A:Type), (Var A) -> A -> Env -> Env.
  Parameter eval: forall (A:Type), (Expr A) -> Env -> A.

End  ExprLang.

(** * Definitions of my Hoare logic *)
Module Type HoareLogicDefs.

Declare Module E: ExprLang.

(** ** The programming language: syntax and semantics *)

(** Abstract syntax of the imperative programming language 
    - [Iskip] is an instruction to "do nothing" 
    - "[Iset x expr]" stores in [x] the result of [expr] 
    - [Iif] represents conditional branching
    - [Iseq] represents the sequence of two instructions
    - [Iwhile] represents the while-loop

  This semantics is formalizes by [exec] predicate below.   
*)  
Inductive ImpProg: Type := 
  | Iskip: ImpProg
  | Iset (A:Type) (x:E.Var A) (expr:E.Expr A): ImpProg
  | Iif (cond:E.Expr bool) (p1 p2:ImpProg): ImpProg
  | Iseq (p1 p2:ImpProg): ImpProg
  | Iwhile (cond:E.Expr bool) (p:ImpProg): ImpProg.

(** The semantics of the programming language is given by the following natural semantics.
  Here "[exec e0 p e1]" means that "in the initial environment [e0] the execution of [p] 
  terminates in the final environment [e1]".
*) 
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

(** This language is thus deterministic. 
   This is proved by lemma [exec_deterministic] in file 
   #<a href="totalhoarelogic.html">#[totalhoarelogic]#</a>#. 
*)

(** ** The specification language: syntax and semantics 

  If [prog] is a program, [pre] a precondition (i.e. a required
  property on the initial environment) and [post] a postcondition
  (i.e. a property on the final environment that [prog] must ensure
  when [pre] is initially satisfied), then a specification in Hoare
  logic is written:
   - "[pre |= prog {= post =}]" in partial correctness (i.e. even if
    [pre] is satisfied, [prog] may not terminate)
   - "[pre |= prog [= post =]]" in total correctness (i.e. when [pre]
     is satisfied, [prog] must terminate).

  Below, we give the semantics of these notations. Here the assertion
  language is shallow embedded (there is no syntax for it: we use
  directly the Coq proposition language).

  [Pred] is the type of assertions. 
*)
Definition Pred := E.Env -> Prop.

(** Deduction operator "|=" is here only a syntactic sugar. 
    In the following, [p |= q] can also be read "[q] is weaker than [p]". 
*)
Notation "p |= q" := (forall e, (p e) -> (q e)) (at level 80, no associativity).

(** [wlp] represents the Weakest Liberal Precondition (i.e. 
  "[wlp prog post]" is the weakest condition on the initial environment ensuring
  that [post] is ensured on any final environment of [prog], when such environment
  exists) 
*)
Definition wlp: ImpProg -> Pred -> Pred
 := fun prog post e => (forall e', (exec e prog e') -> (post e')).

Notation "p {= post =}" := (wlp p post) (at level 70).

(** [wp] represents the Weakest Precondition (i.e. "[wp prog post]" is
  the weakest condition on the initial environment ensuring that there
  exists a final environment of [prog] satisfying [post]). Here as the language is
  deterministic, I proved that "[(wp prog post) |= (wlp prog post)]" 
  see lemma [wp_entails_wlp] below.
*)
Definition wp: ImpProg -> Pred -> Pred
 := fun prog post e => exists e', (exec e prog e') /\ (post e').

Notation "p [= post =]" := (wp p post) (at level 70).


(** ** A useful base of hints
 
  These hints are used in the metatheoritical proofs of the logic.
*)

Hint Resolve exec_Iskip exec_Iset exec_Iif exec_Iseq exec_Iwhile: hoare.

Parameter exec_Iif_true:
  forall e cond p1 p2 e', 
     (E.eval cond e)=true
       -> (exec e p1 e') 
         -> (exec e (Iif cond p1 p2) e').

Parameter exec_Iif_false:
  forall e cond p1 p2 e', 
     (E.eval cond e)=false
      -> (exec e p2 e') 
         -> (exec e (Iif cond p1 p2) e').


Hint Resolve exec_Iif_true exec_Iif_false: hoare.

End HoareLogicDefs.


(** * Generation of proof obligations (POs)

Given [sem_wp] one of the two preceding notion of
weakest-precondition, the generation of proof obligations is a
function [synt_wp] logically equivalent to [sem_wp], which proceeds
recursively on the abstract syntax of the program. Hence, 
"[synt_wp prog post]" is an assertion which does not involve [exec]. 

In practice, the PO generation is run by invoking the [soundness] lemma.
The [completeness] lemma is only ensuring that if the generated PO
seems hard to prove, this is not due to a bug in [synt_wp]
implementation.

*)

Module Type HoareProofSystem.

Declare Module HLD: HoareLogicDefs.

Import HLD.

Parameter sem_wp: ImpProg -> Pred -> Pred.
Parameter synt_wp: ImpProg -> Pred -> Pred.

Parameter soundness: forall pre p post, pre |= (synt_wp p post) -> pre |= (sem_wp p post).
Parameter completeness: forall pre p post, pre |= (sem_wp p post) -> pre |= (synt_wp p post).

End HoareProofSystem.


(** * The whole meta-theory
The whole meta-theory is described by this module signature. This signature is implemented in file #<a href="hoarelogic.html">#[hoarelogic]#</a>#.

  See the file #<a href="exgcd.html">#[exgcd]#</a># to get a simple example
  of how the "proof obligation generation" is used.  
  - module [PHL] contains the PO generation in partial correctness.
  - module [THL] contains the PO generation in total correctness.
*)

Module Type HoareLogicSem.

Declare Module E: ExprLang.

Declare Module HLD: HoareLogicDefs with Module E:=E.
Import HLD.

Declare Module PHL: HoareProofSystem with Module HLD:=HLD with Definition sem_wp:=wlp.
Declare Module THL: HoareProofSystem with Module HLD:=HLD with Definition sem_wp:=wp.

Parameter wp_entails_wlp: forall prog post, prog [= post =] |= prog {= post =}.

End HoareLogicSem. 

(** "Tutorial on Hoare Logic" Library. Copyright 2007 Sylvain Boulme.

This file is distributed under the terms of the 
 "GNU LESSER GENERAL PUBLIC LICENSE" version 3.  
*)
