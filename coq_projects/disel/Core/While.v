From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl
Require Import pred prelude ordtype finmap pcm unionmap heap.
From DiSeL
Require Import Freshness State EqTypeX DepMaps Protocols Worlds NetworkSem Rely.
From DiSeL
Require Import Actions Injection Process Always HoareTriples InferenceRules.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section While.
Variable this : nid.
Variable W : world.

Variable A B : Type.
Variable cond : B -> bool.
Variable I : A -> cont B.
Variable I_stable : forall a b s0 s1, I a b s0 -> network_rely W this s0 s1 -> I a b s1.

Notation body_spec' :=
  (fun b a => binarify (fun s => cond b /\ I a b s) (fun b' s1 => I a b' s1)).

Notation body_spec := (forall b : B, DTbin this W (logvar (body_spec' b))).

Variable body : body_spec.

Definition loop_spec := forall b, 
  {a : A}, DHT [this, W]
  (fun s => I a b s, fun b' s1 => ~~ cond b' /\ I a b' s1).

Program Definition while b0 : 
  {a : A}, DHT [this, W]
  (fun s => I a b0 s,
   fun b' s1 => ~~ cond b' /\ I a b' s1) :=
  Do (ffix (fun (rec : loop_spec) (b : B) =>
              Do (if cond b
                  then (b' <-- body b;
                       rec b')
                  else ret _ _ b)) b0).
Next Obligation.
apply: ghC=>s0 a/= HI0 C.
case: ifP=> Hcond; last by apply: ret_rule=>s1 R1; split;[rewrite Hcond | eauto].
apply: step.
apply: call_rule'; first by move=> _; exists a. 
move=> b' s1 HI1 C1.
apply: (gh_ex (g:=a)).
apply: call_rule'; first by move=>_; apply: HI1. 
by move=>x m; case=>//; apply: HI1. 
Qed.

Next Obligation.
move => s0/= HI0.
by apply: call_rule'.
Qed.

End While.
