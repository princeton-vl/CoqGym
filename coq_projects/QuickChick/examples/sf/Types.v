(* QuickChick Prelude *)
Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import String List. Open Scope string.

From QuickChick Require Import QuickChick Tactics.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Import QcDefaultNotation. Open Scope qc_scope.

Set Bullet Behavior "Strict Subproofs".

(* End prelude *)

Require Import Coq.Arith.Arith.
Require Import Maps.
Require Import Imp.
Require Import Smallstep.

Hint Constructors multi.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm
  | tzero : tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tiszero : tm -> tm.

Derive (Arbitrary, Show) for tm.
Derive (Sized, CanonicalSized) for tm.
Derive SizeMonotonic for tm using genStm0.
Derive SizedMonotonic for tm.
Derive SizedCorrect for tm using genStm0 and SizeMonotonictm.

Instance eq_dec_tm (t1 t2 : tm) : Dec (t1 = t2).
constructor; unfold decidable; repeat decide equality. Defined.

Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue ttrue
  | bv_false : bvalue tfalse.

Derive ArbitrarySizedSuchThat for (fun tm => bvalue tm).
Derive SizedProofEqs for (fun tm => bvalue tm).
Derive SizeMonotonicSuchThatOpt for (fun tm => bvalue tm).
Derive GenSizedSuchThatCorrect for (fun tm => bvalue tm).
Derive GenSizedSuchThatSizeMonotonicOpt for (fun tm => bvalue tm).

Instance dec_bvalue t : Dec (bvalue t) :=
  {| dec := _ |}.
induction t; 
try solve [right => contra; inversion contra];
try solve [left; constructor].
Defined.

Inductive nvalue : tm -> Prop :=
  | nv_zero : nvalue tzero
  | nv_succ : forall t, nvalue t -> nvalue (tsucc t).

Instance dec_nvalue t : Dec (nvalue t) :=
  {| dec := _ |}.
induction t; 
try solve[right => contra; inversion contra].
- left; constructor.
- destruct IHt as [L | R]; [left; constructor | right => contra; inversion contra]; eauto.
Defined.

Derive ArbitrarySizedSuchThat for (fun tm => nvalue tm).
Derive SizedProofEqs for (fun tm => nvalue tm).
Derive SizeMonotonicSuchThatOpt for (fun tm => nvalue tm).
Derive GenSizedSuchThatCorrect for (fun tm => nvalue tm).
Derive GenSizedSuchThatSizeMonotonicOpt for (fun tm => nvalue tm).

Definition value (t:tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue.
Hint Unfold value.
Hint Unfold update.

Reserved Notation "t1 '===>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ===> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ===> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ===> t1' ->
      (tif t1 t2 t3) ===> (tif t1' t2 t3)
  | ST_Succ : forall t1 t1',
      t1 ===> t1' ->
      (tsucc t1) ===> (tsucc t1')
  | ST_PredZero :
      (tpred tzero) ===> tzero
  | ST_PredSucc : forall t1,
      nvalue t1 ->
      (tpred (tsucc t1)) ===> t1
  | ST_Pred : forall t1 t1',
      t1 ===> t1' ->
      (tpred t1) ===> (tpred t1')
  | ST_IszeroZero :
      (tiszero tzero) ===> ttrue
  | ST_IszeroSucc : forall t1,
       nvalue t1 ->
      (tiszero (tsucc t1)) ===> tfalse
  | ST_Iszero : forall t1 t1',
      t1 ===> t1' ->
      (tiszero t1) ===> (tiszero t1')

where "t1 '===>' t2" := (step t1 t2).

Hint Constructors step.

Derive ArbitrarySizedSuchThat for (fun tm => step tm0 tm).
Derive SizeMonotonicSuchThatOpt for (fun tm => step tm0 tm).
Derive GenSizedSuchThatSizeMonotonicOpt for (fun tm => step tm0 tm).

(* QuickChickDebug Debug On. *)
Derive SizedProofEqs for (fun tm => step tm0 tm).
(* Zoe: SizedProofEqs -- works but takes forever *)
Derive GenSizedSuchThatCorrect for (fun tm => step tm0 tm).

Definition success := "Proofs work!".
Print success.

Instance step_gen_correct t0 : SuchThatCorrect (fun t => step t0 t)
                                                  (@arbitraryST _ (fun t => step t0 t) _).
Admitted.

Notation step_normal_form := (normal_form step).

Definition stuck (t:tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck.

(* xistential rework - dummy step *)
Definition step_fun (t : tm) : option tm := Some t.

Axiom step_fun_correct : forall t t',
    step_fun t = Some t' <-> step t t'.

Instance dec_step (t : tm) : Dec (exists t', step t t') :=
  {| dec := _ |}.
Proof.
  destruct (step_fun t) eqn:Step.
  - left; exists t0; eapply step_fun_correct; eauto.
  - right => [[t' contra]]. eapply step_fun_correct in contra; congruence.
Defined.

Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Admitted. (* QuickCheck value_is_nf. (* Existential *) *)

Theorem step_deterministic:
  deterministic step.
Admitted. (* QuickChick step_deterministic. *)

Inductive typ : Type :=
  | TBool : typ
  | TNat : typ.

Derive (Arbitrary, Show) for typ.
Derive (Sized, CanonicalSized) for typ.
Derive SizeMonotonic for typ using genStyp.
Derive SizedMonotonic for typ.
Derive SizedCorrect for typ using genStyp and SizeMonotonictyp.

Reserved Notation "'|-' t '\typ' T" (at level 40).

Inductive has_type : tm -> typ -> Prop :=
  | T_True :
       |- ttrue \typ TBool
  | T_False :
       |- tfalse \typ TBool
  | T_If : forall t1 t2 t3 T,
       |- t1 \typ TBool ->
       |- t2 \typ T ->
       |- t3 \typ T ->
       |- tif t1 t2 t3 \typ T
  | T_Zero :
       |- tzero \typ TNat
  | T_Succ : forall t1,
       |- t1 \typ TNat ->
       |- tsucc t1 \typ TNat
  | T_Pred : forall t1,
       |- t1 \typ TNat ->
       |- tpred t1 \typ TNat
  | T_Iszero : forall t1,
       |- t1 \typ TNat ->
       |- tiszero t1 \typ TBool

where "'|-' t '\typ' T" := (has_type t T).

Hint Constructors has_type.

Derive ArbitrarySizedSuchThat for (fun t => has_type t T).
Derive SizeMonotonicSuchThatOpt for (fun t => has_type t T).
Derive GenSizedSuchThatSizeMonotonicOpt for (fun t => has_type t T).
(* KNOWN DUG. The derivation of SizedProofEqs for has_type fails with type error. *)
(* Probably needs a type annotation somewhere to convince the typechecker *)
(* Derive SizedProofEqs for (fun t => has_type t T).
Derive GenSizedSuchThatCorrect for (fun t => has_type t T).
*)
(* Admitting such that the following work *)
Instance has_type_gen_correct T : SuchThatCorrect (fun t => has_type t T)
                                                  (@arbitraryST _ (fun t => has_type t T) _).
Admitted.

Instance dec_has_type (t : tm) (T : typ) : Dec (has_type t T).
constructor; unfold decidable.
move: T; induction t => T; destruct T; eauto;
try solve [right => contra; inversion contra; eauto].
- destruct (IHt1 TBool). 
  + destruct (IHt2 TBool); destruct (IHt3 TBool); eauto;
      right => contra; inversion contra; eauto.
  + right => contra; inversion contra; eauto.
- destruct (IHt1 TBool). 
  + destruct (IHt2 TNat); destruct (IHt3 TNat); eauto;
      right => contra; inversion contra; eauto.
  + right => contra; inversion contra; eauto.
- destruct (IHt TNat); eauto.
  right => contra; inversion contra; eauto.
- destruct (IHt TNat); eauto.
  right => contra; inversion contra; eauto.
- destruct (IHt TNat); eauto.
  right => contra; inversion contra; eauto.
Defined.

Lemma bool_canonical : forall t,
  |- t \typ TBool -> value t -> bvalue t.
Admitted. (* QuickChick bool_canonical. *)

Lemma nat_canonical : forall t,
  |- t \typ TNat -> value t -> nvalue t.
Admitted. (* QuickChick nat_canonical. *)

Theorem progress : forall t T,
  |- t \typ T ->
  value t \/ exists t', t ===> t'.
Admitted. (* QuickChick progress. (* Existential *) *)

Global Instance testSuchThat_swap' {A B C : Type} {pre : A -> C -> Prop} 
       {prop : A -> B -> C -> Type}
       `{Checkable (forall a c, pre a c -> forall b, prop a b c)} :
  Checkable (forall a b c, pre a c -> prop a b c) :=
  {| checker f := @checker (forall a c, pre a c -> forall b, prop a b c) _ _ |}. 
Proof. intros; eauto. Defined.

Conjecture preservation : forall t t' T,
  |- t \typ T -> t ===> t' ->
  |- t' \typ T.
(* QuickChick preservation. *)
(* 
QuickChecking preservation
+++ Passed 10000 tests
*)

Definition multistep := (multi step).
Notation "t1 '===>*' t2" := (multistep t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  |- t \typ T ->
  t ===>* t' ->
  ~(stuck t').
Admitted. (* OUT-OF-SCOPE *) (* Existential *)

Tactic Notation "print_goal" :=
  match goal with |- ?x => idtac x end.
Tactic Notation "normalize" :=
  repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | (instantiate; simpl)]);
  apply multi_refl.
