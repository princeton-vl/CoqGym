(* QuickChick Prelude *)
Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import String List. Open Scope string.

From QuickChick Require Import QuickChick Tactics.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Import QcDefaultNotation. Open Scope qc_scope.

Set Bullet Behavior "Strict Subproofs".

(* End prelude *)

(** * Smallstep: Small-step Operational Semantics *)

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Maps.
Require Import Imp.

Inductive tm : Type :=
  | C : nat -> tm         (* Constant *)
  | P : tm -> tm -> tm.   (* Plus *)

Derive (Arbitrary, Show) for tm.

Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P a1 a2 => evalF a1 + evalF a2
  end.


Reserved Notation " t '\\' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
      C n \\ n
  | E_Plus : forall t1 t2 n1 n2,
      t1 \\ n1 ->
      t2 \\ n2 ->
      P t1 t2 \\ (n1 + n2)

  where " t '\\' n " := (eval t n).

Module SimpleArith1.

Reserved Notation " t '===>' t' " (at level 55).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) ===> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 ===> t1' ->
      P t1 t2 ===> P t1' t2
  | ST_Plus2 : forall n1 t2 t2',
      t2 ===> t2' ->
      P (C n1) t2 ===> P (C n1) t2'

  where " t '===>' t' " := (step t t').

End SimpleArith1.

Definition relation (X: Type) := X->X->Prop.

Definition deterministic {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Module SimpleArith2.
Import SimpleArith1.

Theorem step_deterministic:
  deterministic step.
Admitted. (* Higher order *) 

End SimpleArith2.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ => 
  match type of T with Prop =>
    solve [ 
      inversion H; 
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.


Module SimpleArith3.
Import SimpleArith1.

Theorem step_deterministic_alt: deterministic step.
Admitted. 

End SimpleArith3.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).

Instance dec_value t : Dec (value t).
constructor; unfold decidable.
destruct t.
- left; constructor; auto.
- right=> contra. inversion contra.
Defined.
Derive ArbitrarySizedSuchThat for (fun t => value t).

Reserved Notation " t '===>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
          P (C n1) (C n2)
      ===> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
        t1 ===> t1' ->
        P t1 t2 ===> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
        value v1 ->                     (* <----- n.b. *)
        t2 ===> t2' ->
        P v1 t2 ===> P v1 t2'

  where " t '===>' t' " := (step t t').

Theorem step_deterministic :
  deterministic step.
Admitted. (* OUT-OF-SCOPE *)

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

Theorem strong_progress : forall t,
  value t \/ (exists t', t ===> t').
Admitted. QuickChick strong_progress. 

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.

Lemma value_is_nf : forall v,
  value v -> normal_form step v.
Admitted. (* QuickChick value_is_nf. *) (* Existential *)

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Admitted. (* OUT-OF-SCOPE *)

(* Temp1,2,3,4 identical *)

Inductive multi {X:Type} (R: relation X) : relation X :=
  | multi_refl  : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Notation " t '===>*' t' " := (multi step t t') (at level 40).

Theorem multi_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> (multi R) x y.
Admitted. (* OUT-OF-SCOPE *)

Theorem multi_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Admitted. (* Existential *)

Definition step_normal_form := normal_form step.

Definition normal_form_of (t t' : tm) :=
  (t ===>* t' /\ step_normal_form t').

(** We have already seen that, for our language, single-step reduction is
    deterministic -- i.e., a given term can take a single step in
    at most one way.  It follows from this that, if [t] can reach
    a normal form, then this normal form is unique.  In other words, we
    can actually pronounce [normal_form t t'] as "[t'] is _the_
    normal form of [t]." *)

Theorem normal_forms_unique:
  deterministic normal_form_of.
Admitted. (* Higher Order *)

Definition normalizing {X:Type} (R:relation X) :=
  forall t, exists t',
    (multi R) t t' /\ normal_form R t'.

Lemma multistep_congr_1 : forall t1 t1' t2,
     t1 ===>* t1' ->
     P t1 t2 ===>* P t1' t2.
Admitted. (* OUT-OF-SCOPE *)

(* TODO: Map rewrite
Inductive aval : aexp -> Prop :=
  | av_num : forall n, aval (ANum n).

Reserved Notation " t '/' st '===>a' t' "
                  (at level 40, st at level 39).

Inductive astep : state -> aexp -> aexp -> Prop :=
  | AS_Id : forall st i,
      AId i / st ===>a ANum (st i)
  | AS_Plus : forall st n1 n2,
      APlus (ANum n1) (ANum n2) / st ===>a ANum (n1 + n2)
  | AS_Plus1 : forall st a1 a1' a2,
      a1 / st ===>a a1' ->
      (APlus a1 a2) / st ===>a (APlus a1' a2)
  | AS_Plus2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st ===>a a2' ->
      (APlus v1 a2) / st ===>a (APlus v1 a2')
  | AS_Minus : forall st n1 n2,
      (AMinus (ANum n1) (ANum n2)) / st ===>a (ANum (minus n1 n2))
  | AS_Minus1 : forall st a1 a1' a2,
      a1 / st ===>a a1' ->
      (AMinus a1 a2) / st ===>a (AMinus a1' a2)
  | AS_Minus2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st ===>a a2' ->
      (AMinus v1 a2) / st ===>a (AMinus v1 a2')
  | AS_Mult : forall st n1 n2,
      (AMult (ANum n1) (ANum n2)) / st ===>a (ANum (mult n1 n2))
  | AS_Mult1 : forall st a1 a1' a2,
      a1 / st ===>a a1' ->
      (AMult a1 a2) / st ===>a (AMult a1' a2)
  | AS_Mult2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st ===>a a2' ->
      (AMult v1 a2) / st ===>a (AMult v1 a2')

    where " t '/' st '===>a' t' " := (astep st t t').

Reserved Notation " t '/' st '===>b' t' "
                  (at level 40, st at level 39).

Inductive bstep : state -> bexp -> bexp -> Prop :=
| BS_Eq : forall st n1 n2,
    (BEq (ANum n1) (ANum n2)) / st ===>b
    (if (beq_nat n1 n2) then BTrue else BFalse)
| BS_Eq1 : forall st a1 a1' a2,
    a1 / st ===>a a1' ->
    (BEq a1 a2) / st ===>b (BEq a1' a2)
| BS_Eq2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st ===>a a2' ->
    (BEq v1 a2) / st ===>b (BEq v1 a2')
| BS_LtEq : forall st n1 n2,
    (BLe (ANum n1) (ANum n2)) / st ===>b
             (if (leb n1 n2) then BTrue else BFalse)
| BS_LtEq1 : forall st a1 a1' a2,
    a1 / st ===>a a1' ->
    (BLe a1 a2) / st ===>b (BLe a1' a2)
| BS_LtEq2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st ===>a a2' ->
    (BLe v1 a2) / st ===>b (BLe v1 a2')
| BS_NotTrue : forall st,
    (BNot BTrue) / st ===>b BFalse
| BS_NotFalse : forall st,
    (BNot BFalse) / st ===>b BTrue
| BS_NotStep : forall st b1 b1',
    b1 / st ===>b b1' ->
    (BNot b1) / st ===>b (BNot b1')
| BS_AndTrueTrue : forall st,
    (BAnd BTrue BTrue) / st ===>b BTrue
| BS_AndTrueFalse : forall st,
    (BAnd BTrue BFalse) / st ===>b BFalse
| BS_AndFalse : forall st b2,
    (BAnd BFalse b2) / st ===>b BFalse
| BS_AndTrueStep : forall st b2 b2',
    b2 / st ===>b b2' ->
    (BAnd BTrue b2) / st ===>b (BAnd BTrue b2')
| BS_AndStep : forall st b1 b1' b2,
    b1 / st ===>b b1' ->
    (BAnd b1 b2) / st ===>b (BAnd b1' b2)

where " t '/' st '===>b' t' " := (bstep st t t').

(** The semantics of commands is the interesting part.  We need two
    small tricks to make it work:

       - We use [SKIP] as a "command value" -- i.e., a command that
         has reached a normal form.

            - An assignment command reduces to [SKIP] (and an updated
              state).

            - The sequencing command waits until its left-hand
              subcommand has reduced to [SKIP], then throws it away so
              that reduction can continue with the right-hand
              subcommand.

       - We reduce a [WHILE] command by transforming it into a
         conditional followed by the same [WHILE]. *)

(** (There are other ways of achieving the effect of the latter
    trick, but they all share the feature that the original [WHILE]
    command needs to be saved somewhere while a single copy of the loop
    body is being reduced.) *)

Reserved Notation " t '/' st '===>' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).

Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep : forall st i a a',
      a / st ===>a a' ->
      (i ::= a) / st ===> (i ::= a') / st
  | CS_Ass : forall st i n,
      (i ::= (ANum n)) / st ===> SKIP / (t_update st i n)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st ===> c1' / st' ->
      (c1 ;; c2) / st ===> (c1' ;; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st ===> c2 / st
  | CS_IfTrue : forall st c1 c2,
      IFB BTrue THEN c1 ELSE c2 FI / st ===> c1 / st
  | CS_IfFalse : forall st c1 c2,
      IFB BFalse THEN c1 ELSE c2 FI / st ===> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
      b / st ===>b b' ->
          IFB b THEN c1 ELSE c2 FI / st 
      ===> (IFB b' THEN c1 ELSE c2 FI) / st
  | CS_While : forall st b c1,
          (WHILE b DO c1 END) / st
      ===> (IFB b THEN (c1;; (WHILE b DO c1 END)) ELSE SKIP FI) / st

  where " t '/' st '===>' t' '/' st' " := (cstep (t,st) (t',st')).

(* ################################################################# *)
(** * Concurrent Imp *)

(** Finally, to show the power of this definitional style, let's
    enrich Imp with a new form of command that runs two subcommands in
    parallel and terminates when both have terminated.  To reflect the
    unpredictability of scheduling, the actions of the subcommands may
    be interleaved in any order, but they share the same memory and
    can communicate by reading and writing the same variables. *)

Module CImp.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  (* New: *)
  | CPar : com -> com -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' b 'THEN' c1 'ELSE' c2 'FI'" :=
  (CIf b c1 c2) (at level 80, right associativity).
Notation "'PAR' c1 'WITH' c2 'END'" :=
  (CPar c1 c2) (at level 80, right associativity).

Inductive cstep : (com * state)  -> (com * state) -> Prop :=
    (* Old part *)
  | CS_AssStep : forall st i a a',
      a / st ===>a a' ->
      (i ::= a) / st ===> (i ::= a') / st
  | CS_Ass : forall st i n,
      (i ::= (ANum n)) / st ===> SKIP / (t_update st i n)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st ===> c1' / st' ->
      (c1 ;; c2) / st ===> (c1' ;; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st ===> c2 / st
  | CS_IfTrue : forall st c1 c2,
      (IFB BTrue THEN c1 ELSE c2 FI) / st ===> c1 / st
  | CS_IfFalse : forall st c1 c2,
      (IFB BFalse THEN c1 ELSE c2 FI) / st ===> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
      b /st ===>b b' ->
          (IFB b THEN c1 ELSE c2 FI) / st 
      ===> (IFB b' THEN c1 ELSE c2 FI) / st
  | CS_While : forall st b c1,
          (WHILE b DO c1 END) / st 
      ===> (IFB b THEN (c1;; (WHILE b DO c1 END)) ELSE SKIP FI) / st
    (* New part: *)
  | CS_Par1 : forall st c1 c1' c2 st',
      c1 / st ===> c1' / st' ->
      (PAR c1 WITH c2 END) / st ===> (PAR c1' WITH c2 END) / st'
  | CS_Par2 : forall st c1 c2 c2' st',
      c2 / st ===> c2' / st' ->
      (PAR c1 WITH c2 END) / st ===> (PAR c1 WITH c2' END) / st'
  | CS_ParDone : forall st,
      (PAR SKIP WITH SKIP END) / st ===> SKIP / st
  where " t '/' st '===>' t' '/' st' " := (cstep (t,st) (t',st')).

Definition cmultistep := multi cstep.

Notation " t '/' st '===>*' t' '/' st' " :=
   (multi cstep  (t,st) (t',st'))
   (at level 40, st at level 39, t' at level 39).


(** Among the many interesting properties of this language is the fact
    that the following program can terminate with the variable [X] set
    to any value. *)

Definition par_loop : com :=
  PAR
    Y ::= ANum 1
  WITH
    WHILE BEq (AId Y) (ANum 0) DO
      X ::= APlus (AId X) (ANum 1)
    END
  END.

(** In particular, it can terminate with [X] set to [0]: *)

Example par_loop_example_0:
  exists st',
       par_loop / empty_state  ===>* SKIP / st'
    /\ st' X = 0.
Proof.
  eapply ex_intro. split.
  unfold par_loop.
  eapply multi_step. apply CS_Par1.
    apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  eapply multi_refl.
  reflexivity. Qed.

(** It can also terminate with [X] set to [2]: *)

Example par_loop_example_2:
  exists st',
       par_loop / empty_state ===>* SKIP / st'
    /\ st' X = 2.
Proof.
  eapply ex_intro. split.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfTrue.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.

  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfTrue.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.

  eapply multi_step. apply CS_Par1. apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  eapply multi_refl.
  reflexivity. Qed.

(** More generally... *)

(** **** Exercise: 3 stars, optional (par_body_n__Sn)  *)
Lemma par_body_n__Sn : forall n st,
  st X = n /\ st Y = 0 ->
  par_loop / st ===>* par_loop / (t_update st X (S n)).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (par_body_n)  *)
Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ===>*  par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** ... the above loop can exit with [X] having any value
    whatsoever. *)

Theorem par_loop_any_X:
  forall n, exists st',
    par_loop / empty_state ===>*  SKIP / st'
    /\ st' X = n.
Proof.
  intros n.
  destruct (par_body_n n empty_state).
    split; unfold t_update; reflexivity.

  rename x into st.
  inversion H as [H' [HX HY]]; clear H.
  exists (t_update st Y 1). split.
  eapply multi_trans with (par_loop,st). apply H'.
  eapply multi_step. apply CS_Par1. apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id. rewrite t_update_eq.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  apply multi_refl.

  rewrite t_update_neq. assumption. intro X; inversion X.
Qed.

End CImp.

(* ################################################################# *)
(** * A Small-Step Stack Machine *)

(** Our last example is a small-step semantics for the stack machine
    example from the [Imp] chapter. *)

Definition stack := list nat.
Definition prog  := list sinstr.

Inductive stack_step : state -> prog * stack -> prog * stack -> Prop :=
  | SS_Push : forall st stk n p',
    stack_step st (SPush n :: p', stk)      (p', n :: stk)
  | SS_Load : forall st stk i p',
    stack_step st (SLoad i :: p', stk)      (p', st i :: stk)
  | SS_Plus : forall st stk n m p',
    stack_step st (SPlus :: p', n::m::stk)  (p', (m+n)::stk)
  | SS_Minus : forall st stk n m p',
    stack_step st (SMinus :: p', n::m::stk) (p', (m-n)::stk)
  | SS_Mult : forall st stk n m p',
    stack_step st (SMult :: p', n::m::stk)  (p', (m*n)::stk).

Theorem stack_step_deterministic : forall st,
  deterministic (stack_step st).
Proof.
  unfold deterministic. intros st x y1 y2 H1 H2.
  induction H1; inversion H2; reflexivity.
Qed.

Definition stack_multistep st := multi (stack_step st).

(** **** Exercise: 3 stars, advanced (compiler_is_correct)  *)
(** Remember the definition of [compile] for [aexp] given in the
    [Imp] chapter. We want now to prove [compile] correct with respect
    to the stack machine.

    State what it means for the compiler to be correct according to
    the stack machine small step semantics and then prove it. *)

Definition compiler_is_correct_statement : Prop 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.


Theorem compiler_is_correct : compiler_is_correct_statement.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** $Date: 2016-12-20 11:28:30 -0500 (Tue, 20 Dec 2016) $ *)

*)
