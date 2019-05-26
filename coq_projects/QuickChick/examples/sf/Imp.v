(* QuickChick Prelude *)
Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import String List. Open Scope string.

From QuickChick Require Import QuickChick Tactics.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Import QcDefaultNotation. Open Scope qc_scope.

Set Bullet Behavior "Strict Subproofs".

(* End prelude *)

(* IMPORTS *)
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.

(* LEO: Update Map *)
Require Import Maps.
(* /IMPORTS *)

Module AExp.

Inductive aexp' : Type :=
  | ANum : nat -> aexp'
  | APlus : aexp' -> aexp' -> aexp'
  | AMinus : aexp' -> aexp' -> aexp'
  | AMult : aexp' -> aexp' -> aexp'.

Derive (Arbitrary, Show) for aexp'.
Derive (Sized, CanonicalSized) for aexp'.
Derive SizeMonotonic for aexp' using genSaexp'.
Derive SizedMonotonic for aexp'.
Derive SizedCorrect for aexp' using genSaexp' and SizeMonotonicaexp'.

Instance dec_eq_aex (x y : aexp') : Dec (x = y).
constructor; unfold decidable; repeat decide equality. Defined.

(* AEC Reviewer example *)
Inductive aexpEq : aexp' -> aexp' -> Prop := 
 | ANumEq : forall n1 n2, n1 = n2 -> aexpEq (ANum n1) (ANum n2).

Instance dec_aexpEq (x y : aexp') : Dec (aexpEq x y).
constructor; unfold decidable. destruct x; destruct y;
try solve [right => H; inversion H; eauto].
destruct ((n = n0)?) eqn:Eq; destruct dec; try solve [inversion Eq].
- left; econstructor; eauto. 
- right => H; inversion H; eauto.
Defined. 

Conjecture aexpEq_refl : forall x, aexpEq x x.
QuickChick aexpEq_refl.

Derive ArbitrarySizedSuchThat for (fun x => aexpEq x x').
Derive SizedProofEqs for (fun x => aexpEq x x').
Derive SizeMonotonicSuchThatOpt for (fun x => aexpEq x x').
Derive GenSizedSuchThatSizeMonotonicOpt for (fun x => aexpEq x x').
Derive GenSizedSuchThatCorrect for (fun x => aexpEq x x').

Conjecture aexpEq_eq : forall x x', aexpEq x x' -> x = x'.
QuickChick aexpEq_eq.
(* End Reviwer example *)

Inductive bexp' : Type :=
  | BTrue : bexp'
  | BFalse : bexp'
  | BEq : aexp' -> aexp' -> bexp'
  | BLe : aexp' -> aexp' -> bexp'
  | BNot : bexp' -> bexp'
  | BAnd : bexp' -> bexp' -> bexp'.

Derive (Arbitrary, Show) for bexp'.
Derive (Sized, CanonicalSized) for bexp'.
Derive SizeMonotonic for bexp' using genSbexp'.
Derive SizedMonotonic for bexp'.
Derive SizedCorrect for bexp' using genSbexp' and SizeMonotonicbexp'.

Instance dec_eq_bexp (x y : bexp') : Dec (x = y).
constructor; unfold decidable; repeat decide equality. Defined.

Fixpoint aeval (a : aexp') : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2  => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Fixpoint beval (b : bexp') : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval a1) (aeval a2)
  | BLe a1 a2   => leb (aeval a1) (aeval a2)
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.

Fixpoint optimize_0plus (a:aexp') : aexp' :=
  match a with
  | ANum n =>
      ANum n
  | APlus (ANum 0) e2 =>
      optimize_0plus e2
  | APlus e1 e2 =>
      APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 =>
      AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 =>
      AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

End AExp.

Import AExp.

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Admitted. (* QuickChick optimize_0plus_sound. *)

Theorem silly1 : forall ae, aeval ae = aeval ae.
Admitted. (* QuickChick silly1. *)

Theorem silly2 : forall (P : Prop), P -> P.
Admitted. (* Higher order *)

Lemma foo : forall n, leb 0 n = true.
Admitted. (* QuickChick foo. *)


Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

Module aevalR_first_try.

Inductive aevalR : aexp' -> nat -> Prop :=
  | E_ANum  : forall (n: nat),
      aevalR (ANum n) n
  | E_APlus : forall (e1 e2: aexp') (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus: forall (e1 e2: aexp') (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult : forall (e1 e2: aexp') (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

Notation "e '\\' n"
         := (aevalR e n)
            (at level 50, left associativity)
         : type_scope.

End aevalR_first_try.

(** In fact, Coq provides a way to use this notation in the
    definition of [aevalR] itself.  This reduces confusion by avoiding
    situations where we're working on a proof involving statements in
    the form [e \\ n] but we have to refer back to a definition
    written using the form [aevalR e n].

    We do this by first "reserving" the notation, then giving the
    definition together with a declaration of what the notation
    means. *)

Module AExpR.
Reserved Notation "e '\\' n" (at level 50, left associativity).

Inductive aevalR : aexp' -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) \\ n
  | E_APlus : forall (e1 e2: aexp') (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus : forall (e1 e2: aexp') (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult :  forall (e1 e2: aexp') (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)

  where "e '\\' n" := (aevalR e n) : type_scope.

Theorem aeval_iff_aevalR : forall a n,
  (a \\ n) <-> aeval a = n.
Admitted. (* OUT-OF-SCOPE ? *)
End AExpR.

Definition state := total_map.

Definition empty_state : state := t_empty 0.

(* Zoe: Changing the name of this to aexp because the name clash breaks derivation*)
(* TODO: Fix the above at some point *)
Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp               (* <----- NEW *)
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Definition W : id := Id "W".
Definition X : id := Id "X".
Definition Y : id := Id "Y".
Definition Z : id := Id "Z".
(* For better testing *)
(* Instance gid : Gen id := {| arbitrary := elems [W; X; Y; Z] |}. *)

Derive (Arbitrary, Show) for aexp.
Derive (Sized, CanonicalSized) for aexp.
Derive SizedMonotonic for aexp.
Derive SizeMonotonic for aexp using genSaexp.
Derive SizedCorrect for aexp using genSaexp and SizeMonotonicaexp.

Instance dec_eq_aex (x y : aexp) : Dec (x = y).
constructor; unfold decidable; repeat decide equality. Defined.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Derive (Arbitrary, Show) for bexp.
Derive (Sized, CanonicalSized) for bexp.
Derive SizeMonotonic for bexp using genSbexp.
Derive SizedMonotonic for bexp.
Derive SizedCorrect for bexp using genSbexp and SizeMonotonicbexp.

Instance dec_eq_bexp (x y : bexp) : Dec (x = y).
constructor; unfold decidable; repeat decide equality. Defined.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => t_lookup st x                                (* <----- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2   => leb (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Derive (Arbitrary, Show) for com.
Derive (Sized, CanonicalSized) for com.
Derive SizeMonotonic for com using genScom.
Derive SizedMonotonic for com.
Derive SizedCorrect for com using genScom and SizeMonotoniccom.

Instance dec_eq_com (x y : com) : Dec (x = y).
constructor; unfold decidable; repeat decide equality. Defined.

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

Definition fact_in_coq : com :=
  Z ::= AId X;;
  Y ::= ANum 1;;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId Z);;
    Z ::= AMinus (AId Z) (ANum 1)
  END.

Definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2)).

Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y)).

Definition subtract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1) ;;
  X ::= AMinus (AId X) (ANum 1).

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    subtract_slowly_body
  END.

Definition subtract_3_from_5_slowly : com :=
  X ::= ANum 3 ;;
  Z ::= ANum 5 ;;
  subtract_slowly.

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.

Reserved Notation "c1 '/' st '\\' st'"
                  (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st \\ st
  | E_Ass  : forall st m d a1 n x,
      aeval st a1 = n ->
      st = (m, d) ->
      (x ::= a1) / st \\ (((x,n) :: m), d)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  \\ st' ->
      c2 / st' \\ st'' ->
      (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      c1 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      c2 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileEnd : forall b st c,
      beval st b = false ->
      (WHILE b DO c END) / st \\ st
  | E_WhileLoop : forall st st' st'' b c,
      beval st b = true ->
      c / st \\ st' ->
      (WHILE b DO c END) / st' \\ st'' ->
      (WHILE b DO c END) / st \\ st''

  where "c1 '/' st '\\' st'" := (ceval c1 st st').

Theorem ceval_deterministic: forall c st st1 st2,
     c / st \\ st1  ->
     c / st \\ st2 ->
     st1 = st2.
Admitted. (* OUT-OF-SCOPE *)

Theorem loop_never_stops : forall st st',
  ~(loop / st \\ st').
Admitted. (* Gave Up *)

Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : id -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.

