Require Import Coq.ZArith.ZArith.

Section Imp.

Context {Var: Type}.

Definition stack := Var -> Z.
Definition heap := Z -> option Z.
Definition state: Type := stack * heap.

Definition update_stack (st : stack) (x : Var) (n : Z) (st': stack): Prop :=
  st' x = n /\
  (forall x0, x0 <> x -> st x0 = st' x0).

Definition update_heap (st : heap) (x : Z) (n : option Z) (st': heap): Prop :=
  st' x = n /\
  (forall x0, x0 <> x -> st x0 = st' x0).

Inductive aexp : Type :=
  | AVar : Var -> aexp
  | ANum : Z -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (st : stack) (a : aexp) : Z :=
  match a with
  | AVar x => st x
  | ANum n => n
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : stack) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => Zeq_bool (aeval st a1) (aeval st a2)
  | BLe a1 a2   => Zle_bool (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Inductive cmd : Type :=
  | CSkip : cmd
  | CSet : Var -> aexp -> cmd
  | CLoad : Var -> Var -> cmd
  | CStore : Var -> Var -> cmd
  | CSeq : cmd -> cmd -> cmd
  | CIf : bexp -> cmd -> cmd -> cmd
  | CWhile : bexp -> cmd -> cmd.

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CSet x a) (at level 60).
Notation "x '::=' '<<' y '>>'" :=
  (CLoad x y) (at level 58).
Notation "'<<' x '>>' '::=' y" :=
  (CStore x y) (at level 58).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

Reserved Notation " t '/' st '==>' t' '/' st' " 
                  (at level 40, st at level 39, t' at level 39).

Inductive cstep : (cmd * state) -> (cmd * state) -> Prop :=
  | CS_Set : forall st st' i n a,
      aeval (fst st) a = n ->
      update_stack (fst st) i n (fst st') ->
      snd st = snd st' ->
      (i ::= a) / st ==> SKIP / st'
  | CS_Load : forall (st st': state) i x n,
      snd st (fst st x) = Some n ->
      update_stack (fst st) i n (fst st') ->
      snd st = snd st' ->
      (i ::= << x >>) / st ==> SKIP / st'
  | CS_Store : forall (st st': state) i x n,
      snd st (fst st x) = Some n ->
      update_heap (snd st) (fst st x) (Some (fst st i)) (snd st') ->
      fst st = fst st' ->
      (CStore x i) / st ==> SKIP / st'
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st ==> c1' / st' ->
      (c1 ;; c2) / st ==> (c1' ;; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st ==> c2 / st
  | CS_IfTrue : forall st b c1 c2,
      beval (fst st) b = true ->
      IFB b THEN c1 ELSE c2 FI / st ==> c1 / st
  | CS_IfFalse : forall st b c1 c2,
      beval (fst st) b = false ->
      IFB b THEN c1 ELSE c2 FI / st ==> c2 / st
  | CS_WhileTrue : forall st b c1,
      beval (fst st) b = true ->
      (WHILE b DO c1 END) / st ==> (c1;; (WHILE b DO c1 END)) / st
  | CS_WhileFalse : forall st b c1,
      beval (fst st) b = false ->
      (WHILE b DO c1 END) / st ==> SKIP / st

  where " t '/' st '==>' t' '/' st' " := (cstep (t,st) (t',st')).
