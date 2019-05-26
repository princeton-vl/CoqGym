(* This file contains a definition of a simple imperative programming
   language together with its operational semantics. Most definitions
   and lemma statements were translated into Coq from Isabelle/HOL
   statements present in the book:

   T. Nipkow, G. Klein, Concrete Semantics with Isabelle/HOL.

   This gives a rough idea of how the automation provided by "hammer"
   and our reconstruction tactics compares to the automation available
   in Isabelle/HOL. *)

From Hammer Require Import Hammer Reconstr.

Require Import String.
Require Import Arith.PeanoNat.
Require Import Bool.Bool.

Inductive aexpr :=
| Nval : nat -> aexpr
| Vval : string -> aexpr
| Aplus : aexpr -> aexpr -> aexpr.

Definition state := string -> nat.

Fixpoint aval (s : state) (e : aexpr) :=
  match e with
  | Nval n => n
  | Vval x => s x
  | Aplus x y => aval s x + aval s y
  end.

Fixpoint plus (e1 e2 : aexpr) :=
  match e1, e2 with
  | Nval n1, Nval n2 => Nval (n1 + n2)
  | Nval 0, _ => e2
  | _, Nval 0 => e1
  | _, _ => Aplus e1 e2
  end.

Lemma lem_aval_plus : forall s e1 e2, aval s (plus e1 e2) = aval s e1 + aval s e2.
Proof.
  induction e1; sauto.
Qed.

Fixpoint asimp (e : aexpr) :=
  match e with
  | Aplus x y => plus (asimp x) (asimp y)
  | _ => e
  end.

Lemma lem_aval_asimp : forall s e, aval s (asimp e) = aval s e.
Proof.
  induction e; sauto.
  Reconstr.reasy (@lem_aval_plus) Reconstr.Empty.
Qed.

Inductive bexpr :=
| Bval : bool -> bexpr
| Bnot : bexpr -> bexpr
| Band : bexpr -> bexpr -> bexpr
| Bless : aexpr -> aexpr -> bexpr.

Fixpoint bval (s : state) (e : bexpr) :=
  match e with
  | Bval b => b
  | Bnot e1 => negb (bval s e1)
  | Band e1 e2 => bval s e1 && bval s e2
  | Bless a1 a2 => aval s a1 <? aval s a2
  end.

Fixpoint not (e : bexpr) :=
  match e with
  | Bval true => Bval false
  | Bval false => Bval true
  | _ => Bnot e
  end.

Fixpoint and (e1 e2 : bexpr) :=
  match e1, e2 with
  | Bval true, _ => e2
  | _, Bval true => e1
  | Bval false, _ => Bval false
  | _, Bval false => Bval false
  | _, _ => Band e1 e2
  end.

Definition less (a1 a2 : aexpr) :=
  match a1, a2 with
  | Nval n1, Nval n2 => Bval (n1 <? n2)
  | _, _ => Bless a1 a2
  end.

Fixpoint bsimp (e : bexpr) :=
  match e with
  | Bnot e1 => not (bsimp e1)
  | Band e1 e2 => and (bsimp e1) (bsimp e2)
  | Bless a1 a2 => less a1 a2
  | _ => e
  end.

Lemma lem_bval_not : forall s e, bval s (not e) = negb (bval s e).
Proof.
  induction e; sauto.
Qed.

Lemma lem_bval_and : forall s e1 e2, bval s (and e1 e2) = bval s e1 && bval s e2.
Proof.
  induction e1; sauto.
Qed.

Lemma lem_bval_less : forall s a1 a2, bval s (less a1 a2) = (aval s a1 <? aval s a2).
Proof.
  induction a1; sauto.
Qed.

Lemma lem_bval_bsimp : forall s e, bval s (bsimp e) = bval s e.
Proof.
  induction e; sauto.
  - Reconstr.reasy (@lem_bval_not) Reconstr.Empty.
  - Reconstr.reasy (@lem_bval_and) Reconstr.Empty.
  - ycrush.
  - ycrush.
Qed.

Inductive cmd :=
| Skip : cmd
| Assign : string -> aexpr -> cmd
| Seq : cmd -> cmd -> cmd
| If : bexpr -> cmd -> cmd -> cmd
| While : bexpr -> cmd -> cmd.

Definition update (s : state) x v y := if string_dec x y then v else s y.

Inductive big_step : cmd * state -> state -> Prop :=
| SkipSem : forall s, big_step (Skip, s) s
| AssignSem : forall s x a, big_step (Assign x a, s) (update s x (aval s a))
| SeqSem : forall c1 c2 s1 s2 s3, big_step (c1, s1) s2 -> big_step (c2, s2) s3 ->
                                  big_step (Seq c1 c2, s1) s3
| IfTrue : forall b c1 c2 s s', bval s b = true -> big_step (c1, s) s' ->
                                big_step (If b c1 c2, s) s'
| IfFalse : forall b c1 c2 s s', bval s b = false -> big_step (c2, s) s' ->
                                 big_step (If b c1 c2, s) s'
| WhileFalse : forall b c s, bval s b = false ->
                             big_step (While b c, s) s
| WhileTrue : forall b c s1 s2 s3,
    bval s1 b = true -> big_step (c, s1) s2 -> big_step (While b c, s2) s3 ->
    big_step (While b c, s1) s3.

Notation "A ==> B" := (big_step A B) (at level 80, no associativity).

Lemma lem_seq_assoc : forall c1 c2 c3 s s', (Seq c1 (Seq c2 c3), s) ==> s' <->
                                            (Seq (Seq c1 c2) c3, s) ==> s'.
Proof.
  scrush. (* > 2s *)
Qed.

Definition equiv_cmd (c1 c2 : cmd) := forall s s', (c1, s) ==> s' <-> (c2, s) ==> s'.

Notation "A ~~ B" := (equiv_cmd A B) (at level 70, no associativity).

Lemma lem_unfold_loop : forall b c, While b c ~~ If b (Seq c (While b c)) Skip.
Proof.
  unfold equiv_cmd; intros; split; intro H; inversion H; ycrush.
Qed.

Lemma lem_while_cong_aux : forall b c c' s s', (While b c, s) ==> s' -> c ~~ c' ->
                                               (While b c', s) ==> s'.
Proof.
  assert (forall p s', p ==> s' -> forall b c c' s, p = (While b c, s) -> c ~~ c' -> (While b c', s) ==> s').
  intros p s' H.
  induction H; sauto.
  - ycrush.
  - unfold equiv_cmd in *; ycrush.
  - eauto.
Qed.

Lemma lem_while_cong : forall b c c', c ~~ c' -> While b c ~~ While b c'.
Proof.
  Reconstr.reasy (@lem_while_cong_aux) (@equiv_cmd).
Qed.

Lemma lem_big_step_deterministic :
  forall c s s1 s2, (c, s) ==> s1 -> (c, s) ==> s2 -> s1 = s2.
Proof.
  intros c s s1 s2 H.
  revert s2.
  induction H; try yelles 1.
  scrush.
  intros s0 H2; inversion H2; scrush.
Qed.

Inductive small_step : cmd * state -> cmd * state -> Prop :=
| AssignSemS : forall x a s, small_step (Assign x a, s) (Skip, update s x (aval s a))
| SeqSemS1 : forall c s, small_step (Seq Skip c, s) (c, s)
| SeqSemS2 : forall c1 c2 s c1' s', small_step (c1, s) (c1', s') ->
                                    small_step (Seq c1 c2, s) (Seq c1' c2, s')
| IfTrueS : forall b c1 c2 s, bval s b = true ->
                              small_step (If b c1 c2, s) (c1, s)
| IfFalseS : forall b c1 c2 s, bval s b = false ->
                               small_step (If b c1 c2, s) (c2, s)
| WhileS : forall b c s, small_step (While b c, s) (If b (Seq c (While b c)) Skip, s).

Notation "A --> B" := (small_step A B) (at level 80, no associativity).

Require Import Relations.

Ltac pose_rt := pose @rt_step; pose @rt_refl; pose @rt_trans.

Definition small_step_star := clos_refl_trans (cmd * state) small_step.

Hint Unfold small_step_star : yhints.

Notation "A -->* B" := (small_step_star A B) (at level 80, no associativity).

Lemma lem_small_step_deterministic :
  forall c s s1 s2, (c, s) --> s1 -> (c, s) --> s2 -> s1 = s2.
Proof.
  intros c s s1 s2 H.
  revert s2.
  induction H; try yelles 1.
  scrush.
  intros s2 H2; inversion H2; scrush.
Qed.

Lemma lem_star_seq2 : forall c1 c2 s c1' s', (c1, s) -->* (c1', s') ->
                                             (Seq c1 c2, s) -->* (Seq c1' c2, s').
Proof.
  assert (forall p1 p2, p1 -->* p2 ->
                        forall c1 c2 s c1' s', p1 = (c1, s) -> p2 = (c1', s') ->
                                               (Seq c1 c2, s) -->* (Seq c1' c2, s')).
  intros p1 p2 H.
  induction H as [ | | ? y ]; try yelles 1.
  pose_rt; pose SeqSemS2; scrush.
  intros c1 c2 s c1' s' H1 H2; subst.
  destruct y as [ c0 s0 ].
  assert ((Seq c1 c2, s) -->* (Seq c0 c2, s0)) by scrush.
  assert ((Seq c0 c2, s0) -->* (Seq c1' c2, s')) by scrush.
  pose_rt; scrush.
  scrush.
Qed.

Lemma lem_seq_comp : forall c1 c2 s1 s2 s3, (c1, s1) -->* (Skip, s2) -> (c2, s2) -->* (Skip, s3) ->
                                            (Seq c1 c2, s1) -->* (Skip, s3).
Proof.
  intros c1 c2 s1 s2 s3 H1 H2.
  assert ((Seq c1 c2, s1) -->* (Seq Skip c2, s2)).
  pose lem_star_seq2; scrush.
  assert ((Seq Skip c2, s2) -->* (c2, s2)).
  pose_rt; scrush.
  pose_rt; scrush.
Qed.

Lemma lem_big_to_small : forall p s', p ==> s' -> p -->* (Skip, s').
Proof.
  intros p s' H.
  induction H as [ | | | | | | b c s1 s2 ]; try yelles 1.
  - Reconstr.reasy (@lem_seq_comp) Reconstr.Empty.
  - pose_rt; pose IfTrueS; scrush.
  - pose_rt; pose IfFalseS; scrush.
  - pose_rt; pose WhileS; pose IfFalseS; ycrush.
  - assert ((While b c, s1) -->* (Seq c (While b c), s1)) by
        (pose_rt; pose WhileS; pose IfTrueS; ycrush).
    assert ((Seq c (While b c), s1) -->* (Seq Skip (While b c), s2)) by
        Reconstr.reasy (@lem_star_seq2) Reconstr.Empty.
    pose_rt; pose SeqSemS1; ycrush.
Qed.

Lemma lem_small_to_big_aux : forall p p', p --> p' -> forall s, p' ==> s -> p ==> s.
Proof.
  intros p p' H.
  induction H; sauto; try yelles 1.
  Reconstr.reasy (@lem_unfold_loop) (@equiv_cmd).
Qed.

Lemma lem_small_to_big_aux_2 : forall p p', p -->* p' -> forall s, p' ==> s -> p ==> s.
Proof.
  intros p p' H.
  induction H; sauto.
  Reconstr.reasy (@lem_small_to_big_aux) Reconstr.Empty.
Qed.

Lemma lem_small_to_big : forall p s, p -->* (Skip, s) -> p ==> s.
Proof.
  assert (forall p p', p -->* p' -> forall s, p' = (Skip, s) -> p ==> s).
  intros p p' H.
  induction H; sauto.
  - ycrush.
  - Reconstr.rsimple (@lem_small_to_big_aux_2) (@small_step_star).
  - ycrush.
Qed.

Corollary cor_big_iff_small : forall p s, p ==> s <-> p -->* (Skip, s).
Proof.
  Reconstr.reasy (@lem_small_to_big, @lem_big_to_small) Reconstr.Empty.
Qed.
