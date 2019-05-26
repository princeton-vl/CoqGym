Require Import String.
Require Import Ascii.
Require Import Orders.

Inductive lex_lt: string -> string -> Prop :=
| lex_lt_lt : forall (c1 c2 : ascii) (s1 s2 : string),
    nat_of_ascii c1 < nat_of_ascii c2 ->
    lex_lt (String c1 s1) (String c2 s2)
| lex_lt_eq : forall (c : ascii) (s1 s2 : string),
    lex_lt s1 s2 ->
    lex_lt (String c s1) (String c s2)
| lex_lt_empty : forall (c : ascii) (s : string),
    lex_lt EmptyString (String c s).

Theorem lex_lt_not_eq : forall s0 s1,
    lex_lt s0 s1 -> s0 <> s1.
Proof.
  induction s0.
  - intros.
    inversion H; subst.
    congruence.
  - intros.
    inversion H; subst.
    * intro H_eq.
      injection H_eq; intros; subst.
      contradict H3.
      auto with arith.
    * intro H_eq.
      injection H_eq; intros; subst.
      specialize (IHs0 s3).
      apply IHs0 in H3.
      auto.
Qed.

Lemma lex_lt_irrefl : Irreflexive lex_lt.
Proof.
  intros s0 H_lt.
  apply lex_lt_not_eq in H_lt.
  auto.
Qed.

Theorem lex_lt_trans : forall s0 s1 s2,
    lex_lt s0 s1 -> lex_lt s1 s2 -> lex_lt s0 s2.
Proof.
induction s0.
- intros.  
  inversion H; subst.
  inversion H0; subst.
  * apply lex_lt_empty.
  * apply lex_lt_empty.
- intros.
  inversion H; subst; inversion H0; subst.
  * apply lex_lt_lt.
    eauto with arith.
  * apply lex_lt_lt.
    assumption.
  * apply lex_lt_lt.
    assumption.
  * apply lex_lt_eq.
    eapply IHs0; eauto.
Qed.

Theorem lex_lt_strorder : StrictOrder lex_lt.
Proof.
  exact (Build_StrictOrder _ lex_lt_irrefl lex_lt_trans).
Qed.
