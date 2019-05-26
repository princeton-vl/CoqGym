Require Import String.
Require Import Ascii.
Require Import Arith.
Require Import OrderedType.
Require Import OrderedTypeEx.

Require Import StructTact.StructTactics.

Inductive lex_lt: string -> string -> Prop :=
| lex_lt_lt : forall (c1 c2 : ascii) (s1 s2 : string),
    nat_of_ascii c1 < nat_of_ascii c2 ->
    lex_lt (String c1 s1) (String c2 s2)
| lex_lt_eq : forall (c : ascii) (s1 s2 : string),
    lex_lt s1 s2 ->
    lex_lt (String c s1) (String c s2)
| lex_lt_empty : forall (c : ascii) (s : string),
    lex_lt EmptyString (String c s).

Inductive lex_order : string -> string -> Prop :=
| lex_order_empty :
    lex_order EmptyString EmptyString
| lex_order_char_lt :
    forall (c1 c2: ascii) (s1 s2: string),
      nat_of_ascii c1 < nat_of_ascii c2 ->
      lex_order (String c1 s1) (String c2 s2)
| lex_order_char_eq :
    forall (c: ascii) (s1 s2: string),
      lex_order s1 s2 ->
      lex_order (String c s1) (String c s2)
| lex_order_empty_string :
    forall s, lex_order EmptyString s.

Definition lex_le (s1 s2 : string) : Prop := lex_lt s1 s2 \/ s1 = s2.

Lemma lex_le_in_lex_order : forall (s1 s2 : string),
    lex_order s1 s2 -> lex_le s1 s2.
Proof.
  intros s1 s2 H.
  induction H.
  - right.
    reflexivity.
  - left.
    apply lex_lt_lt.
    assumption.
  - case IHlex_order; intro H_le.
    * left.
      apply lex_lt_eq.
      assumption.
    * rewrite H_le.
      right.
      reflexivity.
  - case s.
    * right.
      reflexivity.
    * intros c s0.
      left.
      apply lex_lt_empty.
Qed.

Lemma lex_order_refl : forall (s : string), lex_order s s.
Proof.
  induction s.
  * apply lex_order_empty_string.
  * intros.
    apply lex_order_char_eq.
    assumption.
Qed.
  
Lemma lex_order_lex_le : forall (s1 s2 : string),
    lex_le s1 s2 -> lex_order s1 s2.
intros s1 s2 H_le.
case H_le; intro H_le'.
- induction H_le'.
  * apply lex_order_char_lt.
    assumption.
  * apply lex_order_char_eq.
    apply IHH_le'.
    left.
    assumption.
  * apply lex_order_empty_string.
- rewrite <- H_le'.
  apply lex_order_refl.
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
      find_injection.
      contradict H3.
      auto with arith.
    * intro H_eq.
      find_injection.
      specialize (IHs0 s3).
      concludes.
      auto.
Qed.

Lemma nat_of_ascii_injective:
  forall c1 c2, nat_of_ascii c1 = nat_of_ascii c2 -> c1 = c2.
Proof.
  intros; simpl.
  assert (ascii_of_nat (nat_of_ascii c1) =
          ascii_of_nat (nat_of_ascii c2))
      as Hinvol. auto.
  repeat rewrite ascii_nat_embedding in Hinvol.
  trivial.
Qed.

Fixpoint string_compare_lex_compat (s0 s1 : string) : Compare lex_lt eq s0 s1.
refine
  (match s0 as ss0, s1 as ss1 return (_ = ss0 -> _ = ss1 -> _) with
   | EmptyString, EmptyString => fun H_eq H_eq' => EQ _
   | EmptyString, String c' s'1 => fun H_eq H_eq' => LT _
   | String c s'0, EmptyString => fun H_eq H_eq' => GT _
   | String c s'0, String c' s'1 => fun H_eq H_eq' =>
     match Nat.compare (nat_of_ascii c) (nat_of_ascii c') as cmp return (_ = cmp -> _) with
     | Lt => fun H_eq_cmp => LT _
     | Eq => fun H_eq_cmp =>
       match string_compare_lex_compat s'0 s'1 with
       | LT H_lt => LT _
       | EQ H_eq_lex => EQ _
       | GT H_gt => GT _
       end
     | Gt => fun H_eq_cmp => GT _
     end (refl_equal _)
   end (refl_equal _) (refl_equal _)); try (rewrite H_eq; rewrite H_eq'); auto.
- apply lex_lt_empty.
- apply lex_lt_empty.
- apply nat_compare_eq in H_eq_cmp.
  apply nat_of_ascii_injective in H_eq_cmp.
  rewrite H_eq_cmp.
  apply lex_lt_eq.
  assumption.
- apply nat_compare_eq in H_eq_cmp.
  apply nat_of_ascii_injective in H_eq_cmp.
  subst.
  reflexivity.
- apply nat_compare_eq in H_eq_cmp.
  apply nat_of_ascii_injective in H_eq_cmp.
  rewrite H_eq_cmp.
  apply lex_lt_eq.
  assumption.
- apply nat_compare_lt in H_eq_cmp.
  apply lex_lt_lt.
  assumption.
- apply nat_compare_gt in H_eq_cmp.
  apply lex_lt_lt.
  auto with arith.
Defined.

Module string_lex_as_OT_compat <: UsualOrderedType.
  Definition t := string.
  Definition eq := @eq string.
  Definition lt := lex_lt.
  Definition eq_refl := @eq_refl string.
  Definition eq_sym := @eq_sym string.
  Definition eq_trans := @eq_trans string.
  Definition lt_trans := lex_lt_trans.
  Definition lt_not_eq := lex_lt_not_eq.
  Definition compare := string_compare_lex_compat.
  Definition eq_dec := string_dec.
End string_lex_as_OT_compat.

Require Import Orders.

Lemma lex_lt_irrefl : Irreflexive lex_lt.
Proof.
  intros s0 H_lt.
  apply lex_lt_not_eq in H_lt.
  auto.
Qed.

Theorem lex_lt_strorder : StrictOrder lex_lt.
Proof.
  exact (Build_StrictOrder _ lex_lt_irrefl lex_lt_trans).
Qed.

Theorem lex_lt_lt_compat : Proper (eq ==> eq ==> iff) lex_lt.
Proof.
intros s0 s1 H_eq s2 s3 H_eq'.
split; intro H_imp; subst; auto.
Qed.

Fixpoint string_compare_lex (s0 s1 : string) : { cmp : comparison | CompSpec eq lex_lt s0 s1 cmp }.
refine
  (match s0 as ss0, s1 as ss1 return (_ = ss0 -> _ = ss1 -> _) with
   | EmptyString, EmptyString => fun H_eq H_eq' => exist _ Eq _
   | EmptyString, String c' s'1 => fun H_eq H_eq' => exist _ Lt _
   | String c s'0, EmptyString => fun H_eq H_eq' => exist _ Gt _
   | String c s'0, String c' s'1 => fun H_eq H_eq' =>
     match Nat.compare (nat_of_ascii c) (nat_of_ascii c') as cmp0 return (_ = cmp0 -> _)  with
     | Lt => fun H_eq_cmp0 => exist _ Lt _
     | Eq => fun H_eq_cmp0 =>
       match string_compare_lex s'0 s'1 with
       | exist _ cmp H_cmp' =>
         match cmp as cmp1 return (cmp = cmp1 -> _) with
         | Lt => fun H_eq_cmp1 => exist _ Lt _
         | Eq => fun H_eq_cmp1 => exist _ Eq _
         | Gt => fun H_eq_cmp1 => exist _ Gt _
         end (refl_equal _)
       end
     | Gt => fun H_eq_cmp0 => exist _ Gt _
     end (refl_equal _)
   end (refl_equal _) (refl_equal _)); try (rewrite H_eq; rewrite H_eq').
- apply CompEq; auto.
- apply CompLt.
  apply lex_lt_empty.
- apply CompGt.
  apply lex_lt_empty.
- apply nat_compare_eq in H_eq_cmp0.
  apply nat_of_ascii_injective in H_eq_cmp0.
  rewrite H_eq_cmp1 in H_cmp'.
  inversion H_cmp'; subst.
  apply CompEq.
  reflexivity.
- apply nat_compare_eq in H_eq_cmp0.
  apply nat_of_ascii_injective in H_eq_cmp0.
  rewrite H_eq_cmp1 in H_cmp'.
  inversion H_cmp'.
  subst.
  apply CompLt.
  apply lex_lt_eq.
  assumption.
- apply nat_compare_eq in H_eq_cmp0.
  apply nat_of_ascii_injective in H_eq_cmp0.
  rewrite H_eq_cmp1 in H_cmp'.
  subst.
  inversion H_cmp'.
  apply CompGt.
  apply lex_lt_eq.
  assumption.
- apply nat_compare_lt in H_eq_cmp0.
  apply CompLt.
  apply lex_lt_lt.
  assumption.
- apply nat_compare_gt in H_eq_cmp0.
  apply CompGt.
  apply lex_lt_lt.
  auto with arith.
Defined.

Module string_lex_as_OT <: UsualOrderedType.
  Definition t := string.
  Definition eq := @eq string.
  Definition eq_equiv := @eq_equivalence string.
  Definition lt := lex_lt.
  Definition lt_strorder := lex_lt_strorder.
  Definition lt_compat := lex_lt_lt_compat.
  Definition compare := fun x y => proj1_sig (string_compare_lex x y).
  Definition compare_spec := fun x y => proj2_sig (string_compare_lex x y).
  Definition eq_dec := string_dec.
End string_lex_as_OT.
