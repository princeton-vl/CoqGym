Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.Injection.

Set Implicit Arguments.
Set Strict Implicit.


Section PairParam.
  Variable T : Type.
  Variable eqT : T -> T -> Prop.
  Variable U : Type.
  Variable eqU : U -> U -> Prop.

  Inductive sum_eq : T + U -> T + U -> Prop :=
  | Inl_eq : forall a b, eqT a b -> sum_eq (inl a) (inl b)
  | Inr_eq : forall a b, eqU a b -> sum_eq (inr a) (inr b).

  Variable EDT : RelDec eqT.
  Variable EDU : RelDec eqU.

  Global Instance RelDec_equ_sum
  : RelDec (sum_eq) :=
  { rel_dec := fun x y =>
                 match x , y with
                   | inl x , inl y => rel_dec x y
                   | inr x , inr y => rel_dec x y
                   | inl _ , inr _ => false
                   | inr _ , inl _ => false
                 end }.

  Variable EDCT : RelDec_Correct EDT.
  Variable EDCU : RelDec_Correct EDU.

  Global Instance RelDec_Correct_equ_sum : RelDec_Correct RelDec_equ_sum.
  Proof.
    constructor; destruct x; destruct y; split; simpl in *; intros;
      repeat match goal with
               | [ H : context [ rel_dec ?X ?Y ] |- _ ] =>
                 consider (rel_dec X Y); intros; subst
               | [ |- context [ rel_dec ?X ?Y ] ] =>
                 consider (rel_dec X Y); intros; subst
             end; intuition; try solve [ constructor; auto | congruence ].
    + inversion H. intuition.
    + inversion H.
    + inversion H.
    + inversion H; intuition.
  Qed.
End PairParam.

Section SumEq.
  Variable T : Type.
  Variable U : Type.

  Variable EDT : RelDec (@eq T).
  Variable EDU : RelDec (@eq U).

  (** Specialization for equality **)
  Global Instance RelDec_eq_pair : RelDec (@eq (T + U)) :=
  { rel_dec := fun x y =>
                 match x , y with
                   | inl x , inl y => rel_dec x y
                   | inr x , inr y => rel_dec x y
                   | inl _ , inr _ => false
                   | inr _ , inl _ => false
                 end }.

  Variable EDCT : RelDec_Correct EDT.
  Variable EDCU : RelDec_Correct EDU.

  Global Instance RelDec_Correct_eq_pair : RelDec_Correct RelDec_eq_pair.
  Proof.
    constructor; destruct x; destruct y; split; simpl in *; intros;
      repeat match goal with
               | [ H : context [ rel_dec ?X ?Y ] |- _ ] =>
                 consider (rel_dec X Y); intros; subst
               | [ |- context [ rel_dec ?X ?Y ] ] =>
                 consider (rel_dec X Y); intros; subst
             end; congruence.
  Qed.
End SumEq.

Global Instance Injective_inl T U a c : Injective (@inl T U a = inl c).
refine {| result := a = c |}.
Proof. abstract (inversion 1; intuition). Defined.

Global Instance Injective_inr T U a c : Injective (@inr T U a = inr c).
refine {| result := a = c |}.
Proof. abstract (inversion 1; intuition). Defined.

Global Instance Injective_inl_False T U a c : Injective (@inl T U a = inr c).
refine {| result := False |}.
Proof. abstract (inversion 1; intuition). Defined.

Global Instance Injective_inr_False T U a c : Injective (@inr T U a = inl c).
refine {| result := False |}.
Proof. abstract (inversion 1; intuition). Defined.