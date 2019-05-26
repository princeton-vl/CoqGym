Require Import StructTact.StructTactics.

Set Implicit Arguments.

Lemma or_false :
  forall P : Prop, P -> (P \/ False).
Proof.
  firstorder.
Qed.

Lemma if_sum_bool_fun_comm :
  forall A B C D (b : {A}+{B}) (c1 c2 : C) (f : C -> D),
    f (if b then c1 else c2) = if b then f c1 else f c2.
Proof.
  intros. break_if; auto.
Qed.

Lemma if_decider_true :
  forall A B (P : A -> Prop) (dec : forall x, {P x} + {~ P x}) a (b1 b2 : B),
    P a ->
    (if dec a then b1 else b2) = b1.
Proof.
  intros.
  break_if; congruence.
Qed.

Lemma if_decider_false :
  forall A B (P : A -> Prop) (dec : forall x, {P x} + {~ P x}) a (b1 b2 : B),
    ~ P a ->
    (if dec a then b1 else b2) = b2.
Proof.
  intros.
  break_if; congruence.
Qed.

Definition prod_eq_dec :
  forall A B
    (A_eq_dec : forall x y : A, {x = y} + {x <> y})
    (B_eq_dec : forall x y : B, {x = y} + {x <> y})
    (x y : A * B),
    {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

(* from SF's tactics library *)
Section equatesLemma.
Variables
  (A0 A1 : Type)
  (A2 : forall(x1 : A1), Type)
  (A3 : forall(x1 : A1) (x2 : A2 x1), Type)
  (A4 : forall(x1 : A1) (x2 : A2 x1) (x3 : A3 x2), Type)
  (A5 : forall(x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3), Type)
  (A6 : forall(x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3) (x5 : A5 x4), Type).

Lemma equates_0 : forall(P Q:Prop),
  P -> P = Q -> Q.
Proof using. intros. subst. auto. Qed.

Lemma equates_1 :
  forall(P:A0->Prop) x1 y1,
  P y1 -> x1 = y1 -> P x1.
Proof using. intros. subst. auto. Qed.

Lemma equates_2 :
  forall y1 (P:A0->forall(x1:A1),Prop) x1 x2,
  P y1 x2 -> x1 = y1 -> P x1 x2.
Proof using. intros. subst. auto. Qed.

Lemma equates_3 :
  forall y1 (P:A0->forall(x1:A1)(x2:A2 x1),Prop) x1 x2 x3,
  P y1 x2 x3 -> x1 = y1 -> P x1 x2 x3.
Proof using. intros. subst. auto. Qed.

Lemma equates_4 :
  forall y1 (P:A0->forall(x1:A1)(x2:A2 x1)(x3:A3 x2),Prop) x1 x2 x3 x4,
  P y1 x2 x3 x4 -> x1 = y1 -> P x1 x2 x3 x4.
Proof using. intros. subst. auto. Qed.

Lemma equates_5 :
  forall y1 (P:A0->forall(x1:A1)(x2:A2 x1)(x3:A3 x2)(x4:A4 x3),Prop) x1 x2 x3 x4 x5,
  P y1 x2 x3 x4 x5 -> x1 = y1 -> P x1 x2 x3 x4 x5.
Proof using. intros. subst. auto. Qed.

Lemma equates_6 :
  forall y1 (P:A0->forall(x1:A1)(x2:A2 x1)(x3:A3 x2)(x4:A4 x3)(x5:A5 x4),Prop)
  x1 x2 x3 x4 x5 x6,
  P y1 x2 x3 x4 x5 x6 -> x1 = y1 -> P x1 x2 x3 x4 x5 x6.
Proof using. intros. subst. auto. Qed.
    
End equatesLemma.

