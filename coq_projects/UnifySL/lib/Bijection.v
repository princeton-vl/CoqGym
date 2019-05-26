Require Export Coq.Relations.Relation_Definitions.
Require Export Coq.Relations.Relation_Operators.
Require Export Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.RelationClasses.
Require Import Coq.Arith.Even.
Require Import Coq.Arith.Div2.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Omega.

Definition image_defined {A B} (R: A -> B -> Prop): Prop :=
  forall a, exists b, R a b.

Definition partial_functional {A B} (R: A -> B -> Prop): Prop :=
  forall a b1 b2, R a b1 -> R a b2 -> b1 = b2.

Definition injective {A B} (R: A -> B -> Prop): Prop :=
  forall a1 a2 b, R a1 b -> R a2 b -> a1 = a2.

Definition surjective {A B} (R: A -> B -> Prop): Prop :=
  forall b, exists a, R a b.

Definition function_injective {A B} (f: A -> B): Prop :=
  forall a1 a2, f a1 = f a2 -> a1 = a2.

Definition function_surjective {A B} (f: A -> B): Prop :=
  forall b, exists a, f a = b.

Record injection (A B: Type): Type := {
  inj_R:> A -> B -> Prop;
  im_inj: image_defined inj_R;
  pf_inj: partial_functional inj_R;
  in_inj: injective inj_R
}.

Record surjection (A B: Type): Type := {
  sur_R:> A -> B -> Prop;
  im_surj: image_defined sur_R;
  pf_surj: partial_functional sur_R;
  su_surj: surjective sur_R
}.

Record bijection (A B: Type): Type := {
  bij_R:> A -> B -> Prop;
  im_bij: image_defined bij_R;
  pf_bij: partial_functional bij_R;
  in_bij: injective bij_R;
  su_bij: surjective bij_R
}.

Definition FBuild_injection (A B: Type) (f: A -> B) (H: function_injective f): injection A B.
  apply (Build_injection _ _ (fun a b => f a = b)).
  + hnf; intros; eauto.
  + hnf; intros; congruence.
  + hnf; intros.
    apply H; congruence.
Defined.

Definition FBuild_surjection (A B: Type) (f: A -> B) (H: function_surjective f): surjection A B.
  apply (Build_surjection _ _ (fun a b => f a = b)).
  + hnf; intros; eauto.
  + hnf; intros; congruence.
  + hnf; intros.
    apply H; congruence.
Defined.

Definition FBuild_bijection (A B: Type) (f: A -> B) (H: function_injective f) (H0: function_surjective f): bijection A B.
  apply (Build_bijection _ _ (fun a b => f a = b)).
  + hnf; intros; eauto.
  + hnf; intros; congruence.
  + hnf; intros.
    apply H; congruence.
  + hnf; intros.
    apply H0.
Defined.

Definition injection_trans {A B C} (R1: injection A B) (R2: injection B C): injection A C.
  intros.
  apply (Build_injection _ _ (fun a c => exists b, R1 a b /\ R2 b c)).
  + hnf; intros.
    destruct (im_inj _ _ R1 a) as [b ?].
    destruct (im_inj _ _ R2 b) as [c ?].
    exists c; eauto.
  + hnf; intros a c1 c2 [b1 [? ?]] [b2 [? ?]].
    pose proof pf_inj _ _ R1 a b1 b2 H H1.
    subst b2.
    pose proof pf_inj _ _ R2 b1 c1 c2 H0 H2.
    auto.
  + hnf; intros a1 a2 c [b1 [? ?]] [b2 [? ?]].
    pose proof in_inj _ _ R2 b1 b2 c H0 H2.
    subst b2.
    pose proof in_inj _ _ R1 a1 a2 b1 H H1.
    auto.
Defined.

Definition bijection_sym {A B} (R: bijection A B): bijection B A.
  apply (Build_bijection _ _ (fun a b => R b a)).
  + hnf.
    apply (su_bij _ _ R).
  + hnf; intros.
    apply (in_bij _ _ R b1 b2 a); auto.
  + hnf; intros.
    apply (pf_bij _ _ R b a1 a2); auto.
  + hnf.
    apply (im_bij _ _ R).
Defined.

Definition bijection_refl {A}: bijection A A.
  apply (Build_bijection _ _ eq).
  + hnf; intros.
    eauto.
  + hnf; intros.
    congruence.
  + hnf; intros.
    congruence.
  + hnf; intros.
    eauto.
Defined.

Definition sum_injection {A1 B1 A2 B2} (R1: injection A1 B1) (R2: injection A2 B2): injection (sum A1 A2) (sum B1 B2).
Proof.
  intros.
  apply (Build_injection _ _ (fun a b =>
          match a, b with
          | inl a, inl b => R1 a b
          | inr a, inr b => R2 a b
          | _, _ => False
          end)).
  + hnf; intros.
    destruct a as [a | a].
    - destruct (im_inj _ _ R1 a) as [b ?].
      exists (inl b); auto.
    - destruct (im_inj _ _ R2 a) as [b ?].
      exists (inr b); auto.
  + hnf; intros.
    destruct a as [a | a], b1 as [b1 | b1], b2 as [b2 | b2]; try solve [inversion H | inversion H0].
    - f_equal; apply (pf_inj _ _ R1 a); auto.
    - f_equal; apply (pf_inj _ _ R2 a); auto.
  + hnf; intros.
    destruct a1 as [a1 | a1], a2 as [a2 | a2], b as [b | b]; try solve [inversion H | inversion H0].
    - f_equal; apply (in_inj _ _ R1 _ _ b); auto.
    - f_equal; apply (in_inj _ _ R2 _ _ b); auto.
Defined.

Definition prod_injection {A1 B1 A2 B2} (R1: injection A1 B1) (R2: injection A2 B2): injection (prod A1 A2) (prod B1 B2).
Proof.
  intros.
  apply (Build_injection _ _ (fun a b => R1 (fst a) (fst b) /\ R2 (snd a) (snd b))).
  + hnf; intros.
    destruct (im_inj _ _ R1 (fst a)) as [b1 ?].
    destruct (im_inj _ _ R2 (snd a)) as [b2 ?].
    exists (b1, b2); auto.
  + hnf; intros.
    destruct b1, b2, H, H0.
    pose proof pf_inj _ _ R1 (fst a) _ _ H H0.
    pose proof pf_inj _ _ R2 (snd a) _ _ H1 H2.
    simpl in *; subst; auto.
  + hnf; intros.
    destruct a1, a2, H, H0.
    pose proof in_inj _ _ R1 _ _ _ H H0.
    pose proof in_inj _ _ R2 _ _ _ H1 H2.
    simpl in *; subst; auto.
Defined.

Definition sigT_injection (I: Type) (A: I -> Type) (B: Type) (R: forall i: I, injection (A i) B): injection (sigT A) (I * B).
  apply (Build_injection _ _ (fun a b => projT1 a = fst b /\ (R (projT1 a)) (projT2 a) (snd b))).
  + hnf; intros.
    destruct a as [i a0].
    destruct (im_inj _ _ (R i) a0) as [b0 ?].
    exists (i, b0).
    auto.
  + hnf; intros.
    destruct b1 as [i1 b1]; simpl in H.
    destruct b2 as [i2 b2]; simpl in H0.
    destruct H, H0; subst.
    pose proof pf_inj _ _ (R (projT1 a)) _ _ _ H1 H2.
    subst; auto.
  + hnf; intros.
    destruct b, H, H0; simpl in *; subst.
    destruct a1, a2; simpl in *; subst.
    pose proof in_inj _ _ (R x) _ _ _ H1 H2.
    subst; auto.
Qed.

Definition bijection_injection {A B} (R: bijection A B): injection A B :=
  Build_injection _ _ R (im_bij _ _ R) (pf_bij _ _ R) (in_bij _ _ R).

Definition nat2_nat_bijection: bijection (sum nat nat) nat.
  apply (Build_bijection _ _ (fun n m => match n with | inl n => m = n + n | inr n => m = n + n +1 end)).
  + hnf; intros.
    destruct a; eauto.
  + hnf; intros.
    destruct a; inversion H; inversion H0; auto.
  + hnf; intros.
    destruct a1, a2; inversion H; inversion H0; destruct (lt_eq_lt_dec n n0) as [[? | ?] | ?]; try omega; subst; auto.
  + hnf; intros.
    destruct (Even.even_odd_dec b) as [H | H].
    - rewrite (proj1 (Div2.even_odd_double _)), NPeano.double_twice in H.
      exists (inl (Div2.div2 b)).
      rewrite H at 1. omega.
    - rewrite (proj2 (Div2.even_odd_double _)), NPeano.double_twice in H.
      exists (inr (Div2.div2 b)).
      rewrite H at 1. omega.
Defined.

Definition natnat_nat_bijection: bijection (prod nat nat) nat.
  apply (Build_bijection _ _
          (fun n m => m = match n with | (n1, n2) => 
                            (fix sum (x: nat): nat := match x with | O => O | S x => S x + sum x end)
                              (n1 + n2)
                            + n1
                          end)).
  + hnf; intros.
    destruct a; eauto.
  + hnf; intros.
    destruct a; omega.
  + hnf; intros.
    destruct a1 as [a11 a12], a2 as [a21 a22].
    assert (forall m1 m2, m1 < m2 ->
      (fix sum (x : nat) : nat :=
          match x with
          | 0 => 0
          | S x0 => S x0 + sum x0
          end) m1 + m1 <
      (fix sum (x : nat) : nat :=
          match x with
          | 0 => 0
          | S x0 => S x0 + sum x0
          end) m2).
    Focus 1. {
      intros.
      remember (m2 - m1 - 1) as d; assert (m2 = (S d) + m1) by omega.
      subst m2; clear.
      induction d.
      + simpl.
        omega.
      + simpl in *.
        omega.
    } Unfocus.
    destruct (lt_eq_lt_dec (a11 + a12) (a21 + a22)) as [[HH | HH] | HH].
    - specialize (H1 _ _ HH).
      omega.
    - rewrite HH in H.
      assert (a11 = a21) by omega.
      assert (a12 = a22) by omega.
      subst; auto.
    - specialize (H1 _ _ HH).
      omega.
  + hnf; intros.
    assert (exists s,
        (fix sum (x : nat) : nat :=
          match x with
          | 0 => 0
          | S x0 => S x0 + sum x0
          end) s <= b <
        (fix sum (x : nat) : nat :=
          match x with
          | 0 => 0
          | S x0 => S x0 + sum x0
          end) (S s)).
    Focus 1. {
      induction b.
      + exists 0; simpl.
        omega.
      + destruct IHb as [s ?].
        remember (b - (fix sum (x : nat) : nat :=
                         match x with
                         | 0 => 0
                         | S x0 => S x0 + sum x0
                         end) s) as d.
        destruct (lt_dec d s) as [HH | HH].
        - exists s; simpl in *; omega.
        - exists (S s); simpl in *; omega.
    } Unfocus.
    destruct H as [s ?].
    remember (b - (fix sum (x : nat) : nat :=
                match x with
                | 0 => 0
                | S x0 => S x0 + sum x0
                end) s) as a1.
    exists (a1, s - a1).
    replace (a1 + (s - a1)) with s by omega.
    omega.
Defined.

