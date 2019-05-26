Require Export FunctionProperties.
Require Import DecidableDec.
Require Import Description.
Require Import Classical.

(* CSB = Cantor-Schroeder-Bernstein theorem *)

Section CSB.
Variable X Y:Type.
Variable f:X->Y.
Variable g:Y->X.
Hypothesis f_inj: injective f.
Hypothesis g_inj: injective g.

Inductive X_even: X->Prop :=
  | not_g_img: forall x:X, (forall y:Y, g y <> x) -> X_even x
  | g_Y_odd: forall y:Y, Y_odd y -> X_even (g y)
with Y_odd: Y->Prop :=
  | f_X_even: forall x:X, X_even x -> Y_odd (f x).
Inductive X_odd: X->Prop :=
  | g_Y_even: forall y:Y, Y_even y -> X_odd (g y)
with Y_even: Y->Prop :=
  | not_f_img: forall y:Y, (forall x:X, f x <> y) -> Y_even y
  | f_X_odd: forall x:X, X_odd x -> Y_even (f x).

Scheme X_even_coind := Minimality for X_even Sort Prop
  with Y_odd_coind := Minimality for Y_odd Sort Prop.
Scheme X_odd_coind := Minimality for X_odd Sort Prop
  with Y_even_coind := Minimality for Y_even Sort Prop.

Lemma even_odd_excl: forall x:X, ~(X_even x /\ X_odd x).
Proof.
intro.
assert (X_even x -> ~ X_odd x).
2:tauto.
pose proof (X_even_coind (fun x:X => ~ X_odd x) (fun y:Y => ~ Y_even y)).
apply H.
intuition.
destruct H1.
apply H0 with y.
reflexivity.
intuition.
inversion H2.
apply g_inj in H3.
apply H1.
rewrite <- H3.
assumption.
intuition.
inversion H2.
apply H3 with x0.
reflexivity.
apply f_inj in H3.
apply H1.
rewrite <- H3.
assumption.
Qed.

Lemma even_odd_excl2: forall y:Y, ~(Y_even y /\ Y_odd y).
Proof.
intro.
assert (Y_odd y -> ~ Y_even y).
2:tauto.
pose proof (Y_odd_coind (fun x:X => ~ X_odd x) (fun y:Y => ~ Y_even y)).
apply H.
intuition.
destruct H1.
apply H0 with y0.
reflexivity.
intuition.
inversion H2.
apply g_inj in H3.
apply H1.
rewrite <- H3.
assumption.
intuition.
inversion H2.
apply H3 with x.
reflexivity.
apply f_inj in H3.
apply H1.
rewrite <- H3.
assumption.
Qed.

Definition finv: forall y:Y, (exists x:X, f x = y) ->
  { x:X | f x = y }.
intros.
apply constructive_definite_description.
destruct H.
exists x.
red; split.
assumption.
intros.
apply f_inj.
transitivity y; trivial.
symmetry; trivial.
Defined.

Definition ginv: forall x:X, (exists y:Y, g y = x) ->
  { y:Y | g y = x }.
intros.
apply constructive_definite_description.
destruct H.
exists x0.
red; split.
assumption.
intros.
apply g_inj.
transitivity x; trivial; symmetry; trivial.
Defined.

Definition ginv_odd: forall x:X, X_odd x ->
  { y:Y | g y = x }.
intros.
apply ginv.
destruct H.
exists y.
reflexivity.
Defined.

Definition finv_noteven: forall y:Y, ~ Y_even y ->
  { x:X | f x = y }.
intros.
apply finv.
apply NNPP.
red; intro.
contradict H.
constructor 1.
intro; red; intro.
apply H0.
exists x.
assumption.
Defined.

Definition CSB_bijection (x:X) : Y :=
  match (classic_dec (X_odd x)) with
  | left o => proj1_sig (ginv_odd x o)
  | right _ => f x
  end.
Definition CSB_bijection2 (y:Y) : X :=
  match (classic_dec (Y_even y)) with
  | left _ => g y
  | right ne => proj1_sig (finv_noteven y ne)
  end.

Lemma CSB_comp1: forall x:X, CSB_bijection2 (CSB_bijection x) = x.
Proof.
intro.
unfold CSB_bijection; case (classic_dec (X_odd x)).
intro.
destruct ginv_odd.
simpl.
unfold CSB_bijection2; case (classic_dec (Y_even x1)).
intro.
assumption.
intro.
destruct x0.
contradict n.
apply g_inj in e.
rewrite e.
assumption.
intro.
unfold CSB_bijection2; case (classic_dec (Y_even (f x))).
intro.
contradict n.
inversion y.
pose proof (H x).
contradict H1; reflexivity.
apply f_inj in H.
rewrite <- H.
assumption.
intro.
destruct finv_noteven.
simpl.
apply f_inj.
assumption.
Qed.

Lemma CSB_comp2: forall y:Y, CSB_bijection (CSB_bijection2 y) = y.
Proof.
intro.
unfold CSB_bijection2; case (classic_dec (Y_even y)).
intro.
unfold CSB_bijection; case (classic_dec (X_odd (g y))).
intro.
destruct ginv_odd.
simpl.
apply g_inj.
assumption.
intro.
contradict n.
constructor.
assumption.
intro.
destruct finv_noteven.
simpl.
unfold CSB_bijection; case (classic_dec (X_odd x)).
intro.
contradict n.
rewrite <- e.
constructor 2.
assumption.
trivial.
Qed.

Theorem CSB: exists h:X->Y, bijective h.
Proof.
exists CSB_bijection.
apply invertible_impl_bijective.
exists CSB_bijection2.
exact CSB_comp1.
exact CSB_comp2.
Qed.

End CSB.
