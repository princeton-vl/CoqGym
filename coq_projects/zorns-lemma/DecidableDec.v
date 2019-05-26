Require Import Description.

Lemma exclusive_dec: forall P Q:Prop, ~(P /\ Q) ->
  (P \/ Q) -> {P} + {Q}.
Proof.
intros.
assert ({x:bool | if x then P else Q}).
apply constructive_definite_description.
case H0.
exists true.
red; split.
assumption.
destruct x'.
reflexivity.
tauto.
exists false.
red; split.
assumption.
destruct x'.
tauto.
reflexivity.

destruct H1.
destruct x.
left.
assumption.
right.
assumption.
Qed.

Lemma decidable_dec: forall P:Prop, P \/ ~P -> {P} + {~P}.
Proof.
intros.
apply exclusive_dec.
tauto.
assumption.
Qed.

Require Import Classical.

Lemma classic_dec: forall P:Prop, {P} + {~P}.
Proof.
intro P.
apply decidable_dec.
apply classic.
Qed.
