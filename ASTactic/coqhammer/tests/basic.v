From Hammer Require Import Hammer Reconstr.

Hammer_version.
Hammer_objects.

Set Hammer CrushLimit 0.

Lemma lem_1 {A : Type} (P : A -> Prop) : forall x, P x -> P x.
Proof.
  hammer.
Qed.

Lemma lem_2 {A : Type} (P Q : A -> Prop) : forall x, P x \/ Q x -> Q x \/ P x.
Proof.
  hammer.
Qed.

Lemma lem_3 {A : Type} (P Q : A -> Prop) : forall x, (forall x, P x -> Q x) -> P x -> Q x.
Proof.
  hammer.
Qed.

Section Sets.

Variable U : Type.
Variable P : U -> Prop.
Variable Q : U -> Prop.
Variable R : U -> Prop.

Lemma lem_sets_1 :
  (forall x, P x \/ Q x) /\ (forall x y, x = y /\ P x -> R y) /\
  (forall x y, x = y /\ Q x -> R y) -> forall x, R x.
Proof.
  hammer.
Qed.

Variable Sum : U -> U -> U.
Variable Subset : U -> U -> Prop.
Variable In : U -> U -> Prop.
Variable Seteq : U -> U -> Prop.

Lemma lem_sets_2 :
  (forall A B X, In X (Sum A B) <-> In X A \/ In X B) /\
  (forall A B, Seteq A B <-> Subset A B /\ Subset B A) /\
  (forall A B, Subset A B <-> forall X, In X A -> In X B) ->
  (forall A, Seteq (Sum A A) A).
Proof.
  yelles 3.
Qed.

End Sets.
