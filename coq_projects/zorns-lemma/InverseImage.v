Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export EnsemblesSpec.

Definition inverse_image {X Y:Type} (f:X->Y) (T:Ensemble Y) : Ensemble X :=
  [ x:X | In T (f x) ].
Hint Unfold inverse_image : sets.

Lemma inverse_image_increasing: forall {X Y:Type} (f:X->Y)
  (T1 T2:Ensemble Y), Included T1 T2 ->
  Included (inverse_image f T1) (inverse_image f T2).
Proof.
intros.
red; intros.
destruct H0.
constructor.
auto.
Qed.

Lemma inverse_image_empty: forall {X Y:Type} (f:X->Y),
  inverse_image f Empty_set = Empty_set.
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
destruct H as [[]].
destruct H.
Qed.

Lemma inverse_image_full: forall {X Y:Type} (f:X->Y),
  inverse_image f Full_set = Full_set.
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros;
  constructor; constructor.
Qed.

Lemma inverse_image_intersection: forall {X Y:Type} (f:X->Y)
  (T1 T2:Ensemble Y), inverse_image f (Intersection T1 T2) =
  Intersection (inverse_image f T1) (inverse_image f T2).
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
destruct H.
inversion H.
constructor; constructor; trivial.

destruct H as [? [] []].
constructor; constructor; trivial.
Qed.

Lemma inverse_image_union: forall {X Y:Type} (f:X->Y)
  (T1 T2:Ensemble Y), inverse_image f (Union T1 T2) =
  Union (inverse_image f T1) (inverse_image f T2).
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
destruct H.
inversion H.
left; constructor; trivial.
right; constructor; trivial.

constructor.
destruct H as [? []|? []].
left; trivial.
right; trivial.
Qed.

Lemma inverse_image_complement: forall {X Y:Type} (f:X->Y)
  (T:Ensemble Y), inverse_image f (Complement T) =
  Complement (inverse_image f T).
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
red; intro.
destruct H.
destruct H0.
contradiction H.

constructor.
intro.
contradiction H.
constructor; trivial.
Qed.

Lemma inverse_image_composition: forall {X Y Z:Type} (f:Y->Z) (g:X->Y)
  (U:Ensemble Z), inverse_image (fun x:X => f (g x)) U =
  inverse_image g (inverse_image f U).
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
constructor; constructor.
destruct H.
assumption.

destruct H; inversion H.
constructor; trivial.
Qed.

Hint Resolve @inverse_image_increasing : sets.
Hint Rewrite @inverse_image_empty @inverse_image_full
  @inverse_image_intersection @inverse_image_union
  @inverse_image_complement @inverse_image_composition : sets.
