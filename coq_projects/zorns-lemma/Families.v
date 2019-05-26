Require Export Ensembles.
Require Import EnsemblesImplicit.

Set Implicit Arguments.

Section Families.

Variable T:Type.
Definition Family := Ensemble (Ensemble T).
Variable F:Family.

Inductive FamilyUnion: Ensemble T :=
  | family_union_intro: forall (S:Ensemble T) (x:T),
    In F S -> In S x -> In FamilyUnion x.

Inductive FamilyIntersection: Ensemble T :=
  | family_intersection_intro: forall x:T,
    (forall S:Ensemble T, In F S -> In S x) ->
    In FamilyIntersection x.

End Families.

Section FamilyFacts.

Variable T:Type.

Lemma empty_family_union: FamilyUnion (@Empty_set (Ensemble T)) =
                          Empty_set.
Proof.
apply Extensionality_Ensembles.
unfold Same_set.
unfold Included.
intuition.
destruct H.
contradiction H.

contradiction H.
Qed.

Lemma empty_family_intersection:
  FamilyIntersection (@Empty_set (Ensemble T)) = Full_set.
Proof.
apply Extensionality_Ensembles.
unfold Same_set.
unfold Included.
intuition.
constructor.
constructor.
intros.
contradiction H0.
Qed.

(* unions and intersections of subfamilies *)

Lemma subfamily_union: forall F G:Family T, Included F G ->
  Included (FamilyUnion F) (FamilyUnion G).
Proof.
unfold Included.
intros.
destruct H0.
apply family_union_intro with S.
apply H.
assumption.
assumption.
Qed.

Lemma subfamily_intersection: forall F G:Family T, Included F G ->
  Included (FamilyIntersection G) (FamilyIntersection F).
Proof.
unfold Included.
intros.
constructor.
destruct H0.
intros.
apply H0.
apply H.
assumption.
Qed.

End FamilyFacts.
