Require Export Families.
Require Export Image.
Require Import ImageImplicit.

Set Implicit Arguments.

Section IndexedFamilies.

Variable A T:Type.
Definition IndexedFamily := A -> Ensemble T.
Variable F:IndexedFamily.

Inductive IndexedUnion : Ensemble T :=
  | indexed_union_intro: forall (a:A) (x:T),
    In (F a) x -> In IndexedUnion x.

Inductive IndexedIntersection : Ensemble T :=
  | indexed_intersection_intro: forall (x:T),
    (forall a:A, In (F a) x) -> In IndexedIntersection x.

End IndexedFamilies.

Section IndexedFamilyFacts.

(* unions and intersections over subsets of the index set *)
Lemma sub_indexed_union: forall {A B T:Type} (f:A->B)
  (F:IndexedFamily B T),
  let subF := (fun a:A => F (f a)) in
    Included (IndexedUnion subF) (IndexedUnion F).
Proof.
unfold Included.
intros.
destruct H.
apply indexed_union_intro with (f a).
assumption.
Qed.

Lemma sub_indexed_intersection: forall {A B T:Type} (f:A->B)
  (F:IndexedFamily B T),
  let subF := (fun a:A => F (f a)) in
    Included (IndexedIntersection F) (IndexedIntersection subF).
Proof.
unfold Included.
intros.
constructor.
destruct H.
intro.
apply H.
Qed.

Lemma empty_indexed_intersection: forall {T:Type}
  (F:IndexedFamily False T),
  IndexedIntersection F = Full_set.
Proof.
intros.
apply Extensionality_Ensembles; red; split; red; intros;
  auto with sets.
constructor.
constructor.
destruct a.
Qed.

Lemma empty_indexed_union: forall {T:Type}
  (F:IndexedFamily False T),
  IndexedUnion F = Empty_set.
Proof.
intros.
apply Extensionality_Ensembles; red; split; red; intros.
destruct H.
destruct a.
destruct H.
Qed.

End IndexedFamilyFacts.

Section IndexedFamilyToFamily.

(* relation to families of subsets of T *)
Variable T:Type.
Variable A:Type.
Variable F:IndexedFamily A T.

Definition ImageFamily : Family T :=
  Im Full_set F.

Lemma indexed_to_family_union: IndexedUnion F = FamilyUnion ImageFamily.
Proof.
apply Extensionality_Ensembles.
unfold Same_set.
unfold Included.
intuition.
destruct H.
apply family_union_intro with (F a).
apply Im_intro with a.
constructor.
reflexivity.
assumption.

destruct H.
destruct H.
apply indexed_union_intro with x0.
rewrite <- H1.
assumption.
Qed.

Lemma indexed_to_family_intersection:
  IndexedIntersection F = FamilyIntersection ImageFamily.
Proof.
apply Extensionality_Ensembles.
unfold Same_set.
unfold Included.
intuition.
constructor.
intros.
destruct H.
destruct H0.
rewrite H1.
apply H.

constructor.
intro.
destruct H.
apply H.
apply Im_intro with a.
constructor.
reflexivity.
Qed.

End IndexedFamilyToFamily.
