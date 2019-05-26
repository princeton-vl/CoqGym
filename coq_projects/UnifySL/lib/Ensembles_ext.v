(* This file is copied from RamifyCoq project. *)

Require Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Export Coq.Classes.Equivalence.
Require Export Coq.Sets.Ensembles.
Require Import Coq.Sets.Constructive_sets.
Require Import Logic.lib.Coqlib.

Lemma Full_set_spec: forall A (v: A), Full_set A v <-> True.
Proof.
  intros.
  split; intros; constructor.
Qed.

Lemma Empty_set_spec: forall A (v: A), Empty_set A v <-> False.
  intros.
  split; intros [].
Qed.

Lemma Intersection_spec: forall A (v: A) P Q, Intersection _ P Q v <-> P v /\ Q v.
Proof.
  intros.
  split; intros.
  + inversion H; auto.
  + constructor; tauto.
Qed.

Lemma Union_spec: forall A (v: A) P Q, Union _ P Q v <-> P v \/ Q v.
Proof.
  intros.
  split; intros.
  + inversion H; auto.
  + destruct H; [apply Union_introl | apply Union_intror]; auto.
Qed.

Lemma Disjoint_spec: forall A P Q, Disjoint A P Q <-> (forall x, P x -> Q x -> False).
Proof.
  intros; split; intros.
  + inversion H.
    eapply H2.
    unfold In; rewrite Intersection_spec; split; eauto.
  + constructor.
    intros.
    unfold In; rewrite Intersection_spec.
    intro; apply H with x; tauto.
Qed.

Lemma Singleton_spec: forall U x y, (Singleton U x) y <-> x = y.
Proof.
  intros; split; intro.
  + inversion H; auto.
  + subst; constructor.
Qed.

Lemma Included_Full_set: forall A P, Included A P (Full_set A).
Proof.
  intros.
  hnf; unfold In; intros.
  apply Full_set_spec; auto.
Qed.

Lemma Intersection_Complement: forall A (P Q: Ensemble A),
  Same_set A
  (Intersection A (Complement A P) (Complement A Q))
  (Complement A (Union A P Q)).
Proof.
  intros.
  unfold Same_set, Included, Complement, Ensembles.In.
  split; intros.
  + rewrite Union_spec.
    rewrite Intersection_spec in H.
    tauto.
  + rewrite Union_spec in H.
    rewrite Intersection_spec.
    tauto.
Qed.

Lemma Union_iff: forall U A B x, Ensembles.In U (Union U A B) x <-> Ensembles.In U A x \/ Ensembles.In U B x.
Proof.
  intros; split; intros.
  + apply Constructive_sets.Union_inv; auto.
  + destruct H; [apply Union_introl | apply Union_intror]; auto.
Qed.

Lemma Empty_set_iff: forall U x, Ensembles.In U (Empty_set U) x <-> False.
Proof.
  intros; split; intro; inversion H.
Qed.

Lemma Singleton_iff: forall U x y, Ensembles.In U (Singleton U x) y <-> x = y.
Proof.
  intros; split; intro.
  + inversion H; auto.
  + subst; constructor.
Qed.

Arguments Included {U} B C.
Arguments Same_set {U} B C.

Lemma Same_set_refl: forall A (S : Ensemble A), Same_set S S. Proof. intros; split; intro; tauto. Qed.

Lemma Same_set_sym: forall A (S1 S2 : Ensemble A), Same_set S1 S2 -> Same_set S2 S1. Proof. intros; destruct H; split; auto. Qed.

Lemma Same_set_trans: forall A (S1 S2 S3: Ensemble A), Same_set S1 S2 -> Same_set S2 S3 -> Same_set S1 S3.
Proof. intros; destruct H, H0; split; repeat intro; [apply H0, H, H3 | apply H1, H2, H3]. Qed.

Add Parametric Relation {A} : (Ensemble A) Same_set
    reflexivity proved by (Same_set_refl A)
    symmetry proved by (Same_set_sym A)
    transitivity proved by (Same_set_trans A) as Same_set_rel.

Lemma Same_set_spec: forall A P Q, Same_set P Q <-> (pointwise_relation A iff) P Q.
Proof.
  intros.
  unfold Same_set, Included, In, pointwise_relation.
  firstorder.
Qed.

Lemma Complement_Empty_set: forall A, Same_set (Complement A (Empty_set _)) (Full_set _).
Proof.
  intros.
  rewrite Same_set_spec.
  intro a.
  unfold Complement, Ensembles.In.
  pose proof Empty_set_iff _ a.
  pose proof Full_set_spec _ a.
  tauto.
Qed.

Lemma Intersection_comm: forall A P Q, Same_set (Intersection A P Q) (Intersection A Q P).
Proof.
  intros.
  rewrite Same_set_spec; hnf; intros.
  rewrite !Intersection_spec.
  tauto.
Qed.

Lemma Intersection_assoc: forall A P Q R, Same_set (Intersection A (Intersection A P Q) R) (Intersection A P (Intersection A Q R)).
Proof.
  intros.
  rewrite Same_set_spec; hnf; intros.
  rewrite !Intersection_spec.
  tauto.
Qed.

Lemma Union_comm: forall A P Q, Same_set (Union A P Q) (Union A Q P).
Proof.
  intros.
  rewrite Same_set_spec; hnf; intros.
  rewrite !Union_spec.
  tauto.
Qed.

Lemma Union_assoc: forall A P Q R, Same_set (Union A (Union A P Q) R) (Union A P (Union A Q R)).
Proof.
  intros.
  rewrite Same_set_spec; hnf; intros.
  rewrite !Union_spec.
  tauto.
Qed.

Lemma Intersection_Union_distr_l: forall A P Q R,
  Same_set (Intersection A (Union A Q R) P)
   (Union A (Intersection A Q P) (Intersection A R P)).
Proof.
  intros.
  rewrite Same_set_spec; intro x.
  rewrite !Intersection_spec, !Union_spec, !Intersection_spec.
  tauto.
Qed.

Lemma Intersection_Union_distr_r: forall A P Q R,
  Same_set (Intersection A P (Union A Q R))
   (Union A (Intersection A P Q) (Intersection A P R)).
Proof.
  intros.
  rewrite Same_set_spec; intro x.
  rewrite !Intersection_spec, !Union_spec, !Intersection_spec.
  tauto.
Qed.

Instance Included_proper (V: Type): Proper (Same_set ==> Same_set ==> iff) (@Included V).
Proof.
  hnf; intros.
  hnf; intros.
  rewrite Same_set_spec in *.
  unfold pointwise_relation, Included, Ensembles.In in *.
  firstorder.
Defined.

Instance complement_proper (V: Type): Proper (Same_set ==> Same_set) (Complement V).
  hnf; intros.
  rewrite Same_set_spec in *.
  hnf; intros.
  unfold Complement, Ensembles.In.
  specialize (H a).
  tauto.
Defined.

Instance Union_proper (V: Type): Proper (Same_set ==> Same_set ==> Same_set) (Union V).
  hnf; intros.
  hnf; intros.
  rewrite Same_set_spec in *.
  unfold pointwise_relation in *; intros.
  rewrite !Union_spec.
  firstorder.
Defined.

Instance Disjoint_proper (V: Type): Proper (Same_set ==> Same_set ==> iff) (Disjoint V).
  hnf; intros.
  hnf; intros.
  rewrite Same_set_spec in *.
  unfold pointwise_relation in *.
  rewrite !Disjoint_spec.
  firstorder.
Defined.

Lemma Union_Included {A: Type}: forall P Q R, Included (Union A P Q) R <-> Included P R /\ Included Q R.
Proof.
  intros.
  unfold Included.
  pose proof Union_iff A P Q.
  firstorder.
Qed.

Lemma left_Included_Union {A: Type}: forall P Q, Included P (Union A P Q).
Proof.
  intros.
  intros ? ?.
  rewrite Union_iff.
  tauto.
Qed.

Lemma right_Included_Union {A: Type}: forall P Q, Included Q (Union A P Q).
Proof.
  intros.
  intros ? ?.
  rewrite Union_iff.
  tauto.
Qed.

Lemma Union_Empty_left {A: Type}: forall P, Same_set (Union _ (Empty_set A) P) P.
Proof.
  intros.
  rewrite Same_set_spec.
  hnf; intros.
  rewrite Union_spec.
  pose proof Noone_in_empty A a.
  tauto.
Qed.

Lemma Union_Empty_right {A: Type}: forall P, Same_set (Union _ P (Empty_set A)) P.
Proof.
  intros.
  rewrite Same_set_spec.
  hnf; intros.
  rewrite Union_spec.
  pose proof Noone_in_empty A a.
  tauto.
Qed.

Lemma Intersection_Full_left {A: Type}: forall P, Same_set (Intersection _ (Full_set A) P) P.
Proof.
  intros.
  rewrite Same_set_spec.
  hnf; intros.
  rewrite Intersection_spec.
  pose proof Full_set_spec A a.
  tauto.
Qed.

Lemma Intersection_Full_right {A: Type}: forall P, Same_set (Intersection _ P (Full_set A)) P.
Proof.
  intros.
  rewrite Same_set_spec.
  hnf; intros.
  rewrite Intersection_spec.
  pose proof Full_set_spec A a.
  tauto.
Qed.

Lemma Intersection_Empty_left {A: Type}: forall P, Same_set (Intersection _ (Empty_set A) P) (Empty_set A).
Proof.
  intros.
  rewrite Same_set_spec.
  hnf; intros.
  rewrite Intersection_spec.
  pose proof Empty_set_spec A a.
  tauto.
Qed.

Lemma Intersection_Empty_right {A: Type}: forall P, Same_set (Intersection _ P (Empty_set A)) (Empty_set A).
Proof.
  intros.
  rewrite Same_set_spec.
  hnf; intros.
  rewrite Intersection_spec.
  pose proof Empty_set_spec A a.
  tauto.
Qed.

Lemma Intersection_absort_right: forall U (A B: Ensemble U), Included A B -> Same_set (Intersection _ A B) A.
Proof.
  intros.
  rewrite Same_set_spec; intro x.
  rewrite Intersection_spec.
  specialize (H x); unfold Ensembles.In in H.
  tauto.
Qed.

Lemma Intersection_absort_left: forall U (A B: Ensemble U), Included B A -> Same_set (Intersection _ A B) B.
Proof.
  intros.
  rewrite Same_set_spec; intro x.
  rewrite Intersection_spec.
  specialize (H x); unfold Ensembles.In in H.
  tauto.
Qed.

Lemma Complement_Included_rev: forall (U: Type) P Q, Included P Q -> Included (Complement U Q) (Complement U P).
Proof.
  unfold Included, Complement, Ensembles.In.
  intros.
  firstorder.
Qed.

Instance Intersection_proper {A}: Proper (Same_set ==> Same_set ==> Same_set) (Intersection A).
Proof.
  do 2 (hnf; intros).
  rewrite Same_set_spec in *.
  intro a; specialize (H0 a); specialize (H a).
  rewrite !Intersection_spec.
  tauto.
Defined.

Lemma Included_Disjoint: forall A P Q P' Q',
  Included P P' ->
  Included Q Q' ->
  Disjoint A P' Q' ->
  Disjoint A P Q.
Proof.
  intros.
  rewrite Disjoint_spec in H1 |- *.
  intros; apply (H1 x).
  + apply H; auto.
  + apply H0; auto.
Qed.

Lemma Union_left_Disjoint: forall A P Q R,
  Disjoint A (Union A P Q) R <-> Disjoint A P R /\ Disjoint A Q R.
Proof.
  intros.
  rewrite !Disjoint_spec.
  pose proof (fun x => Union_spec A x P Q).
  firstorder.
Qed.

Lemma Union_right_Disjoint: forall A P Q R,
  Disjoint A R (Union A P Q) <-> Disjoint A R P /\ Disjoint A R Q.
Proof.
  intros.
  rewrite !Disjoint_spec.
  pose proof (fun x => Union_spec A x P Q).
  firstorder.
Qed.

Lemma Included_Complement_Disjoint: forall A P Q,
  (Included P (Complement _ Q)) <-> Disjoint A P Q.
Proof.
  intros.
  unfold Included, Complement, In.
  rewrite Disjoint_spec.
  firstorder.
Qed.

Lemma Disjoint_comm: forall A P Q,
  Disjoint A P Q <-> Disjoint A Q P.
Proof.
  intros.
  rewrite !Disjoint_spec.
  firstorder.
Qed.

Lemma Disjoint_Empty_set_right: forall {A} (P: Ensemble A), Disjoint A P (Empty_set A).
Proof.
  intros.
  rewrite Disjoint_comm.
  apply Included_Complement_Disjoint.
  apply Constructive_sets.Included_Empty.
Qed.

Lemma Disjoint_Empty_set_left: forall {A} (P: Ensemble A), Disjoint A (Empty_set A) P.
Proof.
  intros.
  apply Included_Complement_Disjoint.
  apply Constructive_sets.Included_Empty.
Qed.

Lemma Included_trans: forall {A} (P Q R: Ensemble A), Included P Q -> Included Q R -> Included P R.
Proof.
  unfold Included, Ensembles.In.
  intros; firstorder.
Qed.

Lemma Intersection1_Included: forall {A} P Q R, Included P R -> Included (Intersection A P Q) R.
Proof.
  unfold Included, Ensembles.In.
  intros.
  rewrite Intersection_spec in H0.
  firstorder.
Qed.

Lemma Intersection2_Included: forall {A} P Q R, Included Q R -> Included (Intersection A P Q) R.
Proof.
  unfold Included, Ensembles.In.
  intros.
  rewrite Intersection_spec in H0.
  firstorder.
Qed.

Lemma Included_refl: forall A P, @Included A P P.
Proof.
  intros; hnf; auto.
Qed.

Definition app_same_set {A: Type} {P Q: Ensemble A} (H: Same_set P Q) (x: A): P x <-> Q x := proj1 (Same_set_spec A P Q) H x.

Coercion app_same_set : Same_set >-> Funclass.

(* TODO: rename it into preimage set *)
Definition respectful_set {A B: Type} (X: Ensemble B) (f: A -> B): Ensemble A := fun x => X (f x).

Inductive image_set {A B: Type}: Ensemble A -> (A -> B) -> Ensemble B :=
  | image_set_intro: forall (X: Ensemble A) (f: A -> B) (x: A), X x -> image_set X f (f x).

Lemma image_set_spec: forall {A B: Type} f X (y: B),
  image_set X f y <-> exists x: A, X x /\ y = f x.
Proof.
  intros.
  split; intros.
  + inversion H; subst.
    exists x.
    split; auto.
  + destruct H as [x [?H ?H]].
    subst.
    constructor; auto.
Qed.

Instance respectful_set_proper {A B: Type}: Proper (Same_set ==> pointwise_relation A (@eq B) ==> Same_set) respectful_set.
Proof.
  intros.
  do 2 (hnf; intros).
  rewrite Same_set_spec in *.
  unfold pointwise_relation in *.
  unfold respectful_set.
  firstorder.
  + rewrite <- H, <- H0; firstorder.
  + rewrite H, H0; firstorder.
Qed.

Instance image_set_proper2 {A B: Type}: Proper (Same_set ==> eq ==> Same_set) (@image_set A B).
Proof.
  intros.
  do 2 (hnf; intros).
  rewrite Same_set_spec in *.
  unfold pointwise_relation in *.
  intros.
  rewrite !image_set_spec.
  firstorder.
  + subst. firstorder.
  + subst. firstorder.
Qed.

Lemma resp_Included: forall {A B: Type} (X Y: Ensemble B) (f: A -> B),
  Included X Y ->
  Included (respectful_set X f) (respectful_set Y f).
Proof.
  intros.
  unfold respectful_set, Included, In.
  intro x.
  apply H.
Qed.

Lemma resp_Same_set: forall {A B: Type} (X Y: Ensemble B) (f: A -> B),
  Same_set X Y ->
  Same_set (respectful_set X f) (respectful_set Y f).
Proof.
  intros.
  unfold Same_set in *.
  split; apply resp_Included; tauto.
Qed.

Lemma resp_Intersection: forall {A B: Type} (X Y: Ensemble B) (f: A -> B),
  Same_set
   (respectful_set (Intersection _ X Y) f)
   (Intersection _ (respectful_set X f) (respectful_set Y f)).
Proof.
  intros.
  rewrite Same_set_spec; intros x.
  unfold respectful_set.
  rewrite !Intersection_spec.
  reflexivity.
Qed.

Lemma resp_Union: forall {A B: Type} (X Y: Ensemble B) (f: A -> B) ,
  Same_set
   (respectful_set (Union _ X Y) f)
   (Union _ (respectful_set X f) (respectful_set Y f)).
Proof.
  intros.
  rewrite Same_set_spec; intros x.
  unfold respectful_set.
  rewrite !Union_spec.
  reflexivity.
Qed.

Lemma resp_Complement: forall {A B: Type} (X: Ensemble B) (f: A -> B),
  Same_set
   (respectful_set (Complement _ X) f)
   (Complement _ (respectful_set X f)).
Proof.
  intros.
  rewrite Same_set_spec; intros x.
  unfold respectful_set, Complement, In.
  reflexivity.
Qed.

Lemma resp_Disjoint: forall {A B: Type} (X Y: Ensemble B) (f: A -> B),
  Disjoint _ X Y ->
  Disjoint _ (respectful_set X f) (respectful_set Y f).
Proof.
  intros.
  rewrite <- Included_Complement_Disjoint in *.
  rewrite <- resp_Complement.
  apply resp_Included; auto.
Qed.

Lemma resp_Empty: forall {A B: Type} (f: A -> B),
  Same_set (respectful_set (Empty_set _) f) (Empty_set _).
Proof.
  intros.
  rewrite Same_set_spec.
  intro x.
  pose proof Noone_in_empty A.
  pose proof Noone_in_empty B.
  firstorder.
Qed.

Lemma image_Included: forall {A B: Type} (f: A -> B) (X Y: Ensemble A),
  Included X Y ->
  Included (image_set X f) (image_set Y f).
Proof.
  intros.
  unfold Included, In.
  intro y.
  rewrite !image_set_spec.
  intros [x [? ?]].
  exists x; split; auto.
  apply H; auto.
Qed.

Lemma image_Same_set: forall {A B: Type} (f: A -> B) (X Y: Ensemble A),
  Same_set X Y ->
  Same_set (image_set X f) (image_set Y f).
Proof.
  intros.
  unfold Same_set in *.
  split; apply image_Included; tauto.
Qed.

Lemma image_Intersection: forall {A B: Type} (X Y: Ensemble A) (f: A -> B),
  Included
   (image_set (Intersection _ X Y) f)
   (Intersection _ (image_set X f) (image_set Y f)).
Proof.
  intros.
  unfold Included, In; intros y.
  rewrite !Intersection_spec, !image_set_spec.
  intros [x [? ?]].
  rewrite Intersection_spec in H.
  split; exists x; tauto.
Qed.

Lemma image_Union: forall {A B: Type} (X Y: Ensemble A) (f: A -> B),
  Same_set
   (image_set (Union _ X Y) f)
   (Union _ (image_set X f) (image_set Y f)).
Proof.
  intros.
  rewrite Same_set_spec; intros y.
  rewrite !Union_spec, !image_set_spec.
  pose proof (fun x => Union_spec A x X Y).
  firstorder.
Qed.

Lemma image_Disjoint_rev: forall {A B: Type} (X Y: Ensemble A) (f: A -> B),
  Disjoint _ (image_set X f) (image_set Y f) ->
  Disjoint _ X Y.
Proof.
  intros.
  rewrite Disjoint_spec in *.
  intros x ? ?.
  apply (H (f x)); constructor; auto.
Qed.

Lemma image_Empty: forall {A B: Type} (f: A -> B),
  Same_set (image_set (Empty_set _) f) (Empty_set _).
Proof.
  intros.
  rewrite Same_set_spec.
  intro x.
  rewrite image_set_spec.
  pose proof Noone_in_empty A.
  pose proof Noone_in_empty B.
  firstorder.
Qed.

Lemma image_single: forall {A B: Type} (a: A) (f: A -> B),
  Same_set (image_set (eq a) f) (eq (f a)).
Proof.
  intros.
  rewrite Same_set_spec.
  intro x.
  rewrite image_set_spec.
  split; intros; eauto.
  destruct H as [? [? ?]]; subst; auto.
Qed.

Definition Countable_Union (A: Type) (P: nat -> Ensemble A) : Ensemble A :=
  fun x => exists i, P i x.

Definition Non_Empty {U: Type} (A: Ensemble U): Prop := exists x, A x.

Definition Binart_set_list (U: Type) (A B: Ensemble U): nat -> Ensemble U :=
  fun n => match n with | 0 => A | 1 => B | _ => Empty_set _ end.

Lemma Union_is_Countable_Union: forall {U: Type} (A B: Ensemble U),
  Same_set (Union _ A B) (Countable_Union _ (Binart_set_list _ A B)).
Proof.
  intros.
  rewrite Same_set_spec.
  intros x.
  rewrite Union_spec; unfold Countable_Union.
  split.
  + intros [? | ?].
    - exists 0; auto.
    - exists 1; auto.
  + intros [[ | [ | ]] ?].
    - left; auto.
    - right; auto.
    - intros; inversion H.
Qed.

Lemma Intersection_is_Complement_Union (classic: forall P: Prop, P \/ ~ P): forall {U: Type} (A B: Ensemble U),
  Same_set (Intersection _ A B) (Complement _ (Union _ (Complement _ A) (Complement _ B))).
Proof.
  intros.
  rewrite Same_set_spec.
  intros x; unfold Complement, Ensembles.In.
  rewrite Union_spec, Intersection_spec.
  destruct (classic (A x)), (classic (B x)); tauto.
Qed.

Arguments Included: clear implicits.
Arguments Same_set: clear implicits.
