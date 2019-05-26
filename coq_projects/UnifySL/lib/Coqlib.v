Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Logic.ClassicalFacts.

Lemma prop_ext: prop_extensionality.
Proof.
  hnf; intros.
  set (A0 := fun x: unit => A).
  set (B0 := fun x: unit => B).
  assert (A0 = B0).
  + apply Extensionality_Ensembles.
    split; subst A0 B0; unfold Included, Ensembles.In; intros; tauto.
  + change A with (A0 tt).
    change B with (B0 tt).
    rewrite H0; auto.
Qed.

Lemma fin_subset_match {A B: Type} {P: A -> B -> Prop}: forall (X: Ensemble A) (Y: Ensemble B),
  (forall x, X x -> exists y, P x y /\ Y y) ->
  forall xs, Forall (fun x => X x) xs -> exists ys, Forall2 P xs ys /\ Forall (fun y => Y y) ys.
Proof.
  intros.
  induction xs as [| x0 xs].
  + exists nil; split; constructor.
  + inversion H0; subst.
    specialize (IHxs H4).
    destruct IHxs as [ys [? ?]].
    specialize (H x0 H3).
    destruct H as [y0 [? ?]].
    exists (y0 :: ys).
    split; constructor; auto.
Qed.

Lemma Forall2_lr_rev {A B: Type} {P: A -> B -> Prop}: forall xs ys,
  Forall2 (fun y x => P x y) ys xs ->
  Forall2 P xs ys.
Proof.
  intros.
  induction H; auto.
Qed.

(* This one copy from RamifyCoq *)
Lemma Forall_app_iff: forall {A : Type} (P : A -> Prop) (l1 l2 : list A), Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
Proof.
  intros; induction l1; intros.
  + simpl.
    assert (Forall P nil) by constructor; tauto.
  + simpl; split; intros.
    - inversion H; subst; split; try tauto.
      constructor; auto; tauto.
    - destruct H.
      inversion H; subst.
      constructor; auto; tauto.
Qed.

Inductive remove_rel {A: Type}: A -> list A -> list A -> Prop :=
| remove_rel_nil: forall a, remove_rel a nil nil
| remove_rel_cons_eq: forall a xs ys, remove_rel a xs ys -> remove_rel a (a :: xs) ys
| remove_rel_cons_neq: forall a b xs ys, a <> b -> remove_rel a xs ys -> remove_rel a (b :: xs) (b :: ys).

Lemma remove_rel_In: forall (A : Type) (l1 l2 : list A) (x : A), remove_rel x l1 l2 -> ~ In x l2.
Proof.
  intros.
  induction H.
  + intros [].
  + auto.
  + intros [|]; auto.
Qed.

Lemma remove_rel_exist: forall (A : Type) (l1 : list A) (x : A) (DEC: forall y, x = y \/ x <> y), exists l2, remove_rel x l1 l2.
Proof.
  intros.
  induction l1.
  + exists nil.
    apply remove_rel_nil.
  + destruct IHl1 as [l2 ?].
    destruct (DEC a).
    - exists l2; subst.
      apply remove_rel_cons_eq; auto.
    - exists (a :: l2); subst.
      apply remove_rel_cons_neq; auto.
Qed.

Lemma remove_rel_result_belong: forall (A : Type) (l1 l2 : list A) (x : A), remove_rel x l1 l2 -> Forall (fun y => In y l1) l2.
Proof.
  intros.
  induction H.
  + auto.
  + simpl.
    revert IHremove_rel; apply Forall_impl.
    intros; auto.
  + constructor; simpl; auto.
    revert IHremove_rel; apply Forall_impl.
    intros; auto.
Qed.

Definition isSome {A} (o: option A) := match o with Some _ => True | None => False end.

(* These three lemmas are copied from veric/assert_lemmas.v and veric/initial_world.v *)
Lemma nth_error_in_bounds: forall {A} (l: list A) i, (O <= i < length l)%nat
  -> exists x, nth_error l i = value x.
Proof.
intros until i; intros H.
revert i l H.
induction i; destruct l; intros; simpl in *;
  try solve [eauto | omega].
apply IHi; omega.
Qed.

Lemma nth_error_app: forall {T} (al bl : list T) (j: nat),
     nth_error (al++bl) (length al + j) = nth_error bl j.
Proof.
 intros. induction al; simpl; auto.
Qed.

Lemma nth_error_app1: forall {T} (al bl : list T) (j: nat),
     (j < length al)%nat ->
     nth_error (al++bl) j = nth_error al j.
Proof.
  intros. revert al H; induction j; destruct al; simpl; intros; auto; try omega.
   apply IHj. omega.
Qed.

Lemma nth_error_None_iff: forall {A} (l: list A) n, nth_error l n = None <-> n >= length l.
Proof.
  intros.
  revert n; induction l; intros; destruct n; simpl.
  + split; [intros _; omega | auto].
  + split; [intros _; omega | auto].
  + split; [intros; inversion H | omega].
  + rewrite IHl.
    omega.
Qed.

Lemma Forall_rev: forall {A} (P: A -> Prop) (l: list A), Forall P (rev l) <-> Forall P l.
Proof.
  intros.
  rewrite !Forall_forall.
  pose proof in_rev l.
  firstorder.
Qed.
