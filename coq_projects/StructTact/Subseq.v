Require Import Omega.
Require Import List.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import StructTact.ListTactics.
Require Import StructTact.FilterMap.
Require Import StructTact.RemoveAll.

Set Implicit Arguments.

Fixpoint subseq {A} (xs ys : list A) : Prop :=
  match xs, ys with
    | [], _ => True
    | x :: xs', y :: ys' => (x = y /\ subseq xs' ys') \/ subseq xs ys'
    | _, _ => False
  end.

Section subseq.
  Variable A B : Type.
  Hypothesis A_eq_dec : forall x y : A, {x = y} + {x <> y}.

  Lemma subseq_refl : forall (l : list A), subseq l l.
  Proof using.
    induction l; simpl; tauto.
  Qed.

  Lemma subseq_trans :
    forall (zs xs ys : list A),
      subseq xs ys ->
      subseq ys zs ->
      subseq xs zs.
  Proof using.
    induction zs; intros; simpl in *;
      repeat break_match; subst; simpl in *; intuition; subst; eauto;
        right; (eapply IHzs; [|eauto]); simpl; eauto.
  Qed.

  Lemma subseq_In :
    forall (ys xs : list A) x,
      subseq xs ys ->
      In x xs ->
      In x ys.
  Proof using.
    induction ys; intros.
    - destruct xs; simpl in *; intuition.
    - simpl in *. break_match; simpl in *; intuition; subst; intuition eauto;
                    right; (eapply IHys; [eauto| intuition]).
  Qed.

  Theorem subseq_NoDup :
    forall (ys xs : list A),
      subseq xs ys ->
      NoDup ys ->
      NoDup xs.
  Proof using.
    induction ys; intros.
    - destruct xs; simpl in *; intuition.
    - simpl in *. invc_NoDup.
      break_match.
      + constructor.
      + intuition.
        subst. constructor; eauto using subseq_In.
  Qed.

  Lemma subseq_remove :
    forall (x : A) xs,
      subseq (remove A_eq_dec x xs) xs.
  Proof using.
    induction xs; intros; simpl.
    - auto.
    - repeat break_match; auto.
      + intuition congruence.
      + find_inversion. auto.
  Qed.

  Lemma subseq_map :
    forall (f : A -> B) ys xs,
      subseq xs ys ->
      subseq (map f xs) (map f ys).
  Proof using.
    induction ys; intros; simpl in *.
    - repeat break_match; try discriminate; auto.
    - repeat break_match; try discriminate; auto.
      intuition.
      + subst. simpl in *. find_inversion. auto.
      + right. repeat find_reverse_rewrite. auto.
  Qed.

  Lemma subseq_cons_drop :
    forall xs ys (a : A),
      subseq (a :: xs) ys -> subseq xs ys.
  Proof using.
    induction ys; intros; simpl in *; intuition; break_match; eauto.
  Qed.

  Lemma subseq_length :
    forall (ys xs : list A),
      subseq xs ys ->
      length xs <= length ys.
  Proof using.
    induction ys; intros; simpl in *; break_match; intuition.
    subst. simpl in *. specialize (IHys l). concludes. auto with *.
  Qed.

  Lemma subseq_subseq_eq :
    forall (xs ys : list A),
      subseq xs ys ->
      subseq ys xs ->
      xs = ys.
  Proof using.
    induction xs; intros; destruct ys; simpl in *;
      intuition eauto using f_equal2, subseq_cons_drop.
    exfalso.
    repeat find_apply_lem_hyp subseq_length.
    simpl in *. omega.
  Qed.

  Lemma subseq_filter :
    forall (f : A -> bool) xs,
      subseq (filter f xs) xs.
  Proof using.
    induction xs; intros; simpl.
    - auto.
    - repeat break_match; intuition congruence.
  Qed.

  Lemma subseq_nil :
    forall xs,
      subseq (A:=A) [] xs.
  Proof using.
    destruct xs; simpl; auto.
  Qed.

  Lemma subseq_skip :
    forall a xs ys,
      subseq(A:=A) xs ys ->
      subseq xs (a :: ys).
  Proof using.
    induction ys; intros; simpl in *; repeat break_match; intuition.
  Qed.

  Lemma subseq_filterMap :
    forall (f : B -> option A) ys xs,
      subseq xs ys ->
      subseq (filterMap f xs) (filterMap f ys).
  Proof using.
    induction ys; intros; simpl in *; repeat break_match; auto; try discriminate; intuition; subst.
    - simpl. find_rewrite. auto.
    - auto using subseq_skip.
    - auto using subseq_nil.
    - simpl. find_rewrite. auto.
  Qed.

  Lemma subseq_app_r :
    forall xs ys,
      subseq (A:=A) ys (xs ++ ys).
  Proof using.
    induction xs; intros; simpl.
    + auto using subseq_refl.
    + break_match.
      * auto.
      * right. auto using subseq_nil.
  Qed.

  Lemma subseq_app_tail :
    forall ys xs zs,
      subseq (A:=A) xs ys ->
      subseq (xs ++ zs) (ys ++ zs).
  Proof using.
    induction ys; intros; simpl in *.
    - break_match; intuition auto using subseq_refl.
    - repeat break_match.
      + auto.
      + discriminate.
      + simpl in *. subst. right. auto using subseq_app_r.
      + simpl in *. find_inversion. intuition.
        rewrite app_comm_cons. auto.
  Qed.

  Lemma subseq_app_head :
    forall xs ys zs,
      subseq (A:=A) ys zs ->
      subseq (A:=A) (xs ++ ys) (xs ++ zs).
  Proof using.
    induction xs; intros; simpl; intuition.
  Qed.

  Lemma subseq_2_3 :
    forall xs ys zs x y,
      subseq(A:=A) (xs ++ ys ++ zs) (xs ++ x :: ys ++ y :: zs).
  Proof using.
    auto using subseq_refl, subseq_skip, subseq_app_head.
  Qed.

  Lemma subseq_middle :
    forall xs y zs,
      subseq (A:=A) (xs ++ zs) (xs ++ y :: zs).
  Proof using.
    intros.
    apply subseq_app_head.
    apply subseq_skip.
    apply subseq_refl.
  Qed.

  Lemma subseq_remove_all :
    forall (ds l l' : list A),
      subseq l l' ->
      subseq (remove_all A_eq_dec ds l) l'.
  Proof using.
    induction ds; intros; simpl.
    - auto.
    - apply IHds.
      eapply subseq_trans.
      apply subseq_remove.
      auto.
  Qed.
End subseq.
