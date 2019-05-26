Require Import List.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import StructTact.ListUtil.
Require Import StructTact.ListTactics.
Require Import StructTact.Before.

Set Implicit Arguments.

Section remove_all.
  Variable A : Type.
  Hypothesis A_eq_dec : forall x y : A, {x = y} + {x <> y}.

  Fixpoint remove_all (to_delete l : list A) : list A :=
    match to_delete with
    | [] => l
    | d :: ds => remove_all ds (remove A_eq_dec d l)
    end.

  Lemma in_remove_all_was_in :
    forall ds l x,
      In x (remove_all ds l) ->
      In x l.
  Proof using.
    induction ds; intros; simpl in *; intuition.
    eauto using in_remove.
  Qed.

  Lemma in_remove_all_preserve :
    forall ds l x,
      ~ In x ds ->
      In x l ->
      In x (remove_all ds l).
  Proof using.
    induction ds; intros; simpl in *; intuition auto using remove_preserve.
  Qed.

  Lemma in_remove_all_not_in :
    forall ds l x,
      In x (remove_all ds l) ->
      In x ds ->
      False.
  Proof using.
    induction ds; intros; simpl in *; intuition.
    - subst. find_apply_lem_hyp in_remove_all_was_in.
      eapply remove_In; eauto.
    - eauto.
  Qed.

  Lemma remove_all_nil :
    forall ys,
      remove_all ys [] = [].
  Proof using.
    intros. induction ys; simpl in *; intuition.
  Qed.

  Lemma remove_all_cons :
    forall ys a l,
      (remove_all ys (a :: l) = remove_all ys l /\
       In a ys) \/
      (remove_all ys (a :: l) = a :: (remove_all ys l) /\
       ~In a ys).
  Proof using.
    induction ys; intros; simpl in *; intuition.
    break_if; subst; simpl in *; intuition.
    specialize (IHys a0 (remove A_eq_dec a l)). intuition.
  Qed.

  Lemma before_remove_all :
    forall x y l ys,
      before x y (remove_all ys l) ->
      ~ In y ys ->
      before x y l.
  Proof using.
    induction l; intros; simpl in *; intuition.
    - rewrite remove_all_nil in *. simpl in *. intuition.
    - pose proof remove_all_cons ys a l. intuition.
      + repeat find_rewrite. right. intuition eauto.
        subst; intuition.
      + repeat find_rewrite. simpl in *. intuition eauto.
  Qed.

  Lemma before_remove_all_if :
    forall x y l xs,
      before x y l ->
      ~ In x xs ->
      before x y (remove_all xs l).
  Proof using.
    induction l; intros; simpl in *; intuition;
      pose proof remove_all_cons xs a l; subst; intuition;
        repeat find_rewrite; simpl in *; intuition.
  Qed.

  Lemma NoDup_remove_all :
    forall l l',
    NoDup l' ->
    NoDup (remove_all l l').
  Proof using.
    intros.
    induction l'.
    - rewrite remove_all_nil; auto.
    - invc_NoDup.
      concludes.
      pose proof remove_all_cons l a l'.
      break_or_hyp; break_and; find_rewrite; auto.
      constructor; auto.
      intro.
      find_apply_lem_hyp in_remove_all_was_in; auto.
  Qed.

  Lemma remove_all_NoDup_split :
    forall l l' l0 l1 a,
     NoDup l' ->
     remove_all l l' = l0 ++ a :: l1 ->
     remove_all l (remove A_eq_dec a l') = l0 ++ l1.
  Proof using.
    induction l'; intros; simpl in *.
    - find_rewrite_lem remove_all_nil.
      destruct l0; simpl in *; match goal with H: [] = _ |- _ => contradict H end; auto using nil_cons.
    - invc_NoDup.
      break_if; subst.
      * rewrite remove_not_in; auto.
        pose proof remove_all_cons l a l'.
        break_or_hyp; break_and.
        + find_rewrite.          
          match goal with H0: NoDup _, H1: _ = remove_all _ _ |- _ => specialize (IHl' _ _ _ H0 (eq_sym H1)) end.
          rewrite remove_not_in in IHl'; auto.
        + destruct l0; simpl in *; find_rewrite; find_injection; auto.
          assert (In a (remove_all l l')).
            match goal with H: _ = remove_all _ _ |- _ => rewrite <- H end.
            apply in_or_app.
            right; left; auto.
          find_apply_lem_hyp in_remove_all_was_in.
          intuition.
      * pose proof remove_all_cons l a l'.
        break_or_hyp; break_and; find_rewrite.
        + pose proof remove_all_cons l a (remove A_eq_dec a0 l').
          break_or_hyp; break_and; intuition.
          aggressive_rewrite_goal; auto.
        + destruct l0; simpl in *; find_injection; intuition.
          match goal with H0: NoDup _, H1: _ = remove_all _ _ |- _ => specialize (IHl' _ _ _ H0 (eq_sym H1)) end.
          rewrite <- IHl'.
          pose proof remove_all_cons l a (remove A_eq_dec a0 l').
          break_or_hyp; break_and; intuition.
  Qed.

  Lemma remove_all_app_l :
    forall xs ys zs,
      remove_all (xs ++ ys) zs = remove_all xs (remove_all ys zs).
  Proof using.
    induction zs; intros.
    - now repeat rewrite remove_all_nil.
    - pose proof (remove_all_cons (xs ++ ys) a zs).
      pose proof (remove_all_cons ys a zs).
      pose proof (remove_all_cons xs a (remove_all ys zs)).
      repeat (break_or_hyp; break_and); repeat find_rewrite;
      try find_eapply_lem_hyp in_app_or;
      try assert (In a (xs ++ ys)) by (eapply in_or_app; eauto);
      tauto.
  Qed.

  Lemma remove_all_app_r :
    forall xs ys zs,
      remove_all xs (ys ++ zs) = remove_all xs ys ++ remove_all xs zs.
  Proof using.
    induction xs.
    - auto.
    - intros.
      simpl.
      rewrite remove_app_comm.
      auto.
  Qed.

  Lemma remove_all_del_comm :
    forall xs ys zs,
      remove_all xs (remove_all ys zs) = remove_all ys (remove_all xs zs).
  Proof using.
    intros.
    induction zs; intros.
    - now repeat rewrite remove_all_nil.
    - pose proof (remove_all_cons xs a zs).
      pose proof (remove_all_cons ys a zs).
      pose proof (remove_all_cons ys a (remove_all xs zs)).
      pose proof (remove_all_cons xs a (remove_all ys zs)).
      repeat (break_or_hyp; break_and);
        repeat find_rewrite;
        congruence.
  Qed.

End remove_all.
Arguments in_remove_all_was_in : clear implicits.
