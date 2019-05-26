Require Import List.
Import ListNotations.
Require Import StructTact.StructTactics.

Set Implicit Arguments.

Section assoc.
  Variable K V : Type.
  Variable K_eq_dec : forall k k' : K, {k = k'} + {k <> k'}.

  Fixpoint assoc (l : list (K * V)) (k : K) : option V :=
    match l with
      | [] => None
      | (k', v) :: l' =>
        if K_eq_dec k k' then
          Some v
        else
          assoc l' k
    end.

  Definition assoc_default (l : list (K * V)) (k : K) (default : V) : V :=
    match (assoc l k) with
      | Some x => x
      | None => default
    end.

  Fixpoint assoc_set (l : list (K * V)) (k : K) (v : V) : list (K * V) :=
    match l with
      | [] => [(k, v)]
      | (k', v') :: l' =>
        if K_eq_dec k k' then
          (k, v) :: l'
        else
          (k', v') :: (assoc_set l' k v)
    end.

  Fixpoint assoc_del (l : list (K * V)) (k : K) : list (K * V) :=
    match l with
      | [] => []
      | (k', v') :: l' =>
        if K_eq_dec k k' then
          assoc_del l' k
        else
          (k', v') :: (assoc_del l' k)
    end.

  Lemma get_set_same :
    forall k v l,
      assoc (assoc_set l k v) k = Some v.
  Proof using.
    induction l; intros; simpl; repeat (break_match; simpl); subst; congruence.
  Qed.

  Lemma get_set_same' :
    forall k k' v l,
      k = k' ->
      assoc (assoc_set l k v) k' = Some v.
  Proof using.
    intros. subst. auto using get_set_same.
  Qed.

  Lemma get_set_diff :
    forall k k' v l,
      k <> k' ->
      assoc (assoc_set l k v) k' = assoc l k'.
  Proof using.
    induction l; intros; simpl; repeat (break_match; simpl); subst; try congruence; auto.
  Qed.

  Lemma not_in_assoc :
    forall k l,
      ~ In k (map (@fst _ _) l) ->
      assoc l k = None.
  Proof using.
    intros.
    induction l.
    - auto.
    - simpl in *. repeat break_match; intuition.
      subst. simpl in *. congruence.
  Qed.

  Lemma get_del_same :
    forall k l,
      assoc (assoc_del l k) k = None.
  Proof using.
    induction l; intros; simpl in *.
    - auto.
    - repeat break_match; subst; simpl in *; auto.
      break_if; try congruence.
  Qed.

  Lemma get_del_diff :
    forall k k' l,
      k <> k' ->
      assoc (assoc_del l k') k = assoc l k.
  Proof using.
    induction l; intros; simpl in *.
    - auto.
    - repeat (break_match; simpl); subst; try congruence; auto.
  Qed.

  Lemma get_set_diff_default :
    forall (k k' : K) (v : V) l d,
      k <> k' ->
      assoc_default (assoc_set l k v) k' d = assoc_default l k' d.
  Proof using.
    unfold assoc_default.
    intros.
    repeat break_match; auto;
    rewrite get_set_diff in * by auto; congruence.
  Qed.

  Lemma get_set_same_default :
    forall (k : K) (v : V) l d,
      assoc_default (assoc_set l k v) k d = v.
  Proof using.
    unfold assoc_default.
    intros.
    repeat break_match; auto;
    rewrite get_set_same in *; congruence.
  Qed.

  Lemma assoc_assoc_default:
    forall l k (v : V) d,
      assoc l k = Some v ->
      assoc_default l k d = v.
  Proof using.
    intros. unfold assoc_default.
    break_match; congruence.
  Qed.

  Lemma assoc_assoc_default_missing:
    forall (l : list (K * V)) k d,
      assoc l k = None ->
      assoc_default l k d = d.
  Proof using.
    intros. unfold assoc_default.
    break_match; congruence.
  Qed.

  Lemma assoc_set_same :
    forall (l : list (K * V)) k v,
      assoc l k = Some v ->
      assoc_set l k v = l.
  Proof using.
    intros. induction l; simpl in *; auto; try congruence.
    repeat break_match; simpl in *; intuition.
    - subst. find_inversion. auto.
    - repeat find_rewrite. auto.
  Qed.

  Lemma assoc_default_assoc_set :
    forall l (k : K) (v : V) d,
      assoc_default (assoc_set l k v) k d = v.
  Proof using.
    intros. unfold assoc_default.
    rewrite get_set_same. auto.
  Qed.

  Lemma assoc_set_assoc_set_same :
    forall l (k : K) (v : V) v',
      assoc_set (assoc_set l k v) k v' = assoc_set l k v'.
  Proof using.
    induction l; intros; simpl in *; repeat break_match; simpl in *; subst; try congruence; eauto;
break_if; congruence.
  Qed.

  Definition a_equiv (l1 : list (K * V)) l2 :=
    forall k,
      assoc l1 k = assoc l2 k.

  Lemma a_equiv_refl :
    forall l,
      a_equiv l l.
  Proof using.
    intros. unfold a_equiv. auto.
  Qed.

  Lemma a_equiv_sym :
    forall l l',
      a_equiv l l' ->
      a_equiv l' l.
  Proof using.
    unfold a_equiv. intros. auto.
  Qed.

  Lemma a_equiv_trans :
    forall l l' l'',
      a_equiv l l' ->
      a_equiv l' l'' ->
      a_equiv l l''.
  Proof using.
    unfold a_equiv in *.
    intros. repeat find_higher_order_rewrite.
    auto.
  Qed.

  Ltac assoc_destruct :=
    match goal with
    | [ |- context [assoc (assoc_set _ ?k0' _) ?k0 ] ] =>
      destruct (K_eq_dec k0 k0'); [subst k0'; rewrite get_set_same with (k := k0)|
                                   rewrite get_set_diff with (k' := k0) by auto]
    end.

  Ltac assoc_rewrite :=
    match goal with
    | [  |- context [assoc (assoc_set _ ?k0' _) ?k0 ] ] =>
      first [rewrite get_set_same with (k := k0) by auto |
             rewrite get_set_diff with (k' := k0) by auto ]
    end.

  Lemma assoc_set_assoc_set_diff :
    forall l (k : K) (v : V) k' v',
      k <> k' ->
      a_equiv (assoc_set (assoc_set l k v) k' v')
              (assoc_set (assoc_set l k' v') k v).
  Proof using.
    unfold a_equiv.
    intros.
    assoc_destruct.
    - now repeat assoc_rewrite.
    - assoc_destruct.
      + now repeat assoc_rewrite.
      + now repeat assoc_rewrite.
  Qed.

  Lemma a_equiv_nil :
    forall l,
      a_equiv l [] ->
      l = [].
  Proof using.
    intros.
    destruct l; auto.
    unfold a_equiv in *. simpl in *.
    destruct p.
    specialize (H k).
    break_if; try congruence.
  Qed.

  Lemma assoc_set_a_equiv :
    forall l l' (k : K) (v : V),
      a_equiv l l' ->
      a_equiv (assoc_set l k v) (assoc_set l' k v).
  Proof using.
    unfold a_equiv.
    intros.
    assoc_destruct; assoc_rewrite; auto.
  Qed.

  Lemma assoc_default_a_equiv :
    forall l l' (k : K) (v : V),
      a_equiv l l' ->
      assoc_default l k v = assoc_default l' k v.
  Proof using.
    intros. unfold a_equiv, assoc_default in *.
    find_higher_order_rewrite.
    auto.
  Qed.

  Lemma assoc_a_equiv :
    forall l l' (k : K),
      a_equiv l l' ->
      assoc l k = assoc l' k.
  Proof using.
    unfold a_equiv.
    auto.
  Qed.

  Lemma assoc_default_assoc_set_diff :
    forall (l : list (K * V)) k v k' d,
      k <> k' ->
      assoc_default (assoc_set l k' v) k d =
      assoc_default l k d.
  Proof using.
    intros. unfold assoc_default. rewrite get_set_diff; auto.
  Qed.
End assoc.
Arguments a_equiv {_} {_} _ _ _.
