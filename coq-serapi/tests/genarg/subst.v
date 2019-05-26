Require Import List.
Import ListNotations.

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

  Fixpoint assoc_set (l : list (K * V)) (k : K) (v : V) : list (K * V) :=
    match l with
      | [] => [(k, v)]
      | (k', v') :: l' =>
        if K_eq_dec k k' then
          (k, v) :: l'
        else
          (k', v') :: (assoc_set l' k v)
    end.

  Lemma get_set_same :
    forall k v l,
      assoc (assoc_set l k v) k = Some v.
  Proof using.
    induction l; intros; simpl.
    - destruct (K_eq_dec _ _); simpl; subst; congruence.
    - destruct a; repeat (destruct (K_eq_dec _ _); simpl; subst; try congruence).
  Qed.

  Lemma get_set_diff :
    forall k k' v l,
      k <> k' ->
      assoc (assoc_set l k v) k' = assoc l k'.
  Proof using.
    induction l; intros; simpl.
    - destruct (K_eq_dec _ _); simpl; subst; congruence.
    - destruct a.
      repeat (destruct (K_eq_dec _ _); simpl; subst; try congruence).
      rewrite IHl; auto.
  Qed.

  Ltac assoc_rewrite :=
    match goal with
    | [  |- context [assoc (assoc_set _ ?k0' _) ?k0 ] ] =>
      first [rewrite get_set_same with (k := k0) by auto |
             rewrite get_set_diff with (k' := k0) by auto ]
    end.

  Definition a_equiv (l1 : list (K * V)) l2 :=
    forall k,assoc l1 k = assoc l2 k.

  Lemma assoc_set_assoc_set_diff :
    forall l (k : K) (v : V) k' v',
      k <> k' ->
      a_equiv (assoc_set (assoc_set l k v) k' v')
              (assoc_set (assoc_set l k' v') k v).
  Proof using.
    unfold a_equiv.
    intros.
    destruct (K_eq_dec k0 k'); [subst k'; rewrite get_set_same with (k := k0)|
                                   rewrite get_set_diff with (k' := k0) by auto].
    - now repeat assoc_rewrite.
    - destruct (K_eq_dec k0 k); [subst k; rewrite get_set_same with (k := k0)|
                                   rewrite get_set_diff with (k' := k0) by auto].
      + now repeat assoc_rewrite.
      + now repeat assoc_rewrite.
  Qed.
End assoc.