Require Import Coq.Lists.List.

Set Implicit Arguments.
Set Strict Implicit.

Section parametric.
  Variable T : Type.

  Lemma nth_error_app_L : forall (A B : list T) n,
    n < length A ->
    nth_error (A ++ B) n = nth_error A n.
  Proof.
    induction A; destruct n; simpl; intros; auto.
    { inversion H. }
    { inversion H. }
    { eapply IHA. apply Lt.lt_S_n; assumption. }
  Qed.

  Lemma nth_error_app_R : forall (A B : list T) n,
    length A <= n ->
    nth_error (A ++ B) n = nth_error B (n - length A).
  Proof.
    induction A; destruct n; simpl; intros; auto.
    + inversion H.
    + apply IHA. apply Le.le_S_n; assumption.
  Qed.

  Lemma nth_error_weaken : forall ls' (ls : list T) n v,
    nth_error ls n = Some v ->
    nth_error (ls ++ ls') n = Some v.
  Proof.
    clear. induction ls; destruct n; simpl; intros; unfold value, error in *; try congruence; auto.
  Qed.

  Lemma nth_error_nil : forall n,
    nth_error nil n = @None T.
  Proof.
    destruct n; reflexivity.
  Qed.

  Lemma nth_error_past_end : forall (ls : list T) n,
    length ls <= n ->
    nth_error ls n = None.
  Proof.
    clear. induction ls; destruct n; simpl; intros; auto.
    + inversion H.
    + apply IHls. apply Le.le_S_n; assumption.
  Qed.

  Lemma nth_error_length : forall (ls ls' : list T) n,
    nth_error (ls ++ ls') (n + length ls) = nth_error ls' n.
  Proof.
    induction ls; simpl; intros.
    rewrite Plus.plus_0_r. auto.
    rewrite <- Plus.plus_Snm_nSm.
    simpl. eapply IHls.
  Qed.

  Theorem nth_error_length_ge : forall T (ls : list T) n,
    nth_error ls n = None -> length ls <= n.
  Proof.
    induction ls; destruct n; simpl in *; auto; simpl in *.
    + intro. apply Le.le_0_n.
    + inversion 1.
    + intros. eapply Le.le_n_S. auto.
  Qed.

  Lemma nth_error_length_lt : forall {T} (ls : list T) n val,
    nth_error ls n = Some val -> n < length ls.
  Proof.
    induction ls; destruct n; simpl; intros; auto.
    + inversion H.
    + inversion H.
    + apply Lt.lt_0_Sn.
    + apply Lt.lt_n_S. eauto.
  Qed.


  Theorem nth_error_map : forall U (f : T -> U) ls n,
    nth_error (map f ls) n = match nth_error ls n with
                               | None => None
                               | Some x => Some (f x)
                             end.
  Proof.
    induction ls; destruct n; simpl; auto.
  Qed.

End parametric.
