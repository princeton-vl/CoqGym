Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Lemma firstn_app_L : forall T n (a b : list T),
  n <= length a ->
  firstn n (a ++ b) = firstn n a.
Proof.
  induction n; destruct a; simpl in *; intros; auto.
  exfalso; omega.
  f_equal. eapply IHn; eauto. omega.
Qed.

Lemma firstn_app_R : forall T n (a b : list T),
  length a <= n ->
  firstn n (a ++ b) = a ++ firstn (n - length a) b.
Proof.
  induction n; destruct a; simpl in *; intros; auto.
  exfalso; omega.
  f_equal. eapply IHn; eauto. omega.
Qed.

Lemma firstn_all : forall T n (a : list T),
  length a <= n ->
  firstn n a = a.
Proof.
  induction n; destruct a; simpl; intros; auto.
  exfalso; omega.
  simpl. f_equal. eapply IHn; omega.
Qed.

Lemma firstn_0 : forall T n (a : list T),
  n = 0 ->
  firstn n a = nil.
Proof.
  intros; subst; auto.
Qed.

Lemma firstn_cons : forall T n a (b : list T),
  0 < n ->
  firstn n (a :: b) = a :: firstn (n - 1) b.
Proof.
  destruct n; intros.
  omega.
  simpl. cutrewrite (n - 0 = n); [ | omega ]. reflexivity.
Qed.

Hint Rewrite firstn_app_L firstn_app_R firstn_all firstn_0 firstn_cons using omega : list_rw.

Lemma skipn_app_R : forall T n (a b : list T),
  length a <= n ->
  skipn n (a ++ b) = skipn (n - length a) b.
Proof.
  induction n; destruct a; simpl in *; intros; auto.
  exfalso; omega.
  eapply IHn. omega.
Qed.

Lemma skipn_app_L : forall T n (a b : list T),
  n <= length a ->
  skipn n (a ++ b) = (skipn n a) ++ b.
Proof.
  induction n; destruct a; simpl in *; intros; auto.
  exfalso; omega.
  eapply IHn. omega.
Qed.

Lemma skipn_0 : forall T n (a : list T),
  n = 0 ->
  skipn n a = a.
Proof.
  intros; subst; auto.
Qed.

Lemma skipn_all : forall T n (a : list T),
  length a <= n ->
  skipn n a = nil.
Proof.
  induction n; destruct a; simpl in *; intros; auto.
  exfalso; omega.
  apply IHn; omega.
Qed.

Lemma skipn_cons : forall T n a (b : list T),
  0 < n ->
  skipn n (a :: b) = skipn (n - 1) b.
Proof.
  destruct n; intros.
  omega.
  simpl. cutrewrite (n - 0 = n); [ | omega ]. reflexivity.
Qed.

Hint Rewrite skipn_app_L skipn_app_R skipn_0 skipn_all skipn_cons using omega : list_rw.