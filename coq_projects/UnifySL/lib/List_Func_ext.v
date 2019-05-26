(* Copied from RamifyCoq project *)

Require Import Coq.Classes.Morphisms.
Require Import Coq.Sorting.Permutation.
Require Export Coq.Relations.Relation_Definitions.
Require Import Logic.lib.Relation_ext.
Require Import Logic.lib.Equivalence_ext.
Require Export Coq.Lists.List.


Local Open Scope equiv_scope.

Section ListFun2.

Context {A B: Type}.
Context {RA: relation A}.
Context {RB: relation B}.
Context {EqRA: Equivalence RA}.
Context {EqRB: Equivalence RB}.

Instance proper_fold_left: forall (f: A -> B -> A) {Proper_f: Proper (equiv ==> equiv ==> equiv) f}, Proper (Forall2 equiv ==> equiv ==> equiv) (fold_left f).
Proof.
  intros.
  hnf; intros.
  induction H; hnf; intros; simpl.
  + auto.
  + apply IHForall2.
    apply Proper_f; auto.
Qed.

Lemma monoid_fold_left_tail: forall {f: A -> B -> A} {Proper_f: Proper (equiv ==> equiv ==> equiv) f} (e: A) a l,
  fold_left f (l ++ a :: nil) e === f (fold_left f l e) a.
Proof.
  intros.
  simpl.
  pose proof (proper_fold_left f).
  revert e; induction l; intros; simpl.
  + reflexivity.
  + apply IHl.
Qed.

End ListFun2.

Existing Instance proper_fold_left.

Section ListFun1.

Context {A: Type}.
Context {RA: relation A}.
Context {EqRA: Equivalence RA}.

Lemma monoid_fold_left_head: forall {f} {Proper_f: Proper (equiv ==> equiv ==> equiv) f} (e: A) a l,
  (forall x, f e x === x) ->
  (forall x, f x e === x) ->
  (forall x y z, f (f x y) z === f x (f y z)) ->
  fold_left f (a :: l) e === f a (fold_left f l e).
Proof.
  intros.
  simpl.
  pose proof (proper_fold_left f).
  rewrite H.
  revert a; induction l; intros; simpl.
  + symmetry; auto.
  + rewrite (IHl (f a0 a)), H, (IHl a).
    rewrite H1.
    reflexivity.
Qed.

Lemma monoid_fold_symm: forall {f} {Proper_f: Proper (equiv ==> equiv ==> equiv) f} (e: A) l,
  (forall x, f e x === x) ->
  (forall x, f x e === x) ->
  (forall x y z, f (f x y) z === f x (f y z)) ->
  fold_left f l e === fold_right f e l.
Proof.
  intros.
  pose proof (proper_fold_left f).
  destruct l.
  + simpl.
    reflexivity.
  + simpl.
    rewrite H.
    revert a; induction l; intros; simpl.
    - symmetry; auto.
    - rewrite <- H1.
      apply IHl.
Qed.

Lemma monoid_fold_left_app: forall {f} {Proper_f: Proper (equiv ==> equiv ==> equiv) f} (e: A) l l',
  (forall x, f e x === x) ->
  (forall x, f x e === x) ->
  (forall x y z, f (f x y) z === f x (f y z)) ->
  fold_left f (l ++ l') e === f (fold_left f l e) (fold_left f l' e).
Proof.
  intros.
  rewrite fold_left_app.
  generalize (fold_left f l e) as a; clear l; intros.
  pose proof @monoid_fold_left_head f _ e a l'.
  simpl in H2.
  pose proof (proper_fold_left f).
  rewrite H in H2.
  auto.
Qed.
  
End ListFun1.

(* Above is copied from RamifyCoq project *)

Section ListFun2'.

Context {A B: Type}.
Context {RA: relation A}.
Context {RB: relation B}.

Instance proper_fold_left': forall (f: A -> B -> A) {Proper_f: Proper (RA ==> RB ==> RA) f}, Proper (Forall2 RB ==> RA ==> RA) (fold_left f).
Proof.
  intros.
  hnf; intros.
  induction H; hnf; intros; simpl.
  + auto.
  + apply IHForall2.
    apply Proper_f; auto.
Qed.

Context {EqRA: Equivalence RA}.

Lemma proper_permutation_fold_left: forall (f: A -> B -> A) {Proper_f: Proper (RA ==> eq ==> RA) f},
  (forall x1 x2 y z, x1 === x2 -> f (f x1 y) z === f (f x2 z) y) ->
  Proper (@Permutation _ ==> RA ==> RA) (fold_left f).
Proof.
  intros.
  hnf; intros.
  hnf; intros.
  revert x0 y0 H1.
  induction H0; intros.
  + simpl.
    auto.
  + simpl.
    apply IHPermutation.
    apply Proper_f; auto.
  + simpl.
    assert (RA (f (f x0 y) x) (f (f y0 x) y)) by (apply H; auto).
    revert H0; generalize (f (f x0 y) x) (f (f y0 x) y).
    induction l; intros.
    - simpl; auto.
    - simpl.
      apply IHl.
      apply Proper_f; auto.
  + etransitivity.
    - apply IHPermutation1, H1.
    - apply IHPermutation2.
      reflexivity.
Qed.

End ListFun2'.

Definition not_nil {A: Type} (l: list A): Prop := l <> nil.

Lemma not_nil_app_l {A: Type}: forall (l l': list A), not_nil l -> not_nil (l ++ l').
Proof.
  intros.
  hnf in *.
  destruct l;intros; simpl in *; congruence.
Qed.

Lemma eq_nil_dec {A: Type}: forall (l: list A), {l = nil} + {not_nil l}.
Proof.
  intros.
  destruct l; [left | right]; auto.
  intro; congruence.
Qed.

Instance Proper_perm_not_nil {A: Type}: Proper (@Permutation A ==> iff) (@not_nil A).
Proof.
  hnf; intros.
  induction H; unfold not_nil in *.
  + reflexivity.
  + split; intros ? ?; congruence.
  + split; intros ? ?; congruence.
  + tauto.
Qed.

Definition semi_group_fold {A: Type} (default: A) (f: A -> A -> A) (l: list A): A :=
  match l with
  | nil => default
  | a :: l0 => fold_left f l0 a
  end.

Section ListFun1'.

Context {A: Type}.
Context {RA: relation A}.
Context {EqRA: Equivalence RA}.

Instance proper_semi_group_fold: forall (f: A -> A -> A) (default: A) {Proper_f: Proper (equiv ==> equiv ==> equiv) f}, Proper (Forall2 equiv ==> equiv) (semi_group_fold default f).
Proof.
  intros.
  hnf; intros.
  destruct H.
  + reflexivity.
  + simpl.
    apply proper_fold_left; auto.
Qed.

Lemma semi_group_fold_app: forall {f} {Proper_f: Proper (equiv ==> equiv ==> equiv) f} (default: A) l l',
  (forall x y z, f (f x y) z === f x (f y z)) ->
  not_nil l ->
  not_nil l' ->
  semi_group_fold default f (l ++ l') === f (semi_group_fold default f l) (semi_group_fold default f l').
Proof.
  intros.
  destruct l as [| a l], l' as [| a' l']; hnf in H0, H1; try congruence; clear H0 H1.
  revert a; induction l; intros.
  + simpl.
    revert a'; induction l'; intros.
    - simpl.
      reflexivity.
    - specialize (IHl' (f a' a0)).
      simpl in *.
      rewrite <- IHl'; clear IHl'.
      specialize (H a a' a0).
      set (b := f (f a a') a0) in H |- *.
      set (c := f a (f a' a0)) in H |- *.
      clearbody b c; clear a a' a0.
      revert b c H; induction l'; intros.
      * auto.
      * simpl.
        apply IHl'.
        rewrite H; reflexivity.
  + exact (IHl (f a0 a)).
Qed.

Lemma semi_group_fold_concat: forall {f} {Proper_f: Proper (equiv ==> equiv ==> equiv) f} (default: A) ls,
  (forall x y z, f (f x y) z === f x (f y z)) ->
  Forall not_nil ls ->
  semi_group_fold default f (concat ls) === semi_group_fold default f (map (semi_group_fold default f) ls).
Proof.
  intros.
  destruct H0; [reflexivity |].
  revert x H0; induction H1; intros.
  + simpl.
    rewrite app_nil_r.
    reflexivity.
  + Opaque semi_group_fold.
    simpl.
    rewrite semi_group_fold_app; auto.
      2: apply not_nil_app_l; auto.
    specialize (IHForall x H0).
    simpl in IHForall.
    rewrite IHForall.
    change (semi_group_fold default f x0 :: semi_group_fold default f x :: map (semi_group_fold default f) l)
      with ((semi_group_fold default f x0 :: nil) ++ semi_group_fold default f x :: map (semi_group_fold default f) l).
    rewrite semi_group_fold_app by (auto; intro; congruence).
    reflexivity.
    Transparent semi_group_fold.
Qed.

Lemma comm_semi_group_fold_perm: forall {f} {Proper_f: Proper (equiv ==> equiv ==> equiv) f} (default: A) l l',
  (forall x y, f x y === f y x) ->
  (forall x y z, f (f x y) z === f x (f y z)) ->
  Permutation l l' ->
  semi_group_fold default f l === semi_group_fold default f l'.
Proof.
  intros.
  induction H1.
  + reflexivity.
  + destruct (eq_nil_dec l) as [?H | ?H].
    - subst; apply Permutation_nil in H1; subst.
      reflexivity.
    - pose proof H2.
      rewrite H1 in H3.
      change (x :: l) with ((x :: nil) ++ l).
      change (x :: l') with ((x :: nil) ++ l').
      rewrite semi_group_fold_app by (auto; intro; congruence).
      rewrite semi_group_fold_app by (auto; intro; congruence).
      rewrite IHPermutation.
      reflexivity.
  + simpl.
    rewrite <- H.
    reflexivity.
  + rewrite IHPermutation1.
    auto.
Qed.

End ListFun1'.

Lemma Forall2_impl: forall {A B: Type} (P Q: A -> B -> Prop),
  (forall a b, P a b -> Q a b) ->
  (forall (lA: list A) (lB: list B), Forall2 P lA lB -> Forall2 Q lA lB).
Proof.
  intros.
  induction H0.
  + constructor.
  + constructor.
    - auto.
    - auto.
Qed.

Lemma Forall2_rev: forall {A B: Type} (P: A -> B -> Prop),
  forall (lA: list A) (lB: list B), Forall2 (fun b a => P a b) lB lA -> Forall2 P lA lB.
Proof.
  intros.
  induction H.
  + constructor.
  + constructor.
    - auto.
    - auto.
Qed.

