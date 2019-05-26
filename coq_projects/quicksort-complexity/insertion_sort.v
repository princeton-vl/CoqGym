
Set Implicit Arguments.

Require Import Bool.
Require Import Lt.
Require Import Recdef.
Require Import List.
Require Import Permutation.
Require Import Ring.
Require Import Plus.
Require Import Mult.
Require Import Compare_dec.
Require Import monoid_monad_trans.
Require Import Le.
Require Import Div2.
Require Import Arith.
Require Import Wf_nat.
Require Import monads.
Require Import Arith.
Require Import Omega.
Require Import arith_lems.
Require Import list_utils.
Require Import Morphisms.
Require Import Relation_Definitions.
Require vec.

Definition numbers := 3 :: 2 :: 5 :: 9 :: 7 :: 6 :: 1 :: 0 :: 4 :: 8 :: nil.

Require Vector.

Hint Constructors vec.sorted.

Lemma vec_sorted_impl (X: Set) (P Q: relation X): (forall x y, P x y -> Q x y) ->
  forall n (l: Vector.t X n), vec.sorted P l -> vec.sorted Q l.
Proof. induction 2; auto. Qed.

Module plain.
Section plain.

  Variables (T: Set) (le: T -> T -> bool).

  Let R (x y: T): Prop := le x y = true.

  Fixpoint insert (x: T) (l: list T): list T :=
    match l with
    | nil => x :: nil
    | h :: t => if le x h then x :: h :: t else h :: insert x t
    end.

  Lemma insert_perm x l: Permutation (insert x l) (x :: l).
  Proof with eauto.
    induction l...
    simpl.
    destruct (le x a)...
  Qed.

  Instance insert_perm_mor: Proper (eq ==> Permutation ==> Permutation) insert.
  Proof with eauto.
    repeat intro.
    induction H0; subst; simpl...
      destruct (le y x0)...
    destruct (le y y0); destruct (le y x0)...
  Qed.

  Hypotheses
    (le_yippee: forall x y, le x y = false -> le y x = true)
    (preorder_R: preorder _ R).

  Lemma inserted_ordered x (l: list T): vec.sorted R l -> vec.sorted R (insert x l).
  Proof with auto.
    induction l.
      simpl.
      intros.
      apply vec.sorted_one.
    intros.
    pose proof (vec.sorted_tail H).
    apply IHl in H0.
    simpl.
    case_eq (le x a); intro.
      simpl.
      apply vec.sorted_more...
    simpl.
    apply vec.sorted_cons'...
    pose proof (le_yippee H1).
    intros.
    rewrite vec.list_round_trip in H3.
    unfold R.
    destruct (Permutation_in _ (insert_perm x l) H3).
      subst...
    simpl in H.
    apply (vec.sorted_cons_inv' preorder_R H).
    rewrite vec.list_round_trip...
  Qed.

  Definition isort: list T -> list T := fold_right insert nil.

  Lemma isort_permutes l: Permutation (isort l) l.
  Proof with auto.
    induction l...
    simpl.
    rewrite IHl.
    apply insert_perm.
  Qed.

  Hint Constructors vec.sorted.

  Lemma isort_sorts l: vec.sorted R (isort l).
  Proof with auto.
    induction l; simpl...
    apply inserted_ordered...
  Qed.

  Lemma isort_sorts' (U: relation T): (forall x y, le x y = true -> U x y) -> forall l, vec.sorted U (isort l).
    intros.
    apply (vec_sorted_impl _ H).
    apply isort_sorts.
  Qed.

End plain.
End plain.

Module pairs.
Section pairs.

  Variables (T: Set) (le: T -> T -> bool).

  Fixpoint insert (l: list T) (x: T) {struct l}: nat * list T :=
      match l with
      | nil => (0, x :: nil)
      | h :: t =>
          if le x h
            then (1, x :: h :: t)
            else let (n, t') := insert t x in (S n, h :: t')
      end.

  Fixpoint insert_many (l l': list T) {struct l'}: nat * list T :=
      match l' with
      | nil => (0, l)
      | h :: t =>
          let (n, u) := insert l h in
          let (m, v) := insert_many u t in
            (n + m, v)
      end.

  Definition isort: list T -> (nat * list T) := insert_many nil.

End pairs.
End pairs.

Eval compute in (pairs.isort leb numbers).

Module monadic.
Section monadic.

  Variables (M: Monad) (T: Set) (le: T -> T -> M bool).

  Fixpoint insert (l: list T) (x: T): M (list T) :=
    match l with
    | nil => ret (x :: nil)
    | h :: t =>
        r <- le x h ;
        if r
          then ret (x :: h :: t)
          else t' <- insert t x ; ret (h :: t')
  end.

  Lemma insert_unfold: forall l x, insert l x =
    match l with
    | nil => ret (x :: nil)
    | h :: t =>
        r <- le x h ;
        if r then ret (x :: h :: t) else t' <- insert t x ; ret (h :: t')
    end.
  Proof. destruct l; auto. Qed.

  Definition isort: list T -> M (list T) := foldlM insert nil.

  Hypothesis run: forall U, M U -> U.
  Arguments run [U].
  Hypothesis run_ret: forall (U: Set) (x: U), run (ret x) = x.
  Hypothesis run_bind: forall (A B: Set) (x: M A) (f: A -> M B),
    run (x >>= f) = run (f (run x)).

  Lemma insert_length (x: T) (l: list T):
    length (run (insert l x)) = S (length l).
  Proof with simpl; auto with arith.
    induction l...
      rewrite run_ret...
    rewrite run_bind.
    destruct (run (U:=bool) (le x a)).
      rewrite run_ret...
    unfold liftM.
    rewrite run_bind.
    rewrite run_ret...
  Qed.

End monadic.
End monadic.

Section quadratic.

  Import monadic.

  Definition plain_leb: nat -> nat -> IdMonad.M bool := leb.

  (*Eval compute in (isort _ plain_leb numbers).*)

  Variables (T: Set) (le: T -> T -> bool).

  Definition mle (x y: T): SimplyProfiled bool := (1, le x y).

  Lemma insert_cost (l: list T) (x: T): cost (insert _ mle l x) <= length l.
  Proof with auto with arith.
    induction l...
    intros.
    rewrite insert_unfold, bind_cost.
    destruct (result (mle x a)).
      rewrite return_cost.
      simpl...
    rewrite bind_cost, return_cost.
    deep_le_trans IHl...
    simpl.
    omega.
  Qed.

  Lemma fold_insert_cost : forall (x y: list T),
    cost (foldlM (insert _ mle) y x) <= length y * length x + div2 (sqrd (length x)).
  Proof with auto with arith; try omega.
    induction x; intros.
      simpl. omega.
    rename a into h, x into t.
    rewrite foldlM_cons.
    rewrite bind_cost.
    deep_le_trans (insert_cost y h)...
      apply plus_le_compat...
      apply insert_cost.
    deep_le_trans (IHx (result (insert _ mle y h)))...
    clear IHx.
    rewrite insert_length...
    simpl @length.
    simpl mult.
    rewrite <- mult_n_Sm.
    apply le_trans with ((length y * length t + length y) + (length t + div2 (sqrd (length t))))...
    apply plus_le_compat_l.
    rewrite plus_comm.
    apply div2_sqrdSn.
  Qed.

  Theorem insertion_sort_quadratic: forall (l: list T),
    cost (isort _ mle l) <= div2 (sqrd (length l)).
  Proof fun l => fold_insert_cost l nil.

End quadratic.
