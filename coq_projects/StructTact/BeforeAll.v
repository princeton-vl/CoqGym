Require Import List.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import StructTact.ListTactics.

Fixpoint before_all {A : Type} (x : A) y l : Prop :=
  match l with
    | [] => True
    | a :: l' => 
      ~ In x l' \/ 
      (y <> a /\ before_all x y l')
  end.

Section before_all.
  Variable A : Type.

  Lemma before_all_head_not_in :
    forall l (x y : A),
      x <> y ->
      before_all x y (y :: l) ->
      ~ In x l.
  Proof using.
    intros.
    simpl in *.
    break_or_hyp; auto.
    break_and. auto.
  Qed.

  Lemma before_all_neq_append : 
  forall l (x y a : A),
    a <> x ->
    before_all x y l ->
    before_all x y (l ++ [a]).
  Proof using.
  induction l.
  - intros; left; auto.
  - intros;
    simpl in *.
    break_or_hyp.
    * left.
      intro H_in.
      do_in_app.
      break_or_hyp; auto.
      simpl in *.
      break_or_hyp; auto.
    * break_and.
      right.
      split; auto.
  Qed.

  Lemma before_all_not_in_1 :
    forall l (x y : A),
      ~ In x l ->
      before_all x y l.
  Proof using.
    intros.
    destruct l; simpl in *; auto.
  Qed.

  Lemma before_all_not_in_2 :
    forall l (x y : A),
      ~ In y l ->
      before_all x y l.
  Proof using.
    induction l.
    - intros. simpl in *. auto.
    - intros. simpl in *.
      assert (H_neq: y <> a); auto.
      assert (H_in: ~ In y l); auto.
   Qed.
End before_all.
