Require Import Coq.Lists.List.
Require Import Coq.Logic.ClassicalChoice.

Module Type NAT_CHOICE.

Fixpoint fisrtn_list_from_fun {A: Type} (f: nat -> A) (n: nat) : list A :=
  match n with
  | 0 => nil
  | S m => fisrtn_list_from_fun f m ++ f m :: nil
  end.

Axiom nat_stepwise_choice: forall {A: Type} (P: list A -> Prop),
  P nil ->
  (forall l, P l -> exists a, P (l ++ a :: nil)) ->
  exists f, forall n, P (fisrtn_list_from_fun f n).

End NAT_CHOICE.

Module NatChoice: NAT_CHOICE.

Section NatChoice.

Fixpoint fisrtn_list_from_fun {A: Type} (f: nat -> A) (n: nat) : list A :=
  match n with
  | 0 => nil
  | S m => fisrtn_list_from_fun f m ++ f m :: nil
  end.

Context {A: Type} (P: list A -> Prop).

Definition State: Type := {l: list A | P l}.

Hypothesis H_init: P nil.

Definition state_nil: State := exist _ nil H_init.

Section step.

Variable F: State -> A.
Hypothesis HF: forall l: State, P (proj1_sig l ++ F l :: nil).

Fixpoint step (n: nat): State := 
  match n with
  | 0 => state_nil
  | S m => exist _ _ (HF (step m))
  end.

Lemma fisrtn_list_step: forall n, fisrtn_list_from_fun (fun n0 : nat => F (step n0)) n = proj1_sig (step n).
Proof.
  intros.
  induction n.
  + simpl.
    reflexivity.
  + simpl.
    f_equal; auto.
Qed.

End step.

Lemma nat_stepwise_choice:
  (forall l, P l -> exists a, P (l ++ a :: nil)) ->
  exists f, forall n, P (fisrtn_list_from_fun f n).
Proof.
  intros.
  assert (forall (l: list A | P l), exists a : A, P (proj1_sig l ++ a :: nil)) as HH; [| clear H].
  Focus 1. {
    intros [l ?H].
    apply H; auto.
  } Unfocus.

  apply choice in HH.
  destruct HH as [f ?].

  exists (fun n => f (step f H n)).
  intros.
  rewrite fisrtn_list_step.

  apply (proj2_sig (step f H n)).
Qed.

End NatChoice.

End NatChoice.

Export NatChoice.

Lemma nat_coinduction {A: Type}: forall (P: A -> Prop) (R: A -> A -> Prop) a0,
  P a0 ->
  (forall a, P a -> exists b, R a b /\ P b) ->
  exists l: nat -> A, l 0 = a0 /\ (forall k, R (l k) (l (S k))).
Proof.
  intros.
  pose (Rs := 
            fix Rs (a: A) (l: list A): Prop :=
              match l with
              | nil => True
              | a0 :: l0 => P a0 /\ R a a0 /\ Rs a0 l0
              end).
  destruct (nat_stepwise_choice (Rs a0)) as [l ?].
  + simpl; auto.
  + intro l.
    revert a0 H.
    induction l.
    - simpl; intros.
      destruct (H0 a0 H) as [a1 [? ?]].
      exists a1; auto.
    - simpl; intros ? ? [? [? ?]].
      specialize (IHl _ H1 H3).
      destruct IHl as [a1 ?].
      exists a1; auto.
  + exists (fun n => match n with 0 => a0 | S n => l n end).
    split; auto.
    intros.
    specialize (H1 (S k)).
    destruct k; [simpl in H1; tauto |].
    simpl in H1.
    rewrite <- app_assoc in H1; simpl in H1.
    clear H H0.
    revert a0 H1; induction (fisrtn_list_from_fun l k); intros.
    - simpl in H1.
      tauto.
    - apply (IHl0 a); clear IHl0.
      simpl in H1.
      simpl; tauto.
Qed.

Lemma nat_coinduction' {A: Type}: forall (P: A -> Prop) (R: A -> A -> Prop) a0,
  P a0 ->
  (forall a, P a -> exists b, R a b /\ P b) ->
  exists l: nat -> A, l 0 = a0 /\ (forall k, R (l k) (l (S k))) /\ (forall k, P (l k)).
Proof.
  intros.
  pose (R' := fun (a b: A) => R a b /\ P b).
  
  destruct (nat_coinduction P R' a0 H) as [l [? ?]].
  + simpl; unfold R'; firstorder.
  + exists l.
    split; auto.
    split; [subst R'; firstorder |].
    intros.
    destruct k; [subst; auto |].
    specialize (H2 k).
    destruct H2; auto.
Qed.
