Require Import IntuitionisticLogic.Wf.
Require Import IntuitionisticLogic.base.

Import IPC_Notation.
Import LogicNotation.
Local Open Scope IPC_scope.

Section IPC.

Context {venv: Var_env}.

Inductive IPC_derive: Context -> Term -> Prop :=
  | assum : forall ctx a, ctx a = true -> IPC_derive ctx a
  | and_elim_l : forall ctx a b, IPC_derive ctx (a && b) -> IPC_derive ctx a
  | and_elim_r : forall ctx a b, IPC_derive ctx (a && b) -> IPC_derive ctx b
  | and_intro : forall ctx a b, IPC_derive ctx a -> IPC_derive ctx b -> IPC_derive ctx (a && b)
  | or_elim : forall ctx a b c, IPC_derive ctx (a || b) ->
                IPC_derive (ctx;;a) c -> IPC_derive (ctx;;b) c -> IPC_derive ctx c
  | or_intro_l : forall ctx a b, IPC_derive ctx a -> IPC_derive ctx (a || b)
  | or_intro_r : forall ctx a b, IPC_derive ctx b -> IPC_derive ctx (a || b)
  | imp_elim : forall ctx a b, IPC_derive ctx a -> IPC_derive ctx (a --> b) -> IPC_derive ctx b
  | imp_intro : forall ctx a b, IPC_derive (ctx;;a) b -> IPC_derive ctx (a --> b)
  | false_elim : forall ctx a, IPC_derive ctx falsep -> IPC_derive ctx a.

Instance IPC : ProofTheory := mk_pt IPC_derive.

Lemma IPC_weakening: forall ctx1 ctx2 t,
  (forall t0, ctx1 t0 = true -> ctx2 t0 = true) ->
  ctx1 |-- t -> ctx2 |-- t.
Proof.
  intros.
  revert ctx2 H.
  induction H0; intros.
  + apply assum.
    apply H0; auto.
  + apply and_elim_l with b.
    apply IHIPC_derive; auto.
  + apply and_elim_r with a.
    apply IHIPC_derive; auto.
  + apply and_intro.
    - apply IHIPC_derive1; auto.
    - apply IHIPC_derive2; auto.
  + apply or_elim with (a := a) (b := b).
    - apply IHIPC_derive1; auto.
    - apply IHIPC_derive2; auto.
      intro t.
      specialize (H t).
      unfold ExtendContext.
      destruct (term_eq t a); tauto.
    - apply IHIPC_derive3; auto.
      intro t.
      specialize (H t).
      unfold ExtendContext.
      destruct (term_eq t b); tauto.
  + apply or_intro_l.
    apply IHIPC_derive; auto.
  + apply or_intro_r.
    apply IHIPC_derive; auto.
  + apply imp_elim with a.
    - apply IHIPC_derive1; auto.
    - apply IHIPC_derive2; auto.
  + apply imp_intro.
    apply IHIPC_derive; auto.
    intro t.
    specialize (H t).
    unfold ExtendContext.
    destruct (term_eq t a); tauto.
  + apply false_elim.
    apply IHIPC_derive; auto.
Qed.

Lemma IPC_substitution: forall ctx1 ctx2 t,
  (forall t0, ctx2 t0 = true -> ctx1 |-- t0) ->
  ctx2 |-- t ->
  ctx1 |-- t.
Proof.
  intros.
  revert ctx1 H; induction H0; intros.
  + apply H0; auto.
  + apply and_elim_l with b.
    apply IHIPC_derive; auto.
  + apply and_elim_r with a.
    apply IHIPC_derive; auto.
  + apply and_intro.
    - apply IHIPC_derive1; auto.
    - apply IHIPC_derive2; auto.
  + apply or_elim with (a := a) (b := b).
    - apply IHIPC_derive1; auto.
    - apply IHIPC_derive2; auto.
      unfold ExtendContext.
      intros t ?.
      destruct (term_eq t a).
      * apply assum.
        subst.
        destruct (term_eq a a); congruence.
      * apply IPC_weakening with ctx1; auto.
        intros.
        destruct (term_eq t0 a); congruence.
    - apply IHIPC_derive3; auto.
      unfold ExtendContext.
      intros t ?.
      destruct (term_eq t b).
      * apply assum.
        subst.
        destruct (term_eq b b); congruence.
      * apply IPC_weakening with ctx1; auto.
        intros.
        destruct (term_eq t0 b); congruence.
  + apply or_intro_l.
    apply IHIPC_derive; auto.
  + apply or_intro_r.
    apply IHIPC_derive; auto.
  + apply imp_elim with a.
    - apply IHIPC_derive1; auto.
    - apply IHIPC_derive2; auto.
  + apply imp_intro.
    apply IHIPC_derive; auto.
    unfold ExtendContext.
    intros t ?.
    destruct (term_eq t a).
    * apply assum.
      subst.
      destruct (term_eq a a); congruence.
    * apply IPC_weakening with ctx1; auto.
      intros.
      destruct (term_eq t0 a); congruence.
  + apply false_elim.
    apply IHIPC_derive; auto.
Qed.

End IPC.
    
