Require Import IntuitionisticLogic.base.
Import LogicNotation.
Local Open Scope IPC_scope.

Section TrivialSemantic.

Context {venv: Var_env}.

Fixpoint denote (f: Var -> Prop) (t: Term) : Prop :=
  match t with
  | andp t1 t2 => denote f t1 /\ denote f t2
  | orp t1 t2 => denote f t1 \/ denote f t2
  | impp t1 t2 => denote f t1 -> denote f t2
  | falsep => False
  | varp x => f x
  end.

Definition Trivial_sem: Semantic := mk_sem (Var -> Prop) denote.

End TrivialSemantic.

Require Import IntuitionisticLogic.IPC.

Lemma sound_Trivial_IPC: forall {venv: Var_env}, sound Trivial_sem IPC.
Proof.
  unfold sound.
  intros.
  induction H; intros M CONTEXT.
  + apply CONTEXT.
    auto.
  + specialize (IHIPC_derive M CONTEXT).
    simpl in IHIPC_derive |- *.
    tauto.
  + specialize (IHIPC_derive M CONTEXT).
    simpl in IHIPC_derive |- *.
    tauto.
  + specialize (IHIPC_derive1 M CONTEXT).
    specialize (IHIPC_derive2 M CONTEXT).
    simpl in IHIPC_derive1, IHIPC_derive2 |- *.
    tauto.
  + specialize (IHIPC_derive1 M CONTEXT).
    destruct IHIPC_derive1.
    - assert (CONTEXT_a: forall t0 : Term, (ctx;; a) t0 = true -> M |= t0).
      Focus 1. {
        intros.
        unfold ExtendContext in H3.
        destruct (term_eq t0 a).
        + subst; exact H2.
        + apply CONTEXT; auto.
      } Unfocus.
      exact (IHIPC_derive2 M CONTEXT_a).
    - assert (CONTEXT_b: forall t0 : Term, (ctx;; b) t0 = true -> M |= t0).
      Focus 1. {
        intros.
        unfold ExtendContext in H3.
        destruct (term_eq t0 b).
        + subst; exact H2.
        + apply CONTEXT; auto.
      } Unfocus.
      exact (IHIPC_derive3 M CONTEXT_b).
  + specialize (IHIPC_derive M CONTEXT).
    simpl in IHIPC_derive |- *.
    tauto.
  + specialize (IHIPC_derive M CONTEXT).
    simpl in IHIPC_derive |- *.
    tauto.
  + specialize (IHIPC_derive1 M CONTEXT).
    specialize (IHIPC_derive2 M CONTEXT).
    simpl in IHIPC_derive1, IHIPC_derive2 |- *.
    tauto.
  + simpl; intros.
    assert (CONTEXT_a: forall t0 : Term, (ctx;; a) t0 = true -> M |= t0).
    Focus 1. {
      intros.
      unfold ExtendContext in H1.
      destruct (term_eq t0 a).
      + subst; exact H0.
      + apply CONTEXT; auto.
    } Unfocus.
    specialize (IHIPC_derive M CONTEXT_a).
    exact IHIPC_derive.
  + specialize (IHIPC_derive M CONTEXT).
    simpl in IHIPC_derive |- *.
    tauto.
Qed.

