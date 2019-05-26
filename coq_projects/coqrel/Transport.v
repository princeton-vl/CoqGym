Require Export Monotonicity.
Require Import KLR.

(** ** The [transport] tactic *)

(** Often, we know that a number of terms are related, and need to
  transport hypotheses built out the the left-hand sides into ones
  with similar shapes, but built out of the right-hand sides. For
  instance, in cirumstances where [rauto] can establish
  [option_rel R x y], we will want to turn a hypothesis of the form
  [x = Some a] into one of the form [y = Some b], and remember that
  [R a b]. This is the role of the [transport] tactic. *)

(** *** Transportable hypotheses *)

(* To make the tactic extensible, we use the following typeclass to
  declare patterns of relations and hypothesis shapes that can be
  handled in this way. *)

Class Transport {A B} (R: rel A B) (a: A) (b: B) (PA: Prop) (PB: Prop) :=
  transport: R a b -> PA -> PB.

(** One stereotypical example is [option_le]: the [Transport] instance
  defined in the [OptionRel] library allows us to transport hypothese
  of the form [x = Some a] into hypotheses of the form [y = Some b],
  with [a] and [b] related by [R] whenever [x] and [y] are related by
  [option_le R], and similarly for [None] and [option_rel].

  Other instances are declared below. *)

Global Instance prod_rel_transport_eq_pair {A1 B1 A2 B2} (R1: rel A1 B1) (R2: rel A2 B2) x y a1 a2:
  Transport (prod_rel R1 R2) x y (x = (a1, a2)) (exists b1 b2, y = (b1, b2) /\ R1 a1 b1 /\ R2 a2 b2).
Proof.
  intros [Hxy1 Hxy2] Hx.
  destruct y.
  subst.
  simpl in *.
  eauto.
Qed.

(** For [set_le] the situation is slightly more involved, for two
  reasons. First, a regular [eapply set_le_transport] fails to unify
  the parameter [B] of [Transport] against the [_ -> Prop] provied by
  the instance below. This can be worked around by pre-unifying that
  specific parameter. Second, because [set_le_transport] is
  potentially applicable to virtually any hypothesis (since there is
  no strongly distinguishing syntactic format in our target
  hypotheses), it makes [transport_hyps] very slow.

  To address this, we explicitely register hints based on the
  [set_le_transport] tactic, which looks for "keywords" before doing
  anything, then applies the lemma with the required unification
  preparation. For example, [set_le_transport] is used in the
  following way in the [SimClight] library:
<<
    Hint Extern 1 (Transport _ _ _ _ _) =>
      set_le_transport @assign_loc : typeclass_instances.
>>
  Note that it's necessary to use [@] because [assign_loc] is
  parametrized by typeclasses, and we want to avoid undue
  specialization at hint registration time. *)

Lemma set_le_transport {A B} (R: rel A B) sA sB a:
  Transport (set_le R) sA sB (sA a) (exists b, sB b /\ R a b).
Proof.
  intros HsAB Ha.
  edestruct HsAB; eauto.
Qed.

Ltac set_le_transport keyword :=
  lazymatch goal with
    | |- @Transport ?A ?B ?R ?a ?b ?PA ?PB =>
      lazymatch PA with
        | context [keyword] =>
          let Xv := fresh "X" in evar (Xv: Type);
          let X := eval red in Xv in clear Xv;
          unify B (X -> Prop);
          eapply set_le_transport
      end
  end.
      
(** We defined a few more relation patterns based on [set_le] and
  [rel_curry], with a similar strategy. *)

Lemma rel_curry_set_le_transport {A1 A2 B1 B2} R sA sB (a1: A1) (a2: A2):
  Transport (% set_le R) sA sB
    (sA a1 a2)
    (exists (b1: B1) (b2: B2), sB b1 b2 /\ R (a1, a2) (b1, b2)).
Proof.
  intros HsAB Ha.
  destruct (HsAB (a1, a2)) as ([b1 b2] & Hb & Hab); eauto.
Qed.

Ltac rel_curry_set_le_transport keyword :=
  lazymatch goal with
    | |- @Transport ?A ?B ?R ?a ?b ?PA ?PB =>
      lazymatch PA with
        | context [keyword] =>
          let Xv := fresh "X" in evar (Xv: Type);
          let X := eval red in Xv in clear Xv;
          let Yv := fresh "Y" in evar (Yv: Type);
          let Y := eval red in Yv in clear Yv;
          unify B (X -> Y -> Prop);
          eapply rel_curry_set_le_transport
      end
  end.

Lemma rel_curry2_set_le_transport {A1 A2 A3 B1 B2 B3} R sA sB (a1: A1) (a2: A2) (a3: A3):
  Transport (% % set_le R) sA sB
    (sA a1 a2 a3)
    (exists (b1: B1) (b2: B2) (b3: B3), sB b1 b2 b3 /\ R (a1, a2, a3) (b1, b2, b3)).
Proof.
  intros HsAB Ha.
  destruct (HsAB (a1, a2, a3)) as ([[b1 b2] b3] & Hb & Hab); eauto.
Qed.

Ltac rel_curry2_set_le_transport keyword :=
  lazymatch goal with
    | |- @Transport ?A ?B ?R ?a ?b ?PA ?PB =>
      lazymatch PA with
        | context [keyword] =>
          let Xv := fresh "X" in evar (Xv: Type);
          let X := eval red in Xv in clear Xv;
          let Yv := fresh "Y" in evar (Yv: Type);
          let Y := eval red in Yv in clear Yv;
          let Zv := fresh "Y" in evar (Yv: Type);
          let Z := eval red in Yv in clear Yv;
          unify B (X -> Y -> Z -> Prop);
          eapply rel_curry2_set_le_transport
      end
  end.

(** The situation for [impl] is similar: since this transport instance
  can apply to pretty much anything, we need to register it on a
  case-by-case basis. Here is an example used in the CertiKOS proof
  for hypotheses of the form [writable_block ge b]:
<<
    Hint Extern 10 (Transport _ _ _ (writable_block _ _) _) =>
      eapply impl_transport : typeclass_instances.
>> *)

Lemma impl_transport P Q:
  Transport impl P Q P Q.
Proof.
  firstorder.
Qed.

(*** *** The actual tactic *)

(** Often, the target hypotheses declared using the [Transport] class
  have existential quantifiers, and need to be broken up to get to the
  actual relational hypotheses we're interested in. The [split_hyp]
  tactic does that. We also use that opportunity to split up
  [prod_rel] and [rel_incr] when appropriate. For [prod_rel] this is
  especially useful when [rel_curry] is involved. Likewise we
  generally want to split up [rel_incr] as soon as possible, so that
  the existentially quantified world therein can be used to
  instantiate evars that have been spawned from that point on.

  As a generally useful complement, the [split_hyps] tactic applies
  the same process to all hypotheses. *)

Ltac split_hyp H :=
  lazymatch type of H with
    | ex _ =>
      destruct H as [? H];
      split_hyp H
    | _ /\ _ =>
      let H1 := fresh in
      let H2 := fresh in
      destruct H as [H1 H2];
      split_hyp H1;
      split_hyp H2
    | prod_rel ?Rx ?Ry (?x1, ?y1) (?x2, ?y2) =>
      change (Rx x1 x2 /\ Ry y1 y2) in H;
      split_hyp H
    | rel_incr ?acc ?R ?w ?x ?y =>
      let w' := fresh w "'" in
      let Hw' := fresh "H" w' in
      destruct H as (w' & Hw' & H);
      split_hyp H
    | klr_diam ?l ?R ?w ?x ?y =>
      let w' := fresh w "'" in
      let Hw' := fresh "H" w' in
      destruct H as (w' & Hw' & H);
      split_hyp H
    | prod_klr ?Rx ?Ry ?w (?x1, ?y1) (?x2, ?y2) =>
      change (Rx w x1 x2 /\ Ry w y1 y2) in H;
      split_hyp H
    | _ =>
      idtac
  end.

Ltac split_hyps :=
  repeat
    lazymatch goal with
      | H: ex _ |- _ =>
        destruct H
      | H: _ /\ _ |- _ =>
        destruct H
      | H: prod_rel ?Rx ?Ry (?x1, ?y1) (?x2, ?y2) |- _ =>
        change (Rx x1 x2 /\ Ry y1 y2) in H
      | H: klr_diam ?R ?w ?x ?y |- _ =>
        let w' := fresh w "'" in
        let Hw' := fresh "H" w' in
        destruct H as (w' & Hw' & H)
      | H: prod_klr ?Rx ?Ry ?w (?x1, ?y1) (?x2, ?y2) |- _ =>
        change (Rx w x1 x2 /\ Ry w y1 y2) in H
    end.

(** We're now ready to defined the [transport] tactic, which
  essentially looks up a [Transport] instance and applies it the the
  hypothesis to be transported, using [RAuto] to solve the relational
  subgoal. Note that the relation and right-hand side will usually
  contain existential variables, but the proof search can hopefully
  proceed by following the structure of the left-hand side. Once the
  [Transport] instance has been applied, we use [split_hyp] on the
  modified hypothesis as post-processing.

  Because we have many open-ended evars involved, it is easy for
  trivial relations such as [eq] to kick in and sabotage us,
  overriding the more interesting properties that we actually want to
  use and preventing any progress from actually being made. In order
  to attenuate this issue, we require that [RAuto] yield unconvertible
  related elements.

  Another pitfall we want to avoid is illustrated by the [option_rel]
  case. When we have a hypothesis of the form [H: m = Some a], but no
  interesting way to relate [m] to something else, then the search for
  [(option_rel ?R) m ?n] can end up using [H] itself (because
  [option_rel eq] is reflexive, hence [subrel_eq] applies). To prevent
  such cases we need to make sure that the hypothesis being
  transported is not used to discharge the relational premise, and so
  we revert it into the conclusing before we proceed, and use the
  following lemma to work on a goal of that form directly. *)

Lemma transport_in_goal `{Transport} `{!RAuto (R a b)} `{!Unconvertible a b}:
  forall (Q: Prop), (PB -> Q) -> (PA -> Q).
Proof.
  firstorder.
Qed.

Ltac transport H :=
  revert H;
  lazymatch goal with
    | |- ?PA -> ?Q =>
      apply (transport_in_goal (PA:=PA) Q)
  end;
  intro H;
  split_hyp H.

(** Again we provide a tactic which attempts to transport all
  hypotheses. Notice that earlier transportations may provide new
  hypotheses making later transportations possible. Hence it would be
  hard to provide a much more effective tactic, even though this one
  may retry failing transportations many times. *)

Ltac transport_hyps :=
  repeat
    match goal with
      | H: _ |- _ => transport H
    end.
