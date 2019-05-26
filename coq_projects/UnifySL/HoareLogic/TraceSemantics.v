Require Import Coq.Relations.Relation_Operators.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OSAExamples.
Require Import Logic.SeparationLogic.Model.OSAGenerators.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.
Require Import Logic.HoareLogic.BigStepSemantics.

Local Open Scope kripke_model.
Import KripkeModelNotation_Intuitionistic.

Class Action: Type := {
  action: Type;
  trace := list action;
  traces := trace -> Prop
}.

Definition singleton_trace {Ac: Action} (a: action): trace := cons a nil.

Definition singleton_traces {Ac: Action} (tr: trace): traces := eq tr.

Definition trace_app {Ac: Action}: trace -> trace -> trace := @app _.

Inductive traces_app {Ac: Action}: traces -> traces -> traces :=
  traces_app_intro: forall tr1 tr2 (Tr1 Tr2: traces), Tr1 tr1 -> Tr2 tr2 -> traces_app Tr1 Tr2 (trace_app tr1 tr2).

Class Command2Traces (P: ProgrammingLanguage) (Ac: Action): Type := {
  cmd_denote: cmd -> traces
}.

Class ActionInterpret (state: Type) (Ac: Action): Type := {
  state_enable: action -> state -> MetaState state -> Prop (*;
  state_enable_pf: forall a s ms1 ms2, state_enable a s ms1 -> state_enable a s ms2 -> ms1 = ms2*)
}.

Class TraceSemantics (P: ProgrammingLanguage) (state: Type) (Ac: Action): Type := {
  c2t :> Command2Traces P Ac;
  ac_sem :> ActionInterpret state Ac
}.

Class Action_resource (Ac: Action) (Res: Resource) : Type := {
  Aacquire_res: resource -> action;
  Arelease_res: resource -> action;
}.

Class NormalAction_resource (Ac: Action) (Res: Resource) {Acr: Action_resource Ac Res}: Type := {
  Aacquire_res_inv: forall r1 r2, Aacquire_res r1 = Aacquire_res r2 -> r1 = r2;
  Arelease_res_inv: forall r1 r2, Arelease_res r1 = Arelease_res r2 -> r1 = r2;
  Aacquire_Arelease_res: forall r1 r2, Aacquire_res r1 <> Arelease_res r2;
}.

Definition is_resource_action {Ac: Action} {Res: Resource} {Acr: Action_resource Ac Res} (r: resource) (a: action) := Aacquire_res r = a \/ Arelease_res r = a.

Definition is_resources_action {Ac: Action} {Res: Resource} {Acr: Action_resource Ac Res} (a: action) := exists r, is_resource_action r a.

Ltac solve_resource_action :=
  repeat
  match goal with
  | H: Aacquire_res ?r1 = Aacquire_res ?r2 |- _ => apply Aacquire_res_inv in H; subst
  | H: Arelease_res ?r1 = Arelease_res ?r2 |- _ => apply Arelease_res_inv in H; subst
  | H: Aacquire_res ?r1 = Arelease_res ?r2 |- _ => exfalso; apply Aacquire_Arelease_res in H; apply H
  | H: Arelease_res ?r1 = Aacquire_res ?r2 |- _ => exfalso; symmetry in H; apply Aacquire_Arelease_res in H; apply H
  | H: ~ is_resource_action ?r (Aacquire_res ?r) |- _ => exfalso; apply H; left; auto
  | H: ~ is_resource_action ?r (Arelease_res ?r) |- _ => exfalso; apply H; right; auto
  | H: ~ is_resources_action (Aacquire_res ?r) |- _ => exfalso; apply H; exists r; left; auto
  | H: ~ is_resources_action (Arelease_res ?r) |- _ => exfalso; apply H; exists r; right; auto
  end;
  repeat
  let HH := fresh "H" in
  match goal with
  | H: ~ is_resource_action ?r1 (Aacquire_res ?r2) |- _ =>
         specialize (fun (HH: r2 = r1) => H (or_introl (f_equal Aacquire_res (eq_sym HH))))
  | H: ~ is_resource_action ?r1 (Arelease_res ?r2) |- _ =>
         specialize (fun (HH: r2 = r1) => H (or_intror (f_equal Arelease_res (eq_sym HH))))
  end.
  

Instance Res_Join (Res: Resource): Join resources := Pred_Join resource.

Instance Res_SA (Res: Resource): SeparationAlgebra resources := Pred_SA resource.

(* res_enable A1 A1' A2 := A1 ==> A1' while A2 is the environ *)
Inductive res_enable {Ac: Action} {Res: Resource} {Acr: Action_resource Ac Res}: action -> resources -> resources -> resources -> Prop :=
| res_enable_acq: forall r A1 A1' A2, join A1 (eq r) A1' -> ~ A2 r -> res_enable (Aacquire_res r) A1 A1' A2
| res_enable_rel: forall r A1 A1' A2, join A1' (eq r) A1 -> res_enable (Arelease_res r) A1 A1' A2
| res_enable_other: forall a A1 A2, ~ is_resources_action a -> res_enable a A1 A1 A2.

Lemma res_enable_acq_inv {Ac: Action} {Res: Resource} {Acr: Action_resource Ac Res} {nAcr: NormalAction_resource Ac Res}:
  forall r A1 A1' A2, res_enable (Aacquire_res r) A1 A1' A2 -> join A1 (eq r) A1' /\ ~ A2 r.
Proof.
  intros.
  inversion H; subst; solve_resource_action.
  auto.
Qed.

Lemma res_enable_rel_inv {Ac: Action} {Res: Resource} {Acr: Action_resource Ac Res} {nAcr: NormalAction_resource Ac Res}:
  forall r A1 A1' A2, res_enable (Arelease_res r) A1 A1' A2 -> join A1' (eq r) A1.
Proof.
  intros.
  inversion H; subst; solve_resource_action.
  auto.
Qed.

Lemma res_enable_not_res_inv {Ac: Action} {Res: Resource} {Acr: Action_resource Ac Res} {nAcr: NormalAction_resource Ac Res}:
  forall a A1 A1' A2, ~ is_resources_action a -> res_enable a A1 A1' A2 -> A1 = A1'.
Proof.
  intros.
  inversion H0; subst; solve_resource_action.
  auto.
Qed.

Inductive start_by_Aacq {Ac: Action} {Res: Resource} {Acr: Action_resource Ac Res}: resource -> trace -> Prop :=
| start_by_Aacq_nil: forall r, start_by_Aacq r nil
| start_by_Aacq_acq: forall r tr, start_by_Arel r tr -> start_by_Aacq r (cons (Aacquire_res r) tr)
| start_by_Aacq_irr: forall r a tr, ~ is_resource_action r a -> start_by_Aacq r tr -> start_by_Aacq r (cons a tr)
with start_by_Arel {Ac: Action} {Res: Resource} {Acr: Action_resource Ac Res}: resource -> trace -> Prop :=
| start_by_Arel_rel: forall r tr, start_by_Aacq r tr -> start_by_Arel r (cons (Arelease_res r) tr)
| start_by_Arel_irr: forall r a tr, ~ is_resource_action r a -> start_by_Arel r tr -> start_by_Arel r (cons a tr).

Class Action_Parallel (Ac: Action): Type := {
  race: action;
  race_actions: action -> action -> Prop;
}.

Class NormalAction_Parallel_resource (Ac: Action) (Res: Resource) {AcP: Action_Parallel Ac} {Acr: Action_resource Ac Res}: Type := {
  res_actions_no_race: forall a1 a2, race_actions a1 a2 -> ~ is_resources_action a1 /\ ~ is_resources_action a2;
  race_not_resource: ~ is_resources_action race
}.

Inductive trace_interleave {Ac: Action} {Res: Resource} {AcP: Action_Parallel Ac} {Acr: Action_resource Ac Res}: resources -> resources -> trace -> trace -> trace -> Prop :=
| trace_interleave_nil_nil: forall (A1 A2: resources), trace_interleave A1 A2 nil nil nil
| trace_interleave_race: forall (A1 A2: resources) a1 tr1 a2 tr2, race_actions a1 a2 -> trace_interleave A1 A2 (cons a1 tr1) (cons a2 tr2) (cons race nil)
| trace_interleave_left: forall (A1 A1' A2: resources) a1 tr1 tr2 tr, res_enable a1 A1 A1' A2 -> trace_interleave A1' A2 tr1 tr2 tr -> trace_interleave A1 A2 (cons a1 tr1) tr2 (cons a1 tr)
| trace_interleave_right: forall (A1 A2 A2': resources) tr1 a2 tr2 tr, res_enable a2 A2 A2' A1 -> trace_interleave A1 A2' tr1 tr2 tr -> trace_interleave A1 A2 tr1 (cons a2 tr2) (cons a2 tr).

Inductive traces_interleave {Ac: Action} {Res: Resource} {AcP: Action_Parallel Ac} {Acr: Action_resource Ac Res}: traces -> traces -> traces :=
| traces_interleave_intro: forall (Tr1 Tr2: traces) tr1 tr2 tr, Tr1 tr1 -> Tr2 tr2 -> trace_interleave (fun _ => False) (fun _ => False) tr1 tr2 tr -> traces_interleave Tr1 Tr2 tr.

Class ActionInterpret_resource (state: Type) (Ac: Action) (Res: Resource) {Acr: Action_resource Ac Res} (ac_sem: ActionInterpret (resources * state) Ac): Type := {
  state_enable_Aacquire_res: forall r (A1 A2: resources) (s: state),
    join A1 (eq r) A2 -> state_enable (Aacquire_res r) (A1, s) (Terminating (A2, s));
  state_enable_Arelease_res: forall r (A1 A2: resources) (s: state),
    join A2 (eq r) A1 -> state_enable (Arelease_res r) (A1, s) (Terminating (A2, s));
  state_enable_non_resource_action1: forall a (A1 A2: resources) (s1 s2: state),
    ~ is_resources_action a -> state_enable a (A1, s1) (Terminating (A2, s2)) -> A1 = A2;
  state_enable_non_resource_action2: forall a (A A': resources) (s: state) (ms: MetaState state),
    ~ is_resources_action a -> state_enable a (A, s) (lift_function (pair A) ms) -> state_enable a (A', s) (lift_function (pair A') ms)
}.

Class ActionInterpret_Parallel_resource (state: Type) {J: Join state} (Ac: Action) {AcP: Action_Parallel Ac} (Res: Resource) {Acr: Action_resource Ac Res} (ac_sem: ActionInterpret (resources * state) Ac): Type := {
  state_enable_race: forall A s ms, state_enable race (A, s) ms <-> ms = Error; (* TODO: is this line necessary? *)
  state_enable_race_actions_spec: forall a1 a2 (A1 A2: resources) (s1 s2 s: state),
      race_actions a1 a2 -> ~ state_enable a1 (A1, s1) Error -> ~ state_enable a2 (A2, s2) Error -> join s1 s2 s -> False
  (* This formalization is critical. Even if there is no ms s.t. stable_enable a1 (s1, A1) ms, it still means (s1, A1) has a domain to perform a1. It's just the result does not match, i.e. the read action. *)
}.

Class Command2Traces_Sresource (P: ProgrammingLanguage) (Ac: Action) (Res: Resource) {Acr: Action_resource Ac Res} {CPR: ConcurrentProgrammingLanguage_Sresource P Res} (c2t: Command2Traces P Ac): Type := {
  Sresource_denote: forall r c, cmd_denote (Sresource r c) = traces_app (singleton_traces (singleton_trace (Aacquire_res r))) (traces_app (cmd_denote c) (singleton_traces (singleton_trace (Arelease_res r))))
}.

Class Command2Traces_Sparallel_resource (P: ProgrammingLanguage) (state: Type) (Ac: Action) (Res: Resource) {AcP: Action_Parallel Ac} {Acr: Action_resource Ac Res} {CPP: ConcurrentProgrammingLanguage_Sparallel P} (c2t: Command2Traces P Ac): Type := {
  Sparallel_denote: forall c1 c2, cmd_denote (Sparallel c1 c2) = traces_interleave (cmd_denote c1) (cmd_denote c2)
}.

Class StructuralResourceAccess (P: ProgrammingLanguage) (Ac: Action) (Res: Resource) {Acr: Action_resource Ac Res} (c2t: Command2Traces P Ac): Type := {
  resource_sequential: forall c r tr, cmd_denote c tr -> start_by_Aacq r tr
}.

Definition resource_no_occur {Ac: Action} {Res: Resource} {Acr: Action_resource Ac Res} (r: resource) (Tr: traces): Prop :=
  forall tr, Tr tr -> ~ List.In (Aacquire_res r) tr /\ ~ List.In (Arelease_res r) tr.

Class SAActionInterpret_resource (state: Type) (Ac: Action) (ac_sem: ActionInterpret state Ac) {J: Join state} (G: action -> Prop) : Prop := {
  frame_property: forall (a: action) (m1 f n1: state) (n2: MetaState state),
    G a ->
    join m1 f n1 ->
    state_enable a n1 n2 ->
    exists m2, lift_join m2 (Terminating f) n2 /\ state_enable a m1 m2
}.

Class KActionInterpret_resource (state: Type) (Ac: Action) (ac_sem: ActionInterpret state Ac) {state_R: Relation state}: Prop := {
  ordered_action_interpret: forall (a: action) (m1 n1: state) (n2: MetaState state),
    m1 <= n1 ->
    state_enable a n1 n2 ->
    exists m2, Partial.forward m2 n2 /\ state_enable a m1 m2
}.

Class KSAActionInterpret_resource (state: Type) (Ac: Action) (ac_sem: ActionInterpret state Ac) {J: Join state} {state_R: Relation state} (G: action -> Prop): Prop := {
  ordered_frame_property: forall (a: action) (m1 f n1' n1: state) (n2: MetaState state),
    G a ->
    join m1 f n1' ->
    n1' <= n1 ->
    state_enable a n1 n2  ->
    exists m2 n2', lift_join m2 (Terminating f) n2' /\ Partial.forward n2' n2 /\ state_enable a m1 m2
}.

Lemma ordered_and_frame_AIr {state: Type} {Ac: Action} {ac_sem: ActionInterpret state Ac} {J: Join state} {state_R: Relation state} (G: action -> Prop):
  SAActionInterpret_resource state Ac ac_sem G ->
  KActionInterpret_resource state Ac ac_sem ->
  KSAActionInterpret_resource state Ac ac_sem G.
Proof.
  intros.
  constructor.
  intros.
  pose proof ordered_action_interpret _ _ _ _ H3 H4 as [n2' [? ?]].
  pose proof frame_property _ _ _ _ _ H1 H2 H6 as [m2 [? ?]].
  exists m2, n2'; auto.
Qed.

Inductive trace_access {state: Type} {Ac: Action} {ac_sem: ActionInterpret state Ac}: trace -> state -> MetaState state -> Prop :=
| trace_access_nil: forall s, trace_access nil s (Terminating s)
| trace_access_NonTerminating: forall a tr s, state_enable a s NonTerminating -> trace_access (cons a tr) s NonTerminating
| trace_access_Error: forall a tr s, state_enable a s Error -> trace_access (cons a tr) s Error
| trace_access_Terminating: forall a tr s s' ms, state_enable a s (Terminating s') -> trace_access tr s' ms -> trace_access (cons a tr) s ms.

Inductive traces_access {state: Type} {Ac: Action} {ac_sem: ActionInterpret state Ac}: traces -> state -> MetaState state -> Prop :=
| traces_access_intro: forall tr (Tr: traces) s ms, Tr tr -> trace_access tr s ms -> traces_access Tr s ms.

(* TODO: maybe not necessary *)
Lemma trace_access_Terminating_inv {state: Type} {Ac: Action} {ac_sem: ActionInterpret state Ac}:
  forall P a tr s ms,
    trace_access (cons a tr) s ms ->
    (forall ms', state_enable a s ms' -> exists s', P s' /\ ms' = Terminating s') ->
    (exists s', P s' /\ trace_access tr s' ms).
Proof.
  intros.
  inversion H; subst.
  + apply H0 in H5.
    destruct H5 as [? [? ?]].
    inversion H2.
  + apply H0 in H5.
    destruct H5 as [? [? ?]].
    inversion H2.
  + apply H0 in H3.
    destruct H3 as [? [? ?]].
    inversion H2; subst.
    exists x; auto.
Qed.

Definition TS2BSS {P: ProgrammingLanguage} {state: Type} {Ac: Action} {Res: Resource} (TS: TraceSemantics P (resources * state) Ac): BigStepSemantics P state :=
  Build_BigStepSemantics _ _ (fun s c ms => traces_access (cmd_denote c) (fun _ => False, s) (lift_function (pair ( fun _ => False)) ms)).

Definition is_upper_bound {A: Type} {R: Relation A} (s: A -> Prop) (a: A): Prop :=
  forall a0, s a0 -> a0 <= a.

Definition greatest {A: Type} {R: Relation A} (s: A -> Prop) (a: A): Prop :=
  s a /\ is_upper_bound s a.

Inductive thread_local_state_enable {state: Type} {Ac: Action} {Res: Resource} {J: Join state} {state_R: Relation state} {Acr: Action_resource Ac Res} {ac_sem: ActionInterpret (resources * state) Ac} (Inv: resource * (state -> Prop) -> Prop) : action -> resources * state -> MetaState (resources * state) -> Prop :=
| thread_local_state_enable_acq: forall r A1 A2 I m f n,
    join A1 (eq r) A2 ->
    Inv (r, I) -> I f ->
    join m f n ->
    thread_local_state_enable Inv (Aacquire_res r) (A1, m) (Terminating (A2, n))
| thread_local_state_enable_rel_succ: forall r A1 A2 I m n,
    join A2 (eq r) A1 ->
    Inv (r, I) ->
    greatest (fun n => exists f, I f /\ join n f m) n ->
    thread_local_state_enable Inv (Arelease_res r) (A1, m) (Terminating (A2, n))
| thread_local_state_enable_rel_fail: forall r A1 A2 I m,
    join A2 (eq r) A1 ->
    Inv (r, I) ->
    (forall n, ~ exists f, I f /\ join n f m) ->
    thread_local_state_enable Inv (Arelease_res r) (A1, m) Error
| thread_local_state_enable_non_resource: forall a s s',
    ~ is_resources_action a ->
    state_enable a s s' ->
    thread_local_state_enable Inv a s s'.

Lemma thread_local_state_enable_non_resource_action {state: Type} {Ac: Action} {Res: Resource} {J: Join state} {state_R: Relation state} {Acr: Action_resource Ac Res} {ac_sem: ActionInterpret (resources * state) Ac}:
  forall Inv a s s',
    ~ is_resources_action a ->
    (state_enable a s s' <-> thread_local_state_enable Inv a s s').
Proof.
  intros.
  split; intros.
  + constructor; auto.
  + inversion H0; subst; solve_resource_action.
    auto.
Qed.

Definition ThreadLocal_ActionInterpret_resource {state: Type} {Ac: Action} {Res: Resource} {J: Join state} {state_R: Relation state} {Acr: Action_resource Ac Res} (ac_sem: ActionInterpret (resources * state) Ac) (Inv: resource * (state -> Prop) -> Prop): ActionInterpret (resources * state) Ac :=
  Build_ActionInterpret _ _ (thread_local_state_enable Inv).

Definition ThreadLocal_BSS {P: ProgrammingLanguage} {state: Type} {Ac: Action} {Res: Resource} {J: Join state} {state_R: Relation state} {Acr: Action_resource Ac Res} (TS: TraceSemantics P (resources * state) Ac) (Inv: resource * (state -> Prop) -> Prop): BigStepSemantics P state :=
  TS2BSS (Build_TraceSemantics _ _ _ c2t (ThreadLocal_ActionInterpret_resource ac_sem Inv)).

Definition ThreadLocal_AIPr {state: Type} {Ac: Action} {Res: Resource} {J: Join state} {state_R: Relation state} {AcP: Action_Parallel Ac} {Acr: Action_resource Ac Res} {nAcPr: NormalAction_Parallel_resource Ac Res} {ac_sem: ActionInterpret (resources * state) Ac} {AIPr: ActionInterpret_Parallel_resource state Ac Res ac_sem}: forall (Inv: resource * (state -> Prop) -> Prop), ActionInterpret_Parallel_resource state Ac Res (ThreadLocal_ActionInterpret_resource ac_sem Inv).
  intros.
  constructor.
  + intros.
    simpl.
    rewrite <- (state_enable_race A s ms).
    rewrite (thread_local_state_enable_non_resource_action Inv) by (apply race_not_resource).
    tauto.
  + intros.
    simpl in H0, H1.
    destruct (res_actions_no_race _ _ H).
    rewrite <- (thread_local_state_enable_non_resource_action Inv) in H0, H1 by auto.
    revert H H0 H1 H2.
    apply state_enable_race_actions_spec.
Qed.
