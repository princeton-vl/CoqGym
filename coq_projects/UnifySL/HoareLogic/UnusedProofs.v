(*
Class NormalImperativeProgrammingLanguage (Imp: ImperativeProgrammingLanguage): Type := {
  Ssequence: cmd -> cmd -> cmd;
  Sskip: cmd;
  neq_Sskip_Ssequence: forall c1 c2, Sskip <> Ssequence c1 c2
}.

Class SmallStepSemantics (Imp: ImperativeProgrammingLanguage) (MD: Model): Type := {
  state := model;
  exceptional_state: Type;
  step: cmd * state -> cmd * state + exceptional_state -> Prop
}.

Definition fmap_sum_left {A1 A2 B: Type} (f: A1 -> A2) (x: A1 + B): A2 + B :=
  match x with
  | inl a => inl (f a)
  | inr b => inr b
  end.

Definition fmap_Sseq {Imp: ImperativeProgrammingLanguage} {nImp: NormalImperativeProgrammingLanguage Imp} {MD: Model} {sss: SmallStepSemantics Imp MD} (mcs: cmd * state + exceptional_state) (c0: cmd) :=
  fmap_sum_left (fun cs: cmd * state => let (c, s) := cs in (Ssequence c c0, s)) mcs.

Definition fmap_pair_cmd {Imp: ImperativeProgrammingLanguage} {nImp: NormalImperativeProgrammingLanguage Imp} {MD: Model} {sss: SmallStepSemantics Imp MD} (ms: state + exceptional_state) (c: cmd) :=
  fmap_sum_left (pair c) ms.

Class NormalSmallStepSemantics (Imp: ImperativeProgrammingLanguage) {nImp: NormalImperativeProgrammingLanguage Imp} (MD: Model) (sss: SmallStepSemantics Imp MD): Type := {
  step_Ssequence1: forall c1 c2 s1 mcs2,
    c2 <> Sskip ->
    ((exists mcs1, step (c1, s1) mcs1 /\ mcs2 = fmap_Sseq mcs1 c2) <->
     step (Ssequence c1 c2, s1) mcs2);
  step_Ssequence2: forall c s mcs,
    step (c, s) mcs <->
    step (Ssequence Sskip c, s) mcs;
  step_progress: forall c s, c = Sskip <-> exists mcs, step (c, s) mcs
}.

Inductive iter_step {Imp: ImperativeProgrammingLanguage} {nImp: NormalImperativeProgrammingLanguage Imp} {MD: Model} {sss: SmallStepSemantics Imp MD}: cmd * state + exceptional_state -> cmd * state + exceptional_state -> Prop :=
| iter_step_refl: forall mcs, iter_step mcs mcs
| iter_step_step: forall cs mcs1 mcs2, step cs mcs1 -> iter_step mcs1 mcs2 -> iter_step (inl cs) mcs2.

Definition access {Imp: ImperativeProgrammingLanguage} {nImp: NormalImperativeProgrammingLanguage Imp} {MD: Model} {sss: SmallStepSemantics Imp MD} (ms_init: state + exceptional_state) (c: cmd) (ms_end: state + exceptional_state): Prop :=
  iter_step (fmap_pair_cmd ms_init c) (fmap_pair_cmd ms_end Sskip).
*)
(*
Lemma exception_go_nowhere: forall e c ms,
  access (inr e) c ms <->
  ms = inr e.
Proof.
  intros.
  split; intros.
  + hnf in H.
    remember (fmap_pair_cmd (inr e) c) as mcs1 eqn:?H.
    remember (fmap_pair_cmd ms Sskip) as mcs2 eqn:?H.
    induction H.
    - subst.
      destruct ms; inversion H1.
      subst; auto.
    - subst.
      inversion H0.
  + subst.
    hnf.
    simpl.
    apply iter_step_refl.
Qed.

Lemma aux_sequence_sound: forall c1 c2 ms1 ms3,
  access ms1 (Ssequence c1 c2) ms3 ->
  exists ms2,
  access ms1 c1 ms2 /\ access ms2 c2 ms3.
Proof.
  intros.
  destruct ms1 as [s1 | e1].
  Focus 2. {
    exists (inr e1).
    rewrite exception_go_nowhere in H.
    subst.
    split; rewrite exception_go_nowhere; auto.
  } Unfocus.
  unfold access in H.
  remember (fmap_pair_cmd (inl s1) (Ssequence c1 c2)) as mcs1 eqn:?H.
  remember (fmap_pair_cmd ms3 Sskip) as mcs2 eqn:?H.
  revert c1 H0.
  induction H; intros; subst.
  + destruct ms3 as [s3 | e3]; inversion H0.
    apply neq_Sskip_Ssequence in H1; contradiction.
  + rename IHiter_step into IH.
    specialize (IH eq_refl).
    inversion H2; subst; clear H2.
*)(*
Lemma hoare_sequence_sound: forall c1 c2 P Q R,
  triple_valid guard P c1 Q ->
  triple_valid guard Q c2 R ->
  triple_valid guard P (Ssequence c1 c2) R.
Proof.
  intros.
  hnf; intros.
  unfold access in H1.
  remember (fmap_pair_cmd (inl s_pre) (Ssequence c1 c2)) as mcs1 eqn:?H.
  remember (fmap_pair_cmd ms_post Sskip) as mcs2 eqn:?H.
  revert P c1 H H2 H3.
  induction H1; intros; subst.
  + destruct ms_post as [s_post | e]; [| inversion H3].
    inversion H3; clear H3.
    apply neq_Sskip_Ssequence in H4; contradiction.
  + rename IHiter_step into IH.
    specialize (IH eq_refl).
Abort.

*)