Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.SeparationLogic.Semantics.SemanticsExtension.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.
Require Import Logic.HoareLogic.BigStepSemantics.
Require Import Logic.HoareLogic.ConcurrentSemantics_Angelic.
Require Import Logic.HoareLogic.HoareTriple_BigStepSemantics.
Require Import Logic.HoareLogic.GuardedHoareTriple_Angelic.

Definition Inv_free
           {resource state: Type}
           (r: resource)
           (Inv: list (resource * (state -> Prop))): Prop :=
  fold_right or True (map (fun ri => fst ri = r) Inv).

Inductive Inv_cons {resource state: Type} (r: resource) (I: state -> Prop):
  list (resource * (state -> Prop)) ->
  list (resource * (state -> Prop)) ->
  Prop :=
| Inv_cons_spec: forall Inv1 Inv2,
   Inv_free r Inv1 ->
   Inv_free r Inv2 ->
   Inv_cons r I (Inv1 ++ Inv2) (Inv1 ++ (r, I) :: Inv2).

Record split_hint {state: Type} {J: Join state} (s: state) : Type := {
  split_piece1: state;
  split_piece2: state;
  split_sound: join split_piece1 split_piece2 s
}.

Module Resource_BigStepSemantics (D: FORWARD).

Export D.

Class Resource_BigStepSemantics
      (P: ProgrammingLanguage)
      {Res: Resource}
      {CPP: ConcurrentProgrammingLanguage_Sparallel P}
      {CPR: ConcurrentProgrammingLanguage_Sresource P Res}
      (state: Type)
      {J: Join state}
      {R: Relation state}
      {po_R: PreOrder Krelation}
      (TLBSS: ThreadLocalBigStepSemantics P state
                (list (resource * (state -> Prop)))): Type :=
{
  hint_Sparallel: forall Inv c1 c2,
    (forall (s: state), split_hint s -> Prop) ->
    hint Inv c1 ->
    hint Inv c2 ->
    hint Inv (Sparallel c1 c2);
  hint_Sresource: forall Inv Inv' I r c,
    Inv_cons r I Inv Inv' ->
    hint Inv c ->
    hint Inv' (Sresource r c);
  access_Sparallel:
    forall Inv
      c1 c2 hs h1 h2 (m: state) (n: MetaState state),
    tl_access Inv m (existT _ _ (hint_Sparallel Inv c1 c2 hs h1 h2)) n ->
    exists (m1 m2: state) H (n1' n2' n1 n2: MetaState state),
    hs m (Build_split_hint _ _ m m1 m2 H) /\
    tl_access Inv m1 (existT _ c1 h1) n1' /\
    tl_access Inv m2 (existT _ c2 h2) n2' /\
    forward n1' n1 /\
    forward n2' n2 /\
    strong_lift_join n1 n2 n;
  access_Sresource:
    forall (I: state -> Prop) Inv Inv' (r: resource) c (h: hint Inv c) m n
      (H_Inv: Inv_cons r I Inv Inv'),
    tl_access Inv' m (existT _ _ (hint_Sresource _ _ _ _ _ H_Inv h)) n ->
    exists m_acq m' n1 n2 n3,
    join m_acq m m' /\
    forward (Terminating m') n1 /\
    lift_tl_access Inv n1 (existT _ c h) n2 /\
    forward n2 n3 /\
    match n3, n with
    | Terminating nn3, Terminating nn => greatest_cut nn3 I nn
    | NonTerminating, NonTerminating => True
    | Error, Error => True
    | _, _ => False
    end /\
    I m_acq
}.

End Resource_BigStepSemantics.

Module Partial := Resource_BigStepSemantics (ProgramState.Partial).
Module Total := Resource_BigStepSemantics (ProgramState.Total).

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelSingleNotation.
Import KripkeModelNotation_Intuitionistic.

Section soundness.

Definition sem_precise
        {L: Language}
        {MD: Model}
        {J: Join model}
        {R: Relation model}
        {po_R: PreOrder Krelation}
        {SM: Semantics L MD}
        (x: expr): Prop :=
  Kdenote_precise (fun m => KRIPKE: m |= x).

Lemma sem_precise_spec
        {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {SL: SeparationLanguage L}
        {MD: Model}
        {J: Join model}
        {R: Relation model}
        {po_R: PreOrder Krelation}
        {SM: Semantics L MD}
        {kiSM: KripkeIntuitionisticSemantics L MD (tt: @Kmodel MD (unit_kMD _)) SM}
        {fsSM: FlatSemantics.SeparatingSemantics L MD (tt: @Kmodel MD (unit_kMD _)) SM}:
  forall m n P Q,
    sem_precise P ->
    greatest_cut m (fun m => KRIPKE: m |= P) n ->
    KRIPKE: m |= P * Q ->
    KRIPKE: n |= Q.
Proof.
  intros.
  rewrite FlatSemantics.sat_sepcon in H1.
  destruct H1 as [m1 [m2 [? [? ?]]]].
  destruct H0 as [? ?].
  destruct H0 as [mf [? ?]].
  specialize (H4 m2).
  eapply sat_mono; [| eassumption].
  apply H4.
  exists m1; split; auto.
Qed.

Import Partial.

Context {P: ProgrammingLanguage}
      {Res: Resource}
      {CPP: ConcurrentProgrammingLanguage_Sparallel P}
      {CPR: ConcurrentProgrammingLanguage_Sresource P Res}
 {MD: Model} {TLBSS: ThreadLocalBigStepSemantics P model (list (resource * (model -> Prop)))} {J: Join model} {R: Relation model} {po_R: PreOrder Krelation} {R_BSS: Resource_BigStepSemantics P model TLBSS}.

Context {L: Language} {minL: MinimunLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD (tt: @Kmodel MD (unit_kMD _)) SM} {fsSM: FlatSemantics.SeparatingSemantics L MD (tt: @Kmodel MD (unit_kMD _)) SM}.

Lemma hoare_resource_partial_sound: forall
  (r: resource)
  (I: expr)
  (Inv Inv': list (resource * (model -> Prop)))
  c P Q,
  guarded_triple_partial_valid Inv (I * P) c (I * Q) ->
  Inv_cons r (fun s: model => s |= I) Inv Inv' ->
  sem_precise I ->
  guarded_triple_partial_valid Inv' P (Sresource r c) Q.
Proof.
  intros.
  unfold guarded_triple_partial_valid, triple_partial_valid in *.
  destruct H as [h ?].
  exists (hint_Sresource _ _ _ _ _ H0 h).
  intros s ms ? ?.
  apply (access_Sresource (fun m => KRIPKE: m |= I) Inv) in H3; auto.
  destruct H3 as [m_acq [m' [n1 [n2 [n3 [? [? [? [? [? ?]]]]]]]]]].
  assert (KRIPKE: m' |= I * P0).
  Focus 1. {
    rewrite FlatSemantics.sat_sepcon.
    eexists; eexists.
    split; [| split]; eassumption.
  } Unfocus.
  destruct n1 as [| |].
  + inversion H4.
  + inversion H5; subst.
    inversion H6; subst.
    destruct ms; tauto.
  + inversion H4; subst.
    eapply sat_mono in H9; [| eassumption].
    inversion H5; subst.
    specialize (H _ _ H9 H11).
    destruct n2.
    - tauto.
    - inversion H6; subst.
      destruct ms; tauto.
    - inversion H6; subst.
      * destruct ms; tauto.
      * destruct ms; auto.
        eapply sat_mono in H; [| eassumption].
        pose proof sem_precise_spec _ _ _ _ H1 H7 H; auto.
Qed.

Lemma hoare_parallel_partial_sound: forall
  (Inv: list (resource * (model -> Prop)))
  c1 c2 P1 P2 Q1 Q2,
  guarded_triple_partial_valid Inv P1 c1 Q1 ->
  guarded_triple_partial_valid Inv P2 c2 Q2 ->
  guarded_triple_partial_valid Inv (P1 * P2) (Sparallel c1 c2) (Q1 * Q2).
Proof.
  intros.
  unfold guarded_triple_partial_valid, triple_partial_valid in *.
  destruct H as [h1 ?], H0 as [h2 ?].
  exists (hint_Sparallel Inv c1 c2
            (fun m sh => KRIPKE: (split_piece1 _ sh) |= P1 /\
                         KRIPKE: (split_piece2 _ sh) |= P2) h1 h2).
  intros s ms ? ?.
  apply access_Sparallel in H2.
  destruct H2 as [s1 [s2 [? [ms1 [ms2 [ms1' [ms2' [? [? [? [? [? ?]]]]]]]]]]]].
  destruct H2 as [H21 H22]; simpl in H21, H22.
  specialize (H _ _ H21 H3).
  specialize (H0 _ _ H22 H4).
  destruct ms1, ms2; try solve [tauto | inversion H5; inversion H6; inversion H7; subst; congruence].
  destruct ms1', ms2'; inversion H5; inversion H6; inversion H7; subst; auto.
  rewrite FlatSemantics.sat_sepcon; exists m1, m2; split; [| split]; auto.
  + eapply sat_mono; eauto.
  + eapply sat_mono; eauto.
Qed.

End soundness.
