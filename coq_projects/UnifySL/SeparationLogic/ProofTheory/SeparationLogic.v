Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.SeparationLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Class SeparationLogic
        (L: Language)
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {sL: SeparationLanguage L}
        (Gamma: ProofTheory L)
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma} := {
  sepcon_comm_impp: forall x y, |-- x * y --> y * x;
  sepcon_assoc: forall x y z, |-- x * (y * z) <--> (x * y) * z;
  wand_sepcon_adjoint: forall x y z, |-- x * y --> z <-> |-- x --> (y -* z)
}.

Class EmpSeparationLogic
        (L: Language)
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {sL: SeparationLanguage L}
        {s'L: SeparationEmpLanguage L}
        (Gamma: ProofTheory L)
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {sGamma: SeparationLogic L Gamma} := {
  sepcon_emp: forall x, |-- x * emp <--> x
}.

Class ExtSeparationLogic
        (L: Language)
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {sL: SeparationLanguage L}
        (Gamma: ProofTheory L)
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {sGamma: SeparationLogic L Gamma} := {
  sepcon_ext: forall x, |-- x --> x * TT
}.

Class NonsplitEmpSeparationLogic
        (L: Language)
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {sL: SeparationLanguage L}
        {s'L: SeparationEmpLanguage L}
        (Gamma: ProofTheory L)
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {sGamma: SeparationLogic L Gamma}
        {eGamma: EmpSeparationLogic L Gamma} := {
  emp_sepcon_truep_elim: forall x, |-- x * TT && emp --> x
}.

Class DupEmpSeparationLogic
        (L: Language)
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {sL: SeparationLanguage L}
        {s'L: SeparationEmpLanguage L}
        (Gamma: ProofTheory L)
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {sGamma: SeparationLogic L Gamma}
        {eGamma: EmpSeparationLogic L Gamma} := {
  emp_dup: forall x, |-- x && emp --> x * x
}.

Class MallocFreeSeparationLogic
        (L: Language)
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {sL: SeparationLanguage L}
        {s'L: SeparationEmpLanguage L}
        (Gamma: ProofTheory L)
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {sGamma: SeparationLogic L Gamma}
        {eGamma: EmpSeparationLogic L Gamma} := {
  MallocFreeSeparationLogic_NonsplitEmpSeparationLogic :>
    NonsplitEmpSeparationLogic L Gamma;
  MallocFreeSeparationLogic_DupEmpSeparationLogic :>
    DupEmpSeparationLogic L Gamma
}.

Class GarbageCollectSeparationLogic
        (L: Language)
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {sL: SeparationLanguage L}
        (Gamma: ProofTheory L)
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {sGamma: SeparationLogic L Gamma} := {
  sepcon_elim1: forall x y, |-- x * y --> x
}.

Section DerivableRules.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {sL: SeparationLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {sGamma: SeparationLogic L Gamma}.

Lemma wand_sepcon_Adj: Adjointness L Gamma sepcon wand.
Proof.
  constructor.
  intros.
  apply wand_sepcon_adjoint.
Qed.

Lemma sepcon_orp_distr_l: forall (x y z: expr),
  |-- (x || y) * z <--> x * z || y * z.
Proof.
  intros.
  apply (@prodp_orp_distr_l _ _ _ _ _ _ _ _ wand_sepcon_Adj).
Qed.

Lemma falsep_sepcon: forall (x: expr),
  |-- FF * x <--> FF.
Proof.
  intros.
  apply (@falsep_prodp _ _ _ _ _ _ _ _ wand_sepcon_Adj).
Qed.

Lemma provable_wand_sepcon_modus_ponens1: forall (x y: expr),
  |-- (x -* y) * x --> y.
Proof.
  intros.
  apply (@adjoint_modus_ponens _ _ _ _ _ _ wand_sepcon_Adj).
Qed.

Lemma wand_andp: forall x y z: expr,
  |-- x -* y && z <--> (x -* y) && (x -* z).
Proof.
  intros.
  apply (@funcp_andp_distr_r _ _ _ _ _ _ _ _ wand_sepcon_Adj); auto.
Qed.

Lemma sepcon_Comm: Commutativity L Gamma sepcon.
Proof.
  constructor.
  intros.
  apply sepcon_comm_impp.
Qed.

Lemma sepcon_comm: forall (x y: expr),
  |-- x * y <--> y * x.
Proof.
  intros.
  apply (@prodp_comm _ _ _ _ _ _ _ sepcon_Comm).
Qed.

Lemma sepcon_orp_distr_r: forall (x y z: expr),
  |-- x * (y || z) <--> x * y || x * z.
Proof.
  intros.
  apply (@prodp_orp_distr_r _ _ _ _ _ _ _ _ wand_sepcon_Adj sepcon_Comm).
Qed.

Lemma sepcon_falsep: forall (x: expr),
  |-- x * FF <--> FF.
Proof.
  intros.
  apply (@prodp_falsep _ _ _ _ _ _ _ _ wand_sepcon_Adj sepcon_Comm).
Qed.

Lemma provable_wand_sepcon_modus_ponens2: forall (x y: expr),
  |-- x * (x -* y) --> y.
Proof.
  intros.
  rewrite (sepcon_comm x (x -* y)).
  apply provable_wand_sepcon_modus_ponens1.
Qed.

Lemma wand_mono: forall x1 x2 y1 y2, |-- x2 --> x1 -> |-- y1 --> y2 -> |-- (x1 -* y1) --> (x2 -* y2).
Proof.
  intros.
  apply (@funcp_mono _ _ _ _ _ _ wand_sepcon_Adj sepcon_Comm); auto.
Qed.

Lemma orp_wand: forall x y z: expr,
  |-- (x || y) -* z <--> (x -* z) && (y -* z).
Proof.
  intros.
  apply (@orp_funcp _ _ _ _ _ _ _ _ wand_sepcon_Adj sepcon_Comm); auto.
Qed.

Lemma sepcon_Mono: Monotonicity L Gamma sepcon.
Proof.
  apply @Adjoint2Mono with (funcp := wand).
  + auto.
  + apply wand_sepcon_Adj.
  + apply sepcon_Comm.
Qed.

Lemma sepcon_mono: forall x1 x2 y1 y2, |-- x1 --> x2 -> |-- y1 --> y2 -> |-- (x1 * y1) --> (x2 * y2).
Proof.
  intros.
  apply (@prodp_mono _ _ _ _ sepcon_Mono); auto.
Qed.

Lemma sepcon_Assoc: Associativity L Gamma sepcon.
Proof.
  apply Build_Associativity'.
  intros.
  rewrite sepcon_assoc.
  apply provable_iffp_refl.
Qed.

Lemma sepcon_LU {s'L: SeparationEmpLanguage L} {eGamma: EmpSeparationLogic L Gamma}: LeftUnit L Gamma emp sepcon.
Proof.
  apply Build_LeftUnit'.
  intros.
  rewrite sepcon_comm.
  apply sepcon_emp.
Qed.

Lemma sepcon_RU {s'L: SeparationEmpLanguage L} {eGamma: EmpSeparationLogic L Gamma}: RightUnit L Gamma emp sepcon.
Proof.
  apply Build_RightUnit'.
  intros.
  apply sepcon_emp.
Qed.

Lemma sepcon_elim2: forall {gcsGamma: GarbageCollectSeparationLogic L Gamma} (x y: expr),
  |-- x * y --> y.
Proof.
  intros.
  rewrite (sepcon_comm x y).
  apply sepcon_elim1.
Qed.

Lemma emp_sepcon_elim1: forall {s'L: SeparationEmpLanguage L} {eGamma: EmpSeparationLogic L Gamma} {nssGamma: NonsplitEmpSeparationLogic L Gamma} x y,
  |-- x * y && emp --> x.
Proof.
  intros.
  rewrite <- (emp_sepcon_truep_elim x) at 2.
  apply andp_proper_impp; [| apply provable_impp_refl].
  apply sepcon_mono; [apply provable_impp_refl |].
  apply solve_impp_elim_left, provable_truep.
Qed.

Lemma emp_sepcon_elim2: forall {s'L: SeparationEmpLanguage L} {eGamma: EmpSeparationLogic L Gamma} {nssGamma: NonsplitEmpSeparationLogic L Gamma} x y,
  |-- x * y && emp --> y.
Proof.
  intros.
  rewrite sepcon_comm.
  apply emp_sepcon_elim1.
Qed.

End DerivableRules.
