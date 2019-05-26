Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Sorting.Permutation.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.List_Func_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimunLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Definition iter_sepcon {L: Language} {sL: SeparationLanguage L} {s'L: SeparationEmpLanguage L} (xs: list expr) : expr := fold_left sepcon xs emp.

Definition iter_wand {L: Language} {sL: SeparationLanguage L} (xs: list expr) (y: expr) : expr := fold_right wand y xs.

Section IterSepconRules.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {sL: SeparationLanguage L}
        {s'L: SeparationEmpLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {sGamma: SeparationLogic L Gamma}
        {EmpGamma: EmpSeparationLogic L Gamma}.

Lemma sepcon_iter_sepcon:
  forall xs ys,
    |-- iter_sepcon xs * iter_sepcon ys <--> iter_sepcon (xs ++ ys).
Proof.
  intros.
  apply (@assoc_prodp_fold_left_equiv _ _ _ _ _ _ _ _ sepcon_Mono sepcon_Assoc sepcon_LU sepcon_RU).
Qed.

(* TODO: Should this really be an instance? *)
Instance proper_iter_sepcon_impp:
  Proper (Forall2 (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) iter_sepcon.
Proof.
  intros.
  unfold iter_sepcon.
  hnf; intros.
  exact (proper_fold_left' sepcon _ _ H emp emp (provable_impp_refl _)).
Qed.

(* TODO: Should this really be an instance? *)
Instance proper_iter_sepcon_iffp:
  Proper (Forall2 (fun x y => |-- iffp x y) ==> (fun x y => |-- iffp x y)) iter_sepcon.
Proof.
  intros.
  unfold iter_sepcon.
  hnf; intros.
  exact (proper_fold_left' sepcon _ _ H emp emp (provable_iffp_refl _)).
Qed.

(* TODO: Should this really be an instance? *)
Instance proper_iter_sepcon_Permutation: Proper (@Permutation expr ==> (fun x y => |-- iffp x y)) iter_sepcon.
Proof.
  intros.
  hnf; intros.
  apply (@assoc_fold_left_Permutation _ _ _ _ _ _ _ sepcon_Mono sepcon_Comm sepcon_Assoc); auto.
Qed.

End IterSepconRules.
