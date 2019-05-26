Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.omega.Omega.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.

Instance MonoPred_L (A: Type) {R: Relation A} : Language := Build_Language (MonoEnsemble A).

Instance MonoPred_strongGamma (A: Type) {R: Relation A}: ProofTheory (MonoPred_L A) := Build_ProofTheory (MonoPred_L A) (fun x => forall a, proj1_sig x a) (fun Phi x => forall a, (forall y, Phi y -> proj1_sig y a) -> proj1_sig x a).

Instance MonoPred_SM (A: Type) {R: Relation A}: Semantics (MonoPred_L A) (Build_Model A) := Build_Semantics (MonoPred_L A) (Build_Model A) (fun x => proj1_sig x).
