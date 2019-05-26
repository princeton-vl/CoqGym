Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.omega.Omega.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.

Instance Pred_L (A: Type) : Language := Build_Language (A -> Prop).

Instance Pred_strongGamma (A: Type): ProofTheory (Pred_L A) := Build_ProofTheory (Pred_L A) (fun x => forall a, x a) (fun Phi x => forall a, (forall y, Phi y -> y a) -> x a).

Instance Pred_SM (A: Type): Semantics (Pred_L A) (Build_Model A) := Build_Semantics (Pred_L A) (Build_Model A) (fun x => x).
