(*
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.SublistT.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.QuantifierLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.

Local Open Scope logic_base.
Local Open Scope syntax.

Class BindedProofTheory (BL: BinderLanguage): Type := {
  binded_Gamma:> forall ts, ProofTheory (binded_L ts)
}.

Class QuantifierLogic
      (BL: BinderLanguage)
      {nL: forall ts, NormalLanguage (binded_L ts)}
      {qL: QuantifierLanguage BL}
      (BGamma: BindedProofTheory BL)
      {nGamma: forall ts, NormalProofTheory (binded_L ts) (binded_Gamma ts)}
      {mpGamma: forall ts, MinimunPropositionalLogic (binded_L ts) (binded_Gamma ts)} :=
{
  allp_elim: forall (t: type) (ts: list type) (x: binded_expr (t :: ts)) (e: binded_term ts t),
    |-- allp x --> ins_expr x e;
  allp_gen: forall (t: type) (ts: list type) (x: binded_expr ts) (y: binded_expr (t :: ts)),
    |-- lift_expr (sublistT_cons t (sublistT_refl ts)) x --> y ->
    |-- x --> allp y;
  exp_intros: forall (t: type) (ts: list type) (x: binded_expr (t :: ts)) (e: binded_term ts t),
    |-- ins_expr x e --> exp x;
  exp_gen: forall (t: type) (ts: list type) (x: binded_expr (t :: ts)) (y: binded_expr ts),
    |-- x --> lift_expr (sublistT_cons t (sublistT_refl ts)) y ->
    |-- exp x --> y
}.

*)