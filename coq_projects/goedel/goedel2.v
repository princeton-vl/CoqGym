Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import folProp.
Require Import folProof.
Require Import folReplace.
Require Import folLogic3.
Require Import subProp.
Require Import ListExt.
(*
Require Import NNtheory.
*)
Require Import fixPoint.
Require Import NN2PA.
Require Import codeSysPrf.
Require Import PAtheory.
Require Import code.
(*
Require Import PRrepresentable.
Require Import expressible.
*)
Require Import checkPrf.
Require Import codeNatToTerm.
Require Import rosserPA.

Unset Standard Proposition Elimination Names.

Section Goedel's_2nd_Incompleteness.

Variable T : System.

Hypothesis extendsPA : Included _ PA T.

Variable repT : Formula.
Variable v0 : nat.
Hypothesis
  freeVarRepT : forall v : nat, In v (freeVarFormula LNT repT) -> v = v0.
Hypothesis
  expressT1 :
    forall f : Formula,
    mem _ T f ->
    SysPrf T (substituteFormula LNT repT v0 (natToTerm (codeFormula f))).
Hypothesis
  expressT2 :
    forall f : Formula,
    ~ mem _ T f ->
    SysPrf T
      (notH (substituteFormula LNT repT v0 (natToTerm (codeFormula f)))).

Definition codeSysPf := 
  (codeSysPf LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR
    codeArityLNTFIsPR codeArityLNTRIsPR (LNT2LNN_formula repT) v0).

(*
Definition codeSysPrfCorrect2 :=
  codeSysPrfCorrect2 LNT codeLNTFunction codeLNTRelation codeArityLNTF
    codeArityLNTR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNTRIsPR
    codeArityLNTRIsCorrect1 T' extendsNN T (LNT2LNN_formula repT) v0
    freeVarRepT' expressT'2.

Definition codeSysPrfCorrect3 :=
  codeSysPrfCorrect3 LNT codeLNTFunction codeLNTRelation codeArityLNTF
    codeArityLNTR codeArityLNTFIsPR codeArityLNTFIsCorrect1
    codeArityLNTFIsCorrect2 codeArityLNTRIsPR codeArityLNTRIsCorrect1
    codeArityLNTRIsCorrect2 codeLNTFunctionInj codeLNTRelationInj T'
    extendsNN.
*)

Section Goedel1PA.

(*Let's reuse some of our work from rosserPA*)

Definition T' := T' T.

Definition extendsNN := extendsNN T.

Definition Tprf2T'prf := Tprf2T'prf T.

Definition expressT'1 := expressT'1 T repT v0 expressT1.

Definition expressT'2 := expressT'2 T repT v0 expressT2.

Definition freeVarRepT' := freeVarRepT' repT v0 freeVarRepT.

Definition codeSysPfCorrect :=
  codeSysPfCorrect LNT codeLNTFunction codeLNTRelation codeArityLNTF
    codeArityLNTR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNTRIsPR
    codeArityLNTRIsCorrect1 T' extendsNN T (LNT2LNN_formula repT) v0
    freeVarRepT' expressT'1.

Definition G := let (a,_) := FixPointLNT (notH (LNN2LNT_formula codeSysPf)) 0 in a.

Definition box (f:Formula) := (substituteFormula LNT (LNN2LNT_formula codeSysPf) 0 (natToTerm (codeFormula f))).

Lemma GS : SysPrf T (iffH G (notH (box G))).
Proof.
unfold G.
destruct (FixPointLNT (notH (LNN2LNT_formula codeSysPf)) 0).
destruct a.
unfold box.
apply sysExtend with PA.
assumption.
rewrite <- (subFormulaNot LNT).
apply H.
Qed.

Lemma HBL1 : forall f, SysPrf T f -> SysPrf T (box f).
Proof.
intros x H.
unfold box.
apply impE with (LNN2LNT_formula (substituteFormula LNN codeSysPf 0 
  (LNN.natToTerm (codeFormula x)))).
replace (natToTerm (codeFormula x)) with (LNN2LNT_term (LNN.natToTerm (codeFormula x))).
apply iffE1.
apply LNN2LNT_subFormula.
induction (codeFormula x).
reflexivity.
simpl.
rewrite IHn.
reflexivity.
assert (forall f : fol.Formula LNN,
     mem (fol.Formula LNN) T' f ->
     exists Axm : Formulas,
       ex
         (fun _ : Prf LNT Axm (LNN2LNT_formula f) =>
          forall g : Formula, In g Axm -> mem (fol.Formula LNT) T g) /\
       (forall v : nat,
        In v (freeVarListFormula LNT Axm) -> In v (freeVarFormula LNN f))).
intros.
destruct H0.
assert (SysPrf PA (LNN2LNT_formula x0)).
apply NN2PA.
apply (folLogic.Axm).
assumption.
destruct H1.
destruct H1.
exists x1.
split.
exists x2.
intros.
apply extendsPA.
apply H1.
assumption.
intros.
elim closedPA with v.
destruct (In_freeVarListFormulaE _ _ _ H2).
exists x3.
split.
tauto.
apply H1.
tauto.
exists ((LNN2LNT_formula x0)::nil).
split.
exists (AXM LNT (LNN2LNT_formula x0)).
intros.
simpl in H1.
destruct H1.
rewrite <- H1.
apply H0.
contradiction.
intros.
destruct (In_freeVarListFormulaE _ _ _ H1).
simpl in H2.
destruct H2.
destruct H3.
rewrite <- H3 in H2.
apply LNN2LNT_freeVarFormula1.
assumption.
contradiction.
destruct (codeSysPfCorrect _ H).
destruct H1.
destruct (translatePrf T' T H0 
 (substituteFormula LNN codeSysPf 0 (LNN.natToTerm (codeFormula x)))
 x0 x1 H1).
exists x2.
destruct H2.
assumption.
Qed.

Lemma FirstIncompletenessA : SysPrf T G -> Inconsistent LNT T.
Proof.
intros.
unfold G in H.
destruct (FixPointLNT (notH (LNN2LNT_formula codeSysPf)) 0) as [x [H1 H2]].
unfold Inconsistent in |- *.
intros.
apply contradiction with x.
assumption.
apply
 impE
  with
    (notH
       (substituteFormula LNT (notH (LNN2LNT_formula codeSysPf)) 0
          (natToTerm
             (codeFormula x)))).
apply cp2.
apply iffE1.
apply sysExtend with PA.
assumption.
apply H1.
rewrite (subFormulaNot LNT).
apply nnI.
change (substituteFormula LNT (LNN2LNT_formula codeSysPf) 0
     (natToTerm (codeFormula x))) with (box x).
apply HBL1.
assumption.
Qed.

End Goedel1PA.

Definition F := (notH (forallH 0 (equal (var 0) (var  0)))).

(*Show Con is a sentence?*)
(*Make Con say not all formulas are provable*)
Definition Con := notH (box F).

Hypothesis HBL2 : forall f, SysPrf T (impH (box f) (box (box f))).
Hypothesis HBL3 : forall f g, SysPrf T (impH (box (impH f g)) (impH (box f) (box g))).
(*
Lemma HBL3 : forall f g, SysPrf T (impH (box f) (impH (box (impH f g)) (box g))).
Proof.
intros.
apply sysExtend with PA.
assumption.
unfold box.
unfold codeSysPf, codeSysPrf.codeSysPf.
rewrite LNN2LNT_exist.
repeat rewrite (subFormulaExist LNT).
destruct (eq_nat_dec 1 0).
discriminate e.
destruct (In_dec eq_nat_dec 1 (freeVarTerm LNT (natToTerm (codeFormula g)))).
elim (closedNatToTerm _ _ i).
destruct (In_dec eq_nat_dec 1 (freeVarTerm LNT (natToTerm (codeFormula f)))).
elim (closedNatToTerm _ _ i).
destruct (In_dec eq_nat_dec 1 (freeVarTerm LNT (natToTerm (codeFormula (impH f g))))).
elim (closedNatToTerm _ _ i).
clear n n0 n1 n2.
apply impI.
apply existSys.
apply closedPA.
intro H.
unfold impH in H.
SimplFreeVar.
apply impI.
apply existI with (cPair 1
        (cPair
           (cPair (cPair 1 (cPair (codeFormula f) (codeFormula g)))
              (codePrf _ _ rec1)) (cPair (codeFormula A) (codePrf _ _ rec2))).
*)

Theorem SecondIncompletness : 
SysPrf T Con -> Inconsistent LNT T.
Proof.
intros H.
apply FirstIncompletenessA.
apply impE with Con; auto.
apply cp1.
apply impTrans with (box G).
apply cp1.
apply impTrans with G.
apply iffE2.
apply GS.
apply impI.
apply nnI.
apply Axm.
right.
constructor.
unfold Con.
apply impI.
apply nnI.
apply impE with (box (box G)).
apply impE with (box (impH (box G) F)).
apply sysWeaken.
apply HBL3.
apply impE with (box G).
apply impE with (box (impH G (impH (box G) F))).
apply sysWeaken.
apply HBL3.
apply sysWeaken.
apply HBL1.
apply impTrans with (notH (box G)).
apply iffE1.
apply GS.
apply impI.
apply impI.
apply contradiction with (box G).
apply Axm.
right; constructor.
apply Axm.
left; right; constructor.
apply Axm; right; constructor.
apply impE with (box G).
apply sysWeaken.
apply HBL2.
apply Axm; right; constructor.
Qed.

End Goedel's_2nd_Incompleteness.