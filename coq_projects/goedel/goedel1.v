Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import folProp.
Require Import folProof.
Require Import subProp.
Require Import ListExt.
Require Import fixPoint.
Require Import codeSysPrf.
Require Import wConsistent.
Require Import NN.
Require Import code.

Require Import checkPrf.

Section Goedel's_1st_Incompleteness.

Definition codeFormula := codeFormula LNN codeLNTFunction codeLNNRelation.

Variable T : System.

Hypothesis extendsNN : Included _ NN T.

Variable repT : Formula.
Variable v0 : nat.
Hypothesis
  freeVarRepT : forall v : nat, In v (freeVarFormula LNN repT) -> v = v0.
Hypothesis
  expressT1 :
    forall f : Formula,
    mem _ T f ->
    SysPrf T (substituteFormula LNN repT v0 (natToTerm (codeFormula f))).
Hypothesis
  expressT2 :
    forall f : Formula,
    ~ mem _ T f ->
    SysPrf T
      (notH (substituteFormula LNN repT v0 (natToTerm (codeFormula f)))).

Definition codeSysPrf :=
  codeSysPrf LNN codeLNTFunction codeLNNRelation codeArityLNTF codeArityLNNR
    codeArityLNTFIsPR codeArityLNNRIsPR repT v0.

Definition codeSysPf :=
  codeSysPf LNN codeLNTFunction codeLNNRelation codeArityLNTF codeArityLNNR
    codeArityLNTFIsPR codeArityLNNRIsPR repT v0.

Definition codeSysPfCorrect :=
  codeSysPfCorrect LNN codeLNTFunction codeLNNRelation codeArityLNTF
    codeArityLNNR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNNRIsPR
    codeArityLNNRIsCorrect1 T extendsNN T repT v0 freeVarRepT expressT1.

Definition codeSysPrfCorrect2 :=
  codeSysPrfCorrect2 LNN codeLNTFunction codeLNNRelation codeArityLNTF
    codeArityLNNR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNNRIsPR
    codeArityLNNRIsCorrect1 T extendsNN T repT v0 freeVarRepT expressT2.

Definition codeSysPrfCorrect3 :=
  codeSysPrfCorrect3 LNN codeLNTFunction codeLNNRelation codeArityLNTF
    codeArityLNNR codeArityLNTFIsPR codeArityLNTFIsCorrect1
    codeArityLNTFIsCorrect2 codeArityLNNRIsPR codeArityLNNRIsCorrect1
    codeArityLNNRIsCorrect2 codeLNTFunctionInj codeLNNRelationInj T extendsNN.
 
Definition G := let (a,_) := FixPointLNN (notH codeSysPf) 0 in a.

Lemma freeVarG : forall v : nat, ~ In v (freeVarFormula LNN G).
Proof.
unfold G.
destruct (FixPointLNN (notH codeSysPf) 0) as [x [H1 H2]].
unfold not in |- *; intros.
induction (H2 v).
rename H3 into foo.
rename H0 into H3.
absurd (v = 0).
eapply In_list_remove2.
apply H3.
assumption.
eapply
 (freeVarCodeSysPf LNN codeLNTFunction codeLNNRelation codeArityLNTF
    codeArityLNNR codeArityLNTFIsPR codeArityLNNRIsPR)
 .
apply freeVarRepT.
assert
 (H5:(forall f : Formula,
  In v (freeVarFormula LNN (notH f)) -> In v (freeVarFormula LNN f))).
intros f H5.
apply H5.
apply H5.
eapply In_list_remove1.
unfold codeSysPf in H3.
apply H3.
assumption.
Qed.

Lemma FirstIncompletenessA :
 SysPrf T G -> Inconsistent LNN T.
Proof.
intros.
unfold G in H.
destruct (FixPointLNN (notH codeSysPf) 0) as [x [H1 H2]].
unfold Inconsistent in |- *.
intros.
apply contradiction with x.
assumption.
apply
 impE
  with
    (notH
       (substituteFormula LNN (notH codeSysPf) 0
          (codeNatToTerm.natToTermLNN
             (code.codeFormula LNN codeLNTFunction codeLNNRelation x)))).
apply cp2.
apply iffE1.
apply sysExtend with NN.
assumption.
apply H1.
rewrite (subFormulaNot LNN).
apply nnI.
apply codeSysPfCorrect.
assumption.
Qed.

(*I don't beleive I can prove

 (SysPrf T (notH G))->(wInconsistent T))
 
 So instead I prove: *)

Lemma FirstIncompletenessB :
 wConsistent T -> ~ SysPrf T (notH G).
Proof.
intros.
assert (con : (forall f:Formula, SysPrf T f) -> False).
intros.
induction (wCon2Con T).
apply H1.
apply H0.
assumption.
unfold G.
destruct (FixPointLNN (notH codeSysPf) 0) as [x [H1 H2]].
unfold not in |- *; intros.
set (codeX := code.codeFormula LNN codeLNTFunction codeLNNRelation x) in *.
unfold wConsistent in H.
set
 (y :=
  notH
    (substituteFormula LNN codeSysPrf 0 (codeNatToTerm.natToTermLNN codeX)))
 in *.
assert (forall x : nat, In x (freeVarFormula LNN y) -> 1 = x).
intros.
unfold y in H3.
assert
 (In x0
    (freeVarFormula LNN
       (substituteFormula LNN codeSysPrf 0 (codeNatToTerm.natToTermLNN codeX)))).
apply H3.
induction (freeVarSubFormula3 _ _ _ _ _ H4).
destruct x0 as [| n].
elim (In_list_remove2 _ _ _ _ _ H5).
reflexivity.
destruct n.
reflexivity.
elim (le_not_lt (S (S n)) 1).
assert (In (S (S n)) (freeVarFormula LNN codeSysPrf)).
eapply In_list_remove1.
apply H5.
apply (freeVarCodeSysPrf _ _ _ _ _ _ _ _ _ freeVarRepT _ H6).
apply lt_n_S.
apply lt_O_Sn.
elim (closedNatToTerm _ _ H5).
induction (H _ _ H3).
unfold y in H4.
induction
 (eq_nat_dec
    (checkPrf LNN codeLNTFunction codeLNNRelation codeArityLNTF codeArityLNNR
       (codeFormula x) x0) 0).
apply H4.
rewrite (subFormulaNot LNN).
unfold codeSysPrf, codeX in |- *.
apply codeSysPrfCorrect3.
unfold not in |- *; intros.
assert
 (checkPrf LNN codeLNTFunction codeLNNRelation codeArityLNTF codeArityLNNR
    (codeFormula x) (codePrf LNN codeLNTFunction codeLNNRelation A x p) =
  S (cPair.codeList (map codeFormula A))).
apply
 (checkPrfCorrect1 LNN codeLNTFunction codeLNNRelation codeArityLNTF
    codeArityLNNR codeArityLNTFIsCorrect1 codeArityLNNRIsCorrect1 A x p).
rewrite <- H5 in H6.
rewrite H6 in a.
discriminate a.
assert
 (checkPrf LNN codeLNTFunction codeLNNRelation codeArityLNTF codeArityLNNR
    (codeFormula x) x0 <> 0).
assumption.
clear b.
decompose record
 (checkPrfCorrect2 LNN codeLNTFunction codeLNNRelation codeArityLNTF
    codeArityLNNR codeArityLNTFIsCorrect1 codeArityLNTFIsCorrect2
    codeArityLNNRIsCorrect1 codeArityLNNRIsCorrect2 codeLNTFunctionInj
    codeLNNRelationInj _ _ H5).
assert (x1 = x).
eapply codeFormulaInj.
apply codeLNTFunctionInj.
apply codeLNNRelationInj.
apply H7.
cut (codePrf LNN codeLNTFunction codeLNNRelation x2 x1 x3 = x0).
generalize x3.
rewrite H6.
intros.
clear H6 H8 x3 H7 x1.
assert
 (~
  (forall g : fol.Formula LNN, In g x2 -> mem (fol.Formula LNN) T g)).
unfold not in |- *; intros.
assert (SysPrf T x).
unfold not in |- *; intros.
exists x2.
exists x4.
intros.
apply H6.
assumption.
apply con.
unfold Inconsistent in |- *.
intros.
apply contradiction with x; assumption.
assert (~ (exists g : Formula, In g x2 /\ ~ mem _ T g)).
unfold not in |- *; intros.
apply H4.
rewrite (subFormulaNot LNN).
unfold codeSysPrf, codeX in |- *.
rewrite <- H9.
apply codeSysPrfCorrect2.
assumption.
clear x4 H9.
induction x2 as [| a x2 Hrecx2].
apply H6.
intros.
elim H8.
assert
 (~ (exists g : Formula, In g x2 /\ ~ mem (fol.Formula LNN) T g)).
unfold not in |- *; intros.
apply H7.
induction H8 as (x1, H8).
exists x1.
simpl in |- *.
tauto.
assert
 (~
  ~
  (mem (fol.Formula LNN) T a \/ ~ mem (fol.Formula LNN) T a)).
tauto.
apply H9.
unfold not in |- *; intros.
induction H10 as [H10| H10].
apply Hrecx2.
unfold not in |- *; intros.
apply H6.
intros.
induction H12 as [H12| H12].
rewrite <- H12.
assumption.
apply H11.
assumption.
assumption.
apply H7.
exists a.
simpl in |- *.
auto.
assumption.
apply
 impE
  with
    (notH
       (substituteFormula LNN (notH codeSysPf) 0
          (codeNatToTerm.natToTermLNN codeX))).
unfold codeSysPf, codeSysPrf.codeSysPf, y in |- *.
fold codeSysPrf in |- *.
rewrite (subFormulaNot LNN).
apply
 impTrans
  with
    (substituteFormula LNN (existH 1 codeSysPrf) 0
       (codeNatToTerm.natToTermLNN codeX)).
apply impI.
apply nnE.
apply Axm; right; constructor.
apply sysExtend with NN.
assumption.
apply impI.
rewrite (subFormulaExist LNN).
induction (eq_nat_dec 1 0).
discriminate a.
induction
 (In_dec eq_nat_dec 1 (freeVarTerm LNN (codeNatToTerm.natToTermLNN codeX))).
elim (closedNatToTerm _ _ a).
clear b b0.
apply existSys.
apply closedNN.
unfold not in |- *; intros.
elim (In_list_remove2 _ _ _ _ _ H4).
reflexivity.
apply existSimp.
apply nnI.
apply Axm; right; constructor.
apply impE with (notH x).
apply cp2.
apply iffE2.
apply sysExtend with NN.
assumption.
apply H1.
assumption.
Qed.

Theorem Goedel'sIncompleteness1st :
 wConsistent T ->
 exists f : Formula,
   ~ SysPrf T f /\
   ~ SysPrf T (notH f) /\ (forall v : nat, ~ In v (freeVarFormula LNN f)).
Proof.
intros.
exists G.
pose freeVarG.
pose FirstIncompletenessA.
pose FirstIncompletenessB.
assert (~Inconsistent LNN T).
intro.
destruct (wCon2Con T H).
apply H1.
apply H0.
tauto.
Qed.

End Goedel's_1st_Incompleteness.
