Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import folProp.
Require Import folProof.
Require Import folReplace.
Require Import folLogic3.
Require Import subProp.
Require Import ListExt.
Require Import fixPoint.
Require Import codeSysPrf.
Require Import NNtheory.
Require Import code.
Require Import PRrepresentable.
Require Import expressible.
Require Import checkPrf.
Require Import codeNatToTerm.

Section Rosser's_Incompleteness.


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

Definition codeSysPrfCorrect1 :=
  codeSysPrfCorrect1 LNN codeLNTFunction codeLNNRelation codeArityLNTF
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
  
Definition codePrf := codePrf LNN codeLNTFunction codeLNNRelation.

Definition codeSysPrfNot :=
  codeSysPrfNot LNN codeLNTFunction codeLNNRelation codeArityLNTF
    codeArityLNNR codeArityLNTFIsPR codeArityLNNRIsPR repT v0.

Definition freeVarCodeSysPrfN :=
  freeVarCodeSysPrfN LNN codeLNTFunction codeLNNRelation codeArityLNTF
    codeArityLNNR codeArityLNTFIsPR codeArityLNNRIsPR repT v0 freeVarRepT.

Definition codeSysPrfNCorrect1 :=
  codeSysPrfNCorrect1 LNN codeLNTFunction codeLNNRelation codeArityLNTF
    codeArityLNNR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNNRIsPR
    codeArityLNNRIsCorrect1 T extendsNN T repT v0 freeVarRepT expressT1.

Definition codeSysPrfNCorrect2 :=
  codeSysPrfNCorrect2 LNN codeLNTFunction codeLNNRelation codeArityLNTF
    codeArityLNNR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNNRIsPR
    codeArityLNNRIsCorrect1 T extendsNN T repT v0 freeVarRepT expressT2.

Definition codeSysPrfNCorrect3 :=
  codeSysPrfNCorrect3 LNN codeLNTFunction codeLNNRelation codeArityLNTF
    codeArityLNNR codeArityLNTFIsPR codeArityLNTFIsCorrect1
    codeArityLNTFIsCorrect2 codeArityLNNRIsPR codeArityLNNRIsCorrect1
    codeArityLNNRIsCorrect2 codeLNTFunctionInj codeLNNRelationInj T extendsNN
    repT v0 freeVarRepT.

Lemma decideAxioms :
 (forall x : Formula, mem _ T x \/ ~ mem _ T x) ->
 forall x : Formulas,
 (forall g : Formula, In g x -> mem _ T g) \/
 (exists g : Formula, In g x /\ ~ mem _ T g).
Proof.
intros.
induction x as [| a x Hrecx].
left.
intros.
elim H0.
induction Hrecx as [H0| H0].
induction (H a).
left.
intros.
induction H2 as [H2| H2].
rewrite <- H2.
assumption.
auto.
right.
exists a.
split.
auto with datatypes.
assumption.
right.
induction H0 as (x0, H0).
exists x0.
induction H0 as (H0, H1).
auto with datatypes.
Qed.

Lemma searchProof :
 (forall x : Formula, mem _ T x \/ ~ mem _ T x) ->
 forall (a b : Formula) (A : Formulas) (p : Prf LNN A a),
 (exists B : Formulas,
    (exists q : Prf LNN B b,
       codePrf _ _ q < S (codePrf _ _ p) /\
       (forall x : Formula, In x B -> mem _ T x))) \/
 (forall (B : Formulas) (q : Prf LNN B b),
  codePrf _ _ q < S (codePrf _ _ p) ->
  exists g : Formula, In g B /\ ~ mem _ T g).
Proof.
intros.
induction (S (codePrf A a p)).
right.
intros.
elim (lt_n_O _ H0).
induction IHn as [H0| H0].
left.
decompose record H0.
exists x.
exists x0.
auto.
induction
 (eq_nat_dec
    (checkPrf LNN codeLNTFunction codeLNNRelation codeArityLNTF codeArityLNNR
       (codeFormula b) n) 0).
right.
intros.
induction (le_lt_or_eq _ _ (lt_n_Sm_le _ _ H1)).
eauto.
rewrite <- H2 in a0.
rewrite
 (checkPrfCorrect1 LNN codeLNTFunction codeLNNRelation codeArityLNTF
    codeArityLNNR codeArityLNTFIsCorrect1 codeArityLNNRIsCorrect1)
  in a0.
discriminate a0.
decompose record
 (checkPrfCorrect2 LNN codeLNTFunction codeLNNRelation codeArityLNTF
    codeArityLNNR codeArityLNTFIsCorrect1 codeArityLNTFIsCorrect2
    codeArityLNNRIsCorrect1 codeArityLNNRIsCorrect2 codeLNTFunctionInj
    codeLNNRelationInj _ _ b0).
assert (x = b).
eapply codeFormulaInj.
apply codeLNTFunctionInj.
apply codeLNNRelationInj.
assumption.
rewrite <- H1.
induction (decideAxioms H x0).
left.
exists x0.
exists x1.
unfold codePrf in |- *.
rewrite H3.
auto.
right.
intros.
induction (le_lt_or_eq _ _ (lt_n_Sm_le _ _ H5)).
rewrite <- H1 in H0.
eauto.
assert (B = x0).
eapply (codePrfInjAxm LNN) with (p := q) (q := x1).
apply codeLNTFunctionInj.
apply codeLNNRelationInj.
transitivity n.
unfold codePrf in H6.
apply H6.
symmetry  in |- *.
apply H3.
rewrite H7.
assumption.
Qed.

(*To prove the strong contructive result we need the decidability of T*)

Theorem Rosser'sIncompleteness :
 (forall x : Formula, mem _ T x \/ ~ mem _ T x) ->
 exists f : Formula,
   (forall v : nat, ~ In v (freeVarFormula LNN f)) /\
   (SysPrf T f \/ SysPrf T (notH f) -> Inconsistent LNN T).
Proof.
intros decide.
set
 (A :=
  forallH 1
    (impH codeSysPrf
       (existH 2
          (andH (LT (var 2) (var 1))
             (substituteFormula LNN codeSysPrfNot 1 (var 2)))))) 
 in *.
destruct (FixPointLNN A 0) as [x [H0 H1]].
exists x.
split.
unfold not in |- *; intros.
induction (H1 v).
assert (In v (list_remove nat eq_nat_dec 0 (freeVarFormula LNN A))).
apply H2.
assumption.
unfold A in H4.
SimplFreeVar.
assert (v <= 1).
apply
 (freeVarCodeSysPrf LNN codeLNTFunction codeLNNRelation codeArityLNTF
    codeArityLNNR codeArityLNTFIsPR codeArityLNNRIsPR repT v0 freeVarRepT).
apply H5.
destruct v as [| n].
apply H6.
reflexivity.
destruct n.
apply H7.
reflexivity.
apply (le_not_lt (S (S n)) 1).
assumption.
apply lt_n_S.
apply lt_O_Sn.
assert (v <= 1).
apply freeVarCodeSysPrfN.
assumption.
destruct v as [| n].
apply H6.
reflexivity.
destruct n.
apply H7.
reflexivity.
apply (le_not_lt (S (S n)) 1).
assumption.
apply lt_n_S.
apply lt_O_Sn.
intros.
induction H as [H| H].
unfold Inconsistent in |- *.
intros.
elim H.
intros.
induction H2 as (x1, H2).
induction (searchProof decide _ (notH x) _ x1).
decompose record H3.
apply contradiction with x.
assumption.
exists x2.
exists x3.
assumption.
apply
 contradiction
  with
    (existH 2
       (andH (LT (var 2) (natToTerm (codePrf _ _ x1)))
          (substituteFormula LNN
             (substituteFormula LNN codeSysPrfNot 0
                (natToTerm (codeFormula x))) 1 (var 2)))).
apply
 impE
  with
    (existH 2
       (andH (LT (var 2) (natToTerm (codePrf x0 x x1)))
          (substituteFormula LNN
             (substituteFormula LNN
                (substituteFormula LNN codeSysPrfNot 0
                   (natToTerm (codeFormula x))) 1 (var 2)) 1
             (natToTerm (codePrf _ _ x1))))).
apply iffE1.
apply sysExtend with NN.
apply extendsNN.
apply (reduceExist LNN).
apply closedNN.
apply (reduceAnd LNN).
apply iffRefl.
apply (subFormulaNil LNN).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H4).
apply (In_list_remove2 _ _ _ _ _ H5).
reflexivity.
simpl in H5.
decompose sum H5.
discriminate H6.
replace (LT (var 2) (natToTerm (codePrf _ _ x1))) with
 (substituteFormula LNN (LT (var 2) (var 1)) 1 (natToTerm (codePrf _ _ x1))).
rewrite <- (subFormulaAnd LNN).
apply
 impE
  with
    (existH 2
       (substituteFormula LNN
          (fol.andH LNN (LT (var 2) (var 1))
             (substituteFormula LNN
                (substituteFormula LNN codeSysPrfNot 1 (var 2)) 0
                (natToTerm (codeFormula x)))) 1 (natToTerm (codePrf x0 x x1)))).
apply iffE1.
apply sysExtend with NN.
apply extendsNN.
apply (reduceExist LNN).
apply closedNN.
apply (reduceSub LNN).
apply closedNN.
apply (reduceAnd LNN).
apply iffRefl.
apply (subFormulaExch LNN).
discriminate.
unfold not in |- *; intros.
simpl in H4.
decompose sum H4.
discriminate H5.
apply closedNatToTerm.
replace (LT (var 2) (var 1)) with
 (substituteFormula LNN (LT (var 2) (var 1)) 0 (natToTerm (codeFormula x))).
rewrite <- (subFormulaAnd LNN).
replace
 (existH 2
    (substituteFormula LNN
       (substituteFormula LNN
          (fol.andH LNN (LT (var 2) (var 1))
             (substituteFormula LNN codeSysPrfNot 1 (var 2))) 0
          (natToTerm (codeFormula x))) 1 (natToTerm (codePrf x0 x x1)))) with
 (substituteFormula LNN
    (existH 2
       (substituteFormula LNN
          (fol.andH LNN (LT (var 2) (var 1))
             (substituteFormula LNN codeSysPrfNot 1 (var 2))) 0
          (natToTerm (codeFormula x)))) 1 (natToTerm (codePrf x0 x x1))).
replace
 (existH 2
    (substituteFormula LNN
       (fol.andH LNN (LT (var 2) (var 1))
          (substituteFormula LNN codeSysPrfNot 1 (var 2))) 0
       (natToTerm (codeFormula x)))) with
 (substituteFormula LNN
    (existH 2
       (fol.andH LNN (LT (var 2) (var 1))
          (substituteFormula LNN codeSysPrfNot 1 (var 2)))) 0
    (natToTerm (codeFormula x))).
apply
 impE
  with
    (substituteFormula LNN
       (substituteFormula LNN codeSysPrf 0 (natToTerm (codeFormula x))) 1
       (natToTerm (codePrf _ _ x1))).
repeat rewrite <- (subFormulaImp LNN).
apply forallE.
replace
 (forallH 1
    (substituteFormula LNN
       (fol.impH LNN codeSysPrf
          (existH 2
             (fol.andH LNN (LT (var 2) (var 1))
                (substituteFormula LNN codeSysPrfNot 1 (var 2))))) 0
       (natToTerm (codeFormula x)))) with
 (substituteFormula LNN
    (forallH 1
       (fol.impH LNN codeSysPrf
          (existH 2
             (fol.andH LNN (LT (var 2) (var 1))
                (substituteFormula LNN codeSysPrfNot 1 (var 2)))))) 0
    (natToTerm (codeFormula x))).
apply impE with x.
apply iffE1.
apply sysExtend with NN.
apply extendsNN.
apply H0.
assumption.
rewrite (subFormulaForall LNN).
induction (eq_nat_dec 1 0).
discriminate a.
induction (In_dec eq_nat_dec 1 (freeVarTerm LNN (natToTerm (codeFormula x)))).
elim (closedNatToTerm _ _ a).
reflexivity.
apply codeSysPrfCorrect1.
assumption.
rewrite (subFormulaExist LNN).
induction (eq_nat_dec 2 0).
discriminate a.
induction (In_dec eq_nat_dec 2 (freeVarTerm LNN (natToTerm (codeFormula x)))).
elim (closedNatToTerm _ _ a).
reflexivity.
rewrite (subFormulaExist LNN).
induction (eq_nat_dec 2 1).
discriminate a.
induction
 (In_dec eq_nat_dec 2 (freeVarTerm LNN (natToTerm (codePrf x0 x x1)))).
elim (closedNatToTerm _ _ a).
reflexivity.
unfold LT in |- *.
rewrite (subFormulaRelation LNN).
simpl in |- *.
reflexivity.
unfold LT in |- *.
rewrite (subFormulaRelation LNN).
simpl in |- *.
reflexivity.
apply nExist.
set
 (E :=
  nat_rec (fun _ => Formula) (equal Zero Zero)
    (fun (n : nat) (rec : Formula) =>
     andH
       (notH
          (substituteFormula LNN
             (substituteFormula LNN codeSysPrfNot 0
                (natToTerm (codeFormula x))) 1 (natToTerm n))) rec)
    (codePrf x0 x x1)) in *.
assert (forall x : nat, ~ In x (freeVarFormula LNN E)).
unfold E in |- *.
clear H3 E.
induction (codePrf x0 x x1).
simpl in |- *.
auto.
intros.
unfold nat_rec, nat_rect in |- *.
unfold not in |- *; intros.
set
 (Q :=
  (fix F (n : nat) : (fun _ : nat => Formula) n :=
     match n with
     | O => equal Zero Zero
     | S n0 =>
         (fun (n1 : nat) (rec : Formula) =>
          andH
            (notH
               (substituteFormula LNN
                  (substituteFormula LNN codeSysPrfNot 0
                     (natToTerm (codeFormula x))) 1 
                  (natToTerm n1))) rec) n0 (F n0)
     end) n) in *.
SimplFreeVar.
apply (le_not_lt x2 1).
apply freeVarCodeSysPrfN.
assumption.
destruct x2 as [| n0].
elim H6; reflexivity.
destruct n0.
elim H5; reflexivity.
apply lt_n_S.
apply lt_O_Sn.
apply (IHn x2 H3).
apply impE with E.
apply sysExtend with NN.
apply extendsNN.
apply impI.
apply forallI.
unfold not in |- *; intros.
induction H5 as (x2, H5).
induction H5 as (H5, H6).
induction H6 as [x2 H6| x2 H6].
apply (closedNN 2).
exists x2.
auto.
induction H6.
apply (H4 2).
assumption.
apply nAnd.
unfold orH, fol.orH in |- *.
apply impTrans with (LT (var 2) (natToTerm (codePrf x0 x x1))).
apply impI.
apply nnE.
apply Axm; right; constructor.
apply impI.
apply impE with E.
apply impE with (LT (var 2) (natToTerm (codePrf x0 x x1))).
do 2 apply sysWeaken.
apply boundedLT.
intros.
rewrite (subFormulaImp LNN).
rewrite (subFormulaNot LNN).
apply
 impE
  with
    (fol.impH LNN E
       (fol.notH LNN
          (substituteFormula LNN
             (substituteFormula LNN codeSysPrfNot 0
                (natToTerm (codeFormula x))) 1 (natToTerm n)))).
apply iffE2.
apply (reduceImp LNN).
apply (subFormulaNil LNN).
apply H4.
apply (reduceNot LNN).
apply (subFormulaTrans LNN).
unfold not in |- *; intros.
SimplFreeVar.
apply (le_not_lt 2 1).
apply freeVarCodeSysPrfN.
assumption.
apply lt_n_Sn.
unfold E in |- *.
clear E H4 H3.
apply impI.
induction (codePrf x0 x x1).
elim (lt_n_O _ H5).
unfold nat_rec, nat_rect in |- *.
set
 (Q :=
  (fix F (n1 : nat) : (fun _ : nat => Formula) n1 :=
     match n1 with
     | O => equal Zero Zero
     | S n2 =>
         (fun (n3 : nat) (rec : Formula) =>
          andH
            (notH
               (substituteFormula LNN
                  (substituteFormula LNN codeSysPrfNot 0
                     (natToTerm (codeFormula x))) 1 
                  (natToTerm n3))) rec) n2 (F n2)
     end) n0) in *.
induction (le_lt_or_eq _ _ (lt_n_Sm_le _ _ H5)).
apply impE with Q.
apply sysWeaken.
apply impI.
apply (IHn0 H3).
eapply andE2.
apply Axm; right; constructor.
rewrite H3.
eapply andE1.
apply Axm; right; constructor.
apply Axm; right; constructor.
apply Axm; left; right; constructor.
unfold E in |- *.
clear H4 E.
induction (codePrf x0 x x1).
simpl in |- *.
apply eqRefl.
simpl in |- *.
apply andI.
induction
 (eq_nat_dec
    (checkPrf LNN codeLNTFunction codeLNNRelation codeArityLNTF codeArityLNNR
       (codeFormula (notH x)) n) 0).
unfold codeSysPrfNot in |- *.
apply codeSysPrfNCorrect3.
unfold not in |- *; intros.
rewrite H4 in a.
rewrite
 (checkPrfCorrect1 LNN codeLNTFunction codeLNNRelation codeArityLNTF
    codeArityLNNR codeArityLNTFIsCorrect1 codeArityLNNRIsCorrect1)
  in a.
discriminate a.
decompose record
 (checkPrfCorrect2 LNN codeLNTFunction codeLNNRelation codeArityLNTF
    codeArityLNNR codeArityLNTFIsCorrect1 codeArityLNTFIsCorrect2
    codeArityLNNRIsCorrect1 codeArityLNNRIsCorrect2 codeLNTFunctionInj
    codeLNNRelationInj _ _ b).
rewrite <- H6.
assert (x2 = notH x).
eapply codeFormulaInj.
apply codeLNTFunctionInj.
apply codeLNNRelationInj.
assumption.
cut (code.codePrf LNN codeLNTFunction codeLNNRelation x3 x2 x4 = n).
generalize x4.
clear H6 x4.
rewrite H4.
intros.
apply codeSysPrfNCorrect2.
eapply H3.
apply lt_S.
rewrite <- H6.
apply lt_n_Sn.
assumption.
apply IHn.
intros.
eapply H3.
apply lt_S.
apply H4.
unfold Inconsistent in |- *.
intros.
elim H.
intros.
induction H2 as (x1, H2).
induction (searchProof decide _ x _ x1).
decompose record H3.
apply contradiction with x.
exists x2.
exists x3.
assumption.
assumption.
apply
 contradiction
  with
    (substituteFormula LNN A 0
       (natToTermLNN (code.codeFormula LNN codeLNTFunction codeLNNRelation x))).
unfold A in |- *.
rewrite (subFormulaForall LNN).
induction (eq_nat_dec 1 0).
discriminate a.
induction
 (In_dec eq_nat_dec 1
    (freeVarTerm LNN
       (natToTermLNN (code.codeFormula LNN codeLNTFunction codeLNNRelation x)))).
elim (closedNatToTerm _ _ a).
clear b0 b.
set
 (E :=
  nat_rec (fun _ => Formula) (equal Zero Zero)
    (fun (n : nat) (rec : Formula) =>
     andH
       (notH
          (substituteFormula LNN
             (substituteFormula LNN codeSysPrf 0 (natToTerm (codeFormula x)))
             1 (natToTerm n))) rec) (S (codePrf _ _ x1))) 
 in *.
assert (forall x : nat, ~ In x (freeVarFormula LNN E)).
unfold E in |- *.
clear H3 E.
induction (S (codePrf x0 (notH x) x1)).
simpl in |- *.
auto.
intros.
unfold nat_rec, nat_rect in |- *.
unfold not in |- *; intros.
SimplFreeVar.
apply (le_not_lt x2 1).
apply
 (freeVarCodeSysPrf LNN codeLNTFunction codeLNNRelation codeArityLNTF
    codeArityLNNR codeArityLNTFIsPR codeArityLNNRIsPR repT v0 freeVarRepT).
apply H4.
destruct x2 as [| n0].
elim H6; reflexivity.
destruct n0.
elim H5; reflexivity.
apply lt_n_S.
apply lt_O_Sn.
apply (IHn _ H3).
apply impE with E.
set
 (G :=
  substituteFormula LNN
    (substituteFormula LNN codeSysPrfNot 0 (natToTerm (codeFormula x))) 1
    (natToTerm (codePrf x0 (notH x) x1))) in *.
apply impE with G.
apply sysExtend with NN.
assumption.
repeat apply impI.
apply forallI.
unfold not in |- *; intros.
induction H5 as (x2, H5); induction H5 as (H5, H6).
induction H6 as [x2 H6| x2 H6].
induction H6 as [x2 H6| x2 H6].
apply (closedNN 1).
exists x2.
auto.
induction H6.
unfold G in H5.
SimplFreeVar.
induction H6.
apply (H4 _ H5).
rewrite (subFormulaImp LNN).
rewrite (subFormulaExist LNN).
induction (eq_nat_dec 2 0).
discriminate a.
induction
 (In_dec eq_nat_dec 2
    (freeVarTerm LNN
       (natToTermLNN (code.codeFormula LNN codeLNTFunction codeLNNRelation x)))).
elim (closedNatToTerm _ _ a).
clear b0 b.
rewrite (subFormulaAnd LNN).
replace
 (substituteFormula LNN (LT (var 2) (var 1)) 0
    (natToTermLNN (code.codeFormula LNN codeLNTFunction codeLNNRelation x)))
 with (LT (var 2) (var 1)).
apply
 orE
  with
    (orH (LT (var 1) (natToTerm (codePrf x0 (notH x) x1)))
       (equal (var 1) (natToTerm (codePrf x0 (notH x) x1))))
    (LT (natToTerm (codePrf x0 (notH x) x1)) (var 1)).
repeat simple apply sysWeaken.
apply
 impE
  with
    (orH (LT (var 1) (natToTerm (codePrf x0 (notH x) x1)))
       (orH (equal (var 1) (natToTerm (codePrf x0 (notH x) x1)))
          (LT (natToTerm (codePrf x0 (notH x) x1)) (var 1)))).
apply impI.
apply orSys.
apply orI1.
apply orI1.
apply Axm; right; constructor.
apply orSys.
apply orI1.
apply orI2.
apply Axm; right; constructor.
apply orI2.
apply Axm; right; constructor.
apply nn9.
apply impI.
apply impE with G.
apply impE with E.
apply impE with (LT (var 1) (natToTerm (S (codePrf x0 (notH x) x1)))).
repeat simple apply sysWeaken.
apply boundedLT.
intros.
repeat apply impE.
repeat rewrite (subFormulaImp LNN).
repeat apply impI.
fold codeFormula in |- *.
apply
 contradiction
  with
    (substituteFormula LNN
       (substituteFormula LNN codeSysPrf 0 (natToTermLNN (codeFormula x))) 1
       (natToTerm n)).
apply Axm; right; constructor.
apply sysWeaken.
apply impE with E.
repeat simple apply sysWeaken.
apply impI.
clear H3.
clear H4.
induction (S (codePrf x0 (notH x) x1)).
elim (lt_n_O _ H5).
induction (le_lt_or_eq _ _ (lt_n_Sm_le _ _ H5)).
unfold E in |- *.
apply
 impE
  with
    (nat_rec (fun _ : nat => Formula) (equal Zero Zero)
       (fun (n : nat) (rec : Formula) =>
        andH
          (notH
             (substituteFormula LNN
                (substituteFormula LNN codeSysPrf 0
                   (natToTerm (codeFormula x))) 1 (natToTerm n))) rec) n0).
apply sysWeaken.
repeat apply impI.
apply IHn0.
assumption.
simpl in |- *.
eapply andE2.
apply Axm; right; constructor.
unfold E in |- *.
simpl in |- *.
rewrite H3.
eapply andE1.
apply Axm; right; constructor.
apply impE with (substituteFormula LNN E 1 (natToTerm n)).
apply iffE1.
apply (subFormulaNil LNN).
apply H4.
apply Axm; left; right; constructor.
apply
 impE
  with
    (orH (LT (var 1) (natToTerm (codePrf x0 (notH x) x1)))
       (equal (var 1) (natToTerm (codePrf x0 (notH x) x1)))).
repeat simple apply sysWeaken.
simpl in |- *.
apply nnPlusNotNeeded.
apply Axm; right; constructor.
apply Axm; left; right; constructor.
apply Axm; do 2 left; right; constructor.
repeat apply impI.
apply sysWeaken.
apply existI with (natToTerm (codePrf x0 (notH x) x1)).
rewrite (subFormulaAnd LNN).
apply andI.
unfold LT in |- *.
rewrite (subFormulaRelation LNN).
simpl in |- *.
apply Axm; right; constructor.
apply sysWeaken.
apply sysWeaken.
apply
 impE
  with
    (substituteFormula LNN
       (substituteFormula LNN codeSysPrfNot 0 (natToTerm (codeFormula x))) 1
       (natToTerm (codePrf x0 (notH x) x1))).
apply sysWeaken.
apply iffE2.
fold codeFormula in |- *.
apply
 iffTrans
  with
    (substituteFormula LNN
       (substituteFormula LNN
          (substituteFormula LNN codeSysPrfNot 0
             (natToTermLNN (codeFormula x))) 1 (var 2)) 2
       (natToTerm (codePrf x0 (notH x) x1))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
discriminate.
unfold not in |- *; intros; SimplFreeVar.
discriminate H6.
apply closedNatToTerm.
apply (subFormulaTrans LNN).
unfold not in |- *; intros; SimplFreeVar.
apply (le_not_lt 2 1).
apply freeVarCodeSysPrfN.
assumption.
apply lt_n_Sn.
apply Axm; right; constructor.
unfold LT in |- *.
rewrite (subFormulaRelation LNN).
reflexivity.
unfold G in |- *.
apply codeSysPrfNCorrect1.
assumption.
clear H4.
unfold E in |- *; clear E.
induction (S (codePrf x0 (notH x) x1)).
simpl in |- *.
apply eqRefl.
simpl in |- *.
apply andI.
induction
 (eq_nat_dec
    (checkPrf LNN codeLNTFunction codeLNNRelation codeArityLNTF codeArityLNNR
       (codeFormula x) n) 0).
unfold codeSysPrf, codeFormula in |- *.
apply codeSysPrfCorrect3.
unfold not in |- *; intros.
rewrite H4 in a.
rewrite
 (checkPrfCorrect1 LNN codeLNTFunction codeLNNRelation codeArityLNTF
    codeArityLNNR codeArityLNTFIsCorrect1 codeArityLNNRIsCorrect1)
  in a.
discriminate a.
decompose record
 (checkPrfCorrect2 LNN codeLNTFunction codeLNNRelation codeArityLNTF
    codeArityLNNR codeArityLNTFIsCorrect1 codeArityLNTFIsCorrect2
    codeArityLNNRIsCorrect1 codeArityLNNRIsCorrect2 codeLNTFunctionInj
    codeLNNRelationInj _ _ b).
rewrite <- H6.
assert (x2 = x).
eapply (codeFormulaInj LNN).
apply codeLNTFunctionInj.
apply codeLNNRelationInj.
assumption.
rewrite <- H4.
apply codeSysPrfCorrect2.
rewrite <- H4 in H3.
apply H3 with x4.
rewrite <- H6.
apply lt_n_Sn.
apply IHn.
intros.
eapply H3.
apply lt_S.
apply H4.
apply impE with (notH x).
apply cp2.
apply iffE2.
apply sysExtend with NN.
apply extendsNN.
assumption.
assumption.
Qed.

End Rosser's_Incompleteness.

Definition RepresentsInSelf (T:System) := 
exists rep:Formula, exists v:nat,
(forall x : nat, In x (freeVarFormula LNN rep) -> x = v)  /\
(forall f : Formula,
        mem Formula T f ->
        SysPrf T (substituteFormula LNN rep v (natToTerm (codeFormula f)))) /\
(forall f : Formula,
        ~ mem Formula T f ->
        SysPrf T
          (notH (substituteFormula LNN rep v (natToTerm (codeFormula f))))).

Definition DecidableSet (A:_)(s:Ensemble A) :=
(forall x : A,
        mem A s x \/
        ~ mem A s x).

Theorem Incompleteness :
       forall T : System,
       Included Formula NN T ->
       RepresentsInSelf T ->
       DecidableSet Formula T ->
       exists f : Formula,
         (Sentence f) /\
         (SysPrf T f \/ SysPrf T (notH f) -> Inconsistent LNN T).
Proof.
intros.
repeat induction H0.
apply Rosser'sIncompleteness with x x0; auto; tauto.
Qed.
