Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import primRec.
Require Import cPair.
Require Import Arith.
Require Import folProp.
Require Import code.
Require Import codeList.
Require Import codeFreeVar.
Require Import extEqualNat.
Require Vector.
Require Import prLogic.

Section close.

Variable L : Language.
Variable codeF : Functions L -> nat.
Variable codeR : Relations L -> nat.

Let Formula := Formula L.
Let codeFormula := codeFormula L codeF codeR.

Definition codeCloseList : nat -> nat -> nat :=
  evalStrongRec 1
    (fun l recs f : nat =>
     switchPR l
       (cPair 3
          (cPair (cPairPi1 (pred l))
             (codeNth (l - S (cPairPi2 (pred l))) recs))) f).
    
Lemma codeCloseListCorrect :
 forall (l : list nat) (f : Formula),
 codeCloseList (codeList l) (codeFormula f) = codeFormula (closeList L l f).
Proof.
intros.
set
 (g :=
  fun l recs f : nat =>
  switchPR l
    (cPair 3
       (cPair (cPairPi1 (pred l)) (codeNth (l - S (cPairPi2 (pred l))) recs)))
    f) in *.
induction l as [| a l Hrecl].
simpl in |- *.
unfold codeCloseList in |- *.
unfold evalStrongRec in |- *.
simpl in |- *.
rewrite cPairProjections1.
reflexivity.
simpl in |- *.
unfold codeCloseList in |- *.
fold g in |- *.
assert
 (forall n m : nat,
  m < n ->
  extEqual 1
    (evalComposeFunc 1 1 (Vector.cons _ (evalStrongRecHelp 1 g n) 0 (Vector.nil _))
       (fun b : nat => codeNth (n - S m) b)) (evalStrongRec 1 g m)).
intros.
apply (evalStrongRecHelp2 1). 
assumption.
simpl in H.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
unfold g at 1 in |- *.
rewrite H.
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
rewrite <- Hrecl.
reflexivity.
simpl in |- *.
apply le_lt_n_Sm.
apply cPairLe2A.
Qed.

Lemma codeCloseListIsPR : isPR 2 codeCloseList.
Proof.
intros.
unfold codeCloseList in |- *.
apply evalStrongRecIsPR.
apply
 compose3_3IsPR
  with
    (f1 := fun l recs f : nat => l)
    (f2 := fun l recs f : nat =>
           cPair 3
             (cPair (cPairPi1 (pred l))
                (codeNth (l - S (cPairPi2 (pred l))) recs)))
    (f3 := fun l recs f : nat => f).
apply pi1_3IsPR.
apply
 filter110IsPR
  with
    (g := fun l recs : nat =>
          cPair 3
            (cPair (cPairPi1 (pred l))
               (codeNth (l - S (cPairPi2 (pred l))) recs))).
apply
 compose2_2IsPR
  with
    (f := fun l recs : nat => 3)
    (g := fun l recs : nat =>
          cPair (cPairPi1 (pred l))
            (codeNth (l - S (cPairPi2 (pred l))) recs)).
apply filter10IsPR with (g := fun _ : nat => 3).
apply const1_NIsPR.
apply
 compose2_2IsPR
  with
    (f := fun l recs : nat => cPairPi1 (pred l))
    (g := fun l recs : nat => codeNth (l - S (cPairPi2 (pred l))) recs).
apply filter10IsPR with (g := fun l : nat => cPairPi1 (pred l)).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi1IsPR.
apply callIsPR with (g := fun l : nat => cPairPi2 (pred l)).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi2IsPR.
apply cPairIsPR.
apply cPairIsPR.
apply pi3_3IsPR.
apply switchIsPR.
Qed.

Definition codeClose (f : nat) : nat :=
  codeCloseList (codeNoDup (codeFreeVarFormula f)) f.

Lemma codeCloseCorrect :
 forall f : Formula, codeClose (codeFormula f) = codeFormula (close L f).
Proof.
intros.
unfold close in |- *.
unfold codeClose in |- *.
unfold codeFormula in |- *.
rewrite codeFreeVarFormulaCorrect.
rewrite codeNoDupCorrect.
apply codeCloseListCorrect.
Qed.

Lemma codeCloseIsPR : isPR 1 codeClose.
Proof.
unfold codeClose in |- *.
apply
 compose1_2IsPR
  with
    (f := fun f : nat => codeNoDup (codeFreeVarFormula f))
    (f' := fun f : nat => f).
apply compose1_1IsPR.
apply codeFreeVarFormulaIsPR.
apply codeNoDupIsPR.
apply idIsPR.
apply codeCloseListIsPR.
Qed.

End close.

Require Import PA.
Require Import codeSubFormula.

Section Code_PA.

Let codeTerm := codeTerm LNT codeLNTFunction.
Let codeFormula := codeFormula LNT codeLNTFunction codeLNTRelation.
Let codeFormulaInj :=
  codeFormulaInj LNT codeLNTFunction codeLNTRelation codeLNTFunctionInj
    codeLNTRelationInj.

Definition codeOpen : nat -> nat :=
  evalStrongRec 0
    (fun f recs : nat =>
     switchPR (cPairPi1 f)
       (switchPR (pred (cPairPi1 f))
          (switchPR (pred (pred (cPairPi1 f)))
             (switchPR (pred (pred (pred (cPairPi1 f)))) f
                (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs)) f) f) f).

Lemma codeOpenCorrect :
 forall f : Formula, codeOpen (codeFormula f) = codeFormula (open f).
Proof.
intros.
unfold codeOpen, open in |- *.
set
 (g :=
  fun f recs : nat =>
  switchPR (cPairPi1 f)
    (switchPR (pred (cPairPi1 f))
       (switchPR (pred (pred (cPairPi1 f)))
          (switchPR (pred (pred (pred (cPairPi1 f)))) f
             (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs)) f) f) f) 
 in *.
induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf];
 simpl in |- *; unfold evalStrongRec in |- *.
simpl in |- *; unfold g at 1 in |- *;
 repeat rewrite cPairProjections1 || rewrite cPairProjections2; 
 reflexivity.
simpl in |- *; unfold g at 1 in |- *;
 repeat rewrite cPairProjections1 || rewrite cPairProjections2; 
 reflexivity.
simpl in |- *; unfold g at 1 in |- *;
 repeat rewrite cPairProjections1 || rewrite cPairProjections2; 
 reflexivity.
simpl in |- *; unfold g at 1 in |- *;
 repeat rewrite cPairProjections1 || rewrite cPairProjections2; 
 reflexivity.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
unfold g at 1 in |- *.
repeat rewrite evalStrongRecHelp1.
unfold pred in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
simpl in |- *.
apply Hrecf.
eapply le_lt_trans.
apply cPairLe2A.
rewrite cPairProjections2.
apply cPairLt2.
Qed.

Lemma codeOpenIsPR : isPR 1 codeOpen.
Proof.
unfold codeOpen in |- *.
apply evalStrongRecIsPR.
apply
 compose2_3IsPR
  with
    (f1 := fun f recs : nat => cPairPi1 f)
    (f2 := fun f recs : nat =>
           switchPR (pred (cPairPi1 f))
             (switchPR (pred (pred (cPairPi1 f)))
                (switchPR (pred (pred (pred (cPairPi1 f)))) f
                   (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs)) f) f)
    (f3 := fun f recs : nat => f).
apply filter10IsPR.
apply cPairPi1IsPR.
apply
 compose2_3IsPR
  with
    (f1 := fun f recs : nat => pred (cPairPi1 f))
    (f2 := fun f recs : nat =>
           switchPR (pred (pred (cPairPi1 f)))
             (switchPR (pred (pred (pred (cPairPi1 f)))) f
                (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs)) f)
    (f3 := fun f recs : nat => f).
apply filter10IsPR with (g := fun f : nat => pred (cPairPi1 f)).
apply compose1_1IsPR.
apply cPairPi1IsPR.
apply predIsPR.
apply
 compose2_3IsPR
  with
    (f1 := fun f recs : nat => pred (pred (cPairPi1 f)))
    (f2 := fun f recs : nat =>
           switchPR (pred (pred (pred (cPairPi1 f)))) f
             (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))
    (f3 := fun f recs : nat => f).
apply filter10IsPR with (g := fun f : nat => pred (pred (cPairPi1 f))).
apply compose1_1IsPR with (f := fun f : nat => pred (cPairPi1 f)).
apply compose1_1IsPR.
apply cPairPi1IsPR.
apply predIsPR.
apply predIsPR.
apply
 compose2_3IsPR
  with
    (f1 := fun f recs : nat => pred (pred (pred (cPairPi1 f))))
    (f2 := fun f recs : nat => f)
    (f3 := fun f recs : nat => codeNth (f - S (cPairPi2 (cPairPi2 f))) recs).
apply filter10IsPR with (g := fun f : nat => pred (pred (pred (cPairPi1 f)))).
apply compose1_1IsPR with (f := fun f : nat => pred (pred (cPairPi1 f))).
apply compose1_1IsPR with (f := fun f : nat => pred (cPairPi1 f)).
apply compose1_1IsPR.
apply cPairPi1IsPR.
apply predIsPR.
apply predIsPR.
apply predIsPR.
apply pi1_2IsPR.
apply callIsPR with (g := fun f : nat => cPairPi2 (cPairPi2 f)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply switchIsPR.
apply pi1_2IsPR.
apply switchIsPR.
apply pi1_2IsPR.
apply switchIsPR.
apply pi1_2IsPR.
apply switchIsPR.
Qed.

Definition codeInductionSchema (f : nat) : bool :=
  let n :=
    cPairPi1
      (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 (codeOpen f)))))) in
  let g :=
    cPairPi2
      (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 (codeOpen f)))))) in
  beq_nat
    (codeClose
       (codeImp (codeSubFormula g n (codeTerm Zero))
          (codeImp
             (codeForall n
                (codeImp g (codeSubFormula g n (codeTerm (Succ (var n))))))
             (codeForall n g)))) f.

Lemma codeInductionSchemaCorrect1 :
 forall f : Formula,
 InductionSchema f -> codeInductionSchema (codeFormula f) = true.
Proof.
intros.
induction H as (x, H).
induction H as (x0, H).
unfold PA7 in H.
rewrite H.
clear H f.
lazy beta delta [codeInductionSchema] in |- *.
rewrite codeOpenCorrect.
replace
 (open
    (close LNT
       (impH (substituteFormula LNT x x0 Zero)
          (impH
             (forallH x0
                (impH x (substituteFormula LNT x x0 (Succ (var x0)))))
             (forallH x0 x))))) with
 (impH (substituteFormula LNT x x0 Zero)
    (impH (forallH x0 (impH x (substituteFormula LNT x x0 (Succ (var x0)))))
       (forallH x0 x))).
replace
 (cPairPi1
    (cPairPi2
       (cPairPi2
          (cPairPi2
             (cPairPi2
                (cPairPi2
                   (codeFormula
                      (impH (substituteFormula LNT x x0 Zero)
                         (impH
                            (forallH x0
                               (impH x
                                  (substituteFormula LNT x x0 (Succ (var x0)))))
                            (forallH x0 x)))))))))) with x0.
replace
 (cPairPi2
    (cPairPi2
       (cPairPi2
          (cPairPi2
             (cPairPi2
                (cPairPi2
                   (codeFormula
                      (impH (substituteFormula LNT x x0 Zero)
                         (impH
                            (forallH x0
                               (impH x
                                  (substituteFormula LNT x x0 (Succ (var x0)))))
                            (forallH x0 x)))))))))) with 
 (codeFormula x).
cbv zeta in |- *.
unfold codeFormula in |- *.
rewrite <- codeCloseCorrect.
replace
 (codeClose
    (codeImp
       (codeSubFormula
          (code.codeFormula LNT codeLNTFunction codeLNTRelation x) x0
          (codeTerm Zero))
       (codeImp
          (codeForall x0
             (codeImp
                (code.codeFormula LNT codeLNTFunction codeLNTRelation x)
                (codeSubFormula
                   (code.codeFormula LNT codeLNTFunction codeLNTRelation x)
                   x0 (codeTerm (Succ (var x0))))))
          (codeForall x0
             (code.codeFormula LNT codeLNTFunction codeLNTRelation x)))))
 with
 (codeClose
    (code.codeFormula LNT codeLNTFunction codeLNTRelation
       (impH (substituteFormula LNT x x0 Zero)
          (impH
             (forallH x0
                (impH x (substituteFormula LNT x x0 (Succ (var x0)))))
             (forallH x0 x))))).
rewrite <- beq_nat_refl.
reflexivity.
simpl in |- *.
unfold codeTerm in |- *.
repeat rewrite codeSubFormulaCorrect.
reflexivity.
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
reflexivity.
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
reflexivity.
unfold close in |- *.
induction
 (ListExt.no_dup nat eq_nat_dec
    (freeVarFormula LNT
       (impH (substituteFormula LNT x x0 Zero)
          (impH
             (forallH x0
                (impH x (substituteFormula LNT x x0 (Succ (var x0)))))
             (forallH x0 x))))).
reflexivity.
simpl in |- *.
assumption.
Qed.

Lemma codeInductionSchemaCorrect2 :
 forall f : Formula,
 codeInductionSchema (codeFormula f) = true -> InductionSchema f.
Proof.
intros.
lazy beta delta [codeInductionSchema] in H.
rewrite codeOpenCorrect in H.
set
 (n :=
  cPairPi1
    (cPairPi2
       (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 (codeFormula (open f))))))))
 in *.
set
 (g :=
  cPairPi2
    (cPairPi2
       (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 (codeFormula (open f))))))))
 in *.
cbv zeta in H.
induction
 (eq_nat_dec
    (codeImp (codeSubFormula g n (codeTerm Zero))
       (codeImp
          (codeForall n
             (codeImp g (codeSubFormula g n (codeTerm (Succ (var n))))))
          (codeForall n g))) (codeFormula (open f))).
rewrite a in H.
unfold codeFormula in H.
rewrite codeCloseCorrect in H.
fold codeFormula in H.
induction (formula_dec LNT LNT_dec (close LNT (open f)) f).
unfold codeImp at 1 in a.
destruct (open f) as [t t0| r t| f0 f1| f0| n0 f0]; simpl in a;
 try
  match goal with
  | h:(cPair ?X1 ?X2 = cPair ?X3 ?X4) |- _ =>
      elimtype False; cut (X1 = X3);
       [ discriminate | eapply cPairInj1; apply h ]
  end.
assert (codeSubFormula g n (codeTerm Zero) = codeFormula f0).
eapply cPairInj1.
eapply cPairInj2.
apply a.
assert
 (codeImp
    (codeForall n (codeImp g (codeSubFormula g n (codeTerm (Succ (var n))))))
    (codeForall n g) = codeFormula f1).
eapply cPairInj2.
eapply cPairInj2.
apply a.
clear a.
Opaque cPairPi1.
Opaque cPairPi2.
unfold codeImp at 1 in H1.
destruct f1 as [t t0| r t| f1 f2| f1| n0 f1]; simpl in H1;
 try
  match goal with
  | h:(cPair ?X1 ?X2 = cPair ?X3 ?X4) |- _ =>
      elimtype False; cut (X1 = X3);
       [ discriminate | eapply cPairInj1; apply h ]
  end.
assert
 (codeForall n (codeImp g (codeSubFormula g n (codeTerm (Succ (var n))))) =
  codeFormula f1).
eapply cPairInj1.
eapply cPairInj2.
apply H1.
assert (codeForall n g = codeFormula f2).
eapply cPairInj2.
eapply cPairInj2.
apply H1.
clear H1.
unfold codeForall at 1 in H3.
destruct f2 as [t t0| r t| f2 f3| f2| n0 f2]; simpl in H3;
 try
  match goal with
  | h:(cPair ?X1 ?X2 = cPair ?X3 ?X4) |- _ =>
      elimtype False; cut (X1 = X3);
       [ discriminate | eapply cPairInj1; apply h ]
  end.
simpl in (value of n).
simpl in (value of g).
unfold InductionSchema in |- *.
exists f2.
exists n0.
unfold PA7 in |- *.
replace (substituteFormula LNT f2 n0 Zero) with f0.
replace (forallH n0 (impH f2 (substituteFormula LNT f2 n0 (Succ (var n0)))))
 with f1.
symmetry  in |- *.
apply a0.
apply codeFormulaInj.
simpl in |- *.
rewrite <- codeSubFormulaCorrect.
symmetry  in |- *.
unfold n, g in H2.
repeat rewrite cPairProjections1 in H2 || rewrite cPairProjections2 in H2.
apply H2.
apply codeFormulaInj.
rewrite <- codeSubFormulaCorrect.
symmetry  in |- *.
unfold n, g in H0.
repeat rewrite cPairProjections1 in H0 || rewrite cPairProjections2 in H0.
apply H0.
rewrite beq_nat_not_refl in H.
discriminate H.
unfold not in |- *; intros; apply b.
apply codeFormulaInj.
apply H0.
rewrite beq_nat_not_refl in H.
discriminate H.
unfold not in |- *; intros; apply b.
rewrite <- codeOpenCorrect.
rewrite <- H0.
unfold codeImp in |- *.
generalize
 (cPair (codeSubFormula g n (codeTerm Zero))
    (cPair 1
       (cPair
          (codeForall n
             (cPair 1
                (cPair g (codeSubFormula g n (codeTerm (Succ (var n)))))))
          (codeForall n g)))).
intros.
unfold codeClose in |- *.
assert
 (forall m : nat,
  m <= codeNoDup (codeFreeVarFormula (cPair 1 n0)) ->
  cPair 1 n0 = codeOpen (codeCloseList m (cPair 1 n0))).
induction (codeNoDup (codeFreeVarFormula (cPair 1 n0))).
intros.
rewrite <- (le_n_O_eq _ H1).
unfold codeCloseList in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
rewrite cPairProjections1.
unfold codeOpen in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
repeat rewrite cPairProjections1.
simpl in |- *.
repeat rewrite cPairProjections1.
reflexivity.
intros.
induction (le_lt_or_eq _ _ H1).
apply IHn1.
apply lt_n_Sm_le.
assumption.
rewrite H2.
unfold codeCloseList in |- *.
set
 (g0 :=
  fun l recs f0 : nat =>
  switchPR l
    (cPair 3
       (cPair (cPairPi1 (pred l)) (codeNth (l - S (cPairPi2 (pred l))) recs)))
    f0) in *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
assert
 (forall n m : nat,
  m < n ->
  extEqual 1
    (evalComposeFunc 1 1 (Vector.cons _ (evalStrongRecHelp 1 g0 n) 0 (Vector.nil _))
       (fun b : nat => codeNth (n - S m) b)) (evalStrongRec 1 g0 m)).
intros.
apply (evalStrongRecHelp2 1). 
assumption.
simpl in H3.
unfold g0 at 1 in |- *.
rewrite H3.
simpl in |- *.
repeat rewrite cPairProjections1.
unfold codeCloseList in IHn1.
move g0 after IHn1; fold g0 in IHn1.
set (A := evalStrongRec 1 g0 (cPairPi2 n1) (cPair 1 n0)) in *.
unfold codeOpen in |- *.
set
 (g1 :=
  fun f0 recs : nat =>
  switchPR (cPairPi1 f0)
    (switchPR (pred (cPairPi1 f0))
       (switchPR (pred (pred (cPairPi1 f0)))
          (switchPR (pred (pred (pred (cPairPi1 f0)))) f0
             (codeNth (f0 - S (cPairPi2 (cPairPi2 f0))) recs)) f0) f0) f0)
 in *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
unfold g1 at 1 in |- *.
unfold pred at 1 in |- *.
repeat rewrite cPairProjections1.
repeat rewrite evalStrongRecHelp1.
simpl in |- *.
repeat rewrite cPairProjections2.
unfold A in |- *.
unfold codeOpen in IHn1.
move g1 after IHn1; fold g1 in IHn1.
apply IHn1.
apply cPairLe2A.
repeat rewrite cPairProjections2.
eapply le_lt_trans; [ idtac | apply cPairLt2 ].
apply cPairLe2.
simpl in |- *.
apply le_lt_n_Sm.
apply cPairLe2A.
apply H1.
apply le_n.
Qed.

Lemma codeInductionSchemaCorrect3 :
 forall f : Formula,
 ~ InductionSchema f -> codeInductionSchema (codeFormula f) = false.
Proof.
intros.
assert (forall x : bool, x = true \/ x = false).
intros.
induction x; auto.
induction (H0 (codeInductionSchema (codeFormula f))).
elim H.
apply codeInductionSchemaCorrect2.
assumption.
assumption.
Qed.

Lemma codeInductionSchemaIsPR : isPRrel 1 codeInductionSchema.
Proof.
lazy beta delta [codeInductionSchema] in |- *.
set
 (A :=
  fun f : nat =>
  cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 (codeOpen f)))))) 
 in *.
assert (isPR 1 A).
unfold A in |- *.
apply compose1_1IsPR with (g := iterate cPairPi2 5) (f := codeOpen).
apply codeOpenIsPR.
apply iterateIsPR.
apply cPairPi2IsPR.
assert
 (isPRrel 1
    (fun f : nat =>
     let n := cPairPi1 (A f) in
     let g := cPairPi2 (A f) in
     beq_nat
       (codeClose
          (codeImp (codeSubFormula g n (codeTerm Zero))
             (codeImp
                (codeForall n
                   (codeImp g (codeSubFormula g n (codeTerm (Succ (var n))))))
                (codeForall n g)))) f)).
unfold isPRrel in |- *.
apply
 compose1_2IsPR
  with
    (g := charFunction 2 beq_nat)
    (f' := fun f : nat => f)
    (f := fun f : nat =>
          codeClose
            (codeImp
               (codeSubFormula (cPairPi2 (A f)) (cPairPi1 (A f))
                  (codeTerm Zero))
               (codeImp
                  (codeForall (cPairPi1 (A f))
                     (codeImp (cPairPi2 (A f))
                        (codeSubFormula (cPairPi2 (A f)) 
                           (cPairPi1 (A f))
                           (codeTerm (Succ (var (cPairPi1 (A f))))))))
                  (codeForall (cPairPi1 (A f)) (cPairPi2 (A f)))))).
apply
 compose1_1IsPR
  with
    (f := fun f : nat =>
          codeImp
            (codeSubFormula (cPairPi2 (A f)) (cPairPi1 (A f)) (codeTerm Zero))
            (codeImp
               (codeForall (cPairPi1 (A f))
                  (codeImp (cPairPi2 (A f))
                     (codeSubFormula (cPairPi2 (A f)) 
                        (cPairPi1 (A f))
                        (codeTerm (Succ (var (cPairPi1 (A f))))))))
               (codeForall (cPairPi1 (A f)) (cPairPi2 (A f))))).
apply
 compose1_2IsPR
  with
    (f := fun f : nat =>
          codeSubFormula (cPairPi2 (A f)) (cPairPi1 (A f)) (codeTerm Zero))
    (f' := fun f : nat =>
           codeImp
             (codeForall (cPairPi1 (A f))
                (codeImp (cPairPi2 (A f))
                   (codeSubFormula (cPairPi2 (A f)) 
                      (cPairPi1 (A f))
                      (codeTerm (Succ (var (cPairPi1 (A f))))))))
             (codeForall (cPairPi1 (A f)) (cPairPi2 (A f)))).
apply
 compose1_3IsPR
  with
    (f1 := fun f : nat => cPairPi2 (A f))
    (f2 := fun f : nat => cPairPi1 (A f))
    (f3 := fun f : nat => codeTerm Zero).
apply compose1_1IsPR.
assumption.
apply cPairPi2IsPR.
apply compose1_1IsPR.
assumption.
apply cPairPi1IsPR.
apply const1_NIsPR.
apply codeSubFormulaIsPR.
apply
 compose1_2IsPR
  with
    (f := fun f : nat =>
          codeForall (cPairPi1 (A f))
            (codeImp (cPairPi2 (A f))
               (codeSubFormula (cPairPi2 (A f)) (cPairPi1 (A f))
                  (codeTerm (Succ (var (cPairPi1 (A f))))))))
    (f' := fun f : nat => codeForall (cPairPi1 (A f)) (cPairPi2 (A f))).
apply
 compose1_2IsPR
  with
    (f := fun f : nat => cPairPi1 (A f))
    (f' := fun f : nat =>
           codeImp (cPairPi2 (A f))
             (codeSubFormula (cPairPi2 (A f)) (cPairPi1 (A f))
                (codeTerm (Succ (var (cPairPi1 (A f))))))).
apply compose1_1IsPR.
assumption.
apply cPairPi1IsPR.
apply
 compose1_2IsPR
  with
    (f := fun f : nat => cPairPi2 (A f))
    (f' := fun f : nat =>
           codeSubFormula (cPairPi2 (A f)) (cPairPi1 (A f))
             (codeTerm (Succ (var (cPairPi1 (A f)))))).
apply compose1_1IsPR.
assumption.
apply cPairPi2IsPR.
apply
 compose1_3IsPR
  with
    (f1 := fun f : nat => cPairPi2 (A f))
    (f2 := fun f : nat => cPairPi1 (A f))
    (f3 := fun f : nat => codeTerm (Succ (var (cPairPi1 (A f))))).
apply compose1_1IsPR.
assumption.
apply cPairPi2IsPR.
apply compose1_1IsPR.
assumption.
apply cPairPi1IsPR.
assert
 (isPR 1 (fun f : nat => cPair 3 (S (cPair (cPair 0 (cPairPi1 (A f))) 0)))).
apply
 compose1_2IsPR
  with
    (f := fun f : nat => 3)
    (f' := fun f : nat => S (cPair (cPair 0 (cPairPi1 (A f))) 0)).
apply const1_NIsPR.
apply
 compose1_1IsPR with (f := fun f : nat => cPair (cPair 0 (cPairPi1 (A f))) 0).
apply
 compose1_2IsPR
  with
    (f := fun f : nat => cPair 0 (cPairPi1 (A f)))
    (f' := fun f : nat => 0).
apply
 compose1_2IsPR
  with (f := fun f : nat => 0) (f' := fun f : nat => cPairPi1 (A f)).
apply const1_NIsPR.
apply compose1_1IsPR.
assumption.
apply cPairPi1IsPR.
apply cPairIsPR.
apply const1_NIsPR.
apply cPairIsPR.
apply succIsPR.
apply cPairIsPR.
induction H0 as (x, p).
exists x.
eapply extEqualTrans.
apply p.
simpl in |- *.
intros.
reflexivity.
apply codeSubFormulaIsPR.
apply codeImpIsPR.
apply codeForallIsPR.
apply
 compose1_2IsPR
  with
    (f := fun f : nat => cPairPi1 (A f))
    (f' := fun f : nat => cPairPi2 (A f)).
apply compose1_1IsPR.
assumption.
apply cPairPi1IsPR.
apply compose1_1IsPR.
assumption.
apply cPairPi2IsPR.
apply codeForallIsPR.
apply codeImpIsPR.
apply codeImpIsPR.
apply codeCloseIsPR.
apply idIsPR.
apply eqIsPR.
apply H0.
Qed.

Definition codePA : nat -> bool :=
  orRel 1 (beq_nat (codeFormula PA6))
    (orRel 1 (beq_nat (codeFormula PA5))
       (orRel 1 (beq_nat (codeFormula PA4))
          (orRel 1 (beq_nat (codeFormula PA3))
             (orRel 1 (beq_nat (codeFormula PA2))
                (orRel 1 (beq_nat (codeFormula PA1)) codeInductionSchema))))).

Lemma codePAcorrect1 :
 forall f : Formula,
 codePA (codeFormula f) = true -> mem Formula PA f.
Proof.
intros.
induction (PAdec f).
assumption.
unfold codePA in H.
unfold orRel, nat_rec, nat_rect in H.
unfold PA in |- *.
induction (eq_nat_dec (codeFormula PA6) (codeFormula f)).
rewrite a in H.
rewrite <- beq_nat_refl in H.
replace f with PA6.
right; constructor.
eapply codeFormulaInj.
apply a.
left.
rewrite beq_nat_not_refl in H.
clear b.
induction (eq_nat_dec (codeFormula PA5) (codeFormula f)).
rewrite a in H.
rewrite <- beq_nat_refl in H.
replace f with PA5.
right; constructor.
eapply codeFormulaInj.
apply a.
left.
rewrite beq_nat_not_refl in H.
clear b.
induction (eq_nat_dec (codeFormula PA4) (codeFormula f)).
rewrite a in H.
rewrite <- beq_nat_refl in H.
replace f with PA4.
right; constructor.
eapply codeFormulaInj.
apply a.
left.
rewrite beq_nat_not_refl in H.
clear b.
induction (eq_nat_dec (codeFormula PA3) (codeFormula f)).
rewrite a in H.
rewrite <- beq_nat_refl in H.
replace f with PA3.
right; constructor.
eapply codeFormulaInj.
apply a.
left.
rewrite beq_nat_not_refl in H.
clear b.
induction (eq_nat_dec (codeFormula PA2) (codeFormula f)).
rewrite a in H.
rewrite <- beq_nat_refl in H.
replace f with PA2.
right; constructor.
eapply codeFormulaInj.
apply a.
left.
rewrite beq_nat_not_refl in H.
clear b.
induction (eq_nat_dec (codeFormula PA1) (codeFormula f)).
rewrite a in H.
rewrite <- beq_nat_refl in H.
replace f with PA1.
right; constructor.
eapply codeFormulaInj.
apply a.
left.
rewrite beq_nat_not_refl in H.
apply codeInductionSchemaCorrect2.
simpl in H.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
Qed.

Lemma codePAcorrect2 :
 forall f : Formula,
 ~ mem Formula PA f -> codePA (codeFormula f) = false.
Proof.
intros.
assert (forall x : bool, x = true \/ x = false).
intros.
induction x; auto.
induction (H0 (codePA (codeFormula f))).
elim H.
apply codePAcorrect1.
assumption.
assumption.
Qed.

Lemma codePAcorrect3 :
 forall f : Formula,
 mem Formula PA f -> codePA (codeFormula f) = true.
Proof.
intros.
unfold codePA in |- *.
unfold orRel, nat_rec, nat_rect in |- *.
do 6 try induction H.
assert (codeInductionSchema (codeFormula x) = true).
apply codeInductionSchemaCorrect1.
apply H.
rewrite H0.
repeat rewrite orb_true_b; repeat rewrite orb_b_true; reflexivity.
induction H.
generalize (codeFormula PA1).
intros.
rewrite <- beq_nat_refl.
repeat rewrite orb_true_b; repeat rewrite orb_b_true; reflexivity.
generalize (codeFormula PA2).
intros.
rewrite <- beq_nat_refl.
repeat rewrite orb_true_b; repeat rewrite orb_b_true; reflexivity.
generalize (codeFormula PA3).
intros.
rewrite <- beq_nat_refl.
repeat rewrite orb_true_b; repeat rewrite orb_b_true; reflexivity.
generalize (codeFormula PA4).
intros.
rewrite <- beq_nat_refl.
repeat rewrite orb_true_b; repeat rewrite orb_b_true; reflexivity.
generalize (codeFormula PA5).
intros.
rewrite <- beq_nat_refl.
repeat rewrite orb_true_b; repeat rewrite orb_b_true; reflexivity.
rewrite <- beq_nat_refl.
repeat rewrite orb_true_b; repeat rewrite orb_b_true; reflexivity.
Qed.

Lemma codePAIsPR : isPRrel 1 codePA.
Proof.
unfold codePA in |- *.
assert (forall n : nat, isPRrel 1 (beq_nat n)).
intros.
apply
 compose1_2IsPR
  with
    (f := fun f : nat => n)
    (f' := fun f : nat => f)
    (g := charFunction 2 beq_nat).
apply const1_NIsPR.
apply idIsPR.
apply eqIsPR.
repeat apply orRelPR; try apply H.
apply codeInductionSchemaIsPR.
Qed.

End Code_PA.
