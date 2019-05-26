Require Import primRec.
Require Import cPair.
Require Import Coq.Lists.List.
Require Import ListExt.
Require Import Arith.
Require Export codeList.
Require Import folProp.
Require Import code.

Section Code_Free_Vars.

Variable L : Language.
Variable codeF : Functions L -> nat.
Variable codeR : Relations L -> nat.

Let Formula := Formula L.
Let Formulas := Formulas L.
Let System := System L.
Let Term := Term L.
Let Terms := Terms L.
Let var := var L.
Let apply := apply L.
Let equal := equal L.
Let atomic := atomic L.
Let impH := impH L.
Let notH := notH L.
Let forallH := forallH L.
Let orH := orH L.
Let andH := andH L.
Let existH := existH L.
Let iffH := iffH L.
Let ifThenElseH := ifThenElseH L.

Definition codeFreeVarTermTerms : nat -> nat :=
  evalStrongRec 0
    (fun t recs : nat =>
     cPair
       (switchPR (cPairPi1 t) (cPairPi2 (codeNth (t - S (cPairPi2 t)) recs))
          (S (cPair (cPairPi2 t) 0)))
       (switchPR t
          (codeApp (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs))
             (cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs))) 0)).

Definition codeFreeVarTerm (t : nat) : nat :=
  cPairPi1 (codeFreeVarTermTerms t).

Definition codeFreeVarTerms (t : nat) : nat :=
  cPairPi2 (codeFreeVarTermTerms t).

Lemma codeFreeVarTermCorrect :
 forall t : Term,
 codeFreeVarTerm (codeTerm L codeF t) = codeList (freeVarTerm L t).
Proof.
intros.
elim t using
 Term_Terms_ind
  with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
           codeFreeVarTerms (codeTerms L codeF n ts) =
           codeList (freeVarTerms L n ts)); intros.
simpl in |- *.
unfold codeTerm in |- *.
unfold codeFreeVarTerm in |- *.
unfold codeFreeVarTermTerms in |- *.
unfold evalStrongRec in |- *.
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
simpl in |- *.
reflexivity.
unfold freeVarTerm in |- *.
fold (freeVarTerms L (arity L (inr (Relations L) f)) t0) in |- *.
rewrite <- H.
clear H.
unfold codeTerm in |- *.
fold (codeTerms L codeF (arity L (inr (Relations L) f)) t0) in |- *.
generalize (codeTerms L codeF (arity L (inr (Relations L) f)) t0).
intros.
unfold codeFreeVarTerm in |- *.
unfold codeFreeVarTermTerms in |- *.
set
 (g :=
  fun t1 recs : nat =>
  cPair
    (switchPR (cPairPi1 t1) (cPairPi2 (codeNth (t1 - S (cPairPi2 t1)) recs))
       (S (cPair (cPairPi2 t1) 0)))
    (switchPR t1
       (codeApp (cPairPi1 (codeNth (t1 - S (cPairPi1 (pred t1))) recs))
          (cPairPi2 (codeNth (t1 - S (cPairPi2 (pred t1))) recs))) 0)) 
 in *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc in |- *.
unfold evalOneParamList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc in |- *.
unfold g at 1 in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
rewrite (evalStrongRecHelp1 g (cPair (S (codeF f)) n) n).
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
unfold codeFreeVarTerms in |- *.
unfold codeFreeVarTermTerms in |- *.
fold g in |- *.
reflexivity.
apply cPairLt2.
simpl in |- *.
unfold codeTerms in |- *.
unfold codeFreeVarTerms in |- *.
unfold codeFreeVarTermTerms in |- *.
unfold evalStrongRec in |- *.
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
reflexivity.
unfold freeVarTerms in |- *.
fold (freeVarTerm L t0) in |- *.
fold (freeVarTerms L n t1) in |- *.
rewrite <- codeAppCorrect.
rewrite <- H.
rewrite <- H0.
clear H H0.
unfold codeTerms in |- *.
fold (codeTerm L codeF t0) in |- *.
fold (codeTerms L codeF n t1) in |- *.
generalize (codeTerm L codeF t0) (codeTerms L codeF n t1).
clear t0 t1.
intros.
unfold codeFreeVarTerms at 1 in |- *.
unfold codeFreeVarTermTerms in |- *.
unfold evalStrongRec in |- *.
set
 (g :=
  fun t0 recs : nat =>
  cPair
    (switchPR (cPairPi1 t0) (cPairPi2 (codeNth (t0 - S (cPairPi2 t0)) recs))
       (S (cPair (cPairPi2 t0) 0)))
    (switchPR t0
       (codeApp (cPairPi1 (codeNth (t0 - S (cPairPi1 (pred t0))) recs))
          (cPairPi2 (codeNth (t0 - S (cPairPi2 (pred t0))) recs))) 0)) 
 in *.
unfold evalComposeFunc in |- *.
unfold evalOneParamList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc in |- *.
unfold g at 1 in |- *.
rewrite
 (evalStrongRecHelp1 g (S (cPair n0 n1)) (cPairPi1 (pred (S (cPair n0 n1)))))
 .
rewrite
 (evalStrongRecHelp1 g (S (cPair n0 n1)) (cPairPi2 (pred (S (cPair n0 n1)))))
 .
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
reflexivity.
simpl in |- *.
rewrite cPairProjections2.
apply le_lt_n_Sm.
apply cPairLe2.
simpl in |- *.
rewrite cPairProjections1.
apply le_lt_n_Sm.
apply cPairLe1.
Qed.

Lemma codeFreeVarTermsCorrect :
 forall (n : nat) (ts : Terms n),
 codeFreeVarTerms (codeTerms L codeF n ts) = codeList (freeVarTerms L n ts).
Proof.
intros.
induction ts as [| n t ts Hrects].
simpl in |- *.
unfold codeTerms in |- *.
unfold codeFreeVarTerms in |- *.
unfold codeFreeVarTermTerms in |- *.
unfold evalStrongRec in |- *.
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
reflexivity.
unfold freeVarTerms in |- *.
fold (freeVarTerm L t) in |- *.
fold (freeVarTerms L n ts) in |- *.
rewrite <- codeAppCorrect.
rewrite <- Hrects.
rewrite <- codeFreeVarTermCorrect.
clear Hrects.
unfold codeTerms in |- *.
fold (codeTerm L codeF t) in |- *.
fold (codeTerms L codeF n ts) in |- *.
generalize (codeTerm L codeF t) (codeTerms L codeF n ts).
clear t ts.
intros.
unfold codeFreeVarTerms at 1 in |- *.
unfold codeFreeVarTermTerms in |- *.
unfold evalStrongRec in |- *.
set
 (g :=
  fun t0 recs : nat =>
  cPair
    (switchPR (cPairPi1 t0) (cPairPi2 (codeNth (t0 - S (cPairPi2 t0)) recs))
       (S (cPair (cPairPi2 t0) 0)))
    (switchPR t0
       (codeApp (cPairPi1 (codeNth (t0 - S (cPairPi1 (pred t0))) recs))
          (cPairPi2 (codeNth (t0 - S (cPairPi2 (pred t0))) recs))) 0)) 
 in *.
unfold evalComposeFunc in |- *.
unfold evalOneParamList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc in |- *.
unfold g at 1 in |- *.
rewrite
 (evalStrongRecHelp1 g (S (cPair n0 n1)) (cPairPi1 (pred (S (cPair n0 n1)))))
 .
rewrite
 (evalStrongRecHelp1 g (S (cPair n0 n1)) (cPairPi2 (pred (S (cPair n0 n1)))))
 .
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
reflexivity.
simpl in |- *.
rewrite cPairProjections2.
apply le_lt_n_Sm.
apply cPairLe2.
simpl in |- *.
rewrite cPairProjections1.
apply le_lt_n_Sm.
apply cPairLe1.
Qed.

Lemma codeFreeVarTermTermsIsPR : isPR 1 codeFreeVarTermTerms.
Proof.
intros.
unfold codeFreeVarTermTerms in |- *.
apply evalStrongRecIsPR.
apply
 compose2_2IsPR
  with
    (f := fun t recs : nat =>
          switchPR (cPairPi1 t)
            (cPairPi2 (codeNth (t - S (cPairPi2 t)) recs))
            (S (cPair (cPairPi2 t) 0)))
    (g := fun t recs : nat =>
          switchPR t
            (codeApp (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs))
               (cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs))) 0).
apply
 compose2_3IsPR
  with
    (f1 := fun t recs : nat => cPairPi1 t)
    (f2 := fun t recs : nat => cPairPi2 (codeNth (t - S (cPairPi2 t)) recs))
    (f3 := fun t recs : nat => S (cPair (cPairPi2 t) 0)).
apply filter10IsPR.
apply cPairPi1IsPR.
apply
 compose2_1IsPR
  with (f := fun t recs : nat => codeNth (t - S (cPairPi2 t)) recs).
apply
 compose2_2IsPR
  with
    (f := fun t recs : nat => t - S (cPairPi2 t))
    (g := fun t recs : nat => recs).
apply filter10IsPR with (g := fun t : nat => t - S (cPairPi2 t)).
apply
 compose1_2IsPR
  with (f := fun t : nat => t) (f' := fun t : nat => S (cPairPi2 t)).
apply idIsPR.
apply compose1_1IsPR.
apply cPairPi2IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply cPairPi2IsPR.
apply filter10IsPR with (g := fun t : nat => S (cPair (cPairPi2 t) 0)).
apply compose1_1IsPR with (f := fun t : nat => cPair (cPairPi2 t) 0).
apply compose1_2IsPR with (f := cPairPi2) (f' := fun _ : nat => 0).
apply cPairPi2IsPR.
apply const1_NIsPR.
apply cPairIsPR.
apply succIsPR.
apply switchIsPR.
apply
 compose2_3IsPR
  with
    (f1 := fun t recs : nat => t)
    (f2 := fun t recs : nat =>
           codeApp (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs))
             (cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)))
    (f3 := fun t recs : nat => 0).
apply pi1_2IsPR.
apply
 compose2_2IsPR
  with
    (f := fun t recs : nat =>
          cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs))
    (g := fun t recs : nat =>
          cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)).
apply
 compose2_1IsPR
  with (f := fun t recs : nat => codeNth (t - S (cPairPi1 (pred t))) recs).
apply
 compose2_2IsPR
  with
    (f := fun t recs : nat => t - S (cPairPi1 (pred t)))
    (g := fun t recs : nat => recs).
apply filter10IsPR with (g := fun t : nat => t - S (cPairPi1 (pred t))).
apply
 compose1_2IsPR
  with (f := fun t : nat => t) (f' := fun t : nat => S (cPairPi1 (pred t))).
apply idIsPR.
apply compose1_1IsPR with (f := fun t : nat => cPairPi1 (pred t)).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi1IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply cPairPi1IsPR.
apply
 compose2_1IsPR
  with (f := fun t recs : nat => codeNth (t - S (cPairPi2 (pred t))) recs).
apply
 compose2_2IsPR
  with
    (f := fun t recs : nat => t - S (cPairPi2 (pred t)))
    (g := fun t recs : nat => recs).
apply filter10IsPR with (g := fun t : nat => t - S (cPairPi2 (pred t))).
apply
 compose1_2IsPR
  with (f := fun t : nat => t) (f' := fun t : nat => S (cPairPi2 (pred t))).
apply idIsPR.
apply compose1_1IsPR with (f := fun t : nat => cPairPi2 (pred t)).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi2IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply cPairPi2IsPR.
apply codeAppIsPR.
exists (composeFunc 2 0 (PRnil _) zeroFunc).
simpl in |- *.
auto.
apply switchIsPR.
apply cPairIsPR.
Qed.

Lemma codeFreeVarTermIsPR : isPR 1 codeFreeVarTerm.
Proof.
unfold codeFreeVarTerm in |- *.
apply compose1_1IsPR.
apply codeFreeVarTermTermsIsPR.
apply cPairPi1IsPR.
Qed.

Lemma codeFreeVarTermsIsPR : isPR 1 codeFreeVarTerms.
Proof.
unfold codeFreeVarTerms in |- *.
apply compose1_1IsPR.
apply codeFreeVarTermTermsIsPR.
apply cPairPi2IsPR.
Qed.

Definition codeFreeVarFormula : nat -> nat :=
  evalStrongRec 0
    (fun f recs : nat =>
     switchPR (cPairPi1 f)
       (switchPR (pred (cPairPi1 f))
          (switchPR (pred (pred (cPairPi1 f)))
             (switchPR (pred (pred (pred (cPairPi1 f))))
                (codeFreeVarTerms (cPairPi2 f))
                (codeListRemove (cPairPi1 (cPairPi2 f))
                   (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs)))
             (codeNth (f - S (cPairPi2 f)) recs))
          (codeApp (codeNth (f - S (cPairPi1 (cPairPi2 f))) recs)
             (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs)))
       (codeApp (codeFreeVarTerm (cPairPi1 (cPairPi2 f)))
          (codeFreeVarTerm (cPairPi2 (cPairPi2 f))))).

Lemma codeFreeVarFormulaCorrect :
 forall f : Formula,
 codeFreeVarFormula (codeFormula L codeF codeR f) =
 codeList (freeVarFormula L f).
Proof.
intros.
set
 (g :=
  fun f recs : nat =>
  switchPR (cPairPi1 f)
    (switchPR (pred (cPairPi1 f))
       (switchPR (pred (pred (cPairPi1 f)))
          (switchPR (pred (pred (pred (cPairPi1 f))))
             (codeFreeVarTerms (cPairPi2 f))
             (codeListRemove (cPairPi1 (cPairPi2 f))
                (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs)))
          (codeNth (f - S (cPairPi2 f)) recs))
       (codeApp (codeNth (f - S (cPairPi1 (cPairPi2 f))) recs)
          (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs)))
    (codeApp (codeFreeVarTerm (cPairPi1 (cPairPi2 f)))
       (codeFreeVarTerm (cPairPi2 (cPairPi2 f))))) 
 in *.
induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf].
simpl in |- *.
rewrite <- codeAppCorrect.
repeat rewrite <- codeFreeVarTermCorrect.
generalize (codeTerm L codeF t) (codeTerm L codeF t0).
clear t t0.
intros.
unfold codeFreeVarFormula in |- *.
unfold evalStrongRec in |- *.
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
simpl in |- *.
reflexivity.
simpl in |- *.
rewrite <- codeFreeVarTermsCorrect.
generalize (codeTerms L codeF (arity L (inl (Functions L) r)) t).
clear t.
intros.
unfold codeFreeVarFormula in |- *.
unfold evalStrongRec in |- *.
unfold evalStrongRecHelp in |- *.
unfold evalComposeFunc in |- *.
unfold evalOneParamList in |- *.
unfold evalPrimRecFunc in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
reflexivity.
simpl in |- *.
rewrite <- codeAppCorrect.
rewrite <- Hrecf1.
rewrite <- Hrecf0.
clear Hrecf0 Hrecf1.
unfold codeFreeVarFormula in |- *.
fold g in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc in |- *.
unfold evalOneParamList in |- *.
rewrite computeEvalStrongRecHelp.
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
unfold g at 1 in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
rewrite
 (evalStrongRecHelp1 g
    (cPair 1
       (cPair (codeFormula L codeF codeR f1) (codeFormula L codeF codeR f0)))
    (codeFormula L codeF codeR f1)).
rewrite
 (evalStrongRecHelp1 g
    (cPair 1
       (cPair (codeFormula L codeF codeR f1) (codeFormula L codeF codeR f0)))
    (codeFormula L codeF codeR f0)).
simpl in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc in |- *.
unfold evalOneParamList in |- *.
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
reflexivity.
eapply lt_le_trans.
apply cPairLt2.
apply cPairLe3.
apply le_n.
apply cPairLe2.
eapply lt_le_trans.
apply cPairLt2.
apply cPairLe3.
apply le_n.
apply cPairLe1.
simpl in |- *.
rewrite <- Hrecf.
clear Hrecf.
generalize (codeFormula L codeF codeR f).
clear f.
intros.
unfold codeFreeVarFormula at 1 in |- *.
fold g in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc in |- *.
unfold evalOneParamList in |- *.
rewrite computeEvalStrongRecHelp.
unfold evalComposeFunc in |- *.
unfold compose2 in |- *.
unfold evalList in |- *.
unfold pred in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
unfold g at 1 in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
rewrite (evalStrongRecHelp1 g (cPair 2 n) n).
simpl in |- *.
reflexivity.
apply cPairLt2.
simpl in |- *.
rewrite <- codeListRemoveCorrect.
rewrite <- Hrecf.
generalize (codeFormula L codeF codeR f).
clear Hrecf f.
intros.
unfold codeFreeVarFormula at 1 in |- *.
fold g in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc in |- *.
unfold evalOneParamList in |- *.
unfold evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold evalComposeFunc in |- *.
unfold compose2 in |- *.
unfold evalList in |- *.
unfold pred in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
unfold g at 1 in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
rewrite (evalStrongRecHelp1 g (cPair 3 (cPair n n0)) n0).
simpl in |- *.
reflexivity.
eapply lt_le_trans.
apply cPairLt2.
apply cPairLe3.
apply le_n.
apply cPairLe2.
Qed.

Lemma codeFreeVarFormulaIsPR : isPR 1 codeFreeVarFormula.
Proof.
unfold codeFreeVarFormula in |- *.
apply evalStrongRecIsPR.
assert (isPR 1 (fun x : nat => pred (cPairPi1 x))).
apply compose1_1IsPR.
apply cPairPi1IsPR.
apply predIsPR.
assert (isPR 1 (fun x : nat => pred (pred (cPairPi1 x)))).
apply compose1_1IsPR with (f := fun x : nat => pred (cPairPi1 x)).
auto.
apply predIsPR.
assert (isPR 1 (fun x : nat => pred (pred (pred (cPairPi1 x))))).
apply compose1_1IsPR with (f := fun x : nat => pred (pred (cPairPi1 x))).
auto.
apply predIsPR.
apply
 compose2_3IsPR
  with
    (f1 := fun f recs : nat => cPairPi1 f)
    (f2 := fun f recs : nat =>
           switchPR (pred (cPairPi1 f))
             (switchPR (pred (pred (cPairPi1 f)))
                (switchPR (pred (pred (pred (cPairPi1 f))))
                   (codeFreeVarTerms (cPairPi2 f))
                   (codeListRemove (cPairPi1 (cPairPi2 f))
                      (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs)))
                (codeNth (f - S (cPairPi2 f)) recs))
             (codeApp (codeNth (f - S (cPairPi1 (cPairPi2 f))) recs)
                (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs)))
    (f3 := fun f recs : nat =>
           codeApp (codeFreeVarTerm (cPairPi1 (cPairPi2 f)))
             (codeFreeVarTerm (cPairPi2 (cPairPi2 f)))).
apply filter10IsPR.
apply cPairPi1IsPR.
apply
 compose2_3IsPR
  with
    (f1 := fun f recs : nat => pred (cPairPi1 f))
    (f2 := fun f recs : nat =>
           switchPR (pred (pred (cPairPi1 f)))
             (switchPR (pred (pred (pred (cPairPi1 f))))
                (codeFreeVarTerms (cPairPi2 f))
                (codeListRemove (cPairPi1 (cPairPi2 f))
                   (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs)))
             (codeNth (f - S (cPairPi2 f)) recs))
    (f3 := fun f recs : nat =>
           codeApp (codeNth (f - S (cPairPi1 (cPairPi2 f))) recs)
             (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs)).
apply filter10IsPR with (g := fun x : nat => pred (cPairPi1 x)).
auto.
apply
 compose2_3IsPR
  with
    (f1 := fun f recs : nat => pred (pred (cPairPi1 f)))
    (f2 := fun f recs : nat =>
           switchPR (pred (pred (pred (cPairPi1 f))))
             (codeFreeVarTerms (cPairPi2 f))
             (codeListRemove (cPairPi1 (cPairPi2 f))
                (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs)))
    (f3 := fun f recs : nat => codeNth (f - S (cPairPi2 f)) recs).
apply filter10IsPR with (g := fun x : nat => pred (pred (cPairPi1 x))).
auto.
apply
 compose2_3IsPR
  with
    (f1 := fun f recs : nat => pred (pred (pred (cPairPi1 f))))
    (f2 := fun f recs : nat => codeFreeVarTerms (cPairPi2 f))
    (f3 := fun f recs : nat =>
           codeListRemove (cPairPi1 (cPairPi2 f))
             (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs)).
apply filter10IsPR with (g := fun x : nat => pred (pred (pred (cPairPi1 x)))).
auto.
apply filter10IsPR with (g := fun f : nat => codeFreeVarTerms (cPairPi2 f)).
apply compose1_1IsPR.
apply cPairPi2IsPR.
apply codeFreeVarTermsIsPR.
apply
 compose2_2IsPR
  with
    (f := fun f recs : nat => cPairPi1 (cPairPi2 f))
    (g := fun f recs : nat => codeNth (f - S (cPairPi2 (cPairPi2 f))) recs).
apply filter10IsPR with (g := fun f : nat => cPairPi1 (cPairPi2 f)).
apply compose1_1IsPR.
apply cPairPi2IsPR.
apply cPairPi1IsPR.
apply
 compose2_2IsPR
  with
    (f := fun f recs : nat => f - S (cPairPi2 (cPairPi2 f)))
    (g := fun f recs : nat => recs).
apply filter10IsPR with (g := fun f : nat => f - S (cPairPi2 (cPairPi2 f))).
apply
 compose1_2IsPR
  with
    (f := fun f : nat => f)
    (f' := fun f : nat => S (cPairPi2 (cPairPi2 f))).
apply idIsPR.
apply compose1_1IsPR with (f := fun f : nat => cPairPi2 (cPairPi2 f)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply codeListRemoveIsPR.
apply switchIsPR.
apply
 compose2_2IsPR
  with
    (f := fun f recs : nat => f - S (cPairPi2 f))
    (g := fun f recs : nat => recs).
apply filter10IsPR with (g := fun f : nat => f - S (cPairPi2 f)).
apply
 compose1_2IsPR
  with (f := fun f : nat => f) (f' := fun f : nat => S (cPairPi2 f)).
apply idIsPR.
apply compose1_1IsPR.
apply cPairPi2IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply switchIsPR.
apply
 compose2_2IsPR
  with
    (f := fun f recs : nat => codeNth (f - S (cPairPi1 (cPairPi2 f))) recs)
    (g := fun f recs : nat => codeNth (f - S (cPairPi2 (cPairPi2 f))) recs).
apply
 compose2_2IsPR
  with
    (f := fun f recs : nat => f - S (cPairPi1 (cPairPi2 f)))
    (g := fun f recs : nat => recs).
apply filter10IsPR with (g := fun f : nat => f - S (cPairPi1 (cPairPi2 f))).
apply
 compose1_2IsPR
  with
    (f := fun f : nat => f)
    (f' := fun f : nat => S (cPairPi1 (cPairPi2 f))).
apply idIsPR.
apply compose1_1IsPR with (f := fun f : nat => cPairPi1 (cPairPi2 f)).
apply compose1_1IsPR.
apply cPairPi2IsPR.
apply cPairPi1IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply
 compose2_2IsPR
  with
    (f := fun f recs : nat => f - S (cPairPi2 (cPairPi2 f)))
    (g := fun f recs : nat => recs).
apply filter10IsPR with (g := fun f : nat => f - S (cPairPi2 (cPairPi2 f))).
apply
 compose1_2IsPR
  with
    (f := fun f : nat => f)
    (f' := fun f : nat => S (cPairPi2 (cPairPi2 f))).
apply idIsPR.
apply compose1_1IsPR with (f := fun f : nat => cPairPi2 (cPairPi2 f)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply codeAppIsPR.
apply switchIsPR.
apply
 filter10IsPR
  with
    (g := fun f : nat =>
          codeApp (codeFreeVarTerm (cPairPi1 (cPairPi2 f)))
            (codeFreeVarTerm (cPairPi2 (cPairPi2 f)))).
apply
 compose1_2IsPR
  with
    (f := fun f : nat => codeFreeVarTerm (cPairPi1 (cPairPi2 f)))
    (f' := fun f : nat => codeFreeVarTerm (cPairPi2 (cPairPi2 f))).
apply compose1_1IsPR with (f := fun f : nat => cPairPi1 (cPairPi2 f)).
apply compose1_1IsPR.
apply cPairPi2IsPR.
apply cPairPi1IsPR.
apply codeFreeVarTermIsPR.
apply compose1_1IsPR with (f := fun f : nat => cPairPi2 (cPairPi2 f)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply codeFreeVarTermIsPR.
apply codeAppIsPR.
apply switchIsPR.
Qed.

Definition codeFreeVarListFormula : nat -> nat :=
  evalStrongRec 0
    (fun l recs : nat =>
     switchPR l
       (codeApp (codeFreeVarFormula (cPairPi1 (pred l)))
          (codeNth (l - S (cPairPi2 (pred l))) recs)) 0).

Lemma codeFreeVarListFormulaCorrect :
 forall l : list Formula,
 codeFreeVarListFormula (codeList (map (codeFormula L codeF codeR) l)) =
 codeList (freeVarListFormula L l).
Proof.
intros.
unfold codeFreeVarListFormula in |- *.
set
 (A :=
  fun l0 recs : nat =>
  switchPR l0
    (codeApp (codeFreeVarFormula (cPairPi1 (pred l0)))
       (codeNth (l0 - S (cPairPi2 (pred l0))) recs)) 0) 
 in *.
induction l as [| a l Hrecl];
 unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList in |- *;
 rewrite computeEvalStrongRecHelp;
 unfold compose2, evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
rewrite cPairProjections1.
reflexivity.
unfold A at 1 in |- *.
rewrite evalStrongRecHelp1.
simpl in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
rewrite Hrecl.
rewrite codeFreeVarFormulaCorrect.
apply codeAppCorrect.
simpl in |- *.
apply le_lt_n_Sm.
apply cPairLe2A.
Qed.

Lemma codeFreeVarListFormulaIsPR : isPR 1 codeFreeVarListFormula.
Proof.
unfold codeFreeVarListFormula in |- *.
apply evalStrongRecIsPR.
apply
 compose2_3IsPR
  with
    (f1 := fun l recs : nat => l)
    (f2 := fun l recs : nat =>
           codeApp (codeFreeVarFormula (cPairPi1 (pred l)))
             (codeNth (l - S (cPairPi2 (pred l))) recs))
    (f3 := fun l recs : nat => 0).
apply pi1_2IsPR.
apply
 compose2_2IsPR
  with
    (f := fun l recs : nat => codeFreeVarFormula (cPairPi1 (pred l)))
    (g := fun l recs : nat => codeNth (l - S (cPairPi2 (pred l))) recs).
apply
 filter10IsPR
  with (g := fun l : nat => codeFreeVarFormula (cPairPi1 (pred l))).
apply compose1_1IsPR with (f := fun l : nat => cPairPi1 (pred l)).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi1IsPR.
apply codeFreeVarFormulaIsPR.
apply callIsPR with (g := fun l : nat => cPairPi2 (pred l)).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi2IsPR.
apply codeAppIsPR.
apply filter10IsPR with (g := fun _ : nat => 0).
apply const1_NIsPR.
apply switchIsPR.
Qed.

End Code_Free_Vars.