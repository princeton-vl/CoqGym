Require Import primRec.
Require Import cPair.
Require Import Arith.
Require Import code.
Require Import folProp.
Require Import extEqualNat.
Require Import codeList.

Section Well_Formed_Term.

Variable L : Language.
Variable codeF : Functions L -> nat.
Variable codeArityF : nat -> nat.
Hypothesis codeArityFIsPR : isPR 1 codeArityF.
Hypothesis
  codeArityFIsCorrect1 :
    forall f : Functions L, codeArityF (codeF f) = S (arity L (inr _ f)).
Hypothesis
  codeArityFIsCorrect2 :
    forall n : nat, codeArityF n <> 0 -> exists f : Functions L, codeF f = n.

Let Term := Term L.
Let Terms := Terms L.
Let var := var L.
Let apply := apply L.

Definition wellFormedTermTerms : nat -> nat :=
  evalStrongRec 0
    (fun t recs : nat =>
     cPair
       (switchPR (cPairPi1 t)
          (charFunction 2 beq_nat (codeArityF (pred (cPairPi1 t)))
             (S (codeLength (cPairPi2 t))) *
           cPairPi2 (codeNth (t - S (cPairPi2 t)) recs)) 1)
       (switchPR t
          (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs) *
           cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)) 1)).

Definition wellFormedTerm (t : nat) : nat := cPairPi1 (wellFormedTermTerms t).

Definition wellFormedTerms (ts : nat) : nat :=
  cPairPi2 (wellFormedTermTerms ts).

Lemma lengthTerms :
 forall (n : nat) (ts : Terms n), codeLength (codeTerms L codeF n ts) = n.
Proof.
intros.
induction ts as [| n t ts Hrects].
reflexivity.
replace (codeTerms L codeF (S n) (Tcons L n t ts)) with
 (S (cPair (codeTerm L codeF t) (codeTerms L codeF n ts)));
 [ idtac | reflexivity ].
unfold codeLength in |- *.
unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList in |- *.
set
 (A :=
  fun n0 Hrecs : nat =>
  switchPR n0 (S (codeNth (n0 - S (cPairPi2 (pred n0))) Hrecs)) 0) 
 in *.
rewrite computeEvalStrongRecHelp.
unfold compose2, evalComposeFunc, evalOneParamList, evalList in |- *.
unfold A at 1 in |- *.
rewrite evalStrongRecHelp1.
simpl in |- *.
rewrite cPairProjections1.
rewrite cPairProjections2.
apply eq_S.
assumption.
generalize (cPair (codeTerm L codeF t) (codeTerms L codeF n ts)).
simpl in |- *.
intros.
apply le_lt_n_Sm.
apply le_trans with (cPair (cPairPi1 n0) (cPairPi2 n0)).
apply cPairLe2.
rewrite cPairProjections.
apply le_n.
Qed.

Lemma wellFormedTermCorrect1 :
 forall t : Term, wellFormedTerm (codeTerm L codeF t) = 1.
Proof.
intros.
set
 (A :=
  fun t recs : nat =>
  cPair
    (switchPR (cPairPi1 t)
       (charFunction 2 beq_nat (codeArityF (pred (cPairPi1 t)))
          (S (codeLength (cPairPi2 t))) *
        cPairPi2 (codeNth (t - S (cPairPi2 t)) recs)) 1)
    (switchPR t
       (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs) *
        cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)) 1)) 
 in *.
elim t using
 Term_Terms_ind
  with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
           wellFormedTerms (codeTerms L codeF n ts) = 1); 
 simpl in |- *; intros.
unfold codeTerm in |- *.
unfold wellFormedTerm in |- *.
unfold wellFormedTermTerms in |- *.
fold A in |- *.
unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2, evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
unfold A at 1 in |- *.
repeat rewrite cPairProjections1.
simpl in |- *.
reflexivity.
replace (codeTerm L codeF (fol.apply L f t0)) with
 (cPair (S (codeF f)) (codeTerms L codeF _ t0)); [ idtac | reflexivity ].
unfold wellFormedTerm in |- *.
unfold wellFormedTermTerms in |- *.
fold A in |- *.
unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2, evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
unfold A at 1 in |- *.
repeat rewrite cPairProjections1.
rewrite evalStrongRecHelp1.
simpl in |- *.
rewrite codeArityFIsCorrect1.
rewrite cPairProjections2.
simpl in |- *.
rewrite lengthTerms.
rewrite <- beq_nat_refl.
simpl in |- *.
rewrite plus_comm.
simpl in |- *.
apply H.
rewrite cPairProjections2.
apply cPairLt2.
unfold wellFormedTerms in |- *.
unfold wellFormedTermTerms in |- *.
fold A in |- *.
unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2, evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
rewrite cPairProjections1.
unfold A in |- *.
rewrite cPairProjections2.
reflexivity.
unfold wellFormedTerms in |- *.
unfold wellFormedTermTerms in |- *.
fold A in |- *.
unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2, evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
unfold A at 1 in |- *.
rewrite cPairProjections1.
rewrite cPairProjections2.
replace (codeTerms L codeF (S n) (Tcons L n t0 t1)) with
 (S (cPair (codeTerm L codeF t0) (codeTerms L codeF n t1)));
 [ idtac | reflexivity ].
repeat rewrite evalStrongRecHelp1.
simpl in |- *.
rewrite cPairProjections1.
rewrite cPairProjections2.
unfold wellFormedTerm, wellFormedTermTerms in H.
unfold A in |- *; rewrite H.
unfold wellFormedTerms, wellFormedTermTerms in H0.
rewrite H0.
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

Lemma wellFormedTermsCorrect1 :
 forall (n : nat) (ts : Terms n),
 wellFormedTerms (codeTerms L codeF n ts) = 1.
Proof.
intros.
set
 (A :=
  fun t recs : nat =>
  cPair
    (switchPR (cPairPi1 t)
       (charFunction 2 beq_nat (codeArityF (pred (cPairPi1 t)))
          (S (codeLength (cPairPi2 t))) *
        cPairPi2 (codeNth (t - S (cPairPi2 t)) recs)) 1)
    (switchPR t
       (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs) *
        cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)) 1)) 
 in *.
induction ts as [| n t ts Hrects].
unfold wellFormedTerms in |- *.
unfold wellFormedTermTerms in |- *.
fold A in |- *.
unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2, evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
rewrite cPairProjections1.
unfold A in |- *.
rewrite cPairProjections2.
reflexivity.
unfold wellFormedTerms in |- *.
unfold wellFormedTermTerms in |- *.
fold A in |- *.
unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2, evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
unfold A at 1 in |- *.
rewrite cPairProjections1.
rewrite cPairProjections2.
replace (codeTerms L codeF (S n) (Tcons L n t ts)) with
 (S (cPair (codeTerm L codeF t) (codeTerms L codeF n ts)));
 [ idtac | reflexivity ].
repeat rewrite evalStrongRecHelp1.
simpl in |- *.
rewrite cPairProjections1.
rewrite cPairProjections2.
replace (cPairPi1 (evalStrongRec 0 A (codeTerm L codeF t))) with
 (wellFormedTerm (codeTerm L codeF t)).
rewrite (wellFormedTermCorrect1 t).
unfold wellFormedTerms, wellFormedTermTerms in Hrects.
unfold A in |- *; rewrite Hrects.
reflexivity.
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

Remark wellFormedTermTermsCorrect2 :
 forall n : nat,
 (wellFormedTerm n <> 0 -> exists t : Term, codeTerm L codeF t = n) /\
 (wellFormedTerms n <> 0 ->
  exists m : nat, (exists ts : Terms m, codeTerms L codeF m ts = n)).
Proof.
assert (multLemma1 : forall a b : nat, a * b <> 0 -> a <> 0).
unfold not in |- *; intros.
apply H.
rewrite H0.
simpl in |- *.
reflexivity.
assert (multLemma2 : forall a b : nat, a * b <> 0 -> b <> 0).
intros.
rewrite mult_comm in H.
eapply multLemma1.
apply H.
assert
 (forall m n : nat,
  n < m ->
  (wellFormedTerm n <> 0 -> exists t : Term, codeTerm L codeF t = n) /\
  (wellFormedTerms n <> 0 ->
   exists m : nat, (exists ts : Terms m, codeTerms L codeF m ts = n))).
intro.
induction m as [| m Hrecm].
intros.
elim (lt_not_le _ _ H).
apply le_O_n.
intros.
induction (le_lt_or_eq _ _ (lt_n_Sm_le _ _ H)).
apply Hrecm; auto.
unfold wellFormedTerm in |- *.
unfold wellFormedTerms in |- *.
unfold wellFormedTermTerms in |- *.
set
 (A :=
  fun t recs : nat =>
  cPair
    (switchPR (cPairPi1 t)
       (charFunction 2 beq_nat (codeArityF (pred (cPairPi1 t)))
          (S (codeLength (cPairPi2 t))) *
        cPairPi2 (codeNth (t - S (cPairPi2 t)) recs)) 1)
    (switchPR t
       (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs) *
        cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)) 1)) 
 in *.
unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2, evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
rewrite cPairProjections1.
split.
unfold A at 1 in |- *.
rewrite cPairProjections1.
assert (cPair (cPairPi1 n) (cPairPi2 n) = n).
apply cPairProjections.
destruct (cPairPi1 n).
simpl in |- *.
intros.
exists (var (cPairPi2 n)).
transitivity (cPair 0 (cPairPi2 n)).
reflexivity.
assumption.
rewrite evalStrongRecHelp1.
simpl in |- *.
intros.
induction (eq_nat_dec (codeArityF n0) (S (codeLength (cPairPi2 n)))).
assert (wellFormedTerms (cPairPi2 n) <> 0).
eapply multLemma2.
apply H2.
assert (cPairPi2 n < m).
apply lt_le_trans with (cPair (S n0) (cPairPi2 n)).
apply cPairLt2.
rewrite H1.
rewrite H0.
apply le_n.
induction (Hrecm _ H4).
clear H5.
induction (H6 H3).
induction H5 as (x0, H5).
assert (codeArityF n0 <> 0).
unfold not in |- *; intros.
rewrite H7 in a.
discriminate a.
induction (codeArityFIsCorrect2 _ H7).
rewrite <- H8 in a.
rewrite codeArityFIsCorrect1 in a.
injection a.
clear a.
intro.
rewrite <- H5 in H9.
rewrite lengthTerms in H9.
cut (codeTerms L codeF x x0 = cPairPi2 n).
clear H5.
generalize x0.
clear x0.
rewrite <- H9.
intros.
exists (apply x1 x0).
transitivity (cPair (S n0) (cPairPi2 n)).
rewrite <- H8.
rewrite <- H5.
reflexivity.
assumption.
assumption.
rewrite beq_nat_not_refl in H2.
elim H2.
reflexivity.
assumption.
apply lt_le_trans with (cPair (S n0) (cPairPi2 n)).
apply cPairLt2.
rewrite H1.
apply le_n.
unfold A at 1 in |- *.
rewrite cPairProjections2.
destruct n.
simpl in |- *.
intros.
exists 0.
exists (Tnil L).
reflexivity.
repeat rewrite evalStrongRecHelp1.
simpl in |- *.
intros.
assert (cPairPi1 n < m).
rewrite <- H0.
apply le_lt_n_Sm.
apply le_trans with (cPair (cPairPi1 n) (cPairPi2 n)).
apply cPairLe1.
rewrite cPairProjections.
apply le_n.
assert (cPairPi2 n < m).
rewrite <- H0.
apply le_lt_n_Sm.
apply le_trans with (cPair (cPairPi1 n) (cPairPi2 n)).
apply cPairLe2.
rewrite cPairProjections.
apply le_n.
induction (Hrecm _ H2).
clear H5.
induction (Hrecm _ H3).
clear H5.
assert (wellFormedTerm (cPairPi1 n) <> 0).
eapply multLemma1.
apply H1.
assert (wellFormedTerms (cPairPi2 n) <> 0).
eapply multLemma2.
apply H1.
induction (H4 H5).
induction (H6 H7).
induction H9 as (x1, H9).
exists (S x0).
exists (Tcons L x0 x x1).
rewrite <- (cPairProjections n).
rewrite <- H8.
rewrite <- H9.
reflexivity.
simpl in |- *.
apply le_lt_n_Sm.
apply le_trans with (cPair (cPairPi1 n) (cPairPi2 n)).
apply cPairLe2.
rewrite cPairProjections.
apply le_n.
apply le_lt_n_Sm.
apply le_trans with (cPair (cPairPi1 n) (cPairPi2 n)).
apply cPairLe1.
rewrite cPairProjections.
apply le_n.
intros.
eapply H.
apply lt_n_Sn.
Qed.

Lemma wellFormedTermCorrect2 :
 forall n : nat,
 wellFormedTerm n <> 0 -> exists t : Term, codeTerm L codeF t = n.
Proof.
intro.
eapply proj1.
apply wellFormedTermTermsCorrect2.
Qed.

Lemma wellFormedTermsCorrect2 :
 forall n : nat,
 wellFormedTerms n <> 0 ->
 exists m : nat, (exists ts : Terms m, codeTerms L codeF m ts = n).
Proof.
intro.
eapply proj2.
apply wellFormedTermTermsCorrect2.
Qed.

Remark wellFormedTermTermsIsPR : isPR 1 wellFormedTermTerms.
Proof.
unfold wellFormedTermTerms in |- *.
apply evalStrongRecIsPR.
apply
 compose2_2IsPR
  with
    (f := fun t recs : nat =>
          switchPR (cPairPi1 t)
            (charFunction 2 beq_nat (codeArityF (pred (cPairPi1 t)))
               (S (codeLength (cPairPi2 t))) *
             cPairPi2 (codeNth (t - S (cPairPi2 t)) recs)) 1)
    (g := fun t recs : nat =>
          switchPR t
            (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs) *
             cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)) 1).
apply
 compose2_3IsPR
  with
    (f1 := fun t recs : nat => cPairPi1 t)
    (f2 := fun t recs : nat =>
           charFunction 2 beq_nat (codeArityF (pred (cPairPi1 t)))
             (S (codeLength (cPairPi2 t))) *
           cPairPi2 (codeNth (t - S (cPairPi2 t)) recs))
    (f3 := fun t recs : nat => 1).
apply filter10IsPR.
apply cPairPi1IsPR.
apply
 compose2_2IsPR
  with
    (f := fun t recs : nat =>
          charFunction 2 beq_nat (codeArityF (pred (cPairPi1 t)))
            (S (codeLength (cPairPi2 t))))
    (g := fun t recs : nat => cPairPi2 (codeNth (t - S (cPairPi2 t)) recs)).
apply
 filter10IsPR
  with
    (g := fun t : nat =>
          charFunction 2 beq_nat (codeArityF (pred (cPairPi1 t)))
            (S (codeLength (cPairPi2 t)))).
apply
 compose1_2IsPR
  with
    (f := fun t : nat => codeArityF (pred (cPairPi1 t)))
    (f' := fun t : nat => S (codeLength (cPairPi2 t))).
apply compose1_1IsPR with (f := fun t : nat => pred (cPairPi1 t)).
apply compose1_1IsPR.
apply cPairPi1IsPR.
apply predIsPR.
apply codeArityFIsPR.
apply compose1_1IsPR with (f := fun t : nat => codeLength (cPairPi2 t)).
apply compose1_1IsPR.
apply cPairPi2IsPR.
apply codeLengthIsPR.
apply succIsPR.
apply eqIsPR.
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
apply multIsPR.
apply filter10IsPR with (g := fun _ : nat => 1).
apply const1_NIsPR.
apply switchIsPR.
apply
 compose2_3IsPR
  with
    (f1 := fun t recs : nat => t)
    (f2 := fun t recs : nat =>
           cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs) *
           cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs))
    (f3 := fun t recs : nat => 1).
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
apply multIsPR.
apply filter10IsPR with (g := fun _ : nat => 1).
apply const1_NIsPR.
apply switchIsPR.
apply cPairIsPR.
Qed.

Lemma wellFormedTermIsPR : isPR 1 wellFormedTerm.
Proof.
unfold wellFormedTerm in |- *.
apply compose1_1IsPR.
apply wellFormedTermTermsIsPR.
apply cPairPi1IsPR.
Qed.

Lemma wellFormedTermsIsPR : isPR 1 wellFormedTerms.
Proof.
unfold wellFormedTerms in |- *.
apply compose1_1IsPR.
apply wellFormedTermTermsIsPR.
apply cPairPi2IsPR.
Qed.

Section Well_Formed_Formula.

Variable codeR : Relations L -> nat.
Variable codeArityR : nat -> nat.
Hypothesis codeArityRIsPR : isPR 1 codeArityR.
Hypothesis
  codeArityRIsCorrect1 :
    forall r : Relations L, codeArityR (codeR r) = S (arity L (inl _ r)).
Hypothesis
  codeArityRIsCorrect2 :
    forall n : nat, codeArityR n <> 0 -> exists r : Relations L, codeR r = n.

Let Formula := Formula L.
Let equal := equal L.
Let atomic := atomic L.
Let impH := impH L.
Let notH := notH L.
Let forallH := forallH L.

Definition wellFormedFormula : nat -> nat :=
  evalStrongRec 0
    (fun f recs : nat =>
     switchPR (cPairPi1 f)
       (switchPR (pred (cPairPi1 f))
          (switchPR (pred (pred (cPairPi1 f)))
             (switchPR (pred (pred (pred (cPairPi1 f))))
                (charFunction 2 beq_nat
                   (codeArityR (pred (pred (pred (pred (cPairPi1 f))))))
                   (S (codeLength (cPairPi2 f))) *
                 wellFormedTerms (cPairPi2 f))
                (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))
             (codeNth (f - S (cPairPi2 f)) recs))
          (codeNth (f - S (cPairPi1 (cPairPi2 f))) recs *
           codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))
       (wellFormedTerm (cPairPi1 (cPairPi2 f)) *
        wellFormedTerm (cPairPi2 (cPairPi2 f)))).

Lemma wellFormedFormulaCorrect1 :
 forall f : Formula, wellFormedFormula (codeFormula L codeF codeR f) = 1.
Proof.
intros.
set
 (A :=
  fun f recs : nat =>
  switchPR (cPairPi1 f)
    (switchPR (pred (cPairPi1 f))
       (switchPR (pred (pred (cPairPi1 f)))
          (switchPR (pred (pred (pred (cPairPi1 f))))
             (charFunction 2 beq_nat
                (codeArityR (pred (pred (pred (pred (cPairPi1 f))))))
                (S (codeLength (cPairPi2 f))) * wellFormedTerms (cPairPi2 f))
             (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))
          (codeNth (f - S (cPairPi2 f)) recs))
       (codeNth (f - S (cPairPi1 (cPairPi2 f))) recs *
        codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))
    (wellFormedTerm (cPairPi1 (cPairPi2 f)) *
     wellFormedTerm (cPairPi2 (cPairPi2 f)))) in *.
unfold wellFormedFormula in |- *.
fold A in |- *.
induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf]; intros;
 unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList in |- *;
 rewrite computeEvalStrongRecHelp;
 unfold compose2, evalComposeFunc, evalOneParamList, evalList in |- *;
 simpl in |- *; unfold A at 1 in |- *;
 repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
simpl in |- *.
repeat rewrite wellFormedTermCorrect1.
reflexivity.
simpl in |- *.
rewrite wellFormedTermsCorrect1.
rewrite codeArityRIsCorrect1.
rewrite lengthTerms.
rewrite <- beq_nat_refl.
reflexivity.
rewrite evalStrongRecHelp1 with (m := codeFormula L codeF codeR f0).
rewrite evalStrongRecHelp1 with (m := codeFormula L codeF codeR f1).
simpl in |- *.
rewrite Hrecf1.
rewrite Hrecf0.
reflexivity.
eapply le_lt_trans; [ idtac | apply cPairLt2 ].
apply cPairLe1.
eapply le_lt_trans; [ idtac | apply cPairLt2 ].
apply cPairLe2.
rewrite evalStrongRecHelp1 with (m := codeFormula L codeF codeR f).
simpl in |- *.
assumption.
apply cPairLt2.
rewrite evalStrongRecHelp1 with (m := codeFormula L codeF codeR f).
simpl in |- *.
assumption.
eapply le_lt_trans; [ idtac | apply cPairLt2 ].
apply cPairLe2.
Qed.

Lemma wellFormedFormulaCorrect2 :
 forall n : nat,
 wellFormedFormula n <> 0 ->
 exists f : Formula, codeFormula L codeF codeR f = n.
Proof.
assert (multLemma1 : forall a b : nat, a * b <> 0 -> a <> 0).
unfold not in |- *; intros.
apply H.
rewrite H0.
simpl in |- *.
reflexivity.
assert (multLemma2 : forall a b : nat, a * b <> 0 -> b <> 0).
intros.
rewrite mult_comm in H.
eapply multLemma1.
apply H.
assert
 (forall m n : nat,
  n < m ->
  wellFormedFormula n <> 0 ->
  exists f : Formula, codeFormula L codeF codeR f = n).
intro.
induction m as [| m Hrecm].
intros n H.
elim (lt_not_le _ _ H).
apply le_O_n.
intros n H.
induction (le_lt_or_eq _ _ (lt_n_Sm_le _ _ H)).
apply Hrecm; auto.
unfold wellFormedFormula in |- *.
set
 (A :=
  fun f recs : nat =>
  switchPR (cPairPi1 f)
    (switchPR (pred (cPairPi1 f))
       (switchPR (pred (pred (cPairPi1 f)))
          (switchPR (pred (pred (pred (cPairPi1 f))))
             (charFunction 2 beq_nat
                (codeArityR (pred (pred (pred (pred (cPairPi1 f))))))
                (S (codeLength (cPairPi2 f))) * wellFormedTerms (cPairPi2 f))
             (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))
          (codeNth (f - S (cPairPi2 f)) recs))
       (codeNth (f - S (cPairPi1 (cPairPi2 f))) recs *
        codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))
    (wellFormedTerm (cPairPi1 (cPairPi2 f)) *
     wellFormedTerm (cPairPi2 (cPairPi2 f)))) in *.
unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2, evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
rewrite cPairProjections1.
unfold A at 1 in |- *.
assert (cPair (cPairPi1 n) (cPairPi2 n) = n).
apply cPairProjections.
destruct (cPairPi1 n).
simpl in |- *.
intros.
assert (wellFormedTerm (cPairPi1 (cPairPi2 n)) <> 0).
eapply multLemma1.
apply H2.
assert (wellFormedTerm (cPairPi2 (cPairPi2 n)) <> 0).
eapply multLemma2.
apply H2.
induction (wellFormedTermCorrect2 _ H3).
induction (wellFormedTermCorrect2 _ H4).
exists (equal x x0).
simpl in |- *.
rewrite H5.
rewrite H6.
rewrite cPairProjections.
assumption.
destruct n0.
simpl in |- *.
assert (cPairPi2 n < m).
apply lt_le_trans with (cPair 1 (cPairPi2 n)).
apply cPairLt2.
rewrite H1.
rewrite H0.
apply le_n.
assert (cPairPi1 (cPairPi2 n) < m).
apply
 le_lt_trans with (cPair (cPairPi1 (cPairPi2 n)) (cPairPi2 (cPairPi2 n))).
apply cPairLe1.
rewrite cPairProjections.
assumption.
assert (cPairPi2 (cPairPi2 n) < m).
apply
 le_lt_trans with (cPair (cPairPi1 (cPairPi2 n)) (cPairPi2 (cPairPi2 n))).
apply cPairLe2.
rewrite cPairProjections.
assumption.
repeat rewrite evalStrongRecHelp1.
intros.
assert (evalStrongRec 0 A (cPairPi1 (cPairPi2 n)) <> 0).
eapply multLemma1.
apply H5.
assert (evalStrongRec 0 A (cPairPi2 (cPairPi2 n)) <> 0).
eapply multLemma2.
apply H5.
induction (Hrecm _ H3 H6).
induction (Hrecm _ H4 H7).
exists (impH x x0).
simpl in |- *.
rewrite H8.
rewrite H9.
rewrite cPairProjections.
assumption.
eapply lt_le_trans.
apply H4.
rewrite H0.
apply le_n.
eapply lt_le_trans.
apply H3.
rewrite H0.
apply le_n.
destruct n0.
simpl in |- *.
assert (cPairPi2 n < m).
apply lt_le_trans with (cPair 2 (cPairPi2 n)).
apply cPairLt2.
rewrite H1.
rewrite H0.
apply le_n.
repeat rewrite evalStrongRecHelp1.
intros.
induction (Hrecm _ H2 H3).
exists (notH x).
simpl in |- *.
rewrite H4.
assumption.
eapply lt_le_trans.
apply H2.
rewrite H0.
apply le_n.
destruct n0.
simpl in |- *.
assert (cPairPi2 n < m).
apply lt_le_trans with (cPair 3 (cPairPi2 n)).
apply cPairLt2.
rewrite H1.
rewrite H0.
apply le_n.
assert (cPairPi2 (cPairPi2 n) < m).
apply
 le_lt_trans with (cPair (cPairPi1 (cPairPi2 n)) (cPairPi2 (cPairPi2 n))).
apply cPairLe2.
rewrite cPairProjections.
assumption.
repeat rewrite evalStrongRecHelp1.
intros.
induction (Hrecm _ H3 H4).
exists (forallH (cPairPi1 (cPairPi2 n)) x).
simpl in |- *.
rewrite H5.
rewrite cPairProjections.
assumption.
eapply lt_le_trans.
apply H3.
rewrite H0.
apply le_n.
simpl in |- *.
induction (eq_nat_dec (codeArityR n0) (S (codeLength (cPairPi2 n)))).
assert (codeArityR n0 <> 0).
unfold not in |- *; intros.
rewrite H2 in a.
discriminate a.
induction (codeArityRIsCorrect2 _ H2).
intros.
assert (wellFormedTerms (cPairPi2 n) <> 0).
eapply multLemma2.
apply H4.
rewrite <- H3 in a.
rewrite codeArityRIsCorrect1 in a.
injection a.
clear a.
intros.
induction (wellFormedTermsCorrect2 _ H5).
induction H7 as (x1, H7).
rewrite <- H7 in H6.
rewrite lengthTerms in H6.
cut (codeTerms L codeF x0 x1 = cPairPi2 n).
generalize x1.
clear H7 x1.
rewrite <- H6.
intros.
exists (atomic x x1).
simpl in |- *.
rewrite H7.
rewrite H3.
assumption.
assumption.
rewrite beq_nat_not_refl.
intros.
simpl in H2.
elim H2.
reflexivity.
assumption.
intros.
eapply H.
apply lt_n_Sn.
assumption.
Qed.

Lemma wellFormedFormulaIsPR : isPR 1 wellFormedFormula.
Proof.
unfold wellFormedFormula in |- *.
apply evalStrongRecIsPR.
assert (isPR 2 (fun f recs : nat => cPairPi1 f)).
apply filter10IsPR.
apply cPairPi1IsPR.
assert (isPR 2 (fun f recs : nat => pred (cPairPi1 f))).
apply compose2_1IsPR with (f := fun f recs : nat => cPairPi1 f).
assumption.
apply predIsPR.
assert (isPR 2 (fun f recs : nat => pred (pred (cPairPi1 f)))).
apply compose2_1IsPR with (f := fun f recs : nat => pred (cPairPi1 f)).
assumption.
apply predIsPR.
assert (isPR 2 (fun f recs : nat => pred (pred (pred (cPairPi1 f))))).
apply compose2_1IsPR with (f := fun f recs : nat => pred (pred (cPairPi1 f))).
assumption.
apply predIsPR.
assert
 (forall g : nat -> nat,
  isPR 1 g -> isPR 2 (fun f recs : nat => codeNth (f - S (g f)) recs)).
intros.
apply
 compose2_2IsPR
  with (f := fun f recs : nat => f - S (g f)) (g := fun f recs : nat => recs).
apply filter10IsPR with (g := fun f : nat => f - S (g f)).
apply
 compose1_2IsPR with (f := fun f : nat => f) (f' := fun f : nat => S (g f)).
apply idIsPR.
apply compose1_1IsPR.
assumption.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply
 compose2_3IsPR
  with
    (f1 := fun f recs : nat => cPairPi1 f)
    (f2 := fun f recs : nat =>
           switchPR (pred (cPairPi1 f))
             (switchPR (pred (pred (cPairPi1 f)))
                (switchPR (pred (pred (pred (cPairPi1 f))))
                   (charFunction 2 beq_nat
                      (codeArityR (pred (pred (pred (pred (cPairPi1 f))))))
                      (S (codeLength (cPairPi2 f))) *
                    wellFormedTerms (cPairPi2 f))
                   (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))
                (codeNth (f - S (cPairPi2 f)) recs))
             (codeNth (f - S (cPairPi1 (cPairPi2 f))) recs *
              codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))
    (f3 := fun f recs : nat =>
           wellFormedTerm (cPairPi1 (cPairPi2 f)) *
           wellFormedTerm (cPairPi2 (cPairPi2 f))).
assumption.
apply
 compose2_3IsPR
  with
    (f1 := fun f recs : nat => pred (cPairPi1 f))
    (f2 := fun f recs : nat =>
           switchPR (pred (pred (cPairPi1 f)))
             (switchPR (pred (pred (pred (cPairPi1 f))))
                (charFunction 2 beq_nat
                   (codeArityR (pred (pred (pred (pred (cPairPi1 f))))))
                   (S (codeLength (cPairPi2 f))) *
                 wellFormedTerms (cPairPi2 f))
                (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))
             (codeNth (f - S (cPairPi2 f)) recs))
    (f3 := fun f recs : nat =>
           codeNth (f - S (cPairPi1 (cPairPi2 f))) recs *
           codeNth (f - S (cPairPi2 (cPairPi2 f))) recs).
assumption.
apply
 compose2_3IsPR
  with
    (f1 := fun f recs : nat => pred (pred (cPairPi1 f)))
    (f2 := fun f recs : nat =>
           switchPR (pred (pred (pred (cPairPi1 f))))
             (charFunction 2 beq_nat
                (codeArityR (pred (pred (pred (pred (cPairPi1 f))))))
                (S (codeLength (cPairPi2 f))) * wellFormedTerms (cPairPi2 f))
             (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))
    (f3 := fun f recs : nat => codeNth (f - S (cPairPi2 f)) recs).
assumption.
apply
 compose2_3IsPR
  with
    (f1 := fun f recs : nat => pred (pred (pred (cPairPi1 f))))
    (f2 := fun f recs : nat =>
           charFunction 2 beq_nat
             (codeArityR (pred (pred (pred (pred (cPairPi1 f))))))
             (S (codeLength (cPairPi2 f))) * wellFormedTerms (cPairPi2 f))
    (f3 := fun f recs : nat => codeNth (f - S (cPairPi2 (cPairPi2 f))) recs).
assumption.
apply
 filter10IsPR
  with
    (g := fun f : nat =>
          charFunction 2 beq_nat
            (codeArityR (pred (pred (pred (pred (cPairPi1 f))))))
            (S (codeLength (cPairPi2 f))) * wellFormedTerms (cPairPi2 f)).
apply
 compose1_2IsPR
  with
    (f := fun f : nat =>
          charFunction 2 beq_nat
            (codeArityR (pred (pred (pred (pred (cPairPi1 f))))))
            (S (codeLength (cPairPi2 f))))
    (f' := fun f : nat => wellFormedTerms (cPairPi2 f)).
apply
 compose1_2IsPR
  with
    (f := fun f : nat => codeArityR (pred (pred (pred (pred (cPairPi1 f))))))
    (f' := fun f : nat => S (codeLength (cPairPi2 f))).
apply
 compose1_1IsPR
  with (f := fun f : nat => pred (pred (pred (pred (cPairPi1 f))))).
apply
 compose1_1IsPR with (f := fun f : nat => pred (pred (pred (cPairPi1 f))));
 try apply predIsPR.
apply compose1_1IsPR with (f := fun f : nat => pred (pred (cPairPi1 f)));
 try apply predIsPR.
apply compose1_1IsPR with (f := fun f : nat => pred (cPairPi1 f));
 try apply predIsPR.
apply compose1_1IsPR.
apply cPairPi1IsPR.
apply predIsPR.
apply codeArityRIsPR.
apply compose1_1IsPR with (f := fun f : nat => codeLength (cPairPi2 f)).
apply compose1_1IsPR.
apply cPairPi2IsPR.
apply codeLengthIsPR.
apply succIsPR.
apply eqIsPR.
apply compose1_1IsPR.
apply cPairPi2IsPR.
apply wellFormedTermsIsPR.
apply multIsPR.
apply H3 with (g := fun f : nat => cPairPi2 (cPairPi2 f)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply switchIsPR.
apply H3.
apply cPairPi2IsPR.
apply switchIsPR.
apply
 compose2_2IsPR
  with
    (f := fun f recs : nat => codeNth (f - S (cPairPi1 (cPairPi2 f))) recs)
    (g := fun f recs : nat => codeNth (f - S (cPairPi2 (cPairPi2 f))) recs).
apply H3 with (g := fun f : nat => cPairPi1 (cPairPi2 f)).
apply compose1_1IsPR.
apply cPairPi2IsPR.
apply cPairPi1IsPR.
apply H3 with (g := fun f : nat => cPairPi2 (cPairPi2 f)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply multIsPR.
apply switchIsPR.
apply
 filter10IsPR
  with
    (g := fun f : nat =>
          wellFormedTerm (cPairPi1 (cPairPi2 f)) *
          wellFormedTerm (cPairPi2 (cPairPi2 f))).
apply
 compose1_2IsPR
  with
    (f := fun f : nat => wellFormedTerm (cPairPi1 (cPairPi2 f)))
    (f' := fun f : nat => wellFormedTerm (cPairPi2 (cPairPi2 f))).
apply compose1_1IsPR with (f := fun f : nat => cPairPi1 (cPairPi2 f)).
apply compose1_1IsPR.
apply cPairPi2IsPR.
apply cPairPi1IsPR.
apply wellFormedTermIsPR.
apply compose1_1IsPR with (f := fun f : nat => cPairPi2 (cPairPi2 f)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply wellFormedTermIsPR.
apply multIsPR.
apply switchIsPR.
Qed.

End Well_Formed_Formula.

End Well_Formed_Term.
