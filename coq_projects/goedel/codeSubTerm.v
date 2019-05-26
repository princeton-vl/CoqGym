Require Import primRec.
Require Import cPair.
Require Import Arith.
Require Import folProp.
Require Import code.
Require Import extEqualNat.
Require Vector.

Section Code_Substitute_Term.

Variable L : Language.
Variable codeF : Functions L -> nat.

Let Formula := Formula L.
Let Formulas := Formulas L.
Let System := System L.
Let Term := Term L.
Let Terms := Terms L.
Let var := var L.
Let apply := apply L.

Definition codeSubTermTerms : nat -> nat -> nat -> nat :=
  evalStrongRec 2
    (fun t recs v s : nat =>
     cPair
       (switchPR (cPairPi1 t)
          (cPair (cPairPi1 t) (cPairPi2 (codeNth (t - S (cPairPi2 t)) recs)))
          (switchPR (charFunction 2 beq_nat (cPairPi2 t) v) s t))
       (switchPR t
          (S
             (cPair (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs))
                (cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)))) 0)).

Definition codeSubTerm (t s v : nat) : nat :=
  cPairPi1 (codeSubTermTerms t s v).

Definition codeSubTerms (t s v : nat) : nat :=
  cPairPi2 (codeSubTermTerms t s v).

Lemma codeSubTermCorrect :
 forall (t : Term) (v : nat) (s : Term),
 codeSubTerm (codeTerm L codeF t) v (codeTerm L codeF s) =
 codeTerm L codeF (substituteTerm L t v s).
Proof.
set
 (g :=
  fun t0 recs v0 s0 : nat =>
  cPair
    (switchPR (cPairPi1 t0)
       (cPair (cPairPi1 t0) (cPairPi2 (codeNth (t0 - S (cPairPi2 t0)) recs)))
       (switchPR (charFunction 2 beq_nat (cPairPi2 t0) v0) s0 t0))
    (switchPR t0
       (S
          (cPair (cPairPi1 (codeNth (t0 - S (cPairPi1 (pred t0))) recs))
             (cPairPi2 (codeNth (t0 - S (cPairPi2 (pred t0))) recs)))) 0))
 in *.
intros.
elim t using
 Term_Terms_ind
  with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
           codeSubTerms (codeTerms L codeF n ts) v (codeTerm L codeF s) =
           codeTerms L codeF n (substituteTerms L n ts v s)); 
 intros.
simpl in |- *.
replace (codeTerm L codeF (fol.var L n)) with (cPair 0 n).
unfold codeSubTerm in |- *.
unfold codeSubTermTerms in |- *.
unfold evalStrongRec in |- *.
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
simpl in |- *.
induction (eq_nat_dec v n).
rewrite a.
rewrite <- beq_nat_refl.
simpl in |- *.
reflexivity.
rewrite beq_nat_not_refl.
simpl in |- *.
reflexivity.
auto.
reflexivity.
simpl in |- *.
transitivity
 (cPair (S (codeF f))
    (codeTerms L codeF (arity L (inr (Relations L) f))
       (substituteTerms L (arity L (inr (Relations L) f)) t0 v s))).
rewrite <- H.
replace (codeTerm L codeF (fol.apply L f t0)) with
 (cPair (S (codeF f)) (codeTerms L codeF (arity L (inr (Relations L) f)) t0)).
generalize (codeF f) (codeTerms L codeF (arity L (inr (Relations L) f)) t0).
clear H t0 f.
intros.
unfold codeSubTerm in |- *.
unfold codeSubTermTerms in |- *.
fold g in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc in |- *.
unfold evalOneParamList in |- *.
unfold evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
unfold pred in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
unfold g at 1 in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
assert
 (extEqual _
    (evalComposeFunc 2 1
       (Vector.cons _ (evalStrongRecHelp 2 g (cPair (S n) n0)) 0 (Vector.nil _))
       (fun b : nat => codeNth (cPair (S n) n0 - S n0) b))
    (evalStrongRec 2 g n0)).
apply (evalStrongRecHelp2 2).
apply cPairLt2.
simpl in H.
rewrite H.
clear H.
simpl in |- *.
reflexivity.
reflexivity.
reflexivity.
simpl in |- *.
unfold codeTerms in |- *.
unfold codeSubTerms in |- *.
unfold codeSubTermTerms in |- *.
unfold evalStrongRec in |- *.
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
reflexivity.
simpl in |- *.
transitivity
 (S
    (cPair (codeTerm L codeF (substituteTerm L t0 v s))
       (codeTerms L codeF n (substituteTerms L n t1 v s)))).
rewrite <- H.
rewrite <- H0.
replace (codeTerms L codeF (S n) (Tcons L n t0 t1)) with
 (S (cPair (codeTerm L codeF t0) (codeTerms L codeF n t1))).
generalize (codeTerm L codeF t0) (codeTerms L codeF n t1).
clear H0 t1 H t0 n.
intros.
unfold codeSubTerms at 1 in |- *.
unfold codeSubTermTerms in |- *.
fold g in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
unfold pred in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
unfold g at 1 in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
unfold pred in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
assert
 (extEqual _
    (evalComposeFunc 2 1
       (Vector.cons _ (evalStrongRecHelp 2 g (S (cPair n n0))) 0 (Vector.nil _))
       (fun b : nat => codeNth (S (cPair n n0) - S n) b))
    (evalStrongRec 2 g n)).
apply (evalStrongRecHelp2 2).
apply le_lt_n_Sm.
apply cPairLe1.
simpl in H.
rewrite H.
clear H.
assert
 (extEqual _
    (evalComposeFunc 2 1
       (Vector.cons _ (evalStrongRecHelp 2 g (S (cPair n n0))) 0 (Vector.nil _))
       (fun b : nat => codeNth (S (cPair n n0) - S n0) b))
    (evalStrongRec 2 g n0)).
apply (evalStrongRecHelp2 2).
apply le_lt_n_Sm.
apply cPairLe2.
simpl in H.
rewrite H.
clear H.
simpl in |- *.
reflexivity.
reflexivity.
reflexivity.
Qed.

Lemma codeSubTermsCorrect :
 forall (n : nat) (ts : Terms n) (v : nat) (s : Term),
 codeSubTerms (codeTerms L codeF n ts) v (codeTerm L codeF s) =
 codeTerms L codeF n (substituteTerms L n ts v s).
Proof.
set
 (g :=
  fun t0 recs v0 s0 : nat =>
  cPair
    (switchPR (cPairPi1 t0)
       (cPair (cPairPi1 t0) (cPairPi2 (codeNth (t0 - S (cPairPi2 t0)) recs)))
       (switchPR (charFunction 2 beq_nat (cPairPi2 t0) v0) s0 t0))
    (switchPR t0
       (S
          (cPair (cPairPi1 (codeNth (t0 - S (cPairPi1 (pred t0))) recs))
             (cPairPi2 (codeNth (t0 - S (cPairPi2 (pred t0))) recs)))) 0))
 in *.
intros.
induction ts as [| n t ts Hrects].
simpl in |- *.
unfold codeTerms in |- *.
unfold codeSubTerms in |- *.
unfold codeSubTermTerms in |- *.
unfold evalStrongRec in |- *.
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
reflexivity.
simpl in |- *.
transitivity
 (S
    (cPair (codeTerm L codeF (substituteTerm L t v s))
       (codeTerms L codeF n (substituteTerms L n ts v s)))).
rewrite <- Hrects.
rewrite <- codeSubTermCorrect.
replace (codeTerms L codeF (S n) (Tcons L n t ts)) with
 (S (cPair (codeTerm L codeF t) (codeTerms L codeF n ts))).
generalize (codeTerm L codeF t) (codeTerms L codeF n ts).
clear Hrects ts t n.
intros.
unfold codeSubTerms at 1 in |- *.
unfold codeSubTermTerms in |- *.
fold g in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
unfold pred in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
unfold g at 1 in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
unfold pred in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
assert
 (extEqual _
    (evalComposeFunc 2 1
       (Vector.cons _ (evalStrongRecHelp 2 g (S (cPair n n0))) 0 (Vector.nil _))
       (fun b : nat => codeNth (S (cPair n n0) - S n) b))
    (evalStrongRec 2 g n)).
apply (evalStrongRecHelp2 2).
apply le_lt_n_Sm.
apply cPairLe1.
simpl in H.
rewrite H.
clear H.
assert
 (extEqual _
    (evalComposeFunc 2 1
       (Vector.cons _ (evalStrongRecHelp 2 g (S (cPair n n0))) 0 (Vector.nil _))
       (fun b : nat => codeNth (S (cPair n n0) - S n0) b))
    (evalStrongRec 2 g n0)).
apply (evalStrongRecHelp2 2).
apply le_lt_n_Sm.
apply cPairLe2.
simpl in H.
rewrite H.
clear H.
simpl in |- *.
reflexivity.
reflexivity.
reflexivity.
Qed.

Lemma codeSubTermTermsIsPR : isPR 3 codeSubTermTerms.
Proof.
unfold codeSubTermTerms in |- *.
apply evalStrongRecIsPR.
apply
 compose4_2IsPR
  with
    (f1 := fun t recs v s : nat =>
           switchPR (cPairPi1 t)
             (cPair (cPairPi1 t)
                (cPairPi2 (codeNth (t - S (cPairPi2 t)) recs)))
             (switchPR (charFunction 2 beq_nat (cPairPi2 t) v) s t))
    (f2 := fun t recs v s : nat =>
           switchPR t
             (S
                (cPair (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs))
                   (cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)))) 0).
apply
 compose4_3IsPR
  with
    (f1 := fun t recs v s : nat => cPairPi1 t)
    (f2 := fun t recs v s : nat =>
           cPair (cPairPi1 t) (cPairPi2 (codeNth (t - S (cPairPi2 t)) recs)))
    (f3 := fun t recs v s : nat =>
           switchPR (charFunction 2 beq_nat (cPairPi2 t) v) s t).
apply filter1000IsPR with (g := cPairPi1).
apply cPairPi1IsPR.
apply
 filter1100IsPR
  with
    (g := fun t recs : nat =>
          cPair (cPairPi1 t) (cPairPi2 (codeNth (t - S (cPairPi2 t)) recs))).
apply
 compose2_2IsPR
  with
    (f := fun t recs : nat => cPairPi1 t)
    (g := fun t recs : nat => cPairPi2 (codeNth (t - S (cPairPi2 t)) recs)).
apply filter10IsPR with (g := cPairPi1).
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
apply cPairIsPR.
apply
 filter1011IsPR
  with
    (g := fun t v s : nat =>
          switchPR (charFunction 2 beq_nat (cPairPi2 t) v) s t).
apply
 compose3_3IsPR
  with
    (f1 := fun t v s : nat => charFunction 2 beq_nat (cPairPi2 t) v)
    (f2 := fun t v s : nat => s)
    (f3 := fun t v s : nat => t).
apply
 filter110IsPR
  with (g := fun t v : nat => charFunction 2 beq_nat (cPairPi2 t) v).
apply
 compose2_2IsPR
  with (f := fun t v : nat => cPairPi2 t) (g := fun t v : nat => v).
apply filter10IsPR.
apply cPairPi2IsPR.
apply pi2_2IsPR.
apply eqIsPR.
apply pi3_3IsPR.
apply pi1_3IsPR.
apply switchIsPR.
apply switchIsPR.
apply
 filter1100IsPR
  with
    (g := fun t recs : nat =>
          switchPR t
            (S
               (cPair (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs))
                  (cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)))) 0).
apply
 compose2_3IsPR
  with
    (f1 := fun t recs : nat => t)
    (f2 := fun t recs : nat =>
           S
             (cPair (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs))
                (cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs))))
    (f3 := fun t recs : nat => 0).
apply pi1_2IsPR.
apply
 compose2_1IsPR
  with
    (f := fun t recs : nat =>
          cPair (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs))
            (cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs))).
assert
 (forall g : nat -> nat,
  isPR 1 g ->
  isPR 2 (fun t recs : nat => g (codeNth (t - S (g (pred t))) recs))).
intros.
apply
 compose2_1IsPR
  with (f := fun t recs : nat => codeNth (t - S (g (pred t))) recs).
apply
 compose2_2IsPR
  with
    (f := fun t recs : nat => t - S (g (pred t)))
    (g := fun t recs : nat => recs).
apply filter10IsPR with (g := fun t : nat => t - S (g (pred t))).
apply
 compose1_2IsPR
  with (f := fun t : nat => t) (f' := fun t : nat => S (g (pred t))).
apply idIsPR.
apply compose1_1IsPR with (f := fun t : nat => g (pred t)).
apply compose1_1IsPR.
apply predIsPR.
auto.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
auto.
apply
 compose2_2IsPR
  with
    (f := fun t recs : nat =>
          cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs))
    (g := fun t recs : nat =>
          cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)).
apply H.
apply cPairPi1IsPR.
apply H.
apply cPairPi2IsPR.
apply cPairIsPR.
apply succIsPR.
exists (composeFunc 2 0 (PRnil _) zeroFunc).
simpl in |- *.
auto.
apply switchIsPR.
apply cPairIsPR.
Qed.

Lemma codeSubTermIsPR : isPR 3 codeSubTerm.
Proof.
unfold codeSubTerm in |- *.
apply compose3_1IsPR.
apply codeSubTermTermsIsPR.
apply cPairPi1IsPR.
Qed.

Lemma codeSubTermsIsPR : isPR 3 codeSubTerms.
Proof.
unfold codeSubTerms in |- *.
apply compose3_1IsPR.
apply codeSubTermTermsIsPR.
apply cPairPi2IsPR.
Qed.

End Code_Substitute_Term.