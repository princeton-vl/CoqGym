Require Import Arith.
Require Import fol.
Require Import folProof.
Require Import cPair.

Section Code_Term_Formula_Proof.

Variable L : Language.
Variable codeF : Functions L -> nat.
Variable codeR : Relations L -> nat.
Hypothesis codeFInj : forall f g : Functions L, codeF f = codeF g -> f = g.
Hypothesis codeRInj : forall R S : Relations L, codeR R = codeR S -> R = S.

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
Let Prf := Prf L.
Let SysPrf := SysPrf L.

Fixpoint codeTerm (t : Term) : nat :=
  match t with
  | fol.var n => cPair 0 n
  | fol.apply f ts => cPair (S (codeF f)) (codeTerms _ ts)
  end
 
 with codeTerms (n : nat) (ts : Terms n) {struct ts} : nat :=
  match ts with
  | Tnil => 0
  | Tcons n t ss => S (cPair (codeTerm t) (codeTerms n ss))
  end.

Lemma codeTermInj : forall t s : Term, codeTerm t = codeTerm s -> t = s.
Proof.
intro.
elim t using
 Term_Terms_ind
  with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
           forall ss : Terms n, codeTerms n ts = codeTerms n ss -> ts = ss).
intros.
destruct s.
simpl in H.
replace n with n0.
auto.
eapply cPairInj2.
symmetry  in |- *.
apply H.
simpl in H.
assert (0 = S (codeF f)).
eapply cPairInj1.
apply H.
discriminate H0.
intros.
destruct s.
simpl in H0.
assert (S (codeF f) = 0).
eapply cPairInj1.
apply H0.
discriminate H1.
simpl in H0.
assert (f = f0).
apply codeFInj.
apply eq_add_S.
eapply cPairInj1.
apply H0.
cut
 (cPair (S (codeF f)) (codeTerms (arity L (inr (Relations L) f)) t0) =
  cPair (S (codeF f0)) (codeTerms (arity L (inr (Relations L) f0)) t1)).
generalize t1.
rewrite <- H1.
clear H1 H0 t1.
intros.
rewrite (H t1).
reflexivity.
eapply cPairInj2.
apply H0.
apply H0.
intros.
rewrite <- nilTerms.
reflexivity.
intros.
induction (consTerms L n ss).
induction x as (a, b).
simpl in p.
rewrite <- p.
rewrite <- p in H1.
simpl in H1.
rewrite (H a).
rewrite (H0 b).
reflexivity.
eapply cPairInj2.
apply eq_add_S.
apply H1.
eapply cPairInj1.
apply eq_add_S.
apply H1.
Qed.

Lemma codeTermsInj :
 forall (n : nat) (ts ss : Terms n),
 codeTerms n ts = codeTerms n ss -> ts = ss.
Proof.
intros n ts.
induction ts as [| n t ts Hrects].
intros.
rewrite <- (nilTerms L ss).
reflexivity.
intros.
induction (consTerms L n ss).
induction x as (a, b).
simpl in p.
rewrite <- p.
rewrite <- p in H.
simpl in H.
rewrite (Hrects b).
rewrite (codeTermInj t a).
reflexivity.
eapply cPairInj1.
apply eq_add_S.
apply H.
eapply cPairInj2.
apply eq_add_S.
apply H.
Qed.

Fixpoint codeFormula (f : Formula) : nat :=
  match f with
  | fol.equal t1 t2 => cPair 0 (cPair (codeTerm t1) (codeTerm t2))
  | fol.impH f1 f2 => cPair 1 (cPair (codeFormula f1) (codeFormula f2))
  | fol.notH f1 => cPair 2 (codeFormula f1)
  | fol.forallH n f1 => cPair 3 (cPair n (codeFormula f1))
  | fol.atomic R ts => cPair (4+(codeR R)) (codeTerms _ ts)
  end.

Lemma codeFormulaInj :
 forall f g : Formula, codeFormula f = codeFormula g -> f = g.
Proof.
intro.
induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf]; intros;
 [ destruct g as [t1 t2| r t1| f f0| f| n f]
 | destruct g as [t0 t1| r0 t0| f f0| f| n f]
 | destruct g as [t t0| r t| f f2| f| n f]
 | destruct g as [t t0| r t| f0 f1| f0| n f0]
 | destruct g as [t t0| r t| f0 f1| f0| n0 f0] ];
 (simpl in H;
   try
    match goal with
    | h:(cPair ?X1 ?X2 = cPair ?X3 ?X4) |- _ =>
        elimtype False; cut (X1 = X3);
         [ discriminate | eapply cPairInj1; apply h ]
    end).
rewrite (codeTermInj t t1).
rewrite (codeTermInj t0 t2).
reflexivity.
eapply cPairInj2.
eapply cPairInj2.
apply H.
eapply cPairInj1.
eapply cPairInj2.
apply H.
assert (r = r0).
apply codeRInj.
do 4 apply eq_add_S.
eapply cPairInj1.
apply H.
cut
 (cPair (S (S (S (S (codeR r)))))
    (codeTerms (arity L (inl (Functions L) r)) t) =
  cPair (S (S (S (S (codeR r0)))))
    (codeTerms (arity L (inl (Functions L) r0)) t0)).
generalize t0.
rewrite <- H0.
clear H0 H t0.
intros.
rewrite (codeTermsInj _ t t0).
reflexivity.
eapply cPairInj2.
apply H.
apply H.
rewrite (Hrecf1 f).
rewrite (Hrecf0 f2).
reflexivity.
eapply cPairInj2.
eapply cPairInj2.
apply H.
eapply cPairInj1.
eapply cPairInj2.
apply H.
rewrite (Hrecf f0).
reflexivity.
eapply cPairInj2.
apply H.
rewrite (Hrecf f0).
replace n0 with n.
reflexivity.
eapply cPairInj1.
eapply cPairInj2.
apply H.
eapply cPairInj2.
eapply cPairInj2.
apply H.
Qed.

Fixpoint codePrf (Z : Formulas) (f : Formula) (prf : Prf Z f) {struct prf} :
 nat :=
  match prf with
  | AXM A => cPair 0 (codeFormula A)
  | MP Axm1 Axm2 A B rec1 rec2 =>
      cPair 1
        (cPair
           (cPair (cPair 1 (cPair (codeFormula A) (codeFormula B)))
              (codePrf _ _ rec1)) (cPair (codeFormula A) (codePrf _ _ rec2)))
  | GEN Axm A v _ rec =>
      cPair 2 (cPair v (cPair (codeFormula A) (codePrf _ _ rec)))
  | IMP1 A B => cPair 3 (cPair (codeFormula A) (codeFormula B))
  | IMP2 A B C =>
      cPair 4 (cPair (codeFormula A) (cPair (codeFormula B) (codeFormula C)))
  | CP A B => cPair 5 (cPair (codeFormula A) (codeFormula B))
  | FA1 A v t => cPair 6 (cPair (codeFormula A) (cPair v (codeTerm t)))
  | FA2 A v _ => cPair 7 (cPair (codeFormula A) v)
  | FA3 A B v => cPair 8 (cPair (codeFormula A) (cPair (codeFormula B) v))
  | EQ1 => cPair 9 0
  | EQ2 => cPair 10 0
  | EQ3 => cPair 11 0
  | EQ4 r => cPair 12 (codeR r)
  | EQ5 f => cPair 13 (codeF f)
  end.

Lemma codePrfInjAxm :
 forall (a b : Formula) (A B : Formulas) (p : Prf A a) (q : Prf B b),
 codePrf A a p = codePrf B b q -> A = B.
Proof.
intros a b A B p.
generalize B b.
clear B b.
induction p
 as
  [A|
   Axm1 Axm2 A B p1 Hrecp1 p0 Hrecp0|
   Axm A v n p Hrecp|
   A B|
   A B C|
   A B|
   A v t|
   A v n|
   A B v|
   |
   |
   |
   R|
   f]; intros;
 [ destruct q
    as
     [A0|
      Axm1 Axm2 A0 B p p0|
      Axm A0 v n p|
      A0 B|
      A0 B C|
      A0 B|
      A0 v t|
      A0 v n|
      A0 B v|
      |
      |
      |
      R|
      f]
 | destruct q
    as
     [A0|
      Axm0 Axm3 A0 B0 p p2|
      Axm A0 v n p|
      A0 B0|
      A0 B0 C|
      A0 B0|
      A0 v t|
      A0 v n|
      A0 B0 v|
      |
      |
      |
      R|
      f]
 | destruct q
    as
     [A0|
      Axm1 Axm2 A0 B p0 p1|
      Axm0 A0 v0 n0 p0|
      A0 B|
      A0 B C|
      A0 B|
      A0 v0 t|
      A0 v0 n0|
      A0 B v0|
      |
      |
      |
      R|
      f]
 | destruct q
    as
     [A0|
      Axm1 Axm2 A0 B0 p p0|
      Axm A0 v n p|
      A0 B0|
      A0 B0 C|
      A0 B0|
      A0 v t|
      A0 v n|
      A0 B0 v|
      |
      |
      |
      R|
      f]
 | destruct q
    as
     [A0|
      Axm1 Axm2 A0 B0 p p0|
      Axm A0 v n p|
      A0 B0|
      A0 B0 C0|
      A0 B0|
      A0 v t|
      A0 v n|
      A0 B0 v|
      |
      |
      |
      R|
      f]
 | destruct q
    as
     [A0|
      Axm1 Axm2 A0 B0 p p0|
      Axm A0 v n p|
      A0 B0|
      A0 B0 C|
      A0 B0|
      A0 v t|
      A0 v n|
      A0 B0 v|
      |
      |
      |
      R|
      f]
 | destruct q
    as
     [A0|
      Axm1 Axm2 A0 B p p0|
      Axm A0 v0 n p|
      A0 B|
      A0 B C|
      A0 B|
      A0 v0 t0|
      A0 v0 n|
      A0 B v0|
      |
      |
      |
      R|
      f]
 | destruct q
    as
     [A0|
      Axm1 Axm2 A0 B p p0|
      Axm A0 v0 n0 p|
      A0 B|
      A0 B C|
      A0 B|
      A0 v0 t|
      A0 v0 n0|
      A0 B v0|
      |
      |
      |
      R|
      f]
 | destruct q
    as
     [A0|
      Axm1 Axm2 A0 B0 p p0|
      Axm A0 v0 n p|
      A0 B0|
      A0 B0 C|
      A0 B0|
      A0 v0 t|
      A0 v0 n|
      A0 B0 v0|
      |
      |
      |
      R|
      f]
 | destruct q
    as
     [A|
      Axm1 Axm2 A B p p0|
      Axm A v n p|
      A B|
      A B C|
      A B|
      A v t|
      A v n|
      A B v|
      |
      |
      |
      R|
      f]
 | destruct q
    as
     [A|
      Axm1 Axm2 A B p p0|
      Axm A v n p|
      A B|
      A B C|
      A B|
      A v t|
      A v n|
      A B v|
      |
      |
      |
      R|
      f]
 | destruct q
    as
     [A|
      Axm1 Axm2 A B p p0|
      Axm A v n p|
      A B|
      A B C|
      A B|
      A v t|
      A v n|
      A B v|
      |
      |
      |
      R|
      f]
 | destruct q
    as
     [A|
      Axm1 Axm2 A B p p0|
      Axm A v n p|
      A B|
      A B C|
      A B|
      A v t|
      A v n|
      A B v|
      |
      |
      |
      R0|
      f]
 | destruct q
    as
     [A|
      Axm1 Axm2 A B p p0|
      Axm A v n p|
      A B|
      A B C|
      A B|
      A v t|
      A v n|
      A B v|
      |
      |
      |
      R|
      f0] ];
 (simpl in H;
   try
    match goal with
    | h:(cPair ?X1 ?X2 = cPair ?X3 ?X4) |- _ =>
        elimtype False; cut (X1 = X3);
         [ discriminate | eapply cPairInj1; apply h ]
    end); try reflexivity.
replace A0 with A.
reflexivity.
apply codeFormulaInj.
eapply cPairInj2.
apply H.
replace Axm0 with Axm1.
replace Axm3 with Axm2.
reflexivity.
eapply Hrecp0 with A0 p2.
do 3 eapply cPairInj2.
apply H.
eapply Hrecp1 with (fol.impH L A0 B0) p.
eapply cPairInj2.
eapply cPairInj1.
eapply cPairInj2.
apply H.
eapply Hrecp with A0 p0.
do 3 eapply cPairInj2.
apply H.
Qed.

Definition codeImp (a b : nat) := cPair 1 (cPair a b).

Lemma codeImpCorrect :
 forall a b : Formula,
 codeImp (codeFormula a) (codeFormula b) = codeFormula (impH a b).
Proof.
auto.
Qed.

Definition codeNot (a : nat) := cPair 2 a.

Lemma codeNotCorrect :
 forall a : Formula, codeNot (codeFormula a) = codeFormula (notH a).
Proof.
auto.
Qed.

Definition codeForall (n a : nat) := cPair 3 (cPair n a).

Lemma codeForallCorrect :
 forall (n : nat) (a : Formula),
 codeForall n (codeFormula a) = codeFormula (forallH n a).
Proof.
auto.
Qed.

Definition codeOr (a b : nat) := codeImp (codeNot a) b.

Lemma codeOrCorrect :
 forall a b : Formula,
 codeOr (codeFormula a) (codeFormula b) = codeFormula (orH a b).
Proof.
auto.
Qed.

Definition codeAnd (a b : nat) := codeNot (codeOr (codeNot a) (codeNot b)).

Lemma codeAndCorrect :
 forall a b : Formula,
 codeAnd (codeFormula a) (codeFormula b) = codeFormula (andH a b).
Proof.
auto.
Qed.

Definition codeIff (a b : nat) := codeAnd (codeImp a b) (codeImp b a).

Lemma codeIffCorrect :
 forall a b : Formula,
 codeIff (codeFormula a) (codeFormula b) = codeFormula (iffH a b).
Proof.
auto.
Qed.

End Code_Term_Formula_Proof.
