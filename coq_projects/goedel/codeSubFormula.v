Require Import primRec.
Require Import cPair.
Require Import Arith.
Require Import folProp.
Require Import code.
Require Import extEqualNat.
Require Vector.
Require Import codeSubTerm.
Require Import codeFreeVar.
Require Import Max.

Section Code_Substitute_Formula.

Variable L : Language.
Variable codeF : Functions L -> nat.
Variable codeR : Relations L -> nat.

Notation Formula := (Formula L) (only parsing).
Notation Formulas := (Formulas L) (only parsing).
Notation System := (System L) (only parsing).
Notation Term := (Term L) (only parsing).
Notation Terms := (Terms L) (only parsing).
Let var := var L.
Let apply := apply L.
Let codeFormula := codeFormula L codeF codeR.
Let codeTerm := codeTerm L codeF.

Definition cTriple (a b c : nat) : nat := cPair a (cPair b c).

Definition cTriplePi1 (n : nat) : nat := cPairPi1 n.

Definition cTriplePi2 (n : nat) : nat := cPairPi1 (cPairPi2 n).

Definition cTriplePi3 (n : nat) : nat := cPairPi2 (cPairPi2 n).

Lemma cTripleIsPR : isPR 3 cTriple.
Proof.
unfold cTriple in |- *.
apply
 compose3_2IsPR
  with
    (g := cPair)
    (f1 := fun a b c : nat => a)
    (f2 := fun a b c : nat => cPair b c).
apply pi1_3IsPR.
apply filter011IsPR with (g := fun b c : nat => cPair b c).
apply cPairIsPR.
apply cPairIsPR.
Qed.

Lemma cTriplePi1IsPR : isPR 1 cTriplePi1.
Proof.
apply cPairPi1IsPR.
Qed.

Lemma cTriplePi2IsPR : isPR 1 cTriplePi2.
Proof.
unfold cTriplePi2 in |- *.
apply compose1_1IsPR.
apply cPairPi2IsPR.
apply cPairPi1IsPR.
Qed.

Lemma cTriplePi3IsPR : isPR 1 cTriplePi3.
Proof.
unfold cTriplePi3 in |- *.
apply compose1_1IsPR; apply cPairPi2IsPR.
Qed.

Lemma cTripleProj1 : forall a b c : nat, cTriplePi1 (cTriple a b c) = a.
unfold cTriplePi1, cTriple in |- *.
intros.
apply cPairProjections1.
Qed.

Lemma cTripleProj2 : forall a b c : nat, cTriplePi2 (cTriple a b c) = b.
unfold cTriplePi2, cTriple in |- *.
intros.
rewrite cPairProjections2.
apply cPairProjections1.
Qed.

Lemma cTripleProj3 : forall a b c : nat, cTriplePi3 (cTriple a b c) = c.
unfold cTriplePi3, cTriple in |- *.
intros.
rewrite cPairProjections2.
apply cPairProjections2.
Qed.

Lemma cTripleProj :
 forall a : nat, cTriple (cTriplePi1 a) (cTriplePi2 a) (cTriplePi3 a) = a.
Proof.
unfold cTriple, cTriplePi1, cTriplePi2, cTriplePi3 in |- *.
intros.
repeat rewrite cPairProjections.
reflexivity.
Qed.

(*Trace has form
 ((v,s, formula_input), formula_output, [subTrace1], [subTrace2])*)

Definition codeNewVar (l : nat) : nat :=
  evalStrongRec 0
    (fun n Hrecs : nat =>
     switchPR n
       (max (S (cPairPi1 (pred n)))
          (codeNth (n - S (cPairPi2 (pred n))) Hrecs)) 0) l.

Lemma codeNewVarCorrect :
 forall l : list nat, codeNewVar (codeList l) = newVar l.
Proof.
intros.
unfold codeNewVar in |- *.
unfold newVar in |- *.
set
 (f :=
  fun n Hrecs : nat =>
  switchPR n
    (max (S (cPairPi1 (pred n))) (codeNth (n - S (cPairPi2 (pred n))) Hrecs))
    0) in *.
induction l as [| a l Hrecl].
simpl in |- *.
unfold evalStrongRec in |- *.
simpl in |- *.
rewrite cPairProjections1.
reflexivity.
unfold evalStrongRec in |- *.
unfold evalComposeFunc in |- *.
unfold evalOneParamList in |- *.
unfold evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold f at 1 in |- *.
rewrite evalStrongRecHelp1.
simpl in |- *.
repeat rewrite cPairProjections1.
rewrite <- Hrecl.
repeat rewrite cPairProjections2.
reflexivity.
simpl in |- *.
repeat rewrite cPairProjections2.
apply le_lt_n_Sm.
apply cPairLe2.
Qed.

Lemma codeNewVarIsPR : isPR 1 codeNewVar.
Proof.
unfold codeNewVar in |- *.
apply
 (evalStrongRecIsPR 0)
  with
    (f := fun n Hrecs : nat =>
          switchPR n
            (max (S (cPairPi1 (pred n)))
               (codeNth (n - S (cPairPi2 (pred n))) Hrecs)) 0).
apply
 compose2_3IsPR
  with
    (g := switchPR)
    (f1 := fun n Hrecs : nat => n)
    (f2 := fun n Hrecs : nat =>
           max (S (cPairPi1 (pred n)))
             (codeNth (n - S (cPairPi2 (pred n))) Hrecs))
    (f3 := fun n Hrecs : nat => 0).
apply pi1_2IsPR.
apply
 compose2_2IsPR
  with
    (h := max)
    (f := fun n Hrecs : nat => S (cPairPi1 (pred n)))
    (g := fun n Hrecs : nat => codeNth (n - S (cPairPi2 (pred n))) Hrecs).
apply filter10IsPR with (g := fun n : nat => S (cPairPi1 (pred n))).
apply compose1_1IsPR with (g := S) (f := fun n : nat => cPairPi1 (pred n)).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi1IsPR.
apply succIsPR.
apply
 compose2_2IsPR
  with
    (h := codeNth)
    (f := fun n Hrecs : nat => n - S (cPairPi2 (pred n)))
    (g := fun n Hrecs : nat => Hrecs).
apply filter10IsPR with (g := fun n : nat => n - S (cPairPi2 (pred n))).
apply
 compose1_2IsPR
  with
    (g := minus)
    (f := fun n : nat => n)
    (f' := fun n : nat => S (cPairPi2 (pred n))).
apply idIsPR.
apply compose1_1IsPR with (g := S) (f := fun n : nat => cPairPi2 (pred n)).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi2IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply maxIsPR.
apply filter10IsPR with (g := fun _ : nat => 0).
apply const1_NIsPR.
apply switchIsPR.
Qed.

Definition checkSubFormulaTrace : nat -> nat :=
  evalStrongRec 0
    (fun trace recs : nat =>
     let v := cTriplePi1 (cTriplePi1 trace) in
     let s := cTriplePi2 (cTriplePi1 trace) in
     let input := cTriplePi3 (cTriplePi1 trace) in
     let output := cTriplePi2 trace in
     let rest := cTriplePi3 trace in
     let type := cPairPi1 input in
     switchPR type
       (switchPR (pred type)
          (switchPR (pred (pred type))
             (switchPR (pred (pred (pred type)))
                (charFunction 2 beq_nat output
                   (cPair type (codeSubTerms (cPairPi2 input) v s)))
                (switchPR
                   (charFunction 2 beq_nat v (cPairPi1 (cPairPi2 input)))
                   (charFunction 2 beq_nat input output)
                   (switchPR
                      (codeIn (cPairPi1 (cPairPi2 input)) (codeFreeVarTerm s))
                      (let nv :=
                         codeNewVar
                           (S
                              (cPair v
                                 (codeApp (codeFreeVarTerm s)
                                    (codeFreeVarFormula
                                       (cPairPi2 (cPairPi2 input)))))) in
                       charFunction 0
                         (beq_nat output
                            (cPair 3 (cPair nv (cTriplePi2 (cPairPi2 rest)))) &&
                          (beq_nat (cTriple v s (cTriplePi2 (cPairPi1 rest)))
                             (cTriplePi1 (cPairPi2 rest)) &&
                           beq_nat
                             (cTriple (cPairPi1 (cPairPi2 input))
                                (cPair 0 nv) (cPairPi2 (cPairPi2 input)))
                             (cTriplePi1 (cPairPi1 rest)))) *
                       (codeNth (trace - S (cPairPi1 rest)) recs *
                        codeNth (trace - S (cPairPi2 rest)) recs))
                      (charFunction 0
                         (beq_nat output
                            (cPair 3
                               (cPair (cPairPi1 (cPairPi2 input))
                                  (cTriplePi2 rest))) &&
                          beq_nat (cTriple v s (cPairPi2 (cPairPi2 input)))
                            (cTriplePi1 rest)) *
                       codeNth (trace - S rest) recs))))
             (charFunction 0
                (beq_nat output (cPair 2 (cTriplePi2 rest)) &&
                 beq_nat (cTriple v s (cPairPi2 input)) (cTriplePi1 rest)) *
              codeNth (trace - S rest) recs))
          (charFunction 0
             (beq_nat output
                (cPair 1
                   (cPair (cTriplePi2 (cPairPi1 rest))
                      (cTriplePi2 (cPairPi2 rest)))) &&
              (beq_nat (cTriple v s (cPairPi1 (cPairPi2 input)))
                 (cTriplePi1 (cPairPi1 rest)) &&
               beq_nat (cTriple v s (cPairPi2 (cPairPi2 input)))
                 (cTriplePi1 (cPairPi2 rest)))) *
           (codeNth (trace - S (cPairPi1 rest)) recs *
            codeNth (trace - S (cPairPi2 rest)) recs)))
       (charFunction 2 beq_nat output
          (cPair 0
             (cPair (codeSubTerm (cPairPi1 (cPairPi2 input)) v s)
                (codeSubTerm (cPairPi2 (cPairPi2 input)) v s))))).

Definition makeTraceImp (f1 : fol.Formula L)
  (f1rec : nat * fol.Term L -> nat) (f2 : fol.Formula L)
  (f2rec : nat * fol.Term L -> nat) (p : nat * fol.Term L) : nat :=
  let v := fst p in
  let s := snd p in
  cTriple (cTriple v (codeTerm s) (codeFormula (impH L f1 f2)))
    (codeFormula (substituteFormula L (impH L f1 f2) v s))
    (cPair (f1rec p) (f2rec p)).

Definition makeTraceNot (f : fol.Formula L) (frec : nat * fol.Term L -> nat)
  (p : nat * fol.Term L) : nat :=
  let v := fst p in
  let s := snd p in
  cTriple (cTriple v (codeTerm s) (codeFormula (notH L f)))
    (codeFormula (substituteFormula L (notH L f) v s)) 
    (frec p).

Definition makeTraceForall (n : nat) (f : fol.Formula L)
  (rec : forall b : fol.Formula L,
         lt_depth L b (forallH L n f) -> nat * fol.Term L -> nat)
  (p : nat * fol.Term L) : nat.
intros.
set (v := fst p) in *.
set (s := snd p) in *.
induction (eq_nat_dec n v).
exact
 (cTriple (cTriple v (codeTerm s) (codeFormula (forallH L n f)))
    (codeFormula (substituteFormula L (forallH L n f) v s)) 0).
assert (lt_depth L f (forallH L v f)).
apply depthForall.
induction (In_dec eq_nat_dec n (freeVarTerm L s)).
set (nv := newVar (v :: freeVarTerm L s ++ freeVarFormula L f)) in *.
assert (lt_depth L (substituteFormula L f n (var nv)) (forallH L v f)).
apply eqDepth with f.
symmetry  in |- *.
apply subFormulaDepth.
apply H.
exact
 (cTriple (cTriple v (codeTerm s) (codeFormula (forallH L n f)))
    (codeFormula (substituteFormula L (forallH L n f) v s))
    (cPair (rec f H (n, var nv))
       (rec (substituteFormula L f n (var nv)) H0 p))).
exact
 (cTriple (cTriple v (codeTerm s) (codeFormula (forallH L n f)))
    (codeFormula (substituteFormula L (forallH L n f) v s)) 
    (rec f H p)).
Defined.

Definition makeTrace : fol.Formula L -> nat * fol.Term L -> nat :=
  Formula_depth_rec2 L (fun _ : fol.Formula L => nat * fol.Term L -> nat)
    (fun (t t0 : fol.Term L) (p : nat * fol.Term L) =>
     let v := fst p in
     let s := snd p in
     cTriple (cTriple v (codeTerm s) (codeFormula (equal L t t0)))
       (codeFormula (substituteFormula L (equal L t t0) v s)) 0)
    (fun (r : Relations L) t (p : nat * fol.Term L) =>
     let v := fst p in
     let s := snd p in
     cTriple (cTriple v (codeTerm s) (codeFormula (atomic L r t)))
       (codeFormula (substituteFormula L (atomic L r t) v s)) 0) makeTraceImp
    makeTraceNot makeTraceForall.

Lemma makeTraceImpNice :
 forall (f2 g : fol.Formula L) (z1 z2 : nat * fol.Term L -> nat),
 (forall q : nat * fol.Term L, z1 q = z2 q) ->
 forall z3 z4 : nat * fol.Term L -> nat,
 (forall q : nat * fol.Term L, z3 q = z4 q) ->
 forall q : nat * fol.Term L,
 makeTraceImp f2 z1 g z3 q = makeTraceImp f2 z2 g z4 q.
Proof.
intros.
unfold makeTraceImp in |- *.
rewrite H.
rewrite H0.
reflexivity.
Qed.

Lemma makeTraceNotNice :
 forall (f2 : fol.Formula L) (z1 z2 : nat * fol.Term L -> nat),
 (forall q : nat * fol.Term L, z1 q = z2 q) ->
 forall q : nat * fol.Term L, makeTraceNot f2 z1 q = makeTraceNot f2 z2 q.
Proof.
intros.
unfold makeTraceNot in |- *.
rewrite H.
reflexivity.
Qed.

Lemma makeTraceForallNice :
 forall (v0 : nat) (a : fol.Formula L)
   (z1
    z2 : forall b : fol.Formula L,
         lt_depth L b (forallH L v0 a) -> nat * fol.Term L -> nat),
 (forall (b : fol.Formula L) (q : lt_depth L b (forallH L v0 a))
    (r : nat * fol.Term L), z1 b q r = z2 b q r) ->
 forall q : nat * fol.Term L,
 makeTraceForall v0 a z1 q = makeTraceForall v0 a z2 q.
Proof.
intros.
unfold makeTraceForall in |- *.
repeat rewrite H.
reflexivity.
Qed.

Remark makeTrace1 :
 forall (f : fol.Formula L) (v : nat) (s : fol.Term L),
 cTriplePi1 (makeTrace f (v, s)) = cTriple v (codeTerm s) (codeFormula f).
Proof.
intros.
induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf];
 unfold makeTrace, makeTraceImp, makeTraceNot, Formula_depth_rec2,
  Formula_depth_rec in |- *; simpl in |- *;
 try (rewrite cTripleProj1; reflexivity).
unfold makeTraceForall in |- *.
induction (eq_nat_dec n (fst (v, s))); simpl in |- *.
rewrite cTripleProj1.
reflexivity.
induction (In_dec eq_nat_dec n (freeVarTerm L s)); simpl in |- *;
 rewrite cTripleProj1; reflexivity.
Qed.

Remark makeTrace2 :
 forall (f : fol.Formula L) (v : nat) (s : fol.Term L),
 cTriplePi2 (makeTrace f (v, s)) = codeFormula (substituteFormula L f v s).
Proof.
intros.
induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf];
 unfold makeTrace, makeTraceImp, makeTraceNot, Formula_depth_rec2,
  Formula_depth_rec in |- *; simpl in |- *;
 try (rewrite cTripleProj2; reflexivity).
unfold makeTraceForall in |- *.
induction (eq_nat_dec n (fst (v, s))); simpl in |- *.
rewrite cTripleProj2.
reflexivity.
induction (In_dec eq_nat_dec n (freeVarTerm L s)); simpl in |- *;
 rewrite cTripleProj2; reflexivity.
Qed.

Lemma makeTraceCorrect :
 forall (f : fol.Formula L) (v : nat) (s : fol.Term L),
 checkSubFormulaTrace (makeTrace f (v, s)) = 1.
Proof.
intro.
unfold checkSubFormulaTrace in |- *.
set
 (A :=
  fun trace recs : nat =>
  switchPR (cPairPi1 (cTriplePi3 (cTriplePi1 trace)))
    (switchPR (pred (cPairPi1 (cTriplePi3 (cTriplePi1 trace))))
       (switchPR (pred (pred (cPairPi1 (cTriplePi3 (cTriplePi1 trace)))))
          (switchPR
             (pred (pred (pred (cPairPi1 (cTriplePi3 (cTriplePi1 trace))))))
             (charFunction 2 beq_nat (cTriplePi2 trace)
                (cPair (cPairPi1 (cTriplePi3 (cTriplePi1 trace)))
                   (codeSubTerms (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))
                      (cTriplePi1 (cTriplePi1 trace))
                      (cTriplePi2 (cTriplePi1 trace)))))
             (switchPR
                (charFunction 2 beq_nat (cTriplePi1 (cTriplePi1 trace))
                   (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
                (charFunction 2 beq_nat (cTriplePi3 (cTriplePi1 trace))
                   (cTriplePi2 trace))
                (switchPR
                   (codeIn
                      (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                      (codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace))))
                   (charFunction 0
                      (beq_nat (cTriplePi2 trace)
                         (cPair 3
                            (cPair
                               (codeNewVar
                                  (S
                                     (cPair (cTriplePi1 (cTriplePi1 trace))
                                        (codeApp
                                           (codeFreeVarTerm
                                              (cTriplePi2 (cTriplePi1 trace)))
                                           (codeFreeVarFormula
                                              (cPairPi2
                                                 (cPairPi2
                                                  (cTriplePi3
                                                  (cTriplePi1 trace)))))))))
                               (cTriplePi2 (cPairPi2 (cTriplePi3 trace))))) &&
                       (beq_nat
                          (cTriple (cTriplePi1 (cTriplePi1 trace))
                             (cTriplePi2 (cTriplePi1 trace))
                             (cTriplePi2 (cPairPi1 (cTriplePi3 trace))))
                          (cTriplePi1 (cPairPi2 (cTriplePi3 trace))) &&
                        beq_nat
                          (cTriple
                             (cPairPi1
                                (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                             (cPair 0
                                (codeNewVar
                                   (S
                                      (cPair (cTriplePi1 (cTriplePi1 trace))
                                         (codeApp
                                            (codeFreeVarTerm
                                               (cTriplePi2 (cTriplePi1 trace)))
                                            (codeFreeVarFormula
                                               (cPairPi2
                                                  (cPairPi2
                                                  (cTriplePi3
                                                  (cTriplePi1 trace))))))))))
                             (cPairPi2
                                (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
                          (cTriplePi1 (cPairPi1 (cTriplePi3 trace))))) *
                    (codeNth (trace - S (cPairPi1 (cTriplePi3 trace))) recs *
                     codeNth (trace - S (cPairPi2 (cTriplePi3 trace))) recs))
                   (charFunction 0
                      (beq_nat (cTriplePi2 trace)
                         (cPair 3
                            (cPair
                               (cPairPi1
                                  (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                               (cTriplePi2 (cTriplePi3 trace)))) &&
                       beq_nat
                         (cTriple (cTriplePi1 (cTriplePi1 trace))
                            (cTriplePi2 (cTriplePi1 trace))
                            (cPairPi2
                               (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
                         (cTriplePi1 (cTriplePi3 trace))) *
                    codeNth (trace - S (cTriplePi3 trace)) recs))))
          (charFunction 0
             (beq_nat (cTriplePi2 trace)
                (cPair 2 (cTriplePi2 (cTriplePi3 trace))) &&
              beq_nat
                (cTriple (cTriplePi1 (cTriplePi1 trace))
                   (cTriplePi2 (cTriplePi1 trace))
                   (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                (cTriplePi1 (cTriplePi3 trace))) *
           codeNth (trace - S (cTriplePi3 trace)) recs))
       (charFunction 0
          (beq_nat (cTriplePi2 trace)
             (cPair 1
                (cPair (cTriplePi2 (cPairPi1 (cTriplePi3 trace)))
                   (cTriplePi2 (cPairPi2 (cTriplePi3 trace))))) &&
           (beq_nat
              (cTriple (cTriplePi1 (cTriplePi1 trace))
                 (cTriplePi2 (cTriplePi1 trace))
                 (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
              (cTriplePi1 (cPairPi1 (cTriplePi3 trace))) &&
            beq_nat
              (cTriple (cTriplePi1 (cTriplePi1 trace))
                 (cTriplePi2 (cTriplePi1 trace))
                 (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
              (cTriplePi1 (cPairPi2 (cTriplePi3 trace))))) *
        (codeNth (trace - S (cPairPi1 (cTriplePi3 trace))) recs *
         codeNth (trace - S (cPairPi2 (cTriplePi3 trace))) recs)))
    (charFunction 2 beq_nat (cTriplePi2 trace)
       (cPair 0
          (cPair
             (codeSubTerm
                (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                (cTriplePi1 (cTriplePi1 trace))
                (cTriplePi2 (cTriplePi1 trace)))
             (codeSubTerm
                (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                (cTriplePi1 (cTriplePi1 trace))
                (cTriplePi2 (cTriplePi1 trace))))))) 
 in *.
elim f using Formula_depth_ind2; intros.
unfold makeTrace in |- *.
unfold Formula_depth_rec2 in |- *.
unfold Formula_depth_rec in |- *.
simpl in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
rewrite cPairProjections1.
unfold A at 1 in |- *;
 repeat first
  [ rewrite cTripleProj1
  | rewrite cTripleProj2
  | rewrite cTripleProj3
  | rewrite cPairProjections1
  | rewrite cPairProjections2 ].
simpl in |- *.
unfold codeTerm in |- *.
repeat rewrite codeSubTermCorrect.
rewrite <- beq_nat_refl.
reflexivity.
unfold makeTrace in |- *.
unfold Formula_depth_rec2 in |- *.
unfold Formula_depth_rec in |- *.
simpl in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
rewrite cPairProjections1.
unfold A at 1 in |- *;
 repeat first
  [ rewrite cTripleProj1
  | rewrite cTripleProj2
  | rewrite cTripleProj3
  | rewrite cPairProjections1
  | rewrite cPairProjections2 ].
unfold codeTerm in |- *.
rewrite codeSubTermsCorrect.
simpl in |- *.
rewrite <- beq_nat_refl.
reflexivity.
replace (makeTrace (impH L f0 f1) (v, s)) with
 (cTriple (cTriple v (codeTerm s) (codeFormula (impH L f0 f1)))
    (codeFormula (substituteFormula L (impH L f0 f1) v s))
    (cPair (makeTrace f0 (v, s)) (makeTrace f1 (v, s)))).
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
rewrite cPairProjections1.
unfold A at 1 in |- *;
 repeat first
  [ rewrite cTripleProj1
  | rewrite cTripleProj2
  | rewrite cTripleProj3
  | rewrite cPairProjections1
  | rewrite cPairProjections2 ].
rewrite evalStrongRecHelp1 with (m := makeTrace f0 (v, s)).
rewrite evalStrongRecHelp1 with (m := makeTrace f1 (v, s)).
simpl in |- *.
repeat rewrite makeTrace1.
repeat rewrite makeTrace2.
rewrite subFormulaImp.
rewrite H.
rewrite H0.
simpl in |- *.
repeat rewrite <- beq_nat_refl.
reflexivity.
apply le_lt_trans with (cPair (makeTrace f0 (v, s)) (makeTrace f1 (v, s))).
apply cPairLe2.
unfold cTriple in |- *.
apply
 le_lt_trans
  with
    (cPair (codeFormula (substituteFormula L (impH L f0 f1) v s))
       (cPair (makeTrace f0 (v, s)) (makeTrace f1 (v, s)))).
apply cPairLe2.
apply
 lt_le_trans
  with
    (cPair 1
       (cPair (codeFormula (substituteFormula L (impH L f0 f1) v s))
          (cPair (makeTrace f0 (v, s)) (makeTrace f1 (v, s))))).
apply cPairLt2.
apply cPairLe3.
apply le_trans with (cPair 1 (cPair (codeFormula f0) (codeFormula f1))).
apply cPairLe1.
apply
 le_trans
  with
    (cPair (codeTerm s) (cPair 1 (cPair (codeFormula f0) (codeFormula f1)))).
apply cPairLe2.
apply cPairLe2.
apply le_n.
apply le_lt_trans with (cPair (makeTrace f0 (v, s)) (makeTrace f1 (v, s))).
apply cPairLe1.
unfold cTriple in |- *.
apply
 le_lt_trans
  with
    (cPair (codeFormula (substituteFormula L (impH L f0 f1) v s))
       (cPair (makeTrace f0 (v, s)) (makeTrace f1 (v, s)))).
apply cPairLe2.
apply
 lt_le_trans
  with
    (cPair 1
       (cPair (codeFormula (substituteFormula L (impH L f0 f1) v s))
          (cPair (makeTrace f0 (v, s)) (makeTrace f1 (v, s))))).
apply cPairLt2.
apply cPairLe3.
apply le_trans with (cPair 1 (cPair (codeFormula f0) (codeFormula f1))).
apply cPairLe1.
apply
 le_trans
  with
    (cPair (codeTerm s) (cPair 1 (cPair (codeFormula f0) (codeFormula f1)))).
apply cPairLe2.
apply cPairLe2.
apply le_n.
symmetry  in |- *.
unfold makeTrace in |- *.
rewrite
 (Formula_depth_rec2_imp L)
                            with
                            (Q := 
                              fun _ : fol.Formula L =>
                              (nat * fol.Term L)%type)
                           (P := fun _ : fol.Formula L => nat).
unfold makeTraceImp at 1 in |- *.
reflexivity.
apply makeTraceImpNice.
apply makeTraceNotNice.
apply makeTraceForallNice.
replace (makeTrace (notH L f0) (v, s)) with
 (cTriple (cTriple v (codeTerm s) (codeFormula (notH L f0)))
    (codeFormula (substituteFormula L (notH L f0) v s)) 
    (makeTrace f0 (v, s))).
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
rewrite cPairProjections1.
unfold A at 1 in |- *;
 repeat first
  [ rewrite cTripleProj1
  | rewrite cTripleProj2
  | rewrite cTripleProj3
  | rewrite cPairProjections1
  | rewrite cPairProjections2 ].
rewrite evalStrongRecHelp1 with (m := makeTrace f0 (v, s)).
simpl in |- *.
repeat rewrite makeTrace1.
repeat rewrite makeTrace2.
rewrite subFormulaNot.
rewrite H.
simpl in |- *.
repeat rewrite <- beq_nat_refl.
reflexivity.
apply
 le_lt_trans
  with
    (cPair (codeFormula (substituteFormula L (notH L f0) v s))
       (makeTrace f0 (v, s))).
apply cPairLe2.
apply
 lt_le_trans
  with
    (cPair 2
       (cPair (codeFormula (substituteFormula L (notH L f0) v s))
          (makeTrace f0 (v, s)))).
apply cPairLt2.
unfold cTriple in |- *.
apply cPairLe3.
apply le_trans with (cPair 2 (codeFormula f0)).
apply cPairLe1.
apply le_trans with (cPair (codeTerm s) (cPair 2 (codeFormula f0))).
apply cPairLe2.
apply cPairLe2.
apply le_n.
symmetry  in |- *.
unfold makeTrace in |- *.
rewrite
 (Formula_depth_rec2_not L)
                            with
                            (Q := 
                              fun _ : fol.Formula L =>
                              (nat * fol.Term L)%type)
                           (P := fun _ : fol.Formula L => nat).
unfold makeTraceNot at 1 in |- *.
reflexivity.
apply makeTraceImpNice.
apply makeTraceNotNice.
apply makeTraceForallNice.
replace (makeTrace (forallH L v a) (v0, s)) with
 (makeTraceForall v a (fun (b : fol.Formula L) _ => makeTrace b) (v0, s)).
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
rewrite cPairProjections1.
unfold makeTraceForall in |- *.
simpl in |- *.
rewrite (subFormulaForall L).
induction (eq_nat_dec v v0).
simpl in |- *.
unfold A at 1 in |- *;
 repeat first
  [ rewrite cTripleProj1
  | rewrite cTripleProj2
  | rewrite cTripleProj3
  | rewrite cPairProjections1
  | rewrite cPairProjections2 ].
replace (charFunction 2 beq_nat v0 v) with 1.
simpl in |- *.
rewrite <- beq_nat_refl.
reflexivity.
simpl in |- *.
rewrite a0.
rewrite <- beq_nat_refl.
reflexivity.
induction (In_dec eq_nat_dec v (freeVarTerm L s)).
simpl in |- *.
unfold A at 1 in |- *;
 repeat first
  [ rewrite cTripleProj1
  | rewrite cTripleProj2
  | rewrite cTripleProj3
  | rewrite cPairProjections1
  | rewrite cPairProjections2 ].
replace (charFunction 2 beq_nat v0 v) with 0.
replace (codeIn v (codeFreeVarTerm (codeTerm s))) with 1.
rewrite
 evalStrongRecHelp1
                    with
                    (m := 
                      makeTrace a
                        (v,
                        var
                          (newVar
                             (v0 :: freeVarTerm L s ++ freeVarFormula L a)))).
rewrite
 evalStrongRecHelp1
                    with
                    (m := 
                      makeTrace
                        (substituteFormula L a v
                           (var
                              (newVar
                                 (v0 :: freeVarTerm L s ++ freeVarFormula L a))))
                        (v0, s)).
replace
 (codeNewVar
    (S
       (cPair v0
          (codeApp (codeFreeVarTerm (codeTerm s))
             (codeFreeVarFormula (codeFormula a)))))) with
 (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a)).
simpl in |- *.
repeat rewrite makeTrace1.
repeat rewrite makeTrace2.
repeat rewrite <- beq_nat_refl.
repeat rewrite H.
reflexivity.
eapply eqDepth.
symmetry  in |- *.
apply subFormulaDepth.
apply depthForall.
apply depthForall.
unfold codeTerm in |- *.
rewrite codeFreeVarTermCorrect.
unfold codeFormula in |- *.
rewrite codeFreeVarFormulaCorrect.
rewrite codeAppCorrect.
rewrite <- codeNewVarCorrect.
reflexivity.
generalize
 (makeTrace
    (substituteFormula L a v
       (var (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a)))) 
    (v0, s))
 (makeTrace a (v, var (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a))))
 (cPair (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a))
    (codeFormula
       (substituteFormula L
          (substituteFormula L a v
             (fol.var L
                (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a)))) v0 s)))
 (cTriple v0 (codeTerm s) (cPair 3 (cPair v (codeFormula a)))).
intros.
apply le_lt_trans with (cPair n0 n).
apply cPairLe2.
unfold cTriple in |- *.
apply lt_le_trans with (cPair 3 (cPair n0 n)).
apply cPairLt2.
apply le_trans with (cPair (cPair 3 n1) (cPair n0 n)).
apply cPairLe3.
apply cPairLe1.
apply le_n.
apply cPairLe2.
generalize
 (makeTrace
    (substituteFormula L a v
       (var (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a)))) 
    (v0, s))
 (makeTrace a (v, var (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a))))
 (cPair (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a))
    (codeFormula
       (substituteFormula L
          (substituteFormula L a v
             (fol.var L
                (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a)))) v0 s)))
 (cTriple v0 (codeTerm s) (cPair 3 (cPair v (codeFormula a)))).
intros.
apply le_lt_trans with (cPair n0 n).
apply cPairLe1.
unfold cTriple in |- *.
apply lt_le_trans with (cPair 3 (cPair n0 n)).
apply cPairLt2.
apply le_trans with (cPair (cPair 3 n1) (cPair n0 n)).
apply cPairLe3.
apply cPairLe1.
apply le_n.
apply cPairLe2.
unfold codeTerm in |- *.
rewrite codeFreeVarTermCorrect.
rewrite codeInCorrect.
induction (In_dec eq_nat_dec v (freeVarTerm L s)).
reflexivity.
elim b0; assumption.
simpl in |- *.
rewrite beq_nat_not_refl.
reflexivity.
auto.
simpl in |- *.
unfold A at 1 in |- *;
 repeat first
  [ rewrite cTripleProj1
  | rewrite cTripleProj2
  | rewrite cTripleProj3
  | rewrite cPairProjections1
  | rewrite cPairProjections2 ].
replace (charFunction 2 beq_nat v0 v) with 0.
replace (codeIn v (codeFreeVarTerm (codeTerm s))) with 0.
rewrite evalStrongRecHelp1 with (m := makeTrace a (v0, s)).
simpl in |- *.
repeat rewrite makeTrace1.
repeat rewrite makeTrace2.
repeat rewrite <- beq_nat_refl.
repeat rewrite H.
reflexivity.
apply depthForall.
generalize (makeTrace a (v0, s))
 (cPair v (codeFormula (substituteFormula L a v0 s)))
 (cTriple v0 (codeTerm s) (cPair 3 (cPair v (codeFormula a)))).
intros.
unfold cTriple in |- *.
apply lt_le_trans with (cPair 3 n).
apply cPairLt2.
apply le_trans with (cPair (cPair 3 n0) n).
apply cPairLe3.
apply cPairLe1.
apply le_n.
apply cPairLe2.
unfold codeTerm in |- *.
rewrite codeFreeVarTermCorrect.
rewrite codeInCorrect.
induction (In_dec eq_nat_dec v (freeVarTerm L s)).
elim b0; assumption.
reflexivity.
simpl in |- *.
rewrite beq_nat_not_refl.
reflexivity.
auto.
unfold makeTrace in |- *.
rewrite
 (Formula_depth_rec2_forall L)
                               with
                               (Q := 
                                 fun _ : fol.Formula L =>
                                 (nat * fol.Term L)%type)
                              (P := fun _ : fol.Formula L => nat).
unfold makeTraceForall at 1 in |- *.
reflexivity.
apply makeTraceImpNice.
apply makeTraceNotNice.
apply makeTraceForallNice.
Qed.

Lemma checkTraceCorrect :
 forall (f : fol.Formula L) (v : nat) (s : fol.Term L) (n m : nat),
 checkSubFormulaTrace (cTriple (cTriple v (codeTerm s) (codeFormula f)) n m) <>
 0 -> codeFormula (substituteFormula L f v s) = n.
Proof.
assert (mult_lemma1 : forall a b : nat, a * b <> 0 -> a <> 0 /\ b <> 0).
assert (forall a b : nat, a = 0 \/ b = 0 -> a * b = 0).
intros.
induction H as [H| H].
rewrite H.
simpl in |- *.
reflexivity.
rewrite mult_comm.
rewrite H.
reflexivity.
intros.
split.
unfold not in |- *; intros.
elim H0.
apply H.
auto.
unfold not in |- *; intros.
elim H0.
apply H.
auto.
intro.
unfold checkSubFormulaTrace in |- *.
set
 (A :=
  fun trace recs : nat =>
  switchPR (cPairPi1 (cTriplePi3 (cTriplePi1 trace)))
    (switchPR (pred (cPairPi1 (cTriplePi3 (cTriplePi1 trace))))
       (switchPR (pred (pred (cPairPi1 (cTriplePi3 (cTriplePi1 trace)))))
          (switchPR
             (pred (pred (pred (cPairPi1 (cTriplePi3 (cTriplePi1 trace))))))
             (charFunction 2 beq_nat (cTriplePi2 trace)
                (cPair (cPairPi1 (cTriplePi3 (cTriplePi1 trace)))
                   (codeSubTerms (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))
                      (cTriplePi1 (cTriplePi1 trace))
                      (cTriplePi2 (cTriplePi1 trace)))))
             (switchPR
                (charFunction 2 beq_nat (cTriplePi1 (cTriplePi1 trace))
                   (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
                (charFunction 2 beq_nat (cTriplePi3 (cTriplePi1 trace))
                   (cTriplePi2 trace))
                (switchPR
                   (codeIn
                      (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                      (codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace))))
                   (charFunction 0
                      (beq_nat (cTriplePi2 trace)
                         (cPair 3
                            (cPair
                               (codeNewVar
                                  (S
                                     (cPair (cTriplePi1 (cTriplePi1 trace))
                                        (codeApp
                                           (codeFreeVarTerm
                                              (cTriplePi2 (cTriplePi1 trace)))
                                           (codeFreeVarFormula
                                              (cPairPi2
                                                 (cPairPi2
                                                  (cTriplePi3
                                                  (cTriplePi1 trace)))))))))
                               (cTriplePi2 (cPairPi2 (cTriplePi3 trace))))) &&
                       (beq_nat
                          (cTriple (cTriplePi1 (cTriplePi1 trace))
                             (cTriplePi2 (cTriplePi1 trace))
                             (cTriplePi2 (cPairPi1 (cTriplePi3 trace))))
                          (cTriplePi1 (cPairPi2 (cTriplePi3 trace))) &&
                        beq_nat
                          (cTriple
                             (cPairPi1
                                (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                             (cPair 0
                                (codeNewVar
                                   (S
                                      (cPair (cTriplePi1 (cTriplePi1 trace))
                                         (codeApp
                                            (codeFreeVarTerm
                                               (cTriplePi2 (cTriplePi1 trace)))
                                            (codeFreeVarFormula
                                               (cPairPi2
                                                  (cPairPi2
                                                  (cTriplePi3
                                                  (cTriplePi1 trace))))))))))
                             (cPairPi2
                                (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
                          (cTriplePi1 (cPairPi1 (cTriplePi3 trace))))) *
                    (codeNth (trace - S (cPairPi1 (cTriplePi3 trace))) recs *
                     codeNth (trace - S (cPairPi2 (cTriplePi3 trace))) recs))
                   (charFunction 0
                      (beq_nat (cTriplePi2 trace)
                         (cPair 3
                            (cPair
                               (cPairPi1
                                  (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                               (cTriplePi2 (cTriplePi3 trace)))) &&
                       beq_nat
                         (cTriple (cTriplePi1 (cTriplePi1 trace))
                            (cTriplePi2 (cTriplePi1 trace))
                            (cPairPi2
                               (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
                         (cTriplePi1 (cTriplePi3 trace))) *
                    codeNth (trace - S (cTriplePi3 trace)) recs))))
          (charFunction 0
             (beq_nat (cTriplePi2 trace)
                (cPair 2 (cTriplePi2 (cTriplePi3 trace))) &&
              beq_nat
                (cTriple (cTriplePi1 (cTriplePi1 trace))
                   (cTriplePi2 (cTriplePi1 trace))
                   (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                (cTriplePi1 (cTriplePi3 trace))) *
           codeNth (trace - S (cTriplePi3 trace)) recs))
       (charFunction 0
          (beq_nat (cTriplePi2 trace)
             (cPair 1
                (cPair (cTriplePi2 (cPairPi1 (cTriplePi3 trace)))
                   (cTriplePi2 (cPairPi2 (cTriplePi3 trace))))) &&
           (beq_nat
              (cTriple (cTriplePi1 (cTriplePi1 trace))
                 (cTriplePi2 (cTriplePi1 trace))
                 (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
              (cTriplePi1 (cPairPi1 (cTriplePi3 trace))) &&
            beq_nat
              (cTriple (cTriplePi1 (cTriplePi1 trace))
                 (cTriplePi2 (cTriplePi1 trace))
                 (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
              (cTriplePi1 (cPairPi2 (cTriplePi3 trace))))) *
        (codeNth (trace - S (cPairPi1 (cTriplePi3 trace))) recs *
         codeNth (trace - S (cPairPi2 (cTriplePi3 trace))) recs)))
    (charFunction 2 beq_nat (cTriplePi2 trace)
       (cPair 0
          (cPair
             (codeSubTerm
                (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                (cTriplePi1 (cTriplePi1 trace))
                (cTriplePi2 (cTriplePi1 trace)))
             (codeSubTerm
                (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                (cTriplePi1 (cTriplePi1 trace))
                (cTriplePi2 (cTriplePi1 trace))))))) 
 in *.
elim f using Formula_depth_ind2; intros.
unfold evalStrongRec in H.
unfold evalComposeFunc, evalOneParamList, evalList in H.
rewrite computeEvalStrongRecHelp in H.
unfold compose2 in H.
unfold evalComposeFunc, evalOneParamList, evalList in H.
simpl in H.
rewrite cPairProjections1 in H.
unfold A at 1 in H;
 repeat first
  [ rewrite cTripleProj1 in H
  | rewrite cTripleProj2 in H
  | rewrite cTripleProj3 in H
  | rewrite cPairProjections1 in H
  | rewrite cPairProjections2 in H ].
simpl in H.
unfold codeTerm in H.
repeat rewrite codeSubTermCorrect in H.
induction
 (eq_nat_dec n
    (cPair 0
       (cPair (code.codeTerm L codeF (substituteTerm L t v s))
          (code.codeTerm L codeF (substituteTerm L t0 v s))))).
rewrite a.
reflexivity.
rewrite beq_nat_not_refl in H.
elim H; reflexivity.
assumption.
unfold evalStrongRec in H.
unfold evalComposeFunc, evalOneParamList, evalList in H.
rewrite computeEvalStrongRecHelp in H.
unfold compose2 in H.
unfold evalComposeFunc, evalOneParamList, evalList in H.
simpl in H.
rewrite cPairProjections1 in H.
unfold A at 1 in H;
 repeat first
  [ rewrite cTripleProj1 in H
  | rewrite cTripleProj2 in H
  | rewrite cTripleProj3 in H
  | rewrite cPairProjections1 in H
  | rewrite cPairProjections2 in H ].
simpl in H.
unfold codeTerm in H.
repeat rewrite codeSubTermsCorrect in H.
induction
 (eq_nat_dec n
    (cPair (S (S (S (S (codeR r)))))
       (codeTerms L codeF (arity L (inl (Functions L) r))
          (substituteTerms L (arity L (inl (Functions L) r)) t v s)))).
rewrite a.
reflexivity.
rewrite beq_nat_not_refl in H.
elim H; reflexivity.
assumption.
unfold evalStrongRec in H1.
unfold evalComposeFunc, evalOneParamList, evalList in H1.
rewrite computeEvalStrongRecHelp in H1.
unfold compose2 in H1.
unfold evalComposeFunc, evalOneParamList, evalList in H1.
simpl in H1.
rewrite cPairProjections1 in H1.
unfold A at 1 in H1;
 repeat first
  [ rewrite cTripleProj1 in H1
  | rewrite cTripleProj2 in H1
  | rewrite cTripleProj3 in H1
  | rewrite cPairProjections1 in H1
  | rewrite cPairProjections2 in H1 ].
rewrite evalStrongRecHelp1 with (m := cPairPi1 m) in H1.
rewrite evalStrongRecHelp1 with (m := cPairPi2 m) in H1.
simpl in H1.
induction
 (eq_nat_dec n
    (cPair 1 (cPair (cTriplePi2 (cPairPi1 m)) (cTriplePi2 (cPairPi2 m))))).
rewrite <- a in H1.
rewrite <- beq_nat_refl in H1.
induction
 (eq_nat_dec (cTriple v (codeTerm s) (codeFormula f0))
    (cTriplePi1 (cPairPi1 m))).
rewrite <- a0 in H1.
rewrite <- beq_nat_refl in H1.
induction
 (eq_nat_dec (cTriple v (codeTerm s) (codeFormula f1))
    (cTriplePi1 (cPairPi2 m))).
rewrite <- a1 in H1.
rewrite <- beq_nat_refl in H1.
simpl in H1.
rewrite plus_comm in H1; simpl in H1.
decompose record (mult_lemma1 _ _ H1).
rewrite <- (cTripleProj (cPairPi1 m)) in H2.
rewrite <- (cTripleProj (cPairPi2 m)) in H3.
rewrite <- a0 in H2; clear a0.
rewrite <- a1 in H3; clear a1.
rewrite <- (H _ _ _ _ H2) in a.
rewrite <- (H0 _ _ _ _ H3) in a.
rewrite subFormulaImp.
rewrite a; reflexivity.
rewrite beq_nat_not_refl in H1.
elim H1; reflexivity.
assumption.
rewrite beq_nat_not_refl in H1.
elim H1; reflexivity.
assumption.
rewrite beq_nat_not_refl in H1.
elim H1; reflexivity.
assumption.
apply le_lt_trans with (cPair (cPairPi1 m) (cPairPi2 m)).
apply cPairLe2.
rewrite cPairProjections.
unfold cTriple in |- *.
apply lt_le_trans with (cPair 1 (cPair n m)).
apply le_lt_trans with (cPair n m).
apply cPairLe2.
apply cPairLt2.
apply cPairLe3.
apply le_trans with (cPair 1 (cPair (codeFormula f0) (codeFormula f1))).
apply cPairLe1.
apply
 le_trans
  with
    (cPair (codeTerm s) (cPair 1 (cPair (codeFormula f0) (codeFormula f1)))).
apply cPairLe2.
apply cPairLe2.
apply le_n.
apply le_lt_trans with (cPair (cPairPi1 m) (cPairPi2 m)).
apply cPairLe1.
rewrite cPairProjections.
unfold cTriple in |- *.
apply lt_le_trans with (cPair 1 (cPair n m)).
apply le_lt_trans with (cPair n m).
apply cPairLe2.
apply cPairLt2.
apply cPairLe3.
apply le_trans with (cPair 1 (cPair (codeFormula f0) (codeFormula f1))).
apply cPairLe1.
apply
 le_trans
  with
    (cPair (codeTerm s) (cPair 1 (cPair (codeFormula f0) (codeFormula f1)))).
apply cPairLe2.
apply cPairLe2.
apply le_n.
unfold evalStrongRec in H0.
unfold evalComposeFunc, evalOneParamList, evalList in H0.
rewrite computeEvalStrongRecHelp in H0.
unfold compose2 in H0.
unfold evalComposeFunc, evalOneParamList, evalList in H0.
simpl in H0.
rewrite cPairProjections1 in H0.
unfold A at 1 in H0;
 repeat first
  [ rewrite cTripleProj1 in H0
  | rewrite cTripleProj2 in H0
  | rewrite cTripleProj3 in H0
  | rewrite cPairProjections1 in H0
  | rewrite cPairProjections2 in H0 ].
rewrite evalStrongRecHelp1 with (m := m) in H0.
simpl in H0.
induction (eq_nat_dec n (cPair 2 (cTriplePi2 m))).
rewrite <- a in H0.
rewrite <- beq_nat_refl in H0.
induction
 (eq_nat_dec (cTriple v (codeTerm s) (codeFormula f0)) (cTriplePi1 m)).
rewrite <- a0 in H0.
rewrite <- beq_nat_refl in H0.
simpl in H0.
rewrite plus_comm in H0; simpl in H0.
rewrite <- (cTripleProj m) in H0.
rewrite <- a0 in H0; clear a0.
rewrite <- (H _ _ _ _ H0) in a.
rewrite subFormulaNot.
rewrite a; reflexivity.
rewrite beq_nat_not_refl in H0.
elim H0; reflexivity.
assumption.
rewrite beq_nat_not_refl in H0.
elim H0; reflexivity.
assumption.
unfold cTriple in |- *.
apply lt_le_trans with (cPair 2 (cPair n m)).
apply le_lt_trans with (cPair n m).
apply cPairLe2.
apply cPairLt2.
apply cPairLe3.
apply le_trans with (cPair 2 (codeFormula f0)).
apply cPairLe1.
apply le_trans with (cPair (codeTerm s) (cPair 2 (codeFormula f0))).
apply cPairLe2.
apply cPairLe2.
apply le_n.
rewrite subFormulaForall.
unfold evalStrongRec in H0.
unfold evalComposeFunc, evalOneParamList, evalList in H0.
rewrite computeEvalStrongRecHelp in H0.
unfold compose2 in H0.
unfold evalComposeFunc, evalOneParamList, evalList in H0.
simpl in H0.
rewrite cPairProjections1 in H0.
unfold A at 1 in H0;
 repeat first
  [ rewrite cTripleProj1 in H0
  | rewrite cTripleProj2 in H0
  | rewrite cTripleProj3 in H0
  | rewrite cPairProjections1 in H0
  | rewrite cPairProjections2 in H0 ].
induction (eq_nat_dec v v0).
rewrite a0 in H0.
assert (charFunction 2 beq_nat v0 v0 = 1).
simpl in |- *.
rewrite <- beq_nat_refl.
reflexivity.
rewrite H1 in H0.
induction (eq_nat_dec (codeFormula (forallH L v a)) n).
assumption.
assert (charFunction 2 beq_nat (cPair 3 (cPair v0 (codeFormula a))) n = 0).
unfold charFunction in |- *.
rewrite beq_nat_not_refl.
reflexivity.
rewrite <- a0.
apply b.
rewrite H2 in H0.
simpl in H0.
elim H0; reflexivity.
assert (charFunction 2 beq_nat v0 v = 0).
simpl in |- *.
rewrite beq_nat_not_refl.
reflexivity.
auto.
rewrite H1 in H0; clear H1.
unfold codeTerm in H0.
rewrite codeFreeVarTermCorrect in H0.
rewrite codeInCorrect in H0.
induction (In_dec eq_nat_dec v (freeVarTerm L s)).
rewrite evalStrongRecHelp1 with (m := cPairPi1 m) in H0.
rewrite evalStrongRecHelp1 with (m := cPairPi2 m) in H0.
simpl in H0.
induction
 (eq_nat_dec n
    (cPair 3
       (cPair
          (codeNewVar
             (S
                (cPair v0
                   (codeApp (codeList (freeVarTerm L s))
                      (codeFreeVarFormula (codeFormula a))))))
          (cTriplePi2 (cPairPi2 m))))).
rewrite <- a1 in H0.
rewrite <- beq_nat_refl in H0.
induction
 (eq_nat_dec (cTriple v0 (code.codeTerm L codeF s) (cTriplePi2 (cPairPi1 m)))
    (cTriplePi1 (cPairPi2 m))).
rewrite a2 in H0.
rewrite <- beq_nat_refl in H0.
induction
 (eq_nat_dec
    (cTriple v
       (cPair 0
          (codeNewVar
             (S
                (cPair v0
                   (codeApp (codeList (freeVarTerm L s))
                      (codeFreeVarFormula (codeFormula a)))))))
       (codeFormula a)) (cTriplePi1 (cPairPi1 m))).
rewrite a3 in H0.
rewrite <- beq_nat_refl in H0.
simpl in H0.
rewrite plus_comm in H0.
simpl in H0.
decompose record (mult_lemma1 _ _ H0).
rewrite <- (cTripleProj (cPairPi1 m)) in H1.
rewrite <- (cTripleProj (cPairPi2 m)) in H2.
rewrite <- a2 in H2; clear a2.
rewrite <- a3 in H1; clear a3.
assert (lt_depth L a (forallH L v a)).
apply depthForall.
assert
 (cPair 0
    (codeNewVar
       (S
          (cPair v0
             (codeApp (codeList (freeVarTerm L s))
                (codeFreeVarFormula (codeFormula a)))))) =
  codeTerm
    (var
       (codeNewVar
          (S
             (cPair v0
                (codeApp (codeList (freeVarTerm L s))
                   (codeFreeVarFormula (codeFormula a)))))))).
reflexivity.
rewrite H4 in H1.
rewrite <- (H _ H3 _ _ _ _ H1) in H2.
assert
 (lt_depth L
    (substituteFormula L a v
       (var
          (codeNewVar
             (S
                (cPair v0
                   (codeApp (codeList (freeVarTerm L s))
                      (codeFreeVarFormula (codeFormula a))))))))
    (forallH L v a)).
eapply eqDepth.
symmetry  in |- *.
apply subFormulaDepth.
apply depthForall.
rewrite <- (H _ H5 _ _ _ _ H2) in a1.
rewrite a1.
unfold codeFormula at 2 4 in |- *.
rewrite codeFreeVarFormulaCorrect.
rewrite codeAppCorrect.
replace (S (cPair v0 (codeList (freeVarTerm L s ++ freeVarFormula L a))))
 with (codeList (v0 :: freeVarTerm L s ++ freeVarFormula L a));
 [ idtac | reflexivity ].
rewrite codeNewVarCorrect.
reflexivity.
rewrite beq_nat_not_refl in H0.
elim H0.
reflexivity.
assumption.
rewrite beq_nat_not_refl in H0.
elim H0.
reflexivity.
assumption.
rewrite beq_nat_not_refl in H0.
elim H0.
reflexivity.
assumption.
apply le_lt_trans with (cPair (cPairPi1 m) (cPairPi2 m)).
apply cPairLe2.
rewrite cPairProjections.
unfold cTriple in |- *.
apply lt_le_trans with (cPair 3 (cPair n m)).
apply le_lt_trans with (cPair n m).
apply cPairLe2.
apply cPairLt2.
apply cPairLe3.
apply le_trans with (cPair 3 (cPair v (codeFormula a))).
apply cPairLe1.
apply
 le_trans
  with (cPair (code.codeTerm L codeF s) (cPair 3 (cPair v (codeFormula a)))).
apply cPairLe2.
apply cPairLe2.
apply le_n.
apply le_lt_trans with (cPair (cPairPi1 m) (cPairPi2 m)).
apply cPairLe1.
rewrite cPairProjections.
unfold cTriple in |- *.
apply lt_le_trans with (cPair 3 (cPair n m)).
apply le_lt_trans with (cPair n m).
apply cPairLe2.
apply cPairLt2.
apply cPairLe3.
apply le_trans with (cPair 3 (cPair v (codeFormula a))).
apply cPairLe1.
apply
 le_trans
  with (cPair (code.codeTerm L codeF s) (cPair 3 (cPair v (codeFormula a)))).
apply cPairLe2.
apply cPairLe2.
apply le_n.
rewrite evalStrongRecHelp1 with (m := m) in H0.
simpl in H0.
induction (eq_nat_dec n (cPair 3 (cPair v (cTriplePi2 m)))).
rewrite <- a0 in H0.
rewrite <- beq_nat_refl in H0.
induction
 (eq_nat_dec (cTriple v0 (code.codeTerm L codeF s) (codeFormula a))
    (cTriplePi1 m)).
rewrite <- a1 in H0.
rewrite <- beq_nat_refl in H0.
simpl in H0.
rewrite plus_comm in H0.
simpl in H0.
assert (lt_depth L a (forallH L v a)).
apply depthForall.
rewrite <- (cTripleProj m) in H0.
rewrite <- a1 in H0; clear a1.
rewrite <- (H _ H1 _ _ _ _ H0) in a0.
rewrite a0.
reflexivity.
rewrite beq_nat_not_refl in H0.
elim H0.
reflexivity.
assumption.
rewrite beq_nat_not_refl in H0.
elim H0.
reflexivity.
assumption.
unfold cTriple in |- *.
apply lt_le_trans with (cPair 3 (cPair n m)).
apply le_lt_trans with (cPair n m).
apply cPairLe2.
apply cPairLt2.
apply cPairLe3.
apply le_trans with (cPair 3 (cPair v (codeFormula a))).
apply cPairLe1.
apply
 le_trans
  with (cPair (code.codeTerm L codeF s) (cPair 3 (cPair v (codeFormula a)))).
apply cPairLe2.
apply cPairLe2.
apply le_n.
Qed.

Lemma switch5IsPR :
 forall (f1 f2 f3 f4 f5 : nat -> nat -> nat) (g : nat -> nat),
 isPR 2 f1 ->
 isPR 2 f2 ->
 isPR 2 f3 ->
 isPR 2 f4 ->
 isPR 2 f5 ->
 isPR 1 g ->
 isPR 2
   (fun n recs : nat =>
    switchPR (g n)
      (switchPR (pred (g n))
         (switchPR (pred (pred (g n)))
            (switchPR (pred (pred (pred (g n)))) (f1 n recs) (f2 n recs))
            (f3 n recs)) (f4 n recs)) (f5 n recs)).
Proof.
intros.
assert (isPR 1 (fun trace : nat => pred (g trace))).
apply compose1_1IsPR.
assumption.
apply predIsPR.
assert (isPR 1 (fun trace : nat => pred (pred (g trace)))).
apply compose1_1IsPR with (f := fun trace : nat => pred (g trace)).
assumption.
apply predIsPR.
assert (isPR 1 (fun trace : nat => pred (pred (pred (g trace))))).
apply compose1_1IsPR with (f := fun trace : nat => pred (pred (g trace))).
assumption.
apply predIsPR.
apply
 compose2_3IsPR
  with
    (f1 := fun trace recs : nat => g trace)
    (f2 := fun trace recs : nat =>
           switchPR (pred (g trace))
             (switchPR (pred (pred (g trace)))
                (switchPR (pred (pred (pred (g trace)))) 
                   (f1 trace recs) (f2 trace recs)) 
                (f3 trace recs)) (f4 trace recs))
    (f3 := f5).
apply filter10IsPR.
assumption.
apply
 compose2_3IsPR
  with
    (f1 := fun trace recs : nat => pred (g trace))
    (f2 := fun trace recs : nat =>
           switchPR (pred (pred (g trace)))
             (switchPR (pred (pred (pred (g trace)))) 
                (f1 trace recs) (f2 trace recs)) (f3 trace recs))
    (f3 := f4).
apply filter10IsPR with (g := fun trace : nat => pred (g trace)).
assumption.
apply
 compose2_3IsPR
  with
    (f1 := fun trace recs : nat => pred (pred (g trace)))
    (f2 := fun trace recs : nat =>
           switchPR (pred (pred (pred (g trace)))) 
             (f1 trace recs) (f2 trace recs))
    (f3 := f3).
apply filter10IsPR with (g := fun trace : nat => pred (pred (g trace))).
assumption.
apply
 compose2_3IsPR
  with
    (f1 := fun trace recs : nat => pred (pred (pred (g trace))))
    (f2 := f1)
    (f3 := f2).
apply
 filter10IsPR with (g := fun trace : nat => pred (pred (pred (g trace)))).
assumption.
assumption.
assumption.
apply switchIsPR.
assumption.
apply switchIsPR.
assumption.
apply switchIsPR.
assumption.
apply switchIsPR.
Qed.

Lemma checkTraceIsPR : isPR 1 checkSubFormulaTrace.
Proof.
unfold checkSubFormulaTrace in |- *.
assert (isPR 1 (fun trace : nat => cPairPi1 (cTriplePi3 (cTriplePi1 trace)))).
apply
 compose1_1IsPR
  with
    (g := cPairPi1)
    (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace)).
apply compose1_1IsPR.
apply cTriplePi1IsPR.
apply cTriplePi3IsPR.
apply cPairPi1IsPR.
apply evalStrongRecIsPR.
assert
 (forall (f1 f2 f3 f4 f5 : nat -> nat -> nat) (g : nat -> nat),
  isPR 2 f1 ->
  isPR 2 f2 ->
  isPR 2 f3 ->
  isPR 2 f4 ->
  isPR 2 f5 ->
  isPR 1 g ->
  isPR 2
    (fun trace recs : nat =>
     switchPR (g trace)
       (switchPR (pred (g trace))
          (switchPR (pred (pred (g trace)))
             (switchPR (pred (pred (pred (g trace)))) 
                (f1 trace recs) (f2 trace recs)) (f3 trace recs))
          (f4 trace recs)) (f5 trace recs))).
apply switch5IsPR.
assert (isPR 1 (fun trace : nat => cTriplePi1 (cTriplePi1 trace))).
apply compose1_1IsPR; apply cTriplePi1IsPR.
assert (isPR 1 (fun trace : nat => cTriplePi2 (cTriplePi1 trace))).
apply compose1_1IsPR.
apply cTriplePi1IsPR.
apply cTriplePi2IsPR.
assert (isPR 1 (fun trace : nat => cTriplePi3 (cTriplePi1 trace))).
apply compose1_1IsPR.
apply cTriplePi1IsPR.
apply cTriplePi3IsPR.
assert (isPR 1 (fun trace : nat => cPairPi1 (cTriplePi3 (cTriplePi1 trace)))).
apply
 compose1_1IsPR with (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace)).
assumption.
apply cPairPi1IsPR.
apply
 H0
  with
    (f1 := fun trace recs : nat =>
           charFunction 2 beq_nat (cTriplePi2 trace)
             (cPair (cPairPi1 (cTriplePi3 (cTriplePi1 trace)))
                (codeSubTerms (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))
                   (cTriplePi1 (cTriplePi1 trace))
                   (cTriplePi2 (cTriplePi1 trace)))))
    (f2 := fun trace recs : nat =>
           switchPR
             (charFunction 2 beq_nat (cTriplePi1 (cTriplePi1 trace))
                (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
             (charFunction 2 beq_nat (cTriplePi3 (cTriplePi1 trace))
                (cTriplePi2 trace))
             (switchPR
                (codeIn (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                   (codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace))))
                (charFunction 0
                   (beq_nat (cTriplePi2 trace)
                      (cPair 3
                         (cPair
                            (codeNewVar
                               (S
                                  (cPair (cTriplePi1 (cTriplePi1 trace))
                                     (codeApp
                                        (codeFreeVarTerm
                                           (cTriplePi2 (cTriplePi1 trace)))
                                        (codeFreeVarFormula
                                           (cPairPi2
                                              (cPairPi2
                                                 (cTriplePi3
                                                  (cTriplePi1 trace)))))))))
                            (cTriplePi2 (cPairPi2 (cTriplePi3 trace))))) &&
                    (beq_nat
                       (cTriple (cTriplePi1 (cTriplePi1 trace))
                          (cTriplePi2 (cTriplePi1 trace))
                          (cTriplePi2 (cPairPi1 (cTriplePi3 trace))))
                       (cTriplePi1 (cPairPi2 (cTriplePi3 trace))) &&
                     beq_nat
                       (cTriple
                          (cPairPi1
                             (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                          (cPair 0
                             (codeNewVar
                                (S
                                   (cPair (cTriplePi1 (cTriplePi1 trace))
                                      (codeApp
                                         (codeFreeVarTerm
                                            (cTriplePi2 (cTriplePi1 trace)))
                                         (codeFreeVarFormula
                                            (cPairPi2
                                               (cPairPi2
                                                  (cTriplePi3
                                                  (cTriplePi1 trace))))))))))
                          (cPairPi2
                             (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
                       (cTriplePi1 (cPairPi1 (cTriplePi3 trace))))) *
                 (codeNth (trace - S (cPairPi1 (cTriplePi3 trace))) recs *
                  codeNth (trace - S (cPairPi2 (cTriplePi3 trace))) recs))
                (charFunction 0
                   (beq_nat (cTriplePi2 trace)
                      (cPair 3
                         (cPair
                            (cPairPi1
                               (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                            (cTriplePi2 (cTriplePi3 trace)))) &&
                    beq_nat
                      (cTriple (cTriplePi1 (cTriplePi1 trace))
                         (cTriplePi2 (cTriplePi1 trace))
                         (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
                      (cTriplePi1 (cTriplePi3 trace))) *
                 codeNth (trace - S (cTriplePi3 trace)) recs)))
    (f3 := fun trace recs : nat =>
           charFunction 0
             (beq_nat (cTriplePi2 trace)
                (cPair 2 (cTriplePi2 (cTriplePi3 trace))) &&
              beq_nat
                (cTriple (cTriplePi1 (cTriplePi1 trace))
                   (cTriplePi2 (cTriplePi1 trace))
                   (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                (cTriplePi1 (cTriplePi3 trace))) *
           codeNth (trace - S (cTriplePi3 trace)) recs)
    (f4 := fun trace recs : nat =>
           charFunction 0
             (beq_nat (cTriplePi2 trace)
                (cPair 1
                   (cPair (cTriplePi2 (cPairPi1 (cTriplePi3 trace)))
                      (cTriplePi2 (cPairPi2 (cTriplePi3 trace))))) &&
              (beq_nat
                 (cTriple (cTriplePi1 (cTriplePi1 trace))
                    (cTriplePi2 (cTriplePi1 trace))
                    (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
                 (cTriplePi1 (cPairPi1 (cTriplePi3 trace))) &&
               beq_nat
                 (cTriple (cTriplePi1 (cTriplePi1 trace))
                    (cTriplePi2 (cTriplePi1 trace))
                    (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
                 (cTriplePi1 (cPairPi2 (cTriplePi3 trace))))) *
           (codeNth (trace - S (cPairPi1 (cTriplePi3 trace))) recs *
            codeNth (trace - S (cPairPi2 (cTriplePi3 trace))) recs))
    (f5 := fun trace recs : nat =>
           charFunction 2 beq_nat (cTriplePi2 trace)
             (cPair 0
                (cPair
                   (codeSubTerm
                      (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                      (cTriplePi1 (cTriplePi1 trace))
                      (cTriplePi2 (cTriplePi1 trace)))
                   (codeSubTerm
                      (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                      (cTriplePi1 (cTriplePi1 trace))
                      (cTriplePi2 (cTriplePi1 trace))))))
    (g := fun trace : nat => cPairPi1 (cTriplePi3 (cTriplePi1 trace))).
apply
 filter10IsPR
  with
    (g := fun trace : nat =>
          charFunction 2 beq_nat (cTriplePi2 trace)
            (cPair (cPairPi1 (cTriplePi3 (cTriplePi1 trace)))
               (codeSubTerms (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))
                  (cTriplePi1 (cTriplePi1 trace))
                  (cTriplePi2 (cTriplePi1 trace))))).
apply
 compose1_2IsPR
  with
    (g := charFunction 2 beq_nat)
    (f := fun trace : nat => cTriplePi2 trace)
    (f' := fun trace : nat =>
           cPair (cPairPi1 (cTriplePi3 (cTriplePi1 trace)))
             (codeSubTerms (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))
                (cTriplePi1 (cTriplePi1 trace))
                (cTriplePi2 (cTriplePi1 trace)))).
apply cTriplePi2IsPR.
apply
 compose1_2IsPR
  with
    (f := fun trace : nat => cPairPi1 (cTriplePi3 (cTriplePi1 trace)))
    (f' := fun trace : nat =>
           codeSubTerms (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))
             (cTriplePi1 (cTriplePi1 trace)) (cTriplePi2 (cTriplePi1 trace))).
assumption.
apply
 compose1_3IsPR
  with
    (f1 := fun trace : nat => cPairPi2 (cTriplePi3 (cTriplePi1 trace)))
    (f2 := fun trace : nat => cTriplePi1 (cTriplePi1 trace))
    (f3 := fun trace : nat => cTriplePi2 (cTriplePi1 trace)).
apply
 compose1_1IsPR with (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace)).
assumption.
apply cPairPi2IsPR.
assumption.
assumption.
apply codeSubTermsIsPR.
apply cPairIsPR.
apply eqIsPR.
apply
 compose2_3IsPR
  with
    (f1 := fun trace recs : nat =>
           charFunction 2 beq_nat (cTriplePi1 (cTriplePi1 trace))
             (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
    (f2 := fun trace recs : nat =>
           charFunction 2 beq_nat (cTriplePi3 (cTriplePi1 trace))
             (cTriplePi2 trace))
    (f3 := fun trace recs : nat =>
           switchPR
             (codeIn (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                (codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace))))
             (charFunction 0
                (beq_nat (cTriplePi2 trace)
                   (cPair 3
                      (cPair
                         (codeNewVar
                            (S
                               (cPair (cTriplePi1 (cTriplePi1 trace))
                                  (codeApp
                                     (codeFreeVarTerm
                                        (cTriplePi2 (cTriplePi1 trace)))
                                     (codeFreeVarFormula
                                        (cPairPi2
                                           (cPairPi2
                                              (cTriplePi3 (cTriplePi1 trace)))))))))
                         (cTriplePi2 (cPairPi2 (cTriplePi3 trace))))) &&
                 (beq_nat
                    (cTriple (cTriplePi1 (cTriplePi1 trace))
                       (cTriplePi2 (cTriplePi1 trace))
                       (cTriplePi2 (cPairPi1 (cTriplePi3 trace))))
                    (cTriplePi1 (cPairPi2 (cTriplePi3 trace))) &&
                  beq_nat
                    (cTriple
                       (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                       (cPair 0
                          (codeNewVar
                             (S
                                (cPair (cTriplePi1 (cTriplePi1 trace))
                                   (codeApp
                                      (codeFreeVarTerm
                                         (cTriplePi2 (cTriplePi1 trace)))
                                      (codeFreeVarFormula
                                         (cPairPi2
                                            (cPairPi2
                                               (cTriplePi3 (cTriplePi1 trace))))))))))
                       (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
                    (cTriplePi1 (cPairPi1 (cTriplePi3 trace))))) *
              (codeNth (trace - S (cPairPi1 (cTriplePi3 trace))) recs *
               codeNth (trace - S (cPairPi2 (cTriplePi3 trace))) recs))
             (charFunction 0
                (beq_nat (cTriplePi2 trace)
                   (cPair 3
                      (cPair
                         (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                         (cTriplePi2 (cTriplePi3 trace)))) &&
                 beq_nat
                   (cTriple (cTriplePi1 (cTriplePi1 trace))
                      (cTriplePi2 (cTriplePi1 trace))
                      (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
                   (cTriplePi1 (cTriplePi3 trace))) *
              codeNth (trace - S (cTriplePi3 trace)) recs)).
apply
 filter10IsPR
  with
    (g := fun trace : nat =>
          charFunction 2 beq_nat (cTriplePi1 (cTriplePi1 trace))
            (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))).
apply
 compose1_2IsPR
  with
    (g := charFunction 2 beq_nat)
    (f := fun trace : nat => cTriplePi1 (cTriplePi1 trace))
    (f' := fun trace : nat =>
           cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))).
assumption.
apply
 compose1_1IsPR
  with (f := fun trace : nat => cPairPi2 (cTriplePi3 (cTriplePi1 trace))).
apply
 compose1_1IsPR with (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace)).
assumption.
apply cPairPi2IsPR.
apply cPairPi1IsPR.
apply eqIsPR.
apply
 filter10IsPR
  with
    (g := fun trace : nat =>
          charFunction 2 beq_nat (cTriplePi3 (cTriplePi1 trace))
            (cTriplePi2 trace)).
apply
 compose1_2IsPR
  with
    (g := charFunction 2 beq_nat)
    (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace))
    (f' := cTriplePi2).
assumption.
apply cTriplePi2IsPR.
apply eqIsPR.
apply
 compose2_3IsPR
  with
    (f1 := fun trace recs : nat =>
           codeIn (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
             (codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace))))
    (f2 := fun trace recs : nat =>
           charFunction 0
             (beq_nat (cTriplePi2 trace)
                (cPair 3
                   (cPair
                      (codeNewVar
                         (S
                            (cPair (cTriplePi1 (cTriplePi1 trace))
                               (codeApp
                                  (codeFreeVarTerm
                                     (cTriplePi2 (cTriplePi1 trace)))
                                  (codeFreeVarFormula
                                     (cPairPi2
                                        (cPairPi2
                                           (cTriplePi3 (cTriplePi1 trace)))))))))
                      (cTriplePi2 (cPairPi2 (cTriplePi3 trace))))) &&
              (beq_nat
                 (cTriple (cTriplePi1 (cTriplePi1 trace))
                    (cTriplePi2 (cTriplePi1 trace))
                    (cTriplePi2 (cPairPi1 (cTriplePi3 trace))))
                 (cTriplePi1 (cPairPi2 (cTriplePi3 trace))) &&
               beq_nat
                 (cTriple
                    (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                    (cPair 0
                       (codeNewVar
                          (S
                             (cPair (cTriplePi1 (cTriplePi1 trace))
                                (codeApp
                                   (codeFreeVarTerm
                                      (cTriplePi2 (cTriplePi1 trace)))
                                   (codeFreeVarFormula
                                      (cPairPi2
                                         (cPairPi2
                                            (cTriplePi3 (cTriplePi1 trace))))))))))
                    (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
                 (cTriplePi1 (cPairPi1 (cTriplePi3 trace))))) *
           (codeNth (trace - S (cPairPi1 (cTriplePi3 trace))) recs *
            codeNth (trace - S (cPairPi2 (cTriplePi3 trace))) recs))
    (f3 := fun trace recs : nat =>
           charFunction 0
             (beq_nat (cTriplePi2 trace)
                (cPair 3
                   (cPair
                      (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                      (cTriplePi2 (cTriplePi3 trace)))) &&
              beq_nat
                (cTriple (cTriplePi1 (cTriplePi1 trace))
                   (cTriplePi2 (cTriplePi1 trace))
                   (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
                (cTriplePi1 (cTriplePi3 trace))) *
           codeNth (trace - S (cTriplePi3 trace)) recs).
apply
 filter10IsPR
  with
    (g := fun trace : nat =>
          codeIn (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
            (codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace)))).
apply
 compose1_2IsPR
  with
    (f := fun trace : nat =>
          cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
    (f' := fun trace : nat => codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace))).
apply
 compose1_1IsPR
  with (f := fun trace : nat => cPairPi2 (cTriplePi3 (cTriplePi1 trace))).
apply
 compose1_1IsPR with (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace)).
assumption.
apply cPairPi2IsPR.
apply cPairPi1IsPR.
apply
 compose1_1IsPR with (f := fun trace : nat => cTriplePi2 (cTriplePi1 trace)).
assumption.
apply codeFreeVarTermIsPR.
apply codeInIsPR.
assert
 (isPR 1
    (fun trace : nat =>
     codeNewVar
       (S
          (cPair (cTriplePi1 (cTriplePi1 trace))
             (codeApp (codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace)))
                (codeFreeVarFormula
                   (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))))))).
apply
 compose1_1IsPR
  with
    (f := fun trace : nat =>
          S
            (cPair (cTriplePi1 (cTriplePi1 trace))
               (codeApp (codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace)))
                  (codeFreeVarFormula
                     (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))))).
apply
 compose1_1IsPR
  with
    (f := fun trace : nat =>
          cPair (cTriplePi1 (cTriplePi1 trace))
            (codeApp (codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace)))
               (codeFreeVarFormula
                  (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))))).
apply
 compose1_2IsPR
  with
    (f := fun trace : nat => cTriplePi1 (cTriplePi1 trace))
    (f' := fun trace : nat =>
           codeApp (codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace)))
             (codeFreeVarFormula
                (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))).
assumption.
apply
 compose1_2IsPR
  with
    (f := fun trace : nat => codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace)))
    (f' := fun trace : nat =>
           codeFreeVarFormula
             (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))).
apply
 compose1_1IsPR with (f := fun trace : nat => cTriplePi2 (cTriplePi1 trace)).
assumption.
apply codeFreeVarTermIsPR.
apply
 compose1_1IsPR
  with
    (f := fun trace : nat =>
          cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))).
apply
 compose1_1IsPR
  with (f := fun trace : nat => cPairPi2 (cTriplePi3 (cTriplePi1 trace))).
apply
 compose1_1IsPR with (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace)).
assumption.
apply cPairPi2IsPR.
apply cPairPi2IsPR.
apply codeFreeVarFormulaIsPR.
apply codeAppIsPR.
apply cPairIsPR.
apply succIsPR.
apply codeNewVarIsPR.
apply
 compose2_2IsPR
  with
    (f := fun trace recs : nat =>
          charFunction 0
            (beq_nat (cTriplePi2 trace)
               (cPair 3
                  (cPair
                     (codeNewVar
                        (S
                           (cPair (cTriplePi1 (cTriplePi1 trace))
                              (codeApp
                                 (codeFreeVarTerm
                                    (cTriplePi2 (cTriplePi1 trace)))
                                 (codeFreeVarFormula
                                    (cPairPi2
                                       (cPairPi2
                                          (cTriplePi3 (cTriplePi1 trace)))))))))
                     (cTriplePi2 (cPairPi2 (cTriplePi3 trace))))) &&
             (beq_nat
                (cTriple (cTriplePi1 (cTriplePi1 trace))
                   (cTriplePi2 (cTriplePi1 trace))
                   (cTriplePi2 (cPairPi1 (cTriplePi3 trace))))
                (cTriplePi1 (cPairPi2 (cTriplePi3 trace))) &&
              beq_nat
                (cTriple
                   (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                   (cPair 0
                      (codeNewVar
                         (S
                            (cPair (cTriplePi1 (cTriplePi1 trace))
                               (codeApp
                                  (codeFreeVarTerm
                                     (cTriplePi2 (cTriplePi1 trace)))
                                  (codeFreeVarFormula
                                     (cPairPi2
                                        (cPairPi2
                                           (cTriplePi3 (cTriplePi1 trace))))))))))
                   (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
                (cTriplePi1 (cPairPi1 (cTriplePi3 trace))))))
    (g := fun trace recs : nat =>
          codeNth (trace - S (cPairPi1 (cTriplePi3 trace))) recs *
          codeNth (trace - S (cPairPi2 (cTriplePi3 trace))) recs).
apply
 filter10IsPR
  with
    (g := fun trace : nat =>
          charFunction 0
            (beq_nat (cTriplePi2 trace)
               (cPair 3
                  (cPair
                     (codeNewVar
                        (S
                           (cPair (cTriplePi1 (cTriplePi1 trace))
                              (codeApp
                                 (codeFreeVarTerm
                                    (cTriplePi2 (cTriplePi1 trace)))
                                 (codeFreeVarFormula
                                    (cPairPi2
                                       (cPairPi2
                                          (cTriplePi3 (cTriplePi1 trace)))))))))
                     (cTriplePi2 (cPairPi2 (cTriplePi3 trace))))) &&
             (beq_nat
                (cTriple (cTriplePi1 (cTriplePi1 trace))
                   (cTriplePi2 (cTriplePi1 trace))
                   (cTriplePi2 (cPairPi1 (cTriplePi3 trace))))
                (cTriplePi1 (cPairPi2 (cTriplePi3 trace))) &&
              beq_nat
                (cTriple
                   (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                   (cPair 0
                      (codeNewVar
                         (S
                            (cPair (cTriplePi1 (cTriplePi1 trace))
                               (codeApp
                                  (codeFreeVarTerm
                                     (cTriplePi2 (cTriplePi1 trace)))
                                  (codeFreeVarFormula
                                     (cPairPi2
                                        (cPairPi2
                                           (cTriplePi3 (cTriplePi1 trace))))))))))
                   (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
                (cTriplePi1 (cPairPi1 (cTriplePi3 trace)))))).
apply
 (andRelPR 1)
  with
    (R := fun trace : nat =>
          beq_nat (cTriplePi2 trace)
            (cPair 3
               (cPair
                  (codeNewVar
                     (S
                        (cPair (cTriplePi1 (cTriplePi1 trace))
                           (codeApp
                              (codeFreeVarTerm
                                 (cTriplePi2 (cTriplePi1 trace)))
                              (codeFreeVarFormula
                                 (cPairPi2
                                    (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))))))
                  (cTriplePi2 (cPairPi2 (cTriplePi3 trace))))))
    (R' := fun trace : nat =>
           beq_nat
             (cTriple (cTriplePi1 (cTriplePi1 trace))
                (cTriplePi2 (cTriplePi1 trace))
                (cTriplePi2 (cPairPi1 (cTriplePi3 trace))))
             (cTriplePi1 (cPairPi2 (cTriplePi3 trace))) &&
           beq_nat
             (cTriple (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                (cPair 0
                   (codeNewVar
                      (S
                         (cPair (cTriplePi1 (cTriplePi1 trace))
                            (codeApp
                               (codeFreeVarTerm
                                  (cTriplePi2 (cTriplePi1 trace)))
                               (codeFreeVarFormula
                                  (cPairPi2
                                     (cPairPi2
                                        (cTriplePi3 (cTriplePi1 trace))))))))))
                (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
             (cTriplePi1 (cPairPi1 (cTriplePi3 trace)))).
unfold isPRrel in |- *.
apply
 compose1_2IsPR
  with
    (g := charFunction 2 beq_nat)
    (f := fun trace : nat => cTriplePi2 trace)
    (f' := fun trace : nat =>
           cPair 3
             (cPair
                (codeNewVar
                   (S
                      (cPair (cTriplePi1 (cTriplePi1 trace))
                         (codeApp
                            (codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace)))
                            (codeFreeVarFormula
                               (cPairPi2
                                  (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))))))
                (cTriplePi2 (cPairPi2 (cTriplePi3 trace))))).
apply cTriplePi2IsPR.
apply
 compose1_2IsPR
  with
    (f := fun trace : nat => 3)
    (f' := fun trace : nat =>
           cPair
             (codeNewVar
                (S
                   (cPair (cTriplePi1 (cTriplePi1 trace))
                      (codeApp
                         (codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace)))
                         (codeFreeVarFormula
                            (cPairPi2
                               (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))))))
             (cTriplePi2 (cPairPi2 (cTriplePi3 trace)))).
apply const1_NIsPR.
apply
 compose1_2IsPR
  with
    (f := fun trace : nat =>
          codeNewVar
            (S
               (cPair (cTriplePi1 (cTriplePi1 trace))
                  (codeApp (codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace)))
                     (codeFreeVarFormula
                        (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))))))
    (f' := fun trace : nat => cTriplePi2 (cPairPi2 (cTriplePi3 trace))).
assumption.
apply
 compose1_1IsPR with (f := fun trace : nat => cPairPi2 (cTriplePi3 trace)).
apply compose1_1IsPR.
apply cTriplePi3IsPR.
apply cPairPi2IsPR.
apply cTriplePi2IsPR.
apply cPairIsPR.
apply cPairIsPR.
apply eqIsPR.
apply
 (andRelPR 1)
  with
    (R := fun trace : nat =>
          beq_nat
            (cTriple (cTriplePi1 (cTriplePi1 trace))
               (cTriplePi2 (cTriplePi1 trace))
               (cTriplePi2 (cPairPi1 (cTriplePi3 trace))))
            (cTriplePi1 (cPairPi2 (cTriplePi3 trace))))
    (R' := fun trace : nat =>
           beq_nat
             (cTriple (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                (cPair 0
                   (codeNewVar
                      (S
                         (cPair (cTriplePi1 (cTriplePi1 trace))
                            (codeApp
                               (codeFreeVarTerm
                                  (cTriplePi2 (cTriplePi1 trace)))
                               (codeFreeVarFormula
                                  (cPairPi2
                                     (cPairPi2
                                        (cTriplePi3 (cTriplePi1 trace))))))))))
                (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
             (cTriplePi1 (cPairPi1 (cTriplePi3 trace)))).
apply
 compose1_2IsPR
  with
    (g := charFunction 2 beq_nat)
    (f := fun trace : nat =>
          cTriple (cTriplePi1 (cTriplePi1 trace))
            (cTriplePi2 (cTriplePi1 trace))
            (cTriplePi2 (cPairPi1 (cTriplePi3 trace))))
    (f' := fun trace : nat => cTriplePi1 (cPairPi2 (cTriplePi3 trace))).
apply
 compose1_3IsPR
  with
    (f1 := fun trace : nat => cTriplePi1 (cTriplePi1 trace))
    (f2 := fun trace : nat => cTriplePi2 (cTriplePi1 trace))
    (f3 := fun trace : nat => cTriplePi2 (cPairPi1 (cTriplePi3 trace))).
assumption.
assumption.
apply
 compose1_1IsPR with (f := fun trace : nat => cPairPi1 (cTriplePi3 trace)).
apply compose1_1IsPR.
apply cTriplePi3IsPR.
apply cPairPi1IsPR.
apply cTriplePi2IsPR.
apply cTripleIsPR.
apply
 compose1_1IsPR with (f := fun trace : nat => cPairPi2 (cTriplePi3 trace)).
apply compose1_1IsPR.
apply cTriplePi3IsPR.
apply cPairPi2IsPR.
apply cTriplePi1IsPR.
apply eqIsPR.
apply
 compose1_2IsPR
  with
    (g := charFunction 2 beq_nat)
    (f := fun trace : nat =>
          cTriple (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
            (cPair 0
               (codeNewVar
                  (S
                     (cPair (cTriplePi1 (cTriplePi1 trace))
                        (codeApp
                           (codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace)))
                           (codeFreeVarFormula
                              (cPairPi2
                                 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))))))))
            (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
    (f' := fun trace : nat => cTriplePi1 (cPairPi1 (cTriplePi3 trace))).
apply
 compose1_3IsPR
  with
    (f1 := fun trace : nat =>
           cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
    (f2 := fun trace : nat =>
           cPair 0
             (codeNewVar
                (S
                   (cPair (cTriplePi1 (cTriplePi1 trace))
                      (codeApp
                         (codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace)))
                         (codeFreeVarFormula
                            (cPairPi2
                               (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))))))))
    (f3 := fun trace : nat =>
           cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))).
apply
 compose1_1IsPR
  with (f := fun trace : nat => cPairPi2 (cTriplePi3 (cTriplePi1 trace))).
apply
 compose1_1IsPR with (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace)).
assumption.
apply cPairPi2IsPR.
apply cPairPi1IsPR.
apply
 compose1_2IsPR
  with
    (f := fun trace : nat => 0)
    (f' := fun trace : nat =>
           codeNewVar
             (S
                (cPair (cTriplePi1 (cTriplePi1 trace))
                   (codeApp (codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace)))
                      (codeFreeVarFormula
                         (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))))))).
apply const1_NIsPR.
assumption.
apply cPairIsPR.
apply
 compose1_1IsPR
  with (f := fun trace : nat => cPairPi2 (cTriplePi3 (cTriplePi1 trace))).
apply
 compose1_1IsPR with (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace)).
assumption.
apply cPairPi2IsPR.
apply cPairPi2IsPR.
apply cTripleIsPR.
apply
 compose1_1IsPR with (f := fun trace : nat => cPairPi1 (cTriplePi3 trace)).
apply compose1_1IsPR. 
apply cTriplePi3IsPR.
apply cPairPi1IsPR.
apply cTriplePi1IsPR.
apply eqIsPR.
apply
 compose2_2IsPR
  with
    (f := fun trace recs : nat =>
          codeNth (trace - S (cPairPi1 (cTriplePi3 trace))) recs)
    (g := fun trace recs : nat =>
          codeNth (trace - S (cPairPi2 (cTriplePi3 trace))) recs).
apply
 compose2_2IsPR
  with
    (f := fun trace recs : nat => trace - S (cPairPi1 (cTriplePi3 trace)))
    (g := fun trace recs : nat => recs).
apply
 filter10IsPR
  with (g := fun trace : nat => trace - S (cPairPi1 (cTriplePi3 trace))).
apply
 compose1_2IsPR
  with
    (f := fun trace : nat => trace)
    (f' := fun trace : nat => S (cPairPi1 (cTriplePi3 trace))).
apply idIsPR.
apply
 compose1_1IsPR with (f := fun trace : nat => cPairPi1 (cTriplePi3 trace)).
apply compose1_1IsPR.
apply cTriplePi3IsPR.
apply cPairPi1IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply
 compose2_2IsPR
  with
    (f := fun trace recs : nat => trace - S (cPairPi2 (cTriplePi3 trace)))
    (g := fun trace recs : nat => recs).
apply
 filter10IsPR
  with (g := fun trace : nat => trace - S (cPairPi2 (cTriplePi3 trace))).
apply
 compose1_2IsPR
  with
    (f := fun trace : nat => trace)
    (f' := fun trace : nat => S (cPairPi2 (cTriplePi3 trace))).
apply idIsPR.
apply
 compose1_1IsPR with (f := fun trace : nat => cPairPi2 (cTriplePi3 trace)).
apply compose1_1IsPR.
apply cTriplePi3IsPR.
apply cPairPi2IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply multIsPR.
apply multIsPR.
apply
 compose2_2IsPR
  with
    (f := fun trace recs : nat =>
          charFunction 0
            (beq_nat (cTriplePi2 trace)
               (cPair 3
                  (cPair
                     (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                     (cTriplePi2 (cTriplePi3 trace)))) &&
             beq_nat
               (cTriple (cTriplePi1 (cTriplePi1 trace))
                  (cTriplePi2 (cTriplePi1 trace))
                  (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
               (cTriplePi1 (cTriplePi3 trace))))
    (g := fun trace recs : nat => codeNth (trace - S (cTriplePi3 trace)) recs).
apply
 filter10IsPR
  with
    (g := fun trace : nat =>
          charFunction 0
            (beq_nat (cTriplePi2 trace)
               (cPair 3
                  (cPair
                     (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                     (cTriplePi2 (cTriplePi3 trace)))) &&
             beq_nat
               (cTriple (cTriplePi1 (cTriplePi1 trace))
                  (cTriplePi2 (cTriplePi1 trace))
                  (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
               (cTriplePi1 (cTriplePi3 trace)))).
apply
 (andRelPR 1)
  with
    (R := fun trace : nat =>
          beq_nat (cTriplePi2 trace)
            (cPair 3
               (cPair (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                  (cTriplePi2 (cTriplePi3 trace)))))
    (R' := fun trace : nat =>
           beq_nat
             (cTriple (cTriplePi1 (cTriplePi1 trace))
                (cTriplePi2 (cTriplePi1 trace))
                (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
             (cTriplePi1 (cTriplePi3 trace))).
apply
 compose1_2IsPR
  with
    (g := charFunction 2 beq_nat)
    (f := cTriplePi2)
    (f' := fun trace : nat =>
           cPair 3
             (cPair (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                (cTriplePi2 (cTriplePi3 trace)))).
apply cTriplePi2IsPR.
apply
 compose1_2IsPR
  with
    (f := fun trace : nat => 3)
    (f' := fun trace : nat =>
           cPair (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
             (cTriplePi2 (cTriplePi3 trace))).
apply const1_NIsPR.
apply
 compose1_2IsPR
  with
    (f := fun trace : nat =>
          cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
    (f' := fun trace : nat => cTriplePi2 (cTriplePi3 trace)).
apply
 compose1_1IsPR
  with (f := fun trace : nat => cPairPi2 (cTriplePi3 (cTriplePi1 trace))).
apply
 compose1_1IsPR with (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace)).
assumption.
apply cPairPi2IsPR.
apply cPairPi1IsPR.
apply compose1_1IsPR.
apply cTriplePi3IsPR.
apply cTriplePi2IsPR.
apply cPairIsPR.
apply cPairIsPR.
apply eqIsPR.
apply
 compose1_2IsPR
  with
    (g := charFunction 2 beq_nat)
    (f := fun trace : nat =>
          cTriple (cTriplePi1 (cTriplePi1 trace))
            (cTriplePi2 (cTriplePi1 trace))
            (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
    (f' := fun trace : nat => cTriplePi1 (cTriplePi3 trace)).
apply
 compose1_3IsPR
  with
    (f1 := fun trace : nat => cTriplePi1 (cTriplePi1 trace))
    (f2 := fun trace : nat => cTriplePi2 (cTriplePi1 trace))
    (f3 := fun trace : nat =>
           cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))).
assumption.
assumption.
apply
 compose1_1IsPR
  with (f := fun trace : nat => cPairPi2 (cTriplePi3 (cTriplePi1 trace))).
apply
 compose1_1IsPR with (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace)).
assumption.
apply cPairPi2IsPR.
apply cPairPi2IsPR.
apply cTripleIsPR.
apply compose1_1IsPR.
apply cTriplePi3IsPR.
apply cTriplePi1IsPR.
apply eqIsPR.
apply
 compose2_2IsPR
  with
    (f := fun trace recs : nat => trace - S (cTriplePi3 trace))
    (g := fun trace recs : nat => recs).
apply
 filter10IsPR with (g := fun trace : nat => trace - S (cTriplePi3 trace)).
apply
 compose1_2IsPR
  with
    (f := fun trace : nat => trace)
    (f' := fun trace : nat => S (cTriplePi3 trace)).
apply idIsPR.
apply compose1_1IsPR.
apply cTriplePi3IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply multIsPR.
apply switchIsPR.
apply switchIsPR.
apply
 compose2_2IsPR
  with
    (f := fun trace recs : nat =>
          charFunction 0
            (beq_nat (cTriplePi2 trace)
               (cPair 2 (cTriplePi2 (cTriplePi3 trace))) &&
             beq_nat
               (cTriple (cTriplePi1 (cTriplePi1 trace))
                  (cTriplePi2 (cTriplePi1 trace))
                  (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
               (cTriplePi1 (cTriplePi3 trace))))
    (g := fun trace recs : nat => codeNth (trace - S (cTriplePi3 trace)) recs).
apply
 filter10IsPR
  with
    (g := fun trace : nat =>
          charFunction 0
            (beq_nat (cTriplePi2 trace)
               (cPair 2 (cTriplePi2 (cTriplePi3 trace))) &&
             beq_nat
               (cTriple (cTriplePi1 (cTriplePi1 trace))
                  (cTriplePi2 (cTriplePi1 trace))
                  (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
               (cTriplePi1 (cTriplePi3 trace)))).
apply
 (andRelPR 1)
  with
    (R := fun trace : nat =>
          beq_nat (cTriplePi2 trace)
            (cPair 2 (cTriplePi2 (cTriplePi3 trace))))
    (R' := fun trace : nat =>
           beq_nat
             (cTriple (cTriplePi1 (cTriplePi1 trace))
                (cTriplePi2 (cTriplePi1 trace))
                (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
             (cTriplePi1 (cTriplePi3 trace))).
apply
 compose1_2IsPR
  with
    (g := charFunction 2 beq_nat)
    (f := fun trace : nat => cTriplePi2 trace)
    (f' := fun trace : nat => cPair 2 (cTriplePi2 (cTriplePi3 trace))).
apply cTriplePi2IsPR.
apply
 compose1_2IsPR
  with
    (f := fun trace : nat => 2)
    (f' := fun trace : nat => cTriplePi2 (cTriplePi3 trace)).
apply const1_NIsPR.
apply compose1_1IsPR.
apply cTriplePi3IsPR.
apply cTriplePi2IsPR.
apply cPairIsPR.
apply eqIsPR.
apply
 compose1_2IsPR
  with
    (g := charFunction 2 beq_nat)
    (f := fun trace : nat =>
          cTriple (cTriplePi1 (cTriplePi1 trace))
            (cTriplePi2 (cTriplePi1 trace))
            (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
    (f' := fun trace : nat => cTriplePi1 (cTriplePi3 trace)).
apply
 compose1_3IsPR
  with
    (f1 := fun trace : nat => cTriplePi1 (cTriplePi1 trace))
    (f2 := fun trace : nat => cTriplePi2 (cTriplePi1 trace))
    (f3 := fun trace : nat => cPairPi2 (cTriplePi3 (cTriplePi1 trace))).
assumption.
assumption.
apply
 compose1_1IsPR with (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace)).
assumption.
apply cPairPi2IsPR.
apply cTripleIsPR.
apply compose1_1IsPR.
apply cTriplePi3IsPR.
apply cTriplePi1IsPR.
apply eqIsPR.
apply
 compose2_2IsPR
  with
    (f := fun trace recs : nat => trace - S (cTriplePi3 trace))
    (g := fun trace recs : nat => recs).
apply
 filter10IsPR with (g := fun trace : nat => trace - S (cTriplePi3 trace)).
apply
 compose1_2IsPR
  with
    (f := fun trace : nat => trace)
    (f' := fun trace : nat => S (cTriplePi3 trace)).
apply idIsPR.
apply compose1_1IsPR.
apply cTriplePi3IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply multIsPR.
apply
 compose2_2IsPR
  with
    (f := fun trace recs : nat =>
          charFunction 0
            (beq_nat (cTriplePi2 trace)
               (cPair 1
                  (cPair (cTriplePi2 (cPairPi1 (cTriplePi3 trace)))
                     (cTriplePi2 (cPairPi2 (cTriplePi3 trace))))) &&
             (beq_nat
                (cTriple (cTriplePi1 (cTriplePi1 trace))
                   (cTriplePi2 (cTriplePi1 trace))
                   (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
                (cTriplePi1 (cPairPi1 (cTriplePi3 trace))) &&
              beq_nat
                (cTriple (cTriplePi1 (cTriplePi1 trace))
                   (cTriplePi2 (cTriplePi1 trace))
                   (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
                (cTriplePi1 (cPairPi2 (cTriplePi3 trace))))))
    (g := fun trace recs : nat =>
          codeNth (trace - S (cPairPi1 (cTriplePi3 trace))) recs *
          codeNth (trace - S (cPairPi2 (cTriplePi3 trace))) recs).
apply
 filter10IsPR
  with
    (g := fun trace : nat =>
          charFunction 0
            (beq_nat (cTriplePi2 trace)
               (cPair 1
                  (cPair (cTriplePi2 (cPairPi1 (cTriplePi3 trace)))
                     (cTriplePi2 (cPairPi2 (cTriplePi3 trace))))) &&
             (beq_nat
                (cTriple (cTriplePi1 (cTriplePi1 trace))
                   (cTriplePi2 (cTriplePi1 trace))
                   (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
                (cTriplePi1 (cPairPi1 (cTriplePi3 trace))) &&
              beq_nat
                (cTriple (cTriplePi1 (cTriplePi1 trace))
                   (cTriplePi2 (cTriplePi1 trace))
                   (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
                (cTriplePi1 (cPairPi2 (cTriplePi3 trace)))))).
apply
 (andRelPR 1)
  with
    (R := fun trace : nat =>
          beq_nat (cTriplePi2 trace)
            (cPair 1
               (cPair (cTriplePi2 (cPairPi1 (cTriplePi3 trace)))
                  (cTriplePi2 (cPairPi2 (cTriplePi3 trace))))))
    (R' := fun trace : nat =>
           beq_nat
             (cTriple (cTriplePi1 (cTriplePi1 trace))
                (cTriplePi2 (cTriplePi1 trace))
                (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
             (cTriplePi1 (cPairPi1 (cTriplePi3 trace))) &&
           beq_nat
             (cTriple (cTriplePi1 (cTriplePi1 trace))
                (cTriplePi2 (cTriplePi1 trace))
                (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
             (cTriplePi1 (cPairPi2 (cTriplePi3 trace)))).
apply
 compose1_2IsPR
  with
    (g := charFunction 2 beq_nat)
    (f := fun trace : nat => cTriplePi2 trace)
    (f' := fun trace : nat =>
           cPair 1
             (cPair (cTriplePi2 (cPairPi1 (cTriplePi3 trace)))
                (cTriplePi2 (cPairPi2 (cTriplePi3 trace))))).
apply cTriplePi2IsPR.
apply
 compose1_2IsPR
  with
    (f := fun trace : nat => 1)
    (f' := fun trace : nat =>
           cPair (cTriplePi2 (cPairPi1 (cTriplePi3 trace)))
             (cTriplePi2 (cPairPi2 (cTriplePi3 trace)))).
apply const1_NIsPR.
apply
 compose1_2IsPR
  with
    (f := fun trace : nat => cTriplePi2 (cPairPi1 (cTriplePi3 trace)))
    (f' := fun trace : nat => cTriplePi2 (cPairPi2 (cTriplePi3 trace))).
apply
 compose1_1IsPR with (f := fun trace : nat => cPairPi1 (cTriplePi3 trace)).
apply compose1_1IsPR.
apply cTriplePi3IsPR.
apply cPairPi1IsPR.
apply cTriplePi2IsPR.
apply
 compose1_1IsPR with (f := fun trace : nat => cPairPi2 (cTriplePi3 trace)).
apply compose1_1IsPR.
apply cTriplePi3IsPR.
apply cPairPi2IsPR.
apply cTriplePi2IsPR.
apply cPairIsPR.
apply cPairIsPR.
apply eqIsPR.
apply
 (andRelPR 1)
  with
    (R := fun trace : nat =>
          beq_nat
            (cTriple (cTriplePi1 (cTriplePi1 trace))
               (cTriplePi2 (cTriplePi1 trace))
               (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
            (cTriplePi1 (cPairPi1 (cTriplePi3 trace))))
    (R' := fun trace : nat =>
           beq_nat
             (cTriple (cTriplePi1 (cTriplePi1 trace))
                (cTriplePi2 (cTriplePi1 trace))
                (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
             (cTriplePi1 (cPairPi2 (cTriplePi3 trace)))).
apply
 compose1_2IsPR
  with
    (g := charFunction 2 beq_nat)
    (f := fun trace : nat =>
          cTriple (cTriplePi1 (cTriplePi1 trace))
            (cTriplePi2 (cTriplePi1 trace))
            (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
    (f' := fun trace : nat => cTriplePi1 (cPairPi1 (cTriplePi3 trace))).
apply
 compose1_3IsPR
  with
    (f1 := fun trace : nat => cTriplePi1 (cTriplePi1 trace))
    (f2 := fun trace : nat => cTriplePi2 (cTriplePi1 trace))
    (f3 := fun trace : nat =>
           cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))).
assumption.
assumption.
apply
 compose1_1IsPR
  with (f := fun trace : nat => cPairPi2 (cTriplePi3 (cTriplePi1 trace))).
apply
 compose1_1IsPR with (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace)).
assumption.
apply cPairPi2IsPR.
apply cPairPi1IsPR.
apply cTripleIsPR.
apply
 compose1_1IsPR with (f := fun trace : nat => cPairPi1 (cTriplePi3 trace)).
apply compose1_1IsPR.
apply cTriplePi3IsPR.
apply cPairPi1IsPR.
apply cTriplePi1IsPR.
apply eqIsPR.
apply
 compose1_2IsPR
  with
    (g := charFunction 2 beq_nat)
    (f := fun trace : nat =>
          cTriple (cTriplePi1 (cTriplePi1 trace))
            (cTriplePi2 (cTriplePi1 trace))
            (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))))
    (f' := fun trace : nat => cTriplePi1 (cPairPi2 (cTriplePi3 trace))).
apply
 compose1_3IsPR
  with
    (f1 := fun trace : nat => cTriplePi1 (cTriplePi1 trace))
    (f2 := fun trace : nat => cTriplePi2 (cTriplePi1 trace))
    (f3 := fun trace : nat =>
           cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace)))).
assumption.
assumption.
apply
 compose1_1IsPR
  with (f := fun trace : nat => cPairPi2 (cTriplePi3 (cTriplePi1 trace))).
apply
 compose1_1IsPR with (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace)).
assumption.
apply cPairPi2IsPR.
apply cPairPi2IsPR.
apply cTripleIsPR.
apply
 compose1_1IsPR with (f := fun trace : nat => cPairPi2 (cTriplePi3 trace)).
apply compose1_1IsPR.
apply cTriplePi3IsPR.
apply cPairPi2IsPR.
apply cTriplePi1IsPR.
apply eqIsPR.
apply
 compose2_2IsPR
  with
    (f := fun trace recs : nat =>
          codeNth (trace - S (cPairPi1 (cTriplePi3 trace))) recs)
    (g := fun trace recs : nat =>
          codeNth (trace - S (cPairPi2 (cTriplePi3 trace))) recs).
apply
 compose2_2IsPR
  with
    (f := fun trace recs : nat => trace - S (cPairPi1 (cTriplePi3 trace)))
    (g := fun trace recs : nat => recs).
apply
 filter10IsPR
  with (g := fun trace : nat => trace - S (cPairPi1 (cTriplePi3 trace))).
apply
 compose1_2IsPR
  with
    (f := fun trace : nat => trace)
    (f' := fun trace : nat => S (cPairPi1 (cTriplePi3 trace))).
apply idIsPR.
apply
 compose1_1IsPR with (f := fun trace : nat => cPairPi1 (cTriplePi3 trace)).
apply compose1_1IsPR.
apply cTriplePi3IsPR.
apply cPairPi1IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply
 compose2_2IsPR
  with
    (f := fun trace recs : nat => trace - S (cPairPi2 (cTriplePi3 trace)))
    (g := fun trace recs : nat => recs).
apply
 filter10IsPR
  with (g := fun trace : nat => trace - S (cPairPi2 (cTriplePi3 trace))).
apply
 compose1_2IsPR
  with
    (f := fun trace : nat => trace)
    (f' := fun trace : nat => S (cPairPi2 (cTriplePi3 trace))).
apply idIsPR.
apply
 compose1_1IsPR with (f := fun trace : nat => cPairPi2 (cTriplePi3 trace)).
apply compose1_1IsPR.
apply cTriplePi3IsPR.
apply cPairPi2IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply multIsPR.
apply multIsPR.
apply
 filter10IsPR
  with
    (g := fun trace : nat =>
          charFunction 2 beq_nat (cTriplePi2 trace)
            (cPair 0
               (cPair
                  (codeSubTerm
                     (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                     (cTriplePi1 (cTriplePi1 trace))
                     (cTriplePi2 (cTriplePi1 trace)))
                  (codeSubTerm
                     (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                     (cTriplePi1 (cTriplePi1 trace))
                     (cTriplePi2 (cTriplePi1 trace)))))).
apply
 compose1_2IsPR
  with
    (f := fun trace : nat => cTriplePi2 trace)
    (f' := fun trace : nat =>
           cPair 0
             (cPair
                (codeSubTerm
                   (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                   (cTriplePi1 (cTriplePi1 trace))
                   (cTriplePi2 (cTriplePi1 trace)))
                (codeSubTerm
                   (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                   (cTriplePi1 (cTriplePi1 trace))
                   (cTriplePi2 (cTriplePi1 trace))))).
apply cTriplePi2IsPR.
apply
 compose1_2IsPR
  with
    (f := fun trace : nat => 0)
    (f' := fun trace : nat =>
           cPair
             (codeSubTerm
                (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                (cTriplePi1 (cTriplePi1 trace))
                (cTriplePi2 (cTriplePi1 trace)))
             (codeSubTerm
                (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
                (cTriplePi1 (cTriplePi1 trace))
                (cTriplePi2 (cTriplePi1 trace)))).
apply const1_NIsPR.
apply
 compose1_2IsPR
  with
    (f := fun trace : nat =>
          codeSubTerm (cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
            (cTriplePi1 (cTriplePi1 trace)) (cTriplePi2 (cTriplePi1 trace)))
    (f' := fun trace : nat =>
           codeSubTerm (cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
             (cTriplePi1 (cTriplePi1 trace)) (cTriplePi2 (cTriplePi1 trace))).
apply
 compose1_3IsPR
  with
    (f1 := fun trace : nat =>
           cPairPi1 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
    (f2 := fun trace : nat => cTriplePi1 (cTriplePi1 trace))
    (f3 := fun trace : nat => cTriplePi2 (cTriplePi1 trace)).
apply
 compose1_1IsPR
  with (f := fun trace : nat => cPairPi2 (cTriplePi3 (cTriplePi1 trace))).
apply
 compose1_1IsPR with (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace)).
assumption.
apply cPairPi2IsPR.
apply cPairPi1IsPR.
assumption.
assumption.
apply codeSubTermIsPR.
apply
 compose1_3IsPR
  with
    (f1 := fun trace : nat =>
           cPairPi2 (cPairPi2 (cTriplePi3 (cTriplePi1 trace))))
    (f2 := fun trace : nat => cTriplePi1 (cTriplePi1 trace))
    (f3 := fun trace : nat => cTriplePi2 (cTriplePi1 trace)).
apply
 compose1_1IsPR
  with (f := fun trace : nat => cPairPi2 (cTriplePi3 (cTriplePi1 trace))).
apply
 compose1_1IsPR with (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace)).
assumption.
apply cPairPi2IsPR.
apply cPairPi2IsPR.
assumption.
assumption.
apply codeSubTermIsPR.
apply cPairIsPR.
apply cPairIsPR.
apply eqIsPR.
assumption.
Qed.

Definition ReplaceTermTermsTerm : nat -> nat -> nat :=
  evalStrongRec 1
    (fun t recs s : nat =>
     cPair
       (switchPR (cPairPi1 t)
          (cPair (cPairPi1 t) (cPairPi2 (codeNth (t - S (cPairPi2 t)) recs)))
          (cPair 0 s))
       (switchPR t
          (S
             (cPair (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs))
                (cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)))) 0)).

Remark ReplaceTermTermsTermIsPR : isPR 2 ReplaceTermTermsTerm.
Proof.
unfold ReplaceTermTermsTerm in |- *.
apply evalStrongRecIsPR.
apply
 compose3_2IsPR
  with
    (f1 := fun t recs s : nat =>
           switchPR (cPairPi1 t)
             (cPair (cPairPi1 t)
                (cPairPi2 (codeNth (t - S (cPairPi2 t)) recs))) 
             (cPair 0 s))
    (f2 := fun t recs s : nat =>
           switchPR t
             (S
                (cPair (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs))
                   (cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)))) 0).
apply
 compose3_3IsPR
  with
    (f1 := fun t recs s : nat => cPairPi1 t)
    (f2 := fun t recs s : nat =>
           cPair (cPairPi1 t) (cPairPi2 (codeNth (t - S (cPairPi2 t)) recs)))
    (f3 := fun t recs s : nat => cPair 0 s).
apply filter100IsPR with (g := cPairPi1).
apply cPairPi1IsPR.
apply
 filter110IsPR
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
apply filter001IsPR with (g := fun s : nat => cPair 0 s).
apply compose1_2IsPR with (f := fun s : nat => 0) (f' := fun s : nat => s).
apply const1_NIsPR.
apply idIsPR.
apply cPairIsPR.
apply switchIsPR.
apply
 filter110IsPR
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

Definition ReplaceTermTerm (t s : nat) : nat :=
  cPairPi1 (ReplaceTermTermsTerm t s).

Definition ReplaceTermsTerm (t s : nat) : nat :=
  cPairPi2 (ReplaceTermTermsTerm t s).

Lemma ReplaceTermTermIsPR : isPR 2 ReplaceTermTerm.
Proof.
unfold ReplaceTermTerm in |- *.
apply compose2_1IsPR.
apply ReplaceTermTermsTermIsPR.
apply cPairPi1IsPR.
Qed.

Lemma ReplaceTermsTermIsPR : isPR 2 ReplaceTermsTerm.
Proof.
unfold ReplaceTermsTerm in |- *.
apply compose2_1IsPR.
apply ReplaceTermTermsTermIsPR.
apply cPairPi2IsPR.
Qed.

Remark ReplaceTermTermsTermMonotone :
 forall a s1 s2 : nat,
 s1 <= s2 ->
 ReplaceTermTerm a s1 <= ReplaceTermTerm a s2 /\
 ReplaceTermsTerm a s1 <= ReplaceTermsTerm a s2.
Proof.
assert
 (forall a s1 s2 n : nat,
  n < a ->
  s1 <= s2 ->
  ReplaceTermTerm n s1 <= ReplaceTermTerm n s2 /\
  ReplaceTermsTerm n s1 <= ReplaceTermsTerm n s2).
intro.
unfold ReplaceTermTerm in |- *.
unfold ReplaceTermsTerm in |- *.
unfold ReplaceTermTermsTerm in |- *.
set
 (A :=
  fun t recs s : nat =>
  cPair
    (switchPR (cPairPi1 t)
       (cPair (cPairPi1 t) (cPairPi2 (codeNth (t - S (cPairPi2 t)) recs)))
       (cPair 0 s))
    (switchPR t
       (S
          (cPair (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs))
             (cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)))) 0)) 
 in *.
induction a as [| a Hreca]; simpl in |- *; intros.
elim (lt_n_O _ H).
assert
 (forall n m : nat,
  m < n ->
  extEqual 1
    (evalComposeFunc 1 1 (Vector.cons _ (evalStrongRecHelp 1 A n) 0 (Vector.nil _))
       (fun b : nat => codeNth (n - S m) b)) (evalStrongRec 1 A m)).
intros.
apply (evalStrongRecHelp2 1). 
assumption.
simpl in H1.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
repeat rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
repeat rewrite cPairProjections1.
split.
unfold A at 3 1 in |- *.
repeat rewrite cPairProjections1.
assert (cPair (cPairPi1 n) (cPairPi2 n) = n).
apply cPairProjections.
destruct (cPairPi1 n).
simpl in |- *.
apply cPairLe3.
apply le_n.
assumption.
simpl in |- *.
assert (cPairPi2 n < n).
apply lt_le_trans with (cPair (S n0) (cPairPi2 n)).
apply cPairLt2.
rewrite H2.
apply le_n.
repeat rewrite H1.
apply cPairLe3.
apply le_n.
eapply proj2.
apply Hreca.
apply lt_le_trans with n.
apply H3.
apply lt_n_Sm_le.
assumption.
assumption.
assumption.
assumption.
unfold A at 3 1 in |- *.
repeat rewrite cPairProjections2.
destruct n.
simpl in |- *.
apply le_n.
assert (cPairPi2 n < S n).
apply le_lt_n_Sm.
apply le_trans with (cPair (cPairPi1 n) (cPairPi2 n)).
apply cPairLe2.
rewrite cPairProjections.
apply le_n.
assert (cPairPi1 n < S n).
apply le_lt_n_Sm.
apply le_trans with (cPair (cPairPi1 n) (cPairPi2 n)).
apply cPairLe1.
rewrite cPairProjections.
apply le_n.
repeat rewrite H1.
simpl in |- *.
apply le_n_S.
apply cPairLe3.
eapply proj1.
apply Hreca.
apply le_lt_trans with n.
apply lt_n_Sm_le.
assumption.
apply lt_S_n.
assumption.
assumption.
eapply proj2.
apply Hreca.
apply le_lt_trans with n.
apply lt_n_Sm_le.
assumption.
apply lt_S_n.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
intros.
apply H with (S a).
apply lt_n_Sn.
assumption.
Qed.

Lemma ReplaceTermTermMonotone :
 forall a s1 s2 : nat,
 s1 <= s2 -> ReplaceTermTerm a s1 <= ReplaceTermTerm a s2.
Proof.
intros.
eapply proj1.
apply ReplaceTermTermsTermMonotone.
assumption.
Qed.

Lemma ReplaceTermsTermMonotone :
 forall a s1 s2 : nat,
 s1 <= s2 -> ReplaceTermsTerm a s1 <= ReplaceTermsTerm a s2.
Proof.
intros.
eapply proj2.
apply ReplaceTermTermsTermMonotone.
assumption.
Qed.

Remark maxLemma :
 forall a b c d : nat, a <= b -> c <= d -> max a c <= max b d.
Proof.
intros.
apply (max_case2 a c).
apply le_trans with b.
assumption.
apply le_max_l.
apply le_trans with d.
assumption.
apply le_max_r.
Qed.

Remark maxLemma2 :
 forall a b : list nat, fold_right max 0 a <= fold_right max 0 (a ++ b).
Proof.
intros.
induction a as [| a a0 Hreca].
apply le_O_n.
simpl in |- *.
apply maxLemma.
apply le_n.
assumption.
Qed.

Remark maxLemma3 :
 forall a b : list nat, fold_right max 0 b <= fold_right max 0 (a ++ b).
Proof.
intros.
induction a as [| a a0 Hreca].
apply le_n.
simpl in |- *.
apply le_trans with (fold_right max 0 (a0 ++ b)).
assumption.
apply le_max_r.
Qed.

Remark maxApp :
 forall a b : list nat,
 {fold_right max 0 (a ++ b) = fold_right max 0 a} +
 {fold_right max 0 (a ++ b) = fold_right max 0 b}.
Proof.
intros.
induction a as [| a a0 Hreca].
simpl in |- *.
auto.
simpl in |- *.
induction (max_dec a (fold_right max 0 (a0 ++ b))).
rewrite a1.
left.
symmetry  in |- *.
apply max_l.
apply le_trans with (max a (fold_right max 0 (a0 ++ b))).
apply le_trans with (max a (fold_right max 0 a0)).
apply le_max_r.
apply maxLemma.
apply le_n.
apply maxLemma2.
rewrite a1.
apply le_n.
induction Hreca as [a1| b1].
rewrite a1.
auto.
rewrite b0.
rewrite b1.
auto.
Qed.

Lemma boundSubTerm :
 forall (t : fol.Term L) (v : nat) (s : fol.Term L),
 codeTerm (substituteTerm L t v s) <=
 ReplaceTermTerm (codeTerm t)
   (fold_right max 0 (codeTerm s :: freeVarTerm L t)).
Proof.
intro.
unfold ReplaceTermTerm in |- *.
unfold ReplaceTermsTerm in |- *.
unfold ReplaceTermTermsTerm in |- *.
set
 (A :=
  fun t0 recs s0 : nat =>
  cPair
    (switchPR (cPairPi1 t0)
       (cPair (cPairPi1 t0) (cPairPi2 (codeNth (t0 - S (cPairPi2 t0)) recs)))
       (cPair 0 s0))
    (switchPR t0
       (S
          (cPair (cPairPi1 (codeNth (t0 - S (cPairPi1 (pred t0))) recs))
             (cPairPi2 (codeNth (t0 - S (cPairPi2 (pred t0))) recs)))) 0))
 in *.
assert
 (forall n m : nat,
  m < n ->
  extEqual 1
    (evalComposeFunc 1 1 (Vector.cons _ (evalStrongRecHelp 1 A n) 0 (Vector.nil _))
       (fun b : nat => codeNth (n - S m) b)) (evalStrongRec 1 A m)).
intros.
apply (evalStrongRecHelp2 1). 
assumption.
simpl in H.
elim t using
 Term_Terms_ind
  with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
           forall (v : nat) (s : fol.Term L),
           codeTerms L codeF n (substituteTerms L n ts v s) <=
           ReplaceTermsTerm (codeTerms L codeF n ts)
             (fold_right max 0 (codeTerm s :: freeVarTerms L n ts)));
 simpl in |- *; intros; unfold evalStrongRec in |- *;
 unfold evalComposeFunc, evalOneParamList, evalList in |- *;
 repeat rewrite computeEvalStrongRecHelp; unfold compose2 in |- *;
 unfold evalComposeFunc, evalOneParamList, evalList in |- *; 
 simpl in |- *; repeat rewrite cPairProjections1.
unfold A in |- *.
simpl in |- *.
repeat rewrite cPairProjections1.
replace (codeTerm (fol.var L n)) with (cPair 0 n); [ idtac | reflexivity ].
repeat rewrite cPairProjections1.
simpl in |- *.
induction (eq_nat_dec v n).
eapply le_trans; [ idtac | apply cPairLe2 ].
apply le_max_l.
replace (codeTerm (fol.var L n)) with (cPair 0 n); [ idtac | reflexivity ].
apply cPairLe3.
apply le_n.
eapply le_trans; [ idtac | apply le_max_r ].
apply le_max_l.
unfold A in |- *.
repeat rewrite cPairProjections1.
replace (codeTerm (fol.apply L f t0)) with
 (cPair (S (codeF f)) (codeTerms L codeF _ t0)); [ idtac | reflexivity ].
repeat rewrite cPairProjections1.
rewrite
 H
   with
   (m := 
     cPairPi2
       (cPair (S (codeF f))
          (codeTerms L codeF (arity L (inr (Relations L) f)) t0))).
simpl in |- *.
replace
 (codeTerm
    (fol.apply L f (substituteTerms L (arity L (inr (Relations L) f)) t0 v s)))
 with
 (cPair (S (codeF f))
    (codeTerms L codeF _
       (substituteTerms L (arity L (inr (Relations L) f)) t0 v s)));
 [ idtac | reflexivity ].
apply cPairLe3.
apply le_n.
unfold ReplaceTermsTerm in H0.
unfold ReplaceTermTermsTerm in H0.
fold A in H0.
repeat rewrite cPairProjections2.
apply (H0 v s).
repeat rewrite cPairProjections2.
apply cPairLt2.
apply le_O_n.
replace
 (codeTerms L codeF (S n)
    (Tcons L n (substituteTerm L t0 v s) (substituteTerms L n t1 v s))) with
 (S
    (cPair (codeTerm (substituteTerm L t0 v s))
       (codeTerms L codeF n (substituteTerms L n t1 v s))));
 [ idtac | reflexivity ].
unfold ReplaceTermsTerm in |- *.
unfold ReplaceTermsTerm in H1.
unfold ReplaceTermTermsTerm in |- *.
unfold ReplaceTermTermsTerm in H1.
fold A in |- *.
fold A in H1.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
repeat rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
repeat rewrite cPairProjections1.
unfold A at 1 in |- *.
repeat rewrite cPairProjections2.
repeat rewrite H.
replace (codeTerms L codeF (S n) (Tcons L n t0 t1)) with
 (S (cPair (codeTerm t0) (codeTerms L codeF n t1))); 
 [ idtac | reflexivity ].
simpl in |- *.
repeat rewrite cPairProjections1.
apply le_n_S.
apply cPairLe3.
eapply le_trans.
apply H0.
apply
 (ReplaceTermTermMonotone (codeTerm t0)
    (max (codeTerm s) (fold_right max 0 (freeVarTerm L t0)))
    (max (codeTerm s)
       (fold_right max 0 (freeVarTerms L (S n) (Tcons L n t0 t1))))).
apply maxLemma.
apply le_n.
replace (freeVarTerms L (S n) (Tcons L n t0 t1)) with
 (freeVarTerm L t0 ++ freeVarTerms L n t1); [ idtac | reflexivity ].
apply maxLemma2.
eapply le_trans.
apply H1.
repeat rewrite cPairProjections2.
apply
 (ReplaceTermsTermMonotone (codeTerms L codeF n t1)
    (max (codeTerm s) (fold_right max 0 (freeVarTerms L n t1)))
    (max (codeTerm s)
       (fold_right max 0 (freeVarTerms L (S n) (Tcons L n t0 t1))))).
apply maxLemma.
apply le_n.
replace (freeVarTerms L (S n) (Tcons L n t0 t1)) with
 (freeVarTerm L t0 ++ freeVarTerms L n t1); [ idtac | reflexivity ].
apply maxLemma3.
replace (codeTerms L codeF (S n) (Tcons L n t0 t1)) with
 (S (cPair (codeTerm t0) (codeTerms L codeF n t1))); 
 [ idtac | reflexivity ].
simpl in |- *.
repeat rewrite cPairProjections2.
apply le_lt_n_Sm.
apply cPairLe2.
replace (codeTerms L codeF (S n) (Tcons L n t0 t1)) with
 (S (cPair (codeTerm t0) (codeTerms L codeF n t1))); 
 [ idtac | reflexivity ].
simpl in |- *.
repeat rewrite cPairProjections1.
apply le_lt_n_Sm.
apply cPairLe1.
Qed.

Lemma boundSubTerms :
 forall (n : nat) (ts : fol.Terms L n) (v : nat) (s : fol.Term L),
 codeTerms L codeF n (substituteTerms L n ts v s) <=
 ReplaceTermsTerm (codeTerms L codeF n ts)
   (fold_right max 0 (codeTerm s :: freeVarTerms L n ts)).
Proof.
intros n ts.
unfold ReplaceTermTerm in |- *.
unfold ReplaceTermsTerm in |- *.
unfold ReplaceTermTermsTerm in |- *.
set
 (A :=
  fun t0 recs s0 : nat =>
  cPair
    (switchPR (cPairPi1 t0)
       (cPair (cPairPi1 t0) (cPairPi2 (codeNth (t0 - S (cPairPi2 t0)) recs)))
       (cPair 0 s0))
    (switchPR t0
       (S
          (cPair (cPairPi1 (codeNth (t0 - S (cPairPi1 (pred t0))) recs))
             (cPairPi2 (codeNth (t0 - S (cPairPi2 (pred t0))) recs)))) 0))
 in *.
assert
 (forall n m : nat,
  m < n ->
  extEqual 1
    (evalComposeFunc 1 1 (Vector.cons _ (evalStrongRecHelp 1 A n) 0 (Vector.nil _))
       (fun b : nat => codeNth (n - S m) b)) (evalStrongRec 1 A m)).
intros.
apply (evalStrongRecHelp2 1). 
assumption.
simpl in H.
induction ts as [| n t ts Hrects]; simpl in |- *; intros.
apply le_O_n.
replace
 (codeTerms L codeF (S n)
    (Tcons L n (substituteTerm L t v s) (substituteTerms L n ts v s))) with
 (S
    (cPair (codeTerm (substituteTerm L t v s))
       (codeTerms L codeF n (substituteTerms L n ts v s))));
 [ idtac | reflexivity ].
unfold evalStrongRec in |- *;
 unfold evalComposeFunc, evalOneParamList, evalList in |- *;
 repeat rewrite computeEvalStrongRecHelp; unfold compose2 in |- *;
 unfold evalComposeFunc, evalOneParamList, evalList in |- *; 
 simpl in |- *; repeat rewrite cPairProjections1.
unfold A at 1 in |- *.
repeat rewrite cPairProjections2.
repeat rewrite H.
replace (codeTerms L codeF (S n) (Tcons L n t ts)) with
 (S (cPair (codeTerm t) (codeTerms L codeF n ts))); 
 [ idtac | reflexivity ].
simpl in |- *.
repeat rewrite cPairProjections1.
apply le_n_S.
apply cPairLe3.
eapply le_trans.
apply boundSubTerm.
apply
 (ReplaceTermTermMonotone (codeTerm t)
    (max (codeTerm s) (fold_right max 0 (freeVarTerm L t)))
    (max (codeTerm s)
       (fold_right max 0 (freeVarTerms L (S n) (Tcons L n t ts))))).
apply maxLemma.
apply le_n.
replace (freeVarTerms L (S n) (Tcons L n t ts)) with
 (freeVarTerm L t ++ freeVarTerms L n ts); [ idtac | reflexivity ].
apply maxLemma2.
eapply le_trans.
apply Hrects.
repeat rewrite cPairProjections2.
apply
 (ReplaceTermsTermMonotone (codeTerms L codeF n ts)
    (max (codeTerm s) (fold_right max 0 (freeVarTerms L n ts)))
    (max (codeTerm s)
       (fold_right max 0 (freeVarTerms L (S n) (Tcons L n t ts))))).
apply maxLemma.
apply le_n.
replace (freeVarTerms L (S n) (Tcons L n t ts)) with
 (freeVarTerm L t ++ freeVarTerms L n ts); [ idtac | reflexivity ].
apply maxLemma3.
replace (codeTerms L codeF (S n) (Tcons L n t ts)) with
 (S (cPair (codeTerm t) (codeTerms L codeF n ts))); 
 [ idtac | reflexivity ].
simpl in |- *.
repeat rewrite cPairProjections2.
apply le_lt_n_Sm.
apply cPairLe2.
replace (codeTerms L codeF (S n) (Tcons L n t ts)) with
 (S (cPair (codeTerm t) (codeTerms L codeF n ts))); 
 [ idtac | reflexivity ].
simpl in |- *.
repeat rewrite cPairProjections1.
apply le_lt_n_Sm.
apply cPairLe1.
Qed.

Lemma ReplaceTermTermSub :
 forall (t : fol.Term L) (v w s2 : nat),
 ReplaceTermTerm (codeTerm (substituteTerm L t v (var w))) s2 =
 ReplaceTermTerm (codeTerm t) s2.
Proof.
intro.
unfold ReplaceTermTerm in |- *.
unfold ReplaceTermsTerm in |- *.
unfold ReplaceTermTermsTerm in |- *.
set
 (A :=
  fun t0 recs s0 : nat =>
  cPair
    (switchPR (cPairPi1 t0)
       (cPair (cPairPi1 t0) (cPairPi2 (codeNth (t0 - S (cPairPi2 t0)) recs)))
       (cPair 0 s0))
    (switchPR t0
       (S
          (cPair (cPairPi1 (codeNth (t0 - S (cPairPi1 (pred t0))) recs))
             (cPairPi2 (codeNth (t0 - S (cPairPi2 (pred t0))) recs)))) 0))
 in *.
assert
 (forall n m : nat,
  m < n ->
  extEqual 1
    (evalComposeFunc 1 1 (Vector.cons _ (evalStrongRecHelp 1 A n) 0 (Vector.nil _))
       (fun b : nat => codeNth (n - S m) b)) (evalStrongRec 1 A m)).
intros.
apply (evalStrongRecHelp2 1). 
assumption.
simpl in H.
elim t using
 Term_Terms_ind
  with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
           forall v w s2 : nat,
           ReplaceTermsTerm
             (codeTerms L codeF n (substituteTerms L n ts v (var w))) s2 =
           ReplaceTermsTerm (codeTerms L codeF n ts) s2); 
 simpl in |- *; intros; unfold evalStrongRec in |- *;
 unfold evalComposeFunc, evalOneParamList, evalList in |- *;
 repeat rewrite computeEvalStrongRecHelp; unfold compose2 in |- *;
 unfold evalComposeFunc, evalOneParamList, evalList in |- *; 
 simpl in |- *; repeat rewrite cPairProjections1.
induction (eq_nat_dec v n); unfold var in |- *;
 (replace (codeTerm (fol.var L n)) with (cPair 0 n); [ idtac | reflexivity ]).
replace (codeTerm (fol.var L w)) with (cPair 0 w); [ idtac | reflexivity ].
unfold A at 3 1 in |- *.
repeat rewrite cPairProjections1.
simpl in |- *.
reflexivity.
reflexivity.
replace
 (codeTerm
    (fol.apply L f
       (substituteTerms L (arity L (inr (Relations L) f)) t0 v (var w))))
 with
 (cPair (S (codeF f))
    (codeTerms L codeF _
       (substituteTerms L (arity L (inr (Relations L) f)) t0 v (var w))));
 [ idtac | reflexivity ].
unfold A at 3 1 in |- *.
repeat rewrite cPairProjections1.
replace (codeTerm (fol.apply L f t0)) with
 (cPair (S (codeF f)) (codeTerms L codeF _ t0)); [ idtac | reflexivity ].
repeat rewrite H.
repeat rewrite cPairProjections1.
simpl in |- *.
repeat rewrite cPairProjections2.
replace
 (cPairPi2
    (evalStrongRec 1 A
       (codeTerms L codeF (arity L (inr (Relations L) f))
          (substituteTerms L (arity L (inr (Relations L) f)) t0 v (var w)))
       s2)) with
 (cPairPi2
    (evalStrongRec 1 A (codeTerms L codeF (arity L (inr (Relations L) f)) t0)
       s2)).
reflexivity.
symmetry  in |- *.
apply (H0 v w s2).
repeat rewrite cPairProjections2.
apply cPairLt2.
repeat rewrite cPairProjections2.
apply cPairLt2.
reflexivity.
unfold ReplaceTermsTerm in |- *.
unfold ReplaceTermsTerm in H1.
unfold ReplaceTermTermsTerm in |- *.
unfold ReplaceTermTermsTerm in H1.
fold A in |- *.
fold A in H1.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
repeat rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
repeat rewrite cPairProjections1.
unfold A at 3 1 in |- *.
repeat rewrite cPairProjections2.
repeat rewrite H.
replace
 (codeTerms L codeF (S n)
    (Tcons L n (substituteTerm L t0 v (var w))
       (substituteTerms L n t1 v (var w)))) with
 (S
    (cPair (codeTerm (substituteTerm L t0 v (var w)))
       (codeTerms L codeF n (substituteTerms L n t1 v (var w)))));
 [ idtac | reflexivity ].
replace (codeTerms L codeF (S n) (Tcons L n t0 t1)) with
 (S (cPair (codeTerm t0) (codeTerms L codeF n t1))); 
 [ idtac | reflexivity ].
simpl in |- *.
repeat rewrite cPairProjections2.
replace
 (cPairPi1
    (evalStrongRec 1 A
       (cPairPi1 (cPair (codeTerm t0) (codeTerms L codeF n t1))) s2)) with
 (cPairPi1
    (evalStrongRec 1 A
       (cPairPi1
          (cPair (codeTerm (substituteTerm L t0 v (var w)))
             (codeTerms L codeF n (substituteTerms L n t1 v (var w))))) s2)).
replace (cPairPi2 (evalStrongRec 1 A (codeTerms L codeF n t1) s2)) with
 (cPairPi2
    (evalStrongRec 1 A
       (codeTerms L codeF n (substituteTerms L n t1 v (var w))) s2)).
reflexivity.
apply (H1 v w s2).
repeat rewrite cPairProjections1.
apply (H0 v w s2).
replace (codeTerms L codeF (S n) (Tcons L n t0 t1)) with
 (S (cPair (codeTerm t0) (codeTerms L codeF n t1))); 
 [ idtac | reflexivity ].
simpl in |- *.
rewrite cPairProjections2.
apply le_lt_n_Sm.
apply cPairLe2.
replace (codeTerms L codeF (S n) (Tcons L n t0 t1)) with
 (S (cPair (codeTerm t0) (codeTerms L codeF n t1))); 
 [ idtac | reflexivity ].
simpl in |- *.
rewrite cPairProjections1.
apply le_lt_n_Sm.
apply cPairLe1.
replace
 (codeTerms L codeF (S n)
    (Tcons L n (substituteTerm L t0 v (var w))
       (substituteTerms L n t1 v (var w)))) with
 (S
    (cPair (codeTerm (substituteTerm L t0 v (var w)))
       (codeTerms L codeF n (substituteTerms L n t1 v (var w)))));
 [ idtac | reflexivity ].
simpl in |- *.
rewrite cPairProjections2.
apply le_lt_n_Sm.
apply cPairLe2.
replace
 (codeTerms L codeF (S n)
    (Tcons L n (substituteTerm L t0 v (var w))
       (substituteTerms L n t1 v (var w)))) with
 (S
    (cPair (codeTerm (substituteTerm L t0 v (var w)))
       (codeTerms L codeF n (substituteTerms L n t1 v (var w)))));
 [ idtac | reflexivity ].
simpl in |- *.
rewrite cPairProjections1.
apply le_lt_n_Sm.
apply cPairLe1.
Qed.

Lemma ReplaceTermsTermSub :
 forall (n : nat) (ts : fol.Terms L n) (v w s2 : nat),
 ReplaceTermsTerm (codeTerms L codeF n (substituteTerms L n ts v (var w))) s2 =
 ReplaceTermsTerm (codeTerms L codeF n ts) s2.
Proof.
intros n ts.
unfold ReplaceTermTerm in |- *.
unfold ReplaceTermsTerm in |- *.
unfold ReplaceTermTermsTerm in |- *.
set
 (A :=
  fun t0 recs s0 : nat =>
  cPair
    (switchPR (cPairPi1 t0)
       (cPair (cPairPi1 t0) (cPairPi2 (codeNth (t0 - S (cPairPi2 t0)) recs)))
       (cPair 0 s0))
    (switchPR t0
       (S
          (cPair (cPairPi1 (codeNth (t0 - S (cPairPi1 (pred t0))) recs))
             (cPairPi2 (codeNth (t0 - S (cPairPi2 (pred t0))) recs)))) 0))
 in *.
assert
 (forall n m : nat,
  m < n ->
  extEqual 1
    (evalComposeFunc 1 1 (Vector.cons _ (evalStrongRecHelp 1 A n) 0 (Vector.nil _))
       (fun b : nat => codeNth (n - S m) b)) (evalStrongRec 1 A m)).
intros.
apply (evalStrongRecHelp2 1). 
assumption.
simpl in H.
induction ts as [| n t ts Hrects]; simpl in |- *; intros.
reflexivity.
unfold evalStrongRec in |- *;
 unfold evalComposeFunc, evalOneParamList, evalList in |- *;
 repeat rewrite computeEvalStrongRecHelp; unfold compose2 in |- *;
 unfold evalComposeFunc, evalOneParamList, evalList in |- *; 
 simpl in |- *; repeat rewrite cPairProjections1.
unfold A at 3 1 in |- *.
repeat rewrite cPairProjections2.
repeat rewrite H.
replace
 (codeTerms L codeF (S n)
    (Tcons L n (substituteTerm L t v (var w))
       (substituteTerms L n ts v (var w)))) with
 (S
    (cPair (codeTerm (substituteTerm L t v (var w)))
       (codeTerms L codeF n (substituteTerms L n ts v (var w)))));
 [ idtac | reflexivity ].
replace (codeTerms L codeF (S n) (Tcons L n t ts)) with
 (S (cPair (codeTerm t) (codeTerms L codeF n ts))); 
 [ idtac | reflexivity ].
simpl in |- *.
repeat rewrite cPairProjections2.
replace
 (cPairPi1
    (evalStrongRec 1 A
       (cPairPi1 (cPair (codeTerm t) (codeTerms L codeF n ts))) s2)) with
 (cPairPi1
    (evalStrongRec 1 A
       (cPairPi1
          (cPair (codeTerm (substituteTerm L t v (var w)))
             (codeTerms L codeF n (substituteTerms L n ts v (var w))))) s2)).
replace (cPairPi2 (evalStrongRec 1 A (codeTerms L codeF n ts) s2)) with
 (cPairPi2
    (evalStrongRec 1 A
       (codeTerms L codeF n (substituteTerms L n ts v (var w))) s2)).
reflexivity.
apply (Hrects v w s2).
repeat rewrite cPairProjections1.
apply (ReplaceTermTermSub t v w s2).
replace (codeTerms L codeF (S n) (Tcons L n t ts)) with
 (S (cPair (codeTerm t) (codeTerms L codeF n ts))); 
 [ idtac | reflexivity ].
simpl in |- *.
rewrite cPairProjections2.
apply le_lt_n_Sm.
apply cPairLe2.
replace (codeTerms L codeF (S n) (Tcons L n t ts)) with
 (S (cPair (codeTerm t) (codeTerms L codeF n ts))); 
 [ idtac | reflexivity ].
simpl in |- *.
rewrite cPairProjections1.
apply le_lt_n_Sm.
apply cPairLe1.
replace
 (codeTerms L codeF (S n)
    (Tcons L n (substituteTerm L t v (var w))
       (substituteTerms L n ts v (var w)))) with
 (S
    (cPair (codeTerm (substituteTerm L t v (var w)))
       (codeTerms L codeF n (substituteTerms L n ts v (var w)))));
 [ idtac | reflexivity ].
simpl in |- *.
rewrite cPairProjections2.
apply le_lt_n_Sm.
apply cPairLe2.
replace
 (codeTerms L codeF (S n)
    (Tcons L n (substituteTerm L t v (var w))
       (substituteTerms L n ts v (var w)))) with
 (S
    (cPair (codeTerm (substituteTerm L t v (var w)))
       (codeTerms L codeF n (substituteTerms L n ts v (var w)))));
 [ idtac | reflexivity ].
simpl in |- *.
rewrite cPairProjections1.
apply le_lt_n_Sm.
apply cPairLe1.
Qed.

Definition ReplaceFormulaTerm : nat -> nat -> nat :=
  evalStrongRec 1
    (fun f recs s : nat =>
     switchPR (cPairPi1 f)
       (switchPR (pred (cPairPi1 f))
          (switchPR (pred (pred (cPairPi1 f)))
             (switchPR (pred (pred (pred (cPairPi1 f))))
                (cPair (cPairPi1 f) (ReplaceTermsTerm (cPairPi2 f) s))
                (cPair 3
                   (cPair s (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))))
             (cPair 2 (codeNth (f - S (cPairPi2 f)) recs)))
          (cPair 1
             (cPair (codeNth (f - S (cPairPi1 (cPairPi2 f))) recs)
                (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))))
       (cPair 0
          (cPair (ReplaceTermTerm (cPairPi1 (cPairPi2 f)) s)
             (ReplaceTermTerm (cPairPi2 (cPairPi2 f)) s)))).

Lemma ReplaceFormulaTermIsPR : isPR 2 ReplaceFormulaTerm.
Proof.
unfold ReplaceFormulaTerm in |- *.
apply evalStrongRecIsPR.
apply
 compose3_3IsPR
  with
    (f1 := fun f recs s : nat => cPairPi1 f)
    (f2 := fun f recs s : nat =>
           switchPR (pred (cPairPi1 f))
             (switchPR (pred (pred (cPairPi1 f)))
                (switchPR (pred (pred (pred (cPairPi1 f))))
                   (cPair (cPairPi1 f) (ReplaceTermsTerm (cPairPi2 f) s))
                   (cPair 3
                      (cPair s (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))))
                (cPair 2 (codeNth (f - S (cPairPi2 f)) recs)))
             (cPair 1
                (cPair (codeNth (f - S (cPairPi1 (cPairPi2 f))) recs)
                   (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))))
    (f3 := fun f recs s : nat =>
           cPair 0
             (cPair (ReplaceTermTerm (cPairPi1 (cPairPi2 f)) s)
                (ReplaceTermTerm (cPairPi2 (cPairPi2 f)) s))).
apply filter100IsPR.
apply cPairPi1IsPR.
apply
 compose3_3IsPR
  with
    (f1 := fun f recs s : nat => pred (cPairPi1 f))
    (f2 := fun f recs s : nat =>
           switchPR (pred (pred (cPairPi1 f)))
             (switchPR (pred (pred (pred (cPairPi1 f))))
                (cPair (cPairPi1 f) (ReplaceTermsTerm (cPairPi2 f) s))
                (cPair 3
                   (cPair s (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))))
             (cPair 2 (codeNth (f - S (cPairPi2 f)) recs)))
    (f3 := fun f recs s : nat =>
           cPair 1
             (cPair (codeNth (f - S (cPairPi1 (cPairPi2 f))) recs)
                (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))).
apply filter100IsPR with (g := fun f : nat => pred (cPairPi1 f)).
apply compose1_1IsPR.
apply cPairPi1IsPR.
apply predIsPR.
apply
 compose3_3IsPR
  with
    (f1 := fun f recs s : nat => pred (pred (cPairPi1 f)))
    (f2 := fun f recs s : nat =>
           switchPR (pred (pred (pred (cPairPi1 f))))
             (cPair (cPairPi1 f) (ReplaceTermsTerm (cPairPi2 f) s))
             (cPair 3
                (cPair s (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))))
    (f3 := fun f recs s : nat => cPair 2 (codeNth (f - S (cPairPi2 f)) recs)).
apply filter100IsPR with (g := fun f : nat => pred (pred (cPairPi1 f))).
apply compose1_1IsPR with (f := fun f : nat => pred (cPairPi1 f)).
apply compose1_1IsPR.
apply cPairPi1IsPR.
apply predIsPR.
apply predIsPR.
apply
 compose3_3IsPR
  with
    (f1 := fun f recs s : nat => pred (pred (pred (cPairPi1 f))))
    (f2 := fun f recs s : nat =>
           cPair (cPairPi1 f) (ReplaceTermsTerm (cPairPi2 f) s))
    (f3 := fun f recs s : nat =>
           cPair 3 (cPair s (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))).
apply
 filter100IsPR with (g := fun f : nat => pred (pred (pred (cPairPi1 f)))).
apply compose1_1IsPR with (f := fun f : nat => pred (pred (cPairPi1 f))).
apply compose1_1IsPR with (f := fun f : nat => pred (cPairPi1 f)).
apply compose1_1IsPR.
apply cPairPi1IsPR.
apply predIsPR.
apply predIsPR.
apply predIsPR.
apply
 filter101IsPR
  with
    (g := fun f s : nat =>
          cPair (cPairPi1 f) (ReplaceTermsTerm (cPairPi2 f) s)).
apply
 compose2_2IsPR
  with
    (f := fun f s : nat => cPairPi1 f)
    (g := fun f s : nat => ReplaceTermsTerm (cPairPi2 f) s).
apply filter10IsPR.
apply cPairPi1IsPR.
apply
 compose2_2IsPR
  with (f := fun f s : nat => cPairPi2 f) (g := fun f s : nat => s).
apply filter10IsPR.
apply cPairPi2IsPR.
apply pi2_2IsPR.
apply ReplaceTermsTermIsPR.
apply cPairIsPR.
apply
 compose3_2IsPR
  with
    (f1 := fun f recs s : nat => 3)
    (f2 := fun f recs s : nat =>
           cPair s (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs)).
apply filter100IsPR with (g := fun _ : nat => 3).
apply const1_NIsPR.
apply
 compose3_2IsPR
  with
    (f1 := fun f recs s : nat => s)
    (f2 := fun f recs s : nat => codeNth (f - S (cPairPi2 (cPairPi2 f))) recs).
apply pi3_3IsPR.
apply
 filter110IsPR
  with
    (g := fun f recs : nat => codeNth (f - S (cPairPi2 (cPairPi2 f))) recs).
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
apply compose1_1IsPR.
apply cPairPi2IsPR.
apply cPairPi2IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply cPairIsPR.
apply cPairIsPR.
apply switchIsPR.
apply
 filter110IsPR
  with (g := fun f recs : nat => cPair 2 (codeNth (f - S (cPairPi2 f)) recs)).
apply
 compose2_2IsPR
  with
    (f := fun f recs : nat => 2)
    (g := fun f recs : nat => codeNth (f - S (cPairPi2 f)) recs).
apply filter10IsPR with (g := fun _ : nat => 2).
apply const1_NIsPR.
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
apply cPairIsPR.
apply switchIsPR.
apply
 filter110IsPR
  with
    (g := fun f recs : nat =>
          cPair 1
            (cPair (codeNth (f - S (cPairPi1 (cPairPi2 f))) recs)
               (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))).
apply
 compose2_2IsPR
  with
    (f := fun f recs : nat => 1)
    (g := fun f recs : nat =>
          cPair (codeNth (f - S (cPairPi1 (cPairPi2 f))) recs)
            (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs)).
apply filter10IsPR with (g := fun _ : nat => 1).
apply const1_NIsPR.
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
apply compose1_1IsPR.
apply cPairPi2IsPR.
apply cPairPi2IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply cPairIsPR.
apply cPairIsPR.
apply switchIsPR.
apply
 filter101IsPR
  with
    (g := fun f s : nat =>
          cPair 0
            (cPair (ReplaceTermTerm (cPairPi1 (cPairPi2 f)) s)
               (ReplaceTermTerm (cPairPi2 (cPairPi2 f)) s))).
apply
 compose2_2IsPR
  with
    (f := fun f s : nat => 0)
    (g := fun f s : nat =>
          cPair (ReplaceTermTerm (cPairPi1 (cPairPi2 f)) s)
            (ReplaceTermTerm (cPairPi2 (cPairPi2 f)) s)).
apply filter10IsPR with (g := fun _ : nat => 0).
apply const1_NIsPR.
apply
 compose2_2IsPR
  with
    (f := fun f s : nat => ReplaceTermTerm (cPairPi1 (cPairPi2 f)) s)
    (g := fun f s : nat => ReplaceTermTerm (cPairPi2 (cPairPi2 f)) s).
apply
 compose2_2IsPR
  with
    (f := fun f s : nat => cPairPi1 (cPairPi2 f))
    (g := fun f s : nat => s).
apply filter10IsPR with (g := fun f : nat => cPairPi1 (cPairPi2 f)).
apply compose1_1IsPR.
apply cPairPi2IsPR.
apply cPairPi1IsPR.
apply pi2_2IsPR.
apply ReplaceTermTermIsPR.
apply
 compose2_2IsPR
  with
    (f := fun f s : nat => cPairPi2 (cPairPi2 f))
    (g := fun f s : nat => s).
apply filter10IsPR with (g := fun f : nat => cPairPi2 (cPairPi2 f)).
apply compose1_1IsPR.
apply cPairPi2IsPR.
apply cPairPi2IsPR.
apply pi2_2IsPR.
apply ReplaceTermTermIsPR.
apply cPairIsPR.
apply cPairIsPR.
apply switchIsPR.
Qed.

Lemma ReplaceFormulaTermMonotone :
 forall a s1 s2 : nat,
 s1 <= s2 -> ReplaceFormulaTerm a s1 <= ReplaceFormulaTerm a s2.
Proof.
assert
 (forall a s1 s2 n : nat,
  n < a -> s1 <= s2 -> ReplaceFormulaTerm n s1 <= ReplaceFormulaTerm n s2).
unfold ReplaceFormulaTerm in |- *.
set
 (A :=
  fun f recs s : nat =>
  switchPR (cPairPi1 f)
    (switchPR (pred (cPairPi1 f))
       (switchPR (pred (pred (cPairPi1 f)))
          (switchPR (pred (pred (pred (cPairPi1 f))))
             (cPair (cPairPi1 f) (ReplaceTermsTerm (cPairPi2 f) s))
             (cPair 3
                (cPair s (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))))
          (cPair 2 (codeNth (f - S (cPairPi2 f)) recs)))
       (cPair 1
          (cPair (codeNth (f - S (cPairPi1 (cPairPi2 f))) recs)
             (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))))
    (cPair 0
       (cPair (ReplaceTermTerm (cPairPi1 (cPairPi2 f)) s)
          (ReplaceTermTerm (cPairPi2 (cPairPi2 f)) s)))) 
 in *.
assert
 (forall n m : nat,
  m < n ->
  extEqual 1
    (evalComposeFunc 1 1 (Vector.cons _ (evalStrongRecHelp 1 A n) 0 (Vector.nil _))
       (fun b : nat => codeNth (n - S m) b)) (evalStrongRec 1 A m)).
intros.
apply (evalStrongRecHelp2 1). 
assumption.
simpl in H.
simple induction a.
intros.
elim (lt_n_O _ H0).
intros.
induction (le_lt_or_eq _ _ (lt_n_Sm_le _ _ H1)).
apply H0.
assumption.
assumption.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
repeat rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
repeat rewrite cPairProjections1.
unfold A at 3 1 in |- *.
destruct n0.
simpl in |- *.
apply cPairLe3.
apply le_n.
apply cPairLe3; apply ReplaceTermTermMonotone; assumption.
assert (cPair (cPairPi1 (S n0)) (cPairPi2 (S n0)) = S n0).
apply cPairProjections.
destruct (cPairPi1 (S n0)).
simpl in |- *.
apply cPairLe3.
apply le_n.
apply cPairLe3; apply ReplaceTermTermMonotone; assumption.
assert (cPairPi2 (S n0) < S n0).
apply lt_le_trans with (cPair (S n1) (cPairPi2 (S n0))).
apply cPairLt2.
rewrite H4.
apply le_n.
assert (cPairPi1 (cPairPi2 (S n0)) < S n0).
apply le_lt_trans with (cPairPi2 (S n0)).
apply
 le_trans
  with (cPair (cPairPi1 (cPairPi2 (S n0))) (cPairPi2 (cPairPi2 (S n0)))).
apply cPairLe1.
rewrite cPairProjections.
apply le_n.
assumption.
assert (cPairPi2 (cPairPi2 (S n0)) < S n0).
apply le_lt_trans with (cPairPi2 (S n0)).
apply
 le_trans
  with (cPair (cPairPi1 (cPairPi2 (S n0))) (cPairPi2 (cPairPi2 (S n0)))).
apply cPairLe2.
rewrite cPairProjections.
apply le_n.
assumption.
destruct n1.
repeat rewrite H with (m := cPairPi1 (cPairPi2 (S n0))); try assumption.
repeat rewrite H with (m := cPairPi2 (cPairPi2 (S n0))); try assumption.
simpl in |- *.
apply cPairLe3.
apply le_n.
apply cPairLe3.
apply H0.
rewrite <- H3.
assumption.
assumption.
apply H0.
rewrite <- H3.
assumption.
assumption.
destruct n1.
repeat rewrite H with (m := cPairPi2 (S n0)); try assumption.
simpl in |- *.
apply cPairLe3.
apply le_n.
apply H0.
rewrite <- H3.
assumption.
assumption.
destruct n1.
repeat rewrite H with (m := cPairPi2 (cPairPi2 (S n0))); try assumption.
simpl in |- *.
apply cPairLe3.
apply le_n.
apply cPairLe3.
assumption.
apply H0.
rewrite <- H3.
assumption.
assumption.
simpl in |- *.
apply cPairLe3.
apply le_n.
apply ReplaceTermsTermMonotone.
assumption.
intros.
apply (H (S a)); auto.
Qed.

Fixpoint varFormula (f : fol.Formula L) : list nat :=
  match f with
  | equal t s => freeVarTerm L t ++ freeVarTerm L s
  | atomic r ts => freeVarTerms L _ ts
  | impH A B => varFormula A ++ varFormula B
  | notH A => varFormula A
  | forallH v A => v :: varFormula A
  end.

Lemma ReplaceFormulaTermSub :
 forall (f : fol.Formula L) (v w s2 : nat),
 ReplaceFormulaTerm (codeFormula (substituteFormula L f v (var w))) s2 =
 ReplaceFormulaTerm (codeFormula f) s2.
Proof.
intro.
unfold ReplaceFormulaTerm in |- *.
set
 (A :=
  fun f0 recs s0 : nat =>
  switchPR (cPairPi1 f0)
    (switchPR (pred (cPairPi1 f0))
       (switchPR (pred (pred (cPairPi1 f0)))
          (switchPR (pred (pred (pred (cPairPi1 f0))))
             (cPair (cPairPi1 f0) (ReplaceTermsTerm (cPairPi2 f0) s0))
             (cPair 3
                (cPair s0 (codeNth (f0 - S (cPairPi2 (cPairPi2 f0))) recs))))
          (cPair 2 (codeNth (f0 - S (cPairPi2 f0)) recs)))
       (cPair 1
          (cPair (codeNth (f0 - S (cPairPi1 (cPairPi2 f0))) recs)
             (codeNth (f0 - S (cPairPi2 (cPairPi2 f0))) recs))))
    (cPair 0
       (cPair (ReplaceTermTerm (cPairPi1 (cPairPi2 f0)) s0)
          (ReplaceTermTerm (cPairPi2 (cPairPi2 f0)) s0)))) 
 in *.
assert
 (forall n m : nat,
  m < n ->
  extEqual 1
    (evalComposeFunc 1 1 (Vector.cons _ (evalStrongRecHelp 1 A n) 0 (Vector.nil _))
       (fun b : nat => codeNth (n - S m) b)) (evalStrongRec 1 A m)).
intros.
apply (evalStrongRecHelp2 1). 
assumption.
simpl in H.
elim f using Formula_depth_ind2; clear f; intros.
simpl in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
repeat rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
repeat rewrite cPairProjections1.
unfold A at 3 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
simpl in |- *.
repeat rewrite ReplaceTermTermSub.
reflexivity.
simpl in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
repeat rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
repeat rewrite cPairProjections1.
unfold A at 3 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
simpl in |- *.
rewrite ReplaceTermsTermSub.
reflexivity.
simpl in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
repeat rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
repeat rewrite cPairProjections1.
repeat rewrite subFormulaImp.
simpl in |- *.
unfold A at 3 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
rewrite H with (m := codeFormula (substituteFormula L f v (var w))).
rewrite H with (m := codeFormula (substituteFormula L f0 v (var w))).
rewrite H with (m := codeFormula f).
rewrite H with (m := codeFormula f0).
simpl in |- *.
rewrite H0.
rewrite H1.
reflexivity.
apply le_lt_trans with (cPair (codeFormula f) (codeFormula f0)).
apply cPairLe2.
apply cPairLt2.
apply le_lt_trans with (cPair (codeFormula f) (codeFormula f0)).
apply cPairLe1.
apply cPairLt2.
apply
 le_lt_trans
  with
    (cPair (codeFormula (substituteFormula L f v (var w)))
       (codeFormula (substituteFormula L f0 v (var w)))).
apply cPairLe2.
apply cPairLt2.
apply
 le_lt_trans
  with
    (cPair (codeFormula (substituteFormula L f v (var w)))
       (codeFormula (substituteFormula L f0 v (var w)))).
apply cPairLe1.
apply cPairLt2.
simpl in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
repeat rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
repeat rewrite cPairProjections1.
repeat rewrite subFormulaNot.
simpl in |- *.
unfold A at 3 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
rewrite H with (m := codeFormula (substituteFormula L f v (var w))).
rewrite H with (m := codeFormula f).
simpl in |- *.
rewrite H0.
reflexivity.
apply cPairLt2.
apply cPairLt2.
rewrite subFormulaForall.
induction (eq_nat_dec v v0).
reflexivity.
induction (In_dec eq_nat_dec v (freeVarTerm L (var w))).
simpl in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
repeat rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
repeat rewrite cPairProjections1.
simpl in |- *.
unfold A at 3 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
rewrite
 H
   with
   (m := 
     codeFormula
       (substituteFormula L
          (substituteFormula L a v
             (fol.var L
                (newVar (v0 :: freeVarTerm L (var w) ++ freeVarFormula L a))))
          v0 (var w))).
rewrite H with (m := codeFormula a).
simpl in |- *.
rewrite H0.
rewrite H0.
reflexivity.
apply depthForall.
apply eqDepth with a.
symmetry  in |- *.
apply subFormulaDepth.
apply depthForall.
apply le_lt_trans with (cPair v (codeFormula a)).
apply cPairLe2.
apply cPairLt2.
apply
 le_lt_trans
  with
    (cPair (newVar (v0 :: freeVarTerm L (var w) ++ freeVarFormula L a))
       (codeFormula
          (substituteFormula L
             (substituteFormula L a v
                (fol.var L
                   (newVar
                      (v0 :: freeVarTerm L (var w) ++ freeVarFormula L a))))
             v0 (var w)))).
apply cPairLe2.
apply cPairLt2.
simpl in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
repeat rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
repeat rewrite cPairProjections1.
simpl in |- *.
unfold A at 3 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
rewrite H with (m := codeFormula (substituteFormula L a v0 (var w))).
rewrite H with (m := codeFormula a).
simpl in |- *.
rewrite H0.
reflexivity.
apply depthForall.
apply le_lt_trans with (cPair v (codeFormula a)).
apply cPairLe2.
apply cPairLt2.
apply
 le_lt_trans with (cPair v (codeFormula (substituteFormula L a v0 (var w)))).
apply cPairLe2.
apply cPairLt2.
Qed.

Remark codeTermFreeVar :
 forall s : fol.Term L, fold_right max 0 (freeVarTerm L s) <= codeTerm s.
Proof.
intros.
elim s using
 Term_Terms_ind
  with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
           fold_right max 0 (freeVarTerms L n ts) <= codeTerms L codeF n ts);
 simpl in |- *; intros.
apply max_case2.
unfold codeTerm in |- *.
unfold code.codeTerm in |- *.
apply cPairLe2.
apply le_O_n.
apply le_trans with (codeTerms L codeF (arity L (inr (Relations L) f)) t).
assumption.
unfold codeTerm in |- *.
unfold code.codeTerm in |- *.
apply cPairLe2.
apply le_O_n.
replace (freeVarTerms L (S n) (Tcons L n t t0)) with
 (freeVarTerm L t ++ freeVarTerms L n t0); [ idtac | reflexivity ].
replace (codeTerms L codeF (S n) (Tcons L n t t0)) with
 (S (cPair (codeTerm t) (codeTerms L codeF n t0))); 
 [ idtac | reflexivity ].
induction (maxApp (freeVarTerm L t) (freeVarTerms L n t0)).
rewrite a.
eapply le_trans.
apply H.
apply le_S.
apply cPairLe1.
rewrite b.
eapply le_trans.
apply H0.
apply le_S.
apply cPairLe2.
Qed.

Remark maxVarFreeVar :
 forall f : fol.Formula L,
 fold_right max 0 (freeVarFormula L f) <= fold_right max 0 (varFormula f).
Proof.
intros.
induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf];
 simpl in |- *.
apply le_n.
apply le_n.
induction (maxApp (freeVarFormula L f1) (freeVarFormula L f0)).
rewrite a.
eapply le_trans.
apply Hrecf1.
apply maxLemma2.
rewrite b.
eapply le_trans.
apply Hrecf0.
apply maxLemma3.
assumption.
apply le_trans with (fold_right max 0 (freeVarFormula L f)).
clear Hrecf.
induction (freeVarFormula L f).
simpl in |- *.
apply le_O_n.
simpl in |- *.
induction (eq_nat_dec a n).
eapply le_trans.
apply IHl.
apply le_max_r.
simpl in |- *.
apply maxLemma.
apply le_n.
assumption.
eapply le_trans.
apply Hrecf.
apply le_max_r.
Qed.

Remark maxSubTerm :
 forall (t : fol.Term L) (v : nat) (s : fol.Term L),
 fold_right max 0 (freeVarTerm L (substituteTerm L t v s)) <=
 fold_right max 0 (freeVarTerm L s ++ freeVarTerm L t).
Proof.
intros.
elim t using
 Term_Terms_ind
  with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
           fold_right max 0 (freeVarTerms L n (substituteTerms L n ts v s)) <=
           fold_right max 0 (freeVarTerm L s ++ freeVarTerms L n ts));
 simpl in |- *; intros.
induction (eq_nat_dec v n).
apply maxLemma2.
apply maxLemma3.
apply H.
apply le_O_n.
replace
 (freeVarTerms L (S n)
    (Tcons L n (substituteTerm L t0 v s) (substituteTerms L n t1 v s))) with
 (freeVarTerm L (substituteTerm L t0 v s) ++
  freeVarTerms L n (substituteTerms L n t1 v s)).
replace (freeVarTerms L (S n) (Tcons L n t0 t1)) with
 (freeVarTerm L t0 ++ freeVarTerms L n t1).
induction
 (maxApp (freeVarTerm L (substituteTerm L t0 v s))
    (freeVarTerms L n (substituteTerms L n t1 v s))).
rewrite a.
eapply le_trans.
apply H.
induction (maxApp (freeVarTerm L s) (freeVarTerm L t0)).
rewrite a0.
apply maxLemma2.
rewrite b.
apply
 le_trans with (fold_right max 0 (freeVarTerm L t0 ++ freeVarTerms L n t1)).
apply maxLemma2.
apply maxLemma3.
rewrite b.
eapply le_trans.
apply H0.
induction (maxApp (freeVarTerm L s) (freeVarTerms L n t1)).
rewrite a.
apply maxLemma2.
rewrite b0.
apply
 le_trans with (fold_right max 0 (freeVarTerm L t0 ++ freeVarTerms L n t1)).
apply maxLemma3.
apply maxLemma3.
reflexivity.
reflexivity.
Qed.

Remark maxSubTerms :
 forall (n : nat) (ts : fol.Terms L n) (v : nat) (s : fol.Term L),
 fold_right max 0 (freeVarTerms L n (substituteTerms L n ts v s)) <=
 fold_right max 0 (freeVarTerm L s ++ freeVarTerms L n ts).
Proof.
intros.
induction ts as [| n t ts Hrects]; simpl in |- *; intros.
apply le_O_n.
replace
 (freeVarTerms L (S n)
    (Tcons L n (substituteTerm L t v s) (substituteTerms L n ts v s))) with
 (freeVarTerm L (substituteTerm L t v s) ++
  freeVarTerms L n (substituteTerms L n ts v s)).
replace (freeVarTerms L (S n) (Tcons L n t ts)) with
 (freeVarTerm L t ++ freeVarTerms L n ts).
induction
 (maxApp (freeVarTerm L (substituteTerm L t v s))
    (freeVarTerms L n (substituteTerms L n ts v s))).
rewrite a.
eapply le_trans.
apply maxSubTerm.
induction (maxApp (freeVarTerm L s) (freeVarTerm L t)).
rewrite a0.
apply maxLemma2.
rewrite b.
apply
 le_trans with (fold_right max 0 (freeVarTerm L t ++ freeVarTerms L n ts)).
apply maxLemma2.
apply maxLemma3.
rewrite b.
eapply le_trans.
apply Hrects.
induction (maxApp (freeVarTerm L s) (freeVarTerms L n ts)).
rewrite a.
apply maxLemma2.
rewrite b0.
apply
 le_trans with (fold_right max 0 (freeVarTerm L t ++ freeVarTerms L n ts)).
apply maxLemma3.
apply maxLemma3.
reflexivity.
reflexivity.
Qed.

Definition pow3 : nat -> nat :=
  nat_rec (fun _ => nat) 1 (fun _ rec : nat => rec + (rec + rec)).

Lemma pow3IsPR : isPR 1 pow3.
Proof.
unfold pow3 in |- *.
apply indIsPR with (g := 1) (f := fun _ rec : nat => rec + (rec + rec)).
apply filter01IsPR with (g := fun rec : nat => rec + (rec + rec)).
apply
 compose1_2IsPR
  with (f := fun rec : nat => rec) (f' := fun rec : nat => rec + rec).
apply idIsPR.
apply
 compose1_2IsPR with (f := fun rec : nat => rec) (f' := fun rec : nat => rec).
apply idIsPR.
apply idIsPR.
apply plusIsPR.
apply plusIsPR.
Qed.

Lemma pow3Monotone : forall a b : nat, a <= b -> pow3 a <= pow3 b.
Proof.
intros.
induction b as [| b Hrecb].
simpl in |- *.
rewrite <- (le_n_O_eq _ H).
simpl in |- *.
apply le_n.
simpl in |- *.
induction (le_lt_or_eq _ _ H).
apply le_trans with (pow3 b).
apply Hrecb.
apply lt_n_Sm_le.
assumption.
apply le_plus_l.
rewrite H0.
simpl in |- *.
apply le_n.
Qed.

Lemma pow3Min : forall a : nat, 1 <= pow3 a.
Proof.
intros.
induction a as [| a Hreca].
simpl in |- *.
apply le_n.
simpl in |- *.
eapply le_trans.
apply Hreca.
apply le_plus_l.
Qed.

Remark mapListLemma :
 forall l : list nat, fold_right max 0 (map S l) <= S (fold_right max 0 l).
Proof.
intros.
induction l as [| a l Hrecl].
simpl in |- *.
auto.
simpl in |- *.
induction (fold_right max 0 (map S l)).
apply le_n_S.
apply le_max_l.
apply le_n_S.
apply maxLemma.
apply le_n.
apply le_S_n.
assumption.
Qed.

Remark boundSubFormulaHelp2 :
 forall (a : fol.Formula L) (v0 : nat) (s : fol.Term L),
 newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a) <=
 S
   (fold_right max 0
      (v0 :: fold_right max 0 (freeVarTerm L s) :: varFormula a)).
intros.
unfold newVar in |- *.
apply
 le_trans
  with (S (fold_right max 0 (v0 :: freeVarTerm L s ++ freeVarFormula L a))).
apply mapListLemma.
apply le_n_S.
simpl in |- *.
apply maxLemma.
apply le_n.
induction (maxApp (freeVarTerm L s) (freeVarFormula L a)).
rewrite a0.
apply le_max_l.
rewrite b.
eapply le_trans.
apply maxVarFreeVar.
apply le_max_r.
Qed.

Remark boundSubFormulaHelp1 :
 forall (b a : fol.Formula L) (v0 v : nat) (s : fol.Term L),
 fold_right max 0
   (varFormula
      (substituteFormula L b v
         (fol.var L (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a))))) <=
 pow3 (depth L b) + pow3 (depth L b) +
 max v0
   (max (fold_right max 0 (freeVarTerm L s))
      (max v
         (max (fold_right max 0 (varFormula b))
            (fold_right max 0 (varFormula a))))).
Proof.
intro.
elim b using Formula_depth_ind2; intros;
 set (nv := newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a)) in *.
simpl in |- *.
apply le_S.
induction
 (maxApp (freeVarTerm L (substituteTerm L t v (fol.var L nv)))
    (freeVarTerm L (substituteTerm L t0 v (fol.var L nv)))).
rewrite a0.
eapply le_trans.
apply maxSubTerm.
simpl in |- *.
apply (max_case2 nv (fold_right max 0 (freeVarTerm L t))).
eapply le_trans.
apply (boundSubFormulaHelp2 a v0 s).
apply le_n_S.
simpl in |- *.
repeat apply maxLemma; try apply le_n.
eapply le_trans; [ idtac | apply le_max_r ].
apply le_max_r.
apply le_S.
do 3 (eapply le_trans; [ idtac | apply le_max_r ]).
eapply le_trans; [ idtac | apply le_max_l ].
apply maxLemma2.
rewrite b0.
eapply le_trans.
apply maxSubTerm.
simpl in |- *.
apply (max_case2 nv (fold_right max 0 (freeVarTerm L t0))).
eapply le_trans.
apply (boundSubFormulaHelp2 a v0 s).
 apply le_n_S.
simpl in |- *.
repeat apply maxLemma; try apply le_n.
eapply le_trans; [ idtac | apply le_max_r ].
apply le_max_r.
apply le_S.
do 3 (eapply le_trans; [ idtac | apply le_max_r ]).
eapply le_trans; [ idtac | apply le_max_l ].
apply maxLemma3.
eapply le_trans.
simpl in |- *.
apply maxSubTerms.
simpl in |- *.
apply le_S.
apply
 (max_case2 nv
    (fold_right max 0 (freeVarTerms L (arity L (inl (Functions L) r)) t))).
eapply le_trans.
apply (boundSubFormulaHelp2 a v0 s).
apply le_n_S.
simpl in |- *.
repeat apply maxLemma; try apply le_n.
eapply le_trans; [ idtac | apply le_max_r ].
apply le_max_r.
apply le_S.
do 3 (eapply le_trans; [ idtac | apply le_max_r ]).
eapply le_trans; [ idtac | apply le_max_l ].
apply le_n.
rewrite subFormulaImp.
simpl in |- *.
induction
 (maxApp (varFormula (substituteFormula L f v (fol.var L nv)))
    (varFormula (substituteFormula L f0 v (fol.var L nv)))).
rewrite a0.
eapply le_trans.
apply (H a v0 v s).
apply plus_le_compat.
eapply le_trans; [ idtac | apply le_plus_l ].
assert (pow3 (depth L f) <= pow3 (max (depth L f) (depth L f0))).
apply pow3Monotone.
apply le_max_l.
apply plus_le_compat.
assumption.
eapply le_trans; [ idtac | apply le_plus_l ].
assumption.
repeat apply maxLemma; try apply le_n.
apply maxLemma2.
rewrite b0.
eapply le_trans.
apply (H0 a v0 v s).
apply plus_le_compat.
eapply le_trans; [ idtac | apply le_plus_l ].
assert (pow3 (depth L f0) <= pow3 (max (depth L f) (depth L f0))).
apply pow3Monotone.
apply le_max_r.
apply plus_le_compat.
assumption.
eapply le_trans; [ idtac | apply le_plus_l ].
assumption.
repeat apply maxLemma; try apply le_n.
apply maxLemma3.
rewrite subFormulaNot.
eapply le_trans.
apply (H a v0 v s).
apply plus_le_compat.
simpl in |- *.
eapply le_trans; [ idtac | apply le_plus_l ].
apply le_plus_r.
apply le_n.
clear nv.
rewrite subFormulaForall.
induction (eq_nat_dec v v1).
eapply le_trans; [ idtac | apply le_plus_r ].
do 3 (eapply le_trans; [ idtac | apply le_max_r ]).
apply le_max_l.
induction
 (In_dec eq_nat_dec v
    (freeVarTerm L
       (fol.var L (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a0))))).
simpl in |- *.
apply
 (max_case2
    (newVar
       (v1
        :: newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a0)
           :: freeVarFormula L a))
    (fold_right max 0
       (varFormula
          (substituteFormula L
             (substituteFormula L a v
                (fol.var L
                   (newVar
                      (v1
                       :: newVar
                            (v0 :: freeVarTerm L s ++ freeVarFormula L a0)
                          :: freeVarFormula L a)))) v1
             (fol.var L
                (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a0))))))).
unfold newVar at 1 in |- *.
eapply le_trans.
apply mapListLemma.
apply
 le_trans
  with
    (1 + 1 +
     max v0
       (max (fold_right max 0 (freeVarTerm L s))
          (max v1
             (max (max v (fold_right max 0 (varFormula a)))
                (fold_right max 0 (varFormula a0)))))).
simpl in |- *.
apply le_n_S.
apply
 (max_case2 v1
    (max (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a0))
       (fold_right max 0 (freeVarFormula L a)))).
apply le_S.
do 2 (eapply le_trans; [ idtac | apply le_max_r ]).
apply le_max_l.
apply
 (max_case2 (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a0))
    (fold_right max 0 (freeVarFormula L a))).
eapply le_trans.
apply boundSubFormulaHelp2.
apply le_n_S.
simpl in |- *.
repeat apply maxLemma; try apply le_n.
eapply le_trans; [ idtac | apply le_max_r ].
apply le_max_r.
apply le_S.
do 3 (eapply le_trans; [ idtac | apply le_max_r ]).
eapply le_trans; [ idtac | apply le_max_l ].
eapply le_trans.
apply maxVarFreeVar.
apply le_max_r.
apply plus_le_compat.
eapply le_trans; [ idtac | apply le_plus_r ].
apply plus_le_compat.
apply pow3Min.
simpl in |- *.
eapply le_trans; [ idtac | apply le_plus_r ].
apply pow3Min.
apply le_n.
eapply le_trans.
apply H.
eapply eqDepth.
symmetry  in |- *.
apply subFormulaDepth.
apply depthForall.
rewrite subFormulaDepth.
rewrite (plus_assoc (pow3 (depth L a)) (pow3 (depth L a)) (pow3 (depth L a))).
repeat rewrite (plus_assoc_reverse (pow3 (depth L a) + pow3 (depth L a))).
apply plus_le_compat.
apply le_n.
apply
 (max_case2 v0
    (max (fold_right max 0 (freeVarTerm L s))
       (max v1
          (max
             (fold_right max 0
                (varFormula
                   (substituteFormula L a v
                      (fol.var L
                         (newVar
                            (v1
                             :: newVar
                                  (v0
                                   :: freeVarTerm L s ++ freeVarFormula L a0)
                                :: freeVarFormula L a))))))
             (fold_right max 0 (varFormula a0)))))).
eapply le_trans; [ idtac | apply le_plus_r ].
apply le_max_l.
apply
 (max_case2 (fold_right max 0 (freeVarTerm L s))
    (max v1
       (max
          (fold_right max 0
             (varFormula
                (substituteFormula L a v
                   (fol.var L
                      (newVar
                         (v1
                          :: newVar
                               (v0 :: freeVarTerm L s ++ freeVarFormula L a0)
                             :: freeVarFormula L a))))))
          (fold_right max 0 (varFormula a0))))).
eapply le_trans; [ idtac | apply le_plus_r ].
eapply le_trans; [ idtac | apply le_max_r ].
apply le_max_l.
apply
 (max_case2 v1
    (max
       (fold_right max 0
          (varFormula
             (substituteFormula L a v
                (fol.var L
                   (newVar
                      (v1
                       :: newVar
                            (v0 :: freeVarTerm L s ++ freeVarFormula L a0)
                          :: freeVarFormula L a))))))
       (fold_right max 0 (varFormula a0)))).
eapply le_trans; [ idtac | apply le_plus_r ].
do 2 (eapply le_trans; [ idtac | apply le_max_r ]).
apply le_max_l.
apply
 (max_case2
    (fold_right max 0
       (varFormula
          (substituteFormula L a v
             (fol.var L
                (newVar
                   (v1
                    :: newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a0)
                       :: freeVarFormula L a))))))
    (fold_right max 0 (varFormula a0))).
eapply le_trans.
apply
 H
  with
    (b := a)
    (v := v)
    (v0 := v1)
    (a := a)
    (s := var (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a0))).
apply depthForall.
rewrite
 (plus_comm (pow3 (depth L a))
    (pow3 (depth L a) + pow3 (depth L a) + pow3 (depth L a)))
 .
repeat rewrite (plus_assoc_reverse (pow3 (depth L a) + pow3 (depth L a))).
apply plus_le_compat.
apply le_n.
apply
 (max_case2 v1
    (max
       (fold_right max 0
          (freeVarTerm L
             (var (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a0)))))
       (max v
          (max (fold_right max 0 (varFormula a))
             (fold_right max 0 (varFormula a)))))).
eapply le_trans; [ idtac | apply le_plus_r ].
do 2 (eapply le_trans; [ idtac | apply le_max_r ]).
apply le_max_l.
apply
 (max_case2
    (fold_right max 0
       (freeVarTerm L
          (var (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a0)))))
    (max v
       (max (fold_right max 0 (varFormula a))
          (fold_right max 0 (varFormula a))))).
simpl in |- *.
apply (max_case2 (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a0)) 0).
eapply le_trans.
apply boundSubFormulaHelp2.
apply
 le_trans
  with
    (1 +
     max v0
       (max (fold_right max 0 (freeVarTerm L s))
          (max v1
             (max (max v (fold_right max 0 (varFormula a)))
                (fold_right max 0 (varFormula a0)))))).
simpl in |- *.
apply le_n_S.
repeat apply maxLemma; try apply le_n.
repeat (eapply le_trans; [ idtac | apply le_max_r ]).
apply le_n.
apply plus_le_compat.
eapply le_trans; [ idtac | apply le_plus_r ].
apply pow3Min.
apply le_n.
apply le_O_n.
eapply le_trans; [ idtac | apply le_plus_r ].
do 3 (eapply le_trans; [ idtac | apply le_max_r ]).
apply
 (max_case2 v
    (max (fold_right max 0 (varFormula a)) (fold_right max 0 (varFormula a)))).
eapply le_trans; [ idtac | apply le_max_l ].
apply le_max_l.
apply
 (max_case2 (fold_right max 0 (varFormula a))
    (fold_right max 0 (varFormula a)));
 (eapply le_trans; [ idtac | apply le_max_l ]; apply le_max_r).
eapply le_trans; [ idtac | apply le_plus_r ].
repeat (eapply le_trans; [ idtac | apply le_max_r ]).
apply le_n.
simpl in |- *.
apply
 (max_case2 v
    (fold_right max 0
       (varFormula
          (substituteFormula L a v1
             (fol.var L
                (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a0))))))).
eapply le_trans; [ idtac | apply le_plus_r ].
do 3 (eapply le_trans; [ idtac | apply le_max_r ]).
eapply le_trans; [ idtac | apply le_max_l ].
apply le_max_l.
eapply le_trans.
apply H.
apply depthForall.
apply plus_le_compat.
eapply le_trans; [ idtac | apply le_plus_r ].
apply plus_le_compat.
apply le_n.
apply le_plus_l.
repeat apply maxLemma; try apply le_n.
apply le_max_r.
Qed.

Remark boundSubFormulaHelp :
 forall (f : fol.Formula L) (v : nat) (s : fol.Term L),
 codeFormula (substituteFormula L f v s) <=
 ReplaceFormulaTerm (codeFormula f)
   (max (codeTerm s)
      (pow3 (depth L f) +
       fold_right max 0 (v :: freeVarTerm L s ++ varFormula f))).
Proof.
intro.
unfold ReplaceFormulaTerm in |- *.
set
 (A :=
  fun f0 recs s0 : nat =>
  switchPR (cPairPi1 f0)
    (switchPR (pred (cPairPi1 f0))
       (switchPR (pred (pred (cPairPi1 f0)))
          (switchPR (pred (pred (pred (cPairPi1 f0))))
             (cPair (cPairPi1 f0) (ReplaceTermsTerm (cPairPi2 f0) s0))
             (cPair 3
                (cPair s0 (codeNth (f0 - S (cPairPi2 (cPairPi2 f0))) recs))))
          (cPair 2 (codeNth (f0 - S (cPairPi2 f0)) recs)))
       (cPair 1
          (cPair (codeNth (f0 - S (cPairPi1 (cPairPi2 f0))) recs)
             (codeNth (f0 - S (cPairPi2 (cPairPi2 f0))) recs))))
    (cPair 0
       (cPair (ReplaceTermTerm (cPairPi1 (cPairPi2 f0)) s0)
          (ReplaceTermTerm (cPairPi2 (cPairPi2 f0)) s0)))) 
 in *.
assert
 (forall n m : nat,
  m < n ->
  extEqual 1
    (evalComposeFunc 1 1 (Vector.cons _ (evalStrongRecHelp 1 A n) 0 (Vector.nil _))
       (fun b : nat => codeNth (n - S m) b)) (evalStrongRec 1 A m)).
intros.
apply (evalStrongRecHelp2 1). 
assumption.
simpl in H.
elim f using Formula_depth_ind2; intros.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
repeat rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
set
 (C :=
  max (codeTerm s)
    (pow3 (depth L (equal L t t0)) +
     fold_right max 0 (v :: freeVarTerm L s ++ varFormula (equal L t t0))))
 in *.
simpl in |- *.
repeat rewrite cPairProjections1.
unfold A at 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
simpl in |- *.
apply cPairLe3.
apply le_n.
apply cPairLe3.
apply
 le_trans
  with
    (ReplaceTermTerm (codeTerm t)
       (fold_right max 0 (codeTerm s :: freeVarTerm L t))).
apply boundSubTerm.
apply ReplaceTermTermMonotone.
unfold C in |- *.
simpl in |- *.
apply maxLemma.
apply le_n.
apply le_S.
eapply le_trans; [ idtac | apply le_max_r ].
eapply le_trans; [ idtac | apply maxLemma3 ].
apply maxLemma2.
apply
 le_trans
  with
    (ReplaceTermTerm (codeTerm t0)
       (fold_right max 0 (codeTerm s :: freeVarTerm L t0))).
apply boundSubTerm.
apply ReplaceTermTermMonotone.
unfold C in |- *.
simpl in |- *.
apply maxLemma.
apply le_n.
apply le_S.
eapply le_trans; [ idtac | apply le_max_r ].
eapply le_trans; [ idtac | apply maxLemma3 ].
apply maxLemma3.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
repeat rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
set
 (C :=
  max (codeTerm s)
    (pow3 (depth L (atomic L r t)) +
     fold_right max 0 (v :: freeVarTerm L s ++ varFormula (atomic L r t))))
 in *.
simpl in |- *.
repeat rewrite cPairProjections1.
unfold A at 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
simpl in |- *.
apply cPairLe3.
apply le_n.
apply
 le_trans
  with
    (ReplaceTermsTerm (codeTerms L codeF _ t)
       (fold_right max 0 (codeTerm s :: freeVarTerms L _ t))).
apply boundSubTerms.
apply ReplaceTermsTermMonotone.
unfold C in |- *.
simpl in |- *.
apply maxLemma.
apply le_n.
apply le_S.
eapply le_trans; [ idtac | apply le_max_r ].
apply maxLemma3.
rewrite subFormulaImp.
set
 (C :=
  max (codeTerm s)
    (pow3 (depth L (impH L f0 f1)) +
     fold_right max 0 (v :: freeVarTerm L s ++ varFormula (impH L f0 f1))))
 in *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
repeat rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
repeat rewrite cPairProjections1.
unfold A at 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
rewrite H with (m := codeFormula f0).
rewrite H with (m := codeFormula f1).
simpl in |- *.
apply cPairLe3.
apply le_n.
apply cPairLe3.
apply
 le_trans
  with
    (evalStrongRec 1 A (codeFormula f0)
       (max (codeTerm s)
          (pow3 (depth L f0) +
           fold_right max 0 (v :: freeVarTerm L s ++ varFormula f0)))).
auto.
apply ReplaceFormulaTermMonotone.
unfold C in |- *.
apply maxLemma.
apply le_n.
apply plus_le_compat.
apply pow3Monotone.
simpl in |- *.
apply le_S.
apply le_max_l.
simpl in |- *.
apply maxLemma.
apply le_n.
rewrite ass_app.
apply maxLemma2.
apply
 le_trans
  with
    (evalStrongRec 1 A (codeFormula f1)
       (max (codeTerm s)
          (pow3 (depth L f1) +
           fold_right max 0 (v :: freeVarTerm L s ++ varFormula f1)))).
auto.
apply ReplaceFormulaTermMonotone.
unfold C in |- *.
apply maxLemma.
apply le_n.
apply plus_le_compat.
apply pow3Monotone.
simpl in |- *.
apply le_S.
apply le_max_r.
simpl in |- *.
apply maxLemma.
apply le_n.
induction (maxApp (freeVarTerm L s) (varFormula f1)).
rewrite a.
apply maxLemma2.
rewrite b.
eapply le_trans; [ idtac | apply maxLemma3 ].
apply maxLemma3.
eapply le_lt_trans; [ idtac | apply cPairLt2 ].
apply cPairLe2.
eapply le_lt_trans; [ idtac | apply cPairLt2 ].
apply cPairLe1.
rewrite subFormulaNot.
set
 (C :=
  max (codeTerm s)
    (pow3 (depth L (notH L f0)) +
     fold_right max 0 (v :: freeVarTerm L s ++ varFormula (notH L f0)))) 
 in *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
repeat rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
repeat rewrite cPairProjections1.
unfold A at 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
rewrite H with (m := codeFormula f0).
simpl in |- *.
apply cPairLe3.
apply le_n.
apply
 le_trans
  with
    (evalStrongRec 1 A (codeFormula f0)
       (max (codeTerm s)
          (pow3 (depth L f0) +
           fold_right max 0 (v :: freeVarTerm L s ++ varFormula f0)))).
auto.
apply ReplaceFormulaTermMonotone.
unfold C in |- *.
apply maxLemma.
apply le_n.
apply plus_le_compat.
apply pow3Monotone.
simpl in |- *.
apply le_n_Sn.
apply le_n.
apply cPairLt2.
set
 (C :=
  max (codeTerm s)
    (pow3 (depth L (forallH L v a)) +
     fold_right max 0 (v0 :: freeVarTerm L s ++ varFormula (forallH L v a))))
 in *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
repeat rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
repeat rewrite cPairProjections1.
unfold A at 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
rewrite H with (m := codeFormula a).
simpl in |- *.
rewrite subFormulaForall.
induction (eq_nat_dec v v0).
simpl in |- *.
apply cPairLe3.
apply le_n.
apply cPairLe3.
unfold C in |- *.
rewrite a0.
eapply le_trans; [ idtac | apply le_max_r ].
eapply le_trans; [ idtac | apply le_plus_r ].
simpl in |- *.
apply le_max_l.
apply le_trans with (codeFormula (substituteFormula L a 0 (var 0))).
rewrite (subFormulaId L).
apply le_n.
apply
 le_trans
  with
    (evalStrongRec 1 A (codeFormula a)
       (max (codeTerm (var 0))
          (pow3 (depth L a) +
           fold_right max 0 (0 :: freeVarTerm L (var 0) ++ varFormula a)))).
apply H0.
apply depthForall.
apply ReplaceFormulaTermMonotone.
unfold C in |- *.
apply maxLemma.
apply le_O_n.
apply plus_le_compat.
apply pow3Monotone.
simpl in |- *.
apply le_n_Sn.
simpl in |- *.
eapply le_trans; [ idtac | apply le_max_r ].
eapply le_trans; [ idtac | apply maxLemma3 ].
simpl in |- *.
apply le_max_r.
induction (In_dec eq_nat_dec v (freeVarTerm L s)).
simpl in |- *.
apply cPairLe3.
apply le_n.
set (nv := newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a)) in *.
apply cPairLe3.
unfold C in |- *.
eapply le_trans; [ idtac | apply le_max_r ].
simpl in |- *.
apply
 le_trans
  with (1 + max v0 (fold_right max 0 (freeVarTerm L s ++ v :: varFormula a))).
simpl in |- *.
unfold nv in |- *.
unfold newVar in |- *.
eapply le_trans.
apply mapListLemma.
apply le_n_S.
simpl in |- *.
apply maxLemma.
apply le_n.
induction (maxApp (freeVarTerm L s) (freeVarFormula L a)).
rewrite a1.
apply maxLemma2.
rewrite b0.
eapply le_trans; [ idtac | apply maxLemma3 ].
simpl in |- *.
eapply le_trans; [ idtac | apply le_max_r ].
apply maxVarFreeVar.
apply plus_le_compat.
eapply le_trans; [ idtac | apply le_plus_l ].
apply pow3Min.
apply le_n.
set (B := substituteFormula L a v (fol.var L nv)) in *.
apply
 le_trans
  with
    (evalStrongRec 1 A (codeFormula B)
       (max (codeTerm s)
          (pow3 (depth L B) +
           fold_right max 0 (v0 :: freeVarTerm L s ++ varFormula B)))).
apply H0.
unfold B in |- *.
eapply eqDepth.
symmetry  in |- *.
apply subFormulaDepth.
apply depthForall.
unfold B at 1 in |- *.
rewrite ReplaceFormulaTermSub.
apply ReplaceFormulaTermMonotone.
simpl in |- *.
unfold B at 1 2 in |- *.
rewrite subFormulaDepth.
unfold C in |- *.
simpl in |- *.
apply maxLemma.
apply le_n.
rewrite plus_assoc_reverse.
apply plus_le_compat_l.
apply
 (max_case2 v0
    (fold_right max 0
       (freeVarTerm L s ++
        varFormula (substituteFormula L a v (fol.var L nv))))).
eapply le_trans; [ idtac | apply le_plus_r ].
apply le_max_l.
induction
 (maxApp (freeVarTerm L s)
    (varFormula (substituteFormula L a v (fol.var L nv)))).
rewrite a1.
eapply le_trans; [ idtac | apply le_plus_r ].
eapply le_trans; [ idtac | apply le_max_r ].
apply maxLemma2.
rewrite b0; clear b0.
clear H0 C B.
unfold nv in |- *.
clear nv.
eapply le_trans.
apply boundSubFormulaHelp1.
apply plus_le_compat.
apply le_n.
repeat apply maxLemma.
apply le_n.
apply max_case2.
apply maxLemma2.
eapply le_trans; [ idtac | apply maxLemma3 ].
simpl in |- *.
apply maxLemma.
apply le_n.
apply max_case2; apply le_n.
simpl in |- *.
apply cPairLe3.
apply le_n.
apply cPairLe3.
unfold C in |- *.
simpl in |- *.
eapply le_trans; [ idtac | apply le_max_r ].
eapply le_trans; [ idtac | apply le_plus_r ].
eapply le_trans; [ idtac | apply le_max_r ].
eapply le_trans; [ idtac | apply maxLemma3 ].
simpl in |- *.
apply le_max_l.
eapply le_trans.
apply H0.
apply depthForall.
apply ReplaceFormulaTermMonotone.
unfold C in |- *.
apply maxLemma.
apply le_n.
apply plus_le_compat.
simpl in |- *.
apply le_plus_l.
simpl in |- *.
apply maxLemma.
apply le_n.
induction (maxApp (freeVarTerm L s) (varFormula a)).
rewrite a0.
apply maxLemma2.
rewrite b1.
eapply le_trans; [ idtac | apply maxLemma3 ].
simpl in |- *.
apply le_max_r.
eapply le_lt_trans; [ idtac | apply cPairLt2 ].
apply cPairLe2.
Qed.

Definition boundComputation (d p1 p2 : nat) : nat :=
  nat_rec (fun _ => nat) (cTriple p1 p2 0)
    (fun _ rec : nat => cTriple p1 p2 (cPair rec rec)) d.

Lemma boundComputationIsPR : isPR 3 boundComputation.
Proof.
unfold boundComputation in |- *.
apply
 ind2ParamIsPR
  with
    (f := fun _ rec p1 p2 : nat => cTriple p1 p2 (cPair rec rec))
    (g := fun p1 p2 : nat => cTriple p1 p2 0).
apply
 compose4_3IsPR
  with
    (f1 := fun _ rec p1 p2 : nat => p1)
    (f2 := fun _ rec p1 p2 : nat => p2)
    (f3 := fun _ rec p1 p2 : nat => cPair rec rec).
apply pi3_4IsPR.
apply pi4_4IsPR.
apply filter1100IsPR with (g := fun _ rec : nat => cPair rec rec).
apply filter01IsPR with (g := fun rec : nat => cPair rec rec).
apply
 compose1_2IsPR with (f := fun rec : nat => rec) (f' := fun rec : nat => rec).
apply idIsPR.
apply idIsPR.
apply cPairIsPR.
apply cTripleIsPR.
apply
 compose2_3IsPR
  with
    (f1 := fun p1 p2 : nat => p1)
    (f2 := fun p1 p2 : nat => p2)
    (f3 := fun p1 p2 : nat => 0).
apply pi1_2IsPR.
apply pi2_2IsPR.
apply filter10IsPR with (g := fun _ : nat => 0).
apply const1_NIsPR.
apply cTripleIsPR.
Qed.

Lemma boundComputationMonotone :
 forall a1 a2 b1 b2 c1 c2 : nat,
 a1 <= a2 ->
 b1 <= b2 ->
 c1 <= c2 -> boundComputation a1 b1 c1 <= boundComputation a2 b2 c2.
Proof.
intros a1 a2.
generalize a1.
clear a1.
unfold boundComputation in |- *.
induction a2 as [| a2 Hreca2]; simpl in |- *; intros.
rewrite <- (le_n_O_eq _ H).
simpl in |- *.
unfold cTriple in |- *.
apply cPairLe3.
assumption.
apply cPairLe3.
assumption.
apply le_n.
induction (le_lt_or_eq _ _ H).
eapply le_trans.
apply (Hreca2 a1 b1 b2 c1 c2); try assumption.
apply lt_n_Sm_le.
assumption.
unfold cTriple at 3 in |- *.
eapply le_trans; [ idtac | apply cPairLe2 ].
eapply le_trans; [ idtac | apply cPairLe2 ].
apply cPairLe2.
rewrite H2.
simpl in |- *.
unfold cTriple at 6 1 in |- *.
apply cPairLe3.
assumption.
apply cPairLe3.
assumption.
apply cPairLe3; apply Hreca2; apply le_n || assumption.
Qed.

Lemma boundMakeTrace :
 forall (f : fol.Formula L) (v : nat) (s : fol.Term L),
 let C :=
   max (codeTerm s)
     (cPair 0
        (pow3 (depth L f) +
         fold_right max 0 (v :: freeVarTerm L s ++ varFormula f))) in
 makeTrace f (v, s) <=
 boundComputation (depth L f)
   (cTriple C C (ReplaceFormulaTerm (codeFormula f) C))
   (ReplaceFormulaTerm (codeFormula f) C).
Proof.
set
 (A :=
  fun f2 recs s0 : nat =>
  switchPR (cPairPi1 f2)
    (switchPR (pred (cPairPi1 f2))
       (switchPR (pred (pred (cPairPi1 f2)))
          (switchPR (pred (pred (pred (cPairPi1 f2))))
             (cPair (cPairPi1 f2) (ReplaceTermsTerm (cPairPi2 f2) s0))
             (cPair 3
                (cPair s0 (codeNth (f2 - S (cPairPi2 (cPairPi2 f2))) recs))))
          (cPair 2 (codeNth (f2 - S (cPairPi2 f2)) recs)))
       (cPair 1
          (cPair (codeNth (f2 - S (cPairPi1 (cPairPi2 f2))) recs)
             (codeNth (f2 - S (cPairPi2 (cPairPi2 f2))) recs))))
    (cPair 0
       (cPair (ReplaceTermTerm (cPairPi1 (cPairPi2 f2)) s0)
          (ReplaceTermTerm (cPairPi2 (cPairPi2 f2)) s0)))) 
 in *.
assert
 (E :
  forall (f : fol.Formula L) (v : nat) (s : fol.Term L),
  codeFormula (substituteFormula L f v s) <=
  ReplaceFormulaTerm (codeFormula f)
    (max (codeTerm s)
       (cPair 0
          (pow3 (depth L f) +
           fold_right max 0 (v :: freeVarTerm L s ++ varFormula f))))).
intros.
eapply le_trans.
apply boundSubFormulaHelp.
apply ReplaceFormulaTermMonotone.
apply maxLemma.
apply le_n.
apply cPairLe2.
assert
 (D :
  forall n m : nat,
  m < n ->
  extEqual 1
    (evalComposeFunc 1 1 (Vector.cons _ (evalStrongRecHelp 1 A n) 0 (Vector.nil _))
       (fun b : nat => codeNth (n - S m) b)) (evalStrongRec 1 A m)).
intros.
apply (evalStrongRecHelp2 1). 
assumption.
simpl in D.
intro.
assert (forall w v n s : nat, v <= max s (cPair 0 (w + max v n))).
intros.
eapply le_trans; [ idtac | apply le_max_r ].
eapply le_trans; [ idtac | apply cPairLe2 ].
eapply le_trans; [ idtac | apply le_plus_r ].
apply le_max_l.
assert
 (forall (f : fol.Formula L) (v : nat) (s : fol.Term L),
  codeFormula f <=
  ReplaceFormulaTerm (codeFormula f)
    (max (codeTerm s)
       (cPair 0
          (pow3 (depth L f) +
           fold_right max 0 (v :: freeVarTerm L s ++ varFormula f))))).
intros.
apply le_trans with (codeFormula (substituteFormula L f0 0 (var 0))).
rewrite (subFormulaId L).
apply le_n.
eapply le_trans.
apply E.
apply ReplaceFormulaTermMonotone.
apply maxLemma.
apply le_O_n.
apply cPairLe3.
apply le_n.
apply plus_le_compat.
apply le_n.
simpl in |- *.
eapply le_trans; [ idtac | apply le_max_r ].
apply maxLemma3.
elim f using Formula_depth_ind2; intros; simpl in |- *.
unfold makeTrace in |- *.
unfold Formula_depth_rec2 in |- *.
unfold Formula_depth_rec in |- *.
simpl in |- *.
unfold cTriple in |- *.
unfold C in |- *.
simpl in |- *.
repeat apply cPairLe3.
apply
 (H 1 v
    (fold_right max 0
       (freeVarTerm L s ++ freeVarTerm L t ++ freeVarTerm L t0)) 
    (codeTerm s)).
apply le_max_l.
apply (H0 (equal L t t0) v s).
apply (E (equal L t t0) v s).
apply le_n.
unfold makeTrace in |- *.
unfold Formula_depth_rec2 in |- *.
unfold Formula_depth_rec in |- *.
simpl in |- *.
unfold cTriple in |- *.
unfold C in |- *.
simpl in |- *.
repeat apply cPairLe3.
apply
 (H 1 v
    (fold_right max 0
       (freeVarTerm L s ++ freeVarTerms L (arity L (inl (Functions L) r)) t))
    (codeTerm s)).
apply le_max_l.
apply (H0 (atomic L r t) v s).
apply (E (atomic L r t) v s).
apply le_n.
replace (makeTrace (impH L f0 f1) (v, s)) with
 (cTriple (cTriple v (codeTerm s) (codeFormula (impH L f0 f1)))
    (codeFormula (substituteFormula L (impH L f0 f1) v s))
    (cPair (makeTrace f0 (v, s)) (makeTrace f1 (v, s)))).
unfold cTriple in |- *.
repeat apply cPairLe3.
unfold C in |- *; simpl in |- *. 
apply
 (H
    (pow3 (max (depth L f0) (depth L f1)) +
     (pow3 (max (depth L f0) (depth L f1)) +
      pow3 (max (depth L f0) (depth L f1)))) v
    (fold_right max 0 (freeVarTerm L s ++ varFormula f0 ++ varFormula f1))
    (codeTerm s)).
unfold C in |- *; simpl in |- *. 
apply le_max_l.
apply (H0 (impH L f0 f1) v s).
apply (E (impH L f0 f1) v s).
eapply le_trans.
apply H1.
assert
 (max (codeTerm s)
    (cPair 0
       (pow3 (depth L f0) +
        fold_right max 0 (v :: freeVarTerm L s ++ varFormula f0))) <= C).
unfold C in |- *.
apply maxLemma.
apply le_n.
apply cPairLe3.
apply le_n.
apply plus_le_compat.
apply pow3Monotone.
simpl in |- *.
apply le_S.
apply le_max_l.
simpl in |- *.
apply max_case2.
apply le_max_l.
eapply le_trans; [ idtac | apply le_max_r ].
induction (maxApp (freeVarTerm L s) (varFormula f0)).
rewrite a.
apply maxLemma2.
rewrite b.
eapply le_trans; [ idtac | apply maxLemma3 ].
apply maxLemma2.
assert
 (ReplaceFormulaTerm (codeFormula f0)
    (max (codeTerm s)
       (cPair 0
          (pow3 (depth L f0) +
           fold_right max 0 (v :: freeVarTerm L s ++ varFormula f0)))) <=
  ReplaceFormulaTerm (cPair 1 (cPair (codeFormula f0) (codeFormula f1))) C).
unfold ReplaceFormulaTerm at 2 in |- *.
fold A in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
repeat rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
unfold A at 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
rewrite D with (m := codeFormula f0).
simpl in |- *.
eapply le_trans; [ idtac | apply cPairLe2 ].
eapply le_trans; [ idtac | apply cPairLe1 ].
apply ReplaceFormulaTermMonotone.
apply H3.
eapply le_lt_trans; [ idtac | apply cPairLt2 ].
apply cPairLe1.
apply boundComputationMonotone.
apply le_max_l.
unfold cTriple in |- *.
repeat apply cPairLe3.
apply H3.
apply H3.
apply H4.
apply H4.
eapply le_trans.
apply H2.
assert
 (max (codeTerm s)
    (cPair 0
       (pow3 (depth L f1) +
        fold_right max 0 (v :: freeVarTerm L s ++ varFormula f1))) <= C).
unfold C in |- *.
apply maxLemma.
apply le_n.
apply cPairLe3.
apply le_n.
apply plus_le_compat.
apply pow3Monotone.
simpl in |- *.
apply le_S.
apply le_max_r.
simpl in |- *.
apply max_case2.
apply le_max_l.
eapply le_trans; [ idtac | apply le_max_r ].
induction (maxApp (freeVarTerm L s) (varFormula f1)).
rewrite a.
apply maxLemma2.
rewrite b.
eapply le_trans; [ idtac | apply maxLemma3 ].
apply maxLemma3.
assert
 (ReplaceFormulaTerm (codeFormula f1)
    (max (codeTerm s)
       (cPair 0
          (pow3 (depth L f1) +
           fold_right max 0 (v :: freeVarTerm L s ++ varFormula f1)))) <=
  ReplaceFormulaTerm (cPair 1 (cPair (codeFormula f0) (codeFormula f1))) C).
unfold ReplaceFormulaTerm at 2 in |- *.
fold A in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
repeat rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
unfold A at 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
rewrite D with (m := codeFormula f1).
simpl in |- *.
eapply le_trans; [ idtac | apply cPairLe2 ].
eapply le_trans; [ idtac | apply cPairLe2 ].
apply ReplaceFormulaTermMonotone.
apply H3.
eapply le_lt_trans; [ idtac | apply cPairLt2 ].
apply cPairLe2.
apply boundComputationMonotone.
apply le_max_r.
unfold cTriple in |- *.
repeat apply cPairLe3.
apply H3.
apply H3.
apply H4.
apply H4.
unfold makeTrace in |- *.
rewrite
 (Formula_depth_rec2_imp L)
                            with
                            (Q := 
                              fun _ : fol.Formula L =>
                              (nat * fol.Term L)%type)
                           (P := fun _ : fol.Formula L => nat).
unfold makeTraceImp at 1 in |- *.
reflexivity.
apply makeTraceImpNice.
apply makeTraceNotNice.
apply makeTraceForallNice.
replace (makeTrace (notH L f0) (v, s)) with
 (cTriple (cTriple v (codeTerm s) (codeFormula (notH L f0)))
    (codeFormula (substituteFormula L (notH L f0) v s)) 
    (makeTrace f0 (v, s))).
unfold cTriple in |- *.
repeat apply cPairLe3.
unfold C in |- *; simpl in |- *. 
apply
 (H (pow3 (depth L f0) + (pow3 (depth L f0) + pow3 (depth L f0))) v
    (fold_right max 0 (freeVarTerm L s ++ varFormula f0)) 
    (codeTerm s)).
unfold C in |- *; simpl in |- *. 
apply le_max_l.
apply (H0 (notH L f0) v s).
apply (E (notH L f0) v s).
eapply le_trans.
apply H1.
assert
 (max (codeTerm s)
    (cPair 0
       (pow3 (depth L f0) +
        fold_right max 0 (v :: freeVarTerm L s ++ varFormula f0))) <= C).
unfold C in |- *; simpl in |- *.
apply maxLemma.
apply le_n.
apply cPairLe3.
apply le_n.
apply plus_le_compat.
apply le_plus_l.
apply le_n.
assert
 (ReplaceFormulaTerm (codeFormula f0)
    (max (codeTerm s)
       (cPair 0
          (pow3 (depth L f0) +
           fold_right max 0 (v :: freeVarTerm L s ++ varFormula f0)))) <=
  ReplaceFormulaTerm (cPair 2 (codeFormula f0)) C).
unfold ReplaceFormulaTerm at 2 in |- *.
fold A in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
repeat rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
unfold A at 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
rewrite D with (m := codeFormula f0).
simpl in |- *.
eapply le_trans; [ idtac | apply cPairLe2 ].
apply ReplaceFormulaTermMonotone.
apply H2.
apply cPairLt2.
eapply le_trans; [ idtac | apply cPairLe1 ].
apply boundComputationMonotone.
apply le_n.
unfold cTriple in |- *.
repeat apply cPairLe3.
apply H2.
apply H2.
apply H3.
apply H3.
unfold makeTrace in |- *.
rewrite
 (Formula_depth_rec2_not L)
                            with
                            (Q := 
                              fun _ : fol.Formula L =>
                              (nat * fol.Term L)%type)
                           (P := fun _ : fol.Formula L => nat).
unfold makeTraceNot at 1 in |- *.
reflexivity.
apply makeTraceImpNice.
apply makeTraceNotNice.
apply makeTraceForallNice.
replace (makeTrace (forallH L v a) (v0, s)) with
 (makeTraceForall v a (fun (b : fol.Formula L) _ => makeTrace b) (v0, s)).
unfold makeTraceForall in |- *.
simpl in |- *.
induction (eq_nat_dec v v0); simpl in |- *.
unfold cTriple in |- *.
repeat apply cPairLe3.
unfold C in |- *; simpl in |- *. 
apply
 (H (pow3 (depth L a) + (pow3 (depth L a) + pow3 (depth L a))) v0
    (fold_right max 0 (freeVarTerm L s ++ v :: varFormula a)) 
    (codeTerm s)).
unfold C in |- *; simpl in |- *. 
apply le_max_l.
apply (H0 (forallH L v a) v0 s).
apply (E (forallH L v a) v0 s).
apply le_O_n.
induction (In_dec eq_nat_dec v (freeVarTerm L s)); simpl in |- *.
unfold cTriple in |- *.
repeat apply cPairLe3.
unfold C in |- *; simpl in |- *. 
apply
 (H (pow3 (depth L a) + (pow3 (depth L a) + pow3 (depth L a))) v0
    (fold_right max 0 (freeVarTerm L s ++ v :: varFormula a)) 
    (codeTerm s)).
unfold C in |- *; simpl in |- *. 
apply le_max_l.
apply (H0 (forallH L v a) v0 s).
apply (E (forallH L v a) v0 s).
eapply le_trans.
apply H1.
apply depthForall.
assert
 (max (codeTerm (var (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a))))
    (cPair 0
       (pow3 (depth L a) +
        fold_right max 0
          (v
           :: freeVarTerm L
                (var (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a))) ++
              varFormula a))) <= C).
assert
 (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a) <=
  pow3 (depth L a) +
  fold_right max 0 (v0 :: freeVarTerm L s ++ varFormula (forallH L v a))).
apply
 le_trans
  with
    (1 +
     fold_right max 0
       (v0 :: fold_right max 0 (freeVarTerm L s) :: varFormula a)).
apply boundSubFormulaHelp2 with (a := a) (v0 := v0) (s := s).
apply plus_le_compat.
apply pow3Min.
simpl in |- *.
apply max_case2.
apply le_max_l.
eapply le_trans; [ idtac | apply le_max_r ].
apply max_case2.
apply maxLemma2.
eapply le_trans; [ idtac | apply maxLemma3 ].
simpl in |- *.
apply le_max_r.
apply max_case2.
replace
 (codeTerm (var (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a)))) with
 (cPair 0 (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a)));
 [ idtac | reflexivity ].
unfold C in |- *.
eapply le_trans; [ idtac | apply le_max_r ].
apply cPairLe3.
apply le_n.
eapply le_trans.
apply H2.
apply plus_le_compat_r.
simpl in |- *.
apply le_plus_l.
unfold C in |- *.
eapply le_trans; [ idtac | apply le_max_r ].
apply cPairLe3.
apply le_n.
simpl in |- *.
rewrite plus_assoc_reverse.
apply plus_le_compat_l.
apply max_case2.
eapply le_trans; [ idtac | apply le_plus_r ].
eapply le_trans; [ idtac | apply le_max_r ].
eapply le_trans; [ idtac | apply maxLemma3 ].
simpl in |- *.
apply le_max_l.
apply max_case2.
rewrite plus_assoc_reverse.
eapply le_trans; [ idtac | apply le_plus_r ].
apply H2.
eapply le_trans; [ idtac | apply le_plus_r ].
eapply le_trans; [ idtac | apply le_max_r ].
eapply le_trans; [ idtac | apply maxLemma3 ].
simpl in |- *.
apply le_max_r.
assert
 (ReplaceFormulaTerm (codeFormula a)
    (max
       (codeTerm (var (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a))))
       (cPair 0
          (pow3 (depth L a) +
           fold_right max 0
             (v
              :: freeVarTerm L
                   (var
                      (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a))) ++
                 varFormula a)))) <=
  ReplaceFormulaTerm (cPair 3 (cPair v (codeFormula a))) C).
unfold ReplaceFormulaTerm at 2 in |- *.
fold A in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
repeat rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
unfold A at 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
rewrite D with (m := codeFormula a).
simpl in |- *.
eapply le_trans; [ idtac | apply cPairLe2 ].
eapply le_trans; [ idtac | apply cPairLe2 ].
apply ReplaceFormulaTermMonotone.
simpl in H2.
apply H2.
eapply le_lt_trans; [ idtac | apply cPairLt2 ].
apply cPairLe2.
apply boundComputationMonotone.
apply le_n.
unfold cTriple in |- *.
repeat apply cPairLe3.
apply H2.
apply H2.
apply H3.
apply H3.
eapply le_trans.
apply H1.
eapply eqDepth.
symmetry  in |- *.
apply subFormulaDepth.
apply depthForall.
rewrite subFormulaDepth.
assert
 (max (codeTerm s)
    (cPair 0
       (pow3 (depth L a) +
        fold_right max 0
          (v0
           :: freeVarTerm L s ++
              varFormula
                (substituteFormula L a v
                   (var
                      (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a))))))) <=
  C).
unfold C in |- *.
apply maxLemma.
apply le_n.
apply cPairLe3.
apply le_n.
simpl in |- *.
rewrite plus_assoc_reverse.
apply plus_le_compat_l.
apply max_case2.
eapply le_trans; [ idtac | apply le_plus_r ].
apply le_max_l.
induction
 (maxApp (freeVarTerm L s)
    (varFormula
       (substituteFormula L a v
          (var (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a)))))).
rewrite a1.
eapply le_trans; [ idtac | apply le_plus_r ].
eapply le_trans; [ idtac | apply le_max_r ].
apply maxLemma2.
rewrite b0.
clear b0.
eapply le_trans.
apply boundSubFormulaHelp1.
apply plus_le_compat_l.
apply maxLemma.
apply le_n.
apply max_case2.
apply maxLemma2.
eapply le_trans; [ idtac | apply maxLemma3 ].
simpl in |- *.
apply maxLemma.
apply le_n.
apply max_case2; apply le_n.
assert
 (ReplaceFormulaTerm
    (codeFormula
       (substituteFormula L a v
          (var (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a)))))
    (max (codeTerm s)
       (cPair 0
          (pow3 (depth L a) +
           fold_right max 0
             (v0
              :: freeVarTerm L s ++
                 varFormula
                   (substituteFormula L a v
                      (var
                         (newVar
                            (v0 :: freeVarTerm L s ++ freeVarFormula L a)))))))) <=
  ReplaceFormulaTerm (cPair 3 (cPair v (codeFormula a))) C).
unfold ReplaceFormulaTerm at 2 in |- *.
fold A in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
repeat rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
unfold A at 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
rewrite D with (m := codeFormula a).
simpl in |- *.
eapply le_trans; [ idtac | apply cPairLe2 ].
eapply le_trans; [ idtac | apply cPairLe2 ].
rewrite ReplaceFormulaTermSub.
apply ReplaceFormulaTermMonotone.
apply H2.
eapply le_lt_trans; [ idtac | apply cPairLt2 ].
apply cPairLe2.
apply boundComputationMonotone.
apply le_n.
unfold cTriple in |- *.
repeat apply cPairLe3.
apply H2.
apply H2.
apply H3.
apply H3.
unfold cTriple in |- *.
repeat apply cPairLe3.
unfold C in |- *; simpl in |- *. 
apply
 (H (pow3 (depth L a) + (pow3 (depth L a) + pow3 (depth L a))) v0
    (fold_right max 0 (freeVarTerm L s ++ v :: varFormula a)) 
    (codeTerm s)).
unfold C in |- *; simpl in |- *. 
apply le_max_l.
apply (H0 (forallH L v a) v0 s).
apply (E (forallH L v a) v0 s).
eapply le_trans.
apply H1.
apply depthForall.
assert
 (max (codeTerm s)
    (cPair 0
       (pow3 (depth L a) +
        fold_right max 0 (v0 :: freeVarTerm L s ++ varFormula a))) <= C).
unfold C in |- *.
apply maxLemma.
apply le_n.
apply cPairLe3.
apply le_n.
apply plus_le_compat.
simpl in |- *.
apply le_plus_l.
simpl in |- *.
apply maxLemma.
apply le_n.
induction (maxApp (freeVarTerm L s) (varFormula a)).
rewrite a0.
apply maxLemma2.
rewrite b1.
eapply le_trans; [ idtac | apply maxLemma3 ].
simpl in |- *.
apply le_max_r.
assert
 (ReplaceFormulaTerm (codeFormula a)
    (max (codeTerm s)
       (cPair 0
          (pow3 (depth L a) +
           fold_right max 0 (v0 :: freeVarTerm L s ++ varFormula a)))) <=
  ReplaceFormulaTerm (cPair 3 (cPair v (codeFormula a))) C).
unfold ReplaceFormulaTerm at 2 in |- *.
fold A in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
repeat rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
unfold A at 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
rewrite D with (m := codeFormula a).
simpl in |- *.
eapply le_trans; [ idtac | apply cPairLe2 ].
eapply le_trans; [ idtac | apply cPairLe2 ].
apply ReplaceFormulaTermMonotone.
apply H2.
eapply le_lt_trans; [ idtac | apply cPairLt2 ].
apply cPairLe2.
eapply le_trans; [ idtac | apply cPairLe1 ].
apply boundComputationMonotone.
apply le_n.
unfold cTriple in |- *.
repeat apply cPairLe3.
apply H2.
apply H2.
apply H3.
apply H3.
unfold makeTrace in |- *.
rewrite
 (Formula_depth_rec2_forall L)
                               with
                               (Q := 
                                 fun _ : fol.Formula L =>
                                 (nat * fol.Term L)%type)
                              (P := fun _ : fol.Formula L => nat).
unfold makeTraceForall at 1 in |- *.
reflexivity.
apply makeTraceImpNice.
apply makeTraceNotNice.
apply makeTraceForallNice.
Qed.

Definition codeSubFormula (f v s : nat) : nat :=
  let C := cPair 0 (pow3 f + (v + (s + f))) in
  cPairPi1
    (boundedSearch
       (fun p x : nat =>
        ltBool 0 (checkSubFormulaTrace (cPair (cPairPi1 p) x)))
       (cPair (cTriple v s f)
          (S
             (boundComputation f (cTriple C C (ReplaceFormulaTerm f C))
                (ReplaceFormulaTerm f C))))).

Lemma codeSubFormulaCorrect :
 forall (f : Formula) (v : nat) (s : Term),
 codeSubFormula (codeFormula f) v (codeTerm s) =
 codeFormula (substituteFormula L f v s).
Proof.
intros.
unfold codeSubFormula in |- *.
set
 (P :=
  fun p x : nat => ltBool 0 (checkSubFormulaTrace (cPair (cPairPi1 p) x)))
 in *.
set
 (b :=
  boundComputation (codeFormula f)
    (cTriple
       (cPair 0 (pow3 (codeFormula f) + (v + (codeTerm s + codeFormula f))))
       (cPair 0 (pow3 (codeFormula f) + (v + (codeTerm s + codeFormula f))))
       (ReplaceFormulaTerm (codeFormula f)
          (cPair 0
             (pow3 (codeFormula f) + (v + (codeTerm s + codeFormula f))))))
    (ReplaceFormulaTerm (codeFormula f)
       (cPair 0 (pow3 (codeFormula f) + (v + (codeTerm s + codeFormula f))))))
 in *.
induction
 (boundedSearch2 P (cPair (cTriple v (codeTerm s) (codeFormula f)) (S b))).
assert
 (P (cPair (cTriple v (codeTerm s) (codeFormula f)) (S b))
    (cPairPi2 (makeTrace f (v, s))) = true).
unfold P in |- *. 
rewrite cPairProjections1.
replace
 (cPair (cTriple v (codeTerm s) (codeFormula f))
    (cPairPi2 (makeTrace f (v, s)))) with (makeTrace f (v, s)).
rewrite makeTraceCorrect.
unfold ltBool in |- *.
induction (le_lt_dec 1 0).
elim (lt_not_le _ _ a).
apply le_n.
reflexivity.
transitivity
 (cPair (cPairPi1 (makeTrace f (v, s))) (cPairPi2 (makeTrace f (v, s)))).
symmetry  in |- *.
apply cPairProjections.
rewrite makeTrace1.
reflexivity.
assert
 (P (cPair (cTriple v (codeTerm s) (codeFormula f)) (S b))
    (cPairPi2 (makeTrace f (v, s))) = false).
apply boundedSearch1.
rewrite H.
eapply lt_le_trans; [ idtac | apply cPairLe2 ].
apply le_lt_n_Sm.
eapply
 le_trans
          with
          (cPair (cPairPi1 (makeTrace f (v, s)))
             (cPairPi2 (makeTrace f (v, s)))).
apply cPairLe2.
rewrite cPairProjections.
eapply le_trans.
apply boundMakeTrace.
unfold b in |- *.
assert (depth L f <= codeFormula f).
clear H0 H b P s v.
induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf];
 simpl in |- *.
apply le_O_n.
apply le_O_n.
apply lt_n_Sm_le.
apply lt_n_S.
eapply le_lt_trans; [ idtac | apply cPairLt2 ].
apply max_case2.
eapply le_trans.
apply Hrecf1.
apply cPairLe1.
eapply le_trans.
apply Hrecf0.
apply cPairLe2.
apply lt_n_Sm_le.
apply lt_n_S.
eapply le_lt_trans; [ idtac | apply cPairLt2 ].
assumption.
apply lt_n_Sm_le.
apply lt_n_S.
eapply le_lt_trans; [ idtac | apply cPairLt2 ].
eapply le_trans.
apply Hrecf.
apply cPairLe2.
assert
 (max (codeTerm s)
    (cPair 0
       (pow3 (depth L f) +
        fold_right max 0 (v :: freeVarTerm L s ++ varFormula f))) <=
  cPair 0 (pow3 (codeFormula f) + (v + (codeTerm s + codeFormula f)))).
apply max_case2.
eapply le_trans; [ idtac | apply cPairLe2 ].
eapply le_trans; [ idtac | apply le_plus_r ].
eapply le_trans; [ idtac | apply le_plus_r ].
apply le_plus_l.
apply cPairLe3.
apply le_n.
apply plus_le_compat.
apply pow3Monotone.
assumption.
simpl in |- *.
apply max_case2.
apply le_plus_l.
eapply le_trans; [ idtac | apply le_plus_r ].
induction (maxApp (freeVarTerm L s) (varFormula f)).
rewrite a.
eapply le_trans.
apply codeTermFreeVar.
apply le_plus_l.
rewrite b0.
eapply le_trans with (codeFormula f).
clear b0 H1 H0 H b P s v.
induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf];
 simpl in |- *.
eapply le_trans; [ idtac | apply cPairLe2 ].
induction (maxApp (freeVarTerm L t) (freeVarTerm L t0)).
rewrite a.
eapply le_trans.
apply codeTermFreeVar.
apply cPairLe1.
rewrite b.
eapply le_trans.
apply codeTermFreeVar.
apply cPairLe2.
eapply le_trans; [ idtac | apply cPairLe2 ].
induction t as [| n t t0 Hrect].
simpl in |- *.
apply le_O_n.
replace (freeVarTerms L (S n) (Tcons L n t t0)) with
 (freeVarTerm L t ++ freeVarTerms L n t0); [ idtac | reflexivity ].
replace (codeTerms L codeF (S n) (Tcons L n t t0)) with
 (S (cPair (codeTerm t) (codeTerms L codeF n t0))); 
 [ idtac | reflexivity ].
apply le_S.
induction (maxApp (freeVarTerm L t) (freeVarTerms L n t0)).
rewrite a.
eapply le_trans.
apply codeTermFreeVar.
apply cPairLe1.
rewrite b.
eapply le_trans.
apply Hrect.
apply cPairLe2.
eapply le_trans; [ idtac | apply cPairLe2 ].
induction (maxApp (varFormula f1) (varFormula f0)).
rewrite a.
eapply le_trans.
apply Hrecf1.
apply cPairLe1.
rewrite b.
eapply le_trans.
apply Hrecf0.
apply cPairLe2.
eapply le_trans.
apply Hrecf.
apply cPairLe2.
eapply le_trans; [ idtac | apply cPairLe2 ].
apply max_case2.
apply cPairLe1.
eapply le_trans.
apply Hrecf.
apply cPairLe2.
apply le_plus_r.
apply boundComputationMonotone.
assumption.
unfold cTriple in |- *.
repeat apply cPairLe3.
assumption.
assumption.
apply ReplaceFormulaTermMonotone.
assumption.
apply ReplaceFormulaTermMonotone.
assumption.
rewrite H0 in H1.
discriminate H1.
unfold P at 1 in H.
rewrite cPairProjections1 in H.
symmetry  in |- *.
apply
 checkTraceCorrect
  with
    (m := cPairPi2
            (boundedSearch P
               (cPair (cTriple v (codeTerm s) (codeFormula f)) (S b)))).
unfold not in |- *; intros.
unfold cTriple at 1 in H0.
rewrite cPairProjections in H0.
rewrite H0 in H.
elim (lt_not_le 0 0).
apply ltBoolTrue.
assumption.
apply le_n.
Qed.

Lemma codeSubFormulaIsPR : isPR 3 codeSubFormula.
Proof.
unfold codeSubFormula in |- *.
apply
 compose3_1IsPR
  with
    (f := fun f v s : nat =>
          boundedSearch
            (fun p x : nat =>
             ltBool 0 (checkSubFormulaTrace (cPair (cPairPi1 p) x)))
            (cPair (cTriple v s f)
               (S
                  (boundComputation f
                     (cTriple (cPair 0 (pow3 f + (v + (s + f))))
                        (cPair 0 (pow3 f + (v + (s + f))))
                        (ReplaceFormulaTerm f
                           (cPair 0 (pow3 f + (v + (s + f))))))
                     (ReplaceFormulaTerm f (cPair 0 (pow3 f + (v + (s + f))))))))).
apply
 compose3_1IsPR
  with
    (f := fun f v s : nat =>
          cPair (cTriple v s f)
            (S
               (boundComputation f
                  (cTriple (cPair 0 (pow3 f + (v + (s + f))))
                     (cPair 0 (pow3 f + (v + (s + f))))
                     (ReplaceFormulaTerm f (cPair 0 (pow3 f + (v + (s + f))))))
                  (ReplaceFormulaTerm f (cPair 0 (pow3 f + (v + (s + f)))))))).
apply
 compose3_2IsPR
  with
    (f1 := fun f v s : nat => cTriple v s f)
    (f2 := fun f v s : nat =>
           S
             (boundComputation f
                (cTriple (cPair 0 (pow3 f + (v + (s + f))))
                   (cPair 0 (pow3 f + (v + (s + f))))
                   (ReplaceFormulaTerm f (cPair 0 (pow3 f + (v + (s + f))))))
                (ReplaceFormulaTerm f (cPair 0 (pow3 f + (v + (s + f))))))).
apply
 compose3_3IsPR
  with
    (f1 := fun f v s : nat => v)
    (f2 := fun f v s : nat => s)
    (f3 := fun f v s : nat => f).
apply pi2_3IsPR.
apply pi3_3IsPR.
apply pi1_3IsPR.
apply cTripleIsPR.
apply
 compose3_1IsPR
  with
    (f := fun f v s : nat =>
          boundComputation f
            (cTriple (cPair 0 (pow3 f + (v + (s + f))))
               (cPair 0 (pow3 f + (v + (s + f))))
               (ReplaceFormulaTerm f (cPair 0 (pow3 f + (v + (s + f))))))
            (ReplaceFormulaTerm f (cPair 0 (pow3 f + (v + (s + f)))))).
assert (isPR 3 (fun f v s : nat => cPair 0 (pow3 f + (v + (s + f))))).
apply
 compose3_2IsPR
  with
    (f1 := fun f v s : nat => 0)
    (f2 := fun f v s : nat => pow3 f + (v + (s + f))).
apply filter100IsPR with (g := fun _ : nat => 0).
apply const1_NIsPR.
apply
 compose3_2IsPR
  with
    (f1 := fun f v s : nat => pow3 f)
    (f2 := fun f v s : nat => v + (s + f)).
apply filter100IsPR.
apply pow3IsPR.
apply
 compose3_2IsPR
  with (f1 := fun f v s : nat => v) (f2 := fun f v s : nat => s + f).
apply pi2_3IsPR.
apply filter101IsPR with (g := fun f s : nat => s + f).
apply swapIsPR.
apply plusIsPR.
apply plusIsPR.
apply plusIsPR.
apply cPairIsPR.
assert
 (isPR 3
    (fun f v s : nat =>
     ReplaceFormulaTerm f (cPair 0 (pow3 f + (v + (s + f)))))).
apply
 compose3_2IsPR
  with
    (f1 := fun f v s : nat => f)
    (f2 := fun f v s : nat => cPair 0 (pow3 f + (v + (s + f)))).
apply pi1_3IsPR.
assumption.
apply ReplaceFormulaTermIsPR.
apply
 compose3_3IsPR
  with
    (f1 := fun f v s : nat => f)
    (f2 := fun f v s : nat =>
           cTriple (cPair 0 (pow3 f + (v + (s + f))))
             (cPair 0 (pow3 f + (v + (s + f))))
             (ReplaceFormulaTerm f (cPair 0 (pow3 f + (v + (s + f))))))
    (f3 := fun f v s : nat =>
           ReplaceFormulaTerm f (cPair 0 (pow3 f + (v + (s + f))))).
apply pi1_3IsPR.
apply
 compose3_3IsPR
  with
    (f1 := fun f v s : nat => cPair 0 (pow3 f + (v + (s + f))))
    (f2 := fun f v s : nat => cPair 0 (pow3 f + (v + (s + f))))
    (f3 := fun f v s : nat =>
           ReplaceFormulaTerm f (cPair 0 (pow3 f + (v + (s + f)))));
 try assumption.
apply cTripleIsPR.
assumption.
apply boundComputationIsPR.
apply succIsPR.
apply cPairIsPR.
apply
 boundSearchIsPR
  with
    (P := fun p x : nat =>
          ltBool 0 (checkSubFormulaTrace (cPair (cPairPi1 p) x))).
unfold isPRrel in |- *.
apply
 compose2_2IsPR
  with
    (f := fun p x : nat => 0)
    (g := fun p x : nat => checkSubFormulaTrace (cPair (cPairPi1 p) x))
    (h := charFunction 2 ltBool).
apply filter10IsPR with (g := fun _ : nat => 0).
apply const1_NIsPR.
apply compose2_1IsPR with (f := fun p x : nat => cPair (cPairPi1 p) x).
apply
 compose2_2IsPR
  with (f := fun p x : nat => cPairPi1 p) (g := fun p x : nat => x).
apply filter10IsPR.
apply cPairPi1IsPR.
apply pi2_2IsPR.
apply cPairIsPR.
apply checkTraceIsPR.
apply ltIsPR.
apply cPairPi1IsPR.
Qed.

End Code_Substitute_Formula.
