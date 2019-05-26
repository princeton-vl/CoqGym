Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import Arith.

Require Import subAll.
Require Import folReplace.
Require Import folProp.
Require Import folLogic3.
Require Import NN.
Require Import LNN2LNT.
Require Export PA.

Unset Standard Proposition Elimination Names.

Lemma paZeroOrSucc :
 forall t : Term,
 SysPrf PA
   (orH (equal t Zero)
      (existH (newVar (0 :: freeVarTerm LNT t))
         (equal t (Succ (var (newVar (0 :: freeVarTerm LNT t))))))).
Proof.
intros.
set (nv := newVar (0 :: freeVarTerm LNT t)) in *.
apply
 impE
  with
    (substituteFormula LNT
       (orH (equal (var 0) Zero) (existH nv (equal (var 0) (Succ (var nv)))))
       0 t).
rewrite (subFormulaOr LNT).
rewrite (subFormulaEqual LNT).
simpl in |- *.
apply iffE1.
apply (reduceOr LNT).
apply iffRefl.
rewrite (subFormulaExist LNT).
induction (eq_nat_dec nv 0).
elim (newVar1 (0 :: freeVarTerm LNT t)).
fold nv in |- *.
rewrite a.
simpl in |- *.
auto.
induction (In_dec eq_nat_dec nv (freeVarTerm LNT t)).
elim (newVar1 (0 :: freeVarTerm LNT t)).
fold nv in |- *.
simpl in |- *.
auto.
rewrite (subFormulaEqual LNT).
Opaque eq_nat_dec.
simpl in |- *.
Transparent eq_nat_dec.
destruct (eq_nat_dec 0 nv).
elim b.
auto.
apply iffRefl.
apply forallE.
apply induct.
rewrite (subFormulaOr LNT).
apply orI1.
rewrite (subFormulaEqual LNT).
simpl in |- *.
apply eqRefl.
apply forallI.
apply closedPA.
apply impI.
rewrite (subFormulaOr LNT).
apply orI2.
rewrite (subFormulaExist LNT).
induction (eq_nat_dec nv 0).
elim (newVar1 (0 :: freeVarTerm LNT t)).
fold nv in |- *.
simpl in |- *.
auto.
induction (In_dec eq_nat_dec nv (freeVarTerm LNT (Succ (var 0)))).
elim (newVar1 (0 :: freeVarTerm LNT t)).
fold nv in |- *.
simpl in a.
induction a as [H| H].
simpl in |- *.
auto.
elim H.
rewrite (subFormulaEqual LNT).
Opaque eq_nat_dec.
simpl in |- *.
Transparent eq_nat_dec.
induction
 (nat_rec (fun n : nat => {0 = n} + {0 <> n}) (left (0 <> 0) (refl_equal 0))
    (fun (m : nat) (_ : {0 = m} + {0 <> m}) => right (0 = S m) (O_S m)) nv).
elim b.
auto.
fold var in |- *.
fold (Succ (var nv)) in |- *.
apply sysWeaken.
apply existI with (var 0).
rewrite (subFormulaEqual LNT).
simpl in |- *.
destruct (eq_nat_dec nv 0).
elim b1; auto.
change match nv as n return ({0 = n} + {0 <> n}) with
                  | 0 => left (0 <> 0) (refl_equal 0)
                  | S m => right (0 = S m) (O_S m)
                  end
 with (eq_nat_dec 0 nv).
destruct (eq_nat_dec 0 nv).
elim b1.
auto.
simpl.
destruct (eq_nat_dec nv nv).
apply eqRefl.
elim n1.
reflexivity.
Qed.

Lemma paPlusSym : forall a b : Term, SysPrf PA (equal (Plus a b) (Plus b a)).
Proof.
assert
 (SysPrf PA
    (forallH 1
       (forallH 0 (equal (Plus (var 0) (var 1)) (Plus (var 1) (var 0)))))).
apply induct.
rewrite (subFormulaForall LNT).
induction (eq_nat_dec 0 1).
discriminate a.
induction (In_dec eq_nat_dec 0 (freeVarTerm LNT Zero)).
elim a.
apply induct.
repeat rewrite (subFormulaEqual LNT).
simpl in |- *.
apply eqRefl.
apply forallI.
apply closedPA.
repeat rewrite (subFormulaEqual LNT).
simpl in |- *.
apply impI.
apply eqTrans with (Succ (var 0)).
apply sysWeaken.
apply pa3 with (a := Succ (var 0)).
apply eqTrans with (Succ (Plus Zero (var 0))).
apply eqSucc.
apply eqTrans with (Plus (var 0) Zero).
apply sysWeaken.
apply eqSym.
apply pa3.
apply Axm; right; constructor.
apply eqSym.
apply sysWeaken.
apply pa4 with (a := Zero) (b := var 0).
apply forallI.
apply closedPA.
apply impI.
rewrite (subFormulaForall LNT).
induction (eq_nat_dec 0 1).
discriminate a.
induction (In_dec eq_nat_dec 0 (freeVarTerm LNT (Succ (var 1)))).
simpl in a.
induction a as [H| H].
elim b; auto.
contradiction.
rewrite (subFormulaEqual LNT).
simpl in |- *.
apply forallI.
unfold not in |- *; intros.
induction H as (x, H); induction H as (H, H0).
induction H0 as [x H0| x H0].
elim closedPA with 0.
exists x.
auto.
induction H0.
simpl in H.
decompose sum H.
discriminate H0.
discriminate H1.
apply eqTrans with (Succ (Plus (var 0) (var 1))).
apply sysWeaken.
apply pa4 with (a := var 0) (b := var 1).
apply eqTrans with (Succ (Plus (var 1) (var 0))).
apply eqSucc.
apply forallSimp with 0.
apply Axm; right; constructor.
apply sysWeaken.
apply forallSimp with 0.
apply induct.
rewrite (subFormulaEqual LNT).
simpl in |- *.
apply eqTrans with (Succ (var 1)).
fold
 (Succ
    (apply LNT Languages.Plus
       (Tcons LNT 1 (fol.var LNT 1) (Tcons LNT 0 Zero (Tnil LNT))))) 
 in |- *.
apply eqSucc.
apply pa3 with (a := var 1).
apply eqSym.
apply pa3 with (a := Succ (var 1)).
apply forallI.
apply closedPA.
apply impI.
rewrite (subFormulaEqual LNT).
simpl in |- *.
apply eqTrans with (Succ (Plus (Succ (var 1)) (var 0))).
fold
 (Succ
    (apply LNT Languages.Plus
       (Tcons LNT 1 (fol.var LNT 1) (Tcons LNT 0 (Succ (var 0)) (Tnil LNT)))))
 in |- *.
apply eqSucc.
apply eqTrans with (Succ (Plus (var 1) (var 0))).
apply sysWeaken.
apply pa4 with (a := var 1) (b := var 0).
apply Axm; right; constructor.
apply sysWeaken.
apply eqSym.
apply pa4 with (a := Succ (var 1)) (b := var 0).
intros.
set (m := fun x : nat => match x with
                         | O => a
                         | S _ => b
                         end) in *.
replace (equal (Plus a b) (Plus b a)) with
 (subAllFormula LNT (equal (Plus (var 0) (var 1)) (Plus (var 1) (var 0)))
    (fun x : nat =>
     match le_lt_dec 2 x with
     | left _ => var x
     | right _ => m x
     end)).
apply (subAllCloseFrom LNT).
simpl in |- *.
apply H.
simpl in |- *.
induction (le_lt_dec 2 0).
elim (le_not_lt _ _ a0).
auto.
induction (le_lt_dec 2 1).
elim (le_not_lt _ _ a0).
auto.
reflexivity.
Qed.

Lemma NN72PA : SysPrf PA (LNN2LNT_formula NN7).
Proof.
simpl in |- *.
apply forallI.
apply closedPA.
rewrite translateLT1.
simpl in |- *.
set (nv := newVar (0 :: 2 :: 1 :: 0 :: nil)) in *.
fold var in |- *.
fold Zero in |- *.
fold (Succ (var nv)) in |- *.
fold (Plus (var 0) (Succ (var nv))) in |- *.
apply nnI.
apply forallI.
apply closedPA.
apply impE with (notH (equal (Succ (Plus (var 0) (var nv))) Zero)).
apply cp2.
apply impI.
apply eqTrans with (Plus (var 0) (Succ (var nv))).
apply sysWeaken.
apply eqSym.
apply pa4.
apply Axm; right; constructor.
apply pa1.
Qed.

Lemma NN82PA : SysPrf PA (LNN2LNT_formula NN8).
Proof.
replace (LNN2LNT_formula NN8) with
 (forallH 1
    (forallH 0
       (impH (LNN2LNT_formula (LT (LNN.var 0) (LNN.Succ (LNN.var 1))))
          (orH (LNN2LNT_formula (LT (LNN.var 0) (LNN.var 1)))
             (equal (var 0) (var 1)))))).
simpl in |- *.
repeat rewrite translateLT1.
simpl in |- *.
unfold newVar in |- *.
simpl in |- *.
fold var in |- *.
fold (Succ (var 3)) in |- *.
fold (Succ (var 1)) in |- *.
fold (Plus (var 0) (Succ (var 3))) in |- *.
fold equal in |- *.
fold (fol.existH LNT 3 (equal (Plus (var 0) (Succ (var 3))) (Succ (var 1))))
 in |- *.
fold (fol.existH LNT 3 (equal (Plus (var 0) (Succ (var 3))) (var 1))) in |- *.
fold existH in |- *.
apply forallI.
apply closedPA.
apply forallI.
apply closedPA.
apply impI.
apply existSys.
apply closedPA.
simpl in |- *.
unfold not in |- *; intros.
repeat (elim H; clear H; [ discriminate | intros ]); auto.
eapply orE.
apply sysWeaken.
apply paZeroOrSucc.
apply impI.
apply orI2.
apply impE with (equal (Succ (var 0)) (Succ (var 1))).
repeat simple apply sysWeaken.
apply pa2.
apply eqTrans with (Plus (var 0) (Succ (var 3))).
apply eqTrans with (Succ (Plus (var 0) (var 3))).
apply eqSucc.
apply eqTrans with (Plus (var 0) Zero).
apply eqSym.
repeat simple apply sysWeaken.
apply pa3.
apply eqPlus.
apply eqRefl.
apply eqSym.
apply Axm; right; constructor.
apply eqSym.
repeat simple apply sysWeaken.
apply pa4.
apply Axm; left; right; constructor.
unfold newVar in |- *.
simpl in |- *.
apply impI.
apply existSys.
unfold not in |- *; intros.
induction H as (x, H); induction H as (H, H0).
induction H0 as [x H0| x H0].
elim closedPA with 4.
exists x.
auto.
induction H0.
simpl in H.
repeat (elim H; clear H; [ discriminate | intros ]); auto.
unfold not in |- *; intros.
simpl in H.
repeat (elim H; clear H; [ discriminate | intros ]); auto.
apply orI1.
apply existI with (var 4).
rewrite (subFormulaEqual LNT).
simpl in |- *.
apply impE with (equal (Succ (Plus (var 0) (Succ (var 4)))) (Succ (var 1))).
repeat simple apply sysWeaken.
apply pa2.
apply eqTrans with (Plus (var 0) (Succ (var 3))).
apply eqTrans with (Plus (var 0) (Succ (Succ (var 4)))).
repeat simple apply sysWeaken.
apply eqSym.
apply pa4.
apply eqPlus.
apply eqRefl.
apply eqSucc.
apply eqSym.
apply Axm; right; constructor.
apply Axm; left; right; constructor.
reflexivity.
Qed.

Lemma NN92PA : SysPrf PA (LNN2LNT_formula NN9).
Proof.
replace (LNN2LNT_formula NN9) with
 (forallH 1
    (forallH 0
       (orH (LNN2LNT_formula (LT (LNN.var 0) (LNN.var 1)))
          (orH (equal (var 0) (var 1))
             (LNN2LNT_formula (LT (LNN.var 1) (LNN.var 0)))))));
 [ idtac | reflexivity ].
simpl in |- *.
repeat rewrite translateLT1.
simpl in |- *.
unfold newVar in |- *.
simpl in |- *.
fold var in |- *.
fold (Succ (var 3)) in |- *.
fold (Plus (var 0) (Succ (var 3))) in |- *.
fold (Plus (var 1) (Succ (var 3))) in |- *.
fold equal in |- *.
fold (fol.existH LNT 3 (equal (Plus (var 0) (Succ (var 3))) (var 1))) in |- *.
fold (fol.existH LNT 3 (equal (Plus (var 1) (Succ (var 3))) (var 0))) in |- *.
fold existH in |- *.
apply induct.
rewrite (subFormulaForall LNT).
induction (eq_nat_dec 0 1).
discriminate a.
induction (In_dec eq_nat_dec 0 (freeVarTerm LNT Zero)).
simpl in a.
elim a.
rewrite (subFormulaOr LNT).
apply forallI.
apply closedPA.
apply orI2.
rewrite (subFormulaOr LNT).
rewrite (subFormulaEqual LNT).
simpl in |- *.
eapply orE.
apply paZeroOrSucc with (t := var 0).
apply impI.
apply orI1.
apply Axm; right; constructor.
apply impI.
apply orI2.
unfold newVar in |- *.
simpl in |- *.
rewrite (subFormulaExist LNT).
induction (eq_nat_dec 3 1).
discriminate a.
induction (In_dec eq_nat_dec 3 (freeVarTerm LNT Zero)).
elim a.
apply impE with (existH 3 (equal (var 0) (Succ (var 3)))).
apply sysWeaken.
apply impI.
apply existSys.
apply closedPA.
unfold not in |- *; intros.
simpl in H.
induction H as [H| H].
discriminate H.
contradiction.
apply existI with (var 3).
repeat rewrite (subFormulaEqual LNT).
simpl in |- *.
apply eqTrans with (Succ (var 3)).
apply sysWeaken.
apply eqTrans with (Plus (Succ (var 3)) Zero).
apply paPlusSym with (a := Zero) (b := Succ (var 3)).
apply pa3.
apply eqSym.
apply Axm; right; constructor.
apply impE with (existH 1 (equal (var 0) (Succ (var 1)))).
replace (equal (var 0) (Succ (var 3))) with
 (substituteFormula LNT (equal (var 0) (Succ (var 1))) 1 (var 3)).
apply iffE1.
apply (rebindExist LNT).
simpl in |- *.
unfold not in |- *; intros.
induction H as [H| H].
discriminate H.
contradiction.
rewrite (subFormulaEqual LNT).
reflexivity.
apply Axm; right; constructor.
apply forallI.
apply closedPA.
apply impI.
rewrite (subFormulaForall LNT).
induction (eq_nat_dec 0 1).
discriminate a.
induction (In_dec eq_nat_dec 0 (freeVarTerm LNT (Succ (var 1)))).
simpl in a.
induction a as [H| H].
discriminate H.
contradiction.
rewrite (subFormulaOr LNT).
apply sysWeaken.
apply induct.
rewrite (subFormulaOr LNT).
apply orI1.
rewrite (subFormulaExist LNT).
induction (eq_nat_dec 3 1).
discriminate a.
induction (In_dec eq_nat_dec 3 (freeVarTerm LNT (Succ (var 1)))).
simpl in a.
induction a as [H| H].
elim b1; auto.
contradiction.
rewrite (subFormulaExist LNT).
induction (eq_nat_dec 3 0).
discriminate a.
induction (In_dec eq_nat_dec 3 (freeVarTerm LNT Zero)).
simpl in a.
contradiction.
apply existI with (var 1).
repeat rewrite (subFormulaEqual LNT).
simpl in |- *.
apply eqTrans with (Plus (Succ (var 1)) Zero).
apply paPlusSym with (a := Zero) (b := Succ (var 1)).
apply pa3.
apply forallI.
apply closedPA.
apply impI.
apply orSys.
rewrite (subFormulaExist LNT).
induction (eq_nat_dec 3 1).
discriminate a.
induction (In_dec eq_nat_dec 3 (freeVarTerm LNT (Succ (var 1)))).
simpl in a.
induction a as [H| H].
elim b1; auto.
contradiction.
repeat rewrite (subFormulaOr LNT).
rewrite (subFormulaExist LNT).
induction (eq_nat_dec 3 0).
discriminate a.
induction (In_dec eq_nat_dec 3 (freeVarTerm LNT (Succ (var 0)))).
simpl in a.
induction a as [H| H].
elim b3; auto.
contradiction.
rewrite (subFormulaExist LNT).
induction (eq_nat_dec 3 1).
elim b1; auto.
induction (In_dec eq_nat_dec 3 (freeVarTerm LNT (Succ (var 1)))).
elim b2; auto.
rewrite (subFormulaExist LNT).
induction (eq_nat_dec 3 0).
elim b3; auto.
induction (In_dec eq_nat_dec 3 (freeVarTerm LNT (Succ (var 0)))).
elim b4; auto.
repeat rewrite (subFormulaEqual LNT); simpl in |- *.
apply existSys.
apply closedPA.
simpl in |- *.
unfold not in |- *; intros.
decompose sum H; auto.
eapply orE.
apply sysWeaken.
apply paZeroOrSucc with (t := var 3).
apply impI.
apply orI2.
apply orI1.
apply eqTrans with (Plus (var 0) (Succ (var 3))).
apply eqTrans with (Succ (Plus (var 0) (var 3))).
apply eqSucc.
apply eqTrans with (Plus (var 0) Zero).
apply eqSym.
repeat simple apply sysWeaken.
apply pa3.
apply eqPlus.
apply eqRefl.
apply eqSym.
apply Axm; right; constructor.
apply eqSym.
repeat simple apply sysWeaken.
apply pa4.
apply Axm; left; right; constructor.
unfold newVar in |- *.
simpl in |- *.
apply impI.
apply orI1.
apply existSys.
unfold not in |- *; intros.
induction H as (x, H); induction H as (H, H0).
induction H0 as [x H0| x H0].
elim closedPA with 4.
exists x.
auto.
induction H0.
simpl in H.
decompose sum H; discriminate H0 || discriminate H1.
simpl in |- *.
unfold not in |- *; intros.
decompose sum H; discriminate H0 || discriminate H1.
apply existI with (var 4).
rewrite (subFormulaEqual LNT); simpl in |- *.
apply eqTrans with (Plus (var 0) (Succ (var 3))).
apply eqTrans with (Plus (var 0) (Succ (Succ (var 4)))).
apply eqTrans with (Succ (Plus (var 0) (Succ (var 4)))).
apply eqTrans with (Plus (Succ (var 4)) (Succ (var 0))).
repeat simple apply sysWeaken.
apply paPlusSym with (a := Succ (var 0)) (b := Succ (var 4)).
repeat simple apply sysWeaken.
eapply eqTrans.
apply pa4.
apply eqSucc.
apply paPlusSym.
repeat simple apply sysWeaken.
apply eqSym.
apply pa4.
apply eqPlus.
apply eqRefl.
apply eqSucc.
apply eqSym.
apply Axm; right; constructor.
apply Axm; left; right; constructor.
repeat rewrite (subFormulaOr LNT).
apply orSys.
apply orI2.
apply orI2.
rewrite (subFormulaExist LNT).
induction (eq_nat_dec 3 1).
discriminate a.
induction (In_dec eq_nat_dec 3 (freeVarTerm LNT (Succ (var 1)))).
induction a as [H| H].
elim b1; auto.
contradiction.
rewrite (subFormulaExist LNT).
induction (eq_nat_dec 3 0).
discriminate a.
induction (In_dec eq_nat_dec 3 (freeVarTerm LNT (Succ (var 0)))).
induction a as [H| H].
elim b3; auto.
contradiction.
apply existI with Zero.
repeat rewrite (subFormulaEqual LNT).
simpl in |- *.
apply eqTrans with (Succ (Plus (Succ (var 1)) Zero)).
apply sysWeaken.
apply pa4 with (a := Succ (var 1)) (b := Zero).
apply eqTrans with (Succ (Succ (var 1))).
apply eqSucc.
apply sysWeaken.
apply pa3.
fold (Succ (fol.var LNT 0)) in |- *.
apply eqSucc.
apply eqSym.
apply Axm; right; constructor.
do 2 rewrite (subFormulaExist LNT).
induction (eq_nat_dec 3 1).
discriminate a.
induction (In_dec eq_nat_dec 3 (freeVarTerm LNT (Succ (var 1)))).
induction a as [H| H].
elim b1; auto.
contradiction.
do 2 rewrite (subFormulaExist LNT).
induction (eq_nat_dec 3 0).
discriminate a.
induction (In_dec eq_nat_dec 3 (freeVarTerm LNT (Succ (var 0)))).
induction a as [H| H].
elim b3; auto.
contradiction.
apply orI2.
apply orI2.
apply existSys.
apply closedPA.
simpl in |- *.
unfold not in |- *; intros.
decompose sum H; auto.
apply existI with (Succ (var 3)).
repeat rewrite (subFormulaEqual LNT).
simpl in |- *.
apply eqTrans with (Succ (Plus (Succ (var 1)) (Succ (var 3)))).
apply sysWeaken.
apply pa4 with (a := Succ (var 1)) (b := Succ (var 3)).
fold (Succ (fol.var LNT 0)) in |- *.
apply eqSucc.
apply Axm; right; constructor.
Qed.
