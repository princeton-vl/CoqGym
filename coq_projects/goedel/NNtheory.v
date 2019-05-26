Require Import Arith.

Require Import folLogic3.
Require Import folProp.
Require Import subProp.
Require Export NN.

Lemma natNE :
 forall a b : nat,
 a <> b -> SysPrf NN (notH (equal (natToTerm a) (natToTerm b))).
Proof.
assert
 (forall a b : nat,
  a < b -> SysPrf NN (notH (equal (natToTerm a) (natToTerm b)))).
intro.
induction a as [| a Hreca]; intros.
destruct b as [| n].
elim (lt_n_O _ H).
simpl in |- *.
apply impE with (notH (equal (Succ (natToTerm n)) Zero)).
apply cp2.
apply impI.
apply eqSym.
apply Axm; right; constructor.
apply nn1.
destruct b as [| n].
elim (lt_n_O _ H).
simpl in |- *.
apply impE with (notH (equal (natToTerm a) (natToTerm n))).
apply cp2.
apply nn2.
apply Hreca.
apply lt_S_n.
auto.
intros.
induction (nat_total_order _ _ H0).
apply H.
auto.
apply impE with (notH (equal (natToTerm b) (natToTerm a))).
apply cp2.
apply impI.
apply eqSym.
apply Axm; right; constructor.
apply H.
auto.
Qed.

Lemma natLE :
 forall a b : nat,
 b <= a -> SysPrf NN (notH (LT (natToTerm a) (natToTerm b))).
Proof.
intros.
induction b as [| b Hrecb].
apply nn7.
simpl in |- *.
apply
 impE
  with
    (notH
       (orH (LT (natToTerm a) (natToTerm b))
          (equal (natToTerm a) (natToTerm b)))).
apply cp2.
apply nn8.
apply nOr.
apply andI.
apply Hrecb.
apply le_S_n.
apply le_S.
auto.
apply natNE.
unfold not in |- *; intros.
apply (le_not_lt _ _ H).
rewrite H0.
apply lt_n_Sn.
Qed.

Lemma natLT :
 forall a b : nat, a < b -> SysPrf NN (LT (natToTerm a) (natToTerm b)).
Proof.
intros.
eapply orE.
apply nn9 with (a := natToTerm b) (b := natToTerm a).
apply impI.
apply contradiction with (LT (natToTerm b) (natToTerm a)).
apply Axm; right; constructor.
apply sysWeaken.
apply natLE.
apply lt_le_weak.
auto.
apply impI.
apply orSys.
apply contradiction with (equal (natToTerm b) (natToTerm a)).
apply Axm; right; constructor.
apply sysWeaken.
apply natNE.
unfold not in |- *; intros.
apply (le_not_lt _ _ H).
rewrite H0.
apply lt_n_Sn.
apply Axm; right; constructor.
Qed.

Lemma natPlus :
 forall a b : nat,
 SysPrf NN (equal (Plus (natToTerm a) (natToTerm b)) (natToTerm (a + b))).
Proof.
intros.
induction b as [| b Hrecb].
rewrite plus_comm.
simpl in |- *.
apply nn3.
rewrite plus_comm.
simpl in |- *.
apply eqTrans with (Succ (Plus (natToTerm a) (natToTerm b))).
apply nn4.
apply eqSucc.
rewrite plus_comm.
apply Hrecb.
Qed.

Lemma natTimes :
 forall a b : nat,
 SysPrf NN (equal (Times (natToTerm a) (natToTerm b)) (natToTerm (a * b))).
Proof.
intros.
induction b as [| b Hrecb].
rewrite mult_comm.
simpl in |- *.
apply nn5.
rewrite mult_comm.
simpl in |- *.
eapply eqTrans.
apply nn6.
rewrite plus_comm.
apply eqTrans with (Plus (natToTerm (b * a)) (natToTerm a)).
apply eqPlus.
rewrite mult_comm.
apply Hrecb.
apply eqRefl.
apply natPlus.
Qed.

Lemma boundedLT :
 forall (m : nat) (a : Formula) (x : nat),
 (forall n : nat,
  n < m -> SysPrf NN (substituteFormula LNN a x (natToTerm n))) ->
 SysPrf NN (impH (LT (var x) (natToTerm m)) a).
Proof.
simple induction m; intros.
apply impI.
apply contradiction with (LT (var x) (natToTerm 0)).
apply Axm; right; constructor.
apply sysWeaken.
apply nn7.
apply impI.
eapply orE.
apply impE with (LT (var x) (natToTerm (S n))).
apply sysWeaken.
simpl in |- *.
apply nn8.
apply Axm; right; constructor.
apply sysWeaken.
apply H.
intros.
apply H0.
apply lt_S.
auto.
apply sysWeaken.
apply impI.
rewrite <- (subFormulaId LNN a x).
apply impE with (substituteFormula LNN a x (natToTerm n)).
apply (subWithEquals LNN).
apply eqSym.
apply Axm; right; constructor.
apply sysWeaken.
apply H0.
apply lt_n_Sn.
Qed.

Lemma nnPlusNotNeeded :
 forall n : nat,
 SysPrf NN
   (impH (orH (LT (var 1) (natToTerm n)) (equal (var 1) (natToTerm n)))
      (LT (var 1) (Succ (natToTerm n)))).
Proof.
intros.
induction n as [| n Hrecn].
simpl in |- *.
apply impI.
apply orSys.
apply contradiction with (LT (var 1) Zero).
apply Axm; right; constructor.
apply sysWeaken.
apply nn7.
rewrite <- (subFormulaId LNN (LT (var 1) (Succ Zero)) 1).
apply impE with (substituteFormula LNN (LT (var 1) (Succ Zero)) 1 Zero).
apply (subWithEquals LNN).
apply eqSym.
apply Axm; right; constructor.
apply sysWeaken.
replace (substituteFormula LNN (LT (var 1) (Succ Zero)) 1 Zero) with
 (LT (natToTerm 0) (natToTerm 1)).
apply natLT.
auto.
unfold LT in |- *.
rewrite (subFormulaRelation LNN).
reflexivity.
simpl in |- *.
apply impI.
apply orSys.
apply
 impE with (orH (LT (var 1) (natToTerm n)) (equal (var 1) (natToTerm n))).
apply sysWeaken.
apply impTrans with (LT (var 1) (natToTerm (S n))).
apply Hrecn.
apply boundedLT.
intros.
replace
 (substituteFormula LNN (LT (var 1) (Succ (Succ (natToTerm n)))) 1
    (natToTerm n0)) with (LT (natToTerm n0) (natToTerm (S (S n)))).
apply natLT.
apply lt_S.
assumption.
unfold LT in |- *.
rewrite (subFormulaRelation LNN).
simpl in |- *.
rewrite (subTermNil LNN).
reflexivity.
apply closedNatToTerm.
apply impE with (LT (var 1) (Succ (natToTerm n))).
apply sysWeaken.
apply nn8.
apply Axm; right; constructor.
rewrite <- (subFormulaId LNN (LT (var 1) (Succ (Succ (natToTerm n)))) 1).
apply
 impE
  with
    (substituteFormula LNN (LT (var 1) (Succ (Succ (natToTerm n)))) 1
       (Succ (natToTerm n))).
apply (subWithEquals LNN).
apply eqSym.
apply Axm; right; constructor.
apply sysWeaken.
replace
 (substituteFormula LNN (LT (var 1) (Succ (Succ (natToTerm n)))) 1
    (Succ (natToTerm n))) with (LT (natToTerm (S n)) (natToTerm (S (S n)))).
apply natLT.
apply lt_n_Sn.
unfold LT in |- *.
rewrite (subFormulaRelation LNN).
simpl in |- *.
rewrite (subTermNil LNN).
reflexivity.
apply closedNatToTerm.
Qed.
