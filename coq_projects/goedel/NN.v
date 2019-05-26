Require Import Arith.
Require Import Ensembles.
Require Import Coq.Lists.List.

Require Import folProp.
Require Import subAll.
Require Import folLogic3.
Require Export Languages.
Require Export LNN.

Section NN.

Definition NN1 := forallH 0 (notH (equal (Succ (var 0)) Zero)).
Definition NN2 :=
  forallH 1
    (forallH 0
       (impH (equal (Succ (var 0)) (Succ (var 1))) (equal (var 0) (var 1)))).
Definition NN3 := forallH 0 (equal (Plus (var 0) Zero) (var 0)).
Definition NN4 :=
  forallH 1
    (forallH 0
       (equal (Plus (var 0) (Succ (var 1))) (Succ (Plus (var 0) (var 1))))).
Definition NN5 := forallH 0 (equal (Times (var 0) Zero) Zero).
Definition NN6 :=
  forallH 1
    (forallH 0
       (equal (Times (var 0) (Succ (var 1)))
          (Plus (Times (var 0) (var 1)) (var 0)))).
Definition NN7 := forallH 0 (notH (LT (var 0) Zero)).
Definition NN8 :=
  forallH 1
    (forallH 0
       (impH (LT (var 0) (Succ (var 1)))
          (orH (LT (var 0) (var 1)) (equal (var 0) (var 1))))).
Definition NN9 :=
  forallH 1
    (forallH 0
       (orH (LT (var 0) (var 1))
          (orH (equal (var 0) (var 1)) (LT (var 1) (var 0))))).
Definition NNStar :=
  forallH 1
    (forallH 0
       (impH (orH (LT (var 0) (var 1)) (equal (var 0) (var 1)))
          (LT (var 0) (Succ (var 1))))).

Definition NN :=
  Ensembles.Add _
    (Ensembles.Add _
       (Ensembles.Add _
          (Ensembles.Add _
             (Ensembles.Add _ (Ensembles.Add _ (Ensembles.Add _ (Ensembles.Add _ (Singleton _ NN1) NN2) NN3) NN4) NN5)
             NN6) NN7) NN8) NN9.

Lemma closedNN1 : ClosedSystem LNN NN.
Proof.
unfold ClosedSystem in |- *.
unfold NN in |- *.
intros.
repeat induction H; auto.
Qed.

Lemma closedNN : forall v : nat, ~ In_freeVarSys LNN v NN.
Proof.
unfold not in |- *; intros.
unfold In_freeVarSys in H.
induction H as (x, H).
elim closedNN1 with v x; tauto.
Qed.

Lemma nn1 : forall a : Term, SysPrf NN (notH (equal (Succ a) Zero)).
Proof.
intros.
replace (notH (equal (Succ a) Zero)) with
 (substituteFormula LNN (notH (equal (Succ (var 0)) Zero)) 0 a).
apply forallE.
apply Axm; repeat (try right; constructor) || left.
reflexivity.
Qed.

Lemma nn2 :
 forall a b : Term, SysPrf NN (impH (equal (Succ a) (Succ b)) (equal a b)).
Proof.
intros.
set (m := fun x : nat => match x with
                         | O => a
                         | S _ => b
                         end) in *.
replace (impH (equal (Succ a) (Succ b)) (equal a b)) with
 (subAllFormula LNN
    (impH (equal (Succ (var 0)) (Succ (var 1))) (equal (var 0) (var 1)))
    (fun x : nat =>
     match le_lt_dec 2 x with
     | left _ => var x
     | right _ => m x
     end)).
apply (subAllCloseFrom LNN).
simpl in |- *.
apply Axm; repeat (try right; constructor) || left.
simpl in |- *.
induction (le_lt_dec 2 0).
elim (le_not_lt _ _ a0).
auto.
induction (le_lt_dec 2 1).
elim (le_not_lt _ _ a0).
auto.
reflexivity.
Qed.

Lemma nn3 : forall a : Term, SysPrf NN (equal (Plus a Zero) a).
Proof.
intros.
replace (equal (Plus a Zero) a) with
 (substituteFormula LNN (equal (Plus (var 0) Zero) (var 0)) 0 a).
apply forallE.
apply Axm; repeat (try right; constructor) || left.
reflexivity.
Qed.

Lemma nn4 :
 forall a b : Term, SysPrf NN (equal (Plus a (Succ b)) (Succ (Plus a b))).
Proof.
intros.
set (m := fun x : nat => match x with
                         | O => a
                         | S _ => b
                         end) in *.
replace (equal (Plus a (Succ b)) (Succ (Plus a b))) with
 (subAllFormula LNN
    (equal (Plus (var 0) (Succ (var 1))) (Succ (Plus (var 0) (var 1))))
    (fun x : nat =>
     match le_lt_dec 2 x with
     | left _ => var x
     | right _ => m x
     end)).
apply (subAllCloseFrom LNN).
simpl in |- *.
apply Axm; repeat (try right; constructor) || left.
simpl in |- *.
induction (le_lt_dec 2 0).
elim (le_not_lt _ _ a0).
auto.
induction (le_lt_dec 2 1).
elim (le_not_lt _ _ a0).
auto.
reflexivity.
Qed.

Lemma nn5 : forall a : Term, SysPrf NN (equal (Times a Zero) Zero).
Proof.
intros.
replace (equal (Times a Zero) Zero) with
 (substituteFormula LNN (equal (Times (var 0) Zero) Zero) 0 a).
apply forallE.
apply Axm; repeat (try right; constructor) || left.
reflexivity.
Qed.

Lemma nn6 :
 forall a b : Term, SysPrf NN (equal (Times a (Succ b)) (Plus (Times a b) a)).
Proof.
intros.
set (m := fun x : nat => match x with
                         | O => a
                         | S _ => b
                         end) in *.
replace (equal (Times a (Succ b)) (Plus (Times a b) a)) with
 (subAllFormula LNN
    (equal (Times (var 0) (Succ (var 1)))
       (Plus (Times (var 0) (var 1)) (var 0)))
    (fun x : nat =>
     match le_lt_dec 2 x with
     | left _ => var x
     | right _ => m x
     end)).
apply (subAllCloseFrom LNN).
simpl in |- *.
apply Axm; repeat (try right; constructor) || left.
simpl in |- *.
induction (le_lt_dec 2 0).
elim (le_not_lt _ _ a0).
auto.
induction (le_lt_dec 2 1).
elim (le_not_lt _ _ a0).
auto.
reflexivity.
Qed.

Lemma nn7 : forall a : Term, SysPrf NN (notH (LT a Zero)).
Proof.
intros.
replace (notH (LT a Zero)) with
 (substituteFormula LNN (notH (LT (var 0) Zero)) 0 a).
apply forallE.
apply Axm; repeat (try right; constructor) || left.
reflexivity.
Qed.

Lemma nn8 :
 forall a b : Term,
 SysPrf NN (impH (LT a (Succ b)) (orH (LT a b) (equal a b))).
Proof.
intros.
set (m := fun x : nat => match x with
                         | O => a
                         | S _ => b
                         end) in *.
replace (impH (LT a (Succ b)) (orH (LT a b) (equal a b))) with
 (subAllFormula LNN
    (impH (LT (var 0) (Succ (var 1)))
       (orH (LT (var 0) (var 1)) (equal (var 0) (var 1))))
    (fun x : nat =>
     match le_lt_dec 2 x with
     | left _ => var x
     | right _ => m x
     end)).
apply (subAllCloseFrom LNN).
simpl in |- *.
apply Axm; repeat (try right; constructor) || left.
simpl in |- *.
induction (le_lt_dec 2 0).
elim (le_not_lt _ _ a0).
auto.
induction (le_lt_dec 2 1).
elim (le_not_lt _ _ a0).
auto.
reflexivity.
Qed.

Lemma nn9 :
 forall a b : Term, SysPrf NN (orH (LT a b) (orH (equal a b) (LT b a))).
Proof.
intros.
set (m := fun x : nat => match x with
                         | O => a
                         | S _ => b
                         end) in *.
replace (orH (LT a b) (orH (equal a b) (LT b a))) with
 (subAllFormula LNN
    (orH (LT (var 0) (var 1))
       (orH (equal (var 0) (var 1)) (LT (var 1) (var 0))))
    (fun x : nat =>
     match le_lt_dec 2 x with
     | left _ => var x
     | right _ => m x
     end)).
apply (subAllCloseFrom LNN).
simpl in |- *.
apply Axm; repeat (try right; constructor) || left.
simpl in |- *.
induction (le_lt_dec 2 0).
elim (le_not_lt _ _ a0).
auto.
induction (le_lt_dec 2 1).
elim (le_not_lt _ _ a0).
auto.
reflexivity.
Qed.

End NN.

(*
Definition NNPlus := (Add ? NN NNStar).

Lemma nnStar : (a,b:Term)
 (SysPrf NNPlus (impH (orH (LT a b) (equal a b)) (LT a (Succ b)))).
Proof.
Intros.
LetTac m := [x:nat]
Cases x of 
O => a
|(S _) => b
end.
Replace (impH (orH (LT a b) (equal a b)) (LT a (Succ b)))
with (subAllFormula LNN (impH (orH (LT (var (0)) (var (1))) (equal (var (0)) (var (1))))
        (LT (var (0)) (Succ (var (1))))) [x:nat]Cases (le_lt_dec (2) x) of
         (left _) => (var x)
       | (right _) => (m x) end).
Apply (subAllCloseFrom LNN).
Simpl.
Apply Axm; Repeat ((Try Right; Constructor) Orelse Left).
Simpl.
NewInduction (le_lt_dec (2) (0)).
Elim (le_not_lt ? ? a0).
Auto.
NewInduction (le_lt_dec (2) (1)).
Elim (le_not_lt ? ? a0).
Auto.
Reflexivity.
Qed.

Lemma NNPlusExtends : (Included ? NN NNPlus).
Proof.
Intros.
Unfold Included NNPlus.
Intros.
Left.
Assumption.
Qed.

Lemma closedNNPlus1 : (ClosedSystem LNN NNPlus).
Proof.
Unfold ClosedSystem.
Unfold NNPlus.
Intros.
Repeat Induction H; Auto.
Qed.

Lemma closedNNPlus : (v:nat)~(In_freeVarSys LNN v NNPlus).
Proof.
Unfold not; Intros.
Unfold In_freeVarSys in H.
Induction H.
Elim closedNNPlus1 with v x; Tauto.
Qed.
*)
