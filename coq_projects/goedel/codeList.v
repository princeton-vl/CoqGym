Require Import primRec.
Require Import cPair.
Require Export Coq.Lists.List.
Require Import ListExt.
Require Import Arith.
Require Vector.
Require Import extEqualNat.

Definition codeLength : nat -> nat :=
  evalStrongRec 0
    (fun n Hrecs : nat =>
     switchPR n (S (codeNth (n - S (cPairPi2 (pred n))) Hrecs)) 0).

Lemma codeLengthCorrect :
 forall l : list nat, codeLength (codeList l) = length l.
Proof.
intros.
induction l as [| a l Hrecl].
reflexivity.
simpl in |- *.
unfold codeLength in |- *.
set
 (f :=
  fun n Hrecs : nat =>
  switchPR n (S (codeNth (n - S (cPairPi2 (pred n))) Hrecs)) 0) 
 in *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc in |- *.
unfold evalOneParamList in |- *.
unfold evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc in |- *.
unfold evalList in |- *.
unfold f at 1 in |- *.
rewrite evalStrongRecHelp1.
simpl in |- *.
rewrite cPairProjections1.
apply eq_S.
rewrite cPairProjections2.
apply Hrecl.
simpl in |- *.
apply le_lt_n_Sm.
generalize (cPair a (codeList l)).
intro.
apply le_trans with (cPair (cPairPi1 n) (cPairPi2 n)).
apply cPairLe2.
rewrite cPairProjections.
apply le_n.
Qed.

Lemma codeLengthIsPR : isPR 1 codeLength.
Proof.
unfold codeLength in |- *.
apply evalStrongRecIsPR.
apply
 compose2_3IsPR
  with
    (f1 := fun n Hrecs : nat => n)
    (f2 := fun n Hrecs : nat => S (codeNth (n - S (cPairPi2 (pred n))) Hrecs))
    (f3 := fun n Hrecs : nat => 0).
apply pi1_2IsPR.
apply
 compose2_1IsPR
  with (f := fun n Hrecs : nat => codeNth (n - S (cPairPi2 (pred n))) Hrecs).
apply
 compose2_2IsPR
  with
    (f := fun n Hrecs : nat => n - S (cPairPi2 (pred n)))
    (g := fun n Hrecs : nat => Hrecs).
apply filter10IsPR with (g := fun n : nat => n - S (cPairPi2 (pred n))).
apply
 compose1_2IsPR
  with (f := fun n : nat => n) (f' := fun n : nat => S (cPairPi2 (pred n))).
apply idIsPR.
apply compose1_1IsPR with (f := fun n : nat => cPairPi2 (pred n)).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi2IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply succIsPR.
apply filter10IsPR with (g := fun _ : nat => 0).
apply const1_NIsPR.
apply switchIsPR.
Qed.

Definition codeApp : nat -> nat -> nat :=
  evalStrongRec 1
    (fun n Hrecs p1 : nat =>
     switchPR n
       (S
          (cPair (cPairPi1 (pred n))
             (codeNth (n - S (cPairPi2 (pred n))) Hrecs))) p1).

Lemma codeAppCorrect :
 forall l1 l2 : list nat,
 codeApp (codeList l1) (codeList l2) = codeList (l1 ++ l2).
Proof.
intros.
unfold codeApp in |- *.
set
 (f :=
  fun n Hrecs p1 : nat =>
  switchPR n
    (S
       (cPair (cPairPi1 (pred n)) (codeNth (n - S (cPairPi2 (pred n))) Hrecs)))
    p1) in *.
induction l1 as [| a l1 Hrecl1].
unfold evalStrongRec in |- *.
simpl in |- *.
rewrite cPairProjections1.
reflexivity.
simpl in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc in |- *.
unfold evalOneParamList in |- *.
rewrite computeEvalStrongRecHelp.
unfold f at 2 in |- *.
unfold pred in |- *.
set (n := S (cPair a (codeList l1))) in *.
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
replace (codeList (l1 ++ l2)) with
 (codeNth (cPair a (codeList l1) - codeList l1)
    (evalStrongRecHelp 1 f n (codeList l2))).
reflexivity.
assert
 (extEqual 1
    (evalComposeFunc 1 1 (Vector.cons _ (evalStrongRecHelp 1 f n) 0 (Vector.nil _))
       (fun b : nat => codeNth (n - S (codeList l1)) b))
    (evalStrongRec 1 f (codeList l1))).
apply (evalStrongRecHelp2 1).
unfold n in |- *.
apply le_lt_n_Sm.
apply cPairLe2.
simpl in H.
rewrite H.
auto.
Qed.

Lemma codeAppIsPR : isPR 2 codeApp.
Proof.
unfold codeApp in |- *.
apply evalStrongRecIsPR.
apply
 compose3_3IsPR
  with
    (f1 := fun n Hrecs p1 : nat => n)
    (f2 := fun n Hrecs p1 : nat =>
           S
             (cPair (cPairPi1 (pred n))
                (codeNth (n - S (cPairPi2 (pred n))) Hrecs)))
    (f3 := fun n Hrecs p1 : nat => p1).
apply pi1_3IsPR.
apply
 filter110IsPR
  with
    (g := fun n Hrecs : nat =>
          S
            (cPair (cPairPi1 (pred n))
               (codeNth (n - S (cPairPi2 (pred n))) Hrecs))).
apply
 compose2_1IsPR
  with
    (g := S)
    (f := fun n Hrecs : nat =>
          cPair (cPairPi1 (pred n))
            (codeNth (n - S (cPairPi2 (pred n))) Hrecs)).
apply
 compose2_2IsPR
  with
    (h := cPair)
    (f := fun n Hrecs : nat => cPairPi1 (pred n))
    (g := fun n Hrecs : nat => codeNth (n - S (cPairPi2 (pred n))) Hrecs).
apply filter10IsPR with (g := fun n : nat => cPairPi1 (pred n)).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi1IsPR.
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
apply cPairIsPR.
apply succIsPR.
apply pi3_3IsPR.
apply switchIsPR.
Qed.

Definition codeListRemove (a l : nat) : nat :=
  evalStrongRec 1
    (fun n Hrecs p1 : nat =>
     switchPR n
       (switchPR (charFunction 2 beq_nat (cPairPi1 (pred n)) p1)
          (codeNth (n - S (cPairPi2 (pred n))) Hrecs)
          (S
             (cPair (cPairPi1 (pred n))
                (codeNth (n - S (cPairPi2 (pred n))) Hrecs)))) 
       (codeList nil)) l a.

Lemma codeListRemoveCorrect :
 forall (a : nat) (l : list nat),
 codeListRemove a (codeList l) = codeList (list_remove nat eq_nat_dec a l).
Proof.
intros.
unfold codeListRemove in |- *.
set
 (f :=
  fun n Hrecs p1 : nat =>
  switchPR n
    (switchPR (charFunction 2 beq_nat (cPairPi1 (pred n)) p1)
       (codeNth (n - S (cPairPi2 (pred n))) Hrecs)
       (S
          (cPair (cPairPi1 (pred n))
             (codeNth (n - S (cPairPi2 (pred n))) Hrecs)))) 
    (codeList nil)) in *.
induction l as [| a0 l Hrecl].
simpl in |- *.
unfold evalStrongRec in |- *.
simpl in |- *.
reflexivity.
unfold evalStrongRec in |- *.
unfold evalComposeFunc in |- *.
unfold evalOneParamList in |- *.
rewrite computeEvalStrongRecHelp.
unfold f at 2 in |- *.
unfold compose2 in |- *.
set (n := codeList (a0 :: l)) in *.
set (A := n - S (cPairPi2 (pred n))) in *.
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
assert
 (extEqual 1
    (evalComposeFunc 1 1 (Vector.cons _ (evalStrongRecHelp 1 f n) 0 (Vector.nil _))
       (fun b : nat => codeNth (n - S (cPairPi2 (pred n))) b))
    (evalStrongRec 1 f (cPairPi2 (pred n)))).
apply (evalStrongRecHelp2 1).
simpl in |- *.
unfold n in |- *.
rewrite cPairProjections2.
simpl in |- *.
apply le_lt_n_Sm.
apply cPairLe2.
simpl in H.
induction (eq_nat_dec a0 a).
rewrite a1.
rewrite <- beq_nat_refl.
simpl in |- *.
unfold A in |- *.
rewrite H.
rewrite cPairProjections2.
auto.
rewrite beq_nat_not_refl.
simpl in |- *.
replace (codeList (list_remove nat eq_nat_dec a l)) with
 (codeNth A (evalStrongRecHelp 1 f n a)).
reflexivity.
unfold A in |- *.
rewrite H.
simpl in |- *.
rewrite cPairProjections2.
auto.
auto.
Qed.

Lemma codeListRemoveIsPR : isPR 2 codeListRemove.
Proof.
intros.
unfold codeListRemove in |- *.
apply swapIsPR.
apply evalStrongRecIsPR.
apply
 compose3_3IsPR
  with
    (g := switchPR)
    (f1 := fun n Hrecs p1 : nat => n)
    (f2 := fun n Hrecs p1 : nat =>
           switchPR (charFunction 2 beq_nat (cPairPi1 (pred n)) p1)
             (codeNth (n - S (cPairPi2 (pred n))) Hrecs)
             (S
                (cPair (cPairPi1 (pred n))
                   (codeNth (n - S (cPairPi2 (pred n))) Hrecs))))
    (f3 := fun n Hrecs p1 : nat => codeList nil).
apply pi1_3IsPR.
assert
 (isPR 3 (fun n Hrecs p1 : nat => codeNth (n - S (cPairPi2 (pred n))) Hrecs)).
apply
 filter110IsPR
  with (g := fun n Hrecs : nat => codeNth (n - S (cPairPi2 (pred n))) Hrecs).
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
apply compose1_1IsPR with (f := fun n : nat => cPairPi2 (pred n)).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi2IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply
 compose3_3IsPR
  with
    (g := switchPR)
    (f1 := fun n Hrecs p1 : nat =>
           charFunction 2 beq_nat (cPairPi1 (pred n)) p1)
    (f2 := fun n Hrecs p1 : nat => codeNth (n - S (cPairPi2 (pred n))) Hrecs)
    (f3 := fun n Hrecs p1 : nat =>
           S
             (cPair (cPairPi1 (pred n))
                (codeNth (n - S (cPairPi2 (pred n))) Hrecs))).
apply
 filter101IsPR
  with (g := fun n p1 : nat => charFunction 2 beq_nat (cPairPi1 (pred n)) p1).
apply
 compose2_2IsPR
  with (f := fun n p1 : nat => cPairPi1 (pred n)) (g := fun n p1 : nat => p1).
apply filter10IsPR with (g := fun n : nat => cPairPi1 (pred n)).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi1IsPR.
apply pi2_2IsPR.
apply eqIsPR.
apply H.
apply
 compose3_1IsPR
  with
    (g := S)
    (f := fun n Hrecs _ : nat =>
          cPair (cPairPi1 (pred n))
            (codeNth (n - S (cPairPi2 (pred n))) Hrecs)).
apply
 compose3_2IsPR
  with
    (g := cPair)
    (f1 := fun n Hrecs _ : nat => cPairPi1 (pred n))
    (f2 := fun n Hrecs _ : nat => codeNth (n - S (cPairPi2 (pred n))) Hrecs).
apply filter100IsPR with (g := fun n : nat => cPairPi1 (pred n)).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi1IsPR.
apply H.
apply cPairIsPR.
apply succIsPR.
apply switchIsPR.
exists (composeFunc 3 0 (PRnil _) zeroFunc).
simpl in |- *.
auto.
apply switchIsPR.
Qed.

Definition codeIn (a l : nat) : nat :=
  evalStrongRec 1
    (fun n Hrecs p1 : nat =>
     switchPR n
       (switchPR (charFunction 2 beq_nat (cPairPi1 (pred n)) p1) 1
          (codeNth (n - S (cPairPi2 (pred n))) Hrecs)) 0) l a.

Lemma codeInCorrect :
 forall (a : nat) (l : list nat),
 codeIn a (codeList l) =
 match In_dec eq_nat_dec a l with
 | left _ => 1
 | right _ => 0
 end.
Proof.
intros.
induction l as [| a0 l Hrecl]; simpl in |- *.
unfold codeIn, evalStrongRec in |- *.
simpl in |- *.
rewrite cPairProjections1.
reflexivity.
unfold codeIn, evalStrongRec in |- *.
unfold evalComposeFunc in |- *.
unfold evalOneParamList in |- *.
rewrite computeEvalStrongRecHelp.
unfold evalList in |- *.
set
 (f :=
  fun n Hrecs p1 : nat =>
  switchPR n
    (switchPR (charFunction 2 beq_nat (cPairPi1 (pred n)) p1) 1
       (codeNth (n - S (cPairPi2 (pred n))) Hrecs)) 0) 
 in *.
set (m := cPairPi2 (pred (S (cPair a0 (codeList l))))) in *.
set (n := S (cPair a0 (codeList l))) in *.
simpl in |- *.
repeat rewrite cPairProjections1.
induction (eq_nat_dec a0 a).
rewrite a1.
rewrite <- beq_nat_refl.
simpl in |- *.
reflexivity.
rewrite beq_nat_not_refl.
simpl in |- *.
assert
 (extEqual _
    (evalComposeFunc 1 1 (Vector.cons _ (evalStrongRecHelp 1 f n) 0 (Vector.nil _))
       (fun b : nat => codeNth (n - S m) b)) (evalStrongRec 1 f m)).
apply (evalStrongRecHelp2 1).
unfold m in |- *.
unfold n in |- *.
simpl in |- *.
rewrite cPairProjections2.
apply le_lt_n_Sm.
apply cPairLe2.
simpl in H.
rewrite H.
unfold codeIn in Hrecl.
move f after Hrecl;  fold f in Hrecl.
unfold m, n in |- *.
simpl in |- *.
rewrite cPairProjections2.
rewrite Hrecl.
clear H f Hrecl.
induction (In_dec eq_nat_dec a l).
induction (In_dec eq_nat_dec a (a0 :: l)).
reflexivity.
elim b0.
simpl in |- *.
auto.
induction (In_dec eq_nat_dec a (a0 :: l)).
induction a1 as [H| H].
elim b; auto.
elim b0; auto.
reflexivity.
auto.
Qed.

Lemma codeInIsPR : isPR 2 codeIn.
Proof.
unfold codeIn in |- *.
apply swapIsPR.
apply evalStrongRecIsPR.
apply
 compose3_3IsPR
  with
    (g := switchPR)
    (f1 := fun n Hrecs p1 : nat => n)
    (f2 := fun n Hrecs p1 : nat =>
           switchPR (charFunction 2 beq_nat (cPairPi1 (pred n)) p1) 1
             (codeNth (n - S (cPairPi2 (pred n))) Hrecs))
    (f3 := fun n Hrecs p1 : nat => 0).
apply pi1_3IsPR.
apply
 compose3_3IsPR
  with
    (g := switchPR)
    (f1 := fun n Hrecs p1 : nat =>
           charFunction 2 beq_nat (cPairPi1 (pred n)) p1)
    (f2 := fun n Hrecs p1 : nat => 1)
    (f3 := fun n Hrecs p1 : nat => codeNth (n - S (cPairPi2 (pred n))) Hrecs).
apply
 filter101IsPR
  with (g := fun n p1 : nat => charFunction 2 beq_nat (cPairPi1 (pred n)) p1).
apply
 compose2_2IsPR
  with
    (h := charFunction 2 beq_nat)
    (f := fun n p1 : nat => cPairPi1 (pred n))
    (g := fun n p1 : nat => p1).
apply filter10IsPR with (g := fun n : nat => cPairPi1 (pred n)).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi1IsPR.
apply pi2_2IsPR.
apply eqIsPR.
apply filter100IsPR with (g := fun _ : nat => 1).
apply const1_NIsPR.
apply
 filter110IsPR
  with (g := fun n Hrecs : nat => codeNth (n - S (cPairPi2 (pred n))) Hrecs).
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
apply switchIsPR.
apply filter100IsPR with (g := fun _ : nat => 0).
apply const1_NIsPR.
apply switchIsPR.
Qed.

Definition codeNoDup : nat -> nat :=
  evalStrongRec 0
    (fun l recs : nat =>
     switchPR l
       (switchPR
          (codeIn (cPairPi1 (pred l))
             (codeNth (l - S (cPairPi2 (pred l))) recs))
          (codeNth (l - S (cPairPi2 (pred l))) recs)
          (S
             (cPair (cPairPi1 (pred l))
                (codeNth (l - S (cPairPi2 (pred l))) recs)))) 0).

Lemma codeNoDupCorrect :
 forall l : list nat,
 codeNoDup (codeList l) = codeList (no_dup _ eq_nat_dec l).
Proof.
intros.
unfold codeNoDup in |- *.
set
 (g :=
  fun l0 recs : nat =>
  switchPR l0
    (switchPR
       (codeIn (cPairPi1 (pred l0))
          (codeNth (l0 - S (cPairPi2 (pred l0))) recs))
       (codeNth (l0 - S (cPairPi2 (pred l0))) recs)
       (S
          (cPair (cPairPi1 (pred l0))
             (codeNth (l0 - S (cPairPi2 (pred l0))) recs)))) 0) 
 in *.
induction l as [| a l Hrecl].
simpl in |- *.
unfold evalStrongRec in |- *.
simpl in |- *.
rewrite cPairProjections1.
reflexivity.
simpl in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
unfold g at 1 in |- *.
repeat rewrite evalStrongRecHelp1.
unfold pred in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
rewrite Hrecl.
rewrite codeInCorrect.
induction (In_dec eq_nat_dec a (no_dup nat eq_nat_dec l)).
reflexivity.
reflexivity.
simpl in |- *.
apply le_lt_n_Sm.
apply cPairLe2A.
Qed.

Lemma codeNoDupIsPR : isPR 1 codeNoDup.
Proof.
unfold codeNoDup in |- *.
apply evalStrongRecIsPR.
apply
 compose2_3IsPR
  with
    (f1 := fun l recs : nat => l)
    (f2 := fun l recs : nat =>
           switchPR
             (codeIn (cPairPi1 (pred l))
                (codeNth (l - S (cPairPi2 (pred l))) recs))
             (codeNth (l - S (cPairPi2 (pred l))) recs)
             (S
                (cPair (cPairPi1 (pred l))
                   (codeNth (l - S (cPairPi2 (pred l))) recs))))
    (f3 := fun l recs : nat => 0).
apply pi1_2IsPR.
assert
 (isPR 2 (fun l recs : nat => codeNth (l - S (cPairPi2 (pred l))) recs)).
apply callIsPR with (g := fun l : nat => cPairPi2 (pred l)).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi2IsPR.
apply
 compose2_3IsPR
  with
    (f1 := fun l recs : nat =>
           codeIn (cPairPi1 (pred l))
             (codeNth (l - S (cPairPi2 (pred l))) recs))
    (f2 := fun l recs : nat => codeNth (l - S (cPairPi2 (pred l))) recs)
    (f3 := fun l recs : nat =>
           S
             (cPair (cPairPi1 (pred l))
                (codeNth (l - S (cPairPi2 (pred l))) recs))).
apply
 compose2_2IsPR
  with
    (f := fun l recs : nat => cPairPi1 (pred l))
    (g := fun l recs : nat => codeNth (l - S (cPairPi2 (pred l))) recs).
apply filter10IsPR with (g := fun l : nat => cPairPi1 (pred l)).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi1IsPR.
assumption.
apply codeInIsPR.
assumption.
apply
 compose2_1IsPR
  with
    (f := fun l recs : nat =>
          cPair (cPairPi1 (pred l))
            (codeNth (l - S (cPairPi2 (pred l))) recs)).
apply
 compose2_2IsPR
  with
    (f := fun l recs : nat => cPairPi1 (pred l))
    (g := fun l recs : nat => codeNth (l - S (cPairPi2 (pred l))) recs).
apply filter10IsPR with (g := fun l : nat => cPairPi1 (pred l)).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi1IsPR.
assumption.
apply cPairIsPR.
apply succIsPR.
apply switchIsPR.
apply filter10IsPR with (g := fun _ : nat => 0).
apply const1_NIsPR.
apply switchIsPR.
Qed.
