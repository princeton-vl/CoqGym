Require Import primRec.
Require Import cPair.
Require Import Arith.
Require Import code.
Require Import folProp.
Require Import folProof.
Require Import Languages.
Require LNN. 
Require LNT.

Definition natToTermLNN := LNN.natToTerm.

Definition natToTermLNT := LNT.natToTerm.

Definition codeNatToTerm : nat -> nat :=
  nat_rec (fun _ => nat) (cPair 4 0)
    (fun _ rec : nat => cPair 3 (S (cPair rec 0))).

Lemma codeNatToTermCorrectLNN :
 forall n : nat,
 codeNatToTerm n = codeTerm LNN codeLNTFunction (natToTermLNN n).
Proof.
intro.
induction n as [| n Hrecn].
reflexivity.
simpl in |- *.
rewrite Hrecn.
reflexivity.
Qed.

Lemma codeNatToTermCorrectLNT :
 forall n : nat,
 codeNatToTerm n = codeTerm LNT codeLNTFunction (natToTermLNT n).
Proof.
intro.
induction n as [| n Hrecn].
reflexivity.
simpl in |- *.
rewrite Hrecn.
reflexivity.
Qed.

Lemma codeNatToTermIsPR : isPR 1 codeNatToTerm.
Proof.
unfold codeNatToTerm in |- *.
apply
 indIsPR
  with (f := fun _ rec : nat => cPair 3 (S (cPair rec 0))) (g := cPair 4 0).
apply filter01IsPR with (g := fun rec : nat => cPair 3 (S (cPair rec 0))).
apply
 compose1_2IsPR
  with (f := fun _ : nat => 3) (f' := fun rec : nat => S (cPair rec 0)).
apply const1_NIsPR.
apply compose1_1IsPR with (f := fun rec : nat => cPair rec 0).
apply
 compose1_2IsPR with (f := fun rec : nat => rec) (f' := fun _ : nat => 0).
apply idIsPR.
apply const1_NIsPR.
apply cPairIsPR.
apply succIsPR.
apply cPairIsPR.
Qed.