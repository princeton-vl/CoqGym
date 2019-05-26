Require Import primRec.
Require Import code.
Require Import Arith.
Require Import cPair.

Lemma codeForallIsPR : isPR 2 (fun a b : nat => cPair 3 (cPair a b)).
Proof.
apply compose2_2IsPR with (f := fun a b : nat => 3).
apply filter10IsPR with (g := fun _ : nat => 3).
apply const1_NIsPR.
apply cPairIsPR.
apply cPairIsPR.
Qed.

Lemma codeNotIsPR : isPR 1 codeNot.
Proof.
unfold codeNot in |- *.
apply compose1_2IsPR with (f := fun a : nat => 2) (f' := fun a : nat => a).
apply const1_NIsPR.
apply idIsPR.
apply cPairIsPR.
Qed.

Lemma codeImpIsPR : isPR 2 codeImp.
Proof.
unfold codeImp in |- *.
apply compose2_2IsPR with (f := fun a b : nat => 1).
apply filter10IsPR with (g := fun _ : nat => 1).
apply const1_NIsPR.
apply cPairIsPR.
apply cPairIsPR.
Qed.