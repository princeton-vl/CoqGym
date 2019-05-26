Require Import folProof.
Require Import Arith.
Require Import folProp.
Require Import LNN.
Require Import Coq.Lists.List.

Definition wConsistent (T : System) :=
  forall (f : Formula) (v : nat),
  (forall x : nat, In x (freeVarFormula LNN f) -> v = x) ->
  SysPrf T (existH v (notH f)) ->
  exists n : nat, ~ SysPrf T (substituteFormula LNN f v (natToTerm n)).

Lemma wCon2Con : forall T : System, wConsistent T -> Consistent LNN T.
Proof.
intros.
unfold wConsistent in H.
unfold Consistent, Inconsistent in |- *.
assert (SysPrf T (existH 0 (notH (notH (equal (var 0) (var 0)))))).
apply existSimp.
apply nnI.
apply eqRefl.
assert
 (forall x : nat,
  In x (freeVarFormula LNN (notH (equal (var 0) (var 0)))) -> 0 = x).
intros.
simpl in H1.
repeat induction H1; auto.
induction (H _ _ H1 H0).
exists (substituteFormula LNN (notH (equal (var 0) (var 0))) 0 (natToTerm x)).
auto.
Qed.

Definition wInconsistent (T : System) :=
  exists f : Formula,
    (exists v : nat,
       (forall x : nat, In x (freeVarFormula LNN f) -> v = x) /\
       SysPrf T (existH v (notH f)) /\
       (forall n : nat, SysPrf T (substituteFormula LNN f v (natToTerm n)))).

Lemma notCon2wNotCon :
 forall T : System, Inconsistent LNN T -> wInconsistent T.
Proof.
intros.
unfold wInconsistent in |- *.
exists (equal Zero Zero).
exists 0.
split.
intros.
elim H0.
split.
apply H.
intros.
apply H.
Qed.