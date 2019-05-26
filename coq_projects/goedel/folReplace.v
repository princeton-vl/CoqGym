Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import Peano_dec.

Require Import ListExt.
Require Import folProof.
Require Import folLogic.
Require Import folProp.

Section Replacement.

Variable L : Language.
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
Let SysPrf := SysPrf L.

Lemma reduceImp :
 forall (f1 f2 f3 f4 : Formula) (T : System),
 SysPrf T (iffH f1 f3) ->
 SysPrf T (iffH f2 f4) -> SysPrf T (iffH (impH f1 f2) (impH f3 f4)).
Proof.
assert
 (forall (f1 f2 f3 f4 : Formula) (T : System),
  SysPrf T (iffH f1 f3) ->
  SysPrf T (iffH f2 f4) -> SysPrf T (impH (impH f1 f2) (impH f3 f4))).
intros.
repeat apply (impI L).
apply impE with f2.
repeat apply sysWeaken.
apply (iffE1 L).
apply H0.
apply impE with f1.
apply sysWeaken.
apply Axm; right; constructor.
apply impE with f3.
repeat apply sysWeaken.
apply (iffE2 L).
apply H.
apply Axm; right; constructor.
intros.
apply (iffI L).
apply H; auto.
apply H; apply (iffSym L); auto.
Qed.

Lemma reduceNot :
 forall (f1 f2 : Formula) (T : System),
 SysPrf T (iffH f1 f2) -> SysPrf T (iffH (notH f1) (notH f2)).
Proof.
assert
 (forall (f1 f2 : Formula) (T : System),
  SysPrf T (iffH f1 f2) -> SysPrf T (impH (notH f1) (notH f2))).
intros.
apply (cp2 L).
apply (iffE2 L).
apply H.
intros.
apply (iffI L).
apply H.
assumption.
apply H.
apply (iffSym L).
assumption.
Qed.

Lemma impForall :
 forall (f1 f2 : Formula) (v : nat) (T : System),
 ~ In_freeVarSys _ v T ->
 SysPrf T (impH f1 f2) -> SysPrf T (impH (forallH v f1) (forallH v f2)).
Proof.
intros.
apply (impI L).
apply (forallI L).
unfold not in |- *; intros.
induction H1 as (x, H1); induction H1 as (H1, H2).
induction H2 as [x H2| x H2]; [ idtac | induction H2 ].
apply H.
unfold In_freeVarSys in |- *.
exists x.
auto.
apply (In_list_remove2 _ _ _ _ _ H1).
auto.
apply impE with f1.
apply sysWeaken.
apply H0.
eapply forallSimp.
apply Axm; right; constructor.
Qed.

Lemma reduceForall :
 forall (f1 f2 : Formula) (v : nat) (T : System),
 ~ In_freeVarSys _ v T ->
 SysPrf T (iffH f1 f2) -> SysPrf T (iffH (forallH v f1) (forallH v f2)).
Proof.
intros.
apply (iffI L).
apply impForall; auto.
apply (iffE1 L).
apply H0.
apply impForall; auto.
apply (iffE2 L).
apply H0.
Qed.

Lemma reduceOr :
 forall (f1 f2 f3 f4 : Formula) (T : System),
 SysPrf T (iffH f1 f3) ->
 SysPrf T (iffH f2 f4) -> SysPrf T (iffH (orH f1 f2) (orH f3 f4)).
Proof.
assert
 (forall (f1 f2 f3 f4 : Formula) (T : System),
  SysPrf T (iffH f1 f3) ->
  SysPrf T (iffH f2 f4) -> SysPrf T (impH (orH f1 f2) (orH f3 f4))).
intros.
apply (impI L).
apply (orSys L).
apply (orI1 L).
apply impE with f1.
apply sysWeaken.
apply (iffE1 L).
assumption.
apply Axm; right; constructor.
apply (orI2 L).
apply impE with f2.
apply sysWeaken.
apply (iffE1 L).
assumption.
apply Axm; right; constructor.
intros.
apply (iffI L).
apply H; auto.
apply H; apply (iffSym L); auto.
Qed.

Lemma reduceAnd :
 forall (f1 f2 f3 f4 : Formula) (T : System),
 SysPrf T (iffH f1 f3) ->
 SysPrf T (iffH f2 f4) -> SysPrf T (iffH (andH f1 f2) (andH f3 f4)).
Proof.
assert
 (forall (f1 f2 f3 f4 : Formula) (T : System),
  SysPrf T (iffH f1 f3) ->
  SysPrf T (iffH f2 f4) -> SysPrf T (impH (andH f1 f2) (andH f3 f4))).
intros.
apply (impI L).
apply (andI L).
apply impE with f1.
apply sysWeaken.
apply (iffE1 L).
assumption.
eapply (andE1 L).
apply Axm; right; constructor.
apply impE with f2.
apply sysWeaken.
apply (iffE1 L).
assumption.
eapply (andE2 L).
apply Axm; right; constructor.
intros.
apply (iffI L).
apply H; auto.
apply H; apply (iffSym L); auto.
Qed.

Lemma iffExist :
 forall (f1 f2 : Formula) (v : nat) (T : System),
 ~ In_freeVarSys _ v T ->
 SysPrf T (impH f1 f2) -> SysPrf T (impH (existH v f1) (existH v f2)).
Proof.
intros.
unfold existH, fol.existH in |- *.
apply (cp2 L).
apply impForall; auto.
apply (cp2 L).
apply H0.
Qed.

Lemma reduceExist :
 forall (f1 f2 : Formula) (v : nat) (T : System),
 ~ In_freeVarSys _ v T ->
 SysPrf T (iffH f1 f2) -> SysPrf T (iffH (existH v f1) (existH v f2)).
Proof.
intros.
unfold existH, fol.existH in |- *.
apply reduceNot.
apply reduceForall; auto.
apply reduceNot.
apply H0.
Qed.

Lemma reduceIff :
 forall (f1 f2 f3 f4 : Formula) (T : System),
 SysPrf T (iffH f1 f3) ->
 SysPrf T (iffH f2 f4) -> SysPrf T (iffH (iffH f1 f2) (iffH f3 f4)).
Proof.
assert
 (forall (f1 f2 f3 f4 : Formula) (T : System),
  SysPrf T (iffH f1 f3) ->
  SysPrf T (iffH f2 f4) -> SysPrf T (impH (iffH f1 f2) (iffH f3 f4))).
intros.
apply (impI L).
apply (iffTrans L) with f2.
apply (iffTrans L) with f1.
apply sysWeaken.
apply (iffSym L).
apply H.
apply Axm; right; constructor.
apply sysWeaken.
apply H0.
intros.
apply (iffI L).
apply H; auto.
apply H; apply (iffSym L); auto.
Qed.

Lemma reduceIfThenElse :
 forall (f1 f2 f3 f4 f5 f6 : Formula) (T : System),
 SysPrf T (iffH f1 f4) ->
 SysPrf T (iffH f2 f5) ->
 SysPrf T (iffH f3 f6) ->
 SysPrf T (iffH (ifThenElseH f1 f2 f3) (ifThenElseH f4 f5 f6)).
Proof.
intros.
unfold ifThenElseH, fol.ifThenElseH in |- *.
apply reduceAnd; apply reduceImp; auto.
apply reduceNot; auto.
Qed.

Lemma reduceSub :
 forall (T : System) (v : nat) (s : Term) (f g : Formula),
 ~ In_freeVarSys L v T ->
 SysPrf T (iffH f g) ->
 SysPrf T (iffH (substituteFormula L f v s) (substituteFormula L g v s)).
Proof.
assert
 (forall (T : System) (v : nat) (s : Term) (f g : Formula),
  ~ In_freeVarSys L v T ->
  SysPrf T (iffH f g) ->
  SysPrf T (impH (substituteFormula L f v s) (substituteFormula L g v s))).
intros.
rewrite <- (subFormulaImp L).
apply (forallE L).
apply forallI.
assumption.
apply (iffE1 L).
apply H0.
intros.
apply (iffI L).
apply H; auto.
apply H; auto.
apply (iffSym L).
auto.
Qed.

Lemma reduceCloseList :
 forall (l : list nat) (f1 f2 : Formula) (T : System),
 (forall v : nat, In v l -> ~ In_freeVarSys _ v T) ->
 SysPrf T (iffH f1 f2) ->
 SysPrf T (iffH (closeList L l f1) (closeList L l f2)).
Proof.
intro.
induction l as [| a l Hrecl]; simpl in |- *; intros.
apply H0.
apply reduceForall.
apply H.
auto.
apply Hrecl; auto.
Qed.

End Replacement.
