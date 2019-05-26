Require Import Ensembles.
Require Import Coq.Lists.List.

Require Import ListExt.
Require Import folProof.
Require Import folProp.
Require Import Deduction.

Section Logic_Rules.

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
Let Prf := Prf L.
Let SysPrf := SysPrf L.

Lemma Axm :
 forall (T : System) (f : Formula), mem _ T f -> SysPrf T f.
Proof.
intros.
exists (f :: nil).
exists (AXM L f).
intros.
induction H0 as [H0| H0].
rewrite H0 in H.
assumption.
elim H0.
Qed.

Lemma sysExtend :
 forall (T U : System) (f : Formula),
 Included _ T U -> SysPrf T f -> SysPrf U f.
Proof.
intros.
induction H0 as (x, (x0, H0)).
exists x.
exists x0.
intros.
apply H.
apply H0.
auto.
Qed.

Lemma sysWeaken :
 forall (T : System) (f g : Formula), SysPrf T f -> SysPrf (Ensembles.Add _ T g) f.
Proof.
intros.
apply sysExtend with T.
unfold Included in |- *.
intros.
left.
auto.
auto.
Qed.

Lemma impI :
 forall (T : System) (f g : Formula),
 SysPrf (Ensembles.Add _ T g) f -> SysPrf T (impH g f).
Proof.
intros.
apply (DeductionTheorem L).
assumption.
Qed.

Lemma impE :
 forall (T : System) (f g : Formula),
 SysPrf T (impH g f) -> SysPrf T g -> SysPrf T f.
Proof.
intros.
induction H as (x, (x0, H)).
induction H0 as (x1, (x2, H0)).
set (A1 := MP L _ _ _ _ x0 x2) in *.
exists (x ++ x1).
exists A1.
intros.
induction (in_app_or _ _ _ H1); auto.
Qed.

Lemma contradiction :
 forall (T : System) (f g : Formula),
 SysPrf T f -> SysPrf T (notH f) -> SysPrf T g.
Proof.
intros.
eapply impE with f.
eapply impE with (impH (notH g) (notH f)).
exists (nil (A:=Formula)).
exists (CP L g f).
contradiction.
apply impI.
apply sysWeaken.
assumption.
assumption.
Qed.

Lemma nnE :
 forall (T : System) (f : Formula), SysPrf T (notH (notH f)) -> SysPrf T f.
Proof.
intros.
apply impE with (notH (notH f)).
apply impE with (impH (notH f) (notH (notH (notH f)))).
exists (nil (A:=Formula)).
exists (CP L f (notH (notH f))).
contradiction.
apply impI.
apply contradiction with (notH f).
apply Axm.
right; constructor.
apply sysWeaken.
assumption.
assumption.
Qed.

Lemma noMiddle : forall (T : System) (f : Formula), SysPrf T (orH (notH f) f).
Proof.
intros.
unfold orH, fol.orH in |- *.
apply impI.
apply nnE.
apply Axm; right; constructor.
Qed.

Lemma nnI :
 forall (T : System) (f : Formula), SysPrf T f -> SysPrf T (notH (notH f)).
Proof.
intros.
apply impE with f.
apply impE with (impH (notH (notH (notH f))) (notH f)).
exists (nil (A:=Formula)).
exists (CP L (notH (notH f)) f).
contradiction.
apply impI.
apply contradiction with f.
apply sysWeaken.
assumption.
apply nnE.
apply Axm; right; constructor.
assumption.
Qed.

Lemma cp1 :
 forall (T : System) (f g : Formula),
 SysPrf T (impH (notH f) (notH g)) -> SysPrf T (impH g f).
Proof.
intros.
apply impE with (impH (notH f) (notH g)).
exists (nil (A:=Formula)).
exists (CP L f g).
contradiction.
assumption.
Qed.

Lemma cp2 :
 forall (T : System) (f g : Formula),
 SysPrf T (impH g f) -> SysPrf T (impH (notH f) (notH g)).
Proof.
intros.
apply impE with (impH (notH (notH g)) (notH (notH f))).
exists (nil (A:=Formula)).
exists (CP L (notH g) (notH f)).
contradiction.
apply impI.
apply nnI.
apply impE with g.
apply sysWeaken.
assumption.
apply nnE.
apply Axm; right; constructor.
Qed.

Lemma orI1 :
 forall (T : System) (f g : Formula), SysPrf T f -> SysPrf T (orH f g).
Proof.
intros.
unfold orH, fol.orH in |- *.
apply impI.
apply contradiction with f.
apply sysWeaken.
assumption.
apply Axm; right; constructor.
Qed.

Lemma orI2 :
 forall (T : System) (f g : Formula), SysPrf T g -> SysPrf T (orH f g).
Proof.
intros.
unfold orH, fol.orH in |- *.
apply impI.
apply sysWeaken.
assumption.
Qed.

Lemma orE :
 forall (T : System) (f g h : Formula),
 SysPrf T (orH f g) ->
 SysPrf T (impH f h) -> SysPrf T (impH g h) -> SysPrf T h.
Proof.
intros.
unfold orH, fol.orH in H.
apply impE with (impH h h).
apply cp1.
apply impE with (impH (notH h) h).
apply impI.
apply impI.
apply contradiction with h.
apply impE with (notH h).
apply Axm; left; right; constructor.
apply Axm; right; constructor.
apply Axm; right; constructor.
apply impI.
apply impE with g.
apply sysWeaken; assumption.
apply impE with (notH f).
apply sysWeaken; assumption.
apply impE with (notH h).
apply cp2.
apply sysWeaken; assumption.
apply Axm; right; constructor.
apply impI.
apply Axm; right; constructor.
Qed.

Lemma orSys :
 forall (T : System) (f g h : Formula),
 SysPrf (Ensembles.Add _ T f) h -> SysPrf (Ensembles.Add _ T g) h -> SysPrf (Ensembles.Add _ T (orH f g)) h.
Proof.
intros.
eapply orE.
apply Axm; right; constructor.
apply sysWeaken.
apply impI.
assumption.
apply sysWeaken.
apply impI.
assumption.
Qed.

Lemma andI :
 forall (T : System) (f g : Formula),
 SysPrf T f -> SysPrf T g -> SysPrf T (andH f g).
Proof.
intros.
unfold andH, fol.andH in |- *.
apply orE with (notH (orH (notH f) (notH g))) (orH (notH f) (notH g)).
apply noMiddle.
apply impI.
apply Axm; right; constructor.
apply impI.
apply orE with (notH f) (notH g).
apply Axm; right; constructor.
apply cp2.
apply impI.
repeat apply sysWeaken.
assumption.
apply cp2.
apply impI.
repeat apply sysWeaken.
assumption.
Qed.

Lemma andE1 :
 forall (T : System) (f g : Formula), SysPrf T (andH f g) -> SysPrf T f.
Proof.
intros.
apply nnE.
apply impE with (andH f g).
unfold andH, fol.andH in |- *.
apply cp2.
apply impI.
apply orI1.
apply Axm; right; constructor.
assumption.
Qed.

Lemma andE2 :
 forall (T : System) (f g : Formula), SysPrf T (andH f g) -> SysPrf T g.
Proof.
intros.
apply nnE.
apply impE with (andH f g).
unfold andH, fol.andH in |- *.
apply cp2.
apply impI.
apply orI2.
apply Axm; right; constructor.
assumption.
Qed.

Lemma iffI :
 forall (T : System) (f g : Formula),
 SysPrf T (impH f g) -> SysPrf T (impH g f) -> SysPrf T (iffH f g).
Proof.
intros.
unfold iffH, fol.iffH in |- *.
apply andI; auto.
Qed.

Lemma iffE1 :
 forall (T : System) (f g : Formula),
 SysPrf T (iffH f g) -> SysPrf T (impH f g).
Proof.
intros.
unfold iffH, fol.iffH in H.
eapply andE1.
apply H.
Qed.

Lemma iffE2 :
 forall (T : System) (f g : Formula),
 SysPrf T (iffH f g) -> SysPrf T (impH g f).
Proof.
intros.
unfold iffH, fol.iffH in H.
eapply andE2.
apply H.
Qed.

Lemma forallI :
 forall (T : System) (f : Formula) (v : nat),
 ~ In_freeVarSys L v T -> SysPrf T f -> SysPrf T (forallH v f).
Proof.
intros.
induction H0 as (x, H0); induction H0 as (x0, H0).
exists x.
assert (~ In v (freeVarListFormula L x)).
unfold not in |- *; intros; elim H.
induction (In_freeVarListFormulaE _ _ _ H1).
exists x1.
split.
tauto.
apply H0.
tauto.
exists (GEN L _ _ _ H1 x0).
auto.
Qed.

Lemma forallE :
 forall (T : System) (f : Formula) (v : nat) (t : Term),
 SysPrf T (forallH v f) -> SysPrf T (substituteFormula L f v t).
Proof.
intros.
apply impE with (forallH v f).
exists (nil (A:=Formula)).
exists (FA1 L f v t).
contradiction.
assumption.
Qed.

Lemma forallSimp :
 forall (T : System) (f : Formula) (v : nat),
 SysPrf T (forallH v f) -> SysPrf T f.
Proof.
intros.
rewrite <- subFormulaId with L f v.
apply forallE.
assumption.
Qed.

Lemma existI :
 forall (T : System) (f : Formula) (v : nat) (t : Term),
 SysPrf T (substituteFormula L f v t) -> SysPrf T (existH v f).
Proof.
intros.
unfold existH, fol.existH in |- *.
apply impE with (notH (notH (substituteFormula L f v t))).
apply cp2.
apply impI.
rewrite <- (subFormulaNot L).
apply forallE.
apply Axm; right; constructor.
apply nnI.
assumption.
Qed.

Lemma existE :
 forall (T : System) (f g : Formula) (v : nat),
 ~ In_freeVarSys L v T ->
 ~ In v (freeVarFormula L g) ->
 SysPrf T (existH v f) -> SysPrf T (impH f g) -> SysPrf T g.
Proof.
intros.
unfold existH, fol.existH in H1.
apply nnE.
apply impE with (fol.notH L (fol.forallH L v (fol.notH L f))).
apply cp2.
apply impI.
apply impE with (forallH v (notH g)).
apply impE with (forallH v (impH (notH g) (notH f))).
exists (nil (A:=Formula)).
exists (FA3 L (notH g) (notH f) v).
contradiction.
apply sysWeaken.
apply forallI.
auto.
apply cp2.
assumption.
apply impE with (notH g).
exists (nil (A:=Formula)).
exists (FA2 L (notH g) v H0).
contradiction.
apply Axm; right; constructor.
assumption.
Qed.

Lemma existSimp :
 forall (T : System) (f : Formula) (v : nat),
 SysPrf T f -> SysPrf T (existH v f).
Proof.
intros.
eapply existI.
rewrite subFormulaId.
assumption.
Qed.

Lemma existSys :
 forall (T : System) (f g : Formula) (v : nat),
 ~ In_freeVarSys L v T ->
 ~ In v (freeVarFormula L g) ->
 SysPrf (Ensembles.Add _ T f) g -> SysPrf (Ensembles.Add _ T (existH v f)) g.
Proof.
intros.
eapply existE.
unfold not in |- *; intros; elim H.
induction H2 as (x, H2).
exists x.
induction H2 as (H2, H3).
split.
apply H2.
induction H3 as [x H3| x H3].
assumption.
induction H3.
simpl in H2.
absurd (v = v).
eapply In_list_remove2.
apply H2.
auto.
assumption.
apply Axm; right; constructor.
apply sysWeaken.
apply impI.
assumption.
Qed.

Section Not_Rules.

Lemma absurd1 :
 forall (T : System) (f : Formula),
 SysPrf T (impH f (notH f)) -> SysPrf T (notH f).
Proof. 
intros.
apply orE with (notH f) f.
apply noMiddle.
apply impI.
apply Axm; right; constructor.
assumption.
Qed.

Lemma nImp :
 forall (T : System) (f g : Formula),
 SysPrf T (andH f (notH g)) -> SysPrf T (notH (impH f g)).
Proof.
intros.
apply absurd1.
apply impI.
apply contradiction with g.
apply impE with f.
apply Axm; right; constructor.
eapply andE1.
apply sysWeaken.
apply H.
apply sysWeaken.
eapply andE2.
apply H.
Qed.

Lemma nOr :
 forall (T : System) (f g : Formula),
 SysPrf T (andH (notH f) (notH g)) -> SysPrf T (notH (orH f g)).
Proof.
intros.
apply absurd1.
apply impI.
apply orSys.
apply contradiction with f.
apply Axm; right; constructor.
apply sysWeaken.
eapply andE1.
apply H.
apply contradiction with g.
apply Axm; right; constructor.
apply sysWeaken.
eapply andE2.
apply H.
Qed.

Lemma nAnd :
 forall (T : System) (f g : Formula),
 SysPrf T (orH (notH f) (notH g)) -> SysPrf T (notH (andH f g)).
Proof.
intros.
unfold andH, fol.andH in |- *.
apply nnI.
assumption.
Qed.

Lemma nForall :
 forall (T : System) (f : Formula) (v : nat),
 SysPrf T (existH v (notH f)) -> SysPrf T (notH (forallH v f)).
Proof.
intros.
apply impE with (existH v (notH f)).
apply sysExtend with (Empty_set Formula).
unfold Included in |- *.
intros.
induction H0.
apply impI.
apply existSys.
unfold not in |- *; intros.
induction H0 as (x, H0); induction H0 as (H0, H1).
induction H1.
simpl in |- *.
unfold not in |- *; intro.
absurd (v = v).
eapply In_list_remove2.
apply H0.
reflexivity.
apply impE with (notH f).
apply cp2.
apply sysWeaken.
apply impI.
eapply forallSimp.
apply Axm; right; constructor.
apply Axm; right; constructor.
assumption.
Qed.

Lemma nExist :
 forall (T : System) (f : Formula) (v : nat),
 SysPrf T (forallH v (notH f)) -> SysPrf T (notH (existH v f)).
Proof.
intros.
unfold existH, fol.existH in |- *.
apply nnI.
assumption.
Qed.

End Not_Rules.

Section Other_Rules.

Lemma impRefl : forall (T : System) (f : Formula), SysPrf T (impH f f).
Proof.
intros.
apply impI.
apply Axm; right; constructor.
Qed.

Lemma impTrans :
 forall (T : System) (f g h : Formula),
 SysPrf T (impH f g) -> SysPrf T (impH g h) -> SysPrf T (impH f h).
Proof.
intros.
apply impI.
apply impE with g.
apply sysWeaken.
apply H0.
apply impE with f.
apply sysWeaken.
apply H.
apply Axm; right; constructor.
Qed.

Lemma orSym :
 forall (T : System) (f g : Formula),
 SysPrf T (orH f g) -> SysPrf T (orH g f).
Proof.
intros.
eapply orE.
apply H.
apply impI.
apply orI2.
apply Axm; right; constructor.
apply impI.
apply orI1.
apply Axm; right; constructor.
Qed.

Lemma andSym :
 forall (T : System) (f g : Formula),
 SysPrf T (andH f g) -> SysPrf T (andH g f).
Proof.
intros.
apply andI.
eapply andE2.
apply H.
eapply andE1.
apply H.
Qed.

Lemma iffRefl : forall (T : System) (f : Formula), SysPrf T (iffH f f).
Proof.
intros.
apply iffI.
apply impRefl.
apply impRefl.
Qed.

Lemma iffSym :
 forall (T : System) (f g : Formula),
 SysPrf T (iffH f g) -> SysPrf T (iffH g f).
Proof.
unfold iffH, fol.iffH in |- *.
intros.
apply andSym.
assumption.
Qed.

Lemma iffTrans :
 forall (T : System) (f g h : Formula),
 SysPrf T (iffH f g) -> SysPrf T (iffH g h) -> SysPrf T (iffH f h).
Proof.
intros.
apply iffI.
eapply impTrans.
apply iffE1.
apply H.
apply iffE1.
apply H0.
eapply impTrans.
apply iffE2.
apply H0.
apply iffE2.
apply H.
Qed.

End Other_Rules.

Lemma openClosed :
 forall (T : System) (f : Formula), SysPrf T (close L f) -> SysPrf T f.
Proof.
intros T f.
unfold close in |- *.
generalize (no_dup nat Peano_dec.eq_nat_dec (freeVarFormula L f)).
intros.
induction l as [| a l Hrecl].
apply H.
simpl in H.
apply Hrecl.
eapply forallSimp.
apply H.
Qed.

End Logic_Rules.
