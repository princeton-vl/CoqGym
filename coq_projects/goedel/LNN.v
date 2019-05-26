Require Import Arith.
Require Import Ensembles.
Require Import Coq.Lists.List.

Require Export Languages.
Require Import folProof.
Require Import folProp.
Require Import folLogic3.

Definition Formula := Formula LNN.
Definition Formulas := Formulas LNN.
Definition System := System LNN.
Definition Sentence := Sentence LNN.
Definition Term := Term LNN.
Definition Terms := Terms LNN.
Definition var := var LNN.
Definition equal := equal LNN.
Definition impH := impH LNN.
Definition notH := notH LNN.
Definition iffH := iffH LNN.
Definition forallH := forallH LNN.
Definition orH := orH LNN.
Definition andH := andH LNN.
Definition existH := existH LNN.
Definition ifThenElseH := ifThenElseH LNN.
Definition SysPrf := SysPrf LNN.

Definition Plus (x y : Term) : Term :=
  apply LNN Plus (Tcons LNN 1 x (Tcons LNN 0 y (Tnil LNN))).

Definition Times (x y : Term) : Term :=
  apply LNN Times (Tcons LNN 1 x (Tcons LNN 0 y (Tnil LNN))).

Definition Succ (x : Term) : Term :=
  apply LNN Succ (Tcons LNN 0 x (Tnil LNN)).

Definition Zero : Term := apply LNN Zero (Tnil LNN).

Definition LT (x y : Term) : Formula :=
  atomic LNN LT (Tcons LNN 1 x (Tcons LNN 0 y (Tnil LNN))). 

Lemma LNN_dec : language_decideable LNN.
Proof.
unfold language_decideable in |- *.
split; decide equality.
Qed.

Section Free_Variables.

Lemma freeVarPlus :
 forall x y : Term,
 freeVarTerm LNN (Plus x y) = freeVarTerm LNN x ++ freeVarTerm LNN y.
Proof.
intros.
rewrite (app_nil_end (freeVarTerm LNN y)).
reflexivity.
Qed.

Lemma freeVarTimes :
 forall x y : Term,
 freeVarTerm LNN (Times x y) = freeVarTerm LNN x ++ freeVarTerm LNN y.
Proof.
intros.
rewrite (app_nil_end (freeVarTerm LNN y)).
reflexivity.
Qed.

Lemma freeVarSucc :
 forall x : Term, freeVarTerm LNN (Succ x) = freeVarTerm LNN x.
Proof.
intros.
rewrite (app_nil_end (freeVarTerm LNN x)).
reflexivity.
Qed.

Lemma freeVarZero : freeVarTerm LNN Zero = nil.
Proof.
reflexivity.
Qed.

Lemma freeVarLT :
 forall x y : Term,
 freeVarFormula LNN (LT x y) = freeVarTerm LNN x ++ freeVarTerm LNN y.
Proof.
intros.
rewrite (app_nil_end (freeVarTerm LNN y)).
reflexivity.
Qed.

End Free_Variables.

Section Logic.

Lemma Axm :
 forall (T : System) (f : Formula), mem _ T f -> SysPrf T f.
Proof.
apply (Axm LNN).
Qed.

Lemma sysExtend :
 forall (T U : System) (f : Formula),
 Included _ T U -> SysPrf T f -> SysPrf U f.
Proof.
apply (sysExtend LNN).
Qed.

Lemma sysWeaken :
 forall (T : System) (f g : Formula), SysPrf T f -> SysPrf (Ensembles.Add _ T g) f.
Proof.
apply (sysWeaken LNN).
Qed.

Lemma impI :
 forall (T : System) (f g : Formula),
 SysPrf (Ensembles.Add _ T g) f -> SysPrf T (impH g f).
Proof.
apply (impI LNN).
Qed.

Lemma impE :
 forall (T : System) (f g : Formula),
 SysPrf T (impH g f) -> SysPrf T g -> SysPrf T f.
Proof.
apply (impE LNN).
Qed.

Lemma contradiction :
 forall (T : System) (f g : Formula),
 SysPrf T f -> SysPrf T (notH f) -> SysPrf T g.
Proof.
apply (contradiction LNN).
Qed.

Lemma nnE :
 forall (T : System) (f : Formula), SysPrf T (notH (notH f)) -> SysPrf T f.
Proof.
apply (nnE LNN).
Qed.

Lemma noMiddle : forall (T : System) (f : Formula), SysPrf T (orH (notH f) f).
Proof.
apply (noMiddle LNN).
Qed.

Lemma nnI :
 forall (T : System) (f : Formula), SysPrf T f -> SysPrf T (notH (notH f)).
Proof.
apply (nnI LNN).
Qed.

Lemma cp1 :
 forall (T : System) (f g : Formula),
 SysPrf T (impH (notH f) (notH g)) -> SysPrf T (impH g f).
Proof.
apply (cp1 LNN).
Qed.

Lemma cp2 :
 forall (T : System) (f g : Formula),
 SysPrf T (impH g f) -> SysPrf T (impH (notH f) (notH g)).
Proof.
apply (cp2 LNN).
Qed.

Lemma orI1 :
 forall (T : System) (f g : Formula), SysPrf T f -> SysPrf T (orH f g).
Proof.
apply (orI1 LNN).
Qed.

Lemma orI2 :
 forall (T : System) (f g : Formula), SysPrf T g -> SysPrf T (orH f g).
Proof.
apply (orI2 LNN).
Qed.

Lemma orE :
 forall (T : System) (f g h : Formula),
 SysPrf T (orH f g) ->
 SysPrf T (impH f h) -> SysPrf T (impH g h) -> SysPrf T h.
Proof.
apply (orE LNN).
Qed.

Lemma orSys :
 forall (T : System) (f g h : Formula),
 SysPrf (Ensembles.Add _ T f) h -> SysPrf (Ensembles.Add _ T g) h -> SysPrf (Ensembles.Add _ T (orH f g)) h.
Proof.
apply (orSys LNN).
Qed.

Lemma andI :
 forall (T : System) (f g : Formula),
 SysPrf T f -> SysPrf T g -> SysPrf T (andH f g).
Proof.
apply (andI LNN).
Qed.

Lemma andE1 :
 forall (T : System) (f g : Formula), SysPrf T (andH f g) -> SysPrf T f.
Proof.
apply (andE1 LNN).
Qed.

Lemma andE2 :
 forall (T : System) (f g : Formula), SysPrf T (andH f g) -> SysPrf T g.
Proof.
apply (andE2 LNN).
Qed.

Lemma iffI :
 forall (T : System) (f g : Formula),
 SysPrf T (impH f g) -> SysPrf T (impH g f) -> SysPrf T (iffH f g).
Proof.
apply (iffI LNN).
Qed.

Lemma iffE1 :
 forall (T : System) (f g : Formula),
 SysPrf T (iffH f g) -> SysPrf T (impH f g).
Proof.
apply (iffE1 LNN).
Qed.

Lemma iffE2 :
 forall (T : System) (f g : Formula),
 SysPrf T (iffH f g) -> SysPrf T (impH g f).
Proof.
apply (iffE2 LNN).
Qed.

Lemma forallI :
 forall (T : System) (f : Formula) (v : nat),
 ~ In_freeVarSys LNN v T -> SysPrf T f -> SysPrf T (forallH v f).
Proof.
apply (forallI LNN).
Qed.

Lemma forallE :
 forall (T : System) (f : Formula) (v : nat) (t : Term),
 SysPrf T (forallH v f) -> SysPrf T (substituteFormula LNN f v t).
Proof.
apply (forallE LNN).
Qed.

Lemma forallSimp :
 forall (T : System) (f : Formula) (v : nat),
 SysPrf T (forallH v f) -> SysPrf T f.
Proof.
apply (forallSimp LNN).
Qed.

Lemma existI :
 forall (T : System) (f : Formula) (v : nat) (t : Term),
 SysPrf T (substituteFormula LNN f v t) -> SysPrf T (existH v f).
Proof.
apply (existI LNN).
Qed.

Lemma existE :
 forall (T : System) (f g : Formula) (v : nat),
 ~ In_freeVarSys LNN v T ->
 ~ In v (freeVarFormula LNN g) ->
 SysPrf T (existH v f) -> SysPrf T (impH f g) -> SysPrf T g.
Proof.
apply (existE LNN).
Qed.

Lemma existSimp :
 forall (T : System) (f : Formula) (v : nat),
 SysPrf T f -> SysPrf T (existH v f).
Proof.
apply (existSimp LNN).
Qed.

Lemma existSys :
 forall (T : System) (f g : Formula) (v : nat),
 ~ In_freeVarSys LNN v T ->
 ~ In v (freeVarFormula LNN g) ->
 SysPrf (Ensembles.Add _ T f) g -> SysPrf (Ensembles.Add _ T (existH v f)) g.
Proof.
apply (existSys LNN).
Qed.

Lemma absurd1 :
 forall (T : System) (f : Formula),
 SysPrf T (impH f (notH f)) -> SysPrf T (notH f).
Proof. 
apply (absurd1 LNN).
Qed.

Lemma nImp :
 forall (T : System) (f g : Formula),
 SysPrf T (andH f (notH g)) -> SysPrf T (notH (impH f g)).
Proof.
apply (nImp LNN).
Qed.

Lemma nOr :
 forall (T : System) (f g : Formula),
 SysPrf T (andH (notH f) (notH g)) -> SysPrf T (notH (orH f g)).
Proof.
apply (nOr LNN).
Qed.

Lemma nAnd :
 forall (T : System) (f g : Formula),
 SysPrf T (orH (notH f) (notH g)) -> SysPrf T (notH (andH f g)).
Proof.
apply (nAnd LNN).
Qed.

Lemma nForall :
 forall (T : System) (f : Formula) (v : nat),
 SysPrf T (existH v (notH f)) -> SysPrf T (notH (forallH v f)).
Proof.
apply (nForall LNN).
Qed.

Lemma nExist :
 forall (T : System) (f : Formula) (v : nat),
 SysPrf T (forallH v (notH f)) -> SysPrf T (notH (existH v f)).
Proof.
apply (nExist LNN).
Qed.

Lemma impRefl : forall (T : System) (f : Formula), SysPrf T (impH f f).
Proof.
apply (impRefl LNN).
Qed.

Lemma impTrans :
 forall (T : System) (f g h : Formula),
 SysPrf T (impH f g) -> SysPrf T (impH g h) -> SysPrf T (impH f h).
Proof.
apply (impTrans LNN).
Qed.

Lemma orSym :
 forall (T : System) (f g : Formula),
 SysPrf T (orH f g) -> SysPrf T (orH g f).
Proof.
apply (orSym LNN).
Qed.

Lemma andSym :
 forall (T : System) (f g : Formula),
 SysPrf T (andH f g) -> SysPrf T (andH g f).
Proof.
apply (andSym LNN).
Qed.

Lemma iffRefl : forall (T : System) (f : Formula), SysPrf T (iffH f f).
Proof.
apply (iffRefl LNN).
Qed.

Lemma iffSym :
 forall (T : System) (f g : Formula),
 SysPrf T (iffH f g) -> SysPrf T (iffH g f).
Proof.
apply (iffSym LNN).
Qed.

Lemma iffTrans :
 forall (T : System) (f g h : Formula),
 SysPrf T (iffH f g) -> SysPrf T (iffH g h) -> SysPrf T (iffH f h).
Proof.
apply (iffTrans LNN).
Qed.

Lemma eqRefl : forall (T : System) (a : Term), SysPrf T (equal a a).
Proof.
apply (eqRefl LNN).
Qed.

Lemma eqSym :
 forall (T : System) (a b : Term),
 SysPrf T (equal a b) -> SysPrf T (equal b a).
Proof.
apply (eqSym LNN).
Qed.

Lemma eqTrans :
 forall (T : System) (a b c : Term),
 SysPrf T (equal a b) -> SysPrf T (equal b c) -> SysPrf T (equal a c).
Proof.
apply (eqTrans LNN).
Qed.

Lemma eqPlus :
 forall (T : System) (a b c d : Term),
 SysPrf T (equal a b) ->
 SysPrf T (equal c d) -> SysPrf T (equal (Plus a c) (Plus b d)).
Proof.
intros.
unfold Plus in |- *.
apply (equalFunction LNN).
simpl in |- *.
induction (consTerms LNN 1 (Tcons LNN 1 a (Tcons LNN 0 c (Tnil LNN)))).
induction x as (a0, b0).
simpl in |- *.
induction (consTerms LNN 1 (Tcons LNN 1 b (Tcons LNN 0 d (Tnil LNN)))).
induction x as (a1, b1).
simpl in |- *.
induction (consTerms LNN 0 b0).
induction x as (a2, b2).
simpl in |- *.
induction (consTerms LNN 0 b1).
induction x as (a3, b3).
simpl in |- *.
repeat split.
simpl in p.
inversion p.
simpl in p0.
inversion p0.
apply H.
simpl in p.
inversion p.
rewrite <- p1 in H3.
simpl in H3.
inversion H3.
simpl in p0.
inversion p0.
rewrite <- p2 in H7.
inversion H7.
apply H0.
Qed.

Lemma eqTimes :
 forall (T : System) (a b c d : Term),
 SysPrf T (equal a b) ->
 SysPrf T (equal c d) -> SysPrf T (equal (Times a c) (Times b d)).
Proof.
intros.
unfold Times in |- *.
apply (equalFunction LNN).
simpl in |- *.
induction (consTerms LNN 1 (Tcons LNN 1 a (Tcons LNN 0 c (Tnil LNN)))).
induction x as (a0, b0).
simpl in |- *.
induction (consTerms LNN 1 (Tcons LNN 1 b (Tcons LNN 0 d (Tnil LNN)))).
induction x as (a1, b1).
simpl in |- *.
induction (consTerms LNN 0 b0).
induction x as (a2, b2).
simpl in |- *.
induction (consTerms LNN 0 b1).
induction x as (a3, b3).
simpl in |- *.
repeat split.
simpl in p.
inversion p.
simpl in p0.
inversion p0.
apply H.
simpl in p.
inversion p.
rewrite <- p1 in H3.
simpl in H3.
inversion H3.
simpl in p0.
inversion p0.
rewrite <- p2 in H7.
inversion H7.
apply H0.
Qed.

Lemma eqSucc :
 forall (T : System) (a b : Term),
 SysPrf T (equal a b) -> SysPrf T (equal (Succ a) (Succ b)).
Proof.
intros.
unfold Succ in |- *.
apply (equalFunction LNN).
simpl in |- *.
induction (consTerms LNN 0 (Tcons LNN 0 a (Tnil LNN))).
induction x as (a0, b0).
simpl in |- *.
induction (consTerms LNN 0 (Tcons LNN 0 b (Tnil LNN))).
induction x as (a1, b1).
simpl in |- *.
repeat split.
simpl in p.
inversion p.
simpl in p0.
inversion p0.
apply H.
Qed.

Lemma eqLT :
 forall (T : System) (a b c d : Term),
 SysPrf T (equal a b) ->
 SysPrf T (equal c d) -> SysPrf T (iffH (LT a c) (LT b d)).
Proof.
intros.
unfold LT in |- *.
apply (equalRelation LNN).
simpl in |- *.
induction (consTerms LNN 1 (Tcons LNN 1 a (Tcons LNN 0 c (Tnil LNN)))).
induction x as (a0, b0).
simpl in |- *.
induction (consTerms LNN 1 (Tcons LNN 1 b (Tcons LNN 0 d (Tnil LNN)))).
induction x as (a1, b1).
simpl in |- *.
induction (consTerms LNN 0 b0).
induction x as (a2, b2).
simpl in |- *.
induction (consTerms LNN 0 b1).
induction x as (a3, b3).
simpl in |- *.
repeat split.
simpl in p.
inversion p.
simpl in p0.
inversion p0.
apply H.
simpl in p.
inversion p.
rewrite <- p1 in H3.
simpl in H3.
inversion H3.
simpl in p0.
inversion p0.
rewrite <- p2 in H7.
inversion H7.
apply H0.
Qed.

End Logic.

Fixpoint natToTerm (n : nat) : Term :=
  match n with
  | O => Zero
  | S m => Succ (natToTerm m)
  end.

Lemma closedNatToTerm :
 forall a v : nat, ~ In v (freeVarTerm LNN (natToTerm a)).
Proof.
intros.
induction a as [| a Hreca].
auto.
simpl in |- *.
rewrite freeVarSucc.
auto.
Qed.
