Require Import Arith.
Require Import Ensembles.
Require Import Coq.Lists.List.

Require Import Languages.
Require Import folProof.
Require Import folProp.
Require Import folLogic3.

Definition Formula := Formula LNT.
Definition Formulas := Formulas LNT.
Definition System := System LNT.
Definition Sentence := Sentence LNT.
Definition Term := Term LNT.
Definition Terms := Terms LNT.
Definition var := var LNT.
Definition equal := equal LNT.
Definition impH := impH LNT.
Definition notH := notH LNT.
Definition iffH := iffH LNT.
Definition forallH := forallH LNT.
Definition orH := orH LNT.
Definition andH := andH LNT.
Definition existH := existH LNT.
Definition ifThenElseH := ifThenElseH LNT.
Definition SysPrf := SysPrf LNT.

Definition Plus (x y : Term) : Term :=
  apply LNT Plus (Tcons LNT 1 x (Tcons LNT 0 y (Tnil LNT))).

Definition Times (x y : Term) : Term :=
  apply LNT Times (Tcons LNT 1 x (Tcons LNT 0 y (Tnil LNT))).

Definition Succ (x : Term) : Term :=
  apply LNT Succ (Tcons LNT 0 x (Tnil LNT)).

Definition Zero : Term := apply LNT Zero (Tnil LNT).

Lemma LNT_dec : language_decideable LNT.
Proof.
unfold language_decideable in |- *.
split; decide equality.
Qed.

Section Free_Variables.

Lemma freeVarPlus :
 forall x y : Term,
 freeVarTerm LNT (Plus x y) = freeVarTerm LNT x ++ freeVarTerm LNT y.
Proof.
intros.
rewrite (app_nil_end (freeVarTerm LNT y)).
reflexivity.
Qed.

Lemma freeVarTimes :
 forall x y : Term,
 freeVarTerm LNT (Times x y) = freeVarTerm LNT x ++ freeVarTerm LNT y.
Proof.
intros.
rewrite (app_nil_end (freeVarTerm LNT y)).
reflexivity.
Qed.

Lemma freeVarSucc :
 forall x : Term, freeVarTerm LNT (Succ x) = freeVarTerm LNT x.
Proof.
intros.
rewrite (app_nil_end (freeVarTerm LNT x)).
reflexivity.
Qed.

Lemma freeVarZero : freeVarTerm LNT Zero = nil.
Proof.
reflexivity.
Qed.

End Free_Variables.

Section Logic.

Lemma Axm :
 forall (T : System) (f : Formula), mem _ T f -> SysPrf T f.
Proof.
apply (Axm LNT).
Qed.

Lemma sysExtend :
 forall (T U : System) (f : Formula),
 Included _ T U -> SysPrf T f -> SysPrf U f.
Proof.
apply (sysExtend LNT).
Qed.

Lemma sysWeaken :
 forall (T : System) (f g : Formula), SysPrf T f -> SysPrf (Ensembles.Add _ T g) f.
Proof.
apply (sysWeaken LNT).
Qed.

Lemma impI :
 forall (T : System) (f g : Formula),
 SysPrf (Ensembles.Add _ T g) f -> SysPrf T (impH g f).
Proof.
apply (impI LNT).
Qed.

Lemma impE :
 forall (T : System) (f g : Formula),
 SysPrf T (impH g f) -> SysPrf T g -> SysPrf T f.
Proof.
apply (impE LNT).
Qed.

Lemma contradiction :
 forall (T : System) (f g : Formula),
 SysPrf T f -> SysPrf T (notH f) -> SysPrf T g.
Proof.
apply (contradiction LNT).
Qed.

Lemma nnE :
 forall (T : System) (f : Formula), SysPrf T (notH (notH f)) -> SysPrf T f.
Proof.
apply (nnE LNT).
Qed.

Lemma noMiddle : forall (T : System) (f : Formula), SysPrf T (orH (notH f) f).
Proof.
apply (noMiddle LNT).
Qed.

Lemma nnI :
 forall (T : System) (f : Formula), SysPrf T f -> SysPrf T (notH (notH f)).
Proof.
apply (nnI LNT).
Qed.

Lemma cp1 :
 forall (T : System) (f g : Formula),
 SysPrf T (impH (notH f) (notH g)) -> SysPrf T (impH g f).
Proof.
apply (cp1 LNT).
Qed.

Lemma cp2 :
 forall (T : System) (f g : Formula),
 SysPrf T (impH g f) -> SysPrf T (impH (notH f) (notH g)).
Proof.
apply (cp2 LNT).
Qed.

Lemma orI1 :
 forall (T : System) (f g : Formula), SysPrf T f -> SysPrf T (orH f g).
Proof.
apply (orI1 LNT).
Qed.

Lemma orI2 :
 forall (T : System) (f g : Formula), SysPrf T g -> SysPrf T (orH f g).
Proof.
apply (orI2 LNT).
Qed.

Lemma orE :
 forall (T : System) (f g h : Formula),
 SysPrf T (orH f g) ->
 SysPrf T (impH f h) -> SysPrf T (impH g h) -> SysPrf T h.
Proof.
apply (orE LNT).
Qed.

Lemma orSys :
 forall (T : System) (f g h : Formula),
 SysPrf (Ensembles.Add _ T f) h -> SysPrf (Ensembles.Add _ T g) h -> SysPrf (Ensembles.Add _ T (orH f g)) h.
Proof.
apply (orSys LNT).
Qed.

Lemma andI :
 forall (T : System) (f g : Formula),
 SysPrf T f -> SysPrf T g -> SysPrf T (andH f g).
Proof.
apply (andI LNT).
Qed.

Lemma andE1 :
 forall (T : System) (f g : Formula), SysPrf T (andH f g) -> SysPrf T f.
Proof.
apply (andE1 LNT).
Qed.

Lemma andE2 :
 forall (T : System) (f g : Formula), SysPrf T (andH f g) -> SysPrf T g.
Proof.
apply (andE2 LNT).
Qed.

Lemma iffI :
 forall (T : System) (f g : Formula),
 SysPrf T (impH f g) -> SysPrf T (impH g f) -> SysPrf T (iffH f g).
Proof.
apply (iffI LNT).
Qed.

Lemma iffE1 :
 forall (T : System) (f g : Formula),
 SysPrf T (iffH f g) -> SysPrf T (impH f g).
Proof.
apply (iffE1 LNT).
Qed.

Lemma iffE2 :
 forall (T : System) (f g : Formula),
 SysPrf T (iffH f g) -> SysPrf T (impH g f).
Proof.
apply (iffE2 LNT).
Qed.

Lemma forallI :
 forall (T : System) (f : Formula) (v : nat),
 ~ In_freeVarSys LNT v T -> SysPrf T f -> SysPrf T (forallH v f).
Proof.
apply (forallI LNT).
Qed.

Lemma forallE :
 forall (T : System) (f : Formula) (v : nat) (t : Term),
 SysPrf T (forallH v f) -> SysPrf T (substituteFormula LNT f v t).
Proof.
apply (forallE LNT).
Qed.

Lemma forallSimp :
 forall (T : System) (f : Formula) (v : nat),
 SysPrf T (forallH v f) -> SysPrf T f.
Proof.
apply (forallSimp LNT).
Qed.

Lemma existI :
 forall (T : System) (f : Formula) (v : nat) (t : Term),
 SysPrf T (substituteFormula LNT f v t) -> SysPrf T (existH v f).
Proof.
apply (existI LNT).
Qed.

Lemma existE :
 forall (T : System) (f g : Formula) (v : nat),
 ~ In_freeVarSys LNT v T ->
 ~ In v (freeVarFormula LNT g) ->
 SysPrf T (existH v f) -> SysPrf T (impH f g) -> SysPrf T g.
Proof.
apply (existE LNT).
Qed.

Lemma existSimp :
 forall (T : System) (f : Formula) (v : nat),
 SysPrf T f -> SysPrf T (existH v f).
Proof.
apply (existSimp LNT).
Qed.

Lemma existSys :
 forall (T : System) (f g : Formula) (v : nat),
 ~ In_freeVarSys LNT v T ->
 ~ In v (freeVarFormula LNT g) ->
 SysPrf (Ensembles.Add _ T f) g -> SysPrf (Ensembles.Add _ T (existH v f)) g.
Proof.
apply (existSys LNT).
Qed.

Lemma absurd1 :
 forall (T : System) (f : Formula),
 SysPrf T (impH f (notH f)) -> SysPrf T (notH f).
Proof. 
apply (absurd1 LNT).
Qed.

Lemma nImp :
 forall (T : System) (f g : Formula),
 SysPrf T (andH f (notH g)) -> SysPrf T (notH (impH f g)).
Proof.
apply (nImp LNT).
Qed.

Lemma nOr :
 forall (T : System) (f g : Formula),
 SysPrf T (andH (notH f) (notH g)) -> SysPrf T (notH (orH f g)).
Proof.
apply (nOr LNT).
Qed.

Lemma nAnd :
 forall (T : System) (f g : Formula),
 SysPrf T (orH (notH f) (notH g)) -> SysPrf T (notH (andH f g)).
Proof.
apply (nAnd LNT).
Qed.

Lemma nForall :
 forall (T : System) (f : Formula) (v : nat),
 SysPrf T (existH v (notH f)) -> SysPrf T (notH (forallH v f)).
Proof.
apply (nForall LNT).
Qed.

Lemma nExist :
 forall (T : System) (f : Formula) (v : nat),
 SysPrf T (forallH v (notH f)) -> SysPrf T (notH (existH v f)).
Proof.
apply (nExist LNT).
Qed.

Lemma impRefl : forall (T : System) (f : Formula), SysPrf T (impH f f).
Proof.
apply (impRefl LNT).
Qed.

Lemma impTrans :
 forall (T : System) (f g h : Formula),
 SysPrf T (impH f g) -> SysPrf T (impH g h) -> SysPrf T (impH f h).
Proof.
apply (impTrans LNT).
Qed.

Lemma orSym :
 forall (T : System) (f g : Formula),
 SysPrf T (orH f g) -> SysPrf T (orH g f).
Proof.
apply (orSym LNT).
Qed.

Lemma andSym :
 forall (T : System) (f g : Formula),
 SysPrf T (andH f g) -> SysPrf T (andH g f).
Proof.
apply (andSym LNT).
Qed.

Lemma iffRefl : forall (T : System) (f : Formula), SysPrf T (iffH f f).
Proof.
apply (iffRefl LNT).
Qed.

Lemma iffSym :
 forall (T : System) (f g : Formula),
 SysPrf T (iffH f g) -> SysPrf T (iffH g f).
Proof.
apply (iffSym LNT).
Qed.

Lemma iffTrans :
 forall (T : System) (f g h : Formula),
 SysPrf T (iffH f g) -> SysPrf T (iffH g h) -> SysPrf T (iffH f h).
Proof.
apply (iffTrans LNT).
Qed.

Lemma eqRefl : forall (T : System) (a : Term), SysPrf T (equal a a).
Proof.
apply (eqRefl LNT).
Qed.

Lemma eqSym :
 forall (T : System) (a b : Term),
 SysPrf T (equal a b) -> SysPrf T (equal b a).
Proof.
apply (eqSym LNT).
Qed.

Lemma eqTrans :
 forall (T : System) (a b c : Term),
 SysPrf T (equal a b) -> SysPrf T (equal b c) -> SysPrf T (equal a c).
Proof.
apply (eqTrans LNT).
Qed.

Lemma eqPlus :
 forall (T : System) (a b c d : Term),
 SysPrf T (equal a b) ->
 SysPrf T (equal c d) -> SysPrf T (equal (Plus a c) (Plus b d)).
Proof.
intros.
unfold Plus in |- *.
apply (equalFunction LNT).
simpl in |- *.
induction (consTerms LNT 1 (Tcons LNT 1 a (Tcons LNT 0 c (Tnil LNT)))).
induction x as (a0, b0).
simpl in |- *.
induction (consTerms LNT 1 (Tcons LNT 1 b (Tcons LNT 0 d (Tnil LNT)))).
induction x as (a1, b1).
simpl in |- *.
induction (consTerms LNT 0 b0).
induction x as (a2, b2).
simpl in |- *.
induction (consTerms LNT 0 b1).
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
apply (equalFunction LNT).
simpl in |- *.
induction (consTerms LNT 1 (Tcons LNT 1 a (Tcons LNT 0 c (Tnil LNT)))).
induction x as (a0, b0).
simpl in |- *.
induction (consTerms LNT 1 (Tcons LNT 1 b (Tcons LNT 0 d (Tnil LNT)))).
induction x as (a1, b1).
simpl in |- *.
induction (consTerms LNT 0 b0).
induction x as (a2, b2).
simpl in |- *.
induction (consTerms LNT 0 b1).
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
apply (equalFunction LNT).
simpl in |- *.
induction (consTerms LNT 0 (Tcons LNT 0 a (Tnil LNT))).
induction x as (a0, b0).
simpl in |- *.
induction (consTerms LNT 0 (Tcons LNT 0 b (Tnil LNT))).
induction x as (a1, b1).
simpl in |- *.
repeat split.
simpl in p.
inversion p.
simpl in p0.
inversion p0.
apply H.
Qed.

End Logic.

Fixpoint natToTerm (n : nat) : Term :=
  match n with
  | O => Zero
  | S m => Succ (natToTerm m)
  end.

Lemma closedNatToTerm :
 forall a v : nat, ~ In v (freeVarTerm LNT (natToTerm a)).
Proof.
intros.
induction a as [| a Hreca].
auto.
simpl in |- *.
rewrite freeVarSucc.
auto.
Qed.
