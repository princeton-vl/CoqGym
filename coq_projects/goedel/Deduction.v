Require Import Ensembles.
Require Import Coq.Lists.List.

Require Import folProof.
Require Import folProp.

Section Deduction_Theorem.

Variable L : Language.
Let Formula := Formula L.
Let Formulas := Formulas L.
Let System := System L.
Let Term := Term L.
Let Terms := Terms L.
Let var := var L.
Let impH := impH L.
Let notH := notH L.
Let forallH := forallH L.
Let Prf := Prf L.
Let SysPrf := SysPrf L.

Theorem DeductionTheorem :
 forall (T : System) (f g : Formula) (prf : SysPrf (Ensembles.Add _ T g) f),
 SysPrf T (impH g f).
Proof.
intros T.
assert
 (EasyCase :
  forall (g z : Formula),
  Prf nil z -> SysPrf (fun x : fol.Formula L => In x nil /\ mem (fol.Formula L) T x)
  (impH g z)).
intros.
set (A1 := IMP1 L z g) in *.
set (A2 := MP L _ _ _ _ A1 H) in *.
exists (nil:list Formula).
exists A2.
intros.
elim H0.
intros f g [F [H HF]].
assert (SysPrf (fun x => In x F /\ mem _ T x) (impH g f)).
induction  H
 as
  [A|
   Axm1
   Axm2
   A
   B
   H1
   HrecH1
   H0
   HrecH0|
   Axm
   A
   v
   n
   H
   HrecH|
   A
   B|
   A
   B
   C|
   A
   B|
   A
   v
   t|
   A
   v
   n|
   A
   B
   v|
   |
   |
   |
   R|
   f].
pose (HF _ (or_introl _ (refl_equal A))).
clearbody m.
destruct m.
set (A1 := AXM L x) in *.
set (A2 := IMP1 L x g) in *.
set (A3 := MP L _ _ _ _ A2 A1) in *.
exists (x :: nil).
exists A3.
intros.
split.
auto.
destruct H0.
destruct H0.
assumption.
contradiction.
destruct H.
set (A1 := IMP2 L g (impH g g) g) in *.
set (A2 := IMP1 L g (impH g g)) in *.
set (A3 := MP L _ _ _ _ A1 A2) in *.
set (A4 := IMP1 L g g) in *.
set (A5 := MP L _ _ _ _ A3 A4) in *.
exists (nil:list Formula).
exists A5.
contradiction.
induction  HrecH0 as (x, H).
induction  H as (x0, H).
induction  HrecH1 as (x1, H2).
induction  H2 as (x2, H2).
set (A1 := IMP2 L g A B) in *.
set (A2 := MP L _ _ _ _ A1 x2) in *.
set (A3 := MP L _ _ _ _ A2 x0) in *.
exists (x1 ++ x).
exists A3.
simpl in |- *.
clear - H H2.
intros.
split.
change (In g (Axm1++Axm2)).
apply in_or_app.
destruct (in_app_or _ _ _ H0); firstorder.
destruct (in_app_or _ _ _ H0); firstorder.
firstorder.
firstorder.
induction  HrecH as (x, H0).
induction  H0 as (x0, H0).
assert (In g Axm \/ (forall x, In x Axm -> mem _ T x)).
clear - HF.
induction Axm.
firstorder.
elim (HF a (or_introl _ (refl_equal a))).
assert (forall g0 : fol.Formula L,
         In g0 Axm -> mem (fol.Formula L) (Ensembles.Add (fol.Formula L) T g) g0) .
firstorder.
destruct (IHAxm H).
firstorder.
intros.
right.
intros x0 [H2|H2].
elim H2; assumption.
apply H0; assumption.
intros x H.
elim H.
firstorder.
destruct H1 as [a|b].
assert (~ In v (freeVarListFormula L x)).
clear x0 H.
induction  x as [| a0 x Hrecx].
auto.
unfold not in |- *; intro.
simpl in H.
induction (in_app_or _ _ _ H).
elim n.
eapply In_freeVarListFormula.
apply H1.
firstorder.
elim Hrecx.
intros.
apply H0.
firstorder.
assumption.
assert (~ In v (freeVarFormula L g)).
unfold not in |- *; intros; elim n.
eapply In_freeVarListFormula.
apply H2.
assumption.
set (A1 := GEN L _ _ _ H1 x0) in *.
set (A2 := FA3 L g A v) in *.
set (A3 := MP L _ _ _ _ A2 A1) in *.
set (A4 := FA2 L g v H2) in *.
set (A5 := IMP2 L g (forallH v g) (forallH v A)) in *.
set (A6 := IMP1 L (impH (forallH v g) (forallH v A)) g) in *.
set (A7 := MP L _ _ _ _ A6 A3) in *.
set (A8 := MP L _ _ _ _ A5 A7) in *.
set (A9 := MP L _ _ _ _ A8 A4) in *.
exists (x ++ nil).
exists A9.
clear A9 A8 A7 A6 A5 A4 A3 A2 A1.
simpl in |- *.
intros.
apply H0.
induction (in_app_or _ _ _ H3).
auto.
elim H4.
set (A1 := GEN L _ _ _ n H) in *.
set (A2 := IMP1 L (forallH v A) g) in *.
set (A3 := MP L _ _ _ _ A2 A1) in *.
exists (Axm).
exists A3.
firstorder.
firstorder.
apply EasyCase.
apply (IMP1 L).
apply EasyCase.
apply (IMP2 L).
apply EasyCase.
apply (CP L).
apply EasyCase.
apply (FA1 L).
apply EasyCase.
apply (FA2 L); assumption.
apply EasyCase.
apply (FA3 L).
apply EasyCase.
apply (EQ1 L).
apply EasyCase.
apply (EQ2 L).
apply EasyCase.
apply (EQ3 L).
apply EasyCase.
apply (EQ4 L).
apply EasyCase.
apply (EQ5 L).
induction  H0 as (x, H0).
induction  H0 as (x0, H0).
exists x.
exists x0.
firstorder.
Qed.

End Deduction_Theorem.
