Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import ListExt.

Require Import folProp.
Require Import folProof.
Require Export folLogic.
Require Import subProp.
Require Import folReplace.
Require Import Arith.

Section More_Logic_Rules.

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

Lemma rebindForall :
 forall (T : System) (a b : nat) (f : Formula),
 ~ In b (freeVarFormula L (forallH a f)) ->
 SysPrf T (iffH (forallH a f) (forallH b (substituteFormula L f a (var b)))).
Proof.
intros.
eapply (sysExtend L) with (Empty_set Formula).
unfold Included in |- *.
intros.
induction H0.
apply (iffI L).
apply (impI L).
apply (forallI L).
unfold not in |- *; intros.
induction H0 as (x, H0); induction H0 as (H0, H1).
induction H1 as [x H1| x H1]; [ induction H1 | induction H1 ].
auto.
apply forallE.
apply Axm; right; constructor.
apply (impI L).
apply (forallI L).
unfold not in |- *; intros.
induction H0 as (x, H0); induction H0 as (H0, H1).
induction H1 as [x H1| x H1]; [ induction H1 | induction H1 ].
assert (In a (freeVarFormula L (substituteFormula L f a (var b)))).
eapply In_list_remove1.
apply H0.
induction (freeVarSubFormula3 _ _ _ _ _ H1).
elim (In_list_remove2 _ _ _ _ _ H2).
auto.
elim (In_list_remove2 _ _ _ _ _ H0).
induction H2 as [H2| H2].
auto.
elim H2.
set (A1 := forallH b (substituteFormula L f a (var b))) in *.
rewrite <- (subFormulaId L f a).
apply
 (impE L)
  with
    (substituteFormula L (substituteFormula L f a (var b)) b (fol.var L a)).
apply (iffE1 L).
apply (subFormulaTrans L).
apply H.
apply forallE.
apply Axm; right; constructor.
Qed.

Lemma rebindExist :
 forall (T : System) (a b : nat) (f : Formula),
 ~ In b (freeVarFormula L (existH a f)) ->
 SysPrf T (iffH (existH a f) (existH b (substituteFormula L f a (var b)))).
Proof.
intros.
unfold existH in |- *.
unfold fol.existH in |- *.
apply (reduceNot L).
eapply (iffTrans L).
apply (rebindForall T a b (notH f)).
apply H.
rewrite (subFormulaNot L).
apply (iffRefl L).
Qed.

Lemma subSubTerm :
 forall (t : Term) (v1 v2 : nat) (s1 s2 : Term),
 v1 <> v2 ->
 ~ In v1 (freeVarTerm L s2) ->
 substituteTerm L (substituteTerm L t v1 s1) v2 s2 =
 substituteTerm L (substituteTerm L t v2 s2) v1 (substituteTerm L s1 v2 s2).
Proof.
intros.
elim t using
 Term_Terms_ind
  with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
           substituteTerms L n (substituteTerms L n ts v1 s1) v2 s2 =
           substituteTerms L n (substituteTerms L n ts v2 s2) v1
             (substituteTerm L s1 v2 s2)); simpl in |- *; 
 intros.
induction (eq_nat_dec v1 n).
induction (eq_nat_dec v2 n).
elim H.
transitivity n; auto.
simpl in |- *.
induction (eq_nat_dec v1 n).
reflexivity.
elim b0.
auto.
simpl in |- *.
induction (eq_nat_dec v2 n).
rewrite subTermNil.
reflexivity.
auto.
simpl in |- *.
induction (eq_nat_dec v1 n).
elim b; auto.
reflexivity.
rewrite H1.
reflexivity.
reflexivity.
rewrite H1.
rewrite H2.
reflexivity.
Qed.

Lemma subSubTerms :
 forall (n : nat) (ts : Terms n) (v1 v2 : nat) (s1 s2 : Term),
 v1 <> v2 ->
 ~ In v1 (freeVarTerm L s2) ->
 substituteTerms L n (substituteTerms L n ts v1 s1) v2 s2 =
 substituteTerms L n (substituteTerms L n ts v2 s2) v1
   (substituteTerm L s1 v2 s2).
Proof.
intros.
induction ts as [| n t ts Hrects].
reflexivity.
simpl in |- *.
rewrite Hrects.
rewrite subSubTerm.
reflexivity.
auto.
auto.
Qed.

Lemma subSubFormula :
 forall (f : Formula) (v1 v2 : nat) (s1 s2 : Term),
 v1 <> v2 ->
 ~ In v1 (freeVarTerm L s2) ->
 forall T : System,
 SysPrf T
   (iffH (substituteFormula L (substituteFormula L f v1 s1) v2 s2)
      (substituteFormula L (substituteFormula L f v2 s2) v1
         (substituteTerm L s1 v2 s2))).
Proof.
intros.
apply (sysExtend L) with (Empty_set Formula).
unfold Included in |- *.
intros.
induction H1.
elim f using Formula_depth_ind2; intros.
repeat rewrite (subFormulaEqual L).
rewrite subSubTerm; auto.
rewrite (subSubTerm t0); auto.
apply (iffRefl L).
repeat rewrite (subFormulaRelation L).
rewrite subSubTerms; auto.
apply (iffRefl L).
repeat rewrite (subFormulaImp L).
apply (reduceImp L); auto.
repeat rewrite (subFormulaNot L).
apply (reduceNot L); auto.
set
 (v' :=
  newVar
    (v1
     :: v2
        :: freeVarFormula L (fol.forallH L v a) ++
           freeVarTerm L s1 ++ freeVarTerm L s2)) in *.
assert (v' <> v1).
unfold not in |- *; intros.
elim
 (newVar1
    (v1
     :: v2
        :: freeVarFormula L (fol.forallH L v a) ++
           freeVarTerm L s1 ++ freeVarTerm L s2)).
fold v' in |- *.
simpl in |- *.
auto.
assert (v' <> v2).
unfold not in |- *; intros.
elim
 (newVar1
    (v1
     :: v2
        :: freeVarFormula L (fol.forallH L v a) ++
           freeVarTerm L s1 ++ freeVarTerm L s2)).
fold v' in |- *.
simpl in |- *.
auto.
assert (~ In v' (freeVarFormula L (fol.forallH L v a))).
unfold not in |- *; intros.
elim
 (newVar1
    (v1
     :: v2
        :: freeVarFormula L (fol.forallH L v a) ++
           freeVarTerm L s1 ++ freeVarTerm L s2)).
fold v' in |- *.
simpl in |- *.
auto with datatypes.
assert (~ In v' (freeVarTerm L s1)).
unfold not in |- *; intros.
elim
 (newVar1
    (v1
     :: v2
        :: freeVarFormula L (fol.forallH L v a) ++
           freeVarTerm L s1 ++ freeVarTerm L s2)).
fold v' in |- *.
simpl in |- *.
repeat right.
auto with datatypes.
assert (~ In v' (freeVarTerm L s2)).
unfold not in |- *; intros.
elim
 (newVar1
    (v1
     :: v2
        :: freeVarFormula L (fol.forallH L v a) ++
           freeVarTerm L s1 ++ freeVarTerm L s2)).
fold v' in |- *.
simpl in |- *.
repeat right.
auto with datatypes.
apply
 impE
  with
    (iffH
       (substituteFormula L
          (substituteFormula L
             (fol.forallH L v' (substituteFormula L a v (var v'))) v1 s1) v2
          s2)
       (substituteFormula L
          (substituteFormula L
             (fol.forallH L v' (substituteFormula L a v (var v'))) v2 s2) v1
          (substituteTerm L s1 v2 s2))).
apply (iffE2 L).
assert
 (folProof.SysPrf L (Empty_set Formula)
    (iffH (fol.forallH L v a)
       (fol.forallH L v' (substituteFormula L a v (var v'))))).
apply rebindForall.
auto.
repeat first
 [ apply (reduceIff L)
 | apply (reduceSub L)
 | apply (notInFreeVarSys L) ]; auto.
assert
 (forall (f : Formula) (x v : nat) (s : Term),
  x <> v ->
  ~ In x (freeVarTerm L s) ->
  substituteFormula L (forallH x f) v s =
  forallH x (substituteFormula L f v s)). 
intros.
rewrite (subFormulaForall L).
induction (eq_nat_dec x v0).
elim H7; auto.
induction (In_dec eq_nat_dec x (freeVarTerm L s)).
elim H8; auto.
reflexivity.
repeat rewrite H7; auto.
apply (reduceForall L).
apply (notInFreeVarSys L).
apply H1.
apply eqDepth with a.
symmetry  in |- *.
apply subFormulaDepth.
apply depthForall.
unfold not in |- *; intros.
induction (freeVarSubTerm3 _ _ _ _ _ H8).
elim H5.
eapply In_list_remove1.
apply H9.
auto.
Qed.

End More_Logic_Rules.

