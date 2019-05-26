Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import folProp.
Require Import folProof.
Require Import folReplace.
Require Import folLogic3.
Require Import subProp.
Require Import ListExt.
Require Import NNtheory.
Require Import NN2PA.
Require Import fixPoint.
Require Import codeSysPrf.
Require Import PAtheory.
Require Import code.
Require Import PRrepresentable.
Require Import expressible.
Require Import checkPrf.
Require Import codeNatToTerm.

Section Rosser's_Incompleteness.

Definition codeFormula := codeFormula LNT codeLNTFunction codeLNTRelation.

Variable T : System.
Definition T' : fol.System LNN :=
  Union _ NN
    (fun x : fol.Formula LNN => mem _ T (LNN2LNT_formula x)).

Lemma extendsNN : Included _ NN T'.
Proof.
unfold Included in |- *.
intros.
unfold T' in |- *.
left.
assumption.
Qed.

Hypothesis extendsPA : Included _ PA T.

Variable repT : Formula.
Variable v0 : nat.
Hypothesis
  freeVarRepT : forall v : nat, In v (freeVarFormula LNT repT) -> v = v0.
Hypothesis
  expressT1 :
    forall f : Formula,
    mem _ T f ->
    SysPrf T (substituteFormula LNT repT v0 (natToTerm (codeFormula f))).
Hypothesis
  expressT2 :
    forall f : Formula,
    ~ mem _ T f ->
    SysPrf T
      (notH (substituteFormula LNT repT v0 (natToTerm (codeFormula f)))).

Lemma freeVarRepT' :
 forall v : nat, In v (freeVarFormula LNN (LNT2LNN_formula repT)) -> v = v0.
Proof.
intros.
apply freeVarRepT.
rewrite <- (LNT2LNT_formula repT).
apply LNN2LNT_freeVarFormula2.
assumption.
Qed.

Lemma Tprf2T'prf :
 forall f : Formula, SysPrf T f -> folProof.SysPrf LNN T' (LNT2LNN_formula f).
Proof.
intros.
unfold T' in |- *.
apply
 (folLogic.sysExtend LNN)
  with
    (fun x : fol.Formula LNN =>
     mem (fol.Formula LNT) T (LNN2LNT_formula x)).
unfold Included in |- *.
intros.
right.
assumption.
induction H as (x, H); induction H as (x0, H).
exists (map LNT2LNN_formula x).
induction x0
 as
  [A|
   Axm1 Axm2 A B x0_1 Hrecx0_1 x0_0 Hrecx0_0|
   Axm A v n x0 Hrecx0|
   A B|
   A B C|
   A B|
   A v t|
   A v n|
   A B v|
   |
   |
   |
   R|
   f]; simpl in |- *.
exists (AXM LNN (LNT2LNN_formula A)).
intros.
unfold mem in |- *.
unfold Ensembles.In in |- *.
induction H0 as [H0| H0].
rewrite <- H0.
rewrite LNT2LNT_formula.
apply H.
auto with datatypes.
induction H0.
assert
 (forall g : fol.Formula LNT, In g Axm1 -> mem (fol.Formula LNT) T g).
auto with datatypes.
assert
 (forall g : fol.Formula LNT, In g Axm2 -> mem (fol.Formula LNT) T g).
auto with datatypes.
induction (Hrecx0_0 H1).
induction (Hrecx0_1 H0).
clear Hrecx0_0 Hrecx0_1 H0 H1.
assert
 (map LNT2LNN_formula (Axm1 ++ Axm2) =
  map LNT2LNN_formula Axm1 ++ map LNT2LNN_formula Axm2).
generalize Axm1 Axm2; intros.
induction Axm0 as [| a Axm0 HrecAxm0]; simpl in |- *.
reflexivity.
rewrite HrecAxm0.
reflexivity.
rewrite H0.
exists
 (MP LNN (map LNT2LNN_formula Axm1) (map LNT2LNN_formula Axm2)
    (LNT2LNN_formula A) (LNT2LNN_formula B) x0 x).
intros.
induction (in_app_or _ _ _ H1); auto.
induction (Hrecx0 H).
assert (~ In v (freeVarListFormula LNN (map LNT2LNN_formula Axm))).
clear x0 H Hrecx0 x H0.
unfold not in |- *; intros; apply n.
clear n.
induction Axm as [| a Axm HrecAxm].
auto.
simpl in |- *.
simpl in H.
apply in_or_app.
induction (in_app_or _ _ _ H).
left.
rewrite <- (LNT2LNT_formula a).
apply LNN2LNT_freeVarFormula2.
assumption.
auto.
exists (GEN LNN (map LNT2LNN_formula Axm) (LNT2LNN_formula A) v H1 x).
auto.
exists (IMP1 LNN (LNT2LNN_formula A) (LNT2LNN_formula B)).
tauto.
exists (IMP2 LNN (LNT2LNN_formula A) (LNT2LNN_formula B) (LNT2LNN_formula C)).
tauto.
exists (CP LNN (LNT2LNN_formula A) (LNT2LNN_formula B)).
tauto.
rewrite LNT2LNN_subFormula.
exists (FA1 LNN (LNT2LNN_formula A) v (LNT2LNN_term t)).
tauto.
rewrite <- LNT2LNN_freeVarFormula in n.
exists (FA2 LNN (LNT2LNN_formula A) v n).
tauto.
exists (FA3 LNN (LNT2LNN_formula A) (LNT2LNN_formula B) v).
tauto.
exists (EQ1 LNN).
tauto.
exists (EQ2 LNN).
tauto.
exists (EQ3 LNN).
tauto.
induction R.
induction f; simpl in |- *.
exists (EQ5 LNN Languages.Plus).
tauto.
exists (EQ5 LNN Languages.Times).
tauto.
exists (EQ5 LNN Languages.Succ).
tauto.
exists (EQ5 LNN Languages.Zero).
tauto.
Qed.

Lemma expressT'1 :
 forall f : Formula,
 mem _ T f ->
 folProof.SysPrf LNN T'
   (substituteFormula LNN (LNT2LNN_formula repT) v0
      (natToTermLNN (codeFormula f))).
Proof.
intros.
rewrite <- (LNT2LNN_natToTerm (codeFormula f)).
rewrite <- LNT2LNN_subFormula.
apply Tprf2T'prf.
apply expressT1.
assumption.
Qed.

Lemma expressT'2 :
 forall f : Formula,
 ~ mem _ T f ->
 folProof.SysPrf LNN T'
   (fol.notH LNN
      (substituteFormula LNN (LNT2LNN_formula repT) v0
         (natToTermLNN (codeFormula f)))).
Proof.
intros.
rewrite <- (LNT2LNN_natToTerm (codeFormula f)).
rewrite <- LNT2LNN_subFormula.
replace
 (fol.notH LNN
    (LNT2LNN_formula
       (substituteFormula LNT repT v0 (natToTerm (codeFormula f))))) with
 (LNT2LNN_formula
    (notH (substituteFormula LNT repT v0 (natToTerm (codeFormula f))))).
apply Tprf2T'prf.
apply expressT2.
assumption.
reflexivity.
Qed.

Definition codeSysPrf :=
  codeSysPrf LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR
    codeArityLNTFIsPR codeArityLNTRIsPR (LNT2LNN_formula repT) v0.

Definition codeSysPrfCorrect1 :=
  codeSysPrfCorrect1 LNT codeLNTFunction codeLNTRelation codeArityLNTF
    codeArityLNTR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNTRIsPR
    codeArityLNTRIsCorrect1 T' extendsNN T (LNT2LNN_formula repT) v0
    freeVarRepT' expressT'1.

Definition codeSysPrfCorrect2 :=
  codeSysPrfCorrect2 LNT codeLNTFunction codeLNTRelation codeArityLNTF
    codeArityLNTR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNTRIsPR
    codeArityLNTRIsCorrect1 T' extendsNN T (LNT2LNN_formula repT) v0
    freeVarRepT' expressT'2.

Definition codeSysPrfCorrect3 :=
  codeSysPrfCorrect3 LNT codeLNTFunction codeLNTRelation codeArityLNTF
    codeArityLNTR codeArityLNTFIsPR codeArityLNTFIsCorrect1
    codeArityLNTFIsCorrect2 codeArityLNTRIsPR codeArityLNTRIsCorrect1
    codeArityLNTRIsCorrect2 codeLNTFunctionInj codeLNTRelationInj T'
    extendsNN.
  
Definition codePrf := codePrf LNT codeLNTFunction codeLNTRelation.

Definition codeSysPrfNot :=
  codeSysPrfNot LNT codeLNTFunction codeLNTRelation codeArityLNTF
    codeArityLNTR codeArityLNTFIsPR codeArityLNTRIsPR 
    (LNT2LNN_formula repT) v0.

Definition freeVarCodeSysPrfN :=
  freeVarCodeSysPrfN LNT codeLNTFunction codeLNTRelation codeArityLNTF
    codeArityLNTR codeArityLNTFIsPR codeArityLNTRIsPR 
    (LNT2LNN_formula repT) v0 freeVarRepT'.

Definition codeSysPrfNCorrect1 :=
  codeSysPrfNCorrect1 LNT codeLNTFunction codeLNTRelation codeArityLNTF
    codeArityLNTR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNTRIsPR
    codeArityLNTRIsCorrect1 T' extendsNN T (LNT2LNN_formula repT) v0
    freeVarRepT' expressT'1.

Definition codeSysPrfNCorrect2 :=
  codeSysPrfNCorrect2 LNT codeLNTFunction codeLNTRelation codeArityLNTF
    codeArityLNTR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNTRIsPR
    codeArityLNTRIsCorrect1 T' extendsNN T (LNT2LNN_formula repT) v0
    freeVarRepT' expressT'2.

Definition codeSysPrfNCorrect3 :=
  codeSysPrfNCorrect3 LNT codeLNTFunction codeLNTRelation codeArityLNTF
    codeArityLNTR codeArityLNTFIsPR codeArityLNTFIsCorrect1
    codeArityLNTFIsCorrect2 codeArityLNTRIsPR codeArityLNTRIsCorrect1
    codeArityLNTRIsCorrect2 codeLNTFunctionInj codeLNTRelationInj T'
    extendsNN (LNT2LNN_formula repT) v0 freeVarRepT'.

Lemma decideAxioms :
 (forall x : Formula, mem _ T x \/ ~ mem _ T x) ->
 forall x : Formulas,
 (forall g : Formula, In g x -> mem _ T g) \/
 (exists g : Formula, In g x /\ ~ mem _ T g).
Proof.
intros.
induction x as [| a x Hrecx].
left.
intros.
elim H0.
induction Hrecx as [H0| H0].
induction (H a).
left.
intros.
induction H2 as [H2| H2].
rewrite <- H2.
assumption.
auto.
right.
exists a.
split.
auto with datatypes.
assumption.
right.
induction H0 as (x0, H0).
exists x0.
induction H0 as (H0, H1).
auto with datatypes.
Qed.

Lemma searchProof :
 (forall x : Formula, mem _ T x \/ ~ mem _ T x) ->
 forall (a b : Formula) (A : Formulas) (p : Prf LNT A a),
 (exists B : Formulas,
    (exists q : Prf LNT B b,
       codePrf _ _ q < S (codePrf _ _ p) /\
       (forall x : Formula, In x B -> mem _ T x))) \/
 (forall (B : Formulas) (q : Prf LNT B b),
  codePrf _ _ q < S (codePrf _ _ p) ->
  exists g : Formula, In g B /\ ~ mem _ T g).
Proof.
intros.
induction (S (codePrf A a p)).
right.
intros.
elim (lt_n_O _ H0).
induction IHn as [H0| H0].
left.
decompose record H0.
exists x.
exists x0.
auto.
induction
 (eq_nat_dec
    (checkPrf LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR
       (codeFormula b) n) 0).
right.
intros.
induction (le_lt_or_eq _ _ (lt_n_Sm_le _ _ H1)).
eauto.
rewrite <- H2 in a0.
rewrite
 (checkPrfCorrect1 LNT codeLNTFunction codeLNTRelation codeArityLNTF
    codeArityLNTR codeArityLNTFIsCorrect1 codeArityLNTRIsCorrect1)
  in a0.
discriminate a0.
decompose record
 (checkPrfCorrect2 LNT codeLNTFunction codeLNTRelation codeArityLNTF
    codeArityLNTR codeArityLNTFIsCorrect1 codeArityLNTFIsCorrect2
    codeArityLNTRIsCorrect1 codeArityLNTRIsCorrect2 codeLNTFunctionInj
    codeLNTRelationInj _ _ b0).
assert (x = b).
eapply codeFormulaInj.
apply codeLNTFunctionInj.
apply codeLNTRelationInj.
assumption.
rewrite <- H1.
induction (decideAxioms H x0).
left.
exists x0.
exists x1.
unfold codePrf in |- *.
rewrite H3.
auto.
right.
intros.
induction (le_lt_or_eq _ _ (lt_n_Sm_le _ _ H5)).
rewrite <- H1 in H0.
eauto.
assert (B = x0).
eapply (codePrfInjAxm LNT) with (p := q) (q := x1).
apply codeLNTFunctionInj.
apply codeLNTRelationInj.
transitivity n.
unfold codePrf in H6.
apply H6.
symmetry  in |- *.
apply H3.
rewrite H7.
assumption.
Qed.

Lemma T'prf2Tprf :
 forall f : fol.Formula LNN,
 folProof.SysPrf LNN T' f -> SysPrf T (LNN2LNT_formula f).
Proof.
assert
 (freeVarPA :
  forall x : Formulas,
  (forall g : fol.Formula LNT, In g x -> mem (fol.Formula LNT) PA g) ->
  forall v : nat, In v (freeVarListFormula LNT x) -> False).
intros.
induction x as [| a x Hrecx].
apply H0.
simpl in H0.
induction (in_app_or _ _ _ H0).
apply (closedPA v).
exists a.
auto with datatypes.
auto with datatypes.
intros.
induction H as (x, H); induction H as (x0, H).
unfold SysPrf, folProof.SysPrf in |- *.
assert
 (exists Axm : fol.Formulas LNT,
    (forall v : nat,
     In v (freeVarListFormula _ Axm) -> In v (freeVarListFormula _ x)) /\
    ex
      (fun _ : Prf LNT Axm (LNN2LNT_formula f) =>
       forall g : fol.Formula LNT,
       In g Axm -> mem (fol.Formula LNT) T g)).
induction x0
 as
  [A|
   Axm1 Axm2 A B x0_1 Hrecx0_1 x0_0 Hrecx0_0|
   Axm A v n x0 Hrecx0|
   A B|
   A B C|
   A B|
   A v t|
   A v n|
   A B v|
   |
   |
   |
   R|
   f]; simpl in |- *.
assert (mem (fol.Formula LNN) T' A).
auto with datatypes.
repeat induction H0.
exists (PA1 :: nil).
split.
auto.
exists (AXM _ PA1).
intros.
apply extendsPA.
induction H0 as [H0| H0].
rewrite <- H0.
repeat (right; constructor) || left.
elim H0.
exists (PA2 :: nil).
split.
auto.
exists (AXM _ PA2).
intros.
apply extendsPA.
induction H0 as [H0| H0].
rewrite <- H0.
repeat (right; constructor) || left.
elim H0.
exists (PA3 :: nil).
split.
auto.
exists (AXM _ PA3).
intros.
apply extendsPA.
induction H0 as [H0| H0].
rewrite <- H0.
repeat (right; constructor) || left.
elim H0.
exists (PA4 :: nil).
split.
auto.
exists (AXM _ PA4).
intros.
apply extendsPA.
induction H0 as [H0| H0].
rewrite <- H0.
repeat (right; constructor) || left.
elim H0.
exists (PA5 :: nil).
split.
auto.
exists (AXM _ PA5).
intros.
apply extendsPA.
induction H0 as [H0| H0].
rewrite <- H0.
repeat (right; constructor) || left.
elim H0.
exists (PA6 :: nil).
split.
auto.
exists (AXM _ PA6).
intros.
apply extendsPA.
induction H0 as [H0| H0].
rewrite <- H0.
repeat (right; constructor) || left.
elim H0.
assert (SysPrf PA (LNN2LNT_formula NN7)).
apply NN72PA.
induction H0 as (x, H0); induction H0 as (x0, H0).
exists x.
split.
intros.
apply (freeVarPA x H0 v H1).
exists x0.
intros.
apply extendsPA.
fold mem.
auto.
assert (SysPrf PA (LNN2LNT_formula NN8)).
apply NN82PA.
induction H0 as (x, H0); induction H0 as (x0, H0).
exists x.
split.
intros.
apply (freeVarPA x H0 v H1).
exists x0.
intros.
apply extendsPA.
fold mem.
auto.
assert (SysPrf PA (LNN2LNT_formula NN9)).
apply NN92PA.
induction H0 as (x, H0); induction H0 as (x0, H0).
exists x.
split.
intros.
apply (freeVarPA x H0 v H1).
exists x0.
intros.
apply extendsPA.
fold mem.
auto.
exists (LNN2LNT_formula x :: nil).
split.
simpl in |- *.
repeat rewrite <- app_nil_end.
apply (LNN2LNT_freeVarFormula1 x).
exists (AXM _ (LNN2LNT_formula x)).
intros.
induction H1 as [H1| H1].
unfold mem in H0.
unfold Ensembles.In in H0.
rewrite H1 in H0.
apply H0.
elim H1.
assert
 (forall g : fol.Formula LNN,
  In g Axm1 -> mem (fol.Formula LNN) T' g).
auto with datatypes.
assert
 (forall g : fol.Formula LNN,
  In g Axm2 -> mem (fol.Formula LNN) T' g).
auto with datatypes.
induction (Hrecx0_1 H0).
induction (Hrecx0_0 H1).
induction H2 as (H2, H4).
induction H3 as (H3, H5).
induction H4 as (x1, H4).
induction H5 as (x2, H5).
clear Hrecx0_1 H0 Hrecx0_0 H1.
exists (x ++ x0).
split.
repeat rewrite freeVarListFormulaApp.
intros.
induction (in_app_or _ _ _ H0); auto with datatypes.
simpl in x1.
exists (MP _ _ _ _ _ x1 x2).
intros.
induction (in_app_or _ _ _ H0); auto.
assert
 (forall g : fol.Formula LNN, In g Axm -> mem (fol.Formula LNN) T' g).
auto.
induction (Hrecx0 H0).
clear Hrecx0 H0.
induction H1 as (H0, H1).
induction H1 as (x1, H1).
exists x.
split.
assumption.
assert (~ In v (freeVarListFormula LNT x)).
auto.
exists (GEN _ _ _ _ H2 x1).
assumption.
exists (nil (A:=Formula)).
split.
auto.
exists (IMP1 _ (LNN2LNT_formula A) (LNN2LNT_formula B)).
simpl in |- *; tauto.
exists (nil (A:=Formula)).
split.
auto.
exists (IMP2 _ (LNN2LNT_formula A) (LNN2LNT_formula B) (LNN2LNT_formula C)).
simpl in |- *; tauto.
exists (nil (A:=Formula)).
split.
auto.
exists (CP _ (LNN2LNT_formula A) (LNN2LNT_formula B)).
simpl in |- *; tauto.
exists (nil (A:=Formula)).
split.
auto.
assert
 (SysPrf (Empty_set _)
    (impH (forallH v (LNN2LNT_formula A))
       (LNN2LNT_formula (substituteFormula LNN A v t)))).
apply
 impTrans with (substituteFormula LNT (LNN2LNT_formula A) v (LNN2LNT_term t)).
apply impI.
apply forallE.
apply Axm; right; constructor.
apply iffE2.
apply LNN2LNT_subFormula.
induction H0 as (x, H0).
induction H0 as (x0, H0).
induction x as [| a x Hrecx].
exists x0.
simpl in |- *; tauto.
assert (mem (fol.Formula LNT) (Empty_set (fol.Formula LNT)) a).
auto with datatypes.
induction H1.
exists (nil (A:=Formula)).
split.
auto.
assert (~ In v (freeVarFormula LNT (LNN2LNT_formula A))).
unfold not in |- *; intros; apply n.
apply LNN2LNT_freeVarFormula1.
assumption.
exists (FA2 _ (LNN2LNT_formula A) v H0).
simpl in |- *; tauto.
exists (nil (A:=Formula)).
split.
auto.
exists (FA3 _ (LNN2LNT_formula A) (LNN2LNT_formula B) v).
simpl in |- *; tauto.
exists (nil (A:=Formula)).
split.
auto.
exists (EQ1 LNT).
simpl in |- *; tauto.
exists (nil (A:=Formula)).
split.
auto.
exists (EQ2 LNT).
simpl in |- *; tauto.
exists (nil (A:=Formula)).
split.
auto.
exists (EQ3 LNT).
simpl in |- *; tauto.
assert (SysPrf (Empty_set Formula) (LNN2LNT_formula (AxmEq4 LNN R))).
apply translateProof with (Empty_set (fol.Formula LNN)).
unfold ClosedSystem in |- *.
intros.
induction H0.
intros.
induction H0.
exists (nil (A:=fol.Formula LNN)).
exists (EQ4 LNN R).
simpl in |- *; tauto.
induction H0 as (x, H0).
induction H0 as (x0, H0).
exists x.
split.
intros.
induction (In_freeVarListFormulaE _ _ _ H1).
induction H2 as (H2, H3).
assert (mem (fol.Formula LNT) (Empty_set Formula) x1).
auto.
induction H4.
exists x0.
intros.
assert (mem (fol.Formula LNT) (Empty_set Formula) g).
auto.
induction H2.
assert (SysPrf (Empty_set Formula) (LNN2LNT_formula (AxmEq5 LNN f))).
apply translateProof with (Empty_set (fol.Formula LNN)).
unfold ClosedSystem in |- *.
intros.
induction H0.
intros.
induction H0.
exists (nil (A:=fol.Formula LNN)).
exists (EQ5 LNN f).
simpl in |- *; tauto.
induction H0 as (x, H0).
induction H0 as (x0, H0).
exists x.
split.
intros.
induction (In_freeVarListFormulaE _ _ _ H1).
induction H2 as (H2, H3).
assert (mem (fol.Formula LNT) (Empty_set Formula) x1).
auto.
induction H4.
exists x0.
intros.
assert (mem (fol.Formula LNT) (Empty_set Formula) g).
auto.
induction H2.
induction H0 as (x1, H0).
induction H0 as (H0, H1).
exists x1.
assumption.
Qed.

(*To prove the strong contructive result we need the decidability of T*)

Theorem Rosser'sIncompleteness :
 (forall x : Formula, mem _ T x \/ ~ mem _ T x) ->
 exists f : Formula,
   (forall v : nat, ~ In v (freeVarFormula LNT f)) /\
   (SysPrf T f \/ SysPrf T (notH f) -> Inconsistent LNT T).
Proof.
intros decide.
set
 (A :=
  fol.forallH LNN 1
    (fol.impH LNN codeSysPrf
       (fol.existH LNN 2
          (fol.andH LNN (LT (fol.var LNN 2) (fol.var LNN 1))
             (substituteFormula LNN codeSysPrfNot 1 (fol.var LNN 2)))))) 
 in *.
destruct (FixPointLNT (LNN2LNT_formula A) 0) as [x [H0 H1]].
exists x.
split.
unfold not in |- *; intros.
induction (H1 v).
assert
 (In v
    (list_remove nat eq_nat_dec 0 (freeVarFormula LNT (LNN2LNT_formula A)))).
apply H2.
assumption.
cut (In v (list_remove nat eq_nat_dec 0 (freeVarFormula LNN A))).
clear H4.
intros.
unfold A in H4.
SimplFreeVar.
assert (v <= 1).
apply
 (freeVarCodeSysPrf LNT codeLNTFunction codeLNTRelation codeArityLNTF
    codeArityLNTR codeArityLNTFIsPR codeArityLNTRIsPR 
    (LNT2LNN_formula repT) v0 freeVarRepT').
apply H5.
destruct v as [| n].
apply H6.
reflexivity.
destruct n.
apply H7.
reflexivity.
apply (le_not_lt (S (S n)) 1).
assumption.
apply lt_n_S.
apply lt_O_Sn.
assert (v <= 1).
apply freeVarCodeSysPrfN.
assumption.
destruct v as [| n].
apply H6.
reflexivity.
destruct n.
apply H7.
reflexivity.
apply (le_not_lt (S (S n)) 1).
assumption.
apply lt_n_S.
apply lt_O_Sn.
eapply In_list_remove3.
apply LNN2LNT_freeVarFormula1.
eapply In_list_remove1.
apply H4.
eapply In_list_remove2.
apply H4.
intros.
induction H as [H| H].
unfold Inconsistent in |- *.
intros.
elim H.
intros.
induction H2 as (x1, H2).
induction (searchProof decide _ (notH x) _ x1).
decompose record H3.
apply contradiction with x.
assumption.
exists x2.
exists x3.
assumption.
apply
 contradiction
  with
    (existH 2
       (andH
          (LNN2LNT_formula
             (LT (fol.var LNN 2) (natToTermLNN (codePrf _ _ x1))))
          (substituteFormula LNT
             (substituteFormula LNT (LNN2LNT_formula codeSysPrfNot) 0
                (natToTerm (codeFormula x))) 1 (var 2)))).
apply
 impE
  with
    (existH 2
       (andH
          (LNN2LNT_formula
             (LT (fol.var LNN 2) (natToTermLNN (codePrf x0 x x1))))
          (substituteFormula LNT
             (substituteFormula LNT
                (substituteFormula LNT (LNN2LNT_formula codeSysPrfNot) 0
                   (natToTerm (codeFormula x))) 1 (var 2)) 1
             (natToTerm (codePrf _ _ x1))))).
apply iffE1.
apply sysExtend with PA.
apply extendsPA.
apply (reduceExist LNT).
apply closedPA.
apply (reduceAnd LNT).
apply iffRefl.
apply (subFormulaNil LNT).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H4).
apply (In_list_remove2 _ _ _ _ _ H5).
reflexivity.
simpl in H5.
decompose sum H5.
discriminate H6.
replace (LT (fol.var LNN 2) (natToTermLNN (codePrf _ _ x1))) with
 (substituteFormula LNN (LT (fol.var LNN 2) (fol.var LNN 1)) 1
    (natToTermLNN (codePrf _ _ x1))).
apply
 impE
  with
    (existH 2
       (andH
          (substituteFormula LNT
             (LNN2LNT_formula (LT (fol.var LNN 2) (fol.var LNN 1))) 1
             (natToTerm (codePrf x0 x x1)))
          (substituteFormula LNT
             (substituteFormula LNT
                (substituteFormula LNT (LNN2LNT_formula codeSysPrfNot) 0
                   (natToTerm (codeFormula x))) 1 (var 2)) 1
             (natToTerm (codePrf x0 x x1))))).
apply iffE1.
apply sysExtend with PA.
apply extendsPA.
apply (reduceExist LNT).
apply closedPA.
apply (reduceAnd LNT).
apply iffSym.
rewrite <- LNN2LNT_natToTerm.
apply LNN2LNT_subFormula.
apply iffRefl.
rewrite <- (subFormulaAnd LNT).
apply
 impE
  with
    (existH 2
       (substituteFormula LNT
          (fol.andH LNT
             (LNN2LNT_formula (LT (fol.var LNN 2) (fol.var LNN 1)))
             (substituteFormula LNT
                (substituteFormula LNT (LNN2LNT_formula codeSysPrfNot) 1
                   (var 2)) 0 (natToTerm (codeFormula x)))) 1
          (natToTerm (codePrf x0 x x1)))).
apply iffE1.
apply sysExtend with PA.
apply extendsPA.
apply (reduceExist LNT).
apply closedPA.
apply (reduceSub LNT).
apply closedPA.
apply (reduceAnd LNT).
apply iffRefl.
apply (subFormulaExch LNT).
discriminate.
unfold not in |- *; intros.
simpl in H4.
decompose sum H4.
discriminate H5.
apply closedNatToTerm.
replace (LT (fol.var LNN 2) (fol.var LNN 1)) with
 (substituteFormula LNN (LT (fol.var LNN 2) (fol.var LNN 1)) 0
    (natToTermLNN (codeFormula x))).
apply
 impE
  with
    (existH 2
       (substituteFormula LNT
          (fol.andH LNT
             (substituteFormula LNT
                (LNN2LNT_formula (LT (fol.var LNN 2) (fol.var LNN 1))) 0
                (natToTerm (codeFormula x)))
             (substituteFormula LNT
                (LNN2LNT_formula
                   (substituteFormula LNN codeSysPrfNot 1 (fol.var LNN 2))) 0
                (natToTerm (codeFormula x)))) 1 (natToTerm (codePrf x0 x x1)))).
apply iffE1.
apply sysExtend with PA.
apply extendsPA.
apply (reduceExist LNT).
apply closedPA.
apply (reduceSub LNT).
apply closedPA.
apply (reduceAnd LNT).
apply iffSym.
rewrite <- LNN2LNT_natToTerm.
apply LNN2LNT_subFormula.
apply (reduceSub LNT).
apply closedPA.
replace (var 2) with (LNN2LNT_term (fol.var LNN 2)).
apply LNN2LNT_subFormula.
reflexivity.
rewrite <- (subFormulaAnd LNT).
replace
 (existH 2
    (substituteFormula LNT
       (substituteFormula LNT
          (fol.andH LNT
             (LNN2LNT_formula (LT (fol.var LNN 2) (fol.var LNN 1)))
             (LNN2LNT_formula
                (substituteFormula LNN codeSysPrfNot 1 (fol.var LNN 2)))) 0
          (natToTerm (codeFormula x))) 1 (natToTerm (codePrf x0 x x1)))) with
 (substituteFormula LNT
    (existH 2
       (substituteFormula LNT
          (fol.andH LNT
             (LNN2LNT_formula (LT (fol.var LNN 2) (fol.var LNN 1)))
             (LNN2LNT_formula
                (substituteFormula LNN codeSysPrfNot 1 (fol.var LNN 2)))) 0
          (natToTerm (codeFormula x)))) 1 (natToTerm (codePrf x0 x x1))).
replace
 (existH 2
    (substituteFormula LNT
       (fol.andH LNT (LNN2LNT_formula (LT (fol.var LNN 2) (fol.var LNN 1)))
          (LNN2LNT_formula
             (substituteFormula LNN codeSysPrfNot 1 (fol.var LNN 2)))) 0
       (natToTerm (codeFormula x)))) with
 (substituteFormula LNT
    (existH 2
       (fol.andH LNT (LNN2LNT_formula (LT (fol.var LNN 2) (fol.var LNN 1)))
          (LNN2LNT_formula
             (substituteFormula LNN codeSysPrfNot 1 (fol.var LNN 2))))) 0
    (natToTerm (codeFormula x))).
apply
 impE
  with
    (substituteFormula LNT
       (substituteFormula LNT (LNN2LNT_formula codeSysPrf) 0
          (natToTerm (codeFormula x))) 1 (natToTerm (codePrf _ _ x1))).
repeat rewrite <- (subFormulaImp LNT).
apply forallE.
replace
 (forallH 1
    (substituteFormula LNT
       (fol.impH LNT (LNN2LNT_formula codeSysPrf)
          (existH 2
             (fol.andH LNT
                (LNN2LNT_formula (LT (fol.var LNN 2) (fol.var LNN 1)))
                (LNN2LNT_formula
                   (substituteFormula LNN codeSysPrfNot 1 (fol.var LNN 2))))))
       0 (natToTerm (codeFormula x)))) with
 (substituteFormula LNT
    (forallH 1
       (fol.impH LNT (LNN2LNT_formula codeSysPrf)
          (existH 2
             (fol.andH LNT
                (LNN2LNT_formula (LT (fol.var LNN 2) (fol.var LNN 1)))
                (LNN2LNT_formula
                   (substituteFormula LNN codeSysPrfNot 1 (fol.var LNN 2)))))))
    0 (natToTerm (codeFormula x))).
apply impE with x.
apply iffE1.
apply sysExtend with PA.
apply extendsPA.
apply H0.
assumption.
rewrite (subFormulaForall LNT).
induction (eq_nat_dec 1 0).
discriminate a.
induction (In_dec eq_nat_dec 1 (freeVarTerm LNT (natToTerm (codeFormula x)))).
elim (closedNatToTerm _ _ a).
reflexivity.
apply
 impE
  with
    (LNN2LNT_formula
       (substituteFormula LNN
          (substituteFormula LNN codeSysPrf 0 (natToTermLNN (codeFormula x)))
          1 (natToTermLNN (codePrf x0 x x1)))).
apply iffE1.
apply sysExtend with PA.
apply extendsPA.
eapply iffTrans.
apply LNN2LNT_subFormula.
repeat rewrite <- LNN2LNT_natToTerm.
apply (reduceSub LNT).
apply closedPA.
apply LNN2LNT_subFormula.
apply T'prf2Tprf.
apply codeSysPrfCorrect1.
assumption.
rewrite (subFormulaExist LNT).
induction (eq_nat_dec 2 0).
discriminate a.
induction (In_dec eq_nat_dec 2 (freeVarTerm LNT (natToTerm (codeFormula x)))).
elim (closedNatToTerm _ _ a).
reflexivity.
rewrite (subFormulaExist LNT).
induction (eq_nat_dec 2 1).
discriminate a.
induction
 (In_dec eq_nat_dec 2 (freeVarTerm LNT (natToTerm (codePrf x0 x x1)))).
elim (closedNatToTerm _ _ a).
reflexivity.
unfold LT in |- *.
rewrite (subFormulaRelation LNN).
simpl in |- *.
reflexivity.
unfold LT in |- *.
rewrite (subFormulaRelation LNN).
simpl in |- *.
reflexivity.
apply nExist.
set
 (E :=
  LNN2LNT_formula
    (nat_rec (fun _ => fol.Formula LNN) (LNT2LNN_formula (equal Zero Zero))
       (fun (n : nat) rec =>
        fol.andH LNN
          (fol.notH LNN
             (substituteFormula LNN
                (substituteFormula LNN codeSysPrfNot 0
                   (natToTermLNN (codeFormula x))) 1 
                (natToTermLNN n))) rec) (codePrf x0 x x1))) 
 in *.
assert (forall x : nat, ~ In x (freeVarFormula LNT E)).
unfold E in |- *.
clear H3 E.
induction (codePrf x0 x x1).
simpl in |- *.
auto.
intros.
unfold nat_rec, nat_rect in |- *.
unfold not in |- *; intros.
set
 (Q :=
  (fix F (n : nat) : (fun _ : nat => fol.Formula LNN) n :=
     match n with
     | O => LNT2LNN_formula (equal Zero Zero)
     | S n0 =>
         (fun (n1 : nat) (rec : fol.Formula LNN) =>
          fol.andH LNN
            (fol.notH LNN
               (substituteFormula LNN
                  (substituteFormula LNN codeSysPrfNot 0
                     (natToTermLNN (codeFormula x))) 1 
                  (natToTermLNN n1))) rec) n0 (F n0)
     end) n) in *.
assert
 (In x2
    (freeVarFormula LNN
       (fol.andH LNN
          (fol.notH LNN
             (substituteFormula LNN
                (substituteFormula LNN codeSysPrfNot 0
                   (natToTermLNN (codeFormula x))) 1 
                (natToTermLNN n))) Q))).
apply LNN2LNT_freeVarFormula1.
assumption.
clear H3.
SimplFreeVar.
apply (le_not_lt x2 1).
apply freeVarCodeSysPrfN.
assumption.
destruct x2 as [| n0].
elim H6; reflexivity.
destruct n0.
elim H5; reflexivity.
apply lt_n_S.
apply lt_O_Sn.
rewrite <- LNT2LNN_natToTerm in H4.
rewrite LNT2LNN_freeVarTerm in H4.
apply (closedNatToTerm _ _ H4).
rewrite <- LNT2LNN_natToTerm in H4.
rewrite LNT2LNN_freeVarTerm in H4.
apply (closedNatToTerm _ _ H4).
apply (IHn x2).
apply LNN2LNT_freeVarFormula2.
assumption.
apply impE with E.
apply sysExtend with PA.
apply extendsPA.
apply impI.
apply forallI.
unfold not in |- *; intros.
induction H5 as (x2, H5).
induction H5 as (H5, H6).
induction H6 as [x2 H6| x2 H6].
apply (closedPA 2).
exists x2.
auto.
induction H6.
apply (H4 2).
assumption.
apply nAnd.
unfold orH, fol.orH in |- *.
apply
 impTrans
  with
    (LNN2LNT_formula (LT (fol.var LNN 2) (natToTermLNN (codePrf x0 x x1)))).
apply impI.
apply nnE.
apply Axm; right; constructor.
apply impI.
apply impE with E.
apply
 impE
  with
    (LNN2LNT_formula (LT (fol.var LNN 2) (natToTermLNN (codePrf x0 x x1)))).
do 2 apply sysWeaken.
apply PAboundedLT.
intros.
rewrite (subFormulaImp LNT).
rewrite (subFormulaNot LNT).
apply
 impE
  with
    (fol.impH LNT E
       (fol.notH LNT
          (substituteFormula LNT
             (substituteFormula LNT (LNN2LNT_formula codeSysPrfNot) 0
                (natToTerm (codeFormula x))) 1 (natToTerm n)))).
apply iffE2.
apply (reduceImp LNT).
apply (subFormulaNil LNT).
apply H4.
apply (reduceNot LNT).
apply (subFormulaTrans LNT).
unfold not in |- *; intros.
SimplFreeVar.
apply (le_not_lt 2 1).
apply freeVarCodeSysPrfN.
apply LNN2LNT_freeVarFormula1.
apply H7.
apply lt_n_Sn.
unfold E in |- *.
clear E H4 H3.
apply impI.
induction (codePrf x0 x x1).
elim (lt_n_O _ H5).
unfold nat_rec, nat_rect in |- *.
set
 (Q :=
  (fix F (n1 : nat) : (fun _ : nat => fol.Formula LNN) n1 :=
     match n1 with
     | O => LNT2LNN_formula (equal Zero Zero)
     | S n2 =>
         (fun (n3 : nat) (rec : fol.Formula LNN) =>
          fol.andH LNN
            (fol.notH LNN
               (substituteFormula LNN
                  (substituteFormula LNN codeSysPrfNot 0
                     (natToTermLNN (codeFormula x))) 1 
                  (natToTermLNN n3))) rec) n2 (F n2)
     end) n0) in *.
induction (le_lt_or_eq _ _ (lt_n_Sm_le _ _ H5)).
apply impE with (LNN2LNT_formula Q).
apply sysWeaken.
apply impI.
apply (IHn0 H3).
rewrite LNN2LNT_and. 
eapply andE2.
apply Axm; right; constructor.
rewrite H3.
apply
 impE
  with
    (LNN2LNT_formula
       (fol.notH LNN
          (substituteFormula LNN
             (substituteFormula LNN codeSysPrfNot 0
                (natToTermLNN (codeFormula x))) 1 (natToTermLNN n0)))).
apply sysWeaken.
apply iffE1.
apply
 iffTrans
  with
    (notH
       (LNN2LNT_formula
          (substituteFormula LNN
             (substituteFormula LNN codeSysPrfNot 0
                (natToTermLNN (codeFormula x))) 1 (natToTermLNN n0)))).
apply iffRefl.
apply (reduceNot LNT).
rewrite <- LNN2LNT_natToTerm.
rewrite <- LNN2LNT_natToTerm.
apply
 iffTrans
  with
    (substituteFormula LNT
       (LNN2LNT_formula
          (substituteFormula LNN codeSysPrfNot 0
             (natToTermLNN (codeFormula x)))) 1
       (LNN2LNT_term (natToTermLNN n0))).
apply LNN2LNT_subFormula.
apply (reduceSub LNT).
apply closedPA.
apply LNN2LNT_subFormula.
eapply andE1.
rewrite LNN2LNT_and. 
apply Axm; right; constructor.
apply Axm; right; constructor.
apply Axm; left; right; constructor.
unfold E in |- *.
clear H4 E.
induction (codePrf x0 x x1).
simpl in |- *.
apply eqRefl.
unfold nat_rec, nat_rect in |- *.
rewrite LNN2LNT_and.
apply andI.
induction
 (eq_nat_dec
    (checkPrf LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR
       (codeFormula (notH x)) n) 0).
unfold codeSysPrfNot in |- *.
apply T'prf2Tprf.
apply codeSysPrfNCorrect3.
unfold not in |- *; intros.
rewrite H4 in a.
rewrite
 (checkPrfCorrect1 LNT codeLNTFunction codeLNTRelation codeArityLNTF
    codeArityLNTR codeArityLNTFIsCorrect1 codeArityLNTRIsCorrect1)
  in a.
discriminate a.
decompose record
 (checkPrfCorrect2 LNT codeLNTFunction codeLNTRelation codeArityLNTF
    codeArityLNTR codeArityLNTFIsCorrect1 codeArityLNTFIsCorrect2
    codeArityLNTRIsCorrect1 codeArityLNTRIsCorrect2 codeLNTFunctionInj
    codeLNTRelationInj _ _ b).
rewrite <- H6.
assert (x2 = notH x).
eapply codeFormulaInj.
apply codeLNTFunctionInj.
apply codeLNTRelationInj.
assumption.
cut (code.codePrf LNT codeLNTFunction codeLNTRelation x3 x2 x4 = n).
generalize x4.
clear H6 x4.
rewrite H4.
intros.
apply T'prf2Tprf.
apply codeSysPrfNCorrect2.
eapply H3.
apply lt_S.
rewrite <- H6.
apply lt_n_Sn.
assumption.
apply IHn.
intros.
eapply H3.
apply lt_S.
apply H4.
unfold Inconsistent in |- *.
intros.
elim H.
intros.
induction H2 as (x1, H2).
induction (searchProof decide _ x _ x1).
decompose record H3.
apply contradiction with x.
exists x2.
exists x3.
assumption.
assumption.
apply
 contradiction
  with
    (substituteFormula LNT (LNN2LNT_formula A) 0
       (natToTermLNT (code.codeFormula LNT codeLNTFunction codeLNTRelation x))).
unfold A in |- *.
replace
 (LNN2LNT_formula
    (fol.forallH LNN 1
       (fol.impH LNN codeSysPrf
          (fol.existH LNN 2
             (fol.andH LNN (LT (fol.var LNN 2) (fol.var LNN 1))
                (substituteFormula LNN codeSysPrfNot 1 (fol.var LNN 2)))))))
 with
 (forallH 1
    (impH (LNN2LNT_formula codeSysPrf)
       (existH 2
          (andH (LNN2LNT_formula (LT (fol.var LNN 2) (fol.var LNN 1)))
             (LNN2LNT_formula
                (substituteFormula LNN codeSysPrfNot 1 (fol.var LNN 2))))))).
rewrite (subFormulaForall LNT).
induction (eq_nat_dec 1 0).
discriminate a.
induction
 (In_dec eq_nat_dec 1
    (freeVarTerm LNT
       (natToTermLNT (code.codeFormula LNT codeLNTFunction codeLNTRelation x)))).
elim (closedNatToTerm _ _ a).
clear b0 b.
set
 (E :=
  LNN2LNT_formula
    (nat_rec (fun _ => fol.Formula LNN) (LNT2LNN_formula (equal Zero Zero))
       (fun (n : nat) rec =>
        fol.andH LNN
          (fol.notH LNN
             (substituteFormula LNN
                (substituteFormula LNN codeSysPrf 0
                   (natToTermLNN (codeFormula x))) 1 
                (natToTermLNN n))) rec) (S (codePrf _ _ x1)))) 
 in *.
assert (forall x : nat, ~ In x (freeVarFormula LNT E)).
unfold E in |- *.
clear H3 E.
induction (S (codePrf x0 (notH x) x1)).
simpl in |- *.
auto.
intros.
unfold nat_rec, nat_rect in |- *.
unfold not in |- *; intros.
cut
 (In x2
    (freeVarFormula LNN
       (fol.andH LNN
          (fol.notH LNN
             (substituteFormula LNN
                (substituteFormula LNN codeSysPrf 0
                   (natToTermLNN (codeFormula x))) 1 
                (natToTermLNN n)))
          ((fix F (n : nat) : (fun _ : nat => fol.Formula LNN) n :=
              match n with
              | O => LNT2LNN_formula (equal Zero Zero)
              | S n0 =>
                  (fun (n1 : nat) (rec : fol.Formula LNN) =>
                   fol.andH LNN
                     (fol.notH LNN
                        (substituteFormula LNN
                           (substituteFormula LNN codeSysPrf 0
                              (natToTermLNN (codeFormula x))) 1
                           (natToTermLNN n1))) rec) n0 
                    (F n0)
              end) n)))).
clear H3.
intros.
SimplFreeVar.
apply (le_not_lt x2 1).
apply
 (freeVarCodeSysPrf LNT codeLNTFunction codeLNTRelation codeArityLNTF
    codeArityLNTR codeArityLNTFIsPR codeArityLNTRIsPR 
    (LNT2LNN_formula repT) v0 freeVarRepT').
apply H4.
destruct x2 as [| n0].
elim H6; reflexivity.
destruct n0.
elim H5; reflexivity.
apply lt_n_S.
apply lt_O_Sn.
rewrite <- LNT2LNN_natToTerm in H3.
rewrite LNT2LNN_freeVarTerm in H3.
apply (closedNatToTerm _ _ H3).
rewrite <- LNT2LNN_natToTerm in H3.
rewrite LNT2LNN_freeVarTerm in H3.
apply (closedNatToTerm _ _ H3).
assert
 (In x2
    (freeVarFormula LNT
       (LNN2LNT_formula
          (nat_rec (fun _ : nat => fol.Formula LNN)
             (LNT2LNN_formula (equal Zero Zero))
             (fun (n : nat) (rec : fol.Formula LNN) =>
              fol.andH LNN
                (fol.notH LNN
                   (substituteFormula LNN
                      (substituteFormula LNN codeSysPrf 0
                         (natToTermLNN (codeFormula x))) 1 
                      (natToTermLNN n))) rec) n)))).
apply LNN2LNT_freeVarFormula2.
apply H3.
apply (IHn _ H4).
apply LNN2LNT_freeVarFormula1.
apply H3.
apply impE with E.
set
 (G :=
  substituteFormula LNT
    (substituteFormula LNT (LNN2LNT_formula codeSysPrfNot) 0
       (natToTerm (codeFormula x))) 1 (natToTerm (codePrf x0 (notH x) x1)))
 in *.
apply impE with G.
apply sysExtend with PA.
assumption.
repeat apply impI.
apply forallI.
unfold not in |- *; intros.
induction H5 as (x2, H5); induction H5 as (H5, H6).
induction H6 as [x2 H6| x2 H6].
induction H6 as [x2 H6| x2 H6].
apply (closedPA 1).
exists x2.
auto.
induction H6.
unfold G in H5.
SimplFreeVar.
induction H6.
apply (H4 _ H5).
rewrite (subFormulaImp LNT).
rewrite (subFormulaExist LNT).
induction (eq_nat_dec 2 0).
discriminate a.
induction
 (In_dec eq_nat_dec 2
    (freeVarTerm LNT
       (natToTermLNT (code.codeFormula LNT codeLNTFunction codeLNTRelation x)))).
elim (closedNatToTerm _ _ a).
clear b0 b.
rewrite (subFormulaAnd LNT).
apply
 impE
  with
    (fol.impH LNT
       (substituteFormula LNT (LNN2LNT_formula codeSysPrf) 0
          (natToTermLNT
             (code.codeFormula LNT codeLNTFunction codeLNTRelation x)))
       (fol.existH LNT 2
          (fol.andH LNT
             (LNN2LNT_formula (LT (fol.var LNN 2) (fol.var LNN 1)))
             (substituteFormula LNT
                (LNN2LNT_formula
                   (substituteFormula LNN codeSysPrfNot 1 (fol.var LNN 2))) 0
                (natToTermLNT
                   (code.codeFormula LNT codeLNTFunction codeLNTRelation x)))))).
repeat simple apply sysWeaken.
apply iffE1.
apply (reduceImp LNT).
apply iffRefl.
apply (reduceExist LNT).
apply closedPA.
apply (reduceAnd LNT).
apply
 iffTrans
  with
    (LNN2LNT_formula
       (substituteFormula LNN (LT (fol.var LNN 2) (fol.var LNN 1)) 0
          (natToTermLNN
             (code.codeFormula LNT codeLNTFunction codeLNTRelation x)))).
rewrite <- LNN2LNT_iff.
apply NN2PA.
apply (folLogic.iffRefl LNN).
rewrite <- LNN2LNT_natToTerm.
apply LNN2LNT_subFormula.
apply iffRefl.
apply
 orE
  with
    (LNN2LNT_formula
       (fol.orH LNN
          (LT (fol.var LNN 1) (natToTermLNN (codePrf x0 (notH x) x1)))
          (LNT2LNN_formula
             (equal (var 1) (natToTerm (codePrf x0 (notH x) x1))))))
    (LNN2LNT_formula
       (LT (natToTermLNN (codePrf x0 (notH x) x1)) (fol.var LNN 1))).
repeat simple apply sysWeaken.
apply
 impE
  with
    (LNN2LNT_formula
       (fol.orH LNN
          (LT (fol.var LNN 1) (natToTermLNN (codePrf x0 (notH x) x1)))
          (fol.orH LNN
             (LNT2LNN_formula
                (equal (var 1) (natToTerm (codePrf x0 (notH x) x1))))
             (LT (natToTermLNN (codePrf x0 (notH x) x1)) (fol.var LNN 1))))).
repeat rewrite LNN2LNT_or.
apply impI.
apply orSys.
apply orI1.
apply orI1.
apply Axm; right; constructor.
apply orSys.
apply orI1.
apply orI2.
apply Axm; right; constructor.
apply orI2.
apply Axm; right; constructor.
apply NN2PA.
simpl in |- *.
rewrite LNT2LNN_natToTerm.
apply nn9.
apply impI.
apply impE with G.
apply impE with E.
apply
 impE
  with
    (LNN2LNT_formula
       (LT (fol.var LNN 1) (natToTermLNN (S (codePrf x0 (notH x) x1))))).
repeat simple apply sysWeaken.
apply PAboundedLT.
intros.
repeat rewrite (subFormulaImp LNT).
repeat apply impI.
fold codeFormula in |- *.
apply
 contradiction
  with
    (substituteFormula LNT
       (substituteFormula LNT (LNN2LNT_formula codeSysPrf) 0
          (natToTermLNT (codeFormula x))) 1 (natToTerm n)).
apply Axm; right; constructor.
apply sysWeaken.
apply impE with E.
repeat simple apply sysWeaken.
apply impI.
clear H3 H4.
induction (S (codePrf x0 (notH x) x1)).
elim (lt_n_O _ H5).
induction (le_lt_or_eq _ _ (lt_n_Sm_le _ _ H5)).
unfold E in |- *.
apply
 impE
  with
    (LNN2LNT_formula
       (nat_rec (fun _ : nat => fol.Formula LNN)
          (LNT2LNN_formula (equal Zero Zero))
          (fun (n1 : nat) (rec : fol.Formula LNN) =>
           fol.andH LNN
             (fol.notH LNN
                (substituteFormula LNN
                   (substituteFormula LNN codeSysPrf 0
                      (natToTermLNN (codeFormula x))) 1 
                   (natToTermLNN n1))) rec) n0)).
apply sysWeaken.
repeat apply impI.
apply IHn0.
assumption.
unfold nat_rec, nat_rect in |- *.
rewrite LNN2LNT_and.
eapply andE2.
apply Axm; right; constructor.
unfold E in |- *.
unfold nat_rec, nat_rect in |- *.
rewrite H3.
rewrite LNN2LNT_and.
apply
 impE
  with
    (LNN2LNT_formula
       (fol.notH LNN
          (substituteFormula LNN
             (substituteFormula LNN codeSysPrf 0
                (natToTermLNN (codeFormula x))) 1 (natToTermLNN n0)))).
apply sysWeaken.
apply iffE1.
apply
 iffTrans
  with
    (notH
       (LNN2LNT_formula
          (substituteFormula LNN
             (substituteFormula LNN codeSysPrf 0
                (natToTermLNN (codeFormula x))) 1 (natToTermLNN n0)))).
apply iffRefl.
apply (reduceNot LNT).
repeat rewrite <- LNN2LNT_natToTerm.
apply
 iffTrans
  with
    (substituteFormula LNT
       (LNN2LNT_formula
          (substituteFormula LNN codeSysPrf 0 (natToTermLNN (codeFormula x))))
       1 (LNN2LNT_term (natToTermLNN n0))).
apply LNN2LNT_subFormula.
apply (reduceSub LNT).
apply closedPA.
apply LNN2LNT_subFormula.
eapply andE1.
apply Axm; right; constructor.
apply impE with (substituteFormula LNT E 1 (natToTerm n)).
apply iffE1.
apply (subFormulaNil LNT).
apply H4.
apply Axm; left; right; constructor.
apply
 impE
  with
    (LNN2LNT_formula
       (fol.orH LNN
          (LT (fol.var LNN 1) (natToTermLNN (codePrf x0 (notH x) x1)))
          (LNT2LNN_formula
             (equal (var 1) (natToTerm (codePrf x0 (notH x) x1)))))).
repeat simple apply sysWeaken.
replace
 (impH
    (LNN2LNT_formula
       (fol.orH LNN
          (LT (fol.var LNN 1) (natToTermLNN (codePrf x0 (notH x) x1)))
          (LNT2LNN_formula
             (equal (var 1) (natToTerm (codePrf x0 (notH x) x1))))))
    (LNN2LNT_formula
       (LT (fol.var LNN 1) (natToTermLNN (S (codePrf x0 (notH x) x1))))))
 with
 (LNN2LNT_formula
    (fol.impH LNN
       (fol.orH LNN
          (LT (fol.var LNN 1) (natToTermLNN (codePrf x0 (notH x) x1)))
          (LNT2LNN_formula
             (equal (var 1) (natToTerm (codePrf x0 (notH x) x1)))))
       (LT (fol.var LNN 1) (natToTermLNN (S (codePrf x0 (notH x) x1)))))).
apply NN2PA.
simpl in |- *.
rewrite LNT2LNN_natToTerm.
apply nnPlusNotNeeded.
reflexivity.
apply Axm; right; constructor.
apply Axm; left; right; constructor.
apply Axm; do 2 left; right; constructor.
repeat apply impI.
apply sysWeaken.
apply existI with (natToTerm (codePrf x0 (notH x) x1)).
rewrite (subFormulaAnd LNT).
apply andI.
apply
 impE
  with
    (LNN2LNT_formula
       (LT (natToTermLNN (codePrf x0 (notH x) x1)) (fol.var LNN 1))).
repeat simple apply sysWeaken.
apply
 impTrans
  with
    (LNN2LNT_formula
       (substituteFormula LNN (LT (fol.var LNN 2) (fol.var LNN 1)) 2
          (natToTermLNN (codePrf x0 (notH x) x1)))).
replace
 (impH
    (LNN2LNT_formula
       (LT (natToTermLNN (codePrf x0 (notH x) x1)) (fol.var LNN 1)))
    (LNN2LNT_formula
       (substituteFormula LNN (LT (fol.var LNN 2) (fol.var LNN 1)) 2
          (natToTermLNN (codePrf x0 (notH x) x1))))) with
 (LNN2LNT_formula
    (fol.impH LNN
       (LT (natToTermLNN (codePrf x0 (notH x) x1)) (fol.var LNN 1))
       (substituteFormula LNN (LT (fol.var LNN 2) (fol.var LNN 1)) 2
          (natToTermLNN (codePrf x0 (notH x) x1))))).
apply NN2PA.
unfold LT in |- *.
apply (folLogic.impI LNN).
rewrite (subFormulaRelation LNN).
simpl in |- *.
apply (folLogic.Axm LNN); right; constructor.
reflexivity.
apply iffE1.
rewrite <- LNN2LNT_natToTerm.
apply LNN2LNT_subFormula.
apply Axm; right; constructor.
apply sysWeaken.
apply sysWeaken.
apply
 impE
  with
    (substituteFormula LNT
       (substituteFormula LNT (LNN2LNT_formula codeSysPrfNot) 0
          (natToTerm (codeFormula x))) 1 (natToTerm (codePrf x0 (notH x) x1))).
apply sysWeaken.
apply iffE2.
fold codeFormula in |- *.
apply
 iffTrans
  with
    (substituteFormula LNT
       (substituteFormula LNT
          (substituteFormula LNT (LNN2LNT_formula codeSysPrfNot) 1 (var 2)) 0
          (natToTermLNT (codeFormula x))) 2
       (natToTerm (codePrf x0 (notH x) x1))).
repeat (apply (reduceSub LNT); [ apply closedPA | idtac ]).
replace (var 2) with (LNN2LNT_term (fol.var LNN 2)).
apply LNN2LNT_subFormula.
reflexivity.
apply
 iffTrans
  with
    (substituteFormula LNT
       (substituteFormula LNT
          (substituteFormula LNT (LNN2LNT_formula codeSysPrfNot) 0
             (natToTermLNT (codeFormula x))) 1 (var 2)) 2
       (natToTerm (codePrf x0 (notH x) x1))).
repeat (apply (reduceSub LNT); [ apply closedPA | idtac ]).
apply (subFormulaExch LNT).
discriminate.
unfold not in |- *; intros; SimplFreeVar.
discriminate H6.
apply closedNatToTerm.
apply (subFormulaTrans LNT).
unfold not in |- *; intros; SimplFreeVar.
apply (le_not_lt 2 1).
apply freeVarCodeSysPrfN.
apply LNN2LNT_freeVarFormula1.
assumption.
apply lt_n_Sn.
apply Axm; right; constructor.
unfold G in |- *.
apply
 impE
  with
    (LNN2LNT_formula
       (substituteFormula LNN
          (substituteFormula LNN codeSysPrfNot 0
             (natToTermLNN (codeFormula x))) 1
          (natToTermLNN (codePrf x0 (notH x) x1)))).
apply iffE1.
repeat rewrite <- LNN2LNT_natToTerm.
apply
 iffTrans
  with
    (substituteFormula LNT
       (LNN2LNT_formula
          (substituteFormula LNN codeSysPrfNot 0
             (natToTermLNN (codeFormula x)))) 1
       (LNN2LNT_term (natToTermLNN (codePrf x0 (notH x) x1)))).
apply LNN2LNT_subFormula.
apply sysExtend with PA.
assumption.
apply (reduceSub LNT).
apply closedPA.
apply LNN2LNT_subFormula.
apply T'prf2Tprf.
apply codeSysPrfNCorrect1.
assumption.
clear H4.
unfold E in |- *; clear E.
induction (S (codePrf x0 (notH x) x1)).
simpl in |- *.
apply eqRefl.
unfold nat_rec, nat_rect in |- *.
rewrite LNN2LNT_and.
apply andI.
induction
 (eq_nat_dec
    (checkPrf LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR
       (codeFormula x) n) 0).
unfold codeSysPrf, codeFormula in |- *.
apply T'prf2Tprf.
apply codeSysPrfCorrect3.
unfold not in |- *; intros.
rewrite H4 in a.
rewrite
 (checkPrfCorrect1 LNT codeLNTFunction codeLNTRelation codeArityLNTF
    codeArityLNTR codeArityLNTFIsCorrect1 codeArityLNTRIsCorrect1)
  in a.
discriminate a.
decompose record
 (checkPrfCorrect2 LNT codeLNTFunction codeLNTRelation codeArityLNTF
    codeArityLNTR codeArityLNTFIsCorrect1 codeArityLNTFIsCorrect2
    codeArityLNTRIsCorrect1 codeArityLNTRIsCorrect2 codeLNTFunctionInj
    codeLNTRelationInj _ _ b).
rewrite <- H6.
assert (x2 = x).
eapply (codeFormulaInj LNT).
apply codeLNTFunctionInj.
apply codeLNTRelationInj.
assumption.
rewrite <- H4.
apply T'prf2Tprf.
apply codeSysPrfCorrect2.
rewrite <- H4 in H3.
apply H3 with x4.
rewrite <- H6.
apply lt_n_Sn.
apply IHn.
intros.
eapply H3.
apply lt_S.
apply H4.
reflexivity.
apply impE with (notH x).
apply cp2.
apply iffE2.
apply sysExtend with PA.
apply extendsPA.
assumption.
assumption.
Qed.

End Rosser's_Incompleteness.

Require Import codePA.
Require Import PAconsistent.

Theorem PAIncomplete :
 exists f : Formula,
   (Sentence f) /\ ~(SysPrf PA f \/ SysPrf PA (notH f)).
Proof.
assert
 (Expressible NN 1 codePA
    (substituteFormula LNN (primRecFormula 1 (proj1_sig codePAIsPR)) 0
       (natToTermLNN 1))).
apply (Representable2Expressible _ closedNN1).
simpl.
apply nn1.
apply primRecRepresentable.
induction H as (H, H0).
simpl in H0.
assert
 (exists f : Formula,
    (forall v : nat, ~ In v (freeVarFormula LNT f)) /\
    (SysPrf PA f \/ SysPrf PA (notH f) -> Inconsistent LNT PA)).
eapply
 Rosser'sIncompleteness
                        with
                        (repT := 
                          LNN2LNT_formula
                            (substituteFormula LNN
                               (primRecFormula 1 (proj1_sig codePAIsPR)) 0
                               (natToTermLNN 1)))
                       (v0 := 1).
unfold Included in |- *.
auto.
intros.
assert (v <= 1 /\ v <> 0).
apply H.
apply LNN2LNT_freeVarFormula1.
apply H1.
destruct v as [| n].
induction H2 as (H2, H3).
elim H3.
reflexivity.
destruct n.
reflexivity.
induction H2 as (H2, H3).
elim (le_not_lt _ _ H2).
apply lt_n_S.
apply lt_O_Sn.
intros.
rewrite <- LNN2LNT_natToTerm.
eapply impE.
apply iffE1.
apply LNN2LNT_subFormula.
apply NN2PA.
assert
 (if codePA (codeFormula f)
  then
   LNN.SysPrf NN
     (substituteFormula LNN
        (substituteFormula LNN (primRecFormula 1 (proj1_sig codePAIsPR)) 0
           (LNN.Succ LNN.Zero)) 1 (LNN.natToTerm (codeFormula f)))
  else
   LNN.SysPrf NN
     (LNN.notH
        (substituteFormula LNN
           (substituteFormula LNN (primRecFormula 1 (proj1_sig codePAIsPR)) 0
              (LNN.Succ LNN.Zero)) 1 (LNN.natToTerm (codeFormula f))))).
apply H0. clear H0.
assert (codePA (codeFormula f) = true).
apply codePAcorrect3.
assumption.
rewrite H0 in H2.
assumption.
intros.
rewrite <- LNN2LNT_natToTerm.
eapply
 impE
      with
      (LNN2LNT_formula
         (LNN.notH
            (substituteFormula LNN
               (substituteFormula LNN
                  (primRecFormula 1 (proj1_sig codePAIsPR)) 0
                  (LNN.Succ LNN.Zero)) 1 (LNN.natToTerm (codeFormula f))))).
simpl in |- *.
apply cp2.
apply iffE2.
apply LNN2LNT_subFormula.
apply NN2PA.
assert
 (if codePA (codeFormula f)
  then
   LNN.SysPrf NN
     (substituteFormula LNN
        (substituteFormula LNN (primRecFormula 1 (proj1_sig codePAIsPR)) 0
           (LNN.Succ LNN.Zero)) 1 (LNN.natToTerm (codeFormula f)))
  else
   LNN.SysPrf NN
     (LNN.notH
        (substituteFormula LNN
           (substituteFormula LNN (primRecFormula 1 (proj1_sig codePAIsPR)) 0
              (LNN.Succ LNN.Zero)) 1 (LNN.natToTerm (codeFormula f))))).
apply H0. clear H0.
assert (codePA (codeFormula f) = false).
apply codePAcorrect2.
assumption.
rewrite H0 in H2.
assumption.
apply PAdec.
clear H H0.
decompose record H1.
exists x.
split.
assumption.
unfold not in |- *; intros.
unfold Inconsistent in H2.
induction PAconsistent.
auto.
Qed.
