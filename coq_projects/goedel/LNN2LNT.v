Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import misc.

Require Import ListExt.
Require Import folProp.
Require Import folProof.
Require Import Languages.
Require Import subAll.
Require Import subProp.
Require Import folLogic3.
Require Import folReplace.
Require Import LNT.
Require Import Max.
Require Import codeNatToTerm.

Fixpoint LNN2LNT_term (t : fol.Term LNN) : Term :=
  match t with
  | fol.var v => var v
  | apply f ts => apply LNT f (LNN2LNT_terms _ ts)
  end
 
 with LNN2LNT_terms (n : nat) (ts : fol.Terms LNN n) {struct ts} : 
 Terms n :=
  match ts in (fol.Terms _ n0) return (Terms n0) with
  | Tnil => Tnil LNT
  | Tcons m s ss => Tcons LNT m (LNN2LNT_term s) (LNN2LNT_terms m ss)
  end. 

Definition LTFormula :=
  existH 2 (equal (Plus (var 0) (Succ (var 2))) (var 1)).

Definition translateLT (ts : fol.Terms LNN (arity LNN (inl _ LT))) : Formula.
simpl in ts.
induction (consTerms _ _ ts).
induction x as (a, b).
induction (consTerms _ _ b).
induction x as (a0, b0).
set (x := LNN2LNT_term a) in *.
set (y := LNN2LNT_term a0) in *.
apply (subAllFormula LNT LTFormula).
intro.
induction H as [| H HrecH].
exact x.
induction H as [| H HrecH0].
exact y.
exact (var H).
Defined.

Lemma LNN2LNT_natToTerm :
 forall n : nat, LNN2LNT_term (natToTermLNN n) = natToTerm n.
Proof.
intros.
induction n as [| n Hrecn].
reflexivity.
simpl in |- *.
rewrite Hrecn.
reflexivity.
Qed.

Lemma translateLT1 :
 forall a a0 b0,
 translateLT (Tcons LNN 1 a (Tcons LNN 0 a0 b0)) =
 subAllFormula LNT LTFormula
   (fun H : nat =>
    nat_rec (fun _ : nat => fol.Term LNT) (LNN2LNT_term a)
      (fun (H0 : nat) (_ : fol.Term LNT) =>
       nat_rec (fun _ : nat => fol.Term LNT) (LNN2LNT_term a0)
         (fun (H1 : nat) (_ : fol.Term LNT) => var H1) H0) H).
Proof.
intros.
unfold translateLT in |- *.
induction (consTerms LNN 1 (Tcons LNN 1 a (Tcons LNN 0 a0 b0))).
induction x as (a1, b).
simpl in |- *.
induction (consTerms LNN 0 b).
induction x as (a2, b1).
simpl in |- *.
simpl in p.
inversion p.
assert (b = Tcons LNN 0 a0 b0).
refine (inj_right_pair2 _ eq_nat_dec _ _ _ _ H1).
rewrite H in p0.
simpl in p0.
inversion p0.
clear H4 H3 H H1 H0.
reflexivity.
Qed.

Fixpoint LNN2LNT_formula (f : fol.Formula LNN) : Formula :=
  match f with
  | fol.equal t1 t2 => equal (LNN2LNT_term t1) (LNN2LNT_term t2)
  | atomic r ts =>
      match
        r as l return (fol.Terms LNN (arity LNN (inl _ l)) -> Formula)
      with
      | LT => fun t0 : fol.Terms LNN (arity LNN (inl _ LT)) => translateLT t0
      end ts
  | fol.impH A B => impH (LNN2LNT_formula A) (LNN2LNT_formula B)
  | fol.notH A => notH (LNN2LNT_formula A)
  | fol.forallH v A => forallH v (LNN2LNT_formula A)
  end.

Lemma LNN2LNT_or :
 forall a b : fol.Formula LNN,
 LNN2LNT_formula (fol.orH LNN a b) =
 orH (LNN2LNT_formula a) (LNN2LNT_formula b).
Proof.
reflexivity.
Qed.

Lemma LNN2LNT_and :
 forall a b : fol.Formula LNN,
 LNN2LNT_formula (fol.andH LNN a b) =
 andH (LNN2LNT_formula a) (LNN2LNT_formula b).
Proof.
reflexivity.
Qed.

Lemma LNN2LNT_iff :
 forall a b : fol.Formula LNN,
 LNN2LNT_formula (fol.iffH LNN a b) =
 iffH (LNN2LNT_formula a) (LNN2LNT_formula b).
Proof.
reflexivity.
Qed.

Lemma LNN2LNT_exist :
 forall (v : nat) (a : fol.Formula LNN),
 LNN2LNT_formula (fol.existH LNN v a) = existH v (LNN2LNT_formula a).
Proof.
reflexivity.
Qed.

Lemma LNN2LNT_freeVarTerm :
 forall t : fol.Term LNN,
 freeVarTerm LNT (LNN2LNT_term t) = freeVarTerm LNN t.
Proof.
intros.
elim t using
 Term_Terms_ind
  with
    (P0 := fun (n : nat) (ts : fol.Terms LNN n) =>
           freeVarTerms LNT n (LNN2LNT_terms n ts) = freeVarTerms LNN n ts).
intros.
reflexivity.
intros.
simpl in |- *.
repeat rewrite freeVarTermApply.
apply H.
reflexivity.
intros.
simpl in |- *.
transitivity (freeVarTerm LNN t0 ++ freeVarTerms LNN n t1).
rewrite <- H0.
rewrite <- H.
reflexivity.
reflexivity.
Qed.

Lemma LNN2LNT_freeVarTerms :
 forall (n : nat) (ts : fol.Terms LNN n),
 freeVarTerms LNT n (LNN2LNT_terms n ts) = freeVarTerms LNN n ts.
Proof.
intros.
induction ts as [| n t ts Hrects].
reflexivity.
intros.
simpl in |- *.
transitivity (freeVarTerm LNN t ++ freeVarTerms LNN n ts).
rewrite <- Hrects.
rewrite <- LNN2LNT_freeVarTerm.
reflexivity.
reflexivity.
Qed.

Lemma LNN2LNT_freeVarFormula :
 forall (f : fol.Formula LNN) (v : nat),
 In v (freeVarFormula LNT (LNN2LNT_formula f)) <->
 In v (freeVarFormula LNN f).
Proof.
intros.
induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf].
simpl in |- *.
repeat rewrite LNN2LNT_freeVarTerm.
tauto.
induction r.
simpl in |- *.
induction (consTerms _ _ t).
induction x as (a, b).
simpl in p.
rewrite <- p.
induction (consTerms _ _ b).
induction x as (a0, b0).
simpl in p0.
rewrite <- p0.
rewrite translateLT1.
rewrite <- (nilTerms _ b0).
unfold freeVarTerms in |- *.
fold (freeVarTerm LNN) in |- *.
rewrite <- app_nil_end.
split.
intros.
decompose record (freeVarSubAllFormula1 _ _ _ _ H).
simpl in H1.
induction H1 as [H0| H0].
rewrite <- H0 in H2.
simpl in H2.
rewrite LNN2LNT_freeVarTerm in H2.
auto with datatypes.
induction H0 as [H0| H0].
rewrite <- H0 in H2.
simpl in H2.
rewrite LNN2LNT_freeVarTerm in H2.
auto with datatypes.
contradiction.
intros.
induction (in_app_or _ _ _ H).
eapply freeVarSubAllFormula2.
simpl in |- *.
left.
reflexivity.
simpl in |- *.
rewrite LNN2LNT_freeVarTerm.
auto.
eapply freeVarSubAllFormula2.
simpl in |- *.
right.
left.
reflexivity.
simpl in |- *.
rewrite LNN2LNT_freeVarTerm.
auto.
simpl in |- *.
induction Hrecf1 as (H, H0).
induction Hrecf0 as (H1, H2).
split.
intros.
apply in_or_app.
induction (in_app_or _ _ _ H3); tauto.
intros.
apply in_or_app.
induction (in_app_or _ _ _ H3); tauto.
assumption.
simpl in |- *.
induction Hrecf as (H, H0).
split.
intros.
apply In_list_remove3.
apply H.
eapply In_list_remove1.
apply H1.
eapply In_list_remove2.
apply H1.
intros.
apply In_list_remove3.
apply H0.
eapply In_list_remove1.
apply H1.
eapply In_list_remove2.
apply H1.
Qed.

Lemma LNN2LNT_freeVarFormula1 :
 forall (f : fol.Formula LNN) (v : nat),
 In v (freeVarFormula LNT (LNN2LNT_formula f)) -> In v (freeVarFormula LNN f).
Proof.
intros.
induction (LNN2LNT_freeVarFormula f v).
auto.
Qed.

Lemma LNN2LNT_freeVarFormula2 :
 forall (f : fol.Formula LNN) (v : nat),
 In v (freeVarFormula LNN f) -> In v (freeVarFormula LNT (LNN2LNT_formula f)).
Proof.
intros.
induction (LNN2LNT_freeVarFormula f v).
auto.
Qed.

Lemma LNN2LNT_subTerm :
 forall (t : fol.Term LNN) (v : nat) (s : fol.Term LNN),
 LNN2LNT_term (substituteTerm LNN t v s) =
 substituteTerm LNT (LNN2LNT_term t) v (LNN2LNT_term s).
Proof.
intros.
elim t using
 Term_Terms_ind
  with
    (P0 := fun (n : nat) (ts : fol.Terms LNN n) =>
           LNN2LNT_terms n (substituteTerms LNN n ts v s) =
           substituteTerms LNT n (LNN2LNT_terms n ts) v (LNN2LNT_term s)).
intros.
simpl in |- *.
induction (eq_nat_dec v n); auto.
simpl in |- *.
intros.
rewrite H.
reflexivity.
reflexivity.
simpl in |- *.
intros.
rewrite H.
rewrite H0.
reflexivity.
Qed.

Lemma LNN2LNT_subTerms :
 forall (n : nat) (ts : fol.Terms LNN n) (v : nat) (s : fol.Term LNN),
 LNN2LNT_terms n (substituteTerms LNN n ts v s) =
 substituteTerms LNT n (LNN2LNT_terms n ts) v (LNN2LNT_term s).
Proof.
intros.
induction ts as [| n t ts Hrects].
reflexivity.
simpl in |- *.
rewrite Hrects.
rewrite LNN2LNT_subTerm.
reflexivity.
Qed.

Lemma LNN2LNT_subFormula :
 forall (T : System) (f : fol.Formula LNN) (v : nat) (s : fol.Term LNN),
 SysPrf T
   (iffH (LNN2LNT_formula (substituteFormula LNN f v s))
      (substituteFormula LNT (LNN2LNT_formula f) v (LNN2LNT_term s))).
Proof.
intros.
apply sysExtend with (Empty_set Formula).
unfold Included in |- *.
intros.
induction H.
generalize f v s.
clear T f v s.
intro.
elim f using Formula_depth_ind2; intros.
simpl in |- *.
rewrite (subFormulaEqual LNT).
repeat rewrite LNN2LNT_subTerm.
apply iffRefl.
induction r.
rewrite subFormulaRelation.
simpl in |- *.
induction (consTerms _ _ t).
induction x as (a, b).
simpl in p.
rewrite <- p.
induction (consTerms _ _ b).
induction x as (a0, b0).
simpl in p0.
rewrite <- p0.
rewrite translateLT1.
apply iffSym.
eapply iffTrans.
apply (subSubAllFormula LNT).
rewrite <- (nilTerms _ b0).
replace
 (substituteTerms LNN 2 (Tcons LNN 1 a (Tcons LNN 0 a0 (Tnil LNN))) v s) with
 (Tcons LNN 1 (substituteTerm LNN a v s)
    (Tcons LNN 0 (substituteTerm LNN a0 v s) (Tnil LNN))).
rewrite translateLT1.
rewrite
 (subAllFormula_ext LNT LTFormula
    (fun H : nat =>
     nat_rec (fun _ : nat => fol.Term LNT)
       (LNN2LNT_term (substituteTerm LNN a v s))
       (fun (H0 : nat) (_ : fol.Term LNT) =>
        nat_rec (fun _ : nat => fol.Term LNT)
          (LNN2LNT_term (substituteTerm LNN a0 v s))
          (fun (H1 : nat) (_ : fol.Term LNT) => var H1) H0) H)
    (fun n : nat =>
     substituteTerm LNT
       (nat_rec (fun _ : nat => fol.Term LNT) (LNN2LNT_term a)
          (fun (H0 : nat) (_ : fol.Term LNT) =>
           nat_rec (fun _ : nat => fol.Term LNT) (LNN2LNT_term a0)
             (fun (H1 : nat) (_ : fol.Term LNT) => var H1) H0) n) v
       (LNN2LNT_term s))).
apply iffRefl.
intros.
destruct m as [| n].
simpl in |- *.
apply LNN2LNT_subTerm.
destruct n.
simpl in |- *.
apply LNN2LNT_subTerm.
simpl in H.
decompose sum H.
discriminate H0.
discriminate H1.
reflexivity.
rewrite subFormulaImp.
simpl in |- *.
rewrite (subFormulaImp LNT).
apply (reduceImp LNT).
apply H.
apply H0.
rewrite subFormulaNot.
simpl in |- *.
rewrite (subFormulaNot LNT).
apply (reduceNot LNT).
apply H.
simpl in |- *.
decompose record (subFormulaForall2 LNN a v v0 s).
rewrite H4; clear H4.
decompose record
 (subFormulaForall2 LNT (LNN2LNT_formula a) v v0 (LNN2LNT_term s)).
unfold forallH in |- *.
rewrite H7; clear H7.
induction (eq_nat_dec v v0).
simpl in |- *.
apply iffRefl.
simpl in |- *.
apply
 iffTrans
  with
    (forallH x0
       (substituteFormula LNT
          (LNN2LNT_formula
             (substituteFormula LNN
                (substituteFormula LNN a v (fol.var LNN x)) v0 s)) x 
          (var x0))).
apply (rebindForall LNT).
unfold not in |- *; intros.
assert
 (In x0
    (freeVarFormula LNT
       (LNN2LNT_formula
          (substituteFormula LNN (substituteFormula LNN a v (fol.var LNN x))
             v0 s)))).
eapply In_list_remove1.
apply H6.
assert
 (In x0
    (freeVarFormula LNN
       (substituteFormula LNN (substituteFormula LNN a v (fol.var LNN x)) v0
          s))).
apply LNN2LNT_freeVarFormula1.
assumption.
induction (freeVarSubFormula3 _ _ _ _ _ H8).
assert
 (In x0 (freeVarFormula LNN (substituteFormula LNN a v (fol.var LNN x)))).
eapply In_list_remove1.
apply H9.
induction (freeVarSubFormula3 _ _ _ _ _ H10).
elim H5.
eapply In_list_remove3.
apply LNN2LNT_freeVarFormula2.
eapply In_list_remove1.
apply H11.
eapply In_list_remove2.
apply H11.
elim (In_list_remove2 _ _ _ _ _ H6).
induction H11 as [H11| H11].
auto.
contradiction.
elim H4.
rewrite LNN2LNT_freeVarTerm.
assumption.
apply (reduceForall LNT).
apply (notInFreeVarSys LNT).
apply
 iffTrans
  with
    (substituteFormula LNT
       (substituteFormula LNT
          (substituteFormula LNT (LNN2LNT_formula a) v (fol.var LNT x)) v0
          (LNN2LNT_term s)) x (var x0)).
apply (reduceSub LNT).
apply (notInFreeVarSys LNT).
eapply iffTrans.
apply H.
eapply eqDepth.
symmetry  in |- *; rewrite subFormulaDepth; symmetry  in |- *. (*Hack to rewrite the right occ*)
reflexivity.
apply depthForall.
apply (reduceSub LNT).
apply (notInFreeVarSys LNT).
eapply iffTrans.
apply H.
apply depthForall.
simpl in |- *.
apply iffRefl.
eapply iffTrans.
apply (subFormulaExch LNT).
auto.
rewrite LNN2LNT_freeVarTerm.
auto.
simpl in |- *.
tauto.
apply (reduceSub LNT).
apply (notInFreeVarSys LNT).
apply (subFormulaTrans LNT).
unfold not in |- *; intros; elim H2.
apply In_list_remove3.
apply LNN2LNT_freeVarFormula1.
eapply In_list_remove1.
apply H6.
eapply In_list_remove2.
apply H6.
Qed.

Fixpoint LNT2LNN_term (t : Term) : fol.Term LNN :=
  match t with
  | fol.var v => fol.var LNN v
  | apply f ts => apply LNN f (LNT2LNN_terms _ ts)
  end
 
 with LNT2LNN_terms (n : nat) (ts : Terms n) {struct ts} : 
 fol.Terms LNN n :=
  match ts in (fol.Terms _ n0) return (fol.Terms LNN n0) with
  | Tnil => Tnil LNN
  | Tcons m s ss => Tcons LNN m (LNT2LNN_term s) (LNT2LNN_terms m ss)
  end.

Lemma LNT2LNN_natToTerm :
 forall n : nat, LNT2LNN_term (natToTerm n) = natToTermLNN n.
Proof.
intros.
induction n as [| n Hrecn].
reflexivity.
simpl in |- *.
rewrite Hrecn.
reflexivity.
Qed.

Fixpoint LNT2LNN_formula (f : Formula) : fol.Formula LNN :=
  match f with
  | fol.equal t1 t2 => fol.equal LNN (LNT2LNN_term t1) (LNT2LNN_term t2)
  | atomic r ts => match r with
                   end
  | fol.impH A B => fol.impH LNN (LNT2LNN_formula A) (LNT2LNN_formula B)
  | fol.notH A => fol.notH LNN (LNT2LNN_formula A)
  | fol.forallH v A => fol.forallH LNN v (LNT2LNN_formula A)
  end.

Lemma LNT2LNT_term : forall t : Term, LNN2LNT_term (LNT2LNN_term t) = t.
Proof.
intros.
elim t using
 Term_Terms_ind
  with
    (P0 := fun (n : nat) (ts : fol.Terms LNT n) =>
           LNN2LNT_terms n (LNT2LNN_terms n ts) = ts); 
 simpl in |- *; intros.
reflexivity.
rewrite H.
reflexivity.
reflexivity.
rewrite H.
rewrite H0.
reflexivity.
Qed.

Lemma LNT2LNT_formula :
 forall f : Formula, LNN2LNT_formula (LNT2LNN_formula f) = f.
Proof.
intros.
induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf];
 simpl in |- *.
repeat rewrite LNT2LNT_term.
reflexivity.
induction r.
rewrite Hrecf1.
rewrite Hrecf0.
reflexivity.
rewrite Hrecf.
reflexivity.
rewrite Hrecf.
reflexivity.
Qed.

Lemma LNT2LNN_subTerm :
 forall (t : Term) (v : nat) (s : Term),
 LNT2LNN_term (substituteTerm LNT t v s) =
 substituteTerm LNN (LNT2LNN_term t) v (LNT2LNN_term s).
Proof.
intros.
elim t using
 Term_Terms_ind
  with
    (P0 := fun (n : nat) (ts : fol.Terms LNT n) =>
           LNT2LNN_terms n (substituteTerms LNT n ts v s) =
           substituteTerms LNN n (LNT2LNN_terms n ts) v (LNT2LNN_term s));
 simpl in |- *; intros.
induction (eq_nat_dec v n).
reflexivity.
reflexivity.
rewrite H.
reflexivity.
reflexivity.
rewrite H.
rewrite H0.
reflexivity.
Qed.

Lemma LNT2LNN_freeVarTerm :
 forall t : Term, freeVarTerm LNN (LNT2LNN_term t) = freeVarTerm LNT t.
Proof.
intros.
elim t using
 Term_Terms_ind
  with
    (P0 := fun (n : nat) (ts : fol.Terms LNT n) =>
           freeVarTerms LNN n (LNT2LNN_terms n ts) = freeVarTerms LNT n ts);
 simpl in |- *; intros.
reflexivity.
transitivity
 (freeVarTerms LNN (LNTFunctionArity f)
    (LNT2LNN_terms (LNTFunctionArity f) t0)).
reflexivity.
rewrite H.
reflexivity.
reflexivity.
transitivity
 (freeVarTerm LNN (LNT2LNN_term t0) ++
  freeVarTerms LNN n (LNT2LNN_terms n t1)).
reflexivity.
rewrite H.
rewrite H0.
reflexivity.
Qed.

Lemma LNT2LNN_freeVarFormula :
 forall f : Formula,
 freeVarFormula LNN (LNT2LNN_formula f) = freeVarFormula LNT f.
Proof.
intros.
induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf];
 simpl in |- *.
repeat rewrite LNT2LNN_freeVarTerm.
reflexivity.
induction r.
rewrite Hrecf1.
rewrite Hrecf0.
reflexivity.
assumption.
rewrite Hrecf.
reflexivity.
Qed.

Lemma LNT2LNN_subFormula :
 forall (f : Formula) (v : nat) (s : Term),
 LNT2LNN_formula (substituteFormula LNT f v s) =
 substituteFormula LNN (LNT2LNN_formula f) v (LNT2LNN_term s).
Proof.
intro.
elim f using Formula_depth_ind2; simpl in |- *; intros.
repeat rewrite LNT2LNN_subTerm.
reflexivity.
induction r.
rewrite (subFormulaImp LNT).
simpl in |- *.
rewrite H.
rewrite H0.
rewrite (subFormulaImp LNN).
reflexivity.
rewrite (subFormulaNot LNT).
simpl in |- *.
rewrite H.
rewrite (subFormulaNot LNN).
reflexivity.
rewrite (subFormulaForall LNT).
rewrite (subFormulaForall LNN).
induction (eq_nat_dec v v0).
reflexivity.
rewrite LNT2LNN_freeVarTerm.
induction (In_dec eq_nat_dec v (freeVarTerm LNT s)).
simpl in |- *.
repeat rewrite H.
simpl in |- *.
rewrite LNT2LNN_freeVarFormula.
reflexivity.
apply depthForall.
eapply eqDepth.
symmetry  in |- *; rewrite subFormulaDepth; symmetry  in |- *.
reflexivity.
apply depthForall.
simpl in |- *.
rewrite H.
reflexivity.
apply depthForall.
Qed.

Section Translate_Proof.

Variable U : fol.System LNN.
Variable V : System.

Hypothesis
  AxiomsOK :
    forall f : fol.Formula LNN,
    mem _ U f ->  
    exists Axm : Formulas,
    (exists prf : Prf LNT Axm (LNN2LNT_formula f),
       (forall g : Formula, In g Axm -> mem _ V g)) /\
    forall v, In v (freeVarListFormula LNT Axm) -> (In v (freeVarFormula LNN f)).

Lemma translatePrf : forall f,
 forall axm, Prf LNN axm f -> 
  (forall g, In g axm -> mem _ U g) ->
  exists Axm : Formulas,
    (exists prf : Prf LNT Axm (LNN2LNT_formula f),
       (forall g : Formula, In g Axm -> mem _ V g)) /\
    forall v, In v (freeVarListFormula LNT Axm) -> (In v (freeVarListFormula LNN axm)).
Proof.
intros f x x0 H.
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
   f].
destruct (AxiomsOK A).
auto with *.
exists x.
destruct H0.
split.
apply H0.
intros.
simpl.
rewrite <- app_nil_end.
apply H1.
apply H2.
assert (forall g : fol.Formula LNN,
            In g Axm2 -> mem (fol.Formula LNN) U g).
intros.
apply H.
apply in_or_app.
auto.
assert (forall g : fol.Formula LNN,
            In g Axm1 -> mem (fol.Formula LNN) U g).
intros.
apply H.
apply in_or_app.
auto.
destruct (Hrecx0_0 H0) as [x [[x0 I0] Z0]].
destruct (Hrecx0_1 H1) as [x1 [[x2 I1] Z1]].
clear H0 H1.
rename I0 into H0.
rename I1 into H1.
exists (x1 ++ x).
simpl in x2.
split.
exists (MP LNT _ _ _ _ x2 x0).
intros.
induction (in_app_or _ _ _ H2); auto.
intros.
rewrite freeVarListFormulaApp.
rewrite freeVarListFormulaApp in H2.
apply in_or_app.
destruct (in_app_or _ _ _ H2);
auto with *.
destruct (Hrecx0 H) as [x [[x1 H0] Z]].
exists x.
assert (~ In v (freeVarListFormula LNT x)).
firstorder.
split.
exists (GEN LNT _ _ _ H1 x1).
assumption.
assumption.
exists (nil (A:=Formula)).
split.
exists (IMP1 LNT (LNN2LNT_formula A) (LNN2LNT_formula B)).
contradiction.
contradiction.
exists (nil (A:=Formula)).
split.
exists (IMP2 LNT (LNN2LNT_formula A) (LNN2LNT_formula B) (LNN2LNT_formula C)).
contradiction.
contradiction.
exists (nil (A:=Formula)).
split.
exists (CP LNT (LNN2LNT_formula A) (LNN2LNT_formula B)).
contradiction.
contradiction.
assert (SysPrf (Empty_set _) (LNN2LNT_formula (fol.impH LNN (fol.forallH LNN v A) (substituteFormula LNN A v t)))).
simpl in |- *.
apply
 impE
  with
    (impH (forallH v (LNN2LNT_formula A))
       (substituteFormula LNT (LNN2LNT_formula A) v (LNN2LNT_term t))).
apply iffE1.
apply (reduceImp LNT).
apply iffRefl.
apply iffSym.
apply LNN2LNT_subFormula.
exists (nil (A:=Formula)).
exists (FA1 LNT (LNN2LNT_formula A) v (LNN2LNT_term t)).
contradiction.
destruct H0.
exists x.
split.
destruct H0.
exists x0.
intros.
elim (H0 g H1).
intros.
destruct H0.
destruct x.
assumption.
assert (In f (f::x)).
auto with *.
elim (H0 f H2).
exists (nil (A:=Formula)).
assert (~ In v (freeVarFormula LNT (LNN2LNT_formula A))).
unfold not in |- *; intros; elim n.
apply LNN2LNT_freeVarFormula1.
auto.
split.
exists (FA2 LNT (LNN2LNT_formula A) v H0).
contradiction.
contradiction.
exists (nil (A:=Formula)).
split.
exists (FA3 LNT (LNN2LNT_formula A) (LNN2LNT_formula B) v).
contradiction.
contradiction.
exists (nil (A:=Formula)).
split.
exists (EQ1 LNT).
contradiction.
contradiction.
exists (nil (A:=Formula)).
split.
exists (EQ2 LNT).
contradiction.
contradiction.
exists (nil (A:=Formula)).
split.
exists (EQ3 LNT).
contradiction.
contradiction.
assert (SysPrf (Empty_set _) (LNN2LNT_formula (AxmEq4 LNN R))).
induction R.
simpl in |- *.
repeat apply impI.
unfold notH, impH in |- *.
apply
 impE
  with
    (iffH
       (translateLT
          (Tcons LNN 1 (fol.var LNN 2)
             (Tcons LNN 0 (fol.var LNN 0) (Tnil LNN))))
       (translateLT
          (Tcons LNN 1 (fol.var LNN 3)
             (Tcons LNN 0 (fol.var LNN 1) (Tnil LNN))))).
apply impRefl.
repeat rewrite translateLT1.
simpl in |- *.
unfold newVar in |- *.
simpl in |- *.
apply
 impE
  with
    (iffH (existH 3 (equal (Plus (var 2) (Succ (var 3))) (var 0)))
       (existH 4 (equal (Plus (var 3) (Succ (var 4))) (var 1)))).
apply impRefl.
eapply
 iffTrans
          with
          (existH 4
             (substituteFormula LNT
                (equal (Plus (var 2) (Succ (var 3))) (var 0)) 3 
                (var 4))).
apply (rebindExist LNT).
simpl in |- *.
unfold not in |- *; intros.
decompose sum H0.
discriminate H1.
discriminate H2.
apply (reduceExist LNT).
unfold not in |- *; intros.
induction H0 as (x, H0); induction H0 as (H0, H1).
induction H1 as [x H1| x H1]; [ induction H1 as [x H1| x H1] | induction H1 ].
elim H1.
induction H1.
simpl in H0.
decompose sum H0.
discriminate H1.
discriminate H2.
simpl in H0.
decompose sum H0.
discriminate H1.
discriminate H2.
repeat rewrite (subFormulaEqual LNT).
simpl in |- *.
apply iffI.
apply impI.
apply eqTrans with (var 0).
apply eqTrans with (Plus (var 2) (Succ (var 4))).
apply eqPlus.
apply eqSym.
apply Axm.
left.
left.
right.
constructor.
apply eqRefl.
apply Axm.
right; constructor.
apply Axm; left; right; constructor.
apply impI.
apply eqTrans with (var 1).
apply eqTrans with (Plus (var 3) (Succ (var 4))).
fold (Succ (var 4)) in |- *.
fold (Plus (fol.var LNT 2) (Succ (var 4))) in |- *.
apply eqPlus.
apply Axm.
left.
left.
right.
constructor.
apply eqRefl.
apply Axm.
right; constructor.
apply eqSym.
apply Axm; left; right; constructor.
destruct H0.
exists x.
destruct H0.
split.
exists x0.
intros.
elim (H0 g H1).
intros.
destruct x.
assumption.
assert (In f (f::x)).
auto with *.
elim (H0 _ H2).
replace (LNN2LNT_formula (AxmEq5 LNN f)) with (AxmEq5 LNT f).
exists (nil (A:=Formula)).
split.
exists (EQ5 LNT f).
contradiction.
contradiction.
induction f; reflexivity.
Qed.

End Translate_Proof.

Lemma translateProof
     : forall (U : fol.System LNN) (V : System),
       ClosedSystem LNT V ->
       (forall f : fol.Formula LNN,
        mem (fol.Formula LNN) U f -> SysPrf V (LNN2LNT_formula f)) ->
       forall f : fol.Formula LNN,
       folProof.SysPrf LNN U f -> SysPrf V (LNN2LNT_formula f).
Proof.
intros.
destruct H1.
assert (forall f : fol.Formula LNN,
        mem (fol.Formula LNN) U f ->
        exists Axm : Formulas,
          ex
            (fun _ : Prf LNT Axm (LNN2LNT_formula f) =>
             forall g : Formula, In g Axm -> mem (fol.Formula LNT) V g) /\
          (forall v : nat,
           In v (freeVarListFormula LNT Axm) -> In v (freeVarFormula LNN f))).
intros.
destruct (H0 f0 H2).
exists x0.
split.
apply H3.
intros.
destruct H3.
clear x1.
induction x0.
elim H4.
destruct (in_app_or _ _ _ H4).
elim H with v a.
apply H3.
auto with *.
assumption.
apply IHx0.
firstorder.
apply H5.
destruct H1.
destruct (translatePrf U V H2 f x x0 H1).
exists x1.
tauto.
Qed.
