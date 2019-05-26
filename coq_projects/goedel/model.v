Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import ListExt.
Require Import folProof.
Require Import folProp.
Require Vector.
Require Import Peano_dec.
Require Import misc.
Require Import Arith.

Section Model_Theory.

Variable L : Language.

Fixpoint naryFunc (A : Set) (n : nat) {struct n} : Set :=
  match n with
  | O => A
  | S m => A -> naryFunc A m
  end.

Fixpoint naryRel (A : Set) (n : nat) {struct n} : Type :=
  match n with
  | O => Prop
  | S m => A -> naryRel A m
  end.

Record Model : Type := model
  {U : Set;
   func : forall f : Functions L, naryFunc U (arity L (inr _ f));
   rel : forall r : Relations L, naryRel U (arity L (inl _ r))}.

Variable M : Model.

Fixpoint interpTerm (value : nat -> U M) (t : Term L) {struct t} : 
 U M :=
  match t with
  | var v => value v
  | apply f ts => interpTerms _ (func M f) value ts
  end
 
 with interpTerms (m : nat) (f : naryFunc (U M) m) 
 (value : nat -> U M) (ts : Terms L m) {struct ts} : 
 U M :=
  match ts in (Terms _ n) return (naryFunc (U M) n -> U M) with
  | Tnil => fun f => f
  | Tcons m t ts => fun f => interpTerms m (f (interpTerm value t)) value ts
  end f.

Fixpoint interpRels (m : nat) (r : naryRel (U M) m) 
 (value : nat -> U M) (ts : Terms L m) {struct ts} : Prop :=
  match ts in (Terms _ n) return (naryRel (U M) n -> Prop) with
  | Tnil => fun r => r
  | Tcons m t ts => fun r => interpRels m (r (interpTerm value t)) value ts
  end r.

Definition updateValue (value : nat -> U M) (n : nat) 
  (v : U M) (x : nat) : U M :=
  match eq_nat_dec n x with
  | left _ => v
  | right _ => value x
  end.

Fixpoint interpFormula (value : nat -> U M) (f : Formula L) {struct f} :
 Prop :=
  match f with
  | equal t s => interpTerm value t = interpTerm value s
  | atomic r ts => interpRels _ (rel M r) value ts
  | impH A B => interpFormula value A -> interpFormula value B
  | notH A => interpFormula value A -> False
  | forallH v A => forall x : U M, interpFormula (updateValue value v x) A
  end.

Lemma freeVarInterpTerm :
 forall (v1 v2 : nat -> U M) (t : Term L),
 (forall x : nat, In x (freeVarTerm L t) -> v1 x = v2 x) ->
 interpTerm v1 t = interpTerm v2 t.
Proof.
intros v1 v2 t.
elim t using
 Term_Terms_ind
  with
    (P0 := fun (n : nat) (ts : Terms L n) =>
           forall f : naryFunc (U M) n,
           (forall x : nat, In x (freeVarTerms L n ts) -> v1 x = v2 x) ->
           interpTerms n f v1 ts = interpTerms n f v2 ts); 
 simpl in |- *; intros.
apply H.
auto.
apply H.
intros.
apply H0.
apply H1.
auto.
rewrite H.
apply H0.
intros.
apply H1.
unfold freeVarTerms in |- *.
apply in_or_app.
right.
apply H2.
intros.
apply H1.
unfold freeVarTerms in |- *.
apply in_or_app.
left.
apply H2.
Qed.

Lemma freeVarInterpRel :
 forall (v1 v2 : nat -> U M) (n : nat) (ts : Terms L n) (r : naryRel (U M) n),
 (forall x : nat, In x (freeVarTerms L n ts) -> v1 x = v2 x) ->
 interpRels n r v1 ts -> interpRels n r v2 ts.
Proof.
intros v1 v2 n ts r H.
induction ts as [| n t ts Hrects]; simpl in |- *.
auto.
rewrite (freeVarInterpTerm v1 v2).
apply Hrects.
intros.
apply H.
unfold freeVarTerms in |- *.
apply in_or_app.
right.
apply H0.
intros.
apply H.
unfold freeVarTerms in |- *.
apply in_or_app.
left.
apply H0.
Qed.

Lemma freeVarInterpFormula :
 forall (v1 v2 : nat -> U M) (g : Formula L),
 (forall x : nat, In x (freeVarFormula L g) -> v1 x = v2 x) ->
 interpFormula v1 g -> interpFormula v2 g.
Proof.
intros v1 v2 g.
generalize v1 v2.
clear v1 v2.
induction g as [t t0| r t| g1 Hrecg1 g0 Hrecg0| g Hrecg| n g Hrecg];
 simpl in |- *; intros v1 v2 H.
repeat rewrite (freeVarInterpTerm v1 v2).
auto.
intros.
apply H.
simpl in |- *.
auto with datatypes.
intros.
apply H.
simpl in |- *.
auto with datatypes.
intros.
apply (freeVarInterpRel v1 v2).
apply H.
apply H0.
assert (interpFormula v2 g1 -> interpFormula v1 g1).
apply Hrecg1.
intros.
symmetry  in |- *.
apply H.
simpl in |- *.
auto with datatypes.
assert (interpFormula v1 g0 -> interpFormula v2 g0).
apply Hrecg0.
intros.
apply H.
simpl in |- *.
auto with datatypes.
tauto.
intros.
apply H0.
apply Hrecg with v2.
intros.
symmetry  in |- *.
auto.
assumption.
intros.
apply Hrecg with (updateValue v1 n x).
intros.
unfold updateValue in |- *.
induction (eq_nat_dec n x0).
reflexivity.
apply H.
apply In_list_remove3; auto.
auto.
Qed.

Lemma subInterpTerm :
 forall (value : nat -> U M) (t : Term L) (v : nat) (s : Term L),
 interpTerm (updateValue value v (interpTerm value s)) t =
 interpTerm value (substituteTerm L t v s).
Proof.
intros.
elim t using
 Term_Terms_ind
  with
    (P0 := fun (n : nat) (ts : Terms L n) =>
           forall f : naryFunc (U M) n,
           interpTerms n f (updateValue value v (interpTerm value s)) ts =
           interpTerms n f value (substituteTerms L n ts v s)); 
 simpl in |- *; intros.
unfold updateValue in |- *.
induction (eq_nat_dec v n); reflexivity.
rewrite H.
reflexivity.
reflexivity.
rewrite H.
apply H0.
Qed.

Lemma subInterpRel :
 forall (value : nat -> U M) (n : nat) (ts : Terms L n) 
   (v : nat) (s : Term L) (r : naryRel (U M) n),
 interpRels n r (updateValue value v (interpTerm value s)) ts <->
 interpRels n r value (substituteTerms L n ts v s).
Proof.
intros.
induction ts as [| n t ts Hrects].
simpl in |- *.
tauto.
simpl in |- *.
rewrite <- subInterpTerm.
apply Hrects.
Qed.

Lemma subInterpFormula :
 forall (value : nat -> U M) (f : Formula L) (v : nat) (s : Term L),
 interpFormula (updateValue value v (interpTerm value s)) f <->
 interpFormula value (substituteFormula L f v s).
Proof.
intros value f.
generalize value.
clear value.
elim f using Formula_depth_ind2; simpl in |- *; intros.
repeat rewrite subInterpTerm.
tauto.
apply subInterpRel.
rewrite (subFormulaImp L).
simpl in |- *.
assert
 (interpFormula (updateValue value v (interpTerm value s)) f1 <->
  interpFormula value (substituteFormula L f1 v s)).
auto.
assert
 (interpFormula (updateValue value v (interpTerm value s)) f0 <->
  interpFormula value (substituteFormula L f0 v s)).
auto.
tauto.
rewrite (subFormulaNot L).
simpl in |- *.
assert
 (interpFormula (updateValue value v (interpTerm value s)) f0 <->
  interpFormula value (substituteFormula L f0 v s)).
auto.
tauto.
rewrite (subFormulaForall L).
induction (eq_nat_dec v v0).
rewrite a0.
simpl in |- *.
unfold updateValue in |- *.
split.
intros.
apply
 freeVarInterpFormula
  with
    (fun x0 : nat =>
     match eq_nat_dec v0 x0 with
     | left _ => x
     | right _ =>
         match eq_nat_dec v0 x0 with
         | left _ => interpTerm value s
         | right _ => value x0
         end
     end).
intros.
induction (eq_nat_dec v0 x0); reflexivity.
auto.
intros.
apply
 freeVarInterpFormula
  with
    (fun x0 : nat =>
     match eq_nat_dec v0 x0 with
     | left _ => x
     | right _ => value x0
     end).
intros.
induction (eq_nat_dec v0 x0); reflexivity.
auto.
induction (In_dec eq_nat_dec v (freeVarTerm L s)).
simpl in |- *.
set (nv := newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a)) in *.
assert (~ In nv (v0 :: freeVarTerm L s ++ freeVarFormula L a)).
unfold nv in |- *.
apply newVar1.
assert
 (forall (x : U M) (x0 : nat),
  In x0 (freeVarFormula L a) ->
  updateValue (updateValue value v0 (interpTerm value s)) v x x0 =
  updateValue
    (updateValue (updateValue value nv x) v0
       (interpTerm (updateValue value nv x) s)) v
    (interpTerm
       (updateValue (updateValue value nv x) v0
          (interpTerm (updateValue value nv x) s)) 
       (var L nv)) x0).
intros.
unfold updateValue in |- *.
simpl in |- *.
induction (eq_nat_dec v x0).
induction (eq_nat_dec v0 nv).
elim H0.
rewrite a2.
simpl in |- *.
auto.
induction (eq_nat_dec nv nv).
reflexivity.
elim b1.
reflexivity.
induction (eq_nat_dec v0 x0).
apply freeVarInterpTerm.
intros.
induction (eq_nat_dec nv x1).
elim H0.
rewrite a2.
simpl in |- *.
auto with datatypes.
reflexivity.
induction (eq_nat_dec nv x0).
elim H0.
rewrite a1.
auto with datatypes.
reflexivity.
assert
 ((forall x : U M,
   interpFormula
     (updateValue
        (updateValue (updateValue value nv x) v0
           (interpTerm (updateValue value nv x) s)) v
        (interpTerm
           (updateValue (updateValue value nv x) v0
              (interpTerm (updateValue value nv x) s)) 
           (var L nv))) a) <->
  (forall x : U M,
   interpFormula (updateValue value nv x)
     (substituteFormula L (substituteFormula L a v (var L nv)) v0 s))).
split.
assert
 (forall b : Formula L,
  lt_depth L b (forallH L v a) ->
  forall (value : nat -> U M) (v : nat) (s : Term L),
  interpFormula (updateValue value v (interpTerm value s)) b ->
  interpFormula value (substituteFormula L b v s)).
intros.
induction (H b0 H2 value0 v1 s0).
auto.
intros.
apply H2.
eapply eqDepth.
symmetry  in |- *.
apply subFormulaDepth.
apply depthForall.
apply H2.
apply depthForall.
apply H3.
intros.
assert
 (forall b : Formula L,
  lt_depth L b (forallH L v a) ->
  forall (value : nat -> U M) (v : nat) (s : Term L),
  interpFormula value (substituteFormula L b v s) ->
  interpFormula (updateValue value v (interpTerm value s)) b).
intros.
induction (H b0 H3 value0 v1 s0).
auto.
clear H.
intros.
apply H3.
apply depthForall.
apply H3.
eapply eqDepth.
symmetry  in |- *.
apply subFormulaDepth.
apply depthForall.
auto.
assert
 ((forall x : U M,
   interpFormula
     (updateValue (updateValue value v0 (interpTerm value s)) v x) a) <->
  (forall x : U M,
   interpFormula
     (updateValue
        (updateValue (updateValue value nv x) v0
           (interpTerm (updateValue value nv x) s)) v
        (interpTerm
           (updateValue (updateValue value nv x) v0
              (interpTerm (updateValue value nv x) s)) 
           (var L nv))) a)).
split.
intros.
apply
 freeVarInterpFormula
  with (updateValue (updateValue value v0 (interpTerm value s)) v x).
auto.
auto.
intros.
apply
 freeVarInterpFormula
  with
    (updateValue
       (updateValue (updateValue value nv x) v0
          (interpTerm (updateValue value nv x) s)) v
       (interpTerm
          (updateValue (updateValue value nv x) v0
             (interpTerm (updateValue value nv x) s)) 
          (var L nv))).
intros.
symmetry  in |- *.
auto.
auto.
tauto.
simpl in |- *.
assert
 (forall (x : U M) (x0 : nat),
  In x0 (freeVarFormula L a) ->
  updateValue (updateValue value v0 (interpTerm value s)) v x x0 =
  updateValue (updateValue value v x) v0
    (interpTerm (updateValue value v x) s) x0).
intros.
unfold updateValue in |- *.
induction (eq_nat_dec v x0).
induction (eq_nat_dec v0 x0).
elim b.
transitivity x0; auto.
reflexivity.
induction (eq_nat_dec v0 x0).
apply freeVarInterpTerm.
intros.
induction (eq_nat_dec v x1).
elim b0.
rewrite a1.
auto.
reflexivity.
reflexivity.
split.
intros.
assert
 (forall b : Formula L,
  lt_depth L b (forallH L v a) ->
  forall (value : nat -> U M) (v : nat) (s : Term L),
  interpFormula (updateValue value v (interpTerm value s)) b ->
  interpFormula value (substituteFormula L b v s)).
intros.
induction (H b1 H2 value0 v1 s0).
auto.
apply H2.
apply depthForall.
apply
 freeVarInterpFormula
  with (updateValue (updateValue value v0 (interpTerm value s)) v x).
apply (H0 x).
apply H1.
assert
 (forall b : Formula L,
  lt_depth L b (forallH L v a) ->
  forall (value : nat -> U M) (v : nat) (s : Term L),
  interpFormula value (substituteFormula L b v s) ->
  interpFormula (updateValue value v (interpTerm value s)) b).
intros.
induction (H b1 H1 value0 v1 s0).
auto.
intros.
apply
 freeVarInterpFormula
  with
    (updateValue (updateValue value v x) v0
       (interpTerm (updateValue value v x) s)).
intros.
symmetry  in |- *.
auto.
apply H1.
apply depthForall.
auto.
Qed.

Lemma subInterpFormula1 :
 forall (value : nat -> U M) (f : Formula L) (v : nat) (s : Term L),
 interpFormula (updateValue value v (interpTerm value s)) f ->
 interpFormula value (substituteFormula L f v s).
Proof.
intros.
induction (subInterpFormula value f v s).
auto.
Qed.

Lemma subInterpFormula2 :
 forall (value : nat -> U M) (f : Formula L) (v : nat) (s : Term L),
 interpFormula value (substituteFormula L f v s) ->
 interpFormula (updateValue value v (interpTerm value s)) f.
Proof.
intros.
induction (subInterpFormula value f v s).
auto.
Qed.

Fixpoint nnHelp (f : Formula L) : Formula L :=
  match f with
  | equal t s => equal L t s
  | atomic r ts => atomic L r ts
  | impH A B => impH L (nnHelp A) (nnHelp B)
  | notH A => notH L (nnHelp A)
  | forallH v A => forallH L v (notH L (notH L (nnHelp A)))
  end.

Definition nnTranslate (f : Formula L) : Formula L :=
  notH L (notH L (nnHelp f)).

Lemma freeVarNNHelp :
 forall f : Formula L, freeVarFormula L f = freeVarFormula L (nnHelp f).
Proof.
intros.
induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf];
 try reflexivity.
simpl in |- *.
rewrite Hrecf1.
rewrite Hrecf0.
reflexivity.
simpl in |- *.
assumption.
simpl in |- *.
rewrite Hrecf.
reflexivity.
Qed.

Lemma subNNHelp :
 forall (f : Formula L) (v : nat) (s : Term L),
 substituteFormula L (nnHelp f) v s = nnHelp (substituteFormula L f v s).
Proof.
intro f.
elim f using Formula_depth_ind2; intros; try reflexivity.
simpl in |- *.
rewrite subFormulaImp.
rewrite H.
rewrite H0.
rewrite subFormulaImp.
reflexivity.
simpl in |- *.
rewrite subFormulaNot.
rewrite H.
rewrite subFormulaNot.
reflexivity.
simpl in |- *.
do 2 rewrite subFormulaForall.
simpl in |- *.
induction (eq_nat_dec v v0).
simpl in |- *.
reflexivity.
induction (In_dec eq_nat_dec v (freeVarTerm L s)).
simpl in |- *.
repeat rewrite subFormulaNot.
repeat rewrite H.
rewrite <- freeVarNNHelp.
reflexivity.
eapply eqDepth.
symmetry  in |- *.
apply subFormulaDepth.
apply depthForall.
apply depthForall.
repeat rewrite subFormulaNot.
rewrite H.
simpl in |- *.
reflexivity.
apply depthForall.
Qed.

Section Consistent_Theory.

Variable T : System L.

Fixpoint interpTermsVector (value : nat -> U M) (n : nat) 
 (ts : Terms L n) {struct ts} : Vector.t (U M) n :=
  match ts in (Terms _ n) return (Vector.t (U M) n) with
  | Tnil => Vector.nil (U M)
  | Tcons m t ts =>
      Vector.cons (U M) (interpTerm value t) m (interpTermsVector value m ts)
  end.

Lemma preserveValue :
 forall value : nat -> U M,
 (forall f : Formula L,
  mem _ T f -> interpFormula value (nnTranslate f)) ->
 forall g : Formula L, SysPrf L T g -> interpFormula value (nnTranslate g).
Proof.
intros.
induction H0 as (x, H0).
induction H0 as (x0, H0).
cut (forall g : Formula L, In g x -> interpFormula value (nnTranslate g)).
clear H H0.
generalize value.
clear value.
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
   f]; intros; try (simpl in |- *; tauto).
apply H.
auto with datatypes.
assert (interpFormula value (nnTranslate A)).
auto with datatypes.
assert (interpFormula value (nnTranslate (impH L A B))).
auto with datatypes.
clear Hrecx0_1 Hrecx0_0.
simpl in H0.
simpl in H1.
simpl in |- *.
tauto.
simpl in |- *.
intros.
apply H0.
clear H0.
intros.
simpl in Hrecx0.
apply (Hrecx0 (updateValue value v x)).
intros.
simpl in H.
eapply H.
apply H1.
intros.
apply H2.
apply freeVarInterpFormula with value.
intros.
rewrite <- freeVarNNHelp in H4.
unfold updateValue in |- *.
induction (eq_nat_dec v x1).
elim n.
rewrite a.
clear n x0 Hrecx0 H.
induction Axm as [| a0 Axm HrecAxm].
apply H1.
simpl in |- *.
simpl in H1.
induction H1 as [H| H].
rewrite H.
auto with datatypes.
auto with datatypes.
reflexivity.
assumption.
assumption.
simpl in |- *.
intros.
apply H0.
intros.
elim H1 with (interpTerm value t).
intros.
apply H0.
intros.
rewrite <- subNNHelp.
apply subInterpFormula1.
auto.
simpl in |- *.
intros.
apply H0.
intros.
apply H2.
apply freeVarInterpFormula with value.
intros.
unfold updateValue in |- *.
induction (eq_nat_dec v x0).
elim n.
rewrite a.
rewrite freeVarNNHelp.
assumption.
reflexivity.
assumption.
simpl in |- *.
intros.
apply H0.
clear H0.
intros.
apply H0 with x.
intros.
apply H1 with x.
auto.
simpl in |- *.
auto.
simpl in |- *.
intros.
apply H0.
intros.
transitivity (value 1); auto.
simpl in |- *.
intros.
apply H0.
clear H H0.
unfold AxmEq4 in |- *.
cut
 (forall a b : Terms L (arity L (inl (Functions L) R)),
  interpTermsVector value _ a = interpTermsVector value _ b ->
  interpFormula value (nnHelp (iffH L (atomic L R a) (atomic L R b)))).
assert
 (forall A,
  (forall a b : Terms L (arity L (inl (Functions L) R)),
   interpTermsVector value (arity L (inl (Functions L) R)) a =
   interpTermsVector value (arity L (inl (Functions L) R)) b ->
   interpFormula value (nnHelp (A a b))) ->
  interpFormula value
    (nnHelp
       (nat_rec (fun _ : nat => Formula L)
          (prod_rec
             (fun
                _ : Terms L (arity L (inl (Functions L) R)) *
                    Terms L (arity L (inl (Functions L) R)) => 
              Formula L)
             (fun a b : Terms L (arity L (inl (Functions L) R)) => A a b)
             (nVars L (arity L (inl (Functions L) R))))
          (fun (n : nat) (Hrecn : Formula L) =>
           impH L (equal L (var L (n + n)) (var L (S (n + n)))) Hrecn)
          (arity L (inl (Functions L) R))))).
generalize (arity L (inl (Functions L) R)).
simple induction n.
simpl in |- *.
intros.
apply H.
reflexivity.
intros.
simpl in |- *.
induction (nVars L n0).
simpl in |- *.
simpl in H.
intros.
apply
 (H
    (fun x y : Terms L n0 =>
     A (Tcons L n0 (var L (n0 + n0)) x) (Tcons L n0 (var L (S (n0 + n0))) y))).
intros.
apply H0.
simpl in |- *.
rewrite H1.
rewrite H2.
reflexivity.
apply (H (fun a b => iffH L (atomic L R a) (atomic L R b))).
simpl in |- *.
generalize (rel M R).
generalize (arity L (inl (Functions L) R)).
intros.
induction a as [| n t a Hreca].
assert (b = Tnil L).
symmetry  in |- *.
apply nilTerms.
rewrite H1 in H0.
auto.
induction (consTerms L n b).
induction x as (a0, b0).
simpl in p.
rewrite <- p in H0.
rewrite <- p in H.
simpl in H.
inversion H.
simpl in H0.
rewrite H2 in H0.
apply (Hreca (n0 (interpTerm value a0)) b0).
apply (inj_right_pair2 _ eq_nat_dec _ _ _ _ H3).
auto.
simpl in |- *.
intros.
apply H0.
clear H H0.
unfold AxmEq5 in |- *.
cut
 (forall a b : Terms L (arity L (inr (Relations L) f)),
  interpTermsVector value _ a = interpTermsVector value _ b ->
  interpFormula value (nnHelp (equal L (apply L f a) (apply L f b)))).
assert
 (forall A,
  (forall a b : Terms L (arity L (inr (Relations L) f)),
   interpTermsVector value (arity L (inr (Relations L) f)) a =
   interpTermsVector value (arity L (inr (Relations L) f)) b ->
   interpFormula value (nnHelp (A a b))) ->
  interpFormula value
    (nnHelp
       (nat_rec (fun _ : nat => Formula L)
          (prod_rec
             (fun
                _ : Terms L (arity L (inr (Relations L) f)) *
                    Terms L (arity L (inr (Relations L) f)) => 
              Formula L)
             (fun a b : Terms L (arity L (inr (Relations L) f)) => A a b)
             (nVars L (arity L (inr (Relations L) f))))
          (fun (n : nat) (Hrecn : Formula L) =>
           impH L (equal L (var L (n + n)) (var L (S (n + n)))) Hrecn)
          (arity L (inr (Relations L) f))))).
generalize (arity L (inr (Relations L) f)).
simple induction n.
simpl in |- *.
intros.
auto.
intros.
simpl in |- *.
induction (nVars L n0).
simpl in |- *.
simpl in H.
intros.
apply
 (H
    (fun x y : Terms L n0 =>
     A (Tcons L n0 (var L (n0 + n0)) x) (Tcons L n0 (var L (S (n0 + n0))) y))).
intros.
apply H0.
simpl in |- *.
rewrite H1.
rewrite H2.
reflexivity.
apply (H (fun a b => equal L (apply L f a) (apply L f b))).
simpl in |- *.
generalize (func M f).
generalize (arity L (inr (Relations L) f)).
intros.
induction a as [| n t a Hreca].
assert (b = Tnil L).
symmetry  in |- *.
apply nilTerms.
rewrite H0.
reflexivity.
induction (consTerms L n b).
induction x as (a0, b0).
simpl in p.
rewrite <- p.
rewrite <- p in H.
simpl in H.
inversion H.
simpl in |- *.
rewrite H1.
apply Hreca.
apply (inj_right_pair2 _ eq_nat_dec _ _ _ _ H2).
auto.
Qed.

Lemma ModelConsistent :
 forall value : nat -> U M,
 (forall f : Formula L,
  mem _ T f -> interpFormula value (nnTranslate f)) ->
 Consistent L T.
Proof.
intros.
unfold Consistent in |- *.
exists (notH L (equal L (var  L 0) (var L 0))).
unfold not in |- *; intros.
assert
 (interpFormula value
    (nnTranslate (notH L (equal L (var L 0) (var L 0))))).
apply preserveValue.
assumption.
auto.
simpl in *.
auto.
Qed.

End Consistent_Theory.

End Model_Theory.
