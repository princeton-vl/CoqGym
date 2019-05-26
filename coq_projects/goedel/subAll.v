Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import Peano_dec.
Require Import ListExt.
Require Import Max.

Require Import folProof.
Require Import folLogic2.
Require Import folProp.
Require Import folReplace.
Require Import subProp.

Section SubAllVars.

Variable L : Language.
Notation Formula := (Formula L) (only parsing).
Notation Formulas := (Formulas L) (only parsing).
Notation System := (System L) (only parsing).
Notation Term := (Term L) (only parsing).
Notation Terms := (Terms L) (only parsing).
Notation var := (var L) (only parsing).
Notation apply := (apply L) (only parsing).
Notation equal := (equal L) (only parsing).
Notation atomic := (atomic L) (only parsing).
Notation impH := (impH L) (only parsing).
Notation notH := (notH L) (only parsing).
Notation forallH := (forallH L) (only parsing).
Notation iffH := (iffH L) (only parsing).
Notation SysPrf := (SysPrf L) (only parsing).

Fixpoint subAllTerm (t : fol.Term L) : (nat -> fol.Term L) -> fol.Term L :=
  match t return ((nat -> fol.Term L) -> fol.Term L) with
  | fol.var x => fun m => m x
  | fol.apply f ts => fun m => fol.apply L f (subAllTerms _ ts m)
  end
 
 with subAllTerms (n : nat) (ts : fol.Terms L n) {struct ts} :
 (nat -> fol.Term L) -> fol.Terms L n :=
  match
    ts in (fol.Terms _ n) return ((nat -> fol.Term L) -> fol.Terms L n)
  with
  | Tnil => fun _ => Tnil L
  | Tcons n' t ss =>
      fun m => Tcons L n' (subAllTerm t m) (subAllTerms _ ss m)
  end.

Lemma subAllTerm_ext :
 forall (t : fol.Term L) (m1 m2 : nat -> fol.Term L),
 (forall m : nat, In m (freeVarTerm L t) -> m1 m = m2 m) ->
 subAllTerm t m1 = subAllTerm t m2.
Proof.
intro.
elim t using
 Term_Terms_ind
  with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
           forall m1 m2 : nat -> fol.Term L,
           (forall m : nat, In m (freeVarTerms L n ts) -> m1 m = m2 m) ->
           subAllTerms n ts m1 = subAllTerms n ts m2); 
 simpl in |- *; intros.
apply H.
auto.
rewrite (H m1 m2).
auto.
intros.
apply H0.
auto.
auto.
rewrite (H m1 m2).
rewrite (H0 m1 m2).
auto.
intros.
apply H1.
unfold freeVarTerms in |- *.
fold (freeVarTerms L n t1) in |- *.
apply in_or_app.
auto.
intros.
apply H1.
unfold freeVarTerms in |- *.
fold (freeVarTerms L n t1) in |- *.
apply in_or_app.
auto.
Qed.

Lemma subAllTerms_ext :
 forall (n : nat) (ts : fol.Terms L n) (m1 m2 : nat -> fol.Term L),
 (forall m : nat, In m (freeVarTerms L n ts) -> m1 m = m2 m) ->
 subAllTerms n ts m1 = subAllTerms n ts m2.
Proof.
intros.
induction ts as [| n t ts Hrects].
auto.
simpl in |- *.
rewrite Hrects.
rewrite (subAllTerm_ext t m1 m2).
auto.
intros.
apply H.
unfold freeVarTerms in |- *.
fold (freeVarTerms L n ts) in |- *.
apply in_or_app.
auto.
intros.
apply H.
unfold freeVarTerms in |- *.
fold (freeVarTerms L n ts) in |- *.
apply in_or_app.
auto.
Qed.

Fixpoint freeVarMap (l : list nat) : (nat -> fol.Term L) -> list nat :=
  match l with
  | nil => fun _ => nil
  | a :: l' => fun m => freeVarTerm L (m a) ++ freeVarMap l' m
  end.

Lemma freeVarMap_ext :
 forall (l : list nat) (f1 f2 : nat -> fol.Term L),
 (forall m : nat, In m l -> f1 m = f2 m) -> freeVarMap l f1 = freeVarMap l f2.
Proof.
intros.
induction l as [| a l Hrecl].
auto.
simpl in |- *.
rewrite Hrecl.
rewrite H.
auto.
auto with datatypes.
intros.
apply H.
auto with datatypes.
Qed.

Lemma freeVarMap1 :
 forall (l : list nat) (m : nat -> fol.Term L) (v n : nat),
 In v (freeVarTerm L (m n)) -> In n l -> In v (freeVarMap l m).
Proof.
intros.
induction l as [| a l Hrecl].
elim H0.
induction H0 as [H0| H0].
simpl in |- *.
rewrite H0.
auto with datatypes.
simpl in |- *.
auto with datatypes.
Qed.

Fixpoint subAllFormula (f : Formula) (m : (nat -> Term)) {struct f} : Formula :=
  match f with
  | fol.equal t s => equal (subAllTerm t m) (subAllTerm s m)
  | fol.atomic r ts => atomic r (subAllTerms _ ts m)
  | fol.impH f g =>
      impH (subAllFormula f m) (subAllFormula g m)
  | fol.notH f => notH (subAllFormula f m)
  | fol.forallH n f =>
      let nv :=
        newVar
          (freeVarFormula L f ++
           freeVarMap (freeVarFormula L (forallH n f)) m) in
      forallH nv
        (subAllFormula f
           (fun v : nat =>
            match eq_nat_dec v n with
            | left _ => var nv
            | right _ => m v
            end))
  end.

Lemma subAllFormula_ext :
 forall (f : fol.Formula L) (m1 m2 : nat -> fol.Term L),
 (forall m : nat, In m (freeVarFormula L f) -> m1 m = m2 m) ->
 subAllFormula f m1 = subAllFormula f m2.
Proof.
intro.
induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf];
 simpl in |- *; intros.
rewrite (subAllTerm_ext t m1 m2).
rewrite (subAllTerm_ext t0 m1 m2).
reflexivity.
intros.
apply H.
apply in_or_app.
auto.
intros.
apply H.
apply in_or_app.
auto.
rewrite (subAllTerms_ext _ t m1 m2).
reflexivity.
apply H.
rewrite (Hrecf1 m1 m2).
rewrite (Hrecf0 m1 m2).
reflexivity.
intros.
apply H.
apply in_or_app.
auto.
intros.
apply H.
apply in_or_app.
auto.
rewrite (Hrecf m1 m2).
reflexivity.
apply H.
rewrite
 (freeVarMap_ext (list_remove nat eq_nat_dec n (freeVarFormula L f)) m1 m2)
 .
set
 (m1' :=
  fun v : nat =>
  match eq_nat_dec v n with
  | left _ =>
      fol.var L
        (newVar
           (freeVarFormula L f ++
            freeVarMap (list_remove nat eq_nat_dec n (freeVarFormula L f)) m2))
  | right _ => m1 v
  end) in *.
set
 (m2' :=
  fun v : nat =>
  match eq_nat_dec v n with
  | left _ =>
      fol.var L
        (newVar
           (freeVarFormula L f ++
            freeVarMap (list_remove nat eq_nat_dec n (freeVarFormula L f)) m2))
  | right _ => m2 v
  end) in *.
rewrite (Hrecf m1' m2').
reflexivity.
intros.
unfold m1', m2' in |- *; clear m1' m2'.
induction (eq_nat_dec m n).
reflexivity.
apply H.
apply In_list_remove3; auto.
intros.
apply H.
auto.
Qed.

Lemma freeVarSubAllTerm1 :
 forall (t : fol.Term L) (m : nat -> fol.Term L) (v : nat),
 In v (freeVarTerm L (subAllTerm t m)) ->
 exists n : nat, In n (freeVarTerm L t) /\ In v (freeVarTerm L (m n)).
Proof.
intros t m v.
elim t using
 Term_Terms_ind
  with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
           In v (freeVarTerms L n (subAllTerms n ts m)) ->
           exists a : nat,
             In a (freeVarTerms L n ts) /\ In v (freeVarTerm L (m a))).
intros.
simpl in H.
exists n.
simpl in |- *.
auto.
intros.
simpl in H0.
auto.
intros.
contradiction.
intros.
simpl in H1.
unfold freeVarTerms in H1.
fold (freeVarTerm L (subAllTerm t0 m)) in H1.
fold (freeVarTerms L n (subAllTerms n t1 m)) in H1.
induction (in_app_or _ _ _ H1).
induction (H H2).
exists x.
split.
unfold freeVarTerms in |- *.
fold (freeVarTerm L t0) in |- *.
fold (freeVarTerms L n t1) in |- *.
apply in_or_app.
tauto.
tauto.
induction (H0 H2).
exists x.
split.
unfold freeVarTerms in |- *.
fold (freeVarTerm L t0) in |- *.
fold (freeVarTerms L n t1) in |- *.
apply in_or_app.
tauto.
tauto.
Qed.

Lemma freeVarSubAllTerms1 :
 forall (n : nat) (ts : fol.Terms L n) (m : nat -> fol.Term L) (v : nat),
 In v (freeVarTerms L n (subAllTerms n ts m)) ->
 exists a : nat, In a (freeVarTerms L n ts) /\ In v (freeVarTerm L (m a)).
Proof.
intros n ts m v.
induction ts as [| n t ts Hrects].
intros.
contradiction.
intros.
simpl in H.
unfold freeVarTerms in H.
fold (freeVarTerm L (subAllTerm t m)) in H.
fold (freeVarTerms L n (subAllTerms n ts m)) in H.
induction (in_app_or _ _ _ H).
induction (freeVarSubAllTerm1 _ _ _ H0).
exists x.
split.
unfold freeVarTerms in |- *.
fold (freeVarTerm L t) in |- *.
fold (freeVarTerms L n ts) in |- *.
apply in_or_app.
tauto.
tauto.
induction (Hrects H0).
exists x.
split.
unfold freeVarTerms in |- *.
fold (freeVarTerm L t) in |- *.
fold (freeVarTerms L n ts) in |- *.
apply in_or_app.
tauto.
tauto.
Qed.

Lemma freeVarSubAllTerm2 :
 forall (t : fol.Term L) (m : nat -> fol.Term L) (v n : nat),
 In n (freeVarTerm L t) ->
 In v (freeVarTerm L (m n)) -> In v (freeVarTerm L (subAllTerm t m)).
Proof.
intros t m v n.
elim t using
 Term_Terms_ind
  with
    (P0 := fun (a : nat) (ts : fol.Terms L a) =>
           In n (freeVarTerms L a ts) ->
           In v (freeVarTerm L (m n)) ->
           In v (freeVarTerms L a (subAllTerms a ts m))); 
 intros.
simpl in |- *.
simpl in H.
induction H as [H| H].
rewrite H.
auto.
elim H.
auto.
auto.
simpl in |- *.
unfold freeVarTerms in |- *.
fold (freeVarTerm L (subAllTerm t0 m)) in |- *.
fold (freeVarTerms L n0 (subAllTerms n0 t1 m)) in |- *.
apply in_or_app.
unfold freeVarTerms in H1.
fold (freeVarTerm L t0) in H1.
fold (freeVarTerms L n0 t1) in H1.
induction (in_app_or _ _ _ H1).
auto.
auto.
Qed.

Lemma freeVarSubAllTerms2 :
 forall (a : nat) (ts : fol.Terms L a) (m : nat -> fol.Term L) (v n : nat),
 In n (freeVarTerms L a ts) ->
 In v (freeVarTerm L (m n)) -> In v (freeVarTerms L a (subAllTerms a ts m)).
Proof.
intros.
induction ts as [| n0 t ts Hrects].
auto.
simpl in |- *.
unfold freeVarTerms in |- *.
fold (freeVarTerm L (subAllTerm t m)) in |- *.
fold (freeVarTerms L n0 (subAllTerms n0 ts m)) in |- *.
apply in_or_app.
unfold freeVarTerms in H.
fold (freeVarTerm L t) in H.
fold (freeVarTerms L n0 ts) in H.
induction (in_app_or _ _ _ H).
left.
eapply freeVarSubAllTerm2.
apply H1.
auto.
auto.
Qed.

Lemma freeVarSubAllFormula1 :
 forall (f : fol.Formula L) (m : nat -> fol.Term L) (v : nat),
 In v (freeVarFormula L (subAllFormula f m)) ->
 exists n : nat, In n (freeVarFormula L f) /\ In v (freeVarTerm L (m n)).
Proof.
intro.
induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf];
 simpl in |- *; intros.
induction (in_app_or _ _ _ H);
 (induction (freeVarSubAllTerm1 _ _ _ H0); exists x; split;
   [ apply in_or_app; tauto | tauto ]).
apply freeVarSubAllTerms1.
apply H.
induction (in_app_or _ _ _ H);
 (induction (Hrecf1 _ _ H0) || induction (Hrecf0 _ _ H0); exists x; split;
   [ apply in_or_app; tauto | tauto ]).
apply Hrecf.
apply H.
set
 (nv :=
  newVar
    (freeVarFormula L f ++
     freeVarMap (list_remove nat eq_nat_dec n (freeVarFormula L f)) m)) 
 in *.
assert
 (In v
    (freeVarFormula L
       (subAllFormula f
          (fun v : nat =>
           match eq_nat_dec v n with
           | left _ => fol.var L nv
           | right _ => m v
           end)))).
eapply In_list_remove1.
apply H.
decompose record (Hrecf _ _ H0).
induction (eq_nat_dec x n).
elim (In_list_remove2 _ _ _ _ _ H).
induction H3 as [H1| H1].
auto.
contradiction.
exists x.
split.
apply In_list_remove3; auto.
auto.
Qed.

Lemma freeVarSubAllFormula2 :
 forall (f : fol.Formula L) (m : nat -> fol.Term L) (v n : nat),
 In n (freeVarFormula L f) ->
 In v (freeVarTerm L (m n)) -> In v (freeVarFormula L (subAllFormula f m)).
Proof.
intro.
induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf];
 simpl in |- *; intros.
apply in_or_app.
induction (in_app_or _ _ _ H).
left.
eapply freeVarSubAllTerm2.
apply H1.
apply H0.
right.
eapply freeVarSubAllTerm2.
apply H1.
apply H0.
eapply freeVarSubAllTerms2.
apply H.
apply H0.
apply in_or_app.
induction (in_app_or _ _ _ H).
left.
eapply Hrecf1.
apply H1.
apply H0.
right.
eapply Hrecf0.
apply H1.
apply H0.
eapply Hrecf.
apply H.
apply H0.
apply In_list_remove3.
eapply Hrecf.
eapply In_list_remove1.
apply H.
induction (eq_nat_dec n0 n).
elim (In_list_remove2 _ _ _ _ _ H).
auto.
auto.
unfold not in |- *; intros.
eapply
 (newVar1
    (freeVarFormula L f ++
     freeVarMap (list_remove nat eq_nat_dec n (freeVarFormula L f)) m))
 .
rewrite <- H1.
clear H1.
apply in_or_app.
right.
clear Hrecf.
induction (list_remove nat eq_nat_dec n (freeVarFormula L f)); simpl in |- *.
elim H.
apply in_or_app.
simpl in H.
induction H.
rewrite H.
auto.
auto.
Qed.

Lemma subSubAllTerm :
 forall (t : fol.Term L) (m : nat -> fol.Term L) (v : nat) (s : fol.Term L),
 substituteTerm L (subAllTerm t m) v s =
 subAllTerm t (fun n : nat => substituteTerm L (m n) v s).
Proof.
intros.
elim t using
 Term_Terms_ind
  with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
           substituteTerms L n (subAllTerms n ts m) v s =
           subAllTerms n ts (fun n : nat => substituteTerm L (m n) v s));
 intros.
simpl in |- *.
auto.
simpl in |- *.
rewrite H.
auto.
auto.
simpl in |- *.
rewrite H.
rewrite H0.
auto.
Qed.

Lemma subSubAllTerms :
 forall (n : nat) (ts : fol.Terms L n) (m : nat -> fol.Term L) 
   (v : nat) (s : fol.Term L),
 substituteTerms L n (subAllTerms n ts m) v s =
 subAllTerms n ts (fun n : nat => substituteTerm L (m n) v s).
Proof.
intros.
induction ts as [| n t ts Hrects].
auto.
simpl in |- *.
rewrite subSubAllTerm.
rewrite Hrects.
auto.
Qed.

Lemma subSubAllFormula :
 forall (T : fol.System L) (f : fol.Formula L) (m : nat -> fol.Term L)
   (v : nat) (s : fol.Term L),
 folProof.SysPrf L T
   (fol.iffH L (substituteFormula L (subAllFormula f m) v s)
      (subAllFormula f (fun n : nat => substituteTerm L (m n) v s))).
Proof.
intros T f.
generalize f T.
clear f T.
intro f.
elim f using Formula_depth_ind2; simpl in |- *; intros.
rewrite (subFormulaEqual L).
do 2 rewrite subSubAllTerm.
apply (iffRefl L).
rewrite (subFormulaRelation L).
rewrite subSubAllTerms.
apply (iffRefl L).
rewrite (subFormulaImp L).
apply (reduceImp L).
apply H.
apply H0.
rewrite (subFormulaNot L).
apply (reduceNot L).
apply H.
set
 (nv1 :=
  newVar
    (freeVarFormula L a ++
     freeVarMap (list_remove nat eq_nat_dec v (freeVarFormula L a)) m)) 
 in *.
set
 (nv2 :=
  newVar
    (freeVarFormula L a ++
     freeVarMap (list_remove nat eq_nat_dec v (freeVarFormula L a))
       (fun n : nat => substituteTerm L (m n) v0 s))) 
 in *.
apply (sysExtend L) with (Empty_set (fol.Formula L)).
unfold Included in |- *.
intros.
induction H0.
decompose record
 (subFormulaForall2 L
    (subAllFormula a
       (fun v1 : nat =>
        match eq_nat_dec v1 v with
        | left _ => fol.var L nv1
        | right _ => m v1
        end)) nv1 v0 s).
rewrite H4; clear H4.
induction (eq_nat_dec nv1 v0).
assert
 (forall n : nat,
  In n (freeVarFormula L (fol.forallH L v a)) ->
  substituteTerm L (m n) v0 s = m n).
intros.
apply subTermNil.
unfold not in |- *; intros.
elim
 (newVar1
    (freeVarFormula L a ++
     freeVarMap (list_remove nat eq_nat_dec v (freeVarFormula L a)) m)).
fold nv1 in |- *.
rewrite a0.
apply in_or_app.
right.
eapply freeVarMap1.
apply H4.
apply H3.
assert (nv1 = nv2).
unfold nv1, nv2 in |- *.
rewrite
 (freeVarMap_ext (list_remove nat eq_nat_dec v (freeVarFormula L a))
    (fun n : nat => substituteTerm L (m n) v0 s) m)
 .
reflexivity.
apply H3.
rewrite H4.
rewrite
 (subAllFormula_ext a
    (fun v1 : nat =>
     match eq_nat_dec v1 v with
     | left _ => fol.var L nv2
     | right _ => substituteTerm L (m v1) v0 s
     end)
    (fun v1 : nat =>
     match eq_nat_dec v1 v with
     | left _ => fol.var L nv2
     | right _ => m v1
     end)).
apply (iffRefl L).
intros.
induction (eq_nat_dec m0 v).
reflexivity.
apply H3.
simpl in |- *.
apply In_list_remove3; auto.
apply
 (iffTrans L)
  with
    (fol.forallH L x
       (substituteFormula L
          (subAllFormula a
             (fun v1 : nat =>
              match eq_nat_dec v1 v with
              | left _ => fol.var L x
              | right _ => m v1
              end)) v0 s)).
apply (reduceForall L).
apply (notInFreeVarSys L).
apply (reduceSub L).
apply (notInFreeVarSys L).
apply
 (iffTrans L)
  with
    (subAllFormula a
       (fun v1 : nat =>
        substituteTerm L
          match eq_nat_dec v1 v with
          | left _ => fol.var L nv1
          | right _ => m v1
          end nv1 (fol.var L x))).
fold (folProof.SysPrf L) in |- *.
fold (fol.iffH L) in |- *.
apply
 H
  with
    (b := a)
    (v := nv1)
    (s := fol.var L x)
    (m := fun v1 : nat =>
          match eq_nat_dec v1 v with
          | left _ => fol.var L nv1
          | right _ => m v1
          end).
apply depthForall.
rewrite
 (subAllFormula_ext a
    (fun v1 : nat =>
     match eq_nat_dec v1 v with
     | left _ => fol.var L x
     | right _ => m v1
     end)
    (fun v1 : nat =>
     substituteTerm L
       match eq_nat_dec v1 v with
       | left _ => fol.var L nv1
       | right _ => m v1
       end nv1 (fol.var L x))).
apply (iffRefl L).
intros.
induction (eq_nat_dec m0 v).
rewrite (subTermVar1 L).
reflexivity.
rewrite (subTermNil L).
reflexivity.
unfold not in |- *; intros.
elim
 (newVar1
    (freeVarFormula L a ++
     freeVarMap (list_remove nat eq_nat_dec v (freeVarFormula L a)) m)).
fold nv1 in |- *.
apply in_or_app.
right.
eapply freeVarMap1.
apply H4.
apply In_list_remove3; auto.
apply
 (iffTrans L)
  with
    (fol.forallH L x
       (subAllFormula a
          (fun v1 : nat =>
           match eq_nat_dec v1 v with
           | left _ => fol.var L x
           | right _ => substituteTerm L (m v1) v0 s
           end))).
apply (reduceForall L).
apply (notInFreeVarSys L).
eapply (iffTrans L). 
apply
 H
  with
    (b := a)
    (v := v0)
    (s := s)
    (m := fun v1 : nat =>
          match eq_nat_dec v1 v with
          | left _ => fol.var L x
          | right _ => m v1
          end).
apply depthForall.
rewrite
 (subAllFormula_ext a
    (fun v1 : nat =>
     match eq_nat_dec v1 v with
     | left _ => fol.var L x
     | right _ => substituteTerm L (m v1) v0 s
     end)
    (fun n : nat =>
     substituteTerm L
       match eq_nat_dec n v with
       | left _ => fol.var L x
       | right _ => m n
       end v0 s)).
apply (iffRefl L).
intros.
induction (eq_nat_dec m0 v).
rewrite subTermNil.
reflexivity.
simpl in |- *.
tauto.
reflexivity.
apply
 (iffTrans L)
  with
    (fol.forallH L nv2
       (substituteFormula L
          (subAllFormula a
             (fun v1 : nat =>
              match eq_nat_dec v1 v with
              | left _ => fol.var L x
              | right _ => substituteTerm L (m v1) v0 s
              end)) x (fol.var L nv2))).
apply (rebindForall L).
unfold not in |- *; intros.
simpl in H3.
assert
 (In nv2
    (freeVarFormula L
       (subAllFormula a
          (fun v1 : nat =>
           match eq_nat_dec v1 v with
           | left _ => fol.var L x
           | right _ => substituteTerm L (m v1) v0 s
           end)))).
eapply In_list_remove1.
apply H3.
decompose record (freeVarSubAllFormula1 _ _ _ H4).
induction (eq_nat_dec x0 v).
induction H7 as [H5| H5].
elim (In_list_remove2 _ _ _ _ _ H3).
auto.
contradiction.
elim
 (newVar1
    (freeVarFormula L a ++
     freeVarMap (list_remove nat eq_nat_dec v (freeVarFormula L a))
       (fun n : nat => substituteTerm L (m n) v0 s))).
fold nv2 in |- *.
apply in_or_app.
right.
eapply freeVarMap1.
apply H7.
apply In_list_remove3; auto.
apply (reduceForall L).
apply (notInFreeVarSys L).
eapply (iffTrans L).
apply H.
apply depthForall.
simpl in |- *.
rewrite
 (subAllFormula_ext a
    (fun v1 : nat =>
     match eq_nat_dec v1 v with
     | left _ => fol.var L nv2
     | right _ => substituteTerm L (m v1) v0 s
     end)
    (fun n : nat =>
     substituteTerm L
       match eq_nat_dec n v with
       | left _ => fol.var L x
       | right _ => substituteTerm L (m n) v0 s
       end x (fol.var L nv2))).
apply (iffRefl L).
intros.
induction (eq_nat_dec m0 v).
rewrite (subTermVar1 L).
reflexivity.
rewrite (subTermNil L (substituteTerm L (m m0) v0 s)).
reflexivity.
unfold not in |- *.
intros.
induction (freeVarSubTerm3 _ _ _ _ _ H4).
elim H2.
apply In_list_remove3.
eapply freeVarSubAllFormula2.
apply H3.
induction (eq_nat_dec m0 v).
elim b0; auto.
eapply In_list_remove1.
apply H5.
unfold not in |- *; intros.
elim
 (newVar1
    (freeVarFormula L a ++
     freeVarMap (list_remove nat eq_nat_dec v (freeVarFormula L a)) m)).
fold nv1 in |- *.
rewrite <- H6.
apply in_or_app.
right.
eapply freeVarMap1.
eapply In_list_remove1.
apply H5.
apply In_list_remove3; auto.
auto.
Qed.

Lemma subAllTermId :
 forall t : fol.Term L, subAllTerm t (fun x : nat => fol.var L x) = t.
Proof.
intros.
elim t using
 Term_Terms_ind
  with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
           subAllTerms n ts (fun x : nat => fol.var L x) = ts); 
 simpl in |- *; intros.
reflexivity.
rewrite H.
reflexivity.
reflexivity.
rewrite H.
rewrite H0.
reflexivity.
Qed.

Lemma subAllTermsId :
 forall (n : nat) (ts : fol.Terms L n),
 subAllTerms n ts (fun x : nat => fol.var L x) = ts.
Proof.
intros.
induction ts as [| n t ts Hrects].
reflexivity.
simpl in |- *.
rewrite Hrects.
rewrite subAllTermId.
reflexivity.
Qed.

Lemma subAllFormulaId :
 forall (T : fol.System L) (f : fol.Formula L),
 folProof.SysPrf L T
   (fol.iffH L (subAllFormula f (fun x : nat => fol.var L x)) f).
Proof.
intros.
apply (sysExtend L) with (Empty_set (fol.Formula L)).
unfold Included in |- *.
intros.
induction H.
induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf];
 simpl in |- *.
repeat rewrite subAllTermId.
apply (iffRefl L).
rewrite subAllTermsId.
apply (iffRefl L).
apply (reduceImp L).
apply Hrecf1.
apply Hrecf0.
apply (reduceNot L).
apply Hrecf.
set
 (nv :=
  newVar
    (freeVarFormula L f ++
     freeVarMap (list_remove nat eq_nat_dec n (freeVarFormula L f))
       (fun x : nat => fol.var L x))) in *.
apply
 (iffTrans L)
  with (fol.forallH L n (subAllFormula f (fun x : nat => fol.var L x))).
apply
 (iffTrans L)
  with
    (fol.forallH L nv
       (substituteFormula L (subAllFormula f (fun x : nat => fol.var L x)) n
          (fol.var L nv))).
replace
 (subAllFormula f
    (fun v : nat =>
     match eq_nat_dec v n with
     | left _ => fol.var L nv
     | right _ => fol.var L v
     end)) with
 (subAllFormula f
    (fun x : nat => substituteTerm L (fol.var L x) n (fol.var L nv))).
apply (reduceForall L).
apply (notInFreeVarSys L).
apply (iffSym L).
apply subSubAllFormula with (m := fun x : nat => fol.var L x).
apply subAllFormula_ext.
intros.
simpl in |- *.
induction (eq_nat_dec n m); induction (eq_nat_dec m n);
 reflexivity || (elimtype False; auto).
apply (iffSym L).
apply (rebindForall L).
unfold not in |- *; intros.
assert
 (In nv (freeVarFormula L (subAllFormula f (fun x : nat => fol.var L x)))).
eapply In_list_remove1.
apply H.
decompose record (freeVarSubAllFormula1 _ _ _ H0).
elim
 (newVar1
    (freeVarFormula L f ++
     freeVarMap (list_remove nat eq_nat_dec n (freeVarFormula L f))
       (fun x : nat => fol.var L x))).
fold nv in |- *.
apply in_or_app.
right.
eapply freeVarMap1.
apply H3.
apply In_list_remove3.
apply H2.
induction H3 as [H1| H1].
rewrite H1.
eapply In_list_remove2.
apply H.
contradiction.
apply (reduceForall L).
apply (notInFreeVarSys L).
apply Hrecf.
Qed.

Lemma subAllSubAllTerm :
 forall (t : fol.Term L) (m1 m2 : nat -> fol.Term L),
 subAllTerm (subAllTerm t m1) m2 =
 subAllTerm t (fun n : nat => subAllTerm (m1 n) m2).
Proof.
intro.
elim t using
 Term_Terms_ind
  with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
           forall m1 m2 : nat -> fol.Term L,
           subAllTerms n (subAllTerms n ts m1) m2 =
           subAllTerms n ts (fun n : nat => subAllTerm (m1 n) m2));
 simpl in |- *; intros.
reflexivity.
rewrite H.
reflexivity.
reflexivity.
rewrite H.
rewrite H0.
reflexivity.
Qed.

Lemma subAllSubAllTerms :
 forall (n : nat) (ts : fol.Terms L n) (m1 m2 : nat -> fol.Term L),
 subAllTerms n (subAllTerms n ts m1) m2 =
 subAllTerms n ts (fun n : nat => subAllTerm (m1 n) m2).
Proof.
intros.
induction ts as [| n t ts Hrects]; simpl in |- *.
reflexivity.
rewrite Hrects.
rewrite subAllSubAllTerm.
reflexivity.
Qed.

Lemma subAllSubAllFormula :
 forall (T : fol.System L) (f : fol.Formula L) (m1 m2 : nat -> fol.Term L),
 folProof.SysPrf L T
   (fol.iffH L (subAllFormula (subAllFormula f m1) m2)
      (subAllFormula f (fun n : nat => subAllTerm (m1 n) m2))).
Proof.
intros T f.
generalize f T.
clear f T.
intro f.
induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf]; intros.
simpl in |- *.
repeat rewrite subAllSubAllTerm.
apply (iffRefl L).
simpl in |- *.
rewrite subAllSubAllTerms.
apply (iffRefl L).
simpl in |- *.
apply (reduceImp L).
apply Hrecf1.
apply Hrecf0.
simpl in |- *.
apply (reduceNot L).
apply Hrecf.
simpl in |- *.
set
 (nv1 :=
  freeVarFormula L f ++
  freeVarMap (list_remove nat eq_nat_dec n (freeVarFormula L f)) m1) 
 in *.
set
 (nv2 :=
  freeVarFormula L f ++
  freeVarMap (list_remove nat eq_nat_dec n (freeVarFormula L f))
    (fun n0 : nat => subAllTerm (m1 n0) m2)) in *.
set
 (nv3 :=
  freeVarFormula L
    (subAllFormula f
       (fun v : nat =>
        match eq_nat_dec v n with
        | left _ => fol.var L (newVar nv1)
        | right _ => m1 v
        end)) ++
  freeVarMap
    (list_remove nat eq_nat_dec (newVar nv1)
       (freeVarFormula L
          (subAllFormula f
             (fun v : nat =>
              match eq_nat_dec v n with
              | left _ => fol.var L (newVar nv1)
              | right _ => m1 v
              end)))) m2) in *.
apply
 (iffTrans L)
  with
    (fol.forallH L (newVar nv3)
       (substituteFormula L
          (subAllFormula f
             (fun v : nat =>
              match eq_nat_dec v n with
              | left _ => fol.var L (newVar nv2)
              | right _ => subAllTerm (m1 v) m2
              end)) (newVar nv2) (fol.var L (newVar nv3)))).
eapply (sysExtend L) with (Empty_set (fol.Formula L)).
unfold Included in |- *.
intros.
induction H.
apply (reduceForall L).
apply (notInFreeVarSys L).
eapply (iffTrans L).
apply Hrecf.
set
 (a1 :=
  fun v : nat =>
  match eq_nat_dec v n with
  | left _ => fol.var L (newVar nv2)
  | right _ => subAllTerm (m1 v) m2
  end) in *.
simpl in |- *.
set
 (a2 :=
  fun n0 : nat =>
  subAllTerm
    match eq_nat_dec n0 n with
    | left _ => fol.var L (newVar nv1)
    | right _ => m1 n0
    end
    (fun v : nat =>
     match eq_nat_dec v (newVar nv1) with
     | left _ => fol.var L (newVar nv3)
     | right _ => m2 v
     end)) in *.
replace (subAllFormula f a2) with
 (subAllFormula f
    (fun x : nat =>
     substituteTerm L (a1 x) (newVar nv2) (fol.var L (newVar nv3)))).
apply (iffSym L).
apply subSubAllFormula.
apply subAllFormula_ext.
intros.
unfold a1, a2 in |- *.
induction (eq_nat_dec m n).
rewrite (subTermVar1 L).
simpl in |- *.
induction (eq_nat_dec (newVar nv1) (newVar nv1)).
reflexivity.
elim b.
auto.
rewrite subSubAllTerm.
apply subAllTerm_ext.
intros.
induction (eq_nat_dec m0 (newVar nv1)).
elim (newVar1 nv1).
rewrite <- a.
unfold nv1 in |- *.
apply in_or_app.
right.
eapply freeVarMap1.
apply H0.
apply In_list_remove3; auto.
apply (subTermNil L).
unfold not in |- *; intros.
elim (newVar1 nv2).
unfold nv2 at 2 in |- *.
apply in_or_app.
right.
eapply freeVarMap1.
eapply freeVarSubAllTerm2.
apply H0.
apply H1.
apply In_list_remove3; auto.
apply (iffSym L).
apply (rebindForall L).
unfold not in |- *; intros.
assert
 (In (newVar nv3)
    (freeVarFormula L
       (subAllFormula f
          (fun v : nat =>
           match eq_nat_dec v n with
           | left _ => fol.var L (newVar nv2)
           | right _ => subAllTerm (m1 v) m2
           end)))).
eapply In_list_remove1.
apply H.
decompose record (freeVarSubAllFormula1 _ _ _ H0).
induction (eq_nat_dec x n).
induction H3 as [H1| H1].
elim (In_list_remove2 _ _ _ _ _ H).
auto.
contradiction.
decompose record (freeVarSubAllTerm1 _ _ _ H3).
elim (newVar1 nv3).
unfold nv3 at 2 in |- *.
apply in_or_app.
right.
eapply freeVarMap1.
apply H5.
apply In_list_remove3.
eapply freeVarSubAllFormula2.
apply H2.
induction (eq_nat_dec x n).
elim b.
auto.
auto.
unfold not in |- *; intros.
elim (newVar1 nv1).
rewrite <- H1.
unfold nv1 in |- *.
apply in_or_app.
right.
eapply freeVarMap1.
apply H4.
apply In_list_remove3; auto.
Qed.

Section subAllCloseFrom.

Fixpoint closeFrom (a n : nat) (f : fol.Formula L) {struct n} :
 fol.Formula L :=
  match n with
  | O => f
  | S m => fol.forallH L (a + m) (closeFrom a m f)
  end.

Opaque le_lt_dec.

Lemma liftCloseFrom :
 forall (n : nat) (f : fol.Formula L) (T : fol.System L) (m : nat),
 (forall v : nat, In v (freeVarFormula L f) -> v < m) ->
 n <= m ->
 folProof.SysPrf L T (closeFrom 0 n f) ->
 folProof.SysPrf L T
   (closeFrom m n
      (subAllFormula f
         (fun x : nat =>
          match le_lt_dec n x with
          | left _ => fol.var L x
          | right _ => fol.var L (m + x)
          end))).
Proof.
intro.
induction n as [| n Hrecn]; simpl in |- *; intros.
replace
 (subAllFormula f
    (fun x : nat =>
     match le_lt_dec 0 x with
     | left _ => fol.var L x
     | right _ => fol.var L (m + x)
     end)) with (subAllFormula f (fun x : nat => fol.var L x)).
apply (impE L) with f.
apply (iffE2 L).
apply subAllFormulaId.
apply H1.
apply subAllFormula_ext.
intros.
induction (le_lt_dec 0 m0).
auto.
elim (lt_n_O _ b).
apply (impE L) with (fol.forallH L n (closeFrom 0 n f)).
apply sysExtend with (Empty_set (fol.Formula L)).
unfold Included in |- *.
intros.
induction H2.
apply (impI L).
apply (forallI L).
unfold not in |- *; intros.
induction H2 as (x, H2); induction H2 as (H2, H3).
induction H3 as [x H3| x H3]; [ induction H3 | induction H3 ].
assert
 (forall q : nat,
  n <= q ->
  m <= q -> ~ In q (freeVarFormula L (fol.forallH L n (closeFrom 0 n f)))).
clear H2 H1 T Hrecn.
induction n as [| n Hrecn]; simpl in |- *; unfold not in |- *; intros.
elim (lt_not_le q m).
apply H.
eapply In_list_remove1.
apply H3.
auto.
elim Hrecn with (q := q).
apply le_S_n.
apply le_S.
auto.
apply le_S_n.
apply le_S.
auto.
auto.
simpl in |- *.
eapply In_list_remove1.
apply H3.
apply H3 with (q := m + n).
apply le_plus_r.
apply le_plus_l.
apply H2.
apply
 (impE L)
  with
    (closeFrom m n
       (substituteFormula L
          (subAllFormula f
             (fun x : nat =>
              match le_lt_dec n x with
              | left _ => fol.var L x
              | right _ => fol.var L (m + x)
              end)) n (fol.var L (m + n)))).
apply sysWeaken.
clear H1 H T Hrecn.
cut
 (folProof.SysPrf L (Empty_set (fol.Formula L))
    (fol.impH L
       (substituteFormula L
          (subAllFormula f
             (fun x : nat =>
              match le_lt_dec n x with
              | left _ => fol.var L x
              | right _ => fol.var L (m + x)
              end)) n (fol.var L (m + n)))
       (subAllFormula f
          (fun x : nat =>
           match le_lt_dec (S n) x with
           | left _ => fol.var L x
           | right _ => fol.var L (m + x)
           end)))).
generalize
 (substituteFormula L
    (subAllFormula f
       (fun x : nat =>
        match le_lt_dec n x with
        | left _ => fol.var L x
        | right _ => fol.var L (m + x)
        end)) n (fol.var L (m + n))).
generalize
 (subAllFormula f
    (fun x : nat =>
     match le_lt_dec (S n) x with
     | left _ => fol.var L x
     | right _ => fol.var L (m + x)
     end)).
clear f H0.
intros.
induction n as [| n Hrecn]; simpl in |- *.
apply H.
apply (impI L).
apply (forallI L).
unfold not in |- *; intros.
induction H0 as (x, H0); induction H0 as (H0, H1).
induction H1 as [x H1| x H1]; [ induction H1 | induction H1 ].
elim (In_list_remove2 _ _ _ _ _ H0).
auto.
apply impE with (closeFrom m n f0).
apply sysWeaken.
apply Hrecn.
eapply forallSimp.
apply Axm; right; constructor.
replace
 (subAllFormula f
    (fun x : nat =>
     match le_lt_dec (S n) x with
     | left _ => fol.var L x
     | right _ => fol.var L (m + x)
     end)) with
 (subAllFormula f
    (fun x : nat =>
     substituteTerm L
       match le_lt_dec n x with
       | left _ => fol.var L x
       | right _ => fol.var L (m + x)
       end n (fol.var L (m + n)))).
apply (iffE1 L).
apply
 subSubAllFormula
  with
    (m := fun x : nat =>
          match le_lt_dec n x with
          | left _ => fol.var L x
          | right _ => fol.var L (m + x)
          end).
apply subAllFormula_ext.
intros.
induction (le_lt_dec n m0).
induction (le_lt_dec (S n) m0).
apply (subTermVar2 L).
unfold not in |- *; intros.
elim (lt_not_le m0 (S m0)).
apply lt_n_Sn.
rewrite H1 in a0.
auto.
induction (le_lt_or_eq _ _ a).
elim (lt_not_le m0 (S n)).
auto.
apply lt_n_Sm_le.
apply lt_n_S.
auto.
rewrite H1.
apply (subTermVar1 L).
induction (le_lt_dec (S n) m0).
elim (le_not_lt (S n) m0).
auto.
apply lt_S.
auto.
apply (subTermVar2 L).
unfold not in |- *; intros.
rewrite H1 in H0.
apply (le_not_lt (S (m + m0)) m).
apply H0.
apply le_lt_n_Sm.
apply le_plus_l.
assert
 (forall (f : fol.Formula L) (s r m p : nat),
  m < s ->
  s + r <= p ->
  folProof.SysPrf L (Empty_set (fol.Formula L))
    (fol.impH L (substituteFormula L (closeFrom s r f) m (fol.var L p))
       (closeFrom s r (substituteFormula L f m (fol.var L p))))).
clear H0 H H1 m T f n Hrecn.
intros f s n.
induction n as [| n Hrecn]; simpl in |- *; intros.
apply (impRefl L).
rewrite (subFormulaForall L).
induction (eq_nat_dec (s + n) m).
rewrite <- a in H.
elim (le_not_lt s (s + n)).
apply le_plus_l.
auto.
induction (In_dec eq_nat_dec (s + n) (freeVarTerm L (fol.var L p))).
induction a as [H1| H1].
rewrite <- plus_Snm_nSm in H0.
simpl in H0.
rewrite <- H1 in H0.
elim (le_not_lt (S p) p).
auto.
apply lt_n_Sn.
contradiction.
apply (impI L).
apply (forallI L).
unfold not in |- *; intros.
induction H1 as (x, H1); induction H1 as (H1, H2).
induction H2 as [x H2| x H2]; [ induction H2 | induction H2 ].
elim (In_list_remove2 _ _ _ _ _ H1).
auto.
apply impE with (substituteFormula L (closeFrom s n f) m (fol.var L p)).
apply sysWeaken.
apply Hrecn.
auto.
apply le_S_n.
apply le_S.
rewrite <- plus_Snm_nSm in H0.
auto.
eapply (forallSimp L).
apply Axm; right; constructor.
apply
 (impE L)
  with
    (substituteFormula L
       (closeFrom m n
          (subAllFormula f
             (fun x : nat =>
              match le_lt_dec n x with
              | left _ => fol.var L x
              | right _ => fol.var L (m + x)
              end))) n (fol.var L (m + n))).
apply sysWeaken.
apply H2.
apply lt_S_n.
apply le_lt_n_Sm.
auto.
auto.
apply (forallE L).
apply (impE L) with (fol.forallH L n (closeFrom 0 n f)).
apply sysExtend with (Empty_set (fol.Formula L)).
unfold Included in |- *.
intros.
induction H3.
apply (impI L).
apply (forallI L).
unfold not in |- *; intros.
induction H3 as (x, H3); induction H3 as (H3, H4).
induction H4 as [x H4| x H4]; [ induction H4 | induction H4 ].
elim (In_list_remove2 _ _ _ _ _ H3).
auto.
apply Hrecn.
apply H.
apply le_S_n.
apply le_S.
auto.
eapply (forallSimp L).
apply Axm; right; constructor.
apply Axm; right; constructor.
apply H1.
Qed.

Lemma subAllCloseFrom1 :
 forall (n m : nat) (map : nat -> fol.Term L) (f : fol.Formula L)
   (T : fol.System L),
 (forall v : nat,
  v < n -> forall w : nat, In w (freeVarTerm L (map (m + v))) -> w < m) ->
 folProof.SysPrf L T (closeFrom m n f) ->
 folProof.SysPrf L T
   (subAllFormula f
      (fun x : nat =>
       match le_lt_dec m x with
       | left _ =>
           match le_lt_dec (m + n) x with
           | left _ => fol.var L x
           | right _ => map x
           end
       | right _ => fol.var L x
       end)).
Proof.
intro.
induction n as [| n Hrecn]; simpl in |- *; intros.
replace
 (subAllFormula f
    (fun x : nat =>
     match le_lt_dec m x with
     | left _ =>
         match le_lt_dec (m + 0) x with
         | left _ => fol.var L x
         | right _ => map x
         end
     | right _ => fol.var L x
     end)) with (subAllFormula f (fun x : nat => fol.var L x)).
apply (impE L) with f.
apply (iffE2 L).
apply subAllFormulaId.
apply H0.
apply subAllFormula_ext.
intros.
rewrite <- plus_n_O.
induction (le_lt_dec m m0).
auto.
auto.
apply
 (impE L)
  with
    (substituteFormula L
       (subAllFormula f
          (fun x : nat =>
           match le_lt_dec m x with
           | left _ =>
               match le_lt_dec (m + n) x with
               | left _ => fol.var L x
               | right _ => map x
               end
           | right _ => fol.var L x
           end)) (m + n) (map (m + n))).
replace
 (subAllFormula f
    (fun x : nat =>
     match le_lt_dec m x with
     | left _ =>
         match le_lt_dec (m + S n) x with
         | left _ => fol.var L x
         | right _ => map x
         end
     | right _ => fol.var L x
     end)) with
 (subAllFormula f
    (fun x : nat =>
     substituteTerm L
       match le_lt_dec m x with
       | left _ =>
           match le_lt_dec (m + n) x with
           | left _ => fol.var L x
           | right _ => map x
           end
       | right _ => fol.var L x
       end (m + n) (map (m + n)))).
apply (iffE1 L).
apply
 subSubAllFormula
  with
    (m := fun x : nat =>
          match le_lt_dec m x with
          | left _ =>
              match le_lt_dec (m + n) x with
              | left _ => fol.var L x
              | right _ => map x
              end
          | right _ => fol.var L x
          end).
apply subAllFormula_ext.
intros.
induction (le_lt_dec m m0).
rewrite <- plus_Snm_nSm.
induction (le_lt_dec (S m + n) m0).
simpl in a0.
induction (le_lt_dec (m + n) m0).
apply (subTermVar2 L).
unfold not in |- *; intros.
rewrite H2 in a0.
apply (le_not_lt _ _ a0).
apply lt_n_Sn.
elim (le_not_lt (S (m + n)) (m + n)).
eapply le_trans.
apply a0.
apply lt_le_weak.
auto.
apply lt_n_Sn.
induction (le_lt_dec (m + n) m0).
replace (m + n) with m0.
apply (subTermVar1 L).
simpl in b.
induction (le_lt_or_eq _ _ a0).
elim (lt_not_le _ _ H2).
apply lt_n_Sm_le.
auto.
auto.
apply (subTermNil L).
unfold not in |- *; intros.
assert (m + (m0 - m) = m0).
apply le_plus_minus_r.
auto.
elim (lt_not_le (m + n) m).
apply H with (m0 - m).
apply plus_lt_reg_l with m.
rewrite H3.
rewrite <- plus_Snm_nSm.
apply b.
rewrite H3.
apply H2.
apply le_plus_l.
apply (subTermVar2 L).
unfold not in |- *; intros.
rewrite <- H2 in b.
elim (lt_not_le _ _ b).
apply le_plus_l.
apply (forallE L).
apply (impE L) with (fol.forallH L (m + n) (closeFrom m n f)).
apply sysExtend with (Empty_set (fol.Formula L)).
unfold Included in |- *.
intros.
induction H1.
apply (impI L).
apply (forallI L).
unfold not in |- *; intros.
induction H1 as (x, H1); induction H1 as (H1, H2).
induction H2 as [x H2| x H2]; [ induction H2 | induction H2 ].
elim (In_list_remove2 _ _ _ _ _ H1).
auto.
apply Hrecn.
intros.
eapply H.
apply lt_S.
apply H1.
auto.
eapply (forallSimp L).
apply Axm; right; constructor.
apply H0.
Qed.

Lemma subAllCloseFrom :
 forall (n : nat) (m : nat -> fol.Term L) (f : fol.Formula L)
   (T : fol.System L),
 folProof.SysPrf L T (closeFrom 0 n f) ->
 folProof.SysPrf L T
   (subAllFormula f
      (fun x : nat =>
       match le_lt_dec n x with
       | left _ => fol.var L x
       | right _ => m x
       end)).
Proof.
intros.
assert
 (exists r : nat,
    (forall v : nat, v < n -> newVar (freeVarTerm L (m v)) <= r)).
clear H T f.
induction n as [| n Hrecn].
exists 0.
intros.
elim (lt_n_O _ H).
induction Hrecn as (x, H).
exists (max (newVar (freeVarTerm L (m n))) x).
intros.
assert (v <= n).
apply lt_n_Sm_le.
auto.
induction (le_lt_or_eq _ _ H1).
apply le_trans with x.
apply H; auto.
apply le_max_r.
rewrite H2.
apply le_max_l.
induction H0 as (x, H0).
set (r := max (max n (newVar (freeVarFormula L f))) x) in *.
set
 (f' :=
  subAllFormula f
    (fun x : nat =>
     match le_lt_dec n x with
     | left _ => fol.var L x
     | right _ => fol.var L (r + x)
     end)) in *.
set (m' := fun x : nat => m (x - r)) in *.
apply
 (impE L)
  with
    (subAllFormula f'
       (fun x : nat =>
        match le_lt_dec r x with
        | left _ =>
            match le_lt_dec (r + n) x with
            | left _ => fol.var L x
            | right _ => m' x
            end
        | right _ => fol.var L x
        end)).
replace
 (subAllFormula f
    (fun x0 : nat =>
     match le_lt_dec n x0 with
     | left _ => fol.var L x0
     | right _ => m x0
     end)) with
 (subAllFormula f
    (fun x : nat =>
     subAllTerm
       match le_lt_dec n x with
       | left _ => fol.var L x
       | right _ => fol.var L (r + x)
       end
       (fun x0 : nat =>
        match le_lt_dec r x0 with
        | left _ =>
            match le_lt_dec (r + n) x0 with
            | left _ => fol.var L x0
            | right _ => m' x0
            end
        | right _ => fol.var L x0
        end))).
apply (iffE1 L).
unfold f' in |- *.
apply
 subAllSubAllFormula
  with
    (m1 := fun x0 : nat =>
           match le_lt_dec n x0 with
           | left _ => fol.var L x0
           | right _ => fol.var L (r + x0)
           end)
    (m2 := fun x0 : nat =>
           match le_lt_dec r x0 with
           | left _ =>
               match le_lt_dec (r + n) x0 with
               | left _ => fol.var L x0
               | right _ => m' x0
               end
           | right _ => fol.var L x0
           end).
unfold m' in |- *.
apply subAllFormula_ext; intros.
induction (le_lt_dec n m0).
simpl in |- *.
induction (le_lt_dec r m0).
elim (le_not_lt _ _ a0).
apply lt_le_trans with (newVar (freeVarFormula L f)).
apply newVar2.
auto.
unfold r in |- *.
eapply le_trans.
apply le_max_r.
apply le_max_l.
auto.
simpl in |- *.
induction (le_lt_dec r (r + m0)).
induction (le_lt_dec (r + n) (r + m0)).
elim (lt_not_le _ _ b).
eapply (fun p n m : nat => plus_le_reg_l n m p).
apply a0.
rewrite minus_plus.
auto.
elim (lt_not_le _ _ b0).
apply le_plus_l.
apply subAllCloseFrom1.
intros.
apply lt_le_trans with (newVar (freeVarTerm L (m v))).
apply newVar2.
unfold m' in H2.
rewrite minus_plus in H2.
auto.
apply le_trans with x.
apply H0.
auto.
unfold r in |- *.
apply le_max_r.
unfold f' in |- *.
clear f'.
apply liftCloseFrom.
intros.
apply lt_le_trans with (newVar (freeVarFormula L f)).
apply newVar2.
auto.
unfold r in |- *.
eapply le_trans.
apply le_max_r.
apply le_max_l.
unfold r in |- *.
eapply le_trans.
apply le_max_l.
apply le_max_l.
apply H.
Qed.

Lemma reduceSubAll :
 forall (T : fol.System L) (map : nat -> fol.Term L) (A B : fol.Formula L),
 (forall v : nat, ~ In_freeVarSys L v T) ->
 folProof.SysPrf L T (fol.iffH L A B) ->
 folProof.SysPrf L T (fol.iffH L (subAllFormula A map) (subAllFormula B map)).
Proof.
assert
 (forall (T : fol.System L) (map : nat -> fol.Term L) (A B : fol.Formula L),
  (forall v : nat, ~ In_freeVarSys L v T) ->
  folProof.SysPrf L T (fol.iffH L A B) ->
  folProof.SysPrf L T
    (fol.impH L (subAllFormula A map) (subAllFormula B map))).
intros.
replace (fol.impH L (subAllFormula A map) (subAllFormula B map)) with
 (subAllFormula (fol.impH L A B) map).
set (n := newVar (freeVarFormula L (fol.impH L A B))) in *.
replace (subAllFormula (fol.impH L A B) map) with
 (subAllFormula (fol.impH L A B)
    (fun x : nat =>
     match le_lt_dec n x with
     | left _ => fol.var L x
     | right _ => map x
     end)).
apply subAllCloseFrom.
induction n as [| n Hrecn].
simpl in |- *.
apply (iffE1 L).
auto.
simpl in |- *.
apply (forallI L).
auto.
auto.
apply subAllFormula_ext.
intros.
induction (le_lt_dec n m).
elim (le_not_lt _ _ a).
unfold n in |- *.
apply newVar2.
auto.
auto.
reflexivity.
intros.
apply (iffI L).
apply H; auto.
apply H.
auto.
apply (iffSym L).
auto.
Qed.

End subAllCloseFrom.

Lemma subToSubAll :
 forall (T : fol.System L) (A : fol.Formula L) (v : nat) (s : fol.Term L),
 folProof.SysPrf L T
   (fol.iffH L (substituteFormula L A v s)
      (subAllFormula A
         (fun x : nat =>
          match eq_nat_dec v x with
          | left _ => s
          | right _ => fol.var L x
          end))).
Proof.
intros.
apply
 (iffTrans L)
  with
    (substituteFormula L (subAllFormula A (fun x : nat => fol.var L x)) v s).
apply sysExtend with (Empty_set (fol.Formula L)).
intro.
intros.
induction H.
apply (reduceSub L).
unfold not in |- *; intros.
induction H as (x, H); induction H as (H, H0).
induction H0.
apply (iffSym L).
apply subAllFormulaId.
eapply (iffTrans L).
apply subSubAllFormula.
replace
 (subAllFormula A
    (fun x : nat =>
     match eq_nat_dec v x with
     | left _ => s
     | right _ => fol.var L x
     end)) with
 (subAllFormula A
    (fun n : nat => substituteTerm L ((fun x : nat => fol.var L x) n) v s)).
apply (iffRefl L).
apply subAllFormula_ext.
intros.
simpl in |- *.
reflexivity.
Qed.

Lemma subAllSubFormula :
 forall (T : fol.System L) (A : fol.Formula L) (v : nat) 
   (s : fol.Term L) (map : nat -> fol.Term L),
 folProof.SysPrf L T
   (fol.iffH L (subAllFormula (substituteFormula L A v s) map)
      (subAllFormula A
         (fun x : nat =>
          match eq_nat_dec v x with
          | left _ => subAllTerm s map
          | right _ => map x
          end))).
Proof.
intros.
apply (sysExtend L) with (Empty_set (fol.Formula L)).
intro.
intros.
induction H.
eapply (iffTrans L).
apply reduceSubAll.
unfold not in |- *; intros.
induction H as (x, H); induction H as (H, H0).
induction H0.
apply subToSubAll.
eapply (iffTrans L).
apply subAllSubAllFormula.
replace
 (subAllFormula A
    (fun x : nat =>
     match eq_nat_dec v x with
     | left _ => subAllTerm s map
     | right _ => map x
     end)) with
 (subAllFormula A
    (fun n : nat =>
     subAllTerm
       ((fun x : nat =>
         match eq_nat_dec v x with
         | left _ => s
         | right _ => fol.var L x
         end) n) map)).
apply (iffRefl L).
apply subAllFormula_ext.
intros.
induction (eq_nat_dec v m).
auto.
auto.
Qed.

End SubAllVars.
