Require Import Wf_nat.
Require Import Max.
Require Import Arith.
Require Import Coq.Lists.List.
Require Import ListExt.
Require Import Peano_dec.

Require Export fol.

Section Fol_Properties.

Variable L : Language.

Notation Formula := (Formula L) (only parsing).
Notation Formulas := (Formulas L) (only parsing).
Notation System := (System L) (only parsing).
Notation Term := (Term L) (only parsing).
Notation Terms := (Terms L) (only parsing).
Let var := var L.
Let apply := apply L.
Let equal := equal L.
Let atomic := atomic L.
Let impH := impH L.
Let notH := notH L.
Let forallH := forallH L.
Let lt_depth := lt_depth L.

Section Free_Variables.

Fixpoint freeVarTerm (s : fol.Term L) : list nat :=
  match s with
  | fol.var v => v :: nil
  | fol.apply f ts => freeVarTerms (arity L (inr _ f)) ts
  end
 
 with freeVarTerms (n : nat) (ss : fol.Terms L n) {struct ss} : 
 list nat :=
  match ss with
  | Tnil => nil (A:=nat)
  | Tcons m t ts => freeVarTerm t ++ freeVarTerms m ts
  end.

Lemma freeVarTermApply :
 forall (f : Functions L) (ts : fol.Terms L _),
 freeVarTerm (apply f ts) = freeVarTerms _ ts.
Proof.
intros.
reflexivity.
Qed.

Fixpoint freeVarFormula (A : fol.Formula L) : list nat :=
  match A with
  | fol.equal t s => freeVarTerm t ++ freeVarTerm s
  | fol.atomic r ts => freeVarTerms _ ts
  | fol.impH A B => freeVarFormula A ++ freeVarFormula B
  | fol.notH A => freeVarFormula A
  | fol.forallH v A => list_remove _ eq_nat_dec v (freeVarFormula A)
  end.

Definition ClosedSystem (T : fol.System L) :=
  forall (v : nat) (f : fol.Formula L),
  mem _ T f -> ~ In v (freeVarFormula f).

Definition closeList (l : list nat) (x : fol.Formula L) : 
  fol.Formula L :=
  list_rec (fun _ => fol.Formula L) x
    (fun (a : nat) _ (rec : fol.Formula L) => forallH a rec) l.

Definition close (x : fol.Formula L) : fol.Formula L :=
  closeList (no_dup _ eq_nat_dec (freeVarFormula x)) x.

Lemma freeVarClosedList1 :
 forall (l : list nat) (v : nat) (x : fol.Formula L),
 In v l -> ~ In v (freeVarFormula (closeList l x)).
intro.
induction l as [| a l Hrecl].
intros.
elim H.
intros.
induction H as [H| H].
simpl in |- *.
rewrite H.
unfold not in |- *; intros.
elim (In_list_remove2 _ _ _ _ _ H0).
auto.
simpl in |- *.
unfold not in |- *.
intros.
assert
 (In v
    (freeVarFormula
       (list_rec (fun _ => fol.Formula L) x
          (fun (a : nat) (_ : list nat) (rec : fol.Formula L) =>
           forallH a rec) l))).
eapply In_list_remove1.
apply H0.
apply (Hrecl _ _ H H1).
Qed.

Lemma freeVarClosedList2 :
 forall (l : list nat) (v : nat) (x : fol.Formula L),
 In v (freeVarFormula (closeList l x)) -> In v (freeVarFormula x).
intro.
induction l as [| a l Hrecl].
simpl in |- *.
auto.
simpl in |- *.
intros.
apply Hrecl.
eapply In_list_remove1.
apply H.
Qed.

Lemma freeVarClosed :
 forall (x : fol.Formula L) (v : nat), ~ In v (freeVarFormula (close x)).
intros.
unfold close in |- *.
induction (In_dec eq_nat_dec v (no_dup _ eq_nat_dec (freeVarFormula x))).
apply freeVarClosedList1.
auto.
unfold not in |- *; intros.
elim b.
apply no_dup1.
eapply freeVarClosedList2.
apply H.
Qed.

Fixpoint freeVarListFormula (l : fol.Formulas L) : 
 list nat :=
  match l with
  | nil => nil (A:=nat)
  | f :: l => freeVarFormula f ++ freeVarListFormula l
  end.

Lemma freeVarListFormulaApp :
 forall a b : fol.Formulas L,
 freeVarListFormula (a ++ b) = freeVarListFormula a ++ freeVarListFormula b.
Proof.
intros.
induction a as [| a a0 Hreca].
reflexivity.
simpl in |- *.
rewrite Hreca.
auto with datatypes.
Qed.

Lemma In_freeVarListFormula :
 forall (v : nat) (f : fol.Formula L) (F : fol.Formulas L),
 In v (freeVarFormula f) -> In f F -> In v (freeVarListFormula F).
Proof.
intros.
induction F as [| a F HrecF].
elim H0.
induction H0 as [H0| H0].
simpl in |- *.
apply in_or_app.
left.
rewrite H0.
auto.
simpl in |- *.
apply in_or_app.
auto.
Qed.

Lemma In_freeVarListFormulaE :
 forall (v : nat) (F : fol.Formulas L),
 In v (freeVarListFormula F) ->
 exists f : fol.Formula L, In v (freeVarFormula f) /\ In f F.
Proof.
intros.
induction F as [| a F HrecF].
elim H.
induction (in_app_or _ _ _ H).
exists a.
simpl in |- *; auto.
induction (HrecF H0).
exists x.
simpl in |- *; tauto.
Qed.

Definition In_freeVarSys (v : nat) (T : fol.System L) :=
  exists f : fol.Formula L, In v (freeVarFormula f) /\ mem _ T f.

Lemma notInFreeVarSys :
 forall x, ~ In_freeVarSys x (Ensembles.Empty_set (fol.Formula L)).
Proof.
intros.
unfold In_freeVarSys in |- *.
unfold not in |- *; intros.
induction H as (x0, (H, H0)).
induction H0.
Qed.

End Free_Variables.

Section Substitution.

Fixpoint substituteTerm (s : fol.Term L) (x : nat) 
 (t : fol.Term L) {struct s} : fol.Term L :=
  match s with
  | fol.var v =>
      match eq_nat_dec x v with
      | left _ => t
      | right _ => var v
      end
  | fol.apply f ts => apply f (substituteTerms _ ts x t)
  end
 
 with substituteTerms (n : nat) (ss : fol.Terms L n) 
 (x : nat) (t : fol.Term L) {struct ss} : fol.Terms L n :=
  match ss in (fol.Terms _ n0) return (fol.Terms L n0) with
  | Tnil => Tnil L
  | Tcons m s ts =>
      Tcons L m (substituteTerm s x t) (substituteTerms m ts x t)
  end.

Lemma subTermVar1 :
 forall (v : nat) (s : fol.Term L), substituteTerm (var v) v s = s.
Proof.
intros.
unfold var in |- *.
unfold substituteTerm in |- *.
induction (eq_nat_dec v v).
simpl in |- *.
reflexivity.
elim b.
reflexivity.
Qed.

Lemma subTermVar2 :
 forall (v x : nat) (s : fol.Term L),
 v <> x -> substituteTerm (var x) v s = var x.
Proof.
intros.
unfold var in |- *.
unfold substituteTerm in |- *.
induction (eq_nat_dec v x).
elim H.
assumption.
reflexivity.
Qed.

Lemma subTermFunction :
 forall (f : Functions L) (ts : fol.Terms L (arity L (inr _ f))) 
   (v : nat) (s : fol.Term L),
 substituteTerm (apply f ts) v s = apply f (substituteTerms _ ts v s).
Proof.
intros.
reflexivity.
Qed.

Definition newVar (l : list nat) : nat := fold_right max 0 (map S l).

Lemma newVar2 : forall (l : list nat) (n : nat), In n l -> n < newVar l.
Proof.
intro.
induction l as [| a l Hrecl].
intros.
elim H.
intros.
induction H as [H| H].
rewrite H.
unfold newVar in |- *.
simpl in |- *.
induction (fold_right max 0 (map S l)).
apply lt_n_Sn.
apply le_lt_n_Sm.
apply le_max_l.
unfold newVar in |- *.
unfold newVar in Hrecl.
simpl in |- *.
assert
 (fold_right max 0 (map S l) = 0 \/
  (exists n : nat, fold_right max 0 (map S l) = S n)).
induction (fold_right max 0 (map S l)).
auto.
right.
exists n0.
auto.
induction H0 as [H0| H0].
rewrite H0.
rewrite H0 in Hrecl.
elim (lt_n_O n).
apply Hrecl.
auto.
induction H0 as (x, H0).
rewrite H0.
rewrite H0 in Hrecl.
apply lt_le_trans with (S x).
apply Hrecl.
auto.
apply le_n_S.
apply le_max_r.
Qed.

Lemma newVar1 : forall l : list nat, ~ In (newVar l) l.
Proof.
unfold not in |- *; intros.
elim (lt_irrefl (newVar l)).
apply newVar2.
auto.
Qed.

Definition substituteFormulaImp (f : fol.Formula L)
  (frec : nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L f})
  (g : fol.Formula L)
  (grec : nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L g})
  (p : nat * fol.Term L) :
  {y : fol.Formula L | depth L y = depth L (impH f g)} :=
  match frec p with
  | exist f' prf1 =>
      match grec p with
      | exist g' prf2 =>
          exist
            (fun y : fol.Formula L =>
             depth L y = S (max (depth L f) (depth L g))) 
            (impH f' g')
            (eq_ind_r
               (fun n : nat =>
                S (max n (depth L g')) = S (max (depth L f) (depth L g)))
               (eq_ind_r
                  (fun n : nat =>
                   S (max (depth L f) n) = S (max (depth L f) (depth L g)))
                  (refl_equal (S (max (depth L f) (depth L g)))) prf2) prf1)
      end
  end.

Remark substituteFormulaImpNice :
 forall (f g : fol.Formula L)
   (z1 z2 : nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L f}),
 (forall q : nat * fol.Term L, z1 q = z2 q) ->
 forall
   z3 z4 : nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L g},
 (forall q : nat * fol.Term L, z3 q = z4 q) ->
 forall q : nat * fol.Term L,
 substituteFormulaImp f z1 g z3 q = substituteFormulaImp f z2 g z4 q.
Proof.
intros.
unfold substituteFormulaImp in |- *.
rewrite H.
rewrite H0.
reflexivity.
Qed.

Definition substituteFormulaNot (f : fol.Formula L)
  (frec : nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L f})
  (p : nat * fol.Term L) :
  {y : fol.Formula L | depth L y = depth L (notH f)} :=
  match frec p with
  | exist f' prf1 =>
      exist (fun y : fol.Formula L => depth L y = S (depth L f)) 
        (notH f')
        (eq_ind_r (fun n : nat => S n = S (depth L f))
           (refl_equal (S (depth L f))) prf1)
  end.

Remark substituteFormulaNotNice :
 forall (f : fol.Formula L)
   (z1 z2 : nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L f}),
 (forall q : nat * fol.Term L, z1 q = z2 q) ->
 forall q : nat * fol.Term L,
 substituteFormulaNot f z1 q = substituteFormulaNot f z2 q.
Proof.
intros.
unfold substituteFormulaNot in |- *.
rewrite H.
reflexivity.
Qed.

Definition substituteFormulaForall (n : nat) (f : fol.Formula L)
  (frec : forall b : fol.Formula L,
          lt_depth b (forallH n f) ->
          nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L b})
  (p : nat * fol.Term L) :
  {y : fol.Formula L | depth L y = depth L (forallH n f)} :=
  match p with
  | (v, s) =>
      match eq_nat_dec n v with
      | left _ =>
          exist (fun y : fol.Formula L => depth L y = S (depth L f))
            (forallH n f) (refl_equal (depth L (forallH n f)))
      | right _ =>
          match In_dec eq_nat_dec n (freeVarTerm s) with
          | left _ =>
              let nv := newVar (v :: freeVarTerm s ++ freeVarFormula f) in
              match frec f (depthForall L f n) (n, var nv) with
              | exist f' prf1 =>
                  match
                    frec f'
                      (eqDepth L f' f (forallH n f) 
                         (sym_eq prf1) (depthForall L f n)) p
                  with
                  | exist f'' prf2 =>
                      exist
                        (fun y : fol.Formula L => depth L y = S (depth L f))
                        (forallH nv f'')
                        (eq_ind_r (fun n : nat => S n = S (depth L f))
                           (refl_equal (S (depth L f))) 
                           (trans_eq prf2 prf1))
                  end
              end
          | right _ =>
              match frec f (depthForall L f n) p with
              | exist f' prf1 =>
                  exist (fun y : fol.Formula L => depth L y = S (depth L f))
                    (forallH n f')
                    (eq_ind_r (fun n : nat => S n = S (depth L f))
                       (refl_equal (S (depth L f))) prf1)
              end
          end
      end
  end.

Remark substituteFormulaForallNice :
 forall (v : nat) (a : fol.Formula L)
   (z1
    z2 : forall b : fol.Formula L,
         lt_depth b (forallH v a) ->
         nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L b}),
 (forall (b : fol.Formula L) (q : lt_depth b (forallH v a))
    (r : nat * fol.Term L), z1 b q r = z2 b q r) ->
 forall q : nat * fol.Term L,
 substituteFormulaForall v a z1 q = substituteFormulaForall v a z2 q.
Proof.
intros.
unfold substituteFormulaForall in |- *.
induction q as (a0, b).
induction (eq_nat_dec v a0); simpl in |- *.
reflexivity.
induction (In_dec eq_nat_dec v (freeVarTerm b)); simpl in |- *.
rewrite H.
induction
 (z2 a (depthForall L a v)
    (v, var (newVar (a0 :: freeVarTerm b ++ freeVarFormula a)))).
rewrite H.
reflexivity.
rewrite H.
reflexivity.
Qed.

Definition substituteFormulaHelp (f : fol.Formula L) 
  (v : nat) (s : fol.Term L) : {y : fol.Formula L | depth L y = depth L f}.
intros.
apply
 (Formula_depth_rec2 L
    (fun f : fol.Formula L =>
     nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L f})).
intros.
induction H as (a, b).
exists (equal (substituteTerm t a b) (substituteTerm t0 a b)).
auto.
intros.
induction H as (a, b).
exists (atomic r (substituteTerms _ t a b)).
auto.
exact substituteFormulaImp.
exact substituteFormulaNot.
exact substituteFormulaForall.
exact (v, s).
Defined.

Definition substituteFormula (f : fol.Formula L) (v : nat) 
  (s : fol.Term L) : fol.Formula L := proj1_sig (substituteFormulaHelp f v s).

Lemma subFormulaEqual :
 forall (t1 t2 : fol.Term L) (v : nat) (s : fol.Term L),
 substituteFormula (equal t1 t2) v s =
 equal (substituteTerm t1 v s) (substituteTerm t2 v s).
Proof.
auto.
Qed.

Lemma subFormulaRelation :
 forall (r : Relations L) (ts : fol.Terms L (arity L (inl _ r))) 
   (v : nat) (s : fol.Term L),
 substituteFormula (atomic r ts) v s =
 atomic r (substituteTerms (arity L (inl _ r)) ts v s).
Proof.
auto.
Qed.

Lemma subFormulaImp :
 forall (f1 f2 : fol.Formula L) (v : nat) (s : fol.Term L),
 substituteFormula (impH f1 f2) v s =
 impH (substituteFormula f1 v s) (substituteFormula f2 v s).
Proof.
intros.
unfold substituteFormula in |- *.
unfold substituteFormulaHelp in |- *.
rewrite
 (Formula_depth_rec2_imp L)
                            with
                            (Q := 
                              fun _ : fol.Formula L =>
                              (nat * fol.Term L)%type)
                           (P := 
                             fun x : fol.Formula L =>
                             {y : fol.Formula L | depth L y = depth L x}).
unfold substituteFormulaImp at 1 in |- *.
induction
 (Formula_depth_rec2 L
    (fun x : fol.Formula L =>
     nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L x})
    (fun (t t0 : fol.Term L) (H : nat * fol.Term L) =>
     prod_rec
       (fun _ : nat * fol.Term L =>
        {y : fol.Formula L | depth L y = depth L (fol.equal L t t0)})
       (fun (a : nat) (b : fol.Term L) =>
        exist
          (fun y : fol.Formula L => depth L y = depth L (fol.equal L t t0))
          (equal (substituteTerm t a b) (substituteTerm t0 a b))
          (refl_equal (depth L (fol.equal L t t0)))) H)
    (fun (r : Relations L) (t : fol.Terms L (arity L (inl (Functions L) r)))
       (H : nat * fol.Term L) =>
     prod_rec
       (fun _ : nat * fol.Term L =>
        {y : fol.Formula L | depth L y = depth L (fol.atomic L r t)})
       (fun (a : nat) (b : fol.Term L) =>
        exist
          (fun y : fol.Formula L => depth L y = depth L (fol.atomic L r t))
          (atomic r (substituteTerms (arity L (inl (Functions L) r)) t a b))
          (refl_equal (depth L (fol.atomic L r t)))) H) substituteFormulaImp
    substituteFormulaNot substituteFormulaForall f1 
    (v, s)).
induction
 (Formula_depth_rec2 L
    (fun x0 : fol.Formula L =>
     nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L x0})
    (fun (t t0 : fol.Term L) (H : nat * fol.Term L) =>
     prod_rec
       (fun _ : nat * fol.Term L =>
        {y : fol.Formula L | depth L y = depth L (fol.equal L t t0)})
       (fun (a : nat) (b : fol.Term L) =>
        exist
          (fun y : fol.Formula L => depth L y = depth L (fol.equal L t t0))
          (equal (substituteTerm t a b) (substituteTerm t0 a b))
          (refl_equal (depth L (fol.equal L t t0)))) H)
    (fun (r : Relations L) (t : fol.Terms L (arity L (inl (Functions L) r)))
       (H : nat * fol.Term L) =>
     prod_rec
       (fun _ : nat * fol.Term L =>
        {y : fol.Formula L | depth L y = depth L (fol.atomic L r t)})
       (fun (a : nat) (b : fol.Term L) =>
        exist
          (fun y : fol.Formula L => depth L y = depth L (fol.atomic L r t))
          (atomic r (substituteTerms (arity L (inl (Functions L) r)) t a b))
          (refl_equal (depth L (fol.atomic L r t)))) H) substituteFormulaImp
    substituteFormulaNot substituteFormulaForall f2 
    (v, s)).
simpl in |- *.
reflexivity.
apply substituteFormulaImpNice.
apply substituteFormulaNotNice.
apply substituteFormulaForallNice.
Qed.

Lemma subFormulaNot :
 forall (f : fol.Formula L) (v : nat) (s : fol.Term L),
 substituteFormula (notH f) v s = notH (substituteFormula f v s).
Proof.
intros.
unfold substituteFormula in |- *.
unfold substituteFormulaHelp in |- *.
rewrite
 (Formula_depth_rec2_not L)
                            with
                            (Q := 
                              fun _ : fol.Formula L =>
                              (nat * fol.Term L)%type)
                           (P := 
                             fun x : fol.Formula L =>
                             {y : fol.Formula L | depth L y = depth L x}).
unfold substituteFormulaNot at 1 in |- *.
induction
 (Formula_depth_rec2 L
    (fun x : fol.Formula L =>
     nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L x})
    (fun (t t0 : fol.Term L) (H : nat * fol.Term L) =>
     prod_rec
       (fun _ : nat * fol.Term L =>
        {y : fol.Formula L | depth L y = depth L (fol.equal L t t0)})
       (fun (a : nat) (b : fol.Term L) =>
        exist
          (fun y : fol.Formula L => depth L y = depth L (fol.equal L t t0))
          (equal (substituteTerm t a b) (substituteTerm t0 a b))
          (refl_equal (depth L (fol.equal L t t0)))) H)
    (fun (r : Relations L) (t : fol.Terms L (arity L (inl (Functions L) r)))
       (H : nat * fol.Term L) =>
     prod_rec
       (fun _ : nat * fol.Term L =>
        {y : fol.Formula L | depth L y = depth L (fol.atomic L r t)})
       (fun (a : nat) (b : fol.Term L) =>
        exist
          (fun y : fol.Formula L => depth L y = depth L (fol.atomic L r t))
          (atomic r (substituteTerms (arity L (inl (Functions L) r)) t a b))
          (refl_equal (depth L (fol.atomic L r t)))) H) substituteFormulaImp
    substituteFormulaNot substituteFormulaForall f 
    (v, s)).
simpl in |- *.
reflexivity.
apply substituteFormulaImpNice.
apply substituteFormulaNotNice.
apply substituteFormulaForallNice.
Qed.

Lemma subFormulaForall :
 forall (f : fol.Formula L) (x v : nat) (s : fol.Term L),
 let nv := newVar (v :: freeVarTerm s ++ freeVarFormula f) in
 substituteFormula (forallH x f) v s =
 match eq_nat_dec x v with
 | left _ => forallH x f
 | right _ =>
     match In_dec eq_nat_dec x (freeVarTerm s) with
     | right _ => forallH x (substituteFormula f v s)
     | left _ =>
         forallH nv (substituteFormula (substituteFormula f x (var nv)) v s)
     end
 end.
Proof.
intros.
unfold substituteFormula at 1 in |- *.
unfold substituteFormulaHelp in |- *.
rewrite
 (Formula_depth_rec2_forall L)
                               with
                               (Q := 
                                 fun _ : fol.Formula L =>
                                 (nat * fol.Term L)%type)
                              (P := 
                                fun x : fol.Formula L =>
                                {y : fol.Formula L | depth L y = depth L x}).
simpl in |- *.
induction (eq_nat_dec x v); simpl in |- *.
reflexivity.
induction (In_dec eq_nat_dec x (freeVarTerm s)); simpl in |- *.
fold nv in |- *.
unfold substituteFormula at 2 in |- *; unfold substituteFormulaHelp in |- *;
 simpl in |- *.
induction
 (Formula_depth_rec2 L
    (fun x0 : fol.Formula L =>
     nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L x0})
    (fun (t t0 : fol.Term L) (H : nat * fol.Term L) =>
     prod_rec
       (fun _ : nat * fol.Term L => {y : fol.Formula L | depth L y = 0})
       (fun (a0 : nat) (b0 : fol.Term L) =>
        exist (fun y : fol.Formula L => depth L y = 0)
          (equal (substituteTerm t a0 b0) (substituteTerm t0 a0 b0))
          (refl_equal 0)) H)
    (fun (r : Relations L) (t : fol.Terms L (arity L (inl (Functions L) r)))
       (H : nat * fol.Term L) =>
     prod_rec
       (fun _ : nat * fol.Term L => {y : fol.Formula L | depth L y = 0})
       (fun (a0 : nat) (b0 : fol.Term L) =>
        exist (fun y : fol.Formula L => depth L y = 0)
          (atomic r (substituteTerms (arity L (inl (Functions L) r)) t a0 b0))
          (refl_equal 0)) H) substituteFormulaImp substituteFormulaNot
    substituteFormulaForall f (x, var nv)).
unfold substituteFormula in |- *; unfold substituteFormulaHelp in |- *;
 simpl in |- *.
induction
 (Formula_depth_rec2 L
    (fun x1 : fol.Formula L =>
     nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L x1})
    (fun (t t0 : fol.Term L) (H : nat * fol.Term L) =>
     prod_rec
       (fun _ : nat * fol.Term L => {y : fol.Formula L | depth L y = 0})
       (fun (a0 : nat) (b0 : fol.Term L) =>
        exist (fun y : fol.Formula L => depth L y = 0)
          (equal (substituteTerm t a0 b0) (substituteTerm t0 a0 b0))
          (refl_equal 0)) H)
    (fun (r : Relations L) (t : fol.Terms L (arity L (inl (Functions L) r)))
       (H : nat * fol.Term L) =>
     prod_rec
       (fun _ : nat * fol.Term L => {y : fol.Formula L | depth L y = 0})
       (fun (a0 : nat) (b0 : fol.Term L) =>
        exist (fun y : fol.Formula L => depth L y = 0)
          (atomic r (substituteTerms (arity L (inl (Functions L) r)) t a0 b0))
          (refl_equal 0)) H) substituteFormulaImp substituteFormulaNot
    substituteFormulaForall x0 (v, s)).
simpl in |- *.
reflexivity.
unfold substituteFormula in |- *; unfold substituteFormulaHelp in |- *;
 simpl in |- *.
induction
 (Formula_depth_rec2 L
    (fun x0 : fol.Formula L =>
     nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L x0})
    (fun (t t0 : fol.Term L) (H : nat * fol.Term L) =>
     prod_rec
       (fun _ : nat * fol.Term L => {y : fol.Formula L | depth L y = 0})
       (fun (a : nat) (b1 : fol.Term L) =>
        exist (fun y : fol.Formula L => depth L y = 0)
          (equal (substituteTerm t a b1) (substituteTerm t0 a b1))
          (refl_equal 0)) H)
    (fun (r : Relations L) (t : fol.Terms L (arity L (inl (Functions L) r)))
       (H : nat * fol.Term L) =>
     prod_rec
       (fun _ : nat * fol.Term L => {y : fol.Formula L | depth L y = 0})
       (fun (a : nat) (b1 : fol.Term L) =>
        exist (fun y : fol.Formula L => depth L y = 0)
          (atomic r (substituteTerms (arity L (inl (Functions L) r)) t a b1))
          (refl_equal 0)) H) substituteFormulaImp substituteFormulaNot
    substituteFormulaForall f (v, s)).
simpl in |- *.
reflexivity.
apply substituteFormulaImpNice.
apply substituteFormulaNotNice.
apply substituteFormulaForallNice.
Qed.

Section Extensions.

Let orH := orH L.
Let andH := andH L.
Let existH := existH L.
Let iffH := iffH L.
Let ifThenElseH := ifThenElseH L.

Lemma subFormulaOr :
 forall (f1 f2 : fol.Formula L) (v : nat) (s : fol.Term L),
 substituteFormula (orH f1 f2) v s =
 orH (substituteFormula f1 v s) (substituteFormula f2 v s).
intros.
unfold orH, fol.orH in |- *.
rewrite subFormulaImp.
rewrite subFormulaNot.
reflexivity.
Qed.

Lemma subFormulaAnd :
 forall (f1 f2 : fol.Formula L) (v : nat) (s : fol.Term L),
 substituteFormula (andH f1 f2) v s =
 andH (substituteFormula f1 v s) (substituteFormula f2 v s).
intros.
unfold andH, fol.andH in |- *.
rewrite subFormulaNot.
rewrite subFormulaOr.
repeat rewrite subFormulaNot.
reflexivity.
Qed.

Lemma subFormulaExist :
 forall (f : fol.Formula L) (x v : nat) (s : fol.Term L),
 let nv := newVar (v :: freeVarTerm s ++ freeVarFormula f) in
 substituteFormula (existH x f) v s =
 match eq_nat_dec x v with
 | left _ => existH x f
 | right _ =>
     match In_dec eq_nat_dec x (freeVarTerm s) with
     | right _ => existH x (substituteFormula f v s)
     | left _ =>
         existH nv (substituteFormula (substituteFormula f x (var nv)) v s)
     end
 end.
Proof.
intros.
unfold existH, fol.existH in |- *.
rewrite subFormulaNot.
rewrite subFormulaForall.
induction (eq_nat_dec x v).
reflexivity.
induction (In_dec eq_nat_dec x (freeVarTerm s)).
repeat rewrite subFormulaNot.
reflexivity.
rewrite subFormulaNot.
reflexivity.
Qed.

Lemma subFormulaIff :
 forall (f1 f2 : fol.Formula L) (v : nat) (s : fol.Term L),
 substituteFormula (iffH f1 f2) v s =
 iffH (substituteFormula f1 v s) (substituteFormula f2 v s).
intros.
unfold iffH, fol.iffH in |- *.
rewrite subFormulaAnd.
repeat rewrite subFormulaImp.
reflexivity.
Qed.

Lemma subFormulaIfThenElse :
 forall (f1 f2 f3 : fol.Formula L) (v : nat) (s : fol.Term L),
 substituteFormula (ifThenElseH f1 f2 f3) v s =
 ifThenElseH (substituteFormula f1 v s) (substituteFormula f2 v s)
   (substituteFormula f3 v s).
intros.
unfold ifThenElseH, fol.ifThenElseH in |- *.
rewrite subFormulaAnd.
repeat rewrite subFormulaImp.
rewrite subFormulaNot.
reflexivity.
Qed.

End Extensions.

Lemma subFormulaDepth :
 forall (f : fol.Formula L) (v : nat) (s : fol.Term L),
 depth L (substituteFormula f v s) = depth L f.
Proof.
intros.
unfold substituteFormula in |- *.
induction (substituteFormulaHelp f v s).
simpl in |- *.
auto.
Qed.

Section Substitution_Properties.

Lemma subTermId :
 forall (t : fol.Term L) (v : nat), substituteTerm t v (var v) = t.
Proof.
intros.
elim t using
 Term_Terms_ind
  with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
           substituteTerms n ts v (var v) = ts).
simpl in |- *.
intros.
induction (eq_nat_dec v n).
rewrite a.
reflexivity.
reflexivity.
intros.
simpl in |- *.
rewrite H.
reflexivity.
simpl in |- *.
reflexivity.
intros.
simpl in |- *.
rewrite H.
rewrite H0.
reflexivity.
Qed.

Lemma subTermsId :
 forall (n : nat) (ts : fol.Terms L n) (v : nat),
 substituteTerms n ts v (var v) = ts.
Proof.
intros.
induction ts as [| n t ts Hrects].
reflexivity. 
simpl in |- *.
rewrite Hrects.
rewrite subTermId.
reflexivity.
Qed.

Lemma subFormulaId :
 forall (f : fol.Formula L) (v : nat), substituteFormula f v (var v) = f.
Proof.
intros.
induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf].
rewrite subFormulaEqual.
repeat rewrite subTermId.
reflexivity.
rewrite subFormulaRelation.
rewrite subTermsId.
reflexivity.
rewrite subFormulaImp.
rewrite Hrecf1.
rewrite Hrecf0.
reflexivity.
rewrite subFormulaNot.
rewrite Hrecf.
reflexivity.
rewrite subFormulaForall.
induction (eq_nat_dec n v).
reflexivity.
induction (In_dec eq_nat_dec n (freeVarTerm (var v))).
elim b.
simpl in a.
induction a as [H| H].
auto.
contradiction.
rewrite Hrecf.
reflexivity.
Qed.

Lemma subFormulaForall2 :
 forall (f : fol.Formula L) (x v : nat) (s : fol.Term L),
 exists nv : nat,
   ~ In nv (freeVarTerm s) /\
   nv <> v /\
   ~ In nv (list_remove _ eq_nat_dec x (freeVarFormula f)) /\
   substituteFormula (forallH x f) v s =
   match eq_nat_dec x v with
   | left _ => forallH x f
   | right _ =>
       forallH nv (substituteFormula (substituteFormula f x (var nv)) v s)
   end.
Proof.
intros.
rewrite subFormulaForall.
induction (eq_nat_dec x v). 
set
 (A1 :=
  v :: freeVarTerm s ++ list_remove nat eq_nat_dec x (freeVarFormula f)) 
 in *.
exists (newVar A1).
repeat split.
unfold not in |- *; intros; elim (newVar1 A1).
unfold A1 in |- *.
right.
apply in_or_app.
auto.
unfold not in |- *; intros; elim (newVar1 A1).
rewrite H.
left.
auto.
unfold not in |- *; intros; elim (newVar1 A1).
right.
apply in_or_app.
auto.
induction (In_dec eq_nat_dec x (freeVarTerm s)).
set (A1 := v :: freeVarTerm s ++ freeVarFormula f) in *.
exists (newVar A1).
repeat split.
unfold not in |- *; intros; elim (newVar1 A1).
right.
apply in_or_app.
auto.
unfold not in |- *; intros; elim (newVar1 A1).
rewrite H.
left.
auto.
unfold not in |- *; intros; elim (newVar1 A1).
right.
apply in_or_app.
right.
eapply In_list_remove1.
apply H.
exists x.
repeat split; auto.
unfold not in |- *; intros.
eapply (In_list_remove2 _ _ _ _ _ H).
auto.
rewrite subFormulaId.
auto.
Qed.

Let existH := existH L.

Lemma subFormulaExist2 :
 forall (f : fol.Formula L) (x v : nat) (s : fol.Term L),
 exists nv : nat,
   ~ In nv (freeVarTerm s) /\
   nv <> v /\
   ~ In nv (list_remove _ eq_nat_dec x (freeVarFormula f)) /\
   substituteFormula (existH x f) v s =
   match eq_nat_dec x v with
   | left _ => existH x f
   | right _ =>
       existH nv (substituteFormula (substituteFormula f x (var nv)) v s)
   end.
Proof.
intros.
rewrite subFormulaExist.
induction (eq_nat_dec x v). 
set
 (A1 :=
  v :: freeVarTerm s ++ list_remove nat eq_nat_dec x (freeVarFormula f)) 
 in *.
exists (newVar A1).
repeat split.
unfold not in |- *; intros; elim (newVar1 A1).
unfold A1 in |- *.
right.
apply in_or_app.
auto.
unfold not in |- *; intros; elim (newVar1 A1).
rewrite H.
left.
auto.
unfold not in |- *; intros; elim (newVar1 A1).
right.
apply in_or_app.
auto.
induction (In_dec eq_nat_dec x (freeVarTerm s)).
set (A1 := v :: freeVarTerm s ++ freeVarFormula f) in *.
exists (newVar A1).
repeat split.
unfold not in |- *; intros; elim (newVar1 A1).
right.
apply in_or_app.
auto.
unfold not in |- *; intros; elim (newVar1 A1).
rewrite H.
left.
auto.
unfold not in |- *; intros; elim (newVar1 A1).
right.
apply in_or_app.
right.
eapply In_list_remove1.
apply H.
exists x.
repeat split; auto.
unfold not in |- *; intros.
eapply (In_list_remove2 _ _ _ _ _ H).
auto.
rewrite subFormulaId.
auto.
Qed.

End Substitution_Properties.

End Substitution.
 
Definition Sentence (f:Formula) := (forall v : nat, ~ In v (freeVarFormula f)).

End Fol_Properties.
