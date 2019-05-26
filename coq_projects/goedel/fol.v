(* Author: Russell O'Connor *)
(* This file is Public Domain *)

Require Import Coq.Lists.List.
Require Import Ensembles.
Require Import Peano_dec.
Require Import Eqdep_dec.
Require Import Arith.
Require Import Compare_dec.
Require Import Max.
Require Import misc.

Unset Standard Proposition Elimination Names.

Record Language : Type := language
  {Relations : Set; Functions : Set; arity : Relations + Functions -> nat}.

Section First_Order_Logic.

Variable L : Language.

Inductive Term : Set :=
  | var : nat -> Term
  | apply : forall f : Functions L, Terms (arity L (inr _ f)) -> Term
with Terms : nat -> Set :=
  | Tnil : Terms 0
  | Tcons : forall n : nat, Term -> Terms n -> Terms (S n).
 
Scheme Term_Terms_ind := Induction for Term Sort Prop
  with Terms_Term_ind := Induction for Terms Sort Prop.

Scheme Term_Terms_rec := Minimality for Term Sort Set
  with Terms_Term_rec := Minimality for Terms Sort Set.

Scheme Term_Terms_rec_full := Induction for Term
  Sort Set
  with Terms_Term_rec_full := Induction for Terms Sort Set.

Inductive Formula : Set :=
  | equal : Term -> Term -> Formula
  | atomic : forall r : Relations L, Terms (arity L (inl _ r)) -> Formula
  | impH : Formula -> Formula -> Formula
  | notH : Formula -> Formula
  | forallH : nat -> Formula -> Formula.

Definition Formulas := list Formula.

Definition System := Ensemble Formula.
Definition mem := Ensembles.In.

Section Fol_Full.

Definition orH (A B : Formula) := impH (notH A) B.

Definition andH (A B : Formula) := notH (orH (notH A) (notH B)).

Definition iffH (A B : Formula) := andH (impH A B) (impH B A).

Definition existH (x : nat) (A : Formula) := notH (forallH x (notH A)).

End Fol_Full.

Section Fol_Plus.

Definition ifThenElseH (A B C : Formula) := andH (impH A B) (impH (notH A) C).

End Fol_Plus.

Section Formula_Decideability.

Definition language_decideable :=
  ((forall x y : Functions L, {x = y} + {x <> y}) *
   (forall x y : Relations L, {x = y} + {x <> y}))%type.

Hypothesis language_dec : language_decideable.

Let nilTermsHelp : forall n : nat, n = 0 -> Terms n.
intros.
induction n as [| n Hrecn].
apply Tnil.
discriminate H.
Defined.

Lemma nilTerms : forall x : Terms 0, Tnil = x.
Proof.
assert (forall (n : nat) (p : n = 0) (x : Terms n), nilTermsHelp n p = x).
intros.
induction x as [| n t x Hrecx].
reflexivity.
discriminate p.
replace Tnil with (nilTermsHelp 0 (refl_equal 0)).
apply H.
auto.
Qed.

Let consTermsHelp : forall n : nat, Terms n -> Set.
intros.
case n.
exact
 (forall p : 0 = n, {foo : unit | eq_rec _ (fun z => Terms z) Tnil _ p = H}).
intros.
exact
 (forall p : S n0 = n,
  {t : Term * Terms n0 |
  eq_rec _ (fun z => Terms z) (Tcons n0 (fst t) (snd t)) _ p = H}).
Defined.

Lemma consTerms :
 forall (n : nat) (x : Terms (S n)),
 {t : Term * Terms n | Tcons n (fst t) (snd t) = x}.
Proof.
assert (forall (n : nat) (x : Terms n), consTermsHelp n x).
intros.
induction x as [| n t x Hrecx].
simpl in |- *.
intros.
exists tt.
elim p using K_dec_set.
apply eq_nat_dec.
simpl in |- *.
reflexivity.
simpl in |- *.
intros.
exists (t, x).
elim p using K_dec_set.
apply eq_nat_dec.
simpl in |- *.
reflexivity.
intros.
assert (consTermsHelp _ x).
apply H.
simpl in H0.
apply (H0 (refl_equal (S n))).
Qed.

Lemma term_dec : forall x y : Term, {x = y} + {x <> y}.
Proof.
induction language_dec.
assert
 (forall (f g : Functions L) (p : f = g) (ts : Terms (arity L (inr _ f)))
    (ss : Terms (arity L (inr _ g)))
    (q : arity L (inr _ f) = arity L (inr _ g)),
  eq_rec _ (fun x => Terms x) ts _ q = ss <-> apply f ts = apply g ss).
intros f g p.
eapply
 eq_ind
        with
        (x := g)
       (P := 
         fun a =>
         forall (ts : Terms (arity L (inr (Relations L) a)))
           (ss : Terms (arity L (inr (Relations L) g)))
           (q : arity L (inr (Relations L) a) = arity L (inr (Relations L) g)),
         eq_rec (arity L (inr (Relations L) a)) (fun x : nat => Terms x) ts
           (arity L (inr (Relations L) g)) q = ss <-> 
         apply a ts = apply g ss).
intros ts ss q.
apply
 K_dec_set
  with
    (x := arity L (inr (Relations L) g))
    (P := fun z =>
          eq_rec (arity L (inr (Relations L) g)) (fun x : nat => Terms x) ts
            (arity L (inr (Relations L) g)) z = ss <->
          apply g ts = apply g ss).
apply eq_nat_dec.
simpl in |- *.
split.
intros.
rewrite H.
auto.
intros.
inversion H.
eapply
 inj_right_pair2
                 with
                 (P := 
                   fun f : Functions L =>
                   Terms (arity L (inr (Relations L) f))).
assumption.
assumption.
auto.
intro.
elim x using
 Term_Terms_rec_full
  with
    (P0 := fun (n : nat) (ts : Terms n) =>
           forall ss : Terms n, {ts = ss} + {ts <> ss}).
intros.
induction y as [n0| f t].
induction (eq_nat_dec n n0).
rewrite a0.
left.
auto.
right.
unfold not in |- *; intros.
inversion H0.
auto.
right.
discriminate.
intros.
induction y as [n| f0 t0].
right.
discriminate.
induction (a f f0).
assert (arity L (inr (Relations L) f0) = arity L (inr (Relations L) f)).
rewrite a0.
reflexivity.
set (ss' := eq_rec _ (fun z : nat => Terms z) t0 _ H1) in *.
assert (f0 = f).
auto.
induction (H0 ss').
left.
induction (H _ _ H2 t0 t H1).
symmetry  in |- *.
apply H3.
symmetry  in |- *.
apply a1.
right.
unfold not in |- *; intros.
induction (H _ _ H2 t0 t H1).
elim b0.
symmetry  in |- *.
apply H5.
symmetry  in |- *.
assumption.
right.
unfold not in |- *; intro.
inversion H1.
auto.
intros.
left.
apply nilTerms.
intros.
induction (consTerms _ ss).
induction x0 as (a0, b0).
simpl in p.
induction (H1 b0).
induction (H0 a0).
left.
rewrite a1.
rewrite a2.
assumption.
right.
unfold not in |- *; intro.
elim b1.
rewrite <- p in H2.
inversion H2.
reflexivity.
right.
unfold not in |- *; intro.
elim b1.
rewrite <- p in H2.
inversion H2.
eapply inj_right_pair2 with (P := fun n : nat => Terms n).
apply eq_nat_dec.
assumption.
Qed.

Lemma terms_dec : forall (n : nat) (x y : Terms n), {x = y} + {x <> y}.
Proof.
intros.
induction x as [| n t x Hrecx].
left.
apply nilTerms.
induction (consTerms _ y).
induction x0 as (a, b).
simpl in p.
induction (Hrecx b).
induction (term_dec t a).
left.
rewrite a1.
rewrite a0.
assumption.
right.
unfold not in |- *; intro.
elim b0.
rewrite <- p in H.
inversion H.
reflexivity.
right.
unfold not in |- *; intro.
elim b0.
rewrite <- p in H.
inversion H.
eapply inj_right_pair2 with (P := fun n : nat => Terms n).
apply eq_nat_dec.
assumption.
Qed.

Lemma formula_dec : forall x y : Formula, {x = y} + {x <> y}.
Proof.
induction language_dec.
simple induction x; simple induction y; (right; discriminate) || intros.
induction (term_dec t t1).
induction (term_dec t0 t2).
left.
rewrite a0.
rewrite a1.
reflexivity.
right; unfold not in |- *; intros; elim b0.
inversion H.
reflexivity.
right; unfold not in |- *; intros; elim b0.
inversion H.
reflexivity.
induction (b r r0).
assert
 (forall (f g : Relations L) (p : f = g) (ts : Terms (arity L (inl _ f)))
    (ss : Terms (arity L (inl _ g)))
    (q : arity L (inl _ f) = arity L (inl _ g)),
  eq_rec _ (fun x => Terms x) ts _ q = ss <-> atomic f ts = atomic g ss).
intros f g p.
eapply
 eq_ind
        with
        (x := g)
       (P := 
         fun a =>
         forall (ts : Terms (arity L (inl _ a)))
           (ss : Terms (arity L (inl _ g)))
           (q : arity L (inl _ a) = arity L (inl _ g)),
         eq_rec _ (fun x => Terms x) ts _ q = ss <->
         atomic a ts = atomic g ss).
intros ts ss q.
elim q using K_dec_set.
apply eq_nat_dec.
simpl in |- *.
split.
intros.
rewrite H.
reflexivity.
intros.
inversion H.
eapply
 inj_right_pair2
                 with
                 (P := 
                   fun f : Relations L =>
                   Terms (arity L (inl (Functions L) f))).
assumption.
assumption.
auto.
assert (arity L (inl (Functions L) r) = arity L (inl (Functions L) r0)).
rewrite a0.
reflexivity.
induction
 (terms_dec _
    (eq_rec (arity L (inl (Functions L) r)) (fun x : nat => Terms x) t
       (arity L (inl (Functions L) r0)) H0) t0).
left.
induction (H _ _ a0 t t0 H0).
auto.
right.
induction (H _ _ a0 t t0 H0).
tauto.
right.
unfold not in |- *; intros.
inversion H.
auto.
induction (H f1).
induction (H0 f2).
left.
rewrite a0.
rewrite a1.
reflexivity.
right; unfold not in |- *; intros.
inversion H3; auto.
right; unfold not in |- *; intros.
inversion H3; auto.
induction (H f0).
left.
rewrite a0.
reflexivity.
right; unfold not in |- *; intros.
inversion H1; auto.
induction (eq_nat_dec n n0).
induction (H f0).
left.
rewrite a0.
rewrite a1.
reflexivity.
right; unfold not in |- *; intros.
inversion H1; auto.
right; unfold not in |- *; intros.
inversion H1; auto.
Qed.

End Formula_Decideability.

Section Formula_Depth_Induction.

Fixpoint depth (A : Formula) : nat :=
  match A with
  | equal _ _ => 0
  | atomic _ _ => 0
  | impH A B => S (max (depth A) (depth B))
  | notH A => S (depth A)
  | forallH _ A => S (depth A)
  end.

Definition lt_depth (A B : Formula) : Prop := depth A < depth B.

Lemma depthImp1 : forall A B : Formula, lt_depth A (impH A B).
Proof.
unfold lt_depth in |- *.
simpl in |- *.
intros.
apply le_lt_n_Sm.
apply le_max_l.
Qed.

Lemma depthImp2 : forall A B : Formula, lt_depth B (impH A B).
Proof.
unfold lt_depth in |- *.
simpl in |- *.
intros.
apply le_lt_n_Sm.
apply le_max_r.
Qed.

Lemma depthNot : forall A : Formula, lt_depth A (notH A).
Proof.
unfold lt_depth in |- *.
auto.
Qed.

Lemma depthForall : forall (A : Formula) (v : nat), lt_depth A (forallH v A).
Proof.
unfold lt_depth in |- *.
auto.
Qed.

Lemma eqDepth :
 forall A B C : Formula, depth B = depth A -> lt_depth B C -> lt_depth A C.
Proof.
unfold lt_depth in |- *.
intros.
rewrite <- H.
assumption.
Qed.

Definition Formula_depth_rec_rec :
  forall P : Formula -> Set,
  (forall a : Formula, (forall b : Formula, lt_depth b a -> P b) -> P a) ->
  forall (n : nat) (b : Formula), depth b <= n -> P b.
intros P H n.
induction n as [| n Hrecn].
intros.
apply H.
intros.
unfold lt_depth in H1.
rewrite <- (le_n_O_eq _ H0) in H1.
elim (lt_n_O _ H1).
intros.
apply H.
intros.
apply Hrecn.
apply lt_n_Sm_le.
apply lt_le_trans with (depth b).
apply H1.
apply H0.
Defined.

Definition Formula_depth_rec (P : Formula -> Set)
  (rec : forall a : Formula, (forall b : Formula, lt_depth b a -> P b) -> P a)
  (a : Formula) : P a :=
  Formula_depth_rec_rec P rec (depth a) a (le_n (depth a)).

Lemma Formula_depth_rec_indep :
 forall (Q P : Formula -> Set)
   (rec : forall a : Formula,
          (forall b : Formula, lt_depth b a -> Q b -> P b) -> Q a -> P a),
 (forall (a : Formula)
    (z1 z2 : forall b : Formula, lt_depth b a -> Q b -> P b),
  (forall (b : Formula) (p : lt_depth b a) (q : Q b), z1 b p q = z2 b p q) ->
  forall q : Q a, rec a z1 q = rec a z2 q) ->
 forall (a : Formula) (q : Q a),
 Formula_depth_rec (fun x : Formula => Q x -> P x) rec a q =
 rec a
   (fun (b : Formula) _ =>
    Formula_depth_rec (fun x : Formula => Q x -> P x) rec b) q.
Proof.
intros Q P rec H.
unfold Formula_depth_rec in |- *.
set (H0 := Formula_depth_rec_rec (fun x : Formula => Q x -> P x) rec) in *.
assert
 (forall (n m : nat) (b : Formula) (l1 : depth b <= n) 
    (l2 : depth b <= m) (q : Q b), H0 n b l1 q = H0 m b l2 q).
simple induction n.
simpl in |- *.
intros.
induction m as [| m Hrecm].
simpl in |- *.
apply H.
intros.
induction
 (lt_n_O (depth b0)
    (eq_ind_r (fun n0 : nat => depth b0 < n0) p (le_n_O_eq (depth b) l1))).
intros.
simpl in |- *.
apply H.
intros.
induction
 (lt_n_O (depth b0)
    (eq_ind_r (fun n0 : nat => depth b0 < n0) p (le_n_O_eq (depth b) l1))).
simple induction m.
intros.
simpl in |- *.
apply H.
intros.
induction
 (lt_n_O (depth b0)
    (eq_ind_r (fun n1 : nat => depth b0 < n1) p (le_n_O_eq (depth b) l2))).
intros.
simpl in |- *.
apply H.
intros.
apply H1.
intros.
replace (H0 (depth a) a (le_n (depth a)) q) with
 (H0 (S (depth a)) a (le_n_Sn (depth a)) q).
simpl in |- *.
apply H.
intros.
apply H1.
apply H1.
Qed.

Definition Formula_depth_rec2rec (P : Formula -> Set)
  (f1 : forall t t0 : Term, P (equal t t0))
  (f2 : forall (r : Relations L) (t : Terms (arity L (inl (Functions L) r))),
        P (atomic r t))
  (f3 : forall f : Formula, P f -> forall f0 : Formula, P f0 -> P (impH f f0))
  (f4 : forall f : Formula, P f -> P (notH f))
  (f5 : forall (v : nat) (a : Formula),
        (forall b : Formula, lt_depth b (forallH v a) -> P b) ->
        P (forallH v a)) (a : Formula) :
  (forall b : Formula, lt_depth b a -> P b) -> P a :=
  match a return ((forall b : Formula, lt_depth b a -> P b) -> P a) with
  | equal t s => fun _ => f1 t s
  | atomic r t => fun _ => f2 r t
  | impH f g =>
      fun hyp => f3 f (hyp f (depthImp1 f g)) g (hyp g (depthImp2 f g))
  | notH f => fun hyp => f4 f (hyp f (depthNot f))
  | forallH n f => fun hyp => f5 n f hyp
  end.

Definition Formula_depth_rec2 (P : Formula -> Set)
  (f1 : forall t t0 : Term, P (equal t t0))
  (f2 : forall (r : Relations L) (t : Terms (arity L (inl (Functions L) r))),
        P (atomic r t))
  (f3 : forall f : Formula, P f -> forall f0 : Formula, P f0 -> P (impH f f0))
  (f4 : forall f : Formula, P f -> P (notH f))
  (f5 : forall (v : nat) (a : Formula),
        (forall b : Formula, lt_depth b (forallH v a) -> P b) ->
        P (forallH v a)) (a : Formula) : P a :=
  Formula_depth_rec P (Formula_depth_rec2rec P f1 f2 f3 f4 f5) a.

Remark Formula_depth_rec2rec_nice :
 forall (Q P : Formula -> Set)
   (f1 : forall t t0 : Term, Q (equal t t0) -> P (equal t t0))
   (f2 : forall (r : Relations L) (t : Terms (arity L (inl (Functions L) r))),
         Q (atomic r t) -> P (atomic r t))
   (f3 : forall f : Formula,
         (Q f -> P f) ->
         forall f0 : Formula,
         (Q f0 -> P f0) -> Q (impH f f0) -> P (impH f f0)),
 (forall (f g : Formula) (z1 z2 : Q f -> P f),
  (forall q : Q f, z1 q = z2 q) ->
  forall z3 z4 : Q g -> P g,
  (forall q : Q g, z3 q = z4 q) ->
  forall q : Q (impH f g), f3 f z1 g z3 q = f3 f z2 g z4 q) ->
 forall f4 : forall f : Formula, (Q f -> P f) -> Q (notH f) -> P (notH f),
 (forall (f : Formula) (z1 z2 : Q f -> P f),
  (forall q : Q f, z1 q = z2 q) ->
  forall q : Q (notH f), f4 f z1 q = f4 f z2 q) ->
 forall
   f5 : forall (v : nat) (a : Formula),
        (forall b : Formula, lt_depth b (forallH v a) -> Q b -> P b) ->
        Q (forallH v a) -> P (forallH v a),
 (forall (v : nat) (a : Formula)
    (z1 z2 : forall b : Formula, lt_depth b (forallH v a) -> Q b -> P b),
  (forall (b : Formula) (q : lt_depth b (forallH v a)) (r : Q b),
   z1 b q r = z2 b q r) ->
  forall q : Q (forallH v a), f5 v a z1 q = f5 v a z2 q) ->
 forall (a : Formula)
   (z1 z2 : forall b : Formula, lt_depth b a -> Q b -> P b),
 (forall (b : Formula) (p : lt_depth b a) (q : Q b), z1 b p q = z2 b p q) ->
 forall q : Q a,
 Formula_depth_rec2rec (fun x : Formula => Q x -> P x) f1 f2 f3 f4 f5 a z1 q =
 Formula_depth_rec2rec (fun x : Formula => Q x -> P x) f1 f2 f3 f4 f5 a z2 q.
Proof.
intros.
induction a as [t t0| r t| a1 Hreca1 a0 Hreca0| a Hreca| n a Hreca].
auto.
auto.
simpl in |- *.
apply H.
intros.
apply H2.
intros.
apply H2.
simpl in |- *.
apply H0.
intros.
apply H2.
simpl in |- *.
apply H1.
apply H2.
Qed.

Lemma Formula_depth_rec2_imp :
 forall (Q P : Formula -> Set)
   (f1 : forall t t0 : Term, Q (equal t t0) -> P (equal t t0))
   (f2 : forall (r : Relations L) (t : Terms (arity L (inl (Functions L) r))),
         Q (atomic r t) -> P (atomic r t))
   (f3 : forall f : Formula,
         (Q f -> P f) ->
         forall f0 : Formula,
         (Q f0 -> P f0) -> Q (impH f f0) -> P (impH f f0)),
 (forall (f g : Formula) (z1 z2 : Q f -> P f),
  (forall q : Q f, z1 q = z2 q) ->
  forall z3 z4 : Q g -> P g,
  (forall q : Q g, z3 q = z4 q) ->
  forall q : Q (impH f g), f3 f z1 g z3 q = f3 f z2 g z4 q) ->
 forall f4 : forall f : Formula, (Q f -> P f) -> Q (notH f) -> P (notH f),
 (forall (f : Formula) (z1 z2 : Q f -> P f),
  (forall q : Q f, z1 q = z2 q) ->
  forall q : Q (notH f), f4 f z1 q = f4 f z2 q) ->
 forall
   f5 : forall (v : nat) (a : Formula),
        (forall b : Formula, lt_depth b (forallH v a) -> Q b -> P b) ->
        Q (forallH v a) -> P (forallH v a),
 (forall (v : nat) (a : Formula)
    (z1 z2 : forall b : Formula, lt_depth b (forallH v a) -> Q b -> P b),
  (forall (b : Formula) (q : lt_depth b (forallH v a)) (r : Q b),
   z1 b q r = z2 b q r) ->
  forall q : Q (forallH v a), f5 v a z1 q = f5 v a z2 q) ->
 forall (a b : Formula) (q : Q (impH a b)),
 Formula_depth_rec2 (fun x : Formula => Q x -> P x) f1 f2 f3 f4 f5 
   (impH a b) q =
 f3 a (Formula_depth_rec2 (fun x : Formula => Q x -> P x) f1 f2 f3 f4 f5 a) b
   (Formula_depth_rec2 (fun x : Formula => Q x -> P x) f1 f2 f3 f4 f5 b) q.
Proof.
intros.
unfold Formula_depth_rec2 at 1 in |- *.
rewrite Formula_depth_rec_indep.
simpl in |- *.
reflexivity.
intros.
apply Formula_depth_rec2rec_nice; auto.
Qed.

Lemma Formula_depth_rec2_not :
 forall (Q P : Formula -> Set)
   (f1 : forall t t0 : Term, Q (equal t t0) -> P (equal t t0))
   (f2 : forall (r : Relations L) (t : Terms (arity L (inl (Functions L) r))),
         Q (atomic r t) -> P (atomic r t))
   (f3 : forall f : Formula,
         (Q f -> P f) ->
         forall f0 : Formula,
         (Q f0 -> P f0) -> Q (impH f f0) -> P (impH f f0)),
 (forall (f g : Formula) (z1 z2 : Q f -> P f),
  (forall q : Q f, z1 q = z2 q) ->
  forall z3 z4 : Q g -> P g,
  (forall q : Q g, z3 q = z4 q) ->
  forall q : Q (impH f g), f3 f z1 g z3 q = f3 f z2 g z4 q) ->
 forall f4 : forall f : Formula, (Q f -> P f) -> Q (notH f) -> P (notH f),
 (forall (f : Formula) (z1 z2 : Q f -> P f),
  (forall q : Q f, z1 q = z2 q) ->
  forall q : Q (notH f), f4 f z1 q = f4 f z2 q) ->
 forall
   f5 : forall (v : nat) (a : Formula),
        (forall b : Formula, lt_depth b (forallH v a) -> Q b -> P b) ->
        Q (forallH v a) -> P (forallH v a),
 (forall (v : nat) (a : Formula)
    (z1 z2 : forall b : Formula, lt_depth b (forallH v a) -> Q b -> P b),
  (forall (b : Formula) (q : lt_depth b (forallH v a)) (r : Q b),
   z1 b q r = z2 b q r) ->
  forall q : Q (forallH v a), f5 v a z1 q = f5 v a z2 q) ->
 forall (a : Formula) (q : Q (notH a)),
 Formula_depth_rec2 (fun x : Formula => Q x -> P x) f1 f2 f3 f4 f5 (notH a) q =
 f4 a (Formula_depth_rec2 (fun x : Formula => Q x -> P x) f1 f2 f3 f4 f5 a) q.
Proof.
intros.
unfold Formula_depth_rec2 at 1 in |- *.
rewrite Formula_depth_rec_indep.
simpl in |- *.
reflexivity.
apply Formula_depth_rec2rec_nice; auto.
Qed.

Lemma Formula_depth_rec2_forall :
 forall (Q P : Formula -> Set)
   (f1 : forall t t0 : Term, Q (equal t t0) -> P (equal t t0))
   (f2 : forall (r : Relations L) (t : Terms (arity L (inl (Functions L) r))),
         Q (atomic r t) -> P (atomic r t))
   (f3 : forall f : Formula,
         (Q f -> P f) ->
         forall f0 : Formula,
         (Q f0 -> P f0) -> Q (impH f f0) -> P (impH f f0)),
 (forall (f g : Formula) (z1 z2 : Q f -> P f),
  (forall q : Q f, z1 q = z2 q) ->
  forall z3 z4 : Q g -> P g,
  (forall q : Q g, z3 q = z4 q) ->
  forall q : Q (impH f g), f3 f z1 g z3 q = f3 f z2 g z4 q) ->
 forall f4 : forall f : Formula, (Q f -> P f) -> Q (notH f) -> P (notH f),
 (forall (f : Formula) (z1 z2 : Q f -> P f),
  (forall q : Q f, z1 q = z2 q) ->
  forall q : Q (notH f), f4 f z1 q = f4 f z2 q) ->
 forall
   f5 : forall (v : nat) (a : Formula),
        (forall b : Formula, lt_depth b (forallH v a) -> Q b -> P b) ->
        Q (forallH v a) -> P (forallH v a),
 (forall (v : nat) (a : Formula)
    (z1 z2 : forall b : Formula, lt_depth b (forallH v a) -> Q b -> P b),
  (forall (b : Formula) (q : lt_depth b (forallH v a)) (r : Q b),
   z1 b q r = z2 b q r) ->
  forall q : Q (forallH v a), f5 v a z1 q = f5 v a z2 q) ->
 forall (v : nat) (a : Formula) (q : Q (forallH v a)),
 Formula_depth_rec2 (fun x : Formula => Q x -> P x) f1 f2 f3 f4 f5
   (forallH v a) q =
 f5 v a
   (fun (b : Formula) _ (q : Q b) =>
    Formula_depth_rec2 (fun x : Formula => Q x -> P x) f1 f2 f3 f4 f5 b q) q.
Proof.
intros.
unfold Formula_depth_rec2 at 1 in |- *.
rewrite Formula_depth_rec_indep.
simpl in |- *.
apply H1.
intros.
reflexivity.
apply Formula_depth_rec2rec_nice; auto.
Qed.

Definition Formula_depth_ind :
  forall P : Formula -> Prop,
  (forall a : Formula, (forall b : Formula, lt_depth b a -> P b) -> P a) ->
  forall a : Formula, P a.
Proof.
intros.
assert (forall (n : nat) (b : Formula), depth b <= n -> P b).
intro.
induction n as [| n Hrecn].
intros.
apply H.
intros.
unfold lt_depth in H1.
rewrite <- (le_n_O_eq _ H0) in H1.
elim (lt_n_O _ H1).
intros.
apply H.
intros.
apply Hrecn.
apply lt_n_Sm_le.
apply lt_le_trans with (depth b).
apply H1.
apply H0.
eapply H0.
apply le_n.
Qed.

Lemma Formula_depth_ind2 :
 forall P : Formula -> Prop,
 (forall t t0 : Term, P (equal t t0)) ->
 (forall (r : Relations L) (t : Terms (arity L (inl (Functions L) r))),
  P (atomic r t)) ->
 (forall f : Formula, P f -> forall f0 : Formula, P f0 -> P (impH f f0)) ->
 (forall f : Formula, P f -> P (notH f)) ->
 (forall (v : nat) (a : Formula),
  (forall b : Formula, lt_depth b (forallH v a) -> P b) -> P (forallH v a)) ->
 forall f4 : Formula, P f4.
Proof.
intros.
apply Formula_depth_ind.
simple induction a; auto.
intros.
apply H1.
apply H6.
apply depthImp1.
apply H6.
apply depthImp2.
intros.
apply H2.
apply H5.
apply depthNot.
Qed.

End Formula_Depth_Induction.

End First_Order_Logic.
