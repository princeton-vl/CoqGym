Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export Image.
Require Import ImageImplicit.
Require Export Finite_sets.
Require Export FunctionProperties.
Require Import DecidableDec.
Require Import ProofIrrelevance.
Require Import Description.

Set Asymmetric Patterns.

Inductive FiniteT : Type -> Prop :=
  | empty_finite: FiniteT False
  | add_finite: forall T:Type, FiniteT T -> FiniteT (option T)
  | bij_finite: forall (X Y:Type) (f:X->Y), FiniteT X ->
    invertible f -> FiniteT Y.

Lemma True_finite: FiniteT True.
Proof.
apply bij_finite with (option False)
  (fun _ => I).
constructor; constructor.
exists (True_rect None).
destruct x as [[]|].
remember (True_rect (@None False) I) as LHS.
destruct LHS as [[]|].
reflexivity.

exact (fun y:True => match y with
  | I => refl_equal I
  end).
Qed.

Lemma finite_dec_exists: forall (X:Type) (P:X->Prop),
  FiniteT X -> (forall x:X, {P x} + {~ P x}) ->
  { exists x:X, P x } + { forall x:X, ~ P x }.
Proof.
intros.
apply exclusive_dec.
red; intro.
destruct H0.
destruct H0.
contradiction (H1 x).

revert P X0.
induction H.
right.
destruct x.
intros.
case (IHFiniteT (fun x:T => P (Some x))
  (fun x:T => X0 (Some x))).
left.
destruct H0.
exists (Some x).
assumption.
intro.
case (X0 None).
left.
exists None.
assumption.
right.
destruct x.
apply H0.
assumption.
destruct H0.
intros.
case (IHFiniteT (fun x:X => P (f x))
  (fun x:X => X0 (f x))).
left.
destruct H2.
exists (f x).
assumption.
right.
intro.
rewrite <- H1 with x.
apply H2.
Qed.

Lemma finite_dec_forall: forall (X:Type) (P:X->Prop),
  FiniteT X -> (forall x:X, { P x } + { ~ P x }) ->
  { forall x:X, P x } + { exists x:X, ~ P x }.
Proof.
intros.
apply exclusive_dec.
intuition.
destruct H2.
contradiction (H1 x).

revert P X0.
induction H.
left.
destruct x.
intros.
case (IHFiniteT (fun x:T => P (Some x))
  (fun x:T => X0 (Some x))).
intro.
case (X0 None).
left.
destruct x.
apply H0.
assumption.
right.
exists None.
assumption.
right.
destruct H0.
exists (Some x).
assumption.

intros.
destruct H0.
case (IHFiniteT (fun x:X => P (f x))
  (fun x:X => X0 (f x))).
left.
intro y.
rewrite <- H1.
apply H2.
right.
destruct H2.
exists (f x).
assumption.
Qed.

Lemma finite_eq_dec: forall X:Type, FiniteT X ->
  forall x y:X, {x=y} + {x<>y}.
Proof.
intros.
apply decidable_dec.
induction H.
destruct x.
decide equality.

destruct H0.
case (IHFiniteT (g x) (g y)).
left.
rewrite <- H1.
rewrite <- H1 with x.
rewrite H2.
reflexivity.
right.
contradict H2.
rewrite H2.
reflexivity.
Qed.

Lemma finite_dep_choice: forall (A:Type) (B:forall x:A, Type)
  (R:forall x:A, B x->Prop),
  FiniteT A -> (forall x:A, exists y:B x, R x y) ->
  exists f:(forall x:A, B x), forall x:A, R x (f x).
Proof.
intros.
revert B R H0.
induction H.
intros.
exists (fun x:False => False_rect (B x) x).
destruct x.
intros.
pose proof (IHFiniteT (fun x:T => B (Some x))
  (fun x:T => R (Some x))
  (fun x:T => H0 (Some x))).
destruct H1.
pose proof (H0 None).
destruct H2.
exists (fun y:option T =>
  match y return (B y) with
  | Some y0 => x y0
  | None => x0
  end).
destruct x1.
apply H1.
assumption.

intros.
destruct H0.
pose proof (IHFiniteT (fun x:X => B (f x))
  (fun x:X => R (f x))
  (fun x:X => H1 (f x))).
destruct H3.
pose (f0 := fun y:Y => x (g y)).
pose (conv := fun (y:Y) (a:B (f (g y))) =>
  eq_rect (f (g y)) B a y (H2 y)).

exists (fun y:Y => conv y (x (g y))).
intro.
unfold conv; simpl.
generalize (H2 x0).
pattern x0 at 2 3 6.
rewrite <- H2.
intro.
rewrite <- eq_rect_eq.
apply H3.
Qed.

Lemma finite_choice : forall (A B:Type) (R:A->B->Prop),
  FiniteT A -> (forall x:A, exists y:B, R x y) ->
  exists f:A->B, forall x:A, R x (f x).
Proof.
intros.
apply finite_dep_choice.
assumption.
assumption.
Qed.

Lemma Finite_ens_type: forall {X:Type} (S:Ensemble X),
  Finite _ S -> FiniteT { x:X | In S x }.
Proof.
intros.
induction H.
apply bij_finite with False (False_rect _).
constructor.
assert (g:{x:X | In Empty_set x}->False).
intro.
destruct X0.
destruct i.
exists g.
destruct x.
destruct y.
destruct g.

assert (Included A (Add A x)).
auto with sets.
assert (In (Add A x) x).
auto with sets.
pose (g := fun (y: option {x:X | In A x}) =>
  match y return {x0:X | In (Add A x) x0} with
  | Some (exist y0 i) => exist (fun x2:X => In (Add A x) x2) y0 (H1 y0 i)
  | None => exist (fun x2:X => In (Add A x) x2) x H2
  end).
apply bij_finite with _ g.
apply add_finite.
assumption.

assert (h:forall x0:X, In (Add A x) x0 ->
  { In A x0 } + { x0 = x }).
intros; apply exclusive_dec.
intuition.
destruct H6; auto.
destruct H3.
left; assumption.
right; destruct H3; reflexivity.

pose (ginv := fun s:{x0:X | In (Add A x) x0} =>
  match s return option {x:X | In A x} with
  | exist x0 i => match (h x0 i) with
                  | left iA => Some (exist _ x0 iA)
                  | right _ => None
                  end
  end).
exists ginv.
intro; destruct x0.
destruct s.
simpl.
remember (h x0 (H1 x0 i)) as sum; destruct sum.
destruct (proof_irrelevance _ i i0).
reflexivity.
contradiction H0.
rewrite <- e; assumption.
simpl.
remember (h x H2) as sum; destruct sum.
contradiction H0.
reflexivity.

intro.
unfold ginv.
destruct y.
destruct (h x0 i).
simpl.
generalize (H1 x0 i0); intro.
destruct (proof_irrelevance _ i i1).
reflexivity.
simpl.
destruct e.
destruct (proof_irrelevance _ H2 i).
reflexivity.
Qed.

Lemma FiniteT_img: forall (X Y:Type) (f:X->Y),
  FiniteT X -> (forall y1 y2:Y, y1=y2 \/ y1<>y2) ->
  Finite _ (Im Full_set f).
Proof.
intros.
induction H.
assert (Im Full_set f = Empty_set).
apply Extensionality_Ensembles.
red; split.
red; intros.
destruct H.
destruct x.
auto with sets.
rewrite H.
constructor.

assert ({exists x:T, f (Some x) = f None} +
        {forall x:T, f (Some x) <> f None}).
apply finite_dec_exists.
assumption.
intro.
apply decidable_dec.
apply H0.
case H1.
intro.
pose (g := fun (x:T) => f (Some x)).
assert (Im Full_set f =
        Im Full_set g).
apply Extensionality_Ensembles.
red; split.
red; intros.
destruct H2.
destruct x.
exists t.
constructor.
assumption.
destruct e.
exists x.
constructor.
transitivity (f None).
assumption.
symmetry; assumption.
red; intros.
destruct H2.
exists (Some x).
constructor.
assumption.
rewrite H2.
apply IHFiniteT.

intros.
pose (g := fun x:T => f (Some x)).
assert (Im Full_set f =
  Add (Im Full_set g) (f None)).
apply Extensionality_Ensembles.
red; split.
red; intros.
destruct H2.
destruct x.
left.
exists t.
constructor.
assumption.
right.
auto with sets.
red; intros.
destruct H2.
destruct H2.
exists (Some x).
constructor.
assumption.
destruct H2.
exists None.
constructor.
reflexivity.
rewrite H2.
constructor.
apply IHFiniteT.
red; intro.
destruct H3.
contradiction (n x).
symmetry; assumption.

pose (g := fun (x:X) => f (f0 x)).
assert (Im Full_set f = Im Full_set g).
apply Extensionality_Ensembles.
red; split.
red; intros.
destruct H2.
destruct H1.
rewrite H3.
rewrite <- H4 with x.
exists (g0 x).
constructor.
unfold g.
reflexivity.
red; intros.
destruct H2.
exists (f0 x).
constructor.
assumption.

rewrite H2.
apply IHFiniteT.
Qed.

Lemma surj_finite: forall (X Y:Type) (f:X->Y),
  FiniteT X -> surjective f ->
  (forall y1 y2:Y, y1=y2 \/ y1<>y2) ->
  FiniteT Y.
Proof.
intros.
apply bij_finite with {y:Y | In (Im Full_set f) y}
  (@proj1_sig _ (fun y:Y => In (Im Full_set f) y)).
apply Finite_ens_type.
apply FiniteT_img.
assumption.
assumption.
assert (forall y:Y, In (Im Full_set f) y).
intro.
destruct (H0 y).
exists x; auto with sets.
constructor.

pose (proj1_sig_inv := fun y:Y =>
  exist (fun y0:Y => In (Im Full_set f) y0) y (H2 y)).
exists proj1_sig_inv.
destruct x.
simpl.
unfold proj1_sig_inv.
destruct (proof_irrelevance _ (H2 x) i); trivial.
intros; simpl; reflexivity.
Qed.

Lemma finite_subtype: forall (X:Type) (P:X->Prop),
  FiniteT X -> (forall x:X, P x \/ ~ P x) ->
  FiniteT {x:X | P x}.
Proof.
intros.
induction H.
apply bij_finite with False (False_rect _).
constructor.
exists (@proj1_sig _ _).
destruct x.
intro s; destruct s; destruct x.

destruct (H0 None).
pose (g := fun (x:option {x:T | P (Some x)}) =>
  match x return {x:option T | P x} with
  | Some (exist x0 i) => exist (fun x:option T => P x) (Some x0) i
  | None => exist (fun x:option T => P x) None H1
  end).
apply bij_finite with _ g.
apply add_finite.
apply IHFiniteT.
intro; apply H0.
pose (ginv := fun (s:{x0:option T | P x0}) =>
  match s return option {x:T | P (Some x)} with
  | exist (Some x0) i => Some (exist (fun y:T => P (Some y)) x0 i)
  | exist None _ => None
  end).
exists ginv.
destruct x as [[x0]|].
simpl.
reflexivity.
simpl.
reflexivity.
destruct y as [[x0|]].
simpl.
reflexivity.
simpl.
destruct (proof_irrelevance _ H1 p).
reflexivity.

pose (g := fun (x:{x:T | P (Some x)}) =>
  match x return {x:option T | P x} with
    | exist x0 i => exist (fun x:option T => P x) (Some x0) i
  end).
apply bij_finite with _ g.
apply IHFiniteT.
intro; apply H0.
pose (ginv := fun s:{x0:option T | P x0} =>
  match s return {x:T | P (Some x)} with
    | exist (Some x0) i => exist (fun x:T => P (Some x)) x0 i
    | exist None i => False_rect _ (H1 i)
  end).
exists ginv.
destruct x; simpl.
reflexivity.
destruct y as [[x0|]].
simpl.
reflexivity.
contradiction H1.

pose (g := fun (x:{x:X | P (f x)}) =>
  match x with
  | exist x0 i => exist (fun x:Y => P x) (f x0) i
  end).
apply (bij_finite _ _ g).
apply IHFiniteT.
intro; apply H0.
destruct H1.
assert (forall y:Y, P y -> P (f (g0 y))).
intros; rewrite H2; assumption.
pose (ginv := fun (y:{y:Y | P y}) =>
  match y with
  | exist y0 i => exist (fun x:X => P (f x)) (g0 y0) (H3 y0 i)
  end).
exists ginv.
destruct x; simpl.
generalize (H3 (f x) p).
rewrite H1.
intro; destruct (proof_irrelevance _ p p0).
reflexivity.

destruct y; simpl.
generalize (H3 x p).
rewrite H2.
intro; destruct (proof_irrelevance _ p p0).
reflexivity.
Qed.

Lemma inj_finite: forall (X Y:Type) (f:X->Y),
  FiniteT Y -> FunctionProperties.injective f ->
  (forall y:Y, (exists x:X, f x = y) \/
               (~ exists x:X, f x = y)) ->
  FiniteT X.
Proof.
intros.
assert (forall y:{y:Y | exists x:X, f x = y}, {x:X | f x = proj1_sig y}).
intro.
destruct y.
simpl.

apply constructive_definite_description.
destruct e.
exists x0.
red; split.
assumption.
intros.
apply H0.
transitivity x.
assumption.
symmetry; assumption.

pose (g := fun y:{y:Y | exists x:X, f x = y} =>
  proj1_sig (X0 y)).
apply bij_finite with _ g.
apply finite_subtype.
assumption.
assumption.

pose (ginv := fun (x:X) => exist (fun y:Y => exists x:X, f x = y)
  (f x) (ex_intro _ x (refl_equal _))).
exists ginv.
destruct x as [y [x e]].
unfold g; simpl.
match goal with |- context [X0 ?arg] => destruct (X0 arg) end.
simpl.
unfold ginv; simpl.
simpl in e0.
repeat match goal with |- context [ex_intro ?f ?x ?e] =>
  generalize (ex_intro f x e) end.
rewrite <- e0.
intros; destruct (proof_irrelevance _ e1 e2).
reflexivity.

intro; unfold ginv.
unfold g; simpl.
match goal with |- context [X0 ?arg] => destruct (X0 arg) end.
simpl.
simpl in e.
auto.
Qed.

Lemma finite_inj_surj: forall (X:Type) (f:X->X),
  FiniteT X -> injective f -> surjective f.
Proof.
intros.
induction H.
red.
destruct y.

remember (f None) as f0; destruct f0 as [a|].
assert (forall x:T, f (Some x) <> Some a).
unfold not; intros.
assert (Some x = None).
apply H0.
congruence.
discriminate H2.
pose (g := fun x:T => match f (Some x) with
  | Some y => y
  | None => a
end).
assert (surjective g).
apply IHFiniteT.
red; intros.
remember (f (Some x1)) as fx1; destruct fx1;
remember (f (Some x2)) as fx2; destruct fx2.
unfold g in H2.
rewrite <- Heqfx1 in H2; rewrite <- Heqfx2 in H2.
destruct H2; assert (f (Some x1) = f (Some x2)).
congruence.
apply H0 in H2.
injection H2; trivial.

unfold g in H2; rewrite <- Heqfx1 in H2; rewrite <- Heqfx2 in H2.
destruct H2.
contradiction (H1 x1).
symmetry; assumption.

unfold g in H2; rewrite <- Heqfx1 in H2; rewrite <- Heqfx2 in H2.
destruct H2.
contradiction (H1 x2).
symmetry; assumption.

assert (Some x1 = Some x2).
apply H0.
congruence.
injection H3; trivial.

red; intro.
destruct y.
case (finite_eq_dec _ H t a).
exists None.
congruence.
destruct (H2 t).
exists (Some x).
unfold g in H3.
destruct (f (Some x)).
congruence.
contradiction n.
symmetry; assumption.
destruct (H2 a).
exists (Some x).
unfold g in H3.
remember (f (Some x)) as fx; destruct fx.
destruct H3.
contradiction (H1 x).
symmetry; assumption.
reflexivity.

assert (forall x:T, { y:T | f (Some x) = Some y }).
intros.
remember (f (Some x)) as fx; destruct fx.
exists t; reflexivity.
assert (Some x = None).
apply H0.
congruence.
discriminate H1.
pose (g := fun x:T => proj1_sig (X x)).
assert (surjective g).
apply IHFiniteT.
red; intros.
unfold g in H1.
repeat destruct X in H1.
simpl in H1.
assert (Some x1 = Some x2).
apply H0.
congruence.
injection H2; trivial.

red; intro.
destruct y.
destruct (H1 t).
unfold g in H2; destruct X in H2.
simpl in H2.
exists (Some x).
congruence.
exists None.
symmetry; assumption.

destruct H1.

pose (f' := fun (x:X) => g (f (f0 x))).
assert (surjective f').
apply IHFiniteT.
red; intros.
unfold f' in H3.
assert (f (f0 x1) = f (f0 x2)).
congruence.
apply H0 in H4.
congruence.

red; intro.
destruct (H3 (g y)).
unfold f' in H4.
exists (f0 x).
congruence.
Qed.

Lemma finite_surj_inj: forall (X:Type) (f:X->X),
  FiniteT X -> surjective f -> FunctionProperties.injective f.
Proof.
intros.
assert (exists g:X->X, forall x:X, f (g x) = x).
apply finite_choice with (R:=fun (x y:X) => f y = x).
assumption.
assumption.
destruct H1 as [g].
assert (surjective g).
apply finite_inj_surj.
assumption.
red; intros.
rewrite <- H1 with x1.
rewrite <- H1 with x2.
rewrite H2; reflexivity.
red; intros.
destruct (H2 x1).
destruct (H2 x2).
rewrite <- H4 in H3.
rewrite <- H5 in H3.
repeat rewrite H1 in H3.
rewrite <- H4.
rewrite <- H5.
rewrite H3.
reflexivity.
Qed.

Lemma finite_sum: forall X Y:Type, FiniteT X -> FiniteT Y ->
  FiniteT (X+Y).
Proof.
intros.
induction H0.
apply bij_finite with _ inl.
assumption.
pose (g := fun (x:X+False) => match x with
  | inl x => x
  | inr f => False_rect X f
end).
exists g.
intro; simpl.
reflexivity.
destruct y.
simpl.
reflexivity.
destruct f.

pose (g := fun (x:option (X+T)) => match x with
  | Some (inl x) => inl _ x
  | Some (inr t) => inr _ (Some t)
  | None => inr _ None
  end).
apply bij_finite with _ g.
apply add_finite.
assumption.
pose (ginv := fun (x:X + option T) => match x with
  | inl x => Some (inl _ x)
  | inr (Some t) => Some (inr _ t)
  | inr None => None
  end).
exists ginv.
destruct x as [[x|t]|]; trivial.
destruct y as [x|[t|]]; trivial.

pose (g := fun (x:X+X0) => match x with
  | inl x0 => inl _ x0
  | inr x0 => inr _ (f x0)
  end).
destruct H1.
pose (ginv := fun (x:X+Y) => match x with
  | inl x0 => inl _ x0
  | inr y0 => inr _ (g0 y0)
  end).
apply bij_finite with _ g.
assumption.
exists ginv.
destruct x as [x0|x0]; trivial.
simpl.
rewrite H1; reflexivity.
destruct y as [x|y0]; trivial.
simpl.
rewrite H2; reflexivity.
Qed.

Lemma finite_prod: forall (X Y:Type), FiniteT X -> FiniteT Y ->
  FiniteT (X*Y).
Proof.
intros.
induction H0.
apply bij_finite with _ (False_rect _).
constructor.
exists (@snd X False).
destruct x.
destruct y.
destruct f.

pose (g := fun (x:X*T + X) => match x with
  | inl (pair x0 t) => pair x0 (Some t)
  | inr x0 => pair x0 None
  end).
pose (ginv := fun (x:X * option T) => match x with
  | (x0, Some t) => inl _ (x0, t)
  | (x0, None) => inr _ x0
  end).
apply bij_finite with _ g.
apply finite_sum.
assumption.
assumption.
exists ginv.
destruct x as [[x0 t]|x0]; trivial.
destruct y as [x0 [t|]]; trivial.

pose (g := fun (y:X*X0) => match y with
  | pair x x0 => pair x (f x0)
  end).
destruct H1.
pose (ginv := fun (y:X*Y) => let (x,y0) := y in
  (x, g0 y0)).
apply bij_finite with _ g.
assumption.
exists ginv.
destruct x as [x x0]; unfold ginv, g; try rewrite H1; trivial.
destruct y as [x y]; unfold ginv, g; try rewrite H2; trivial.
Qed.

Require Import FunctionalExtensionality.

Lemma finite_exp: forall X Y:Type, FiniteT X -> FiniteT Y ->
  FiniteT (X->Y).
Proof.
intros.
induction H.
pose (g := fun (x:True) (f:False) => False_rect Y f).
pose (ginv := fun (_:False->Y) => I).
apply bij_finite with _ g.
apply True_finite.
exists ginv.
destruct x as [].
trivial.
intro; extensionality f.
destruct f.

pose (g := fun (p:(T->Y)*Y) (x:option T) =>
  let (f,y0) := p in
  match x with
  | Some x0 => f x0
  | None => y0
  end).
pose (ginv := fun (f:option T->Y) =>
  (fun x:T => f (Some x), f None)).
apply bij_finite with _ g.
apply finite_prod.
assumption.
assumption.
exists ginv.
destruct x as [f y0]; try extensionality t;
try destruct t as [t0|]; trivial.
intro.
extensionality t; destruct t as [t0|]; trivial.

destruct H1.
pose (g0 := fun (h:X->Y) (y:Y0) => h (g y)).
apply bij_finite with _ g0.
assumption.
pose (g0inv := fun (h:Y0->Y) (x:X) => h (f x)).
exists g0inv.
intro.
extensionality x0; unfold g0; unfold g0inv; simpl.
rewrite H1; reflexivity.
intro.
extensionality y0; unfold g0; unfold g0inv; simpl.
rewrite H2; reflexivity.
Qed.

Lemma FiniteT_has_nat_cardinal: forall X:Type, FiniteT X ->
  exists! n:nat, cardinal _ (@Full_set X) n.
Proof.
intros.
apply -> unique_existence; split.
apply finite_cardinal.
pose (idX := fun x:X => x).
assert (Im Full_set idX = Full_set).
apply Extensionality_Ensembles.
red; split.
red; intros; constructor.
red; intros.
exists x.
constructor.
trivial.

rewrite <- H0.
apply FiniteT_img with (f:=fun x:X => x).
assumption.
intros.
case (finite_eq_dec X H y1 y2); tauto.

red; intros.
apply cardinal_unicity with X Full_set; trivial.
Qed.

Definition FiniteT_nat_cardinal (X:Type) (H:FiniteT X) : nat :=
  proj1_sig (constructive_definite_description _
              (FiniteT_has_nat_cardinal X H)).
Lemma FiniteT_nat_cardinal_def: forall (X:Type) (H:FiniteT X),
  cardinal _ (@Full_set X) (FiniteT_nat_cardinal X H).
Proof.
intros; unfold FiniteT_nat_cardinal.
destruct constructive_definite_description.
assumption.
Qed.
Lemma FiniteT_nat_cardinal_cond: forall (X:Type) (H:FiniteT X)
  (n:nat),
  cardinal _ (@Full_set X) n ->
  FiniteT_nat_cardinal X H = n.
Proof.
intros.
pose proof (FiniteT_has_nat_cardinal X H).
destruct H1.
red in H1.
destruct H1.
transitivity x.
symmetry; apply H2.
apply FiniteT_nat_cardinal_def.
apply H2; trivial.
Qed.

Lemma FiniteT_nat_cardinal_False:
  FiniteT_nat_cardinal False empty_finite = 0.
Proof.
apply FiniteT_nat_cardinal_cond.
assert (@Full_set False = @Empty_set False).
apply Extensionality_Ensembles; red; split; auto with sets.
red; intros.
destruct x.
rewrite H.
constructor.
Qed.

Lemma injection_preserves_cardinal: forall (X Y:Type)
  (f:X->Y) (n:nat) (S:Ensemble X), cardinal _ S n ->
  injective f -> cardinal _ (Im S f) n.
Proof.
intros.
induction H.
assert (Im Empty_set f = Empty_set).
apply Extensionality_Ensembles; split; auto with sets.
red; intros.
destruct H.
destruct H.
rewrite H; constructor.
assert (Im (Add A x) f = Add (Im A f) (f x)).
apply Extensionality_Ensembles; split.
red; intros.
destruct H2.
symmetry in H3; destruct H3.
destruct H2.
left; exists x0; auto with sets.
destruct H2; right; auto with sets.
red; intros.
destruct H2.
destruct H2.
exists x0.
left; auto with sets.
assumption.
destruct H2.
exists x; trivial; right; auto with sets.
rewrite H2.
constructor; trivial.
red; intro H3; inversion H3.
apply H0 in H5; destruct H5.
contradiction H1.
Qed.

Lemma FiniteT_nat_cardinal_option:
  forall (X:Type) (H:FiniteT X),
  FiniteT_nat_cardinal (option X) (add_finite X H) =
  S (FiniteT_nat_cardinal X H).
Proof.
intros.
apply FiniteT_nat_cardinal_cond.
assert (Full_set =
        Add (Im Full_set (@Some X)) None).
apply Extensionality_Ensembles; split.
red; intros.
destruct x.
left; exists x; constructor.
right; constructor.
red; intros; constructor.
rewrite H0.
constructor.
apply injection_preserves_cardinal.
apply FiniteT_nat_cardinal_def.
red; intros x1 x2 Heq; injection Heq; trivial.
red; intro.
inversion H1.
discriminate H3.
Qed.

Lemma FiniteT_nat_cardinal_bijection:
  forall (X Y:Type) (H:FiniteT X) (g:X->Y) (Hinv:invertible g),
    FiniteT_nat_cardinal Y (bij_finite X Y g H Hinv) =
    FiniteT_nat_cardinal X H.
Proof.
intros.
apply FiniteT_nat_cardinal_cond.
apply invertible_impl_bijective in Hinv.
destruct Hinv as [g_inj g_surj].
assert (Full_set = Im Full_set g).
apply Extensionality_Ensembles; split; red; intros;
  try constructor.
destruct (g_surj x).
exists x0; try constructor; auto.
rewrite H0; apply injection_preserves_cardinal; trivial.
apply FiniteT_nat_cardinal_def.
Qed.

Lemma unique_FiniteT_nat_cardinal:
  exists! f: (forall (X:Type), FiniteT X -> nat),
  f False empty_finite = 0 /\
  (forall (X:Type) (H:FiniteT X),
     f (option X) (add_finite X H) = S (f X H)) /\
  (forall (X Y:Type) (H:FiniteT X) (g:X->Y) (Hinv:invertible g),
     f Y (bij_finite X Y g H Hinv) = f X H).
Proof.
match goal with |- @ex ?T (@unique ?T ?f) =>
  apply -> (@unique_existence T f) end.
split.
exists FiniteT_nat_cardinal.
repeat split.
exact FiniteT_nat_cardinal_False.
exact FiniteT_nat_cardinal_option.
exact FiniteT_nat_cardinal_bijection.
red; intros f g Hf Hg.
destruct Hf as [HFalse_f [Hoption_f Hbijection_f]].
destruct Hg as [HFalse_g [Hoption_g Hbijection_g]].
extensionality X; extensionality HFinite.
generalize HFinite.
induction HFinite.
intro.
destruct (proof_irrelevance _ empty_finite HFinite). 
congruence.
intro.
destruct (proof_irrelevance _ (add_finite T HFinite) HFinite0).
rewrite Hoption_f. rewrite Hoption_g. rewrite IHHFinite. reflexivity.
intro.
destruct (proof_irrelevance _ (bij_finite _ _ f0 HFinite H) HFinite0).
now rewrite Hbijection_f, Hbijection_g, IHHFinite. 
Qed.
