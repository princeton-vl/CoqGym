(**
This file is part of the Coquelicot formalization of real
analysis in Coq: http://coquelicot.saclay.inria.fr/

Copyright (C) 2011-2015 Sylvie Boldo
#<br />#
Copyright (C) 2011-2015 Catherine Lelay
#<br />#
Copyright (C) 2011-2015 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

Require Import Reals mathcomp.ssreflect.ssreflect.
Require Import Rbar Hierarchy RInt Lim_seq Continuity Derive.
Require Import Rcomplements RInt_analysis.

(** This file describes improper integrals, such as integrals with an
infinity endpoint or integrals of a function with a singularity. A few
properties are given: Chasles, operations, composition, derivation.*)

Open Scope R_scope.

(** * Improper Riemann integral *)

Section is_RInt_gen.

Context {V : NormedModule R_AbsRing}.

Definition is_RInt_gen (f : R -> V) (Fa Fb : (R -> Prop) -> Prop) (l : V) :=
  filterlimi (fun ab => is_RInt f (fst ab) (snd ab)) (filter_prod Fa Fb) (locally l).
Definition ex_RInt_gen (f : R -> V) (Fa Fb : (R -> Prop) -> Prop) :=
  exists l : V, is_RInt_gen f Fa Fb l.

Definition is_RInt_gen_at_point f a b l :
  is_RInt_gen f (at_point a) (at_point b) l
    <-> is_RInt f a b l.
Proof.
split.
- intros H P HP.
  apply locally_locally in HP.
  specialize (H _ HP).
  destruct H as [Q R Qa Rb H].
  destruct (H a b Qa Rb) as [y [Hy1 Hy2]].
  now apply Hy1.
- intros Hl P HP.
  exists (fun x => x = a) (fun x => x = b) ; try easy.
  intros x y -> ->.
  exists l.
  apply (conj Hl).
  exact: locally_singleton.
Qed.

(** * Basic properties of integrals *)

Lemma is_RInt_gen_ext {Fa Fb : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFb : Filter Fb} (f g : R -> V) (l : V) :
  filter_prod Fa Fb (fun ab => forall x, Rmin (fst ab) (snd ab) < x < Rmax (fst ab) (snd ab)
                               -> f x = g x) ->
  is_RInt_gen f Fa Fb l -> is_RInt_gen g Fa Fb l.
Proof.
intros Heq.
apply: filterlimi_ext_loc.
apply: filter_imp Heq.
intros [a b] Heq y.
split.
now apply is_RInt_ext.
apply is_RInt_ext.
intros x Hx.
now apply sym_eq, Heq.
Qed.

Lemma ex_RInt_gen_ext {Fa Fb : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFb : Filter Fb} (f g : R -> V) :
  filter_prod Fa Fb (fun ab => forall x, Rmin (fst ab) (snd ab) < x < Rmax (fst ab) (snd ab)
                               -> f x = g x) ->
  ex_RInt_gen f Fa Fb -> ex_RInt_gen g Fa Fb.
Proof.
move => Heq.
case => I HI.
exists I.
exact: (is_RInt_gen_ext f g).
Qed.

Lemma ex_RInt_gen_ext_eq {Fa Fb : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFb : Filter Fb} (f g : R -> V) :
  (forall x, f x = g x) -> ex_RInt_gen f Fa Fb -> ex_RInt_gen g Fa Fb.
Proof.
move => Heq.
apply: ex_RInt_gen_ext.
exact: filter_forall => bds x _.
Qed.

Lemma is_RInt_gen_point (f : R -> V) (a : R) :
  is_RInt_gen f (at_point a) (at_point a) zero.
Proof.
  apply is_RInt_gen_at_point.
  exact: is_RInt_point.
Qed.

Lemma is_RInt_gen_swap {Fa Fb : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFb : Filter Fb} (f : R -> V) (l : V) :
  is_RInt_gen f Fb Fa l -> is_RInt_gen f Fa Fb (opp l).
Proof.
intros Hf P HP.
specialize (Hf (fun y => P (opp y))).
destruct Hf as [Q R HQ HR H].
  exact: filterlim_opp.
apply: Filter_prod HR HQ _ => a b Ha Hb.
specialize (H b a Hb Ha).
destruct H as [y [Hy1 Hy2]].
exists (opp y).
split.
exact: is_RInt_swap.
exact Hy2.
Qed.

Lemma is_RInt_gen_Chasles {Fa Fc : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFc : Filter Fc}
  (f : R -> V) (b : R) (l1 l2 : V) :
  is_RInt_gen f Fa (at_point b) l1 -> is_RInt_gen f (at_point b) Fc l2
  -> is_RInt_gen f Fa Fc (plus l1 l2).
Proof.
intros Hab Hbc P HP.
specialize (filterlim_plus _ _ P HP).
intros [Q R HQ HR H].
specialize (Hab Q HQ).
specialize (Hbc R HR).
destruct Hab as [Qa Ra HQa HRa Hab].
destruct Hbc as [Qc Rc HQc HRc Hbc].
apply: Filter_prod HQa HRc _.
intros a c Ha Hc.
specialize (Hab _ _ Ha HRa).
specialize (Hbc _ _ HQc Hc).
destruct Hab as [ya [Hya1 Hya2]].
destruct Hbc as [yc [Hyc1 Hyc2]].
exists (plus ya yc).
split.
apply: is_RInt_Chasles Hya1 Hyc1.
now apply H.
Qed.

(** * Composition *)

(*
Lemma is_RInt_gen_comp_opp {Fa Fb : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFb : Filter Fb} (f : R -> V) (l : V) :
  is_RInt_gen f (filtermap opp Fa) (filtermap opp Fb) l ->
  is_RInt_gen (fun y => opp (f (- y))) Fa Fb l.
Proof.
intros H.
apply: filterlimi_ext.
unfold is_RInt_gen.
apply: filterlimi_comp_2.
apply filterlim_fst.
apply filterlim_snd.
SearchAbout fst filter_prod.

  case => If [Hf Hl].
  exists (fun x => If (opp x)) ; split.
  case: Hf => P Q ;
  unfold filtermap => Pa Qb H.
  eexists ; try eassumption.
  move => /= a b Ha Hb.
  by apply is_RInt_comp_opp, H.
  eapply filterlim_comp, Hl.
  intros P [Q1 Q2 Q1a Q2b H].
  eexists ; try eassumption.
  move => /= a b Ha Hb.
  by apply H.
Qed.

Lemma is_RInt_gen_comp_lin {Fa Fb : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFb : Filter Fb} (f : R -> V) (u v : R) (l : V) :
  is_RInt_gen f (filtermap (fun a => u * a + v) Fa) (filtermap (fun b => u * b + v) Fb) l
    -> is_RInt_gen (fun y => scal u (f (u * y + v))) Fa Fb l.
Proof.
  case => If [Hf Hl].
  exists (fun x => If (plus (scal u x) (v,v))) ; split.
  case: Hf => P Q ;
  unfold filtermap => Pa Qb H.
  eexists ; try eassumption.
  move => /= a b Ha Hb.
  by apply is_RInt_comp_lin, H.
  eapply filterlim_comp, Hl.
  intros P [Q1 Q2 Q1a Q2b H].
  eexists ; try eassumption.
  move => /= a b Ha Hb.
  by apply H.
Qed.
*)

(** * Operations *)

Lemma is_RInt_gen_scal {Fa Fb : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFb : Filter Fb} (f : R -> V) (k : R) (l : V) :
  is_RInt_gen f Fa Fb l ->
  is_RInt_gen (fun y => scal k (f y)) Fa Fb (scal k l).
Proof.
intros H P HP.
move /filterlim_scal_r in HP.
specialize (H _ HP).
unfold filtermapi in H |- *.
apply: filter_imp H.
move => [a b] /= [y [Hy1 Hy2]].
exists (scal k y).
apply: conj Hy2.
exact: is_RInt_scal.
Qed.

Lemma is_RInt_gen_opp {Fa Fb : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFb : Filter Fb} (f : R -> V) (l : V) :
  is_RInt_gen f Fa Fb l ->
  is_RInt_gen (fun y => opp (f y)) Fa Fb (opp l).
Proof.
intros H P HP.
move /filterlim_opp in HP.
specialize (H _ HP).
unfold filtermapi in H |- *.
apply: filter_imp H.
move => [a b] /= [y [Hy1 Hy2]].
exists (opp y).
apply: conj Hy2.
exact: is_RInt_opp.
Qed.

Lemma is_RInt_gen_plus {Fa Fb : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFb : Filter Fb} (f g : R -> V) (lf lg : V) :
  is_RInt_gen f Fa Fb lf ->
  is_RInt_gen g Fa Fb lg ->
  is_RInt_gen (fun y => plus (f y) (g y)) Fa Fb (plus lf lg).
Proof.
intros Hf Hg P HP.
move /filterlim_plus in HP.
destruct HP as [Q R HQ HR H].
specialize (Hf _ HQ).
specialize (Hg _ HR).
unfold filtermapi in Hf, Hg |- *.
apply: filter_imp (filter_and _ _ Hf Hg).
move => [a b] /= [[If [HIf1 HIf2]] [Ig [HIg1 HIg2]]].
exists (plus If Ig).
apply: conj (H _ _ HIf2 HIg2).
exact: is_RInt_plus.
Qed.

Lemma is_RInt_gen_minus {Fa Fb : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFb : Filter Fb} (f g : R -> V) (lf lg : V) :
  is_RInt_gen f Fa Fb lf ->
  is_RInt_gen g Fa Fb lg ->
  is_RInt_gen (fun y => minus (f y) (g y)) Fa Fb (minus lf lg).
Proof.
intros Hf Hg.
apply: is_RInt_gen_plus Hf _.
exact: is_RInt_gen_opp.
Qed.

End is_RInt_gen.

Section RInt_gen.

Context {V : CompleteNormedModule R_AbsRing}.

Definition RInt_gen (f : R -> V) (a b : (R -> Prop) -> Prop) :=
  iota (is_RInt_gen f a b).

Lemma is_RInt_gen_unique {Fa Fb : (R -> Prop) -> Prop}
  {FFa : ProperFilter' Fa} {FFb : ProperFilter' Fb} (f : R -> V) (l : V) :
  is_RInt_gen f Fa Fb l -> RInt_gen f Fa Fb = l.
Proof.
apply iota_filterlimi_locally.
apply filter_forall.
intros [a b] y1 u2 H1 H2.
rewrite -(is_RInt_unique _ _ _ _ H1).
now apply is_RInt_unique.
Qed.

Lemma RInt_gen_correct {Fa Fb : (R -> Prop) -> Prop}
  {FFa : ProperFilter' Fa} {FFb : ProperFilter' Fb} (f : R -> V) :
  ex_RInt_gen f Fa Fb -> is_RInt_gen f Fa Fb (RInt_gen f Fa Fb).
Proof.
intros [If HIf].
erewrite is_RInt_gen_unique ; exact HIf.
Qed.

Lemma RInt_gen_norm {Fa Fb : (R -> Prop) -> Prop}
  {FFa : ProperFilter Fa} {FFb : ProperFilter Fb} (f : R -> V) (g : R -> R) (lf : V) (lg : R) :
  filter_prod Fa Fb (fun ab => fst ab <= snd ab) ->
  filter_prod Fa Fb (fun ab => forall x, fst ab <= x <= snd ab -> norm (f x) <= g x) ->
  is_RInt_gen f Fa Fb lf -> is_RInt_gen g Fa Fb lg ->
  norm lf <= lg.
Proof.
intros Hab Hle Hf Hg.
apply (filterlim_le (F := filter_prod Fa Fb) (fun ab => norm (RInt f (fst ab) (snd ab))) (fun ab => RInt g (fst ab) (snd ab)) (norm lf) lg).
- specialize (Hf _ (locally_ball lf (mkposreal _ Rlt_0_1))).
  specialize (Hg _ (locally_ball lg (mkposreal _ Rlt_0_1))).
  unfold filtermapi in Hf, Hg.
  apply: filter_imp (filter_and _ _ (filter_and  _ _ Hf Hg) (filter_and _ _ Hab Hle)) => {Hf Hg Hab Hle}.
  move => [a b] /= [[[If [Hf1 Hf2]] [Ig [Hg1 Hg2]]] [H H']].
  apply: norm_RInt_le H H' _ _.
  apply: RInt_correct.
  now exists If.
  apply: RInt_correct.
  now exists Ig.
- eapply filterlim_comp, filterlim_norm.
  intros P HP.
  specialize (Hf P HP).
  unfold filtermapi, filtermap in Hf |- *.
  apply: filter_imp Hf.
  move => [a b] /= [y [Hy1 Hy2]].
  now rewrite (is_RInt_unique _ a b y Hy1).
- intros P HP.
  specialize (Hg P HP).
  unfold filtermapi, filtermap in Hg |- *.
  apply: filter_imp Hg.
  move => [a b] /= [y [Hy1 Hy2]].
  now rewrite (is_RInt_unique _ a b y Hy1).
Qed.

Lemma RInt_gen_ext {Fa Fb : (R -> Prop) -> Prop}
  {FFa : ProperFilter Fa} {FFb : ProperFilter Fb} (f g : R -> V) :
  filter_prod Fa Fb (fun ab => forall x, Rmin (fst ab) (snd ab) < x < Rmax (fst ab) (snd ab)
                               -> f x = g x) ->
  ex_RInt_gen f Fa Fb -> RInt_gen f Fa Fb = RInt_gen g Fa Fb.
Proof.
move => Heq [I HI].
rewrite (is_RInt_gen_unique f I HI); symmetry.
apply is_RInt_gen_unique. (* 'apply:' does not work *)
by apply: is_RInt_gen_ext; first exact: Heq.
Qed.

Lemma RInt_gen_ext_eq {Fa Fb : (R -> Prop) -> Prop}
  {FFa : ProperFilter Fa} {FFb : ProperFilter Fb} (f g : R -> V):
  (forall x, f x = g x) ->
  ex_RInt_gen f Fa Fb -> RInt_gen f Fa Fb = RInt_gen g Fa Fb.
Proof.
move => Heq.
apply: (RInt_gen_ext f g).
exact: filter_forall => bnds x _.
Qed.

End RInt_gen.

Lemma is_RInt_gen_Derive {Fa Fb : (R -> Prop) -> Prop} {FFa : Filter Fa} {FFb : Filter Fb}
  (f : R -> R) (la lb : R) :
  filter_prod Fa Fb
    (fun ab => forall x : R, Rmin (fst ab) (snd ab) <= x <= Rmax (fst ab) (snd ab) -> ex_derive f x)
  -> filter_prod Fa Fb
    (fun ab => forall x : R, Rmin (fst ab) (snd ab) <= x <= Rmax (fst ab) (snd ab) -> continuous (Derive f) x)
  -> filterlim f Fa (locally la) -> filterlim f Fb (locally lb)
  -> is_RInt_gen (Derive f) Fa Fb (lb - la).
Proof.
intros Df Cf Lfa Lfb P HP.
assert (HP': filter_prod Fa Fb (fun ab => P (f (snd ab) - f (fst ab)))).
  unfold Rminus.
  eapply filterlim_comp_2.
  eapply filterlim_comp, Lfb.
  by apply filterlim_snd.
  eapply filterlim_comp, @filterlim_opp.
  eapply filterlim_comp, Lfa.
  by apply filterlim_fst.
  exact: (filterlim_plus lb (- la)).
  exact HP.
apply: filter_imp (filter_and _ _ (filter_and _ _ Df Cf) HP').
move => [a b] /= {Df Cf HP HP'} [[Df Cf] HP].
eexists.
apply: conj HP.
apply: is_RInt_derive => x Hx.
now apply Derive_correct, Df.
exact: Cf.
Qed.

Section Complements_RInt_gen.

Context {V : CompleteNormedModule R_AbsRing}.

Lemma ex_RInt_gen_at_point f a b : @ex_RInt_gen V f (at_point a) (at_point b) <-> ex_RInt f a b.
Proof.
split;  case => I.
  rewrite is_RInt_gen_at_point => HI.
  by exists I.
rewrite -is_RInt_gen_at_point => HI.
  by exists I.
Qed.

Lemma RInt_gen_at_point f a b :
  ex_RInt f a b -> @RInt_gen V f (at_point a) (at_point b) = RInt f a b.
Proof.
move => Hfint.
apply is_RInt_gen_unique.
apply is_RInt_gen_at_point.
exact: RInt_correct.
Qed.

End Complements_RInt_gen.
