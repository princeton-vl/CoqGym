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
Require Import Rcomplements Rbar Markov Iter Lub.

(** This file first describes [Filter]s that are predicates of type
[(T -> Prop) -> Prop] used for limits and neighborhoods.  Then the
algebraic hierarchy of the Coquelicot library is given: from the
[AbelianGroup] to the [CompleteNormedModule]. Topologies on [R] and
[R*R] are also given.

 #<br/># More documentation details can be found in #<a
  href="Coquelicot.Coquelicot.html">Coquelicot.html</a>#. *)

Open Scope R_scope.

(** * Filters *)

(** ** Definitions *)

Class Filter {T : Type} (F : (T -> Prop) -> Prop) := {
  filter_true : F (fun _ => True) ;
  filter_and : forall P Q : T -> Prop, F P -> F Q -> F (fun x => P x /\ Q x) ;
  filter_imp : forall P Q : T -> Prop, (forall x, P x -> Q x) -> F P -> F Q
}.

Global Hint Mode Filter + + : typeclass_instances.

Class ProperFilter' {T : Type} (F : (T -> Prop) -> Prop) := {
  filter_not_empty : not (F (fun _ => False)) ;
  filter_filter' :> Filter F
}.

Class ProperFilter {T : Type} (F : (T -> Prop) -> Prop) := {
  filter_ex : forall P, F P -> exists x, P x ;
  filter_filter :> Filter F
}.

Global Instance Proper_StrongProper :
  forall {T : Type} (F : (T -> Prop) -> Prop),
  ProperFilter F -> ProperFilter' F.
Proof.
intros T F [H1 H2].
constructor.
intros H.
now destruct (H1 _ H) as [x Hx].
exact H2.
Qed.

Lemma filter_forall :
  forall {T : Type} {F} {FF: @Filter T F} (P : T -> Prop),
  (forall x, P x) -> F P.
Proof.
intros T F FF P H.
apply filter_imp with (fun _ => True).
easy.
apply filter_true.
Qed.

Lemma filter_const :
  forall {T : Type} {F} {FF: @ProperFilter T F} (P : Prop),
  F (fun _ => P) -> P.
Proof.
intros T F FF P H.
destruct (filter_ex (fun _ => P) H) as [_ H'].
exact H'.
Qed.

(** ** Limits expressed with filters *)

Definition filter_le {T : Type} (F G : (T -> Prop) -> Prop) :=
  forall P, G P -> F P.

Lemma filter_le_refl :
  forall T F, @filter_le T F F.
Proof.
now intros T F P.
Qed.

Lemma filter_le_trans :
  forall T F G H, @filter_le T F G -> filter_le G H -> filter_le F H.
Proof.
intros T F G H FG GH P K.
now apply FG, GH.
Qed.

Definition filtermap {T U : Type} (f : T -> U) (F : (T -> Prop) -> Prop) :=
  fun P => F (fun x => P (f x)).

Global Instance filtermap_filter :
  forall T U (f : T -> U) (F : (T -> Prop) -> Prop),
  Filter F -> Filter (filtermap f F).
Proof.
intros T U f F FF.
unfold filtermap.
constructor.
- apply filter_true.
- intros P Q HP HQ.
  now apply filter_and.
- intros P Q H HP.
  apply (filter_imp (fun x => P (f x))).
  intros x Hx.
  now apply H.
  exact HP.
Qed.

Global Instance filtermap_proper_filter' :
  forall T U (f : T -> U) (F : (T -> Prop) -> Prop),
  ProperFilter' F -> ProperFilter' (filtermap f F).
Proof.
intros T U f F FF.
unfold filtermap.
split.
- apply filter_not_empty.
- apply filtermap_filter.
  apply filter_filter'.
Qed.

Global Instance filtermap_proper_filter :
  forall T U (f : T -> U) (F : (T -> Prop) -> Prop),
  ProperFilter F -> ProperFilter (filtermap f F).
Proof.
intros T U f F FF.
unfold filtermap.
split.
- intros P FP.
  destruct (filter_ex _ FP) as [x Hx].
  now exists (f x).
- apply filtermap_filter.
  apply filter_filter.
Qed.

Definition filtermapi {T U : Type} (f : T -> U -> Prop) (F : (T -> Prop) -> Prop) :=
  fun P : U -> Prop => F (fun x => exists y, f x y /\ P y).

Global Instance filtermapi_filter :
  forall T U (f : T -> U -> Prop) (F : (T -> Prop) -> Prop),
  F (fun x => (exists y, f x y) /\ forall y1 y2, f x y1 -> f x y2 -> y1 = y2) ->
  Filter F -> Filter (filtermapi f F).
Proof.
intros T U f F H FF.
unfold filtermapi.
constructor.
- apply: filter_imp H => x [[y Hy] H].
  exists y.
  exact (conj Hy I).
- intros P Q HP HQ.
  apply: filter_imp (filter_and _ _ (filter_and _ _ HP HQ) H).
  intros x [[[y1 [Hy1 Py]] [y2 [Hy2 Qy]]] [[y Hy] Hf]].
  exists y.
  apply (conj Hy).
  split.
  now rewrite (Hf y y1).
  now rewrite (Hf y y2).
- intros P Q HPQ HP.
  apply: filter_imp HP.
  intros x [y [Hf Py]].
  exists y.
  apply (conj Hf).
  now apply HPQ.
Qed.

Global Instance filtermapi_proper_filter' :
  forall T U (f : T -> U -> Prop) (F : (T -> Prop) -> Prop),
  F (fun x => (exists y, f x y) /\ forall y1 y2, f x y1 -> f x y2 -> y1 = y2) ->
  ProperFilter' F -> ProperFilter' (filtermapi f F).
Proof.
intros T U f F HF FF.
unfold filtermapi.
split.
- intro H.
  apply filter_not_empty.
  apply filter_imp with (2 := H).
  now intros x [y [_ Hy]].
- apply filtermapi_filter.
  exact HF.
  apply filter_filter'.
Qed.

Global Instance filtermapi_proper_filter :
  forall T U (f : T -> U -> Prop) (F : (T -> Prop) -> Prop),
  F (fun x => (exists y, f x y) /\ forall y1 y2, f x y1 -> f x y2 -> y1 = y2) ->
  ProperFilter F -> ProperFilter (filtermapi f F).
Proof.
intros T U f F HF FF.
unfold filtermapi.
split.
- intros P FP.
  destruct (filter_ex _ FP) as [x [y [_ Hy]]].
  now exists y.
- apply filtermapi_filter.
  exact HF.
  apply filter_filter.
Qed.

Definition filterlim {T U : Type} (f : T -> U) F G :=
  filter_le (filtermap f F) G.

Lemma filterlim_id :
  forall T (F : (T -> Prop) -> Prop), filterlim (fun x => x) F F.
Proof.
now intros T F P HP.
Qed.

Lemma filterlim_comp :
  forall T U V (f : T -> U) (g : U -> V) F G H,
  filterlim f F G -> filterlim g G H ->
  filterlim (fun x => g (f x)) F H.
Proof.
intros T U V f g F G H FG GH P HP.
apply (FG (fun x => P (g x))).
now apply GH.
Qed.

Lemma filterlim_ext_loc :
  forall {T U F G} {FF : Filter F} (f g : T -> U),
  F (fun x => f x = g x) ->
  filterlim f F G ->
  filterlim g F G.
Proof.
intros T U F G FF f g Efg Lf P GP.
specialize (Lf P GP).
generalize (filter_and _ (fun x : T => P (f x)) Efg Lf).
unfold filtermap.
apply filter_imp.
now intros x [-> H].
Qed.

Lemma filterlim_ext :
  forall {T U F G} {FF : Filter F} (f g : T -> U),
  (forall x, f x = g x) ->
  filterlim f F G ->
  filterlim g F G.
Proof.
intros T U F G FF f g Efg.
apply filterlim_ext_loc.
now apply filter_forall.
Qed.

Lemma filterlim_filter_le_1 :
  forall {T U F G H} (f : T -> U),
  filter_le G F ->
  filterlim f F H ->
  filterlim f G H.
Proof.
intros T U F G H f K Hf P HP.
apply K.
now apply Hf.
Qed.

Lemma filterlim_filter_le_2 :
  forall {T U F G H} (f : T -> U),
  filter_le G H ->
  filterlim f F G ->
  filterlim f F H.
Proof.
intros T U F G H f K Hf P HP.
apply Hf.
now apply K.
Qed.

Definition filterlimi {T U : Type} (f : T -> U -> Prop) F G :=
  filter_le (filtermapi f F) G.

Lemma filterlimi_comp :
  forall T U V (f : T -> U) (g : U -> V -> Prop) F G H,
  filterlim f F G -> filterlimi g G H ->
  filterlimi (fun x => g (f x)) F H.
Proof.
intros T U V f g F G H FG GH P HP.
apply (FG (fun x => exists y, g x y /\ P y)).
now apply GH.
Qed.

Lemma filterlimi_ext_loc :
  forall {T U F G} {FF : Filter F} (f g : T -> U -> Prop),
  F (fun x => forall y, f x y <-> g x y) ->
  filterlimi f F G ->
  filterlimi g F G.
Proof.
intros T U F G FF f g Efg Lf P GP.
specialize (Lf P GP).
generalize (filter_and _ _ Efg Lf).
unfold filtermapi.
apply filter_imp.
intros x [H [y [Hy1 Hy2]]].
exists y.
apply: conj Hy2.
now apply H.
Qed.

Lemma filterlimi_ext :
  forall {T U F G} {FF : Filter F} (f g : T -> U -> Prop),
  (forall x y, f x y <-> g x y) ->
  filterlimi f F G ->
  filterlimi g F G.
Proof.
intros T U F G FF f g Efg.
apply filterlimi_ext_loc.
now apply filter_forall.
Qed.

Lemma filterlimi_filter_le_1 :
  forall {T U F G H} (f : T -> U -> Prop),
  filter_le G F ->
  filterlimi f F H ->
  filterlimi f G H.
Proof.
intros T U F G H f K Hf P HP.
apply K.
now apply Hf.
Qed.

Lemma filterlimi_filter_le_2 :
  forall {T U F G H} (f : T -> U -> Prop),
  filter_le G H ->
  filterlimi f F G ->
  filterlimi f F H.
Proof.
intros T U F G H f K Hf P HP.
apply Hf.
now apply K.
Qed.

(** ** Specific filters *)

(** Filters for pairs *)

Inductive filter_prod {T U : Type} (F G : _ -> Prop) (P : T * U -> Prop) : Prop :=
  Filter_prod (Q : T -> Prop) (R : U -> Prop) :
    F Q -> G R -> (forall x y, Q x -> R y -> P (x, y)) -> filter_prod F G P.

Global Instance filter_prod_filter :
  forall T U (F : (T -> Prop) -> Prop) (G : (U -> Prop) -> Prop),
  Filter F -> Filter G -> Filter (filter_prod F G).
Proof.
intros T U F G FF FG.
constructor.
- exists (fun _ => True) (fun _ => True).
  apply filter_true.
  apply filter_true.
  easy.
- intros P Q [AP BP P1 P2 P3] [AQ BQ Q1 Q2 Q3].
  exists (fun x => AP x /\ AQ x) (fun x => BP x /\ BQ x).
  now apply filter_and.
  now apply filter_and.
  intros x y [Px Qx] [Py Qy].
  split.
  now apply P3.
  now apply Q3.
- intros P Q HI [AP BP P1 P2 P3].
  exists AP BP ; try easy.
  intros x y Hx Hy.
  apply HI.
  now apply P3.
Qed.

Global Instance filter_prod_proper' {T1 T2 : Type}
  {F : (T1 -> Prop) -> Prop} {G : (T2 -> Prop) -> Prop}
  {FF : ProperFilter' F} {FG : ProperFilter' G} :
  ProperFilter' (filter_prod F G).
Proof.
  split.
  unfold not.
  apply filter_prod_ind.
  intros Q R HQ HR HQR.
  apply filter_not_empty.
  apply filter_imp with (2 := HR).
  intros y Hy.
  apply FF.
  apply filter_imp with (2 := HQ).
  intros x Hx.
  now apply (HQR x y).
  apply filter_prod_filter.
  apply FF.
  apply FG.
Qed.

Global Instance filter_prod_proper {T1 T2 : Type}
  {F : (T1 -> Prop) -> Prop} {G : (T2 -> Prop) -> Prop}
  {FF : ProperFilter F} {FG : ProperFilter G} :
  ProperFilter (filter_prod F G).
Proof.
  split.
  intros P [Q1 Q2 H1 H2 HP].
  case: (filter_ex _ H1) => x1 Hx1.
  case: (filter_ex _ H2) => x2 Hx2.
  exists (x1,x2).
  by apply HP.
  apply filter_prod_filter.
  apply FF.
  apply FG.
Qed.

Lemma filterlim_fst :
  forall {T U F G} {FG : Filter G},
  filterlim (@fst T U) (filter_prod F G) F.
Proof.
intros T U F G FG P HP.
exists P (fun _ => True) ; try easy.
apply filter_true.
Qed.

Lemma filterlim_snd :
  forall {T U F G} {FF : Filter F},
  filterlim (@snd T U) (filter_prod F G) G.
Proof.
intros T U F G FF P HP.
exists (fun _ => True) P ; try easy.
apply filter_true.
Qed.

Lemma filterlim_pair :
  forall {T U V F G H} {FF : Filter F},
  forall (f : T -> U) (g : T -> V),
  filterlim f F G ->
  filterlim g F H ->
  filterlim (fun x => (f x, g x)) F (filter_prod G H).
Proof.
intros T U V F G H FF f g Cf Cg P [A B GA HB HP].
unfold filtermap.
apply (filter_imp (fun x => A (f x) /\ B (g x))).
intros x [Af Bg].
now apply HP.
apply filter_and.
now apply Cf.
now apply Cg.
Qed.

Lemma filterlim_comp_2 :
  forall {T U V W F G H I} {FF : Filter F},
  forall (f : T -> U) (g : T -> V) (h : U -> V -> W),
  filterlim f F G ->
  filterlim g F H ->
  filterlim (fun x => h (fst x) (snd x)) (filter_prod G H) I ->
  filterlim (fun x => h (f x) (g x)) F I.
Proof.
intros T U V W F G H I FF f g h Cf Cg Ch.
change (fun x => h (f x) (g x)) with (fun x => h (fst (f x, g x)) (snd (f x, g x))).
apply: filterlim_comp Ch.
now apply filterlim_pair.
Qed.

Lemma filterlimi_comp_2 :
  forall {T U V W F G H I} {FF : Filter F},
  forall (f : T -> U) (g : T -> V) (h : U -> V -> W -> Prop),
  filterlim f F G ->
  filterlim g F H ->
  filterlimi (fun x => h (fst x) (snd x)) (filter_prod G H) I ->
  filterlimi (fun x => h (f x) (g x)) F I.
Proof.
intros T U V W F G H I FF f g h Cf Cg Ch.
change (fun x => h (f x) (g x)) with (fun x => h (fst (f x, g x)) (snd (f x, g x))).
apply: filterlimi_comp Ch.
now apply filterlim_pair.
Qed.

(** Restriction of a filter to a domain *)

Definition within {T : Type} D (F : (T -> Prop) -> Prop) (P : T -> Prop) :=
  F (fun x => D x -> P x).

Global Instance within_filter :
  forall T D F, Filter F -> Filter (@within T D F).
Proof.
intros T D F FF.
unfold within.
constructor.
- now apply filter_forall.
- intros P Q WP WQ.
  apply filter_imp with (fun x => (D x -> P x) /\ (D x -> Q x)).
  intros x [HP HQ] HD.
  split.
  now apply HP.
  now apply HQ.
  now apply filter_and.
- intros P Q H FP.
  apply filter_imp with (fun x => (D x -> P x) /\ (P x -> Q x)).
  intros x [H1 H2] HD.
  apply H2, H1, HD.
  apply filter_and.
  exact FP.
  now apply filter_forall.
Qed.

Lemma filter_le_within :
  forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} D,
  filter_le (within D F) F.
Proof.
intros T F D P HP.
unfold within.
now apply filter_imp.
Qed.

Lemma filterlim_within_ext :
  forall {T U F G} {FF : Filter F} D (f g : T -> U),
  (forall x, D x -> f x = g x) ->
  filterlim f (within D F) G ->
  filterlim g (within D F) G.
Proof.
intros T U F G FF D f g Efg.
apply filterlim_ext_loc.
unfold within.
now apply filter_forall.
Qed.

Definition subset_filter {T} (F : (T -> Prop) -> Prop) (dom : T -> Prop) (P : {x|dom x} -> Prop) : Prop :=
  F (fun x => forall H : dom x, P (exist _ x H)).

Global Instance subset_filter_filter :
  forall T F (dom : T -> Prop),
  Filter F ->
  Filter (subset_filter F dom).
Proof.
intros T F dom FF.
constructor ; unfold subset_filter.
- now apply filter_imp with (2 := filter_true).
- intros P Q HP HQ.
  generalize (filter_and _ _ HP HQ).
  apply filter_imp.
  intros x [H1 H2] H.
  now split.
- intros P Q H.
  apply filter_imp.
  intros x H' H0.
  now apply H.
Qed.

Lemma subset_filter_proper' :
  forall {T F} {FF : Filter F} (dom : T -> Prop),
  (forall P, F P -> ~ ~ exists x, dom x /\ P x) ->
  ProperFilter' (subset_filter F dom).
Proof.
intros T F FF dom.
constructor.
2: now apply subset_filter_filter.
intro H1.
unfold subset_filter in H1.
specialize (H (fun x : T => dom x -> False)).
apply H in H1.
apply H1.
clear H ; clear H1.
intro H2.
destruct H2 as (x, Hx).
destruct Hx as (Hx1, Hx2) ; now apply Hx2.
Qed.

Lemma subset_filter_proper :
  forall {T F} {FF : Filter F} (dom : T -> Prop),
  (forall P, F P -> exists x, dom x /\ P x) ->
  ProperFilter (subset_filter F dom).
Proof.
intros T F dom FF H.
constructor.
- unfold subset_filter.
  intros P HP.
  destruct (H _ HP) as [x [H1 H2]].
  exists (exist _ x H1).
  now apply H2.
- now apply subset_filter_filter.
Qed.

(** * Algebraic spaces *)
(** ** Abelian groups *)

Module AbelianGroup.

Record mixin_of (G : Type) := Mixin {
  plus : G -> G -> G ;
  opp : G -> G ;
  zero : G ;
  ax1 : forall x y, plus x y = plus y x ;
  ax2 : forall x y z, plus x (plus y z) = plus (plus x y) z ;
  ax3 : forall x, plus x zero = x ;
  ax4 : forall x, plus x (opp x) = zero
}.

Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.
Definition class (cT : type) := let: Pack _ c _ := cT return class_of cT in c.

End ClassDef.

Module Exports.

Coercion sort : type >-> Sortclass.
Notation AbelianGroup := type.

End Exports.

End AbelianGroup.

Export AbelianGroup.Exports.

(** Arithmetic operations *)

Section AbelianGroup1.

Context {G : AbelianGroup}.

Definition zero := AbelianGroup.zero _ (AbelianGroup.class G).
Definition plus := AbelianGroup.plus _ (AbelianGroup.class G).
Definition opp := AbelianGroup.opp _ (AbelianGroup.class G).
Definition minus x y := (plus x (opp y)).

Lemma plus_comm :
  forall x y : G,
  plus x y = plus y x.
Proof.
apply AbelianGroup.ax1.
Qed.

Lemma plus_assoc :
  forall x y z : G,
  plus x (plus y z) = plus (plus x y) z.
Proof.
apply AbelianGroup.ax2.
Qed.

Lemma plus_zero_r :
  forall x : G,
  plus x zero = x.
Proof.
apply AbelianGroup.ax3.
Qed.

Lemma plus_opp_r :
  forall x : G,
  plus x (opp x) = zero.
Proof.
apply AbelianGroup.ax4.
Qed.

Lemma plus_zero_l :
  forall x : G,
  plus zero x = x.
Proof.
intros x.
now rewrite plus_comm plus_zero_r.
Qed.

Lemma plus_opp_l :
  forall x : G,
  plus (opp x) x = zero.
Proof.
intros x.
rewrite plus_comm.
apply plus_opp_r.
Qed.

Lemma opp_zero :
  opp zero = zero.
Proof.
rewrite <- (plus_zero_r (opp zero)).
apply plus_opp_l.
Qed.

Lemma minus_zero_r :
  forall x : G,
  minus x zero = x.
Proof.
intros x.
unfold minus.
rewrite opp_zero.
apply plus_zero_r.
Qed.

Lemma minus_eq_zero (x : G) :
  minus x x = zero.
Proof.
  apply plus_opp_r.
Qed.

Lemma plus_reg_l :
  forall r x y : G,
  plus r x = plus r y -> x = y.
Proof.
intros r x y H.
rewrite -(plus_zero_l x) -(plus_opp_l r) -plus_assoc.
rewrite H.
now rewrite plus_assoc plus_opp_l plus_zero_l.
Qed.
Lemma plus_reg_r :
  forall r x y : G,
  plus x r = plus y r -> x = y.
Proof.
intros z x y.
rewrite !(plus_comm _ z).
by apply plus_reg_l.
Qed.

Lemma opp_opp :
  forall x : G,
  opp (opp x) = x.
Proof.
intros x.
apply plus_reg_r with (opp x).
rewrite plus_opp_r.
apply plus_opp_l.
Qed.

Lemma opp_plus :
  forall x y : G,
  opp (plus x y) = plus (opp x) (opp y).
Proof.
intros x y.
apply plus_reg_r with (plus x y).
rewrite plus_opp_l.
rewrite plus_assoc.
rewrite (plus_comm (opp x)).
rewrite <- (plus_assoc (opp y)).
rewrite plus_opp_l.
rewrite plus_zero_r.
apply sym_eq, plus_opp_l.
Qed.
Lemma opp_minus (x y : G) :
  opp (minus x y) = minus y x.
Proof.
  rewrite /minus opp_plus opp_opp.
  by apply plus_comm.
Qed.

Lemma minus_trans (r x y : G) :
  minus x y = plus (minus x r) (minus r y).
Proof.
  rewrite /minus -!plus_assoc.
  apply f_equal.
  by rewrite plus_assoc plus_opp_l plus_zero_l.
Qed.

End AbelianGroup1.

(** Sum *)

Section Sums.

Context {G : AbelianGroup}.

Definition sum_n_m (a : nat -> G) n m :=
  iter_nat plus zero a n m.
Definition sum_n (a : nat -> G) n :=
  sum_n_m a O n.

Lemma sum_n_m_Chasles (a : nat -> G) (n m k : nat) :
  (n <= S m)%nat -> (m <= k)%nat
    -> sum_n_m a n k = plus (sum_n_m a n m) (sum_n_m a (S m) k).
Proof.
  intros Hnm Hmk.
  apply iter_nat_Chasles.
  by apply plus_zero_l.
  by apply plus_assoc.
  by [].
  by [].
Qed.

Lemma sum_n_n (a : nat -> G) (n : nat) :
  sum_n_m a n n = a n.
Proof.
  apply iter_nat_point.
  by apply plus_zero_r.
Qed.
Lemma sum_O (a : nat -> G) : sum_n a 0 = a O.
Proof.
  by apply sum_n_n.
Qed.
Lemma sum_n_Sm (a : nat -> G) (n m : nat) :
  (n <= S m)%nat -> sum_n_m a n (S m) = plus (sum_n_m a n m) (a (S m)).
Proof.
  intros Hnmk.
  rewrite (sum_n_m_Chasles _ _ m).
  by rewrite sum_n_n.
  by [].
  by apply le_n_Sn.
Qed.
Lemma sum_Sn_m (a : nat -> G) (n m : nat) :
  (n <= m)%nat -> sum_n_m a n m = plus (a n) (sum_n_m a (S n) m).
Proof.
  intros Hnmk.
  rewrite (sum_n_m_Chasles _ _ n).
  by rewrite sum_n_n.
  by apply le_n_Sn.
  by [].
Qed.
Lemma sum_n_m_S (a : nat -> G) (n m : nat) :
  sum_n_m (fun n => a (S n)) n m = sum_n_m a (S n) (S m).
Proof.
  apply iter_nat_S.
Qed.

Lemma sum_Sn (a : nat -> G) (n : nat) :
  sum_n a (S n) = plus (sum_n a n) (a (S n)).
Proof.
  apply sum_n_Sm.
  by apply le_O_n.
Qed.

Lemma sum_n_m_zero (a : nat -> G) (n m : nat) :
  (m < n)%nat -> sum_n_m a n m = zero.
Proof.
  intros Hnm.
  rewrite /sum_n_m.
  elim: n m a Hnm => [ | n IH] m a Hnm.
  by apply lt_n_O in Hnm.
  case: m Hnm => [|m] Hnm //.
  rewrite -iter_nat_S.
  apply IH.
  by apply lt_S_n.
Qed.
Lemma sum_n_m_const_zero (n m : nat) :
  sum_n_m (fun _ => zero) n m = zero.
Proof.
  rewrite /sum_n_m /iter_nat.
  elim: (seq.iota n (S m - n)) => //= h t ->.
  by apply plus_zero_l.
Qed.

Lemma sum_n_m_ext_loc (a b : nat -> G) (n m : nat) :
  (forall k, (n <= k <= m)%nat -> a k = b k) ->
  sum_n_m a n m = sum_n_m b n m.
Proof.
  intros.
  by apply iter_nat_ext_loc.
Qed.
Lemma sum_n_m_ext (a b : nat -> G) n m :
  (forall n, a n = b n) ->
  sum_n_m a n m = sum_n_m b n m.
Proof.
  intros H.
  by apply sum_n_m_ext_loc.
Qed.

Lemma sum_n_ext_loc :
  forall (a b : nat -> G) N,
  (forall n, (n <= N)%nat -> a n = b n) ->
  sum_n a N = sum_n b N.
Proof.
  intros a b N H.
  apply sum_n_m_ext_loc => k [ _ Hk].
  by apply H.
Qed.
Lemma sum_n_ext :
  forall (a b : nat -> G) N,
  (forall n, a n = b n) ->
  sum_n a N = sum_n b N.
Proof.
  intros a b N H.
  by apply sum_n_ext_loc.
Qed.

Lemma sum_n_m_plus :
  forall (u v : nat -> G) (n m : nat),
  sum_n_m (fun k => plus (u k) (v k)) n m = plus (sum_n_m u n m) (sum_n_m v n m).
Proof.
  intros u v n m.
  case: (le_dec n m) => Hnm.
  elim: m n u v Hnm => [ | m IH] ;
  case => [ | n] u v Hnm.
  by rewrite !sum_n_n.
  by apply le_Sn_O in Hnm.
  rewrite !sum_n_Sm ; try by apply le_O_n.
  rewrite IH.
  rewrite -2!plus_assoc.
  apply f_equal.
  rewrite plus_comm -plus_assoc.
  apply f_equal, plus_comm.
  by apply le_O_n.
  rewrite /sum_n_m -!iter_nat_S -!/(sum_n_m _ n m).
  apply IH.
  by apply le_S_n.
  apply not_le in Hnm.
  rewrite !sum_n_m_zero //.
  by rewrite plus_zero_l.
Qed.

Lemma sum_n_plus :
  forall (u v : nat -> G) (n : nat),
  sum_n (fun k => plus (u k) (v k)) n = plus (sum_n u n) (sum_n v n).
Proof.
  intros u v n.
  apply sum_n_m_plus.
Qed.

Lemma sum_n_switch :
  forall (u : nat -> nat -> G) (m n : nat),
  sum_n (fun i => sum_n (u i) n) m = sum_n (fun j => sum_n (fun i => u i j) m) n.
Proof.
  intros u.
  rewrite /sum_n.
  induction m ; simpl ; intros n.
  rewrite sum_n_n.
  apply iter_nat_ext_loc => k Hk.
  rewrite sum_n_n.
  by [].
  rewrite !sum_n_Sm.
  rewrite IHm ; clear IHm.
  rewrite -sum_n_m_plus.
  apply sum_n_m_ext_loc => k Hk.
  rewrite sum_n_Sm //.
  by apply le_O_n.
  by apply le_O_n.
Qed.

Lemma sum_n_m_sum_n (a:nat -> G) (n m : nat) :
  (n <= m)%nat -> sum_n_m a (S n) m = minus (sum_n a m) (sum_n a n).
Proof.
  intros Hnm.
  apply plus_reg_l with (sum_n a n).
  rewrite (plus_comm _ (minus _ _)) /minus -plus_assoc plus_opp_l plus_zero_r.
  rewrite /sum_n /sum_n_m.
  apply sym_eq, sum_n_m_Chasles.
  by apply le_O_n.
  by [].
Qed.

End Sums.

(** ** Noncommutative rings *)

Module Ring.

Record mixin_of (K : AbelianGroup) := Mixin {
  mult : K -> K -> K ;
  one : K ;
  ax1 : forall x y z, mult x (mult y z) = mult (mult x y) z ;
  ax2 : forall x, mult x one = x ;
  ax3 : forall x, mult one x = x ;
  ax4 : forall x y z, mult (plus x y) z = plus (mult x z) (mult y z) ;
  ax5 : forall x y z, mult x (plus y z) = plus (mult x y) (mult x z)
}.

Section ClassDef.

Record class_of (K : Type) := Class {
  base : AbelianGroup.class_of K ;
  mixin : mixin_of (AbelianGroup.Pack _ base K)
}.
Local Coercion base : class_of >-> AbelianGroup.class_of.

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.

Variable cT : type.

Definition class := let: Pack _ c _ := cT return class_of cT in c.

Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition AbelianGroup := AbelianGroup.Pack cT xclass xT.

End ClassDef.

Module Exports.

Coercion base : class_of >-> AbelianGroup.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion AbelianGroup : type >-> AbelianGroup.type.
Canonical AbelianGroup.
Notation Ring := type.

End Exports.

End Ring.

Export Ring.Exports.

(** Arithmetic operations *)

Section Ring1.

Context {K : Ring}.

Definition mult : K -> K -> K := Ring.mult _ (Ring.class K).
Definition one : K := Ring.one _ (Ring.class K).

Lemma mult_assoc :
  forall x y z : K,
  mult x (mult y z) = mult (mult x y) z.
Proof.
apply Ring.ax1.
Qed.

Lemma mult_one_r :
  forall x : K,
  mult x one = x.
Proof.
apply Ring.ax2.
Qed.

Lemma mult_one_l :
  forall x : K,
  mult one x = x.
Proof.
apply Ring.ax3.
Qed.

Lemma mult_distr_r :
  forall x y z : K,
  mult (plus x y) z = plus (mult x z) (mult y z).
Proof.
apply Ring.ax4.
Qed.

Lemma mult_distr_l :
  forall x y z : K,
  mult x (plus y z) = plus (mult x y) (mult x z).
Proof.
apply Ring.ax5.
Qed.

Lemma mult_zero_r :
  forall x : K,
  mult x zero = zero.
Proof.
intros x.
apply plus_reg_r with (mult x zero).
rewrite <- mult_distr_l.
rewrite plus_zero_r.
now rewrite plus_zero_l.
Qed.

Lemma mult_zero_l :
  forall x : K,
  mult zero x = zero.
Proof.
intros x.
apply plus_reg_r with (mult zero x).
rewrite <- mult_distr_r.
rewrite plus_zero_r.
now rewrite plus_zero_l.
Qed.

Lemma opp_mult_r :
  forall x y : K,
  opp (mult x y) = mult x (opp y).
Proof.
intros x y.
apply plus_reg_l with (mult x y).
rewrite plus_opp_r -mult_distr_l.
now rewrite plus_opp_r mult_zero_r.
Qed.

Lemma opp_mult_l :
  forall x y : K,
  opp (mult x y) = mult (opp x) y.
Proof.
intros x y.
apply plus_reg_l with (mult x y).
rewrite plus_opp_r -mult_distr_r.
now rewrite plus_opp_r mult_zero_l.
Qed.

Lemma opp_mult_m1 :
  forall x : K,
  opp x = mult (opp one) x.
Proof.
  intros x.
  rewrite -opp_mult_l opp_mult_r.
  by rewrite mult_one_l.
Qed.

Lemma sum_n_m_mult_r :
 forall (a : K) (u : nat -> K) (n m : nat),
  sum_n_m (fun k => mult (u k) a) n m = mult (sum_n_m u n m) a.
Proof.
  intros a u n m.
  case: (le_dec n m) => Hnm.
  elim: m n u Hnm => [ | m IH] n u Hnm.
  apply le_n_O_eq in Hnm.
  by rewrite -Hnm !sum_n_n.
  destruct n.
  rewrite !sum_n_Sm ; try by apply le_O_n.
  rewrite IH.
  by apply sym_eq, mult_distr_r.
  by apply le_O_n.
  rewrite -!sum_n_m_S.
  apply IH.
  by apply le_S_n.
  apply not_le in Hnm.
  rewrite !sum_n_m_zero //.
  by rewrite mult_zero_l.
Qed.

Lemma sum_n_m_mult_l :
 forall (a : K) (u : nat -> K) (n m : nat),
  sum_n_m (fun k => mult a (u k)) n m = mult a (sum_n_m u n m).
Proof.
  intros a u n m.
  case: (le_dec n m) => Hnm.
  elim: m n u Hnm => [ | m IH] n u Hnm.
  apply le_n_O_eq in Hnm.
  by rewrite -Hnm !sum_n_n.
  destruct n.
  rewrite !sum_n_Sm ; try by apply le_O_n.
  rewrite IH.
  by apply sym_eq, mult_distr_l.
  by apply le_O_n.
  rewrite -!sum_n_m_S.
  apply IH.
  by apply le_S_n.
  apply not_le in Hnm.
  rewrite !sum_n_m_zero //.
  by rewrite mult_zero_r.
Qed.

Lemma sum_n_mult_r :
 forall (a : K) (u : nat -> K) (n : nat),
  sum_n (fun k => mult (u k) a) n = mult (sum_n u n) a.
Proof.
  intros ; by apply sum_n_m_mult_r.
Qed.

Lemma sum_n_mult_l :
 forall (a : K) (u : nat -> K) (n : nat),
  sum_n (fun k => mult a (u k)) n = mult a (sum_n u n).
Proof.
  intros ; by apply sum_n_m_mult_l.
Qed.

(** pow_n *)

Fixpoint pow_n (x : K) (N : nat) {struct N} : K :=
  match N with
   | 0%nat => one
   | S i => mult x (pow_n x i)
  end.

Lemma pow_n_plus :
  forall (x : K) (n m : nat), pow_n x (n+m) = mult (pow_n x n) (pow_n x m).
Proof.
  intros x.
  elim => /= [ | n IH] m.
  by rewrite mult_one_l.
  by rewrite IH mult_assoc.
Qed.

Lemma pow_n_comm_1 :
  forall (x : K) (n : nat), mult (pow_n x n) x = mult x (pow_n x n).
Proof.
  intros x n.
  elim: n => /= [ | n IH].
  by rewrite mult_one_l mult_one_r.
  by rewrite -(mult_assoc _ (pow_n x n)) IH.
Qed.

Lemma pow_n_comm :
  forall (x : K) n m, mult (pow_n x n) (pow_n x m) = mult (pow_n x m) (pow_n x n).
Proof.
  intros x n m.
  rewrite -2!pow_n_plus.
  by apply f_equal, Plus.plus_comm.
Qed.

End Ring1.

(** ** Rings with absolute value *)

Module AbsRing.

Record mixin_of (K : Ring) := Mixin {
  abs : K -> R ;
  ax1 : abs zero = 0 ;
  ax2 : abs (opp one) = 1 ;
  ax3 : forall x y : K, abs (plus x y) <= abs x + abs y ;
  ax4 : forall x y : K, abs (mult x y) <= abs x * abs y ;
  ax5 : forall x : K, abs x = 0 -> x = zero
}.

Section ClassDef.

Record class_of (K : Type) := Class {
  base : Ring.class_of K ;
  mixin : mixin_of (Ring.Pack _ base K)
}.
Local Coercion base : class_of >-> Ring.class_of.

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.

Variable cT : type.

Definition class := let: Pack _ c _ := cT return class_of cT in c.

Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition AbelianGroup := AbelianGroup.Pack cT xclass xT.
Definition Ring := Ring.Pack cT xclass xT.

End ClassDef.

Module Exports.

Coercion base : class_of >-> Ring.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion AbelianGroup : type >-> AbelianGroup.type.
Canonical AbelianGroup.
Coercion Ring : type >-> Ring.type.
Canonical Ring.
Notation AbsRing := type.

End Exports.

End AbsRing.

Export AbsRing.Exports.

(** Usual properties *)

Section AbsRing1.

Context {K : AbsRing}.

Definition abs : K -> R := AbsRing.abs _ (AbsRing.class K).

Lemma abs_zero :
  abs zero = 0.
Proof.
apply AbsRing.ax1.
Qed.

Lemma abs_opp_one :
  abs (opp one) = 1.
Proof.
apply AbsRing.ax2.
Qed.

Lemma abs_triangle :
  forall x y : K,
  abs (plus x y) <= abs x + abs y.
Proof.
apply: AbsRing.ax3.
Qed.

Lemma abs_mult :
  forall x y : K,
  abs (mult x y) <= abs x * abs y.
Proof.
apply AbsRing.ax4.
Qed.

Lemma abs_eq_zero :
  forall x : K,
  abs x = 0 -> x = zero.
Proof.
apply AbsRing.ax5.
Qed.

Lemma abs_opp :
  forall x, abs (opp x) = abs x.
Proof.
intros x.
apply Rle_antisym.
- rewrite opp_mult_m1.
  rewrite -(Rmult_1_l (abs x)) -abs_opp_one.
  apply abs_mult.
- rewrite -{1}[x]opp_opp.
  rewrite opp_mult_m1.
  rewrite -(Rmult_1_l (abs (opp x))) -abs_opp_one.
  apply abs_mult.
Qed.

Lemma abs_minus :
  forall x y : K, abs (minus x y) = abs (minus y x).
Proof.
intros x y.
by rewrite /minus -abs_opp opp_plus opp_opp plus_comm.
Qed.

Lemma abs_one :
  abs one = 1.
Proof.
rewrite -abs_opp.
exact abs_opp_one.
Qed.

Lemma abs_ge_0 :
  forall x, 0 <= abs x.
Proof.
  intros x.
  apply Rmult_le_reg_l with 2.
  by apply Rlt_0_2.
  rewrite Rmult_0_r -abs_zero -(plus_opp_l x).
  apply Rle_trans with (1 := abs_triangle _ _).
  rewrite abs_opp.
  apply Req_le ; ring.
Qed.

Lemma abs_pow_n :
  forall (x : K) n,
  abs (pow_n x n) <= (abs x)^n.
Proof.
induction n.
apply Req_le, abs_one.
simpl.
apply: Rle_trans (abs_mult _ _) _.
apply Rmult_le_compat_l with (2 := IHn).
apply abs_ge_0.
Qed.

End AbsRing1.

(** * Uniform spaces defined using balls *)

Module UniformSpace.

Record mixin_of (M : Type) := Mixin {
  ball : M -> R -> M -> Prop ;
  ax1 : forall x (e : posreal), ball x e x ;
  ax2 : forall x y e, ball x e y -> ball y e x ;
  ax3 : forall x y z e1 e2, ball x e1 y -> ball y e2 z -> ball x (e1 + e2) z
}.

Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.
Definition class (cT : type) := let: Pack _ c _ := cT return class_of cT in c.

End ClassDef.

Module Exports.

Coercion sort : type >-> Sortclass.
Notation UniformSpace := type.

End Exports.

End UniformSpace.

Export UniformSpace.Exports.

Section UniformSpace1.

Context {M : UniformSpace}.

Definition ball := UniformSpace.ball _ (UniformSpace.class M).

Lemma ball_center :
  forall (x : M) (e : posreal),
  ball x e x.
Proof.
apply UniformSpace.ax1.
Qed.

Lemma ball_sym :
  forall (x y : M) (e : R),
  ball x e y -> ball y e x.
Proof.
apply UniformSpace.ax2.
Qed.

Lemma ball_triangle :
  forall (x y z : M) (e1 e2 : R),
  ball x e1 y -> ball y e2 z -> ball x (e1 + e2) z.
Proof.
apply UniformSpace.ax3.
Qed.

Lemma ball_le :
  forall (x : M) (e1 e2 : R), e1 <= e2 ->
  forall (y : M), ball x e1 y -> ball x e2 y.
Proof.
intros x e1 e2 H y H1.
destruct H.
assert (e2 - e1 > 0).
by apply Rgt_minus.
assert (ball y {| pos := (e2-e1); cond_pos := (H0) |} y).
apply ball_center.
replace e2 with (e1 + (e2 - e1)).
apply ball_triangle with y ; assumption.
by apply Rplus_minus.
by rewrite <- H.
Qed.

Definition close (x y : M) : Prop := forall eps : posreal, ball x eps y.

Lemma close_refl (x : M) : close x x.
Proof.
intros eps.
apply ball_center.
Qed.

Lemma close_sym (x y : M) : close x y -> close y x.
Proof.
intros H eps.
now apply ball_sym.
Qed.

Lemma close_trans (x y z : M) : close x y -> close y z -> close x z.
Proof.
intros H1 H2 eps.
rewrite (double_var eps) -[eps / 2]/(pos (pos_div_2 eps)).
now eapply ball_triangle.
Qed.

End UniformSpace1.

(** ** Specific uniform spaces *)

(** Rings with absolute value *)

Section AbsRing_UniformSpace.

Variable K : AbsRing.

Definition AbsRing_ball (x : K) (eps : R) (y : K) := abs (minus y x) < eps.

Lemma AbsRing_ball_center :
  forall (x : K) (e : posreal),
  AbsRing_ball x e x.
Proof.
  intros x e.
  rewrite /AbsRing_ball /minus plus_opp_r abs_zero.
  apply cond_pos.
Qed.

Lemma AbsRing_ball_sym :
  forall (x y : K) (e : R),
  AbsRing_ball x e y -> AbsRing_ball y e x.
Proof.
  intros x y e.
  by rewrite /AbsRing_ball abs_minus.
Qed.

Lemma AbsRing_ball_triangle :
  forall (x y z : K) (e1 e2 : R),
  AbsRing_ball x e1 y -> AbsRing_ball y e2 z ->
  AbsRing_ball x (e1 + e2) z.
Proof.
intros x y z e1 e2 H1 H2.
unfold AbsRing_ball.
replace (minus z x) with (plus (minus y x) (minus z y)).
apply: Rle_lt_trans (abs_triangle _ _) _.
now apply Rplus_lt_compat.
rewrite plus_comm /minus plus_assoc.
apply (f_equal (fun y => plus y _)).
rewrite <- plus_assoc.
now rewrite plus_opp_l plus_zero_r.
Qed.


Definition AbsRing_UniformSpace_mixin :=
  UniformSpace.Mixin _ _ AbsRing_ball_center AbsRing_ball_sym AbsRing_ball_triangle.

Canonical AbsRing_UniformSpace :=
  UniformSpace.Pack K AbsRing_UniformSpace_mixin K.

End AbsRing_UniformSpace.

(** Functional metric spaces *)

Section fct_UniformSpace.

Variable (T : Type) (U : UniformSpace).

Definition fct_ball (x : T -> U) (eps : R) (y : T -> U) :=
  forall t : T, ball (x t) eps (y t).

Lemma fct_ball_center :
  forall (x : T -> U) (e : posreal),
  fct_ball x e x.
Proof.
  intros x e t.
  exact: ball_center.
Qed.

Lemma fct_ball_sym :
  forall (x y : T -> U) (e : R),
  fct_ball x e y -> fct_ball y e x.
Proof.
  intros x y e H t.
  exact: ball_sym.
Qed.

Lemma fct_ball_triangle :
  forall (x y z : T -> U) (e1 e2 : R),
  fct_ball x e1 y -> fct_ball y e2 z -> fct_ball x (e1 + e2) z.
Proof.
  intros x y z e1 e2 H1 H2 t.
  now apply ball_triangle with (y t).
Qed.


Definition fct_UniformSpace_mixin :=
  UniformSpace.Mixin _ _ fct_ball_center fct_ball_sym fct_ball_triangle.

Canonical fct_UniformSpace :=
  UniformSpace.Pack (T -> U) fct_UniformSpace_mixin (T -> U).

End fct_UniformSpace.

(** ** Local predicates *)
(** locally_dist *)

Definition locally_dist {T : Type} (d : T -> R) (P : T -> Prop) :=
  exists delta : posreal, forall y, d y < delta -> P y.

Global Instance locally_dist_filter :
  forall T (d : T -> R), Filter (locally_dist d).
Proof.
intros T d.
constructor.
- now exists (mkposreal _ Rlt_0_1).
- intros P Q [dP HP] [dQ HQ].
  exists (mkposreal _ (Rmin_stable_in_posreal dP dQ)).
  simpl.
  intros y Hy.
  split.
  apply HP.
  apply Rlt_le_trans with (1 := Hy).
  apply Rmin_l.
  apply HQ.
  apply Rlt_le_trans with (1 := Hy).
  apply Rmin_r.
- intros P Q H [dP HP].
  exists dP.
  intros y Hy.
  apply H.
  now apply HP.
Qed.

(** locally *)

Section Locally.

Context {T : UniformSpace}.

Definition locally (x : T) (P : T -> Prop) :=
  exists eps : posreal, forall y, ball x eps y -> P y.

Global Instance locally_filter :
  forall x : T, ProperFilter (locally x).
Proof.
intros x.
constructor ; [idtac|constructor].
- intros P [eps H].
  exists x.
  apply H.
  apply ball_center.
- now exists (mkposreal _ Rlt_0_1).
- intros P Q [dP HP] [dQ HQ].
  exists (mkposreal _ (Rmin_stable_in_posreal dP dQ)).
  simpl.
  intros y Hy.
  split.
  apply HP.
  apply ball_le with (2 := Hy).
  apply Rmin_l.
  apply HQ.
  apply ball_le with (2 := Hy).
  apply Rmin_r.
- intros P Q H [dP HP].
  exists dP.
  intros y Hy.
  apply H.
  now apply HP.
Qed.

Lemma locally_locally :
  forall (x : T) (P : T -> Prop),
  locally x P -> locally x (fun y => locally y P).
Proof.
intros x P [dp Hp].
exists (pos_div_2 dp).
intros y Hy.
exists (pos_div_2 dp) => /= z Hz.
apply Hp.
rewrite (double_var dp).
now apply ball_triangle with y.
Qed.

Lemma locally_singleton :
  forall (x : T) (P : T -> Prop),
  locally x P -> P x.
Proof.
intros x P [dp H].
apply H.
by apply ball_center.
Qed.

Lemma locally_ball :
  forall (x : T) (eps : posreal), locally x (ball x eps).
Proof.
  intros x eps.
  now exists eps.
Qed.

Lemma locally_not' :
  forall (x : T) (P : T -> Prop),
  not (forall eps : posreal, not (forall y, ball x eps y -> not (P y))) ->
  {d : posreal | forall y, ball x d y -> not (P y)}.
Proof.
intros x P H.
set (Q := fun z => z <= 1 /\ forall y, ball x z y -> not (P y)).
destruct (completeness Q) as [d [H1 H2]].
- exists 1.
  now intros y [Hy _].
- exists 0.
  split.
  apply Rle_0_1.
  intros y Hy Py.
  apply H.
  intros eps He.
  apply He with (2 := Py).
  apply ball_le with (2 := Hy).
  apply Rlt_le, eps.
assert (Zd : 0 < d).
  apply Rnot_le_lt.
  intros Hd.
  apply H.
  intros eps He.
  apply (Rlt_irrefl (Rmin 1 eps)).
  apply Rle_lt_trans with d.
  apply H1.
  split.
  apply Rmin_l.
  intros y By.
  apply He.
  apply ball_le with (2 := By).
  apply Rmin_r.
  apply Rle_lt_trans with (1 := Hd).
  apply Rmin_case.
  apply Rlt_0_1.
  apply cond_pos.
exists (mkposreal _ (is_pos_div_2 (mkposreal _ Zd))).
simpl.
intros y Hy HP.
apply (Rlt_not_le _ _ (Rlt_eps2_eps _ Zd)).
apply H2.
intros z Hz.
apply Rnot_lt_le.
contradict HP.
apply Hz.
apply ball_le with (2 := Hy).
now apply Rlt_le.
Qed.

Lemma locally_not :
  forall (x : T) (P : T -> Prop),
  not (forall eps : posreal, not (forall y, ball x eps y -> not (P y))) ->
  locally x (fun y => not (P y)).
Proof.
intros x P H.
destruct (locally_not' x P H) as [eps He].
now exists eps.
Qed.

Lemma locally_ex_not :
  forall (x : T) (P : T -> Prop),
  locally x (fun y => not (P y)) ->
  {d : posreal | forall y, ball x d y -> not (P y)}.
Proof.
intros x P H.
apply locally_not'.
destruct H as [eps He].
intros H.
now apply (H eps).
Qed.

Lemma locally_ex_dec :
  forall (x : T) (P : T -> Prop),
  (forall x, P x \/ ~P x) ->
  locally x P ->
  {d : posreal | forall y, ball x d y -> P y}.
Proof.
intros x P P_dec H.
destruct (locally_ex_not x (fun y => not (P y))) as [d Hd].
apply: filter_imp H.
intros y Py HP.
now apply HP.
exists d.
intros y Hy.
destruct (P_dec y) as [HP|HP].
exact HP.
exfalso.
now apply (Hd y).
Qed.

Definition is_filter_lim (F : (T -> Prop) -> Prop) (x : T) :=
  forall P, locally x P -> F P.

Lemma is_filter_lim_filter_le :
  forall {F G} (x : T),
  filter_le G F ->
  is_filter_lim F x -> is_filter_lim G x.
Proof.
intros F G x L Fx P HP.
apply L.
now apply Fx.
Qed.

Lemma is_filter_lim_close {F} {FF : ProperFilter F} (x y : T) :
  is_filter_lim F x -> is_filter_lim F y -> close x y.
Proof.
  intros Hx Hy eps.
  specialize (Hy _ (locally_ball y (pos_div_2 eps))).
  specialize (Hx _ (locally_ball x (pos_div_2 eps))).
  generalize (filter_and _ _ Hx Hy) => {Hx Hy} H.
  destruct (filter_ex _ H) as [z Hz].
  rewrite (double_var eps).
  apply ball_triangle with z.
  apply Hz.
  apply ball_sym, Hz.
Qed.

Lemma is_filter_lim_locally_close (x y : T) :
  is_filter_lim (locally x) y -> close x y.
Proof.
  by apply is_filter_lim_close.
Qed.

End Locally.

Lemma filterlim_const :
  forall {T} {U : UniformSpace} {F : (T -> Prop) -> Prop} {FF : Filter F},
  forall a : U, filterlim (fun _ => a) F (locally a).
Proof.
intros T U F FF a P [eps HP].
unfold filtermap.
apply filter_forall.
intros _.
apply HP.
apply ball_center.
Qed.

Section Locally_fct.

Context {T : Type} {U : UniformSpace}.

Lemma filterlim_locally :
  forall {F} {FF : Filter F} (f : T -> U) y,
  filterlim f F (locally y) <->
  forall eps : posreal, F (fun x => ball y eps (f x)).
Proof.
intros F FF f y.
split.
- intros Cf eps.
  apply (Cf (fun x => ball y eps x)).
  now exists eps.
- intros Cf P [eps He].
  apply: filter_imp (Cf eps).
  intros t.
  apply He.
Qed.

Lemma filterlimi_locally :
  forall {F} {FF : Filter F} (f : T -> U -> Prop) y,
  filterlimi f F (locally y) <->
  forall eps : posreal, F (fun x => exists z, f x z /\ ball y eps z).
Proof.
intros F FF f y.
split.
- intros Cf eps.
  apply (Cf (fun x => ball y eps x)).
  now exists eps.
- intros Cf P [eps He].
  unfold filtermapi.
  apply: filter_imp (Cf eps).
  intros t [z [Hz1 Hz2]].
  exists z.
  apply (conj Hz1).
  now apply He.
Qed.

Lemma filterlim_locally_close :
  forall {F} {FF: ProperFilter F} (f : T -> U) l l',
  filterlim f F (locally l) ->  filterlim f F (locally l') ->
  close l l'.
Proof.
intros F FF f l l' Hl Hl' eps.
assert (locally l (ball l (pos_div_2 eps))).
  by apply locally_ball.
specialize (Hl (ball l (pos_div_2 eps)) H).
assert (locally l' (ball l' (pos_div_2 eps))).
  by apply locally_ball.
specialize (Hl' (ball l' (pos_div_2 eps)) H0).
unfold filtermap in Hl, Hl'.
generalize (filter_and _ _ Hl Hl') => {H H0} H.
apply filter_ex in H.
case: H => x H.
rewrite (double_var eps).
apply ball_triangle with (f x).
by apply H.
by apply ball_sym, H.
Qed.

Lemma filterlimi_locally_close :
  forall {F} {FF: ProperFilter F} (f : T -> U -> Prop) l l',
  F (fun x => forall y1 y2, f x y1 -> f x y2 -> y1 = y2) ->
  filterlimi f F (locally l) ->  filterlimi f F (locally l') ->
  close l l'.
Proof.
intros F FF f l l' Hf Hl Hl' eps.
assert (H: locally l (ball l (pos_div_2 eps))).
  by apply locally_ball.
specialize (Hl (ball l (pos_div_2 eps)) H).
assert (H': locally l' (ball l' (pos_div_2 eps))).
  by apply locally_ball.
specialize (Hl' (ball l' (pos_div_2 eps)) H').
unfold filtermapi in Hl, Hl'.
generalize (filter_and _ _ Hf (filter_and _ _ Hl Hl')) => {H H' Hl Hl' Hf} H.
apply filter_ex in H.
destruct H as [x [Hf [[y [H1 H1']] [y' [H2 H2']]]]].
rewrite (double_var eps).
apply ball_triangle with y.
exact H1'.
apply ball_sym.
rewrite (Hf _ _ H1 H2).
exact H2'.
Qed.

End Locally_fct.

Lemma is_filter_lim_filtermap {T: UniformSpace} {U : UniformSpace} :
forall F x (f : T -> U),
  filterlim f (locally x) (locally (f x))
  -> is_filter_lim F x
  -> is_filter_lim (filtermap f F) (f x).
Proof.
  intros F x f Cf Fx P HP.
  apply Cf in HP.
  now apply Fx.
Qed.

(** locally' *)

Definition locally' {T : UniformSpace} (x : T) :=
  within (fun y => y <> x) (locally x).

Global Instance locally'_filter :
  forall {T : UniformSpace} (x : T), Filter (locally' x).
Proof.
intros T x.
apply within_filter.
apply locally_filter.
Qed.

(** Pointed filter *)

Section at_point.

Context {T : UniformSpace}.

Definition at_point (a : T) (P : T -> Prop) : Prop := P a.

Global Instance at_point_filter (a : T) :
  ProperFilter (at_point a).
Proof.
split.
- intros P Pa.
  now exists a.
- split ; try easy.
  intros P Q PQ Ha.
  now apply PQ.
Qed.

End at_point.

(** ** Open sets in uniform spaces *)

Section Open.

Context {T : UniformSpace}.

Definition open (D : T -> Prop) :=
  forall x, D x -> locally x D.

Lemma locally_open :
  forall (D E : T -> Prop),
  open D ->
  (forall x : T, D x -> E x) ->
  forall x : T, D x ->
  locally x E.
Proof.
intros D E OD H x Dx.
apply filter_imp with (1 := H).
now apply OD.
Qed.

Lemma open_ext :
  forall D E : T -> Prop,
  (forall x, D x <-> E x) ->
  open D -> open E.
Proof.
intros D E H OD x Ex.
generalize (OD x (proj2 (H x) Ex)).
apply filter_imp.
intros y.
apply H.
Qed.

Lemma open_and :
  forall D E : T -> Prop,
  open D -> open E ->
  open (fun x => D x /\ E x).
Proof.
intros D E OD OE x [Dx Ex].
apply filter_and.
now apply OD.
now apply OE.
Qed.

Lemma open_or :
  forall D E : T -> Prop,
  open D -> open E ->
  open (fun x => D x \/ E x).
Proof.
intros D E OD OE x [Dx|Ex].
generalize (OD x Dx).
apply filter_imp.
intros y Dy.
now left.
generalize (OE x Ex).
apply filter_imp.
intros y Ey.
now right.
Qed.

Lemma open_true :
  open (fun x : T => True).
Proof.
intros x _.
apply filter_true.
Qed.

Lemma open_false :
  open (fun x : T => False).
Proof.
now intros x Hx.
Qed.

End Open.

Lemma open_comp :
  forall {T U : UniformSpace} (f : T -> U) (D : U -> Prop),
  (forall x, D (f x) -> filterlim f (locally x) (locally (f x))) ->
  open D -> open (fun x : T => D (f x)).
Proof.
intros T U f D Cf OD x Dfx.
apply Cf.
exact Dfx.
now apply OD.
Qed.

(** ** Closed sets in uniform spaces *)

Section Closed.

Context {T : UniformSpace}.

Definition closed (D : T -> Prop) :=
  forall x, not (locally x (fun x : T => not (D x))) -> D x.

Lemma open_not :
  forall D : T -> Prop,
  closed D -> open (fun x => not (D x)).
Proof.
intros D CD x Dx.
apply locally_not.
intros H.
apply Dx, CD.
intros [eps He].
now apply (H eps).
Qed.

Lemma closed_not :
  forall D : T -> Prop,
  open D -> closed (fun x => not (D x)).
Proof.
intros D OD x Lx Dx.
apply Lx.
apply: filter_imp (OD _ Dx).
intros t Dt nDt.
now apply nDt.
Qed.

Lemma closed_ext :
  forall D E : T -> Prop,
  (forall x, D x <-> E x) ->
  closed D -> closed E.
Proof.
intros D E DE CD x Hx.
apply DE, CD.
contradict Hx.
apply: filter_imp Hx.
move => {x} x Dx Ex.
now apply Dx, DE.
Qed.

Lemma closed_and :
  forall D E : T -> Prop,
  closed D -> closed E ->
  closed (fun x => D x /\ E x).
Proof.
intros D E CD CE x Hx.
split.
apply CD.
contradict Hx.
apply: filter_imp Hx.
move => {x} x nDx [Dx _].
now apply nDx.
apply CE.
contradict Hx.
apply: filter_imp Hx.
move => {x} x nEx [_ Ex].
now apply nEx.
Qed.

(*
Lemma closed_or :
  forall D E : T -> Prop,
  closed D -> closed E ->
  closed (fun x => D x \/ E x).
Proof.
intros D E CD CE x Hx.
generalize (open_and _ _ CD CE).
apply open_ext.
clear ; intuition.
Qed.
*)

Lemma closed_true :
  closed (fun x : T => True).
Proof.
now intros _ _.
Qed.

Lemma closed_false :
  closed (fun x : T => False).
Proof.
intros x Hx.
apply Hx.
now exists (mkposreal _ Rlt_0_1).
Qed.

End Closed.

Lemma closed_comp :
  forall {T U : UniformSpace} (f : T -> U) (D : U -> Prop),
  (forall x, filterlim f (locally x) (locally (f x))) ->
  closed D -> closed (fun x : T => D (f x)).
Proof.
intros T U f D Cf CD x Dfx.
apply CD.
contradict Dfx.
exact: Cf Dfx.
Qed.

Lemma closed_filterlim_loc :
  forall {T} {U : UniformSpace} {F} {FF : ProperFilter' F} (f : T -> U) (D : U -> Prop),
  forall y, filterlim f F (locally y) ->
  F (fun x => D (f x)) ->
  closed D -> D y.
Proof.
intros T U F FF f D y Ffy Df CD.
apply CD.
intros LD.
apply filter_not_empty.
specialize (Ffy _ LD).
unfold filtermap in Ffy.
apply: filter_imp (filter_and _ _ Df Ffy).
intros x Dfx.
now apply Dfx.
Qed.

Lemma closed_filterlim :
  forall {T} {U : UniformSpace} {F} {FF : ProperFilter' F} (f : T -> U) (D : U -> Prop),
  forall y, filterlim f F (locally y) ->
  (forall x, D (f x)) ->
  closed D -> D y.
Proof.
intros T U F FF f D y Ffy Df.
apply: closed_filterlim_loc Ffy _.
now apply filter_forall.
Qed.

(** ** Complete uniform spaces *)

Definition cauchy {T : UniformSpace} (F : (T -> Prop) -> Prop) :=
  forall eps : posreal, exists x, F (ball x eps).

Module CompleteSpace.

Record mixin_of (T : UniformSpace) := Mixin {
  lim : ((T -> Prop) -> Prop) -> T ;
  ax1 : forall F, ProperFilter F -> cauchy F -> forall eps : posreal, F (ball (lim F) eps) ;
  ax2 : forall F1 F2, filter_le F1 F2 -> filter_le F2 F1 -> close (lim F1) (lim F2)
}.

Section ClassDef.

Record class_of (T : Type) := Class {
  base : UniformSpace.class_of T ;
  mixin : mixin_of (UniformSpace.Pack _ base T)
}.
Local Coercion base : class_of >-> UniformSpace.class_of.

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.

Variable cT : type.

Definition class := let: Pack _ c _ := cT return class_of cT in c.

Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition UniformSpace := UniformSpace.Pack cT xclass xT.

End ClassDef.

Module Exports.

Coercion base : class_of >-> UniformSpace.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion UniformSpace : type >-> UniformSpace.type.
Canonical UniformSpace.
Notation CompleteSpace := type.

End Exports.

End CompleteSpace.

Export CompleteSpace.Exports.

Section CompleteSpace1.

Context {T : CompleteSpace}.

Definition lim : ((T -> Prop) -> Prop) -> T := CompleteSpace.lim _ (CompleteSpace.class T).

Lemma complete_cauchy :
  forall F : (T -> Prop) -> Prop,
  ProperFilter F -> cauchy F ->
  forall eps : posreal,
  F (ball (lim F) eps).
Proof.
apply CompleteSpace.ax1.
Qed.

Lemma close_lim :
  forall F1 F2 : (T -> Prop) -> Prop,
  filter_le F1 F2 -> filter_le F2 F1 ->
  close (lim F1) (lim F2).
Proof.
apply CompleteSpace.ax2.
Qed.

Definition iota (P : T -> Prop) := lim (fun A => (forall x, P x -> A x)).

Lemma iota_correct_weak :
  forall P : T -> Prop,
  (forall x y, P x -> P y -> close x y) ->
  forall x, P x -> close (iota P) x.
Proof.
intros P HP x Hx eps.
set (F := fun A : T -> Prop => forall t : T, P t -> A t).
assert (forall eps : posreal, F (ball (lim F) eps)) as HF.
apply complete_cauchy.
constructor.
intros Q FQ.
exists x.
now apply FQ.
constructor.
now intro x0.
intros A B HA HB x0 Hx0.
split.
now apply HA.
now apply HB.
intros A B HAB HA x0 Hx0.
apply HAB ; now apply HA.
intro e.
exists x.
intros y Hy.
now apply HP.
assert (F (ball (lim F) eps)) as Heps.
apply HF.
clear HF.
now apply Heps.
Qed.

Lemma close_iota :
  forall P Q : T -> Prop,
  (forall x, P x <-> Q x) ->
  close (iota P) (iota Q).
Proof.
intros P Q H.
apply close_lim ; intros R HR x Hx ; apply HR, H, Hx.
Qed.

End CompleteSpace1.

Lemma cauchy_distance :
  forall {T : UniformSpace} {F} {FF : ProperFilter F},
  (forall eps : posreal, exists x, F (ball x eps)) <->
  (forall eps : posreal, exists P, F P /\ forall u v : T, P u -> P v -> ball u eps v).
Proof.
intros T F FF.
split.
- intros H eps.
  case: (H (pos_div_2 eps)) => {H} x Hx.
  exists (ball x (pos_div_2 eps)).
  split.
  by [].
  move => u v Hu Hv.
  rewrite (double_var eps).
  apply ball_triangle with x.
  by apply ball_sym.
  exact Hv.
- intros H eps.
  case: (H eps) => {H} P [HP H].
  destruct (filter_ex P HP) as [x Hx].
  exists x.
  move: (fun v => H x v Hx) => {H} H.
  apply filter_imp with (1 := H).
  by [].
Qed.

Section fct_CompleteSpace.

Context {T : Type} {U : CompleteSpace}.

Lemma filterlim_locally_cauchy :
  forall {F} {FF : ProperFilter F} (f : T -> U),
  (forall eps : posreal, exists P, F P /\ forall u v : T, P u -> P v -> ball (f u) eps (f v)) <->
  exists y, filterlim f F (locally y).
Proof.
intros F FF f.
split.
- intros H.
  exists (lim (filtermap f F)).
  intros P [eps HP].
  refine (_ (complete_cauchy (filtermap f F) _ _ eps)).
  + now apply filter_imp.
  + clear eps P HP.
    intros eps.
    destruct (H eps) as [P [FP H']].
    destruct (filter_ex _ FP) as [x Hx].
    exists (f x).
    unfold filtermap.
    generalize FP.
    apply filter_imp.
    intros x' Hx'.
    now apply H'.
- intros [y Hy] eps.
  exists (fun x => ball y (pos_div_2 eps) (f x)).
  split.
  apply Hy.
  now exists (pos_div_2 eps).
  intros u v Hu Hv.
  rewrite (double_var eps).
  apply ball_triangle with y.
  apply ball_sym.
  exact Hu.
  exact Hv.
Qed.

Lemma filterlimi_locally_cauchy :
  forall {F} {FF : ProperFilter F} (f : T -> U -> Prop),
  F (fun x => (exists y, f x y) /\
    (forall y1 y2, f x y1 -> f x y2 -> y1 = y2)) ->
  ((forall eps : posreal, exists P, F P /\
   forall u v : T, P u -> P v -> forall u' v': U, f u u' -> f v v' -> ball u' eps v') <->
  exists y, filterlimi f F (locally y)).
Proof.
intros F FF f Hf.
assert (FF': ProperFilter (filtermapi f F)).
  apply filtermapi_proper_filter.
  exact: filter_imp Hf.
  exact FF.
split.
- intros H.
  exists (lim (filtermapi f F)).
  intros P [eps HP].
  refine (_ (complete_cauchy (filtermapi f F) _ _ eps)).
  + now apply filter_imp.
  + clear eps P HP.
    intros eps.
    case: (H eps) => {H} [P [FP H]].
    assert (FfP := filter_and _ _ Hf FP).
    destruct (filter_ex _ FfP) as [x [[[fx Hfx] _] Px]].
    exists fx.
    unfold filtermapi.
    apply: filter_imp FfP.
    intros x' [[[fx' Hfx'] _] Px'].
    exists fx'.
    apply (conj Hfx').
    exact: H Hfx Hfx'.
- intros [y Hy] eps.
  exists (fun x => forall fx, f x fx -> ball y (pos_div_2 eps) fx).
  split.
    assert (Hb: locally y (ball y (pos_div_2 eps))).
      now exists (pos_div_2 eps).
    assert (H := filter_and _ _ Hf (Hy _ Hb)).
    apply: filter_imp H.
    intros x [[_ H] [fx2 [Hfx2 H']]] fx Hfx.
    now rewrite <- (H fx2).
  intros u v Hu Hv fu fv Hfu Hfv.
  rewrite (double_var eps).
  apply ball_triangle with y.
  apply ball_sym.
  now apply Hu.
  now apply Hv.
Qed.

Definition lim_fct (F : ((T -> U) -> Prop) -> Prop) (t : T) :=
  lim (fun P => F (fun g => P (g t))).

Lemma complete_cauchy_fct :
  forall (F : ((T -> U) -> Prop) -> Prop),
  ProperFilter F ->
  (forall eps : posreal, exists f : T -> U, F (ball f eps)) ->
  forall eps : posreal, F (ball (lim_fct F) eps).
Proof.
  move => F FF HFc.

  set Fr := fun (t : T) (P : U -> Prop) => F (fun g => P (g t)).
  have FFr : forall t, ProperFilter (Fr t).
    case: FF => HF FF t.
    split.
    - move => P Hp.
      case: (HF _ Hp) => f Hf.
      by exists (f t).
    - split.
      + by apply FF.
      + move => P P' Hp Hp'.
      by apply FF.
      + move => P P' Hpp'.
      apply FF.
      move => f ; by apply Hpp'.
  assert (HFrc : forall t, forall eps : posreal, exists x : U, Fr t (ball x eps)).
    move => t eps.
    case: (HFc eps) => f Hf.
    exists (f t).
    move: Hf ; apply FF => g.
    by [].
  assert (forall t (eps : posreal), (Fr t) (fun x => ball (lim_fct F t) eps x)).
    move => t.
    apply complete_cauchy.
    apply FFr.
    exact (HFrc t).

  move => eps.

  generalize (proj1 cauchy_distance HFc) => {HFc} HFc.

  case: (HFc (pos_div_2 eps)) => {HFc} P ; simpl ; case => HP H0.
  apply filter_imp with (2 := HP).
  move => g Hg t.
  move: (fun h => H0 g h Hg) => {H0} H0.
  move: (H t (pos_div_2 eps)) ; simpl => {H} H.
  unfold Fr in H ; generalize (filter_and _ _ H HP) => {H} H.
  apply filter_ex in H ; case: H => h H.
  rewrite (double_var eps).
  apply ball_triangle with (h t).
  by apply H.
  apply ball_sym, H0.
  by apply H.
Qed.

Lemma close_lim_fct :
  forall F1 F2 : ((T -> U) -> Prop) -> Prop,
  filter_le F1 F2 -> filter_le F2 F1 ->
  close (lim_fct F1) (lim_fct F2).
Proof.
intros F1 F2 H12 H21 eps t.
apply close_lim => P.
apply H12.
apply H21.
Qed.

Definition fct_CompleteSpace_mixin :=
  CompleteSpace.Mixin _ lim_fct complete_cauchy_fct close_lim_fct.

Canonical fct_CompleteSpace :=
  CompleteSpace.Pack (T -> U) (CompleteSpace.Class _ _ fct_CompleteSpace_mixin) (T -> U).

End fct_CompleteSpace.

(** ** Limit switching *)

Section Filterlim_switch.

Context {T1 T2 : Type}.

Lemma filterlim_switch_1 {U : UniformSpace}
  F1 (FF1 : ProperFilter F1) F2 (FF2 : Filter F2) (f : T1 -> T2 -> U) g h (l : U) :
  filterlim f F1 (locally g) ->
  (forall x, filterlim (f x) F2 (locally (h x))) ->
  filterlim h F1 (locally l) -> filterlim g F2 (locally l).
Proof.
  intros Hfg Hfh Hhl P.
  case: FF1 => HF1 FF1.
  apply filterlim_locally.
  move => eps.

  have FF := (filter_prod_filter _ _ F1 F2 FF1 FF2).

  assert (filter_prod F1 F2 (fun x => ball (g (snd x)) (eps / 2 / 2) (f (fst x) (snd x)))).
    apply Filter_prod with (fun x : T1 => ball g (eps / 2 / 2) (f x)) (fun _ => True).
    move: (proj1 (@filterlim_locally _ _ F1 FF1 f g) Hfg (pos_div_2 (pos_div_2 eps))) => {Hfg} /= Hfg.
    by [].
    by apply FF2.
    simpl ; intros.
    apply H.
  move: H => {Hfg} Hfg.

  assert (filter_prod F1 F2 (fun x : T1 * T2 => ball l (eps / 2) (h (fst x)))).
    apply Filter_prod with (fun x : T1 => ball l (eps / 2) (h x)) (fun _ => True).
    move: (proj1 (@filterlim_locally _ _ F1 FF1 h l) Hhl (pos_div_2 eps)) => {Hhl} /= Hhl.
    by [].
    by apply FF2.
    by [].
  move: H => {Hhl} Hhl.

  case: (@filter_and _ _ FF _ _ Hhl Hfg) => {Hhl Hfg} /= ; intros.

  move: (fun x => proj1 (@filterlim_locally _ _ F2 FF2 (f x) (h x)) (Hfh x) (pos_div_2 (pos_div_2 eps))) => {Hfh} /= Hfh.
  case: (HF1 Q f0) => x Hx.
  move: (@filter_and _ _ FF2 _ _ (Hfh x) g0) => {Hfh}.
  apply filter_imp => y Hy.
  rewrite (double_var eps).
  apply ball_triangle with (h x).
  apply (p x y).
  by [].
  by apply Hy.
  rewrite (double_var (eps / 2)).
  apply ball_triangle with (f x y).
  by apply Hy.
  apply ball_sym, p.
  by [].
  by apply Hy.
Qed.

Lemma filterlim_switch_2 {U : CompleteSpace}
  F1 (FF1 : ProperFilter F1) F2 (FF2 : ProperFilter F2) (f : T1 -> T2 -> U) g h :
  filterlim f F1 (locally g) ->
  (forall x, filterlim (f x) F2 (locally (h x))) ->
  exists l : U, filterlim h F1 (locally l).
Proof.
  move => Hfg Hfh.
  case : (proj1 (filterlim_locally_cauchy h)).
  move => eps.
  generalize (proj2 (filterlim_locally_cauchy f)) => Hf.
  assert (exists y : T2 -> U, filterlim f F1 (locally y)).
    exists g => P Hp.
    apply Hfg.
    case: Hp => d Hp.
    exists d => y Hy.
    apply: Hp.
    by apply Hy.

  move: H => {Hfg} Hfg.
  move: (Hf Hfg (pos_div_2 eps)) => {Hf Hfg} /= Hf.

  case: FF2 => HF2 FF2.
  generalize (fun x => proj1 (filterlim_locally (f x) (h x)) (Hfh x) (pos_div_2 (pos_div_2 eps)))
    => {Hfh} Hfh.

  case: Hf => P [Hp Hf].
  exists P ; split.
  by [].
  move => u v Hu Hv.
  move: (Hfh u) => /= Hu'.
  move: (Hfh v) => /= Hv'.
  move: (@filter_and _ F2 FF2 _ _ Hu' Hv') => {Hu' Hv' Hfh} Hfh.
  case: (HF2 _ Hfh) => {Hfh} y Hy.
  replace (pos eps) with (eps / 2 / 2 + (eps / 2 + eps / 2 / 2)) by field.
  apply ball_triangle with (f u y).
  by apply Hy.
  apply ball_triangle with (f v y).
  by apply Hf.
  now apply ball_sym.

  move => l Hl.
  by exists l.
Qed.

Lemma filterlim_switch {U : CompleteSpace}
  F1 (FF1 : ProperFilter F1) F2 (FF2 : ProperFilter F2) (f : T1 -> T2 -> U) g h :
  filterlim f F1 (locally g) ->
  (forall x, filterlim (f x) F2 (locally (h x))) ->
  exists l : U, filterlim h F1 (locally l) /\ filterlim g F2 (locally l).
Proof.
  move => Hfg Hfh.
  destruct (filterlim_switch_2 F1 FF1 F2 FF2 f g h Hfg Hfh) as [l Hhl].
  exists l ; split.
  exact Hhl.
  case: FF2 => HF2 FF2.
  now apply (filterlim_switch_1 F1 FF1 F2 FF2 f g h l).
Qed.

End Filterlim_switch.

Lemma filterlim_switch_dom {T1 T2 : Type} {U : CompleteSpace}
  F1 (FF1 : ProperFilter F1) F2 (FF2 : Filter F2)
  (dom : T2 -> Prop) (HF2 : forall P, F2 P -> exists x, dom x /\ P x)
  (f : T1 -> T2 -> U) g h :
  filterlim (fun x (y : {z : T2 | dom z}) => f x (proj1_sig y)) F1 (locally (T := fct_UniformSpace _ _) (fun y : {z : T2 | dom z} => g (proj1_sig y))) ->
  (forall x, filterlim (f x) (within dom F2) (locally (h x))) ->
  exists l : U, filterlim h F1 (locally l) /\ filterlim g (within dom F2) (locally l).
Proof.
set (T2' := { y : T2 | dom y }).
set (f' := fun x (y : T2') => f x (proj1_sig y)).
set (F2' := fun P : T2' -> Prop => F2 (fun x => forall (H:dom x), P (exist _ x H))).
set (g' := fun y : T2' => g (proj1_sig y)).
intros Hfg Hfh.
refine (filterlim_switch F1 FF1 F2' _ f' g' h _ _).
now apply subset_filter_proper.
intros H P.
now apply Hfg.
intros x P HP.
now apply Hfh.
Qed.

(** * Modules *)

Module ModuleSpace.

Record mixin_of (K : Ring) (V : AbelianGroup) := Mixin {
  scal : K -> V -> V ;
  ax1 : forall x y u, scal x (scal y u) = scal (mult x y) u ;
  ax2 : forall u, scal one u = u ;
  ax3 : forall x u v, scal x (plus u v) = plus (scal x u) (scal x v) ;
  ax4 : forall x y u, scal (plus x y) u = plus (scal x u) (scal y u)
}.

Section ClassDef.

Variable K : Ring.

Record class_of (V : Type) := Class {
  base : AbelianGroup.class_of V ;
  mixin : mixin_of K (AbelianGroup.Pack _ base V)
}.
Local Coercion base : class_of >-> AbelianGroup.class_of.

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.

Variable cT : type.

Definition class := let: Pack _ c _ := cT return class_of cT in c.

Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition AbelianGroup := AbelianGroup.Pack cT xclass xT.

End ClassDef.

Module Exports.

Coercion base : class_of >-> AbelianGroup.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion AbelianGroup : type >-> AbelianGroup.type.
Canonical AbelianGroup.
Notation ModuleSpace := type.

End Exports.

End ModuleSpace.

Export ModuleSpace.Exports.

Section ModuleSpace1.

Context {K : Ring} {V : ModuleSpace K}.

Definition scal : K -> V -> V := ModuleSpace.scal _ _ (ModuleSpace.class K V).

Lemma scal_assoc :
  forall (x y : K) (u : V),
  scal x (scal y u) = scal (mult x y) u.
Proof.
apply ModuleSpace.ax1.
Qed.

Lemma scal_one :
  forall (u : V), scal one u = u.
Proof.
apply ModuleSpace.ax2.
Qed.

Lemma scal_distr_l :
  forall (x : K) (u v : V),
  scal x (plus u v) = plus (scal x u) (scal x v).
Proof.
apply ModuleSpace.ax3.
Qed.

Lemma scal_distr_r :
  forall (x y : K) (u : V),
  scal (plus x y) u = plus (scal x u) (scal y u).
Proof.
apply ModuleSpace.ax4.
Qed.

Lemma scal_zero_r :
  forall x : K,
  scal x zero = zero.
Proof.
intros x.
apply plus_reg_r with (scal x zero).
rewrite <- scal_distr_l.
rewrite plus_zero_r.
now rewrite plus_zero_l.
Qed.

Lemma scal_zero_l :
  forall u : V,
  scal zero u = zero.
Proof.
intros u.
apply plus_reg_r with (r := scal zero u).
rewrite plus_zero_l.
rewrite <- scal_distr_r.
now rewrite plus_zero_r.
Qed.

Lemma scal_opp_l :
  forall (x : K) (u : V),
  scal (opp x) u = opp (scal x u).
Proof.
intros x u.
apply plus_reg_r with (r := (scal x u)).
rewrite plus_opp_l.
rewrite <- scal_distr_r.
rewrite plus_opp_l.
apply scal_zero_l.
Qed.

Lemma scal_opp_r :
  forall (x : K) (u : V),
  scal x (opp u) = opp (scal x u).
Proof.
intros x u.
apply plus_reg_r with (r := (scal x u)).
rewrite plus_opp_l.
rewrite <- scal_distr_l.
rewrite plus_opp_l.
apply scal_zero_r.
Qed.

Lemma scal_opp_one :
  forall u : V,
  scal (opp one) u = opp u.
Proof.
intros u.
rewrite scal_opp_l.
now rewrite scal_one.
Qed.

Lemma scal_minus_distr_l (x : K) (u v : V) :
   scal x (minus u v) = minus (scal x u) (scal x v).
Proof.
  by rewrite /minus scal_distr_l scal_opp_r.
Qed.
Lemma scal_minus_distr_r (x y : K) (u : V) :
   scal (minus x y) u = minus (scal x u) (scal y u).
Proof.
  by rewrite /minus scal_distr_r scal_opp_l.
Qed.

Lemma sum_n_m_scal_l :
  forall (a : K) (u : nat -> V) (n m : nat),
  sum_n_m (fun k => scal a (u k)) n m = scal a (sum_n_m u n m).
Proof.
  intros a u n m.
  case: (le_dec n m) => Hnm.
  elim: m n u Hnm => [ | m IH] n u Hnm.
  apply le_n_O_eq in Hnm.
  by rewrite -Hnm !sum_n_n.
  destruct n.
  rewrite !sum_n_Sm ; try by apply le_O_n.
  rewrite IH.
  by apply sym_eq, scal_distr_l.
  by apply le_O_n.
  rewrite -!sum_n_m_S.
  apply IH.
  by apply le_S_n.
  apply not_le in Hnm.
  rewrite !sum_n_m_zero //.
  by rewrite scal_zero_r.
Qed.

Lemma sum_n_scal_l :
  forall (a : K) (u : nat -> V) (n : nat),
  sum_n (fun k => scal a (u k)) n = scal a (sum_n u n).
Proof.
  intros a u n.
  apply sum_n_m_scal_l.
Qed.

End ModuleSpace1.

(** Rings are modules *)

Section Ring_ModuleSpace.

Variable (K : Ring).

Definition Ring_ModuleSpace_mixin :=
  ModuleSpace.Mixin K _ _ mult_assoc mult_one_l mult_distr_l mult_distr_r.

Canonical Ring_ModuleSpace :=
  ModuleSpace.Pack K K (ModuleSpace.Class _ _ _ Ring_ModuleSpace_mixin) K.

End Ring_ModuleSpace.

Section AbsRing_ModuleSpace.

Variable (K : AbsRing).

Definition AbsRing_ModuleSpace_mixin :=
  ModuleSpace.Mixin K _ _ mult_assoc mult_one_l mult_distr_l mult_distr_r.

Canonical AbsRing_ModuleSpace :=
  ModuleSpace.Pack K K (ModuleSpace.Class _ _ _ AbsRing_ModuleSpace_mixin) K.

End AbsRing_ModuleSpace.

(** ** Modules with a norm *)

Module NormedModuleAux.

Section ClassDef.

Variable K : AbsRing.

Record class_of (T : Type) := Class {
  base : ModuleSpace.class_of K T ;
  mixin : UniformSpace.mixin_of T
}.
Local Coercion base : class_of >-> ModuleSpace.class_of.
Local Coercion mixin : class_of >-> UniformSpace.class_of.

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.

Variable cT : type.

Definition class := let: Pack _ c _ := cT return class_of cT in c.

Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition AbelianGroup := AbelianGroup.Pack cT xclass xT.
Definition ModuleSpace := ModuleSpace.Pack _ cT xclass xT.
Definition UniformSpace := UniformSpace.Pack cT xclass xT.

End ClassDef.

Module Exports.

Coercion base : class_of >-> ModuleSpace.class_of.
Coercion mixin : class_of >-> UniformSpace.class_of.
Coercion sort : type >-> Sortclass.
Coercion AbelianGroup : type >-> AbelianGroup.type.
Canonical AbelianGroup.
Coercion ModuleSpace : type >-> ModuleSpace.type.
Canonical ModuleSpace.
Coercion UniformSpace : type >-> UniformSpace.type.
Canonical UniformSpace.
Notation NormedModuleAux := type.

End Exports.

End NormedModuleAux.

Export NormedModuleAux.Exports.

Module NormedModule.

Record mixin_of (K : AbsRing) (V : NormedModuleAux K) := Mixin {
  norm : V -> R ;
  norm_factor : R ;
  ax1 : forall (x y : V), norm (plus x y) <= norm x + norm y ;
  ax2 : forall (l : K) (x : V), norm (scal l x) <= abs l * norm x ;
  ax3 : forall (x y : V) (eps : R), norm (minus y x) < eps -> ball x eps y ;
  ax4 : forall (x y : V) (eps : posreal), ball x eps y -> norm (minus y x) < norm_factor * eps ;
  ax5 : forall x : V, norm x = 0 -> x = zero
}.

Section ClassDef.

Variable K : AbsRing.

Record class_of (T : Type) := Class {
  base : NormedModuleAux.class_of K T ;
  mixin : mixin_of K (NormedModuleAux.Pack K T base T)
}.
Local Coercion base : class_of >-> NormedModuleAux.class_of.

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.

Variable cT : type.

Definition class := let: Pack _ c _ := cT return class_of cT in c.

Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition AbelianGroup := AbelianGroup.Pack cT xclass xT.
Definition ModuleSpace := ModuleSpace.Pack _ cT xclass xT.
Definition UniformSpace := UniformSpace.Pack cT xclass xT.
Definition NormedModuleAux := NormedModuleAux.Pack _ cT xclass xT.

End ClassDef.

Module Exports.

Coercion base : class_of >-> NormedModuleAux.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion AbelianGroup : type >-> AbelianGroup.type.
Canonical AbelianGroup.
Coercion ModuleSpace : type >-> ModuleSpace.type.
Canonical ModuleSpace.
Coercion UniformSpace : type >-> UniformSpace.type.
Canonical UniformSpace.
Coercion NormedModuleAux : type >-> NormedModuleAux.type.
Canonical NormedModuleAux.
Notation NormedModule := type.

End Exports.

End NormedModule.

Export NormedModule.Exports.

Section NormedModule1.

Context {K : AbsRing} {V : NormedModule K}.

Definition norm : V -> R := NormedModule.norm K _ (NormedModule.class K V).

Definition norm_factor : R := NormedModule.norm_factor K _ (NormedModule.class K V).

Lemma norm_triangle :
  forall x y : V,
  norm (plus x y) <= norm x + norm y.
Proof.
apply NormedModule.ax1.
Qed.

Lemma norm_scal :
  forall (l : K) (x : V),
  norm (scal l x) <= abs l * norm x.
Proof.
apply NormedModule.ax2.
Qed.

Lemma norm_compat1 :
  forall (x y : V) (eps : R),
  norm (minus y x) < eps -> ball x eps y.
Proof.
apply NormedModule.ax3.
Qed.

Lemma norm_compat2 :
  forall (x y : V) (eps : posreal), ball x eps y -> norm (minus y x) < norm_factor * eps.
Proof.
apply: NormedModule.ax4.
Qed.

Lemma norm_eq_zero :
  forall x : V, norm x = 0 -> x = zero.
Proof.
apply NormedModule.ax5.
Qed.

Lemma norm_zero :
  norm zero = 0.
Proof.
apply Rle_antisym.
- rewrite -(scal_zero_l zero).
  rewrite -(Rmult_0_l (norm zero)).
  rewrite -(@abs_zero K).
  apply norm_scal.
- apply Rplus_le_reg_r with (norm zero).
  rewrite Rplus_0_l.
  rewrite -{1}[zero]plus_zero_r.
  exact (norm_triangle zero zero).
Qed.

Lemma norm_factor_gt_0 :
  0 < norm_factor.
Proof.
rewrite <- (Rmult_1_r norm_factor).
rewrite <- norm_zero.
rewrite <- (plus_opp_r zero).
apply (norm_compat2 _ _ (mkposreal _ Rlt_0_1)).
apply ball_center.
Qed.

Lemma norm_opp :
  forall x : V,
  norm (opp x) = norm x.
Proof.
intros x.
apply Rle_antisym.
- rewrite -scal_opp_one.
  rewrite -(Rmult_1_l (norm x)) -(@abs_opp_one K).
  apply norm_scal.
- rewrite -{1}[x]opp_opp -scal_opp_one.
  rewrite -(Rmult_1_l (norm (opp x))) -(@abs_opp_one K).
  apply norm_scal.
Qed.

Lemma norm_ge_0 :
  forall x : V,
  0 <= norm x.
Proof.
  intros x.
  apply Rmult_le_reg_l with 2.
  by apply Rlt_0_2.
  rewrite Rmult_0_r -norm_zero -(plus_opp_r x).
  apply Rle_trans with (norm x + norm (opp x)).
  apply norm_triangle.
  apply Req_le ; rewrite norm_opp.
  ring.
Qed.

Lemma norm_triangle_inv :
  forall x y : V,
  Rabs (norm x - norm y) <= norm (minus x y).
Proof.
  intros x y.
  apply Rabs_le_between' ; split.
  rewrite -(norm_opp (minus _ _)).
  apply Rle_minus_l ; eapply Rle_trans.
  2 : apply norm_triangle.
  apply Req_le, f_equal.
  by rewrite /minus opp_plus plus_assoc plus_opp_r plus_zero_l opp_opp.
  eapply Rle_trans.
  2 : apply norm_triangle.
  apply Req_le, f_equal.
  by rewrite /minus plus_comm -plus_assoc plus_opp_l plus_zero_r.
Qed.

Lemma eq_close :
  forall x y : V,
  close x y -> x = y.
Proof.
intros x y H.
apply plus_reg_r with (opp x).
rewrite plus_opp_r.
apply eq_sym, norm_eq_zero.
apply Rle_antisym.
2: apply norm_ge_0.
apply prop_eps.
intros eps He.
assert (He' : 0 < eps / norm_factor).
  apply Rdiv_lt_0_compat with (1 := He).
  apply norm_factor_gt_0.
specialize (H (mkposreal _ He')).
replace eps with (norm_factor * (eps / norm_factor)).
apply norm_compat2 with (1 := H).
field.
apply Rgt_not_eq, norm_factor_gt_0.
Qed.

Definition ball_norm (x : V) (eps : R) (y : V) := norm (minus y x) < eps.

Definition locally_norm (x : V) (P : V -> Prop) :=
  exists eps : posreal, forall y, ball_norm x eps y -> P y.

Lemma locally_le_locally_norm :
  forall x, filter_le (locally x) (locally_norm x).
Proof.
intros x P [eps H].
assert (He : 0 < / norm_factor * eps).
  apply Rmult_lt_0_compat.
  apply Rinv_0_lt_compat.
  apply norm_factor_gt_0.
  apply cond_pos.
exists (mkposreal _ He).
intros y By.
apply H.
unfold ball_norm.
rewrite -(Rmult_1_l eps) -(Rinv_r norm_factor).
rewrite Rmult_assoc.
apply norm_compat2 with (1 := By).
apply Rgt_not_eq.
apply norm_factor_gt_0.
Qed.

Lemma locally_norm_le_locally :
  forall x, filter_le (locally_norm x) (locally x).
Proof.
intros x P [eps H].
exists eps.
intros y By.
apply H.
now apply norm_compat1.
Qed.

Lemma locally_norm_ball_norm :
  forall (x : V) (eps : posreal),
  locally_norm x (ball_norm x eps).
Proof.
intros x eps.
now exists eps.
Qed.

Lemma locally_norm_ball :
  forall (x : V) (eps : posreal),
  locally_norm x (ball x eps).
Proof.
intros x eps.
apply locally_norm_le_locally.
apply locally_ball.
Qed.

Lemma locally_ball_norm :
  forall (x : V) (eps : posreal),
  locally x (ball_norm x eps).
Proof.
intros x eps.
apply locally_le_locally_norm.
apply locally_norm_ball_norm.
Qed.

Lemma ball_norm_triangle (x y z : V) (e1 e2 : R) :
  ball_norm x e1 y -> ball_norm y e2 z -> ball_norm x (e1 + e2) z.
Proof.
  intros H1 H2.
  eapply Rle_lt_trans, Rplus_lt_compat.
  2: by apply H1.
  2: by apply H2.
  rewrite Rplus_comm.
  eapply Rle_trans, norm_triangle.
  apply Req_le, f_equal.
  rewrite /minus -!plus_assoc.
  apply f_equal.
  by rewrite plus_assoc plus_opp_l plus_zero_l.
Qed.

Lemma ball_norm_center (x : V) (e : posreal) :
  ball_norm x e x.
Proof.
  eapply Rle_lt_trans, e.
  rewrite minus_eq_zero norm_zero.
  by apply Req_le.
Qed.

Lemma ball_norm_dec : forall (x y : V) (eps : posreal),
  {ball_norm x eps y} + {~ ball_norm x eps y}.
Proof.
  intros x y eps.
  apply Rlt_dec.
Qed.

Lemma ball_norm_sym :
  forall (x y : V) (eps : posreal), ball_norm x eps y -> ball_norm y eps x.
Proof.
  intros x y eps Hxy.
  unfold ball_norm.
  rewrite <- norm_opp.
  rewrite opp_minus.
  apply Hxy.
Qed.

Lemma ball_norm_le :
  forall (x : V) (e1 e2 : posreal), e1 <= e2 ->
  forall y, ball_norm x e1 y -> ball_norm x e2 y.
Proof.
  intros x e1 e2 He y H1.
  now apply Rlt_le_trans with e1.
Qed.

Lemma ball_norm_eq :
  forall x y : V,
  (forall eps : posreal, ball_norm x eps y) -> x = y.
Proof.
intros x y H.
apply plus_reg_r with (opp x).
rewrite plus_opp_r.
apply eq_sym, norm_eq_zero.
apply Rle_antisym.
2: apply norm_ge_0.
apply prop_eps.
intros eps He.
exact (H (mkposreal eps He)).
Qed.

Lemma is_filter_lim_unique :
  forall {F} {FF : ProperFilter' F} (x y : V),
  is_filter_lim F x -> is_filter_lim F y -> x = y.
Proof.
intros F FF x y Hx Hy.
apply ball_norm_eq => eps.
assert (Hx': F (ball_norm x (pos_div_2 eps))).
  apply Hx.
  apply locally_ball_norm.
assert (Hy': F (ball_norm y (pos_div_2 eps))).
  apply Hy.
  apply locally_ball_norm.
apply Rnot_le_lt.
intros H.
apply (@filter_not_empty V F FF).
apply: filter_imp (filter_and _ _ Hx' Hy').
clear -H.
intros z [Bx By].
revert H.
apply Rlt_not_le.
rewrite (double_var eps).
change (eps / 2) with (pos (pos_div_2 eps)).
apply ball_norm_triangle with (1 := Bx).
now apply ball_norm_sym.
Qed.

Lemma is_filter_lim_locally_unique :
  forall (x y : V),
  is_filter_lim (locally x) y -> x = y.
Proof.
intros x y H.
apply eq_close.
now apply is_filter_lim_locally_close.
Qed.

End NormedModule1.

Section NormedModule2.

Context {T : Type} {K : AbsRing} {V : NormedModule K}.

Lemma filterlim_locally_unique :
  forall {F} {FF : ProperFilter' F} (f : T -> V) (x y : V),
  filterlim f F (locally x) -> filterlim f F (locally y) ->
  x = y.
Proof.
intros F FF f x y.
apply is_filter_lim_unique.
Qed.

Lemma filterlimi_locally_unique :
  forall {F} {FF : ProperFilter' F} (f : T -> V -> Prop) (x y : V),
  F (fun x => forall y1 y2, f x y1 -> f x y2 -> y1 = y2) ->
  filterlimi f F (locally x) -> filterlimi f F (locally y) ->
  x = y.
Proof.
intros F FF f x y Hf Hx Hy.
apply ball_norm_eq => eps.
specialize (Hx (ball_norm x (pos_div_2 eps)) (locally_ball_norm _ _)).
specialize (Hy (ball_norm y (pos_div_2 eps)) (locally_ball_norm _ _)).
unfold filtermapi in Hx, Hy.
apply Rnot_le_lt.
intros H.
apply (@filter_not_empty _ F FF).
apply: filter_imp (filter_and _ _ (filter_and _ _ Hx Hy) Hf).
clear -H.
intros z [[[x' [Hx Bx]] [y' [Hy By]]] Hf].
apply: Rlt_not_le H.
rewrite (double_var eps).
change (eps / 2) with (pos (pos_div_2 eps)).
apply ball_norm_triangle with (1 := Bx).
apply ball_norm_sym.
now rewrite (Hf _ _ Hx Hy).
Qed.

End NormedModule2.

(** Rings with absolute values are normed modules *)

Section AbsRing_NormedModule.

Variable (K : AbsRing).

Canonical AbsRing_NormedModuleAux :=
  NormedModuleAux.Pack K K (NormedModuleAux.Class _ _ (ModuleSpace.class _ (AbsRing_ModuleSpace K)) (UniformSpace.class (AbsRing_UniformSpace K))) K.

Lemma AbsRing_norm_compat2 :
  forall (x y : AbsRing_NormedModuleAux) (eps : posreal),
  ball x eps y -> abs (minus y x) < 1 * eps.
Proof.
  intros x y eps H.
  now rewrite Rmult_1_l.
Qed.

Definition AbsRing_NormedModule_mixin :=
  NormedModule.Mixin K _ abs 1 abs_triangle abs_mult (fun x y e H => H) AbsRing_norm_compat2 abs_eq_zero.

Canonical AbsRing_NormedModule :=
  NormedModule.Pack K _ (NormedModule.Class _ _ _ AbsRing_NormedModule_mixin) K.

End AbsRing_NormedModule.

(** Normed vector spaces have some continuous functions *)

Section NVS_continuity.

Context {K : AbsRing} {V : NormedModule K}.

Lemma filterlim_plus :
  forall x y : V,
  filterlim (fun z : V * V => plus (fst z) (snd z)) (filter_prod (locally x) (locally y)) (locally (plus x y)).
Proof.
intros x y.
apply (filterlim_filter_le_1 (F := filter_prod (locally_norm x) (locally_norm y))).
  intros P [Q R LQ LR H].
  exists Q R.
  now apply locally_le_locally_norm.
  now apply locally_le_locally_norm.
  exact H.
apply (filterlim_filter_le_2 (G := locally_norm (plus x y))).
  apply locally_norm_le_locally.
intros P [eps HP].
exists (ball_norm x (pos_div_2 eps)) (ball_norm y (pos_div_2 eps)).
by apply locally_norm_ball_norm.
by apply locally_norm_ball_norm.
intros u v Hu Hv.
apply HP.
rewrite /ball_norm /= (double_var eps).
apply Rle_lt_trans with (2 := Rplus_lt_compat _ _ _ _ Hu Hv).
apply Rle_trans with (2 := norm_triangle _ _).
apply Req_le, f_equal.
rewrite /minus /= opp_plus -2!plus_assoc.
apply f_equal.
rewrite 2!plus_assoc.
apply f_equal2.
by apply plus_comm.
by [].
Qed.

Lemma filterlim_scal (k : K) (x : V) :
  filterlim (fun z => scal (fst z) (snd z)) (filter_prod (locally k) (locally x)) (locally (scal k x)).
Proof.
  apply filterlim_locally => /= eps.
  eapply filter_imp.
  move => /= u Hu.
  rewrite (double_var eps).
  apply ball_triangle with (scal (fst u) x).
  apply norm_compat1.
  rewrite -scal_minus_distr_r.
  eapply Rle_lt_trans.
  apply norm_scal.
  eapply Rle_lt_trans.
  apply Rmult_le_compat_l.
  by apply abs_ge_0.
  apply Rlt_le, Rlt_plus_1.
  apply <- Rlt_div_r.
  2: apply Rle_lt_0_plus_1, norm_ge_0.
  by eapply (proj1 Hu).
  apply norm_compat1.
  rewrite -scal_minus_distr_l.
  eapply Rle_lt_trans.
  apply norm_scal.
  eapply Rle_lt_trans.
  apply Rmult_le_compat_r.
  by apply norm_ge_0.
  replace (fst u) with (plus k (minus (fst u) k)).
  eapply Rle_trans.
  apply abs_triangle.
  apply Rplus_le_compat_l.
  apply Rlt_le.
  instantiate (1 := 1).
  eapply (proj1 (proj2 Hu)).
  by rewrite plus_comm -plus_assoc plus_opp_l plus_zero_r.
  rewrite Rmult_comm.
  apply <- Rlt_div_r.
  2: apply Rle_lt_0_plus_1, abs_ge_0.
  by apply (proj2 (proj2 Hu)).

  repeat apply filter_and.

  assert (Hd : 0 < eps / 2 / (norm x + 1)).
    apply Rdiv_lt_0_compat.
    by apply is_pos_div_2.
    apply Rle_lt_0_plus_1, norm_ge_0.
  eexists.
  apply (locally_ball_norm (V := AbsRing_NormedModule K) _ (mkposreal _ Hd)).
  apply filter_true.
  by [].

  eexists.
  apply (locally_ball_norm (V := AbsRing_NormedModule K) _ (mkposreal _ Rlt_0_1)).
  apply filter_true.
  by [].

  assert (Hd : 0 < eps / 2 / (abs k + 1)).
    apply Rdiv_lt_0_compat.
    by apply is_pos_div_2.
    apply Rle_lt_0_plus_1, abs_ge_0.
  eexists.
  apply filter_true.
  apply (locally_ball_norm _ (mkposreal _ Hd)).
  by [].
Qed.
Lemma filterlim_scal_r (k : K) (x : V) :
  filterlim (fun z : V => scal k z) (locally x) (locally (scal k x)).
Proof.
  eapply filterlim_comp_2.
  by apply filterlim_const.
  by apply filterlim_id.
  by apply filterlim_scal.
Qed.
Lemma filterlim_scal_l (k : K) (x : V) :
  filterlim (fun z => scal z x) (locally k) (locally (scal k x)).
Proof.
  eapply filterlim_comp_2.
  by apply filterlim_id.
  by apply filterlim_const.
  by apply filterlim_scal.
Qed.

Lemma filterlim_opp :
  forall x : V,
  filterlim opp (locally x) (locally (opp x)).
Proof.
intros x.
rewrite -scal_opp_one.
apply filterlim_ext with (2 := filterlim_scal_r _ _).
apply: scal_opp_one.
Qed.

End NVS_continuity.

Lemma filterlim_mult {K : AbsRing} (x y : K) :
  filterlim (fun z => mult (fst z) (snd z)) (filter_prod (locally x) (locally y)) (locally (mult x y)).
Proof.
  by apply @filterlim_scal.
Qed.

Lemma filterlim_locally_ball_norm :
  forall {K : AbsRing} {T} {U : NormedModule K} {F : (T -> Prop) -> Prop} {FF : Filter F} (f : T -> U) (y : U),
  filterlim f F (locally y) <-> forall eps : posreal, F (fun x => ball_norm y eps (f x)).
Proof.
intros K T U F FF f y.
split.
- intros Cf eps.
  apply (Cf (fun x => ball_norm y eps x)).
  apply locally_le_locally_norm.
  apply locally_norm_ball_norm.
- intros Cf.
  apply (filterlim_filter_le_2 _ (locally_norm_le_locally y)).
  intros P [eps He].
  apply: filter_imp (Cf eps).
  intros t.
  apply He.
Qed.

(** ** Complete Normed Modules *)

Module CompleteNormedModule.

Section ClassDef.

Variable K : AbsRing.

Record class_of (T : Type) := Class {
  base : NormedModule.class_of K T ;
  mixin : CompleteSpace.mixin_of (UniformSpace.Pack T base T)
}.
Local Coercion base : class_of >-> NormedModule.class_of.
Definition base2 T (cT : class_of T) : CompleteSpace.class_of T :=
  CompleteSpace.Class _ (base T cT) (mixin T cT).
Local Coercion base2 : class_of >-> CompleteSpace.class_of.

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.

Variable cT : type.

Definition class := let: Pack _ c _ := cT return class_of cT in c.

Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition AbelianGroup := AbelianGroup.Pack cT xclass xT.
Definition ModuleSpace := ModuleSpace.Pack _ cT xclass xT.
Definition NormedModuleAux := NormedModuleAux.Pack _ cT xclass xT.
Definition NormedModule := NormedModule.Pack _ cT xclass xT.
Definition UniformSpace := UniformSpace.Pack cT xclass xT.
Definition CompleteSpace := CompleteSpace.Pack cT xclass xT.

End ClassDef.

Module Exports.

Coercion base : class_of >-> NormedModule.class_of.
Coercion mixin : class_of >-> CompleteSpace.mixin_of.
Coercion base2 : class_of >-> CompleteSpace.class_of.
Coercion sort : type >-> Sortclass.
Coercion AbelianGroup : type >-> AbelianGroup.type.
Canonical AbelianGroup.
Coercion ModuleSpace : type >-> ModuleSpace.type.
Canonical ModuleSpace.
Coercion NormedModuleAux : type >-> NormedModuleAux.type.
Canonical NormedModuleAux.
Coercion NormedModule : type >-> NormedModule.type.
Canonical NormedModule.
Coercion UniformSpace : type >-> UniformSpace.type.
Canonical UniformSpace.
Coercion CompleteSpace : type >-> CompleteSpace.type.
Canonical CompleteSpace.
Notation CompleteNormedModule := type.

End Exports.

End CompleteNormedModule.

Export CompleteNormedModule.Exports.

Section CompleteNormedModule1.

Context {K : AbsRing} {V : CompleteNormedModule K}.

Lemma iota_unique :
  forall (P : V -> Prop) (x : V),
  (forall y, P y -> y = x) ->
  P x ->
  iota P = x.
Proof.
intros P x HP Px.
apply eq_close.
intros eps.
apply: iota_correct_weak Px eps.
intros x' y Px' Py eps.
rewrite (HP _ Py) -(HP _ Px').
apply ball_center.
Qed.

Lemma iota_correct :
  forall P : V -> Prop,
  (exists! x : V, P x) ->
  P (iota P).
Proof.
intros P [x [Px HP]].
rewrite (iota_unique _ x) ; try exact Px.
intros y Py.
now apply sym_eq, HP.
Qed.

Lemma iota_is_filter_lim {F} {FF : ProperFilter' F} (l : V) :
  is_filter_lim F l ->
  iota (is_filter_lim F) = l.
Proof.
intros Hl.
apply: iota_unique (Hl) => l' Hl'.
exact: is_filter_lim_unique Hl' Hl.
Qed.

Context {T : Type}.

Lemma iota_filterlim_locally {F} {FF : ProperFilter' F} (f : T -> V) l :
  filterlim f F (locally l) ->
  iota (fun x => filterlim f F (locally x)) = l.
Proof.
apply iota_is_filter_lim.
Qed.

Lemma iota_filterlimi_locally {F} {FF : ProperFilter' F} (f : T -> V -> Prop) l :
  F (fun x => forall y1 y2, f x y1 -> f x y2 -> y1 = y2) ->
  filterlimi f F (locally l) ->
  iota (fun x => filterlimi f F (locally x)) = l.
Proof.
intros Hf Hl.
apply: iota_unique (Hl) => l' Hl'.
exact: filterlimi_locally_unique Hf Hl' Hl.
Qed.

End CompleteNormedModule1.

(** * Extended Types *)

(** ** Pairs *)

Section prod_AbelianGroup.

Context {U V : AbelianGroup}.

Definition prod_plus (x y : U * V) :=
  (plus (fst x) (fst y), plus (snd x) (snd y)).

Definition prod_opp (x : U * V) :=
  (opp (fst x), opp (snd x)).

Definition prod_zero : U * V := (zero, zero).

Lemma prod_plus_comm :
  forall x y : U * V,
  prod_plus x y = prod_plus y x.
Proof.
intros x y.
apply (f_equal2 pair) ; apply plus_comm.
Qed.

Lemma prod_plus_assoc :
  forall x y z : U * V,
  prod_plus x (prod_plus y z) = prod_plus (prod_plus x y) z.
Proof.
intros x y z.
apply (f_equal2 pair) ; apply plus_assoc.
Qed.

Lemma prod_plus_zero_r :
  forall x : U * V,
  prod_plus x prod_zero = x.
Proof.
intros [u v].
apply (f_equal2 pair) ; apply plus_zero_r.
Qed.

Lemma prod_plus_opp_r :
  forall x : U * V,
  prod_plus x (prod_opp x) = prod_zero.
Proof.
intros x.
apply (f_equal2 pair) ; apply plus_opp_r.
Qed.

End prod_AbelianGroup.

Definition prod_AbelianGroup_mixin (U V : AbelianGroup) :=
  AbelianGroup.Mixin (U * V) _ _ _ prod_plus_comm prod_plus_assoc prod_plus_zero_r prod_plus_opp_r.

Canonical prod_AbelianGroup (U V : AbelianGroup) :=
  AbelianGroup.Pack (U * V) (prod_AbelianGroup_mixin U V) (U * V).

Section prod_UniformSpace.

Context {U V : UniformSpace}.

Definition prod_ball (x : U * V) (eps : R) (y : U * V) :=
  ball (fst x) eps (fst y) /\ ball (snd x) eps (snd y).

Lemma prod_ball_center :
  forall (x : U * V) (eps : posreal),
  prod_ball x eps x.
Proof.
intros x eps.
split ; apply ball_center.
Qed.

Lemma prod_ball_sym :
  forall (x y : U * V) (eps : R),
  prod_ball x eps y -> prod_ball y eps x.
Proof.
intros x y eps [H1 H2].
split ; now apply ball_sym.
Qed.

Lemma prod_ball_triangle :
  forall (x y z : U * V) (e1 e2 : R),
  prod_ball x e1 y -> prod_ball y e2 z ->
  prod_ball x (e1 + e2) z.
Proof.
intros x y z e1 e2 [H1 H2] [H3 H4].
split ; eapply ball_triangle ; eassumption.
Qed.


End prod_UniformSpace.

Definition prod_UniformSpace_mixin (U V : UniformSpace) :=
  UniformSpace.Mixin (U * V) _ prod_ball_center prod_ball_sym prod_ball_triangle.

Canonical prod_UniformSpace (U V : UniformSpace) :=
  UniformSpace.Pack (U * V) (prod_UniformSpace_mixin U V) (U * V).

Section prod_ModuleSpace.

Context {K : Ring} {U V : ModuleSpace K}.

Definition prod_scal (x : K) (u : U * V) :=
  (scal x (fst u), scal x (snd u)).

Lemma prod_scal_assoc :
  forall (x y : K) (u : U * V),
  prod_scal x (prod_scal y u) = prod_scal (mult x y) u.
Proof.
intros x y u.
apply (f_equal2 pair) ; apply scal_assoc.
Qed.

Lemma prod_scal_one :
  forall u : U * V,
  prod_scal one u = u.
Proof.
intros [u v].
apply (f_equal2 pair) ; apply scal_one.
Qed.

Lemma prod_scal_distr_l :
  forall (x : K) (u v : U * V),
  prod_scal x (prod_plus u v) = prod_plus (prod_scal x u) (prod_scal x v).
Proof.
intros x u v.
apply (f_equal2 pair) ; apply scal_distr_l.
Qed.

Lemma prod_scal_distr_r :
  forall (x y : K) (u : U * V),
  prod_scal (plus x y) u = prod_plus (prod_scal x u) (prod_scal y u).
Proof.
intros x y u.
apply (f_equal2 pair) ; apply scal_distr_r.
Qed.

End prod_ModuleSpace.

Definition prod_ModuleSpace_mixin (K : Ring) (U V : ModuleSpace K) :=
  ModuleSpace.Mixin K _ _ (@prod_scal_assoc K U V) prod_scal_one prod_scal_distr_l prod_scal_distr_r.

Canonical prod_ModuleSpace (K : Ring) (U V : ModuleSpace K) :=
  ModuleSpace.Pack K (U * V) (ModuleSpace.Class _ _ _ (prod_ModuleSpace_mixin K U V)) (U * V).

Canonical prod_NormedModuleAux (K : AbsRing) (U V : NormedModuleAux K) :=
  NormedModuleAux.Pack K (U * V) (NormedModuleAux.Class _ _ (ModuleSpace.class K _) (UniformSpace.class (prod_UniformSpace U V))) (U * V).

Lemma sqrt_plus_sqr :
  forall x y : R, Rmax (Rabs x) (Rabs y) <= sqrt (x ^ 2 + y ^ 2) <= sqrt 2 * Rmax (Rabs x) (Rabs y).
Proof.
intros x y.
split.
- rewrite -!sqrt_Rsqr_abs.
  apply Rmax_case ; apply sqrt_le_1_alt, Rminus_le_0 ;
  rewrite /Rsqr /= ; ring_simplify ; by apply pow2_ge_0.
- apply Rmax_case_strong ; intros H0 ;
  rewrite -!sqrt_Rsqr_abs ;
  rewrite -?sqrt_mult ;
  try (by apply Rle_0_sqr) ;
  try (by apply Rlt_le, Rlt_0_2) ;
  apply sqrt_le_1_alt ; simpl ; [ rewrite Rplus_comm | ] ;
  rewrite /Rsqr ; apply Rle_minus_r ; ring_simplify ;
  apply Rsqr_le_abs_1 in H0 ; by rewrite /pow !Rmult_1_r.
Qed.

Section prod_NormedModule.

Context {K : AbsRing} {U V : NormedModule K}.

Definition prod_norm (x : U * V) :=
  sqrt (norm (fst x) ^ 2 + norm (snd x) ^ 2).

Lemma prod_norm_triangle :
  forall x y : U * V,
  prod_norm (plus x y) <= prod_norm x + prod_norm y.
Proof.
intros [xu xv] [yu yv].
rewrite /prod_norm /= !Rmult_1_r.
apply Rle_trans with (sqrt (Rsqr (norm xu + norm yu) + Rsqr (norm xv + norm yv))).
- apply sqrt_le_1_alt.
  apply Rplus_le_compat.
  apply Rsqr_le_abs_1.
  rewrite -> 2!Rabs_pos_eq.
  apply: norm_triangle.
  apply Rplus_le_le_0_compat ; apply norm_ge_0.
  apply norm_ge_0.
  apply Rsqr_le_abs_1.
  rewrite -> 2!Rabs_pos_eq.
  apply: norm_triangle.
  apply Rplus_le_le_0_compat ; apply norm_ge_0.
  apply norm_ge_0.
- apply Rsqr_incr_0_var.
  apply Rminus_le_0.
  unfold Rsqr ; simpl ; ring_simplify.
  rewrite /pow ?Rmult_1_r.
  rewrite ?sqrt_sqrt ; ring_simplify.
  replace (-2 * norm xu * norm yu - 2 * norm xv * norm yv)
    with (-(2 * (norm xu * norm yu + norm xv * norm yv))) by ring.
  rewrite Rmult_assoc -sqrt_mult.
  rewrite Rplus_comm.
  apply -> Rminus_le_0.
  apply Rmult_le_compat_l.
  apply Rlt_le, Rlt_0_2.
  apply Rsqr_incr_0_var.
  apply Rminus_le_0.
  rewrite /Rsqr ?sqrt_sqrt ; ring_simplify.
  replace (norm xu ^ 2 * norm yv ^ 2 - 2 * norm xu * norm xv * norm yu * norm yv + norm xv ^ 2 * norm yu ^ 2)
    with ((norm xu * norm yv - norm xv * norm yu) ^ 2) by ring.
  apply pow2_ge_0.
  repeat apply Rplus_le_le_0_compat ; apply Rmult_le_pos ; apply pow2_ge_0.
  apply sqrt_pos.
  apply Rplus_le_le_0_compat ; apply Rle_0_sqr.
  apply Rplus_le_le_0_compat ; apply Rle_0_sqr.
  replace (norm xu ^ 2 + 2 * norm xu * norm yu + norm yu ^ 2 + norm xv ^ 2 + 2 * norm xv * norm yv + norm yv ^ 2)
    with ((norm xu + norm yu) ^ 2 + (norm xv + norm yv) ^ 2) by ring.
  apply Rplus_le_le_0_compat ; apply pow2_ge_0.
  apply Rplus_le_le_0_compat ; apply pow2_ge_0.
  apply Rplus_le_le_0_compat ; apply pow2_ge_0.
  apply Rplus_le_le_0_compat ; apply sqrt_pos.
Qed.

Lemma prod_norm_scal :
  forall (l : K) (x : U * V),
  prod_norm (scal l x) <= abs l * prod_norm x.
Proof.
intros l [xu xv].
rewrite /prod_norm /= -(sqrt_Rsqr (abs l)).
2: apply abs_ge_0.
rewrite !Rmult_1_r.
rewrite -sqrt_mult.
2: apply Rle_0_sqr.
apply sqrt_le_1_alt.
rewrite Rmult_plus_distr_l.
unfold Rsqr.
apply Rplus_le_compat.
replace (abs l * abs l * (norm xu * norm xu)) with ((abs l * norm xu) * (abs l * norm xu)) by ring.
apply Rmult_le_compat.
apply norm_ge_0.
apply norm_ge_0.
exact (norm_scal l xu).
exact (norm_scal l xu).
replace (abs l * abs l * (norm xv * norm xv)) with ((abs l * norm xv) * (abs l * norm xv)) by ring.
apply Rmult_le_compat.
apply norm_ge_0.
apply norm_ge_0.
exact (norm_scal l xv).
exact (norm_scal l xv).
apply Rplus_le_le_0_compat ; apply Rle_0_sqr.
Qed.

Lemma prod_norm_compat1 :
  forall (x y : U * V) (eps : R),
  prod_norm (minus y x) < eps -> ball x eps y.
Proof.
intros [xu xv] [yu yv] eps H.
generalize (Rle_lt_trans _ _ _ (proj1 (sqrt_plus_sqr _ _)) H).
rewrite -> !Rabs_pos_eq by apply norm_ge_0.
intros H'.
split ;
  apply norm_compat1 ;
  apply Rle_lt_trans with (2 := H').
apply Rmax_l.
apply Rmax_r.
Qed.

Definition prod_norm_factor :=
  sqrt 2 * Rmax (@norm_factor K U) (@norm_factor K V).

Lemma prod_norm_compat2 :
  forall (x y : U * V) (eps : posreal),
  ball x eps y ->
  prod_norm (minus y x) < prod_norm_factor * eps.
Proof.
intros [xu xv] [yu yv] eps [Bu Bv].
apply Rle_lt_trans with (1 := proj2 (sqrt_plus_sqr _ _)).
simpl.
rewrite Rmult_assoc.
apply Rmult_lt_compat_l.
apply sqrt_lt_R0.
apply Rlt_0_2.
rewrite -> !Rabs_pos_eq by apply norm_ge_0.
rewrite Rmax_mult.
apply Rmax_case.
apply Rlt_le_trans with (2 := Rmax_l _ _).
now apply norm_compat2.
apply Rlt_le_trans with (2 := Rmax_r _ _).
now apply norm_compat2.
apply Rlt_le.
apply cond_pos.
Qed.

Lemma prod_norm_eq_zero :
  forall x : U * V,
  prod_norm x = 0 -> x = zero.
Proof.
intros [xu xv] H.
apply sqrt_eq_0 in H.
rewrite !(pow_Rsqr _ 1) !pow_1 in H.
apply Rplus_sqr_eq_0 in H.
destruct H as [H1 H2].
apply norm_eq_zero in H1.
apply norm_eq_zero in H2.
simpl in H1, H2.
now rewrite H1 H2.
apply Rplus_le_le_0_compat ; apply pow2_ge_0.
Qed.

End prod_NormedModule.

Definition prod_NormedModule_mixin (K : AbsRing) (U V : NormedModule K) :=
  NormedModule.Mixin K _ (@prod_norm K U V) prod_norm_factor prod_norm_triangle
  prod_norm_scal prod_norm_compat1 prod_norm_compat2 prod_norm_eq_zero.

Canonical prod_NormedModule (K : AbsRing) (U V : NormedModule K) :=
  NormedModule.Pack K (U * V) (NormedModule.Class K (U * V) _ (prod_NormedModule_mixin K U V)) (U * V).

Lemma norm_prod {K : AbsRing}
  {U : NormedModule K} {V : NormedModule K}
  (x : U) (y : V) :
  Rmax (norm x) (norm y) <= norm (x,y) <= sqrt 2 * Rmax (norm x) (norm y).
Proof.
  rewrite -(Rabs_pos_eq (norm x)).
  rewrite -(Rabs_pos_eq (norm y)).
  apply sqrt_plus_sqr.
  by apply norm_ge_0.
  by apply norm_ge_0.
Qed.

(** ** Iterated Products *)

Fixpoint Tn (n : nat) (T : Type) : Type :=
  match n with
  | O => unit
  | S n => prod T (Tn n T)
  end.

Notation "[ x1 , .. , xn ]" := (pair x1 .. (pair xn tt) .. ).

Fixpoint mk_Tn {T} (n : nat) (u : nat -> T) : Tn n T :=
  match n with
    | O => (tt : Tn O T)
    | S n => (u O, mk_Tn n (fun n => u (S n)))
  end.
Fixpoint coeff_Tn {T} {n : nat} (x0 : T) : (Tn n T) -> nat -> T :=
  match n with
  | O => fun (_ : Tn O T) (_ : nat) => x0
  | S n' => fun (v : Tn (S n') T) (i : nat) => match i with
           | O => fst v
           | S i => coeff_Tn x0 (snd v) i
           end
  end.
Lemma mk_Tn_bij {T} {n : nat} (x0 : T) (v : Tn n T) :
  mk_Tn n (coeff_Tn x0 v) = v.
Proof.
  induction n ; simpl.
  now apply unit_ind.
  rewrite IHn ; by destruct v.
Qed.
Lemma coeff_Tn_bij {T} {n : nat} (x0 : T) (u : nat -> T) :
  forall i, (i < n)%nat -> coeff_Tn x0 (mk_Tn n u) i = u i.
Proof.
  revert u ; induction n => /= u i Hi.
  by apply lt_n_O in Hi.
  destruct i.
  by [].
  now apply (IHn (fun n => u (S n))), lt_S_n.
Qed.
Lemma coeff_Tn_ext {T} {n : nat} (x1 x2 : T) (v1 v2 : Tn n T) :
  v1 = v2 <-> forall i, (i < n)%nat -> coeff_Tn x1 v1 i = coeff_Tn x2 v2 i.
Proof.
  split.
  + move => -> {v1}.
    induction n => i Hi.
    by apply lt_n_O in Hi.
    destruct i ; simpl.
    by [].
    by apply IHn, lt_S_n.
  + induction n => H.
    apply unit_ind ; move: (v1) ; now apply unit_ind.
    apply injective_projections.
    by apply (H O), lt_O_Sn.
    apply IHn => i Hi.
    by apply (H (S i)), lt_n_S.
Qed.
Lemma mk_Tn_ext {T} (n : nat) (u1 u2 : nat -> T) :
  (forall i, (i < n)%nat -> (u1 i) = (u2 i))
    <-> (mk_Tn n u1) = (mk_Tn n u2).
Proof.
  move: u1 u2 ; induction n ; simpl ; split ; intros.
  by [].
  by apply lt_n_O in H0.
  apply f_equal2.
  by apply H, lt_O_Sn.
  apply IHn => i Hi.
  by apply H, lt_n_S.
  destruct i.
  by apply (f_equal (@fst _ _)) in H.
  move: i {H0} (lt_S_n _ _ H0).
  apply IHn.
  by apply (f_equal (@snd _ _)) in H.
Qed.

(*
Global Instance AbelianGroup_Tn {T} :
  AbelianGroup T -> forall n, AbelianGroup (Tn n T) | 10.
Proof.
  intro GT.
  elim => /= [ | n IH].
  - apply Build_AbelianGroup with (fun _ _ => tt) (fun _ => tt) tt ; auto.
    by apply unit_ind.
  - by apply AbelianGroup_prod.
Defined.

Global Instance MetricBall_Tn :
  forall T, MetricBall T -> forall n, MetricBall (Tn n T) | 10.
Proof.
intros T MT n.
elim: n => [ | n MTn].
by apply Build_MetricBall with (fun _ _ _ => True).
by apply MetricBall_prod.
Defined.

Global Instance VectorSpace_mixin_Tn {T} {K} {FK : Ring K} :
  forall GT : AbelianGroup T,
  VectorSpace_mixin T K GT ->
  forall n, VectorSpace_mixin (Tn n T) K (AbelianGroup_Tn GT n) | 10.
Proof.
  intros GT VV.
  elim => [ | n VVn].
  apply Build_VectorSpace_mixin with (fun _ _ => tt) ; by apply unit_ind.
  by apply VectorSpace_mixin_prod.
Defined.

Global Instance VectorSpace_Tn {T} {K} {FK : Ring K} :
  VectorSpace T K -> forall n, VectorSpace (Tn n T) K | 10.
Proof.
  intros VV n.
  apply Build_VectorSpace with (AbelianGroup_Tn _ n).
  now apply VectorSpace_mixin_Tn, VV.
Defined.

Global Instance NormedVectorSpace_Tn {T} {K} {FK : AbsRing K} :
  NormedVectorSpace T K ->
  forall n, NormedVectorSpace (Tn n T) K | 10.
Proof.
  move => VT.
  elim => [ | n NVTn].
  - econstructor.
    apply Build_NormedVectorSpace_mixin with (fun _ => 0).
    move => _ _.
    rewrite Rplus_0_l ; by apply Rle_refl.
    move => l _ ; rewrite Rmult_0_r ; by apply Rle_refl.
    easy.
    exists (mkposreal _ Rlt_0_1).
    intros x y eps _.
    rewrite Rmult_1_l.
    apply cond_pos.
  - by apply NormedVectorSpace_prod.
Defined.
*)

(** *)

Fixpoint Fn (n : nat) (T U : Type) : Type :=
  match n with
  | O => U
  | S n => T -> Fn n T U
  end.

(*
Global Instance MetricBall_Fn {T M} (n : nat) :
  MetricBall M -> MetricBall (Fn n T M) | 10.
Proof.
  intros MM.
  elim: n => /= [ | n IHn].
  exact MM.
  exact (MetricBall_fct IHn).
Defined.
*)

(** ** Matrices *)

Section Matrices.

Context {T : Type}.

Definition matrix (m n : nat) := Tn m (Tn n T).

Definition coeff_mat {m n : nat} (x0 : T) (A : matrix m n) (i j : nat) :=
  coeff_Tn x0 (coeff_Tn (mk_Tn _ (fun _ => x0)) A i) j.

Definition mk_matrix (m n : nat) (U : nat -> nat -> T) : matrix m n :=
  mk_Tn m (fun i => (mk_Tn n (U i))).

Lemma mk_matrix_bij {m n : nat} (x0 : T) (A : matrix m n) :
  mk_matrix m n (coeff_mat x0 A) = A.
Proof.
  unfold mk_matrix, coeff_mat.
  unfold matrix in A.
  rewrite -{2}(mk_Tn_bij (mk_Tn _ (fun _ => x0)) A).
  apply mk_Tn_ext.
  intros i Hi.
  by rewrite mk_Tn_bij.
Qed.

Lemma coeff_mat_bij {m n : nat} (x0 : T) (u : nat -> nat -> T) :
  forall i j, (i < m)%nat -> (j < n)%nat -> coeff_mat x0 (mk_matrix m n u) i j = u i j.
Proof.
  intros i j Hi Hj.
  unfold mk_matrix, coeff_mat.
  by rewrite 2?coeff_Tn_bij .
Qed.

Lemma coeff_mat_ext_aux {m n : nat} (x1 x2 : T) (v1 v2 : matrix m n) :
  v1 = v2 <-> forall i j, (i < m)%nat -> (j < n)%nat -> (coeff_mat x1 v1 i j) = (coeff_mat x2 v2 i j).
Proof.
  split => Hv.
  + move => i j Hi Hj.
    by repeat apply coeff_Tn_ext.
  + unfold matrix in v1, v2.
    rewrite -(mk_matrix_bij x1 v1) -(mk_matrix_bij x2 v2).
    unfold mk_matrix.
    apply mk_Tn_ext => i Hi.
    apply mk_Tn_ext => j Hj.
    by apply Hv.
Qed.

Lemma coeff_mat_ext {m n : nat} (x0 : T) (v1 v2 : matrix m n) :
  v1 = v2 <-> forall i j, (coeff_mat x0 v1 i j) = (coeff_mat x0 v2 i j).
Proof.
  split.
  by move => ->.
  intro H.
  now apply (coeff_mat_ext_aux x0 x0 v1 v2).
Qed.

Lemma mk_matrix_ext (m n : nat) (u1 u2 : nat -> nat -> T) :
  (forall i j, (i < m)%nat -> (j < n)%nat -> (u1 i j) = (u2 i j))
    <-> (mk_matrix m n u1) = (mk_matrix m n u2).
Proof.
  split => H.
  + apply (mk_Tn_ext m) => i Hi.
    apply (mk_Tn_ext n) => j Hj.
    by apply H.
  + intros i j Hi Hj.
    apply (mk_Tn_ext n).
    apply (mk_Tn_ext m (fun i => mk_Tn n (u1 i)) (fun i => mk_Tn n (u2 i))).
    apply H.
    by [].
    by [].
Qed.

End Matrices.

Section MatrixGroup.

Context {G : AbelianGroup} {m n : nat}.

Definition Mzero := mk_matrix m n (fun i j => @zero G).

Definition Mplus (A B : @matrix G m n) :=
  mk_matrix m n (fun i j => plus (coeff_mat zero A i j) (coeff_mat zero B i j)).

Definition Mopp (A : @matrix G m n) :=
  mk_matrix m n (fun i j => opp (coeff_mat zero A i j)).

Lemma Mplus_comm :
  forall A B : @matrix G m n,
  Mplus A B = Mplus B A.
Proof.
  intros A B.
  apply mk_matrix_ext => i j Hi Hj.
  by apply plus_comm.
Qed.

Lemma Mplus_assoc :
  forall A B C : @matrix G m n,
  Mplus A (Mplus B C) = Mplus (Mplus A B) C.
Proof.
  intros A B C.
  apply mk_matrix_ext => /= i j Hi Hj.
  rewrite ?coeff_mat_bij => //.
  by apply plus_assoc.
Qed.

Lemma Mplus_zero_r :
  forall A : @matrix G m n,
  Mplus A Mzero = A.
Proof.
  intros A.
  apply (coeff_mat_ext_aux zero zero) => i j Hi Hj.
  rewrite ?coeff_mat_bij => //=.
  by apply plus_zero_r.
Qed.

Lemma Mplus_opp_r :
  forall A : @matrix G m n,
  Mplus A (Mopp A) = Mzero.
Proof.
  intros A.
  apply (coeff_mat_ext_aux zero zero) => i j Hi Hj.
  rewrite ?coeff_mat_bij => //=.
  by apply plus_opp_r.
Qed.

Definition matrix_AbelianGroup_mixin :=
  AbelianGroup.Mixin _ _ _ _ Mplus_comm Mplus_assoc Mplus_zero_r Mplus_opp_r.

Canonical matrix_AbelianGroup :=
  AbelianGroup.Pack _ matrix_AbelianGroup_mixin (@matrix G m n).

End MatrixGroup.

Section MatrixRing.

Context {T : Ring}.

Fixpoint Mone_seq i j : T :=
  match i,j with
    | O, O => one
    | O, S _ | S _, O => zero
    | S i, S j => Mone_seq i j end.

Definition Mone {n} : matrix n n :=
  mk_matrix n n Mone_seq.

Lemma Mone_seq_diag :
  forall i j : nat, i = j -> Mone_seq i j = @one T.
Proof.
  move => i j <- {j}.
  by induction i.
Qed.
Lemma Mone_seq_not_diag :
  forall i j : nat, i <> j -> Mone_seq i j = @zero T.
Proof.
  elim => //= [ | i IHi] j Hij ;
  destruct j => //=.
  apply IHi.
  contradict Hij.
  by rewrite Hij.
Qed.

Definition Mmult {n m k} (A : @matrix T n m) (B : @matrix T m k) :=
  mk_matrix n k (fun i j => sum_n (fun l => mult (coeff_mat zero A i l) (coeff_mat zero B l j)) (pred m)).

Lemma Mmult_assoc {n m k l} :
  forall (A : matrix n m) (B : matrix m k) (C : matrix k l),
  Mmult A (Mmult B C) = Mmult (Mmult A B) C.
Proof.
  intros A B C.
  apply mk_matrix_ext => n' l' Hn' Hl'.
  unfold Mmult at 1.
  - transitivity (sum_n (fun l0 : nat => mult (coeff_mat zero A n' l0)
      (sum_n (fun l1 : nat => mult (coeff_mat zero B l0 l1) (coeff_mat zero C l1 l')) (pred k))) (pred m)).
    destruct m ; simpl.
    unfold coeff_mat ; simpl.
    by rewrite 2!mult_zero_l.
    apply sum_n_m_ext_loc ; simpl => m' [ _ Hm'].
    apply f_equal.
    rewrite coeff_mat_bij //.
    by apply le_lt_n_Sm, Hm'.
  - transitivity (sum_n (fun l0 : nat => sum_n
      (fun l1 : nat => mult (coeff_mat zero A n' l0) (mult (coeff_mat zero B l0 l1) (coeff_mat zero C l1 l'))) (pred k)) (pred m)).
    destruct m ; simpl.
    rewrite /sum_n !sum_n_n.
    unfold coeff_mat ; simpl.
    rewrite mult_zero_l.
    rewrite sum_n_m_mult_l.
    by rewrite mult_zero_l.
    apply sum_n_m_ext_loc ; simpl => m' [_ Hm'].
    apply sym_eq, sum_n_m_mult_l.
  rewrite sum_n_switch.
  destruct k ; simpl.
  unfold coeff_mat ; simpl.
  rewrite mult_zero_l.
  rewrite /sum_n sum_n_m_mult_r.
  by rewrite mult_zero_r.
  apply sum_n_m_ext_loc => k' [_ Hk'].
  transitivity (mult (sum_n (fun l1 : nat => mult (coeff_mat zero A n' l1) (coeff_mat zero B l1 k')) (pred m))
    (coeff_mat zero C k' l')).
  rewrite -sum_n_m_mult_r.
  apply sum_n_m_ext_loc => m' [_ Hm'].
  apply mult_assoc.
  apply f_equal2.
  unfold Mmult ; rewrite coeff_mat_bij //.
  by apply le_lt_n_Sm.
  by [].
Qed.

Lemma Mmult_one_r {m n} :
  forall x : matrix m n, Mmult x Mone = x.
Proof.
  intros A.
  rewrite -{2}(mk_matrix_bij zero A).
  apply mk_matrix_ext => /= i j Hi Hj.
  destruct n ; simpl.
  by apply lt_n_O in Hj.
  move: (coeff_mat zero A) => {A} A.
  erewrite sum_n_ext_loc ; last first.
  move => /= k Hk.
  rewrite /Mone coeff_mat_bij //.
  by apply le_lt_n_Sm.
  rewrite /sum_n (sum_n_m_Chasles _ _ j) //.
  2: by apply le_O_n.
  2: by apply lt_n_Sm_le.
  rewrite (sum_n_m_ext_loc _ (fun _ => zero) (S j)).
  rewrite sum_n_m_const_zero plus_zero_r.
  rewrite -/(sum_n _ _).
  destruct j => //.
  by rewrite sum_O Mone_seq_diag // mult_one_r.
  rewrite sum_Sn.
  rewrite (sum_n_ext_loc _ (fun _ => zero)).
  rewrite /sum_n sum_n_m_const_zero plus_zero_l.
  by rewrite Mone_seq_diag // mult_one_r.
  move => k Hk.
  rewrite Mone_seq_not_diag.
  by apply mult_zero_r.
  by apply MyNat.lt_neq, le_lt_n_Sm.
  move => k [Hk _].
  rewrite Mone_seq_not_diag.
  by apply mult_zero_r.
  by apply sym_not_eq, MyNat.lt_neq.
Qed.

Lemma Mmult_one_l {m n} :
  forall x : matrix m n, Mmult Mone x = x.
Proof.
  intros A.
  rewrite -{2}(mk_matrix_bij zero A).
  apply mk_matrix_ext => /= i j Hi Hj.
  destruct m ; simpl.
  by apply lt_n_O in Hi.
  move: (coeff_mat zero A) => {A} A.
  erewrite sum_n_ext_loc ; last first.
  move => /= k Hk.
  rewrite /Mone coeff_mat_bij //.
  by apply le_lt_n_Sm.
  rewrite /sum_n (sum_n_m_Chasles _ _ i) //.
  2: by apply le_O_n.
  2: by apply lt_n_Sm_le.
  rewrite (sum_n_m_ext_loc _ (fun _ => zero) (S i)).
  rewrite sum_n_m_const_zero plus_zero_r.
  rewrite -/(sum_n _ _).
  destruct i => //.
  by rewrite sum_O Mone_seq_diag // mult_one_l.
  rewrite sum_Sn.
  rewrite (sum_n_ext_loc _ (fun _ => zero)).
  rewrite /sum_n sum_n_m_const_zero plus_zero_l.
  by rewrite Mone_seq_diag // mult_one_l.
  move => k Hk.
  rewrite Mone_seq_not_diag.
  by apply mult_zero_l.
  by apply sym_not_eq, MyNat.lt_neq, le_lt_n_Sm.
  move => k [Hk _].
  rewrite Mone_seq_not_diag.
  by apply mult_zero_l.
  by apply MyNat.lt_neq.
Qed.

Lemma Mmult_distr_r {m n k} :
  forall (A B : @matrix T m n) (C : @matrix T n k),
  Mmult (Mplus A B) C = Mplus (Mmult A C) (Mmult B C).
Proof.
  intros A B C.
  unfold Mmult, plus ; simpl ; unfold Mplus.
  apply mk_matrix_ext => i j Hi Hj.
  rewrite ?coeff_mat_bij => //=.
  rewrite -sum_n_m_plus.
  destruct n ; simpl.
  unfold coeff_mat ; simpl.
  by rewrite ?mult_zero_l plus_zero_l.
  apply sum_n_m_ext_loc => l [_ Hl].
  rewrite ?coeff_mat_bij => //=.
  by apply mult_distr_r.
  by apply le_lt_n_Sm.
Qed.

Lemma Mmult_distr_l {m n k} :
  forall (A : @matrix T m n) (B C : @matrix T n k),
  Mmult A (Mplus B C) = Mplus (Mmult A B) (Mmult A C).
Proof.
  intros A B C.
  unfold Mmult, plus ; simpl ; unfold Mplus.
  apply mk_matrix_ext => i j Hi Hj.
  rewrite ?coeff_mat_bij => //=.
  rewrite -sum_n_m_plus.
  destruct n ; simpl.
  unfold coeff_mat ; simpl.
  by rewrite ?mult_zero_l plus_zero_l.
  apply sum_n_m_ext_loc => l [_ Hl].
  rewrite ?coeff_mat_bij => //=.
  by apply mult_distr_l.
  by apply le_lt_n_Sm.
Qed.

Definition matrix_Ring_mixin {n} :=
  Ring.Mixin _ _ _ (@Mmult_assoc n n n n) Mmult_one_r Mmult_one_l Mmult_distr_r Mmult_distr_l.

Canonical matrix_Ring {n} :=
  Ring.Pack (@matrix T n n) (Ring.Class _ _ matrix_Ring_mixin) (@matrix T n n).

Definition matrix_ModuleSpace_mixin {m n} :=
  ModuleSpace.Mixin (@matrix_Ring m) (@matrix_AbelianGroup T m n) Mmult
    Mmult_assoc Mmult_one_l Mmult_distr_l Mmult_distr_r.

Canonical matrix_ModuleSpace {m n} :=
  ModuleSpace.Pack _ (@matrix T m n) (ModuleSpace.Class _ _ _ matrix_ModuleSpace_mixin) (@matrix T m n).

End MatrixRing.

(** * The topology on natural numbers *)

Definition eventually (P : nat -> Prop) :=
  exists N : nat, forall n, (N <= n)%nat -> P n.

Global Instance eventually_filter : ProperFilter eventually.
Proof.
constructor.
  intros P [N H].
  exists N.
  apply H.
  apply le_refl.
constructor.
- now exists 0%nat.
- intros P Q [NP HP] [NQ HQ].
  exists (max NP NQ).
  intros n Hn.
  split.
  apply HP.
  apply le_trans with (2 := Hn).
  apply Max.le_max_l.
  apply HQ.
  apply le_trans with (2 := Hn).
  apply Max.le_max_r.
- intros P Q H [NP HP].
  exists NP.
  intros n Hn.
  apply H.
  now apply HP.
Qed.

(** * The topology on real numbers *)

Definition R_AbelianGroup_mixin :=
  AbelianGroup.Mixin _ _ _ _ Rplus_comm (fun x y z => sym_eq (Rplus_assoc x y z)) Rplus_0_r Rplus_opp_r.

Canonical R_AbelianGroup :=
  AbelianGroup.Pack _ R_AbelianGroup_mixin R.

Definition R_Ring_mixin :=
  Ring.Mixin _ _ _ (fun x y z => sym_eq (Rmult_assoc x y z)) Rmult_1_r Rmult_1_l Rmult_plus_distr_r Rmult_plus_distr_l.

Canonical R_Ring :=
  Ring.Pack R (Ring.Class _ _ R_Ring_mixin) R.

Lemma Rabs_m1 :
  Rabs (-1) = 1.
Proof.
  rewrite Rabs_Ropp.
  exact Rabs_R1.
Qed.

Definition R_AbsRing_mixin :=
  AbsRing.Mixin _ _ Rabs_R0 Rabs_m1 Rabs_triang (fun x y => Req_le _ _ (Rabs_mult x y)) Rabs_eq_0.

Canonical R_AbsRing :=
  AbsRing.Pack R (AbsRing.Class _ _ R_AbsRing_mixin) R.

Definition R_UniformSpace_mixin :=
  AbsRing_UniformSpace_mixin R_AbsRing.

Canonical R_UniformSpace :=
  UniformSpace.Pack R R_UniformSpace_mixin R.

Definition R_complete_lim (F : (R -> Prop) -> Prop) : R :=
  Lub_Rbar (fun x : R => F (ball (x + 1) (mkposreal _ Rlt_0_1))).

Lemma R_complete_ax1 :
  forall F : (R -> Prop) -> Prop,
  ProperFilter' F ->
  (forall eps : posreal, exists x : R, F (ball x eps)) ->
  forall eps : posreal, F (ball (R_complete_lim F) eps).
Proof.
intros F FF HF eps.
unfold R_complete_lim.
generalize (Lub_Rbar_correct (fun x : R => F (ball (x + 1) (mkposreal _ Rlt_0_1)))).
generalize (Lub_Rbar (fun x : R => F (ball (x + 1) (mkposreal _ Rlt_0_1)))).
intros [x| |] [Hx1 Hx2].
-
set (eps' := pos_div_2 (mkposreal _ (Rmin_case _ _ _ Rlt_R0_R2 (cond_pos eps)))).
destruct (HF eps') as [z Hz].
assert (H1 : z - Rmin 2 eps / 2 + 1 <= x + 1).
  apply Rplus_le_compat_r.
  apply Hx1.
  revert Hz.
  apply filter_imp.
  unfold ball ; simpl ; intros u Bu.
  apply (Rabs_lt_between' u z) in Bu.
  apply Rabs_lt_between'.
  clear -Bu.
  destruct Bu as [Bu1 Bu2].
  assert (H := Rmin_l 2 eps).
  split ; Fourier.fourier.
assert (H2 : x + 1 <= z + Rmin 2 eps / 2 + 1).
  apply Rplus_le_compat_r.
  apply (Hx2 (Finite _)).
  intros v Hv.
  apply Rbar_not_lt_le => Hlt.
  apply filter_not_empty.
  generalize (filter_and _ _ Hz Hv).
  apply filter_imp.
  unfold ball ; simpl ; intros w [Hw1 Hw2].
  apply (Rabs_lt_between' w z) in Hw1.
  destruct Hw1 as [_ Hw1].
  apply (Rabs_lt_between' w (v + 1)) in Hw2.
  destruct Hw2 as [Hw2 _].
  clear -Hw1 Hw2 Hlt.
  simpl in Hw1, Hw2, Hlt.
  Fourier.fourier.
revert Hz.
apply filter_imp.
unfold ball ; simpl ; intros u Hu.
apply (Rabs_lt_between' u z) in Hu.
apply Rabs_lt_between'.
assert (H3 := Rmin_l 2 eps).
assert (H4 := Rmin_r 2 eps).
clear -H1 H2 Hu H3 H4.
destruct Hu.
split ; Fourier.fourier.
-
  destruct (HF (mkposreal _ Rlt_0_1)) as [y Fy].
  elim (Hx2 (y + 1)).
  intros x Fx.
  apply Rbar_not_lt_le => Hlt.
  apply filter_not_empty.
  generalize (filter_and _ _ Fy Fx).
  apply filter_imp.
  intros z [Hz1 Hz2].
  revert Hlt.
  apply Rbar_le_not_lt.
  apply Rplus_le_reg_r with (-(y - 1)).
  replace (y + 1 + -(y - 1)) with 2 by ring.
  apply Rabs_le_between.
  apply Rlt_le.
  generalize (ball_triangle y z (x + 1) 1 1) => /= H.
  replace (x + -(y - 1)) with ((x + 1) - y) by ring.
  apply H.
  apply Hz1.
  apply ball_sym in Hz2.
  apply Hz2.
-
  destruct (HF (mkposreal _ Rlt_0_1)) as [y Fy].
  elim (Hx1 (y - 1)).
  now replace (y - 1 + 1) with y by ring.
Qed.

Lemma R_complete :
  forall F : (R -> Prop) -> Prop,
  ProperFilter F ->
  (forall eps : posreal, exists x : R, F (ball x eps)) ->
  forall eps : posreal, F (ball (R_complete_lim F) eps).
Proof.
intros F FF.
apply R_complete_ax1.
by apply Proper_StrongProper.
Qed.

Lemma R_complete_ax2 :
  forall F1 F2 : (R -> Prop) -> Prop,
  filter_le F1 F2 -> filter_le F2 F1 ->
  R_complete_lim F1 = R_complete_lim F2.
Proof.
intros F1 F2 H12 H21.
unfold R_complete_lim.
apply f_equal, Lub_Rbar_eqset.
split.
apply H21.
apply H12.
Qed.

Lemma R_complete_close :
  forall F1 F2 : (R -> Prop) -> Prop,
  filter_le F1 F2 -> filter_le F2 F1 ->
  close (R_complete_lim F1) (R_complete_lim F2).
Proof.
intros F1 F2 H12 H21.
replace (R_complete_lim F2) with (R_complete_lim F1).
intros eps.
apply ball_center.
exact: R_complete_ax2.
Qed.

Definition R_CompleteSpace_mixin :=
  CompleteSpace.Mixin _ R_complete_lim R_complete R_complete_close.

Canonical R_CompleteSpace :=
  CompleteSpace.Pack R (CompleteSpace.Class _ _ R_CompleteSpace_mixin) R.

Definition R_ModuleSpace_mixin :=
  AbsRing_ModuleSpace_mixin R_AbsRing.

Canonical R_ModuleSpace :=
  ModuleSpace.Pack _ R (ModuleSpace.Class _ _ _ R_ModuleSpace_mixin) R.

Canonical R_NormedModuleAux :=
  NormedModuleAux.Pack _ R (NormedModuleAux.Class _ _ (ModuleSpace.class _ R_ModuleSpace) (UniformSpace.class R_UniformSpace)) R.

Definition R_NormedModule_mixin :=
  AbsRing_NormedModule_mixin R_AbsRing.

Canonical R_NormedModule :=
  NormedModule.Pack _ R (NormedModule.Class _ _ _ R_NormedModule_mixin) R.

Canonical R_CompleteNormedModule :=
  CompleteNormedModule.Pack _ R (CompleteNormedModule.Class R_AbsRing _ (NormedModule.class _ R_NormedModule) R_CompleteSpace_mixin) R.

Definition at_left x := within (fun u : R => Rlt u x) (locally x).
Definition at_right x := within (fun u : R => Rlt x u) (locally x).

Global Instance at_right_proper_filter : forall (x : R),
  ProperFilter (at_right x).
Proof.
  constructor.
  intros P [d Hd].
  exists (x + d / 2).
  apply Hd.
  apply @norm_compat1 ; rewrite /norm /minus /plus /opp /= /abs /=.
  ring_simplify (x + d / 2 + - x).
  rewrite Rabs_pos_eq.
  apply Rlt_div_l.
  by apply Rlt_0_2.
  apply Rminus_lt_0 ; ring_simplify ; by apply d.
  apply Rlt_le, is_pos_div_2.
  apply Rminus_lt_0 ; ring_simplify ; by apply is_pos_div_2.
  apply within_filter, locally_filter.
Qed.
Global Instance at_left_proper_filter : forall (x : R),
  ProperFilter (at_left x).
Proof.
  constructor.
  intros P [d Hd].
  exists (x - d / 2).
  apply Hd.
  apply @norm_compat1 ; rewrite /norm /minus /plus /opp /= /abs /=.
  ring_simplify (x - d / 2 + - x).
  rewrite Rabs_Ropp Rabs_pos_eq.
  apply Rlt_div_l.
  by apply Rlt_0_2.
  apply Rminus_lt_0 ; ring_simplify ; by apply d.
  apply Rlt_le, is_pos_div_2.
  apply Rminus_lt_0 ; ring_simplify ; by apply is_pos_div_2.
  apply within_filter, locally_filter.
Qed.

(* *)

Lemma sum_n_Reals : forall a N, sum_n a N = sum_f_R0 a N.
Proof.
  intros a; induction N; simpl.
  apply sum_n_n.
  by rewrite sum_Sn IHN.
Qed.
Lemma sum_n_m_Reals a n m : (n <= m)%nat -> sum_n_m a n m = sum_f n m a.
Proof.
  induction m => //= Hnm.
  apply le_n_O_eq in Hnm.
  by rewrite -Hnm sum_n_n /=.
  case: (le_dec n m) => H.
  rewrite sum_n_Sm // IHm //.
  rewrite sum_f_n_Sm //.
  replace n with (S m).
  rewrite sum_n_n.
  by rewrite /sum_f minus_diag /=.
  apply le_antisym => //.
  apply not_le in H.
  by apply lt_le_S.
Qed.

Lemma sum_n_m_const (n m : nat) (a : R) :
  sum_n_m (fun _ => a) n m = INR (S m - n) * a.
Proof.
  rewrite /sum_n_m /iter_nat (iter_const _ a).
  by rewrite -{2}(seq.size_iota n (S m - n)).
Qed.
Lemma sum_n_const (n : nat) (a : R) :
  sum_n (fun _ => a) n = INR (S n) * a.
Proof.
  by rewrite /sum_n sum_n_m_const -minus_n_O.
Qed.

Lemma norm_sum_n_m {K : AbsRing} {V : NormedModule K} (a : nat -> V) (n m : nat) :
  norm (sum_n_m a n m) <= sum_n_m (fun n => norm (a n)) n m.
Proof.
  case: (le_dec n m) => Hnm.
  elim: m n a Hnm => /= [ | m IH] n a Hnm.
  apply le_n_O_eq in Hnm.
  rewrite -Hnm !sum_n_n.
  by apply Rle_refl.
  destruct n.
  rewrite /sum_n !sum_n_Sm ; try by apply le_O_n.
  eapply Rle_trans.
  apply norm_triangle.
  apply Rplus_le_compat_r, IH, le_O_n.
  rewrite -!sum_n_m_S.
  apply IH.
  by apply le_S_n.
  apply not_le in Hnm.
  rewrite !sum_n_m_zero // norm_zero.
  by apply Rle_refl.
Qed.

Lemma sum_n_m_le (a b : nat -> R) (n m : nat) :
  (forall k, a k <= b k)
  -> sum_n_m a n m <= sum_n_m b n m.
Proof.
  intros H.
  case: (le_dec n m) => Hnm.
  elim: m n a b Hnm H => /= [ | m IH] n a b Hnm H.
  apply le_n_O_eq in Hnm ; rewrite -Hnm.
  rewrite !sum_n_n ; by apply H.
  destruct n.
  rewrite !sum_n_Sm ; try by apply le_O_n.
  apply Rplus_le_compat.
  apply IH => // ; by apply le_O_n.
  by apply H.
  rewrite -!sum_n_m_S.
  apply IH => //.
  by apply le_S_n.
  apply not_le in Hnm.
  rewrite !sum_n_m_zero //.
  by apply Rle_refl.
Qed.

Lemma pow_n_pow :
  forall (x : R) k, pow_n x k = x^k.
Proof.
intros x; induction k; simpl.
easy.
now rewrite IHk.
Qed.

(** Continuity of norm *)

Lemma filterlim_norm {K : AbsRing} {V : NormedModule K} :
  forall (x : V), filterlim norm (locally x) (locally (norm x)).
Proof.
  intros x.
  apply (filterlim_filter_le_1 _ (locally_le_locally_norm x)).
  apply filterlim_locally => eps /=.
  exists eps ; move => /= y Hy.
  apply Rle_lt_trans with (2 := Hy).
  apply norm_triangle_inv.
Qed.

Lemma filterlim_norm_zero {U} {K : AbsRing} {V : NormedModule K}
  {F : (U -> Prop) -> Prop} {FF : Filter F} (f : U -> V) :
  filterlim (fun x => norm (f x)) F (locally 0)
  -> filterlim f F (locally (zero (G := V))).
Proof.
  intros Hf.
  apply filterlim_locally_ball_norm => eps.
  generalize (proj1 (filterlim_locally_ball_norm _ _) Hf eps) ;
  unfold ball_norm ; simpl.
  apply filter_imp => /= x.
  rewrite !minus_zero_r {1}/norm /= /abs /= Rabs_pos_eq //.
  by apply norm_ge_0.
Qed.

Lemma filterlim_bounded {K : AbsRing} {V : NormedModule K} (a : nat -> V) :
  (exists x, filterlim a eventually (locally x))
 -> {M : R | forall n, norm (a n) <= M}.
Proof.
  intros Ha.
  assert (exists x : R, filterlim (fun n => norm (a n)) eventually (locally x)).
    destruct Ha as [l Hl].
    exists (norm l).
    eapply filterlim_comp.
    by apply Hl.
    by apply filterlim_norm.
  clear Ha.

  destruct (LPO_ub_dec (fun n => norm (a n))) as [[M HM]|HM].
  now exists M.
  elimtype False.
  case: H => l Hl.
  assert (H := proj1 (filterlim_locally (F := eventually) _ l) Hl (mkposreal _ Rlt_0_1)).
  clear Hl ; simpl in H ; rewrite /ball /= /AbsRing_ball in H.
  destruct H as [N HN].
  specialize (HM (seq.foldr Rmax (1 + norm l) (seq.map (fun n => norm (a n)) (seq.iota 0 N)))).
  destruct HM as [n Hn].
  revert Hn.
  apply Rle_not_lt.
  elim: N a n HN => /=[ |N IH] a n HN.
  rewrite Rplus_comm.
  apply Rlt_le, Rabs_lt_between'.
  eapply Rle_lt_trans, HN.
  rewrite /abs /=.
  eapply Rle_trans, (norm_triangle_inv (norm (a n)) l).
  apply Req_le, f_equal, f_equal2 => //.
  apply sym_eq, Rabs_pos_eq, norm_ge_0.
  by apply le_O_n.
  case: n => [ | n].
  apply Rmax_l.
  eapply Rle_trans, Rmax_r.
  eapply Rle_trans.
  apply (IH (fun n => a (S n))).
  intros k Hk.
  apply HN.
  by apply le_n_S.
  clear.
  apply Req_le.
  elim: N 0%nat => /=[ |N IH] n0.
  by [].
  apply f_equal.
  apply IH.
Qed.

(** Some open sets of [R] *)

Lemma open_lt :
  forall y : R, open (fun u : R => u < y).
Proof.
intros y x Hxy.
apply Rminus_lt_0 in Hxy.
exists (mkposreal _ Hxy).
intros z Bz.
replace y with (x + (y - x)) by ring.
apply Rabs_lt_between'.
apply Bz.
Qed.

Lemma open_gt :
  forall y : R, open (fun u : R => y < u).
Proof.
intros y x Hxy.
apply Rminus_lt_0 in Hxy.
exists (mkposreal _ Hxy).
intros z Bz.
replace y with (x - (x - y)) by ring.
apply Rabs_lt_between'.
apply Bz.
Qed.

Lemma open_neq :
  forall y : R, open (fun u : R => u <> y).
Proof.
intros y.
apply (open_ext (fun u => u < y \/ y < u)).
intros u.
split.
apply Rlt_dichotomy_converse.
apply Rdichotomy.
apply open_or.
apply open_lt.
apply open_gt.
Qed.

(** Some closed sets of [R] *)

Lemma closed_le :
  forall y : R, closed (fun u : R => u <= y).
Proof.
intros y.
apply closed_ext with (fun u => not (Rlt y u)).
intros x.
split.
apply Rnot_lt_le.
apply Rle_not_lt.
apply closed_not.
apply open_gt.
Qed.

Lemma closed_ge :
  forall y : R, closed (fun u : R => y <= u).
Proof.
intros y.
apply closed_ext with (fun u => not (Rlt u y)).
intros x.
split.
apply Rnot_lt_le.
apply Rle_not_lt.
apply closed_not.
apply open_lt.
Qed.

Lemma closed_eq :
  forall y : R, closed (fun u : R => u = y).
Proof.
intros y.
apply closed_ext with (fun u => not (u <> y)).
intros x.
destruct (Req_dec x y) ; intuition.
apply closed_not.
apply open_neq.
Qed.

(** Local properties in [R] *)

Lemma locally_interval (P : R -> Prop) (x : R) (a b : Rbar) :
  Rbar_lt a x -> Rbar_lt x b ->
  (forall (y : R), Rbar_lt a y -> Rbar_lt y b -> P y) ->
  locally x P.
Proof.
  move => Hax Hxb Hp.
  case: (Rbar_lt_locally _ _ _ Hax Hxb) => d Hd.
  exists d => y Hy.
  now apply Hp ; apply Hd.
Qed.

(** * Topology on [R]² *)

Definition locally_2d (P : R -> R -> Prop) x y :=
  exists delta : posreal, forall u v, Rabs (u - x) < delta -> Rabs (v - y) < delta -> P u v.

Lemma locally_2d_locally :
  forall P x y,
  locally_2d P x y <-> locally (x,y) (fun z => P (fst z) (snd z)).
Proof.
intros P x y.
split ; intros [d H] ; exists d.
- simpl.
  intros [u v] H'.
  now apply H ; apply H'.
- intros u v Hu Hv.
  apply (H (u,v)).
  by split.
Qed.

Lemma locally_2d_impl_strong :
  forall (P Q : R -> R -> Prop) x y, locally_2d (fun u v => locally_2d P u v -> Q u v) x y ->
  locally_2d P x y -> locally_2d Q x y.
Proof.
intros P Q x y Li LP.
apply locally_2d_locally in Li.
apply locally_2d_locally in LP.
apply locally_locally in LP.
apply locally_2d_locally.
generalize (filter_and _ _ Li LP).
apply filter_imp.
intros [u v] [H1 H2].
apply H1.
now apply locally_2d_locally.
Qed.

Lemma locally_2d_singleton :
  forall (P : R -> R -> Prop) x y, locally_2d P x y -> P x y.
Proof.
intros P x y LP.
apply locally_2d_locally in LP.
apply locally_singleton with (1 := LP).
Qed.

Lemma locally_2d_impl :
  forall (P Q : R -> R -> Prop) x y, locally_2d (fun u v => P u v -> Q u v) x y ->
  locally_2d P x y -> locally_2d Q x y.
Proof.
intros P Q x y (d,H).
apply locally_2d_impl_strong.
exists d => u v Hu Hv Hp.
apply H => //.
now apply locally_2d_singleton.
Qed.

Lemma locally_2d_forall :
  forall (P : R -> R -> Prop) x y, (forall u v, P u v) -> locally_2d P x y.
Proof.
intros P x y Hp.
now exists (mkposreal _ Rlt_0_1) => u v _ _.
Qed.

Lemma locally_2d_and :
  forall (P Q : R -> R -> Prop) x y, locally_2d P x y -> locally_2d Q x y ->
  locally_2d (fun u v => P u v /\ Q u v) x y.
Proof.
intros P Q x y H.
apply: locally_2d_impl.
apply: locally_2d_impl H.
apply locally_2d_forall.
now split.
Qed.

Lemma locally_2d_align :
  forall (P Q : R -> R -> Prop) x y,
  ( forall eps : posreal, (forall u v, Rabs (u - x) < eps -> Rabs (v - y) < eps -> P u v) ->
    forall u v, Rabs (u - x) < eps -> Rabs (v - y) < eps -> Q u v ) ->
  locally_2d P x y -> locally_2d Q x y.
Proof.
intros P Q x y K (d,H).
exists d => u v Hu Hv.
now apply (K d).
Qed.

Lemma locally_2d_1d_const_x :
  forall (P : R -> R -> Prop) x y,
  locally_2d P x y ->
  locally y (fun t => P x t).
Proof.
intros P x y (d,Hd).
exists d; intros z Hz.
apply Hd.
rewrite Rminus_eq_0 Rabs_R0; apply cond_pos.
exact Hz.
Qed.

Lemma locally_2d_1d_const_y :
  forall (P : R -> R -> Prop) x y,
  locally_2d P x y ->
  locally x (fun t => P t y).
Proof.
intros P x y (d,Hd).
exists d; intros z Hz.
apply Hd.
exact Hz.
rewrite Rminus_eq_0 Rabs_R0; apply cond_pos.
Qed.

Lemma locally_2d_1d_strong :
  forall (P : R -> R -> Prop) x y,
  locally_2d P x y ->
  locally_2d (fun u v => forall t, 0 <= t <= 1 ->
    locally t (fun z => locally_2d P (x + z * (u - x)) (y + z * (v - y)))) x y.
Proof.
intros P x y.
apply locally_2d_align => eps HP u v Hu Hv t Ht.
assert (Zm: 0 <= Rmax (Rabs (u - x)) (Rabs (v - y))).
apply Rmax_case ; apply Rabs_pos.
destruct Zm as [Zm|Zm].
(* *)
assert (H1: Rmax (Rabs (u - x)) (Rabs (v - y)) < eps).
now apply Rmax_case.
set (d1 := mkposreal _ (Rlt_Rminus _ _ H1)).
assert (H2: 0 < pos_div_2 d1 / Rmax (Rabs (u - x)) (Rabs (v - y))).
apply Rmult_lt_0_compat.
apply cond_pos.
now apply Rinv_0_lt_compat.
set (d2 := mkposreal _ H2).
exists d2 => z Hz.
exists (pos_div_2 d1) => p q Hp Hq.
apply HP.
(* . *)
replace (p - x) with (p - (x + z * (u - x)) + (z - t + t) * (u - x)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
replace (pos eps) with (pos_div_2 d1 + (eps - pos_div_2 d1)) by ring.
apply Rplus_lt_le_compat with (1 := Hp).
rewrite Rabs_mult.
apply Rle_trans with ((d2 + 1) * Rmax (Rabs (u - x)) (Rabs (v - y))).
apply Rmult_le_compat.
apply Rabs_pos.
apply Rabs_pos.
apply Rle_trans with (1 := Rabs_triang _ _).
apply Rplus_le_compat.
now apply Rlt_le.
now rewrite Rabs_pos_eq.
apply Rmax_l.
rewrite /d2 /d1 /=.
field_simplify.
apply Rle_refl.
now apply Rgt_not_eq.
(* . *)
replace (q - y) with (q - (y + z * (v - y)) + (z - t + t) * (v - y)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
replace (pos eps) with (pos_div_2 d1 + (eps - pos_div_2 d1)) by ring.
apply Rplus_lt_le_compat with (1 := Hq).
rewrite Rabs_mult.
apply Rle_trans with ((d2 + 1) * Rmax (Rabs (u - x)) (Rabs (v - y))).
apply Rmult_le_compat.
apply Rabs_pos.
apply Rabs_pos.
apply Rle_trans with (1 := Rabs_triang _ _).
apply Rplus_le_compat.
now apply Rlt_le.
now rewrite Rabs_pos_eq.
apply Rmax_r.
rewrite /d2 /d1 /=.
field_simplify.
apply Rle_refl.
now apply Rgt_not_eq.
(* *)
apply filter_forall => z.
exists eps => p q.
replace (u - x) with 0.
replace (v - y) with 0.
rewrite Rmult_0_r 2!Rplus_0_r.
apply HP.
apply sym_eq.
apply Rabs_eq_0.
apply Rle_antisym.
rewrite Zm.
apply Rmax_r.
apply Rabs_pos.
apply sym_eq.
apply Rabs_eq_0.
apply Rle_antisym.
rewrite Zm.
apply Rmax_l.
apply Rabs_pos.
Qed.

Lemma locally_2d_1d :
  forall (P : R -> R -> Prop) x y,
  locally_2d P x y ->
  locally_2d (fun u v => forall t, 0 <= t <= 1 -> locally_2d P (x + t * (u - x)) (y + t * (v - y))) x y.
Proof.
intros P x y H.
apply locally_2d_1d_strong in H.
apply: locally_2d_impl H.
apply locally_2d_forall => u v H t Ht.
specialize (H t Ht).
apply locally_singleton with (1 := H).
Qed.

Lemma locally_2d_ex_dec :
  forall P x y,
  (forall x y, P x y \/ ~P x y) ->
  locally_2d P x y ->
  {d : posreal | forall u v, Rabs (u-x) < d -> Rabs (v-y) < d -> P u v}.
Proof.
intros P x y P_dec H.
destruct (locally_ex_dec (x, y) (fun z => P (fst z) (snd z))) as [d Hd].
- now intros [u v].
- destruct H as [e H].
  exists e.
  intros [u v] Huv.
  apply H.
  apply Huv.
  apply Huv.
exists d.
intros u v Hu Hv.
apply (Hd (u, v)).
simpl.
now split.
Qed.

(** * Some Topology on [Rbar] *)

Definition Rbar_locally' (a : Rbar) (P : R -> Prop) :=
  match a with
    | Finite a => locally' a P
    | p_infty => exists M : R, forall x, M < x -> P x
    | m_infty => exists M : R, forall x, x < M -> P x
  end.
Definition Rbar_locally (a : Rbar) (P : R -> Prop) :=
  match a with
    | Finite a => locally a P
    | p_infty => exists M : R, forall x, M < x -> P x
    | m_infty => exists M : R, forall x, x < M -> P x
  end.

Global Instance Rbar_locally'_filter :
  forall x, ProperFilter (Rbar_locally' x).
Proof.
intros [x| |] ; (constructor ; [idtac | constructor]).
- intros P [eps HP].
  exists (x + eps / 2).
  apply HP.
  rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
  ring_simplify (x + eps / 2 + - x).
  rewrite Rabs_pos_eq.
  apply Rminus_lt_0.
  replace (eps - eps / 2) with (eps / 2) by field.
  apply is_pos_div_2.
  apply Rlt_le, is_pos_div_2.
  apply Rgt_not_eq, Rminus_lt_0 ; ring_simplify.
  apply is_pos_div_2.
- now exists (mkposreal _ Rlt_0_1).
- intros P Q [dP HP] [dQ HQ].
  exists (mkposreal _ (Rmin_stable_in_posreal dP dQ)).
  simpl.
  intros y Hy H.
  split.
  apply HP with (2 := H).
  apply Rlt_le_trans with (1 := Hy).
  apply Rmin_l.
  apply HQ with (2 := H).
  apply Rlt_le_trans with (1 := Hy).
  apply Rmin_r.
- intros P Q H [dP HP].
  exists dP.
  intros y Hy H'.
  apply H.
  now apply HP.
- intros P [N HP].
  exists (N + 1).
  apply HP.
  apply Rlt_plus_1.
- now exists 0.
- intros P Q [MP HP] [MQ HQ].
  exists (Rmax MP MQ).
  intros y Hy.
  split.
  apply HP.
  apply Rle_lt_trans with (2 := Hy).
  apply Rmax_l.
  apply HQ.
  apply Rle_lt_trans with (2 := Hy).
  apply Rmax_r.
- intros P Q H [dP HP].
  exists dP.
  intros y Hy.
  apply H.
  now apply HP.
- intros P [N HP].
  exists (N - 1).
  apply HP.
  apply Rlt_minus_l, Rlt_plus_1.
- now exists 0.
- intros P Q [MP HP] [MQ HQ].
  exists (Rmin MP MQ).
  intros y Hy.
  split.
  apply HP.
  apply Rlt_le_trans with (1 := Hy).
  apply Rmin_l.
  apply HQ.
  apply Rlt_le_trans with (1 := Hy).
  apply Rmin_r.
- intros P Q H [dP HP].
  exists dP.
  intros y Hy.
  apply H.
  now apply HP.
Qed.

Global Instance Rbar_locally_filter :
  forall x, ProperFilter (Rbar_locally x).
Proof.
intros [x| |].
- apply locally_filter.
- exact (Rbar_locally'_filter p_infty).
- exact (Rbar_locally'_filter m_infty).
Qed.

(** Open sets in [Rbar] *)

Lemma open_Rbar_lt :
  forall y, open (fun u : R => Rbar_lt u y).
Proof.
intros [y| |].
- apply open_lt.
- apply open_true.
- apply open_false.
Qed.

Lemma open_Rbar_gt :
  forall y, open (fun u : R => Rbar_lt y u).
Proof.
intros [y| |].
- apply open_gt.
- apply open_false.
- apply open_true.
Qed.

Lemma open_Rbar_lt' :
  forall x y, Rbar_lt x y -> Rbar_locally x (fun u => Rbar_lt u y).
Proof.
intros [x| |] y Hxy.
- now apply open_Rbar_lt.
- easy.
- destruct y as [y| |].
  now exists y.
  now apply filter_forall.
  easy.
Qed.

Lemma open_Rbar_gt' :
  forall x y, Rbar_lt y x -> Rbar_locally x (fun u => Rbar_lt y u).
Proof.
intros [x| |] y Hxy.
- now apply open_Rbar_gt.
- destruct y as [y| |].
  now exists y.
  easy.
  now apply filter_forall.
- now destruct y as [y| |].
Qed.

Lemma Rbar_locally'_le :
  forall x, filter_le (Rbar_locally' x) (Rbar_locally x).
Proof.
intros [x| |] P [eps HP] ; exists eps ; intros ; now apply HP.
Qed.

Lemma Rbar_locally'_le_finite :
  forall x : R, filter_le (Rbar_locally' x) (locally x).
Proof.
intros x P [eps HP] ; exists eps ; intros ; now apply HP.
Qed.

(** * Some limits on real functions *)

Definition Rbar_loc_seq (x : Rbar) (n : nat) := match x with
    | Finite x => x + / (INR n + 1)
    | p_infty => INR n
    | m_infty => - INR n
  end.

Lemma filterlim_Rbar_loc_seq :
  forall x, filterlim (Rbar_loc_seq x) eventually (Rbar_locally' x).
Proof.
  intros x P.
  unfold Rbar_loc_seq.
  case: x => /= [x | | ] [delta Hp].
(* x \in R *)
  case: (nfloor_ex (/delta)) => [ | N [_ HN]].
  by apply Rlt_le, Rinv_0_lt_compat, delta.
  exists N => n Hn.
  apply Hp ; simpl.
  rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
  ring_simplify (x + / (INR n + 1) + - x).
  rewrite Rabs_pos_eq.
  rewrite -(Rinv_involutive delta).
  apply Rinv_lt_contravar.
  apply Rmult_lt_0_compat.
  apply Rinv_0_lt_compat.
  by apply delta.
  exact: INRp1_pos.
  apply Rlt_le_trans with (1 := HN).
  by apply Rplus_le_compat_r, le_INR.
  by apply Rgt_not_eq, delta.
  by apply Rlt_le, RinvN_pos.
  apply Rgt_not_eq, Rminus_lt_0.
  ring_simplify.
  by apply RinvN_pos.
(* x = p_infty *)
  case: (nfloor_ex (Rmax 0 delta)) => [ | N [_ HN]].
  by apply Rmax_l.
  exists (S N) => n Hn.
  apply Hp.
  apply Rle_lt_trans with (1 := Rmax_r 0 _).
  apply Rlt_le_trans with (1 := HN).
  rewrite -S_INR ; by apply le_INR.
(* x = m_infty *)
  case: (nfloor_ex (Rmax 0 (-delta))) => [ | N [_ HN]].
  by apply Rmax_l.
  exists (S N) => n Hn.
  apply Hp.
  rewrite -(Ropp_involutive delta).
  apply Ropp_lt_contravar.
  apply Rle_lt_trans with (1 := Rmax_r 0 _).
  apply Rlt_le_trans with (1 := HN).
  rewrite -S_INR ; by apply le_INR.
Qed.

Lemma continuity_pt_locally :
  forall f x,
  continuity_pt f x <->
  forall eps : posreal, locally x (fun u => Rabs (f u - f x) < eps).
Proof.
intros f x.
split.
intros H eps.
move: (H eps (cond_pos eps)) => {H} [d [H1 H2]].
rewrite /= /R_dist /D_x /no_cond in H2.
exists (mkposreal d H1) => y H.
destruct (Req_dec x y) as [<-|Hxy].
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
by apply H2.
intros H eps He.
move: (H (mkposreal _ He)) => {H} [d H].
exists d.
split.
apply cond_pos.
intros h [Zh Hh].
exact: H.
Qed.

Lemma continuity_pt_locally' :
  forall f x,
  continuity_pt f x <->
  forall eps : posreal, locally' x (fun u => Rabs (f u - f x) < eps).
Proof.
intros f x.
split.
intros H eps.
move: (H eps (cond_pos eps)) => {H} [d [H1 H2]].
rewrite /= /R_dist /D_x /no_cond in H2.
exists (mkposreal d H1) => y H H'.
destruct (Req_dec x y) as [<-|Hxy].
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
by apply H2.
intros H eps He.
move: (H (mkposreal _ He)) => {H} [d H].
exists d.
split.
apply cond_pos.
intros h [Zh Hh].
apply H.
exact Hh.
apply proj2 in Zh.
now contradict Zh.
Qed.

Lemma continuity_pt_filterlim :
  forall (f : R -> R) (x : R),
  continuity_pt f x <->
  filterlim f (locally x) (locally (f x)).
Proof.
intros f x.
eapply iff_trans.
apply continuity_pt_locally.
apply iff_sym.
exact (filterlim_locally f (f x)).
Qed.

Lemma continuity_pt_filterlim' :
  forall f x,
  continuity_pt f x <->
  filterlim f (locally' x) (locally (f x)).
Proof.
intros f x.
eapply iff_trans.
apply continuity_pt_locally'.
apply iff_sym.
exact (filterlim_locally f (f x)).
Qed.

Lemma locally_pt_comp (P : R -> Prop) (f : R -> R) (x : R) :
  locally (f x) P -> continuity_pt f x ->
  locally x (fun x => P (f x)).
Proof.
intros Lf Cf.
apply continuity_pt_filterlim in Cf.
now apply Cf.
Qed.
