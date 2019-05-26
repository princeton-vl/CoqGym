Require Export RelDefinitions.
Require Import RelClasses.
Require Import Coq.Lists.List.


(** * Relators *)

(** With this infrastructure in place, we can define actual relators
  that cover the commonly used type constructors. There are two broad
  categories: those related to function types, and those derived from
  inductive types. *)

(** As a convention, we name relators and the associated monotonicity
  theorems by appending the suffix [_rel] to the name of original type
  and those of its constructors. Likewise, we use the suffix [_subrel]
  for monotonicity theorems that characterize the variance of
  corresponding relators with respect to [subrel], and the suffix
  [_relim] for an associated instance of [RElim]. *)

(** ** A note about universes *)

(** Our use of [subrel] illustrates the fact that we consider
  relations over relations, and use relators to build up relations
  over the types of our relators to characterize their variance.
  In other words: we relate all kind of higher-order things as a
  matter of course and make sure our library eats its own dog
  food. This makes it relatively easy to run into universe
  inconsistency issues. This note is to explain why those happen, fix
  the terminology, and formulate best practices to avoid such
  problems.

  The critical universe level in Coqrel is the universe [U] from which
  the arguments and return type of [rel] are taken (so that
  conceptually we will write [rel : U -> U -> U]). We will call
  "small types" the inhabitants of [U], and "large types" those taken
  from a universe strictly larger than [U]. At the moment, [U] is
  implicit, but at some point we may want declare an explicit
  [Universe] to aid debugging and enhance clarity.

  Generally speaking, [U] is a pretty large universe: for the most
  part, the world of relational things sits well above the world of
  the things we want relate, no matter how high-order those are.
  Even [rel A B] is still a small type, so that
  [@subrel : forall A B : U, rel (rel A B) (rel A B)]
  above didn't cause any issue, although the type of [rel] itself,
  namely [U -> U -> U : U+1], is of course a large type.

  With this in mind, consider the relational operator
  [rel_compose : forall A B C, rel A B -> rel B C -> rel A C].
  We wish to register a monotonicity property for [rel_compose],
  establishing that composing larger relations yields a larger
  composite relation. As usual, we express this property by
  establishing that [rel_compose] is related to itself by an
  appropriate relation. However, the type of [rel_compose] may involve
  [U : U+1] as the type of the arguments [A B C], so that the type of
  [rel_compose] may itself be forced into sort [U+1]. Consequently,
  attempting to define that relation will yield a universe
  inconsistency as soon as, say, [subrel] is used as an argument of
  [rel_compose].

  Fortunately, even if [A B C : U], the specialized form
  [rel_compose A B C] is still in the small type
  [rel A B -> rel B C -> rel A C : U]. Moreover, there is no
  relational structure that we want to capture regarding the type
  parameters [A B C], so that we don't lose anything by defining our
  monotonicity property for the specialized [rel_compose A B C],
  as long as the property itself is generic in the specific values of
  [A B C].

  This is why, as a general rule, we define the [foo_subrel]
  properties of our relators on partially applied versions thereof,
  and use a [foo_subrel_params] hint to make sure our monotonicity
  tactic can resolve them. *)

(** ** Relators for function types *)

(** *** Pointwise extension of a relation *)

(** One useful special case is the pointwise extension of a relation
  on the domain to the function type. This is equivalent to [eq ==> R],
  however with the formulation below we don't have consider two equal
  elements of the domain. *)

Definition arrow_pointwise_rel A {B1 B2}:
  rel B1 B2 -> rel (A -> B1) (A -> B2) :=
    fun RB f g => forall a, RB (f a) (g a).

Arguments arrow_pointwise_rel A%type {B1%type B2%type} RB%rel _ _.

Notation "- ==> R" := (arrow_pointwise_rel _ R)
  (at level 55, right associativity) : rel_scope.

Global Instance arrow_pointwise_subrel {A B1 B2}:
  Monotonic (@arrow_pointwise_rel A B1 B2) (subrel ++> subrel).
Proof.
  firstorder.
Qed.

Global Instance arrow_pointwise_subrel_params:
  Params (@arrow_pointwise_rel) 3.

Lemma arrow_pointwise_rintro {A B1 B2} (R: rel B1 B2) f g:
  RIntro (forall x: A, R (f x) (g x)) (- ==> R) f g.
Proof.
  firstorder.
Qed.

Hint Extern 0 (RIntro _ (- ==> _) _ _) =>
  eapply arrow_pointwise_rintro : typeclass_instances.

(** Note that although the elimination rule could use a single
  variable and dispense with the equality premise, it actually uses
  two distinct variables [m] and [n], and a premise in [P] that [m = n].
  Hence the effect is similar to the elimination rule for the
  equivalent relation [eq ==> R]. We do this because in contexts where
  we have a single term [t] against which both [m] and [n] unify, it
  is easy and cheap to automatically prove that [t = t], but in
  contexts where we have two disctinct variables and a proof of
  equality, it is more involved to massage the goal into a form where
  the single-variable version of the rule could apply. *)

Lemma arrow_pointwise_relim {A B1 B2} (R: rel B1 B2) f g (m n: A) P Q:
  RElim R (f m) (g n) P Q ->
  RElim (- ==> R) f g (m = n /\ P) Q.
Proof.
  intros HPQ Hfg [Hab HP].
  subst.
  firstorder.
Qed.

Hint Extern 1 (RElim (- ==> _) _ _ _ _) =>
  eapply arrow_pointwise_relim : typeclass_instances.

Lemma arrow_pointwise_refl {T} `(Reflexive) :
  @Reflexive (T -> A) (- ==> R).
Proof.
  firstorder.
Qed.

Hint Extern 1 (Reflexive (- ==> _)) =>
  eapply arrow_pointwise_refl : typeclass_instances.

Global Instance arrow_pointwise_rel_compose {T} `(RCompose) :
  RCompose (A := T -> A) (- ==> RAB) (- ==> RBC) (- ==> RAC).
Proof.
  firstorder.
Qed.

(** *** Dependent pointwise extension *)

(** Like we did for non-dependent functions, we can provide a simpler
  definition for the special case where [E] is [eq]. *)

Definition forall_pointwise_rel {V: Type} {FV1 FV2: V -> Type}:
    (forall v, rel (FV1 v) (FV2 v)) ->
    rel (forall v, FV1 v) (forall v, FV2 v) :=
  fun FE f g =>
    forall v, FE v (f v) (g v).

Arguments forall_pointwise_rel {V%type FV1%type FV2%type} FE%rel _ _.

Notation "'forallr' - @ v : V , FE" :=
  (forall_pointwise_rel (V := V) (fun v => FE))
  (v ident, at level 200).

Notation "'forallr' - @ v , FE" :=
  (forall_pointwise_rel (fun v => FE))
  (v ident, at level 200).

Notation "'forallr' - : V , FE" :=
  (forall_pointwise_rel (V := V) (fun _ => FE))
  (at level 200).

Notation "'forallr' - , FE" :=
  (forall_pointwise_rel (fun _ => FE))
  (at level 200).

Lemma forall_pointwise_rintro {V FV1 FV2} (FE: forall v, rel _ _) f g:
  RIntro
    (forall v, FE v (f v) (g v))
    (@forall_pointwise_rel V FV1 FV2 FE) f g.
Proof.
  firstorder.
Qed.

Hint Extern 0 (RIntro _ (forall_pointwise_rel _) _ _) =>
  eapply forall_pointwise_rintro : typeclass_instances.

Lemma forall_pointwise_relim {V FV1 FV2} R f g v P Q:
  RElim (R v) (f v) (g v) P Q ->
  RElim (@forall_pointwise_rel V FV1 FV2 R) f g P Q.
Proof.
  firstorder.
Qed.

Hint Extern 1 (RElim (forall_pointwise_rel _) _ _ _ _) =>
  eapply forall_pointwise_relim : typeclass_instances.

(** *** Dependent products (restricted version) *)

(** This is a restricted version of [forall_rel] with [E] in [Prop],
  when the codomain relation only depends on the arguments. *)

Definition forallp_rel {V1 V2} (E: rel V1 V2) {FV1: V1->Type} {FV2: V2->Type}:
    (forall v1 v2, rel (FV1 v1) (FV2 v2)) ->
    rel (forall v1, FV1 v1) (forall v2, FV2 v2) :=
  fun FE f g =>
    forall v1 v2, E v1 v2 -> FE v1 v2 (f v1) (g v2).

Arguments forallp_rel {V1%type V2%type} E%rel {FV1%type FV2%type} FE%rel _ _.

Notation "'forallr' v1 v2 : E , R" :=
  (forallp_rel E (fun v1 v2 => R))
  (at level 200, v1 ident, v2 ident, right associativity)
  : rel_scope.

Lemma forallp_rintro {V1 V2} {E: rel V1 V2} {F1 F2} (FE: forall v1 v2, rel _ _) f g:
  RIntro
    (forall v1 v2, E v1 v2 -> FE v1 v2 (f v1) (g v2))
    (@forallp_rel V1 V2 E F1 F2 FE) f g.
Proof.
  firstorder.
Qed.

Hint Extern 0 (RIntro _ (forallp_rel _ _) _ _) =>
  eapply forallp_rintro : typeclass_instances.

(** Since [e : E v1 v2] cannot be unified in [Q], the elimination rule
  adds an [E v1 v2] premise to [P] instead. *)

Lemma forallp_relim {V1 V2 E FV1 FV2} R f g v1 v2 P Q:
  RElim (R v1 v2) (f v1) (g v2) P Q ->
  RElim (@forallp_rel V1 V2 E FV1 FV2 R) f g (E v1 v2 /\ P) Q.
Proof.
  firstorder.
Qed.

Hint Extern 1 (RElim (forallp_rel _ _) _ _ _ _) =>
  eapply forallp_relim : typeclass_instances.

(** TODO: A further specialization could be [foralln_rel], which does
  not even require that [v1], [v2] be related (let alone care about
  the proof). In other words, a [forallr v1 v2, R] which would
  essentially boil down to [forallr v1 v2 : ⊤, R]. *)

(** *** Sets ([A -> Prop]) *)

(** Sets of type [A -> Prop] can be related using the regular arrow
  relator, as in [R ++> impl]. This states that for any two elements
  related by [R], if the first is in the first set, then the second
  must be in the second set.

  However, very often we need the following relator instead, which
  states that for any element of the first set, there exists an
  element of the second set which is related to it. This is useful for
  example when defining simulation diagrams. *)

Definition set_le {A B} (R: rel A B): rel (A -> Prop) (B -> Prop) :=
  fun sA sB => forall a, sA a -> exists b, sB b /\ R a b.

Global Instance set_le_subrel {A B}:
  Monotonic (@set_le A B) (subrel ++> subrel).
Proof.
  intros R1 R2 HR sA sB Hs.
  intros x Hx.
  destruct (Hs x) as (y & Hy & Hxy); eauto.
Qed.

Global Instance set_le_subrel_params:
  Params (@set_le) 3.

Lemma set_le_refl {A} (R : relation A) :
  Reflexive R ->
  Reflexive (set_le R).
Proof.
  firstorder.
Qed.

Hint Extern 1 (Reflexive (set_le _)) =>
  eapply set_le_refl : typeclass_instances.

Global Instance set_le_compose `(RCompose) :
  RCompose (set_le RAB) (set_le RBC) (set_le RAC).
Proof.
  intros sa sb sc Hsab Hsbc a Ha.
  edestruct Hsab as (b & Hb & Hab); eauto.
  edestruct Hsbc as (c & Hc & Hbc); eauto.
Qed.

(** We define [set_ge] as well. *)

Definition set_ge {A B} (R: rel A B): rel (A -> Prop) (B -> Prop) :=
  fun sA sB => forall b, sB b -> exists a, sA a /\ R a b.

Global Instance set_ge_subrel {A B}:
  Monotonic (@set_ge A B) (subrel ++> subrel).
Proof.
  firstorder.
Qed.

Global Instance set_ge_subrel_params:
  Params (@set_ge) 3.

Lemma set_ge_refl {A} (R : relation A) :
  Reflexive R ->
  Reflexive (set_ge R).
Proof.
  firstorder.
Qed.

Hint Extern 1 (Reflexive (set_ge _)) =>
  eapply set_ge_refl : typeclass_instances.

Global Instance set_ge_compose `(RCompose) :
  RCompose (set_ge RAB) (set_ge RBC) (set_ge RAC).
Proof.
  intros sa sb sc Hsab Hsbc c Hc.
  edestruct Hsbc as (b & Hb & Hbc); eauto.
  edestruct Hsab as (a & Ha & Hab); eauto.
Qed.

(** ** Inductive types *)

(** For inductive types, there is a systematic way of converting their
  definition into that of the corresponding relator. Where the
  original inductive definition quantifies over types, the
  corresponding relator will quantify over pairs of types and
  relations between them. Then, the constructors of the relator will
  essentially be [Proper] instances for the original constructors.
  In other words, the resulting relation will be the smallest one such
  that the constructors are order-preserving. *)

(** *** Nullary type constructors *)

(** As a proof-of-concept, we start with the most elementary types
  [Empty_set] and [unit], which can be considered as nullary type
  constructors related to [sum] and [prod] below. *)

Inductive Empty_set_rel: rel Empty_set Empty_set := .

Inductive unit_rel: rel unit unit :=
  tt_rel: Proper unit_rel tt.

Global Existing Instance tt_rel.

(** *** Sum types *)

(** The definition of [sum_rel] could look something like this:
<<
    Inductive sum_rel:
      forall {A1 A2 B1 B2}, rel A1 A2 -> rel B1 B2 -> rel (A1+B1) (A2+B2):=
      | inl_rel: Proper (∀ RA : rel, ∀ RB : rel, RA ++> sum_rel RA RB) (@inl)
      | inr_rel: Proper (∀ RA : rel, ∀ RB : rel, RB ++> sum_rel RA RB) (@inr).
>>
  However, to minimize the need for [inversion]s we want to keep as
  many arguments as possible as parameters of the inductive type. *)

Inductive sum_rel {A1 A2 B1 B2} RA RB: rel (A1 + B1)%type (A2 + B2)%type :=
  | inl_rel_def: (RA ++> sum_rel RA RB)%rel (@inl A1 B1) (@inl A2 B2)
  | inr_rel_def: (RB ++> sum_rel RA RB)%rel (@inr A1 B1) (@inr A2 B2).

Infix "+" := sum_rel : rel_scope.

(** Since it is not possible to retype the constructors after the
  fact, we use the [_def] suffix when defining them, then redeclare
  a corresponding, full-blown [Proper] instance. *)

Global Instance inl_rel:
  Monotonic (@inl) (forallr RA, forallr RB, RA ++> RA + RB).
Proof.
  repeat intro; apply inl_rel_def; assumption.
Qed.

Global Instance inr_rel:
  Monotonic (@inr) (forallr RA, forallr RB, RB ++> RA + RB).
Proof.
  repeat intro; apply inr_rel_def; assumption.
Qed.

Global Instance sum_subrel {A1 A2 B1 B2}:
  Monotonic (@sum_rel A1 A2 B1 B2) (subrel ++> subrel ++> subrel).
Proof.
  intros RA1 RA2 HRA RB1 RB2 HRB.
  intros x1 x2 Hx.
  destruct Hx; constructor; eauto.
Qed.

Global Instance sum_subrel_params:
  Params (@sum) 4.

Lemma sum_rel_refl {A B} (R1: rel A A) (R2: rel B B):
  Reflexive R1 -> Reflexive R2 -> Reflexive (R1 + R2).
Proof.
  intros H1 H2 x.
  destruct x; constructor; reflexivity.
Qed.

Hint Extern 2 (Reflexive (_ + _)) =>
  eapply sum_rel_refl : typeclass_instances.

Lemma sum_rel_corefl {A B} (R1: rel A A) (R2: rel B B):
  Coreflexive R1 -> Coreflexive R2 -> Coreflexive (R1 + R2).
Proof.
  intros H1 H2 _ _ [x y H | x y H];
  f_equal;
  eauto using coreflexivity.
Qed.

Hint Extern 2 (Coreflexive (_ + _)) =>
  eapply sum_rel_corefl : typeclass_instances.

Lemma sum_rel_trans {A B} (R1: rel A A) (R2: rel B B):
  Transitive R1 -> Transitive R2 -> Transitive (R1 + R2).
Proof.
  intros H1 H2 x y z Hxy Hyz.
  destruct Hxy; inversion Hyz; constructor; etransitivity; eassumption.
Qed.

Hint Extern 2 (Transitive (_ + _)) =>
  eapply sum_rel_trans : typeclass_instances.

Lemma sum_rel_sym {A B} (R1: rel A A) (R2: rel B B):
  Symmetric R1 -> Symmetric R2 -> Symmetric (R1 + R2).
Proof.
  intros H1 H2 x y Hxy.
  destruct Hxy; constructor; symmetry; eassumption.
Qed.

Hint Extern 2 (Symmetric (_ + _)) =>
  eapply sum_rel_sym : typeclass_instances.

Lemma sum_rel_preorder {A B} (R1: rel A A) (R2: rel B B):
  PreOrder R1 -> PreOrder R2 -> PreOrder (R1 + R2).
Proof.
  split; typeclasses eauto.
Qed.

Hint Extern 2 (PreOrder (_ + _)) =>
  eapply sum_rel_preorder : typeclass_instances.

(** *** Pairs *)

Definition prod_rel {A1 A2 B1 B2} RA RB: rel (A1 * B1)%type (A2 * B2)%type :=
  fun x1 x2 => RA (fst x1) (fst x2) /\ RB (snd x1) (snd x2).

Infix "*" := prod_rel : rel_scope.

Global Instance pair_rel:
  Monotonic (@pair) (forallr RA, forallr RB, RA ++> RB ++> RA * RB).
Proof.
  intros A1 A2 RA B1 B2 RB a1 a2 Ha b1 b2 Hb.
  red.
  eauto.
Qed.

Global Instance fst_rel:
  Monotonic (@fst) (forallr RA, forallr RB, RA * RB ==> RA).
Proof.
  intros A1 A2 RA B1 B2 RB.
  intros x1 x2 [Ha Hb].
  assumption.
Qed.

Global Instance snd_rel:
  Monotonic (@snd) (forallr RA, forallr RB, RA * RB ==> RB).
Proof.
  intros A1 A2 RA B1 B2 RB.
  intros x1 x2 [Ha Hb].
  assumption.
Qed.

Global Instance prod_subrel {A1 A2 B1 B2}:
  Monotonic (@prod_rel A1 A2 B1 B2) (subrel ++> subrel ++> subrel).
Proof.
  firstorder.
Qed.

Global Instance prod_subrel_params:
  Params (@prod_rel) 4.

Global Instance prod_rdestruct {A1 B1 A2 B2} (RA: rel A1 A2) (RB: rel B1 B2):
  RDestruct
    (RA * RB)%rel
    (fun P => forall a1 a2 b1 b2, RA a1 a2 -> RB b1 b2 -> P (a1, b1) (a2, b2)).
Proof.
  intros [a1 b1] [a2 b2] [Ha Hb] P HP.
  firstorder.
Qed.

Lemma prod_rel_refl {A B} (R1: rel A A) (R2: rel B B):
  Reflexive R1 -> Reflexive R2 -> Reflexive (R1 * R2).
Proof.
  intros H1 H2 x.
  destruct x; constructor; reflexivity.
Qed.

Hint Extern 2 (Reflexive (_ * _)) =>
  eapply prod_rel_refl : typeclass_instances.

Lemma prod_rel_corefl {A B} (R1: rel A A) (R2: rel B B):
  Coreflexive R1 -> Coreflexive R2 -> Coreflexive (R1 * R2).
Proof.
  intros H1 H2 [a1 b1] [a2 b2] [Ha Hb].
  f_equal; eauto using coreflexivity.
Qed.

Hint Extern 2 (Coreflexive (_ * _)) =>
  eapply prod_rel_corefl : typeclass_instances.

Lemma prod_rel_trans {A B} (R1: rel A A) (R2: rel B B):
  Transitive R1 -> Transitive R2 -> Transitive (R1 * R2).
Proof.
  intros H1 H2 x y z Hxy Hyz.
  destruct Hxy; inversion Hyz; constructor; etransitivity; eassumption.
Qed.

Hint Extern 2 (Transitive (_ * _)) =>
  eapply prod_rel_trans : typeclass_instances.

Lemma prod_rel_sym {A B} (R1: rel A A) (R2: rel B B):
  Symmetric R1 -> Symmetric R2 -> Symmetric (R1 * R2).
Proof.
  intros H1 H2 x y Hxy.
  destruct Hxy; constructor; symmetry; eassumption.
Qed.

Hint Extern 2 (Symmetric (_ * _)) =>
  eapply prod_rel_sym : typeclass_instances.

Lemma prod_rel_preorder {A B} (R1: rel A A) (R2: rel B B):
  PreOrder R1 -> PreOrder R2 -> PreOrder (R1 * R2).
Proof.
  split; typeclasses eauto.
Qed.

Hint Extern 2 (PreOrder (_ * _)) =>
  eapply prod_rel_preorder : typeclass_instances.

(** *** Option types *)

Inductive option_rel {A1 A2} (RA: rel A1 A2): rel (option A1) (option A2) :=
  | Some_rel_def: (RA ++> option_rel RA)%rel (@Some A1) (@Some A2)
  | None_rel_def: option_rel RA (@None A1) (@None A2).

Global Instance Some_rel:
  Monotonic (@Some) (forallr R @ A1 A2 : rel, R ++> option_rel R).
Proof.
  exact @Some_rel_def.
Qed.

Global Instance None_rel:
  Monotonic (@None) (forallr R, option_rel R).
Proof.
  exact @None_rel_def.
Qed.

Global Instance option_subrel {A1 A2}:
  Monotonic (@option_rel A1 A2) (subrel ++> subrel).
Proof.
  intros RA1 RA2 HRA.
  intros x1 x2 Hx.
  destruct Hx; constructor; eauto.
Qed.

Global Instance option_subrel_params:
  Params (@option_rel) 3.

Lemma option_rel_refl `(HR: Reflexive):
  Reflexive (option_rel R).
Proof.
  intros [x | ]; constructor; reflexivity.
Qed.

Hint Extern 1 (Reflexive (option_rel _)) =>
  eapply option_rel_refl : typeclass_instances.

Global Instance option_map_rel:
  Monotonic
    (@option_map)
    (forallr RA, forallr RB, (RA ++> RB) ++> option_rel RA ++> option_rel RB).
Proof.
  intros A1 A2 RA B1 B2 RB f g Hfg x y Hxy.
  destruct Hxy; constructor; eauto.
Qed.

(** XXX: This does not fit any of our existing patterns, we should
  drop it for consistency or introduce a new convention and generalize
  this kind of lemmas. *)

Lemma option_rel_some_inv A B (R: rel A B) (x: option A) (y: option B) (a: A):
  option_rel R x y ->
  x = Some a ->
  exists b,
    y = Some b /\
    R a b.
Proof.
  destruct 1; inversion 1; subst; eauto.
Qed.

(** *** Lists *)

Inductive list_rel {A1 A2} (R: rel A1 A2): rel (list A1) (list A2) :=
  | nil_rel_def: (list_rel R) (@nil A1) (@nil A2)
  | cons_rel_def: (R ++> list_rel R ++> list_rel R)%rel (@cons A1) (@cons A2).

Global Instance nil_rel:
  Monotonic (@nil) (forallr R, list_rel R).
Proof.
  exact @nil_rel_def.
Qed.

Global Instance cons_rel:
  Monotonic (@cons) (forallr R, R ++> list_rel R ++> list_rel R).
Proof.
  exact @cons_rel_def.
Qed.

Global Instance list_subrel {A1 A2}:
  Monotonic (@list_rel A1 A2) (subrel ++> subrel).
Proof.
  intros R S HRS x y.
  red in HRS.
  induction 1; constructor; eauto.
Qed.

Global Instance list_subrel_params:
  Params (@list_rel) 3.

Lemma list_rel_refl `(HR: Reflexive):
  Reflexive (list_rel R).
Proof.
  intros l.
  induction l; constructor; eauto.
Qed.

Hint Extern 1 (Reflexive (list_rel _)) =>
  eapply list_rel_refl : typeclass_instances.

Lemma list_rel_corefl `(HR: Coreflexive):
  Coreflexive (list_rel R).
Proof.
  intros l1 l2 Hl.
  induction Hl as [ | x1 x2 Hx l1 l2 Hl IHl];
  f_equal; eauto using coreflexivity.
Qed.

Hint Extern 1 (Coreflexive (list_rel _)) =>
  eapply list_rel_corefl : typeclass_instances.

Lemma list_rel_sym `(HR: Symmetric):
  Symmetric (list_rel R).
Proof.
  intros l1 l2 Hl.
  induction Hl; constructor; eauto.
Qed.

Hint Extern 1 (Symmetric (list_rel _)) =>
  eapply list_rel_sym : typeclass_instances.

Lemma list_rel_trans `(HR: Transitive):
  Transitive (list_rel R).
Proof.
  intros l1 l2 l3 Hl12 Hl23.
  revert l3 Hl23.
  induction Hl12; inversion 1; constructor; eauto.
Qed.

Hint Extern 1 (Transitive (list_rel _)) =>
  eapply list_rel_trans : typeclass_instances.

Global Instance length_rel:
  Monotonic
    (@length)
    (forallr R : rel, list_rel R ++> eq).
Proof.
  induction 1; simpl; congruence.
Qed.

Global Instance app_rel:
  Monotonic
    (@app)
    (forallr R : rel, list_rel R ++> list_rel R ++> list_rel R).
Proof.
  intros A1 A2 R l1 l2 Hl.
  induction Hl as [ | x1 x2 Hx l1 l2 Hl IHl]; simpl.
  - firstorder.
  - constructor; eauto.
Qed.

Global Instance map_rel:
  Monotonic
    (@map)
    (forallr RA, forallr RB, (RA ++> RB) ++> list_rel RA ++> list_rel RB).
Proof.
  intros A1 A2 RA B1 B2 RB f g Hfg l1 l2 Hl.
  induction Hl; constructor; eauto.
Qed.

Global Instance fold_right_rel:
  Monotonic
    (@fold_right)
    (forallr RA, forallr RB, (RB ++> RA ++> RA) ++> RA ++> list_rel RB ++> RA).
Proof.
  intros A1 A2 RA B1 B2 RB f g Hfg a1 a2 Ha l1 l2 Hl.
  induction Hl; simpl; eauto.
  eapply Hfg; eauto.
Qed.

Global Instance fold_left_rel:
  Monotonic
    (@fold_left)
    (forallr RA, forallr RB, (RA ++> RB ++> RA) ++> list_rel RB ++> RA ++> RA).
Proof.
  intros A1 A2 RA B1 B2 RB f g Hfg l1 l2 Hl.
  induction Hl; simpl.
  - firstorder.
  - intros a1 a2 Ha.
    eapply IHHl.
    eapply Hfg; assumption.
Qed.

(** ** Monotonicity of logical connectives *)

Lemma fold_impl_rstep (A B: Prop):
  RStep (impl A B) (A -> B).
Proof.
  firstorder.
Qed.

Hint Extern 1 (RStep _ (_ -> _)) =>
  eapply fold_impl_rstep : typeclass_instances.

Global Instance all_monotonic {A}:
  Monotonic (@all A) ((- ==> impl) ++> impl).
Proof.
  intros P Q HPQ H x.
  apply HPQ.
  apply H.
Qed.

Global Instance all_monotonic_params:
  Params (@all) 1.

Global Instance ex_monotonic A:
  Monotonic (@ex A) ((- ==> impl) ++> impl).
Proof.
  intros P Q HPQ [x Hx].
  exists x.
  apply HPQ.
  assumption.
Qed.

Global Instance ex_monotonic_params:
  Params (@ex) 1.

Global Instance and_monotonic:
  Monotonic (@and) (impl ++> impl ++> impl).
Proof.
  intros P1 P2 HP Q1 Q2 HQ [HP1 HQ1].
  eauto.
Qed.

Global Instance or_monotonic:
  Monotonic (@or) (impl ++> impl ++> impl).
Proof.
  intros P1 P2 HP Q1 Q2 HQ [HP1|HQ1];
  eauto.
Qed.
